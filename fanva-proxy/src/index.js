// fanva-proxy — a CORS-adding reverse proxy for the jbotci MCP endpoint.
//
// Why this exists: nibli-fanva's browser McpClient (wasm/gloo-net fetch) needs to
// reach https://jbotci.app/mcp, but jbotci (a) emits no CORS headers, (b) 403s any
// request that carries a browser `Origin` header, and (c) 405s the CORS preflight
// (it does not implement OPTIONS). This Worker makes the browser think it is talking
// to a CORS-friendly server while making jbotci think it is talking to a plain
// server-to-server client.
//
// The upstream is a HARDCODED CONSTANT — never derived from the request path, query,
// or any header. This is therefore a fixed reverse proxy, NOT an open/SSRF proxy: an
// attacker cannot repoint it anywhere but jbotci.
//
// Verified ground truth (live probe 2026-07-07):
//   POST without Origin   -> 200 application/json, JSON-RPC result, no CORS, no session id
//   POST with Origin      -> 403 "invalid Origin for MCP request"  => strip Origin/Host/Referer
//   OPTIONS               -> 405 (allow: GET,HEAD,POST)            => synthesize preflight locally
//   body content-type     -> application/json OR text/event-stream => stream the RESPONSE untouched

// The one and only upstream. Not user-controllable — do not read this from the
// request path/query/headers. That property is what keeps this from being an open proxy.
const UPSTREAM = "https://jbotci.app/mcp";

// Fallback CORS allowlist when env.ALLOWED_ORIGINS is unset/blank: the public
// playground origin only. Local dev (`just ui` on http://localhost:8080) is NOT in the
// code default on purpose — a forgotten prod var must not silently grant localhost.
// For local `wrangler dev`, add localhost via `.dev.vars` (see .dev.vars.example).
const DEFAULT_ALLOWED_ORIGINS = "https://dhilipsiva.dev";

// The request-header set the browser client actually sends, advertised in the
// preflight's Access-Control-Allow-Headers when the browser does not enumerate its own.
const FALLBACK_ALLOW_HEADERS =
  "content-type, accept, mcp-protocol-version, mcp-session-id";

// Methods advertised to the browser. GET/HEAD/POST/DELETE are forwarded upstream for
// MCP Streamable-HTTP completeness; OPTIONS is answered locally. (jbotci itself 405s
// DELETE — that is passed through transparently.)
const ALLOW_METHODS = "GET, HEAD, POST, DELETE, OPTIONS";

// Response headers browser JS must be able to READ. The session id lives here.
const EXPOSE_HEADERS = "mcp-session-id";

// Hard cap on a forwarded request body. MCP JSON-RPC messages are tiny; this bounds any
// amplification through the proxy. 256 KiB is far above any real MCP payload.
const MAX_BODY_BYTES = 256 * 1024;

// Request headers forwarded UPSTREAM. Everything else — origin, host, referer,
// cookie, authorization, cf-* — is dropped by omission, so jbotci sees a clean
// server-to-server call (the whole reason a browser Origin otherwise 403s).
const FORWARD_REQUEST_HEADERS = new Set([
  "content-type",
  "accept",
  "mcp-protocol-version",
  "mcp-session-id",
]);

// Upstream response headers copied BACK to the browser. Strict allow-list: anything
// unnamed is dropped, so no upstream infra fingerprint (Server/cf-ray/rndr-id/...) or
// stale transfer framing leaks. We deliberately do NOT copy content-length /
// content-encoding / transfer-encoding: the runtime re-frames the re-streamed body
// itself, and echoing those would describe a body that no longer exists on the wire.
const PASSTHROUGH_RESPONSE_HEADERS = new Set([
  "content-type", // JSON vs text/event-stream: the client branches on this
  "mcp-session-id", // session persistence
  "cache-control",
  "location", // so a (never-expected) upstream 3xx is at least coherent
]);

// Parse env.ALLOWED_ORIGINS (comma-separated) into { wildcard, origins }.
// The literal "*" anywhere means "allow any origin".
function parseAllowlist(env) {
  const raw =
    env && typeof env.ALLOWED_ORIGINS === "string" && env.ALLOWED_ORIGINS.trim() !== ""
      ? env.ALLOWED_ORIGINS
      : DEFAULT_ALLOWED_ORIGINS;
  const entries = raw
    .split(",")
    .map((s) => s.trim())
    .filter(Boolean);
  return { wildcard: entries.includes("*"), origins: new Set(entries) };
}

// Decide the Access-Control-Allow-Origin value for a request Origin, or null when the
// origin is absent (server-to-server) or not allowed. We never emit a bare "*": no
// credentials are used, so echoing the concrete Origin (with Vary: Origin) is correct,
// cache-safe, and identical in behavior whether or not "*" is configured.
function resolveAllowedOrigin(requestOrigin, allowlist) {
  if (!requestOrigin) return null; // curl / server-to-server — no CORS needed
  if (allowlist.wildcard) return requestOrigin;
  if (allowlist.origins.has(requestOrigin)) return requestOrigin;
  return null;
}

// CORS headers for a browser-facing response. When allowedOrigin is null (origin not
// on the list, or no Origin at all) we omit Access-Control-Allow-Origin entirely — the
// browser then blocks the JS read, while curl/server-to-server still works.
function corsHeaders(allowedOrigin) {
  const h = new Headers();
  h.set("Vary", "Origin");
  if (allowedOrigin) {
    h.set("Access-Control-Allow-Origin", allowedOrigin);
    h.set("Access-Control-Expose-Headers", EXPOSE_HEADERS);
  }
  return h;
}

// Synthesize the CORS preflight locally. jbotci 405s OPTIONS, so we must answer it
// ourselves and must NEVER forward it upstream.
function handlePreflight(request, allowedOrigin) {
  const h = corsHeaders(allowedOrigin);
  if (allowedOrigin) {
    h.set("Access-Control-Allow-Methods", ALLOW_METHODS);
    // Echo the browser's requested headers when present (most permissive + always
    // correct), else fall back to the known-good static set.
    const requested = request.headers.get("Access-Control-Request-Headers");
    h.set("Access-Control-Allow-Headers", requested || FALLBACK_ALLOW_HEADERS);
    // Chromium clamps preflight cache to 7200s; declare the honest ceiling.
    h.set("Access-Control-Max-Age", "7200");
  }
  // No credentials => deliberately no Access-Control-Allow-Credentials.
  // 204 No Content is the conventional preflight status.
  return new Response(null, { status: 204, headers: h });
}

// Graceful native rate limit. Returns true when the request may proceed. No-op when the
// binding is absent (e.g. a `wrangler dev` build without ratelimit emulation), so local
// verification still works. Keyed by client IP. Fails OPEN on any limiter error — a
// limiter fault must not take the proxy down.
async function allowByRateLimit(request, env) {
  if (!env || !env.RATE_LIMITER || typeof env.RATE_LIMITER.limit !== "function") {
    return true;
  }
  const key = request.headers.get("cf-connecting-ip") || "anonymous";
  try {
    const { success } = await env.RATE_LIMITER.limit({ key });
    return success;
  } catch {
    return true;
  }
}

// Build the upstream header set: only the explicit forward-list survives; origin/host/
// referer/cookie/authorization/cf-* are dropped by omission.
function buildUpstreamHeaders(request) {
  const out = new Headers();
  for (const [name, value] of request.headers) {
    if (FORWARD_REQUEST_HEADERS.has(name.toLowerCase())) out.set(name, value);
  }
  return out;
}

// A JSON error response that still carries CORS so the browser can read it.
function jsonError(status, message, allowedOrigin, extraHeaders) {
  const h = corsHeaders(allowedOrigin);
  h.set("content-type", "application/json");
  if (extraHeaders) for (const [k, v] of Object.entries(extraHeaders)) h.set(k, v);
  return new Response(JSON.stringify({ error: message }), { status, headers: h });
}

export default {
  async fetch(request, env, _ctx) {
    const allowlist = parseAllowlist(env);
    const requestOrigin = request.headers.get("Origin");
    const allowedOrigin = resolveAllowedOrigin(requestOrigin, allowlist);

    // 1) Preflight — answered locally, before anything else. Never forwarded upstream.
    if (request.method === "OPTIONS") {
      return handlePreflight(request, allowedOrigin);
    }

    // 2) Method guard. Only these are ever forwarded (OPTIONS handled above).
    const method = request.method;
    if (!["GET", "HEAD", "POST", "DELETE"].includes(method)) {
      return jsonError(405, "method not allowed", allowedOrigin, { Allow: ALLOW_METHODS });
    }

    // 3) Light rate limit (graceful no-op when the binding is missing).
    if (!(await allowByRateLimit(request, env))) {
      return jsonError(429, "rate limit exceeded", allowedOrigin, { "Retry-After": "60" });
    }

    // 4) Forward to the FIXED upstream. The client POSTs to its proxy_url verbatim
    //    (any path — /mcp or /). We ignore the incoming path entirely and always target
    //    jbotci's fixed /mcp, keeping the target non-user-controllable.
    const hasBody = method !== "GET" && method !== "HEAD";

    // Buffer the (tiny) request body before forwarding. MCP JSON-RPC messages are small
    // and the browser client already buffers, so streaming the request upstream buys
    // nothing — and a streamed body forces chunked Transfer-Encoding with no
    // Content-Length, a DIFFERENT framing than the curl-verified 200 that some HTTP
    // stacks reject. Buffering reproduces the exact framing verified against jbotci and
    // lets us enforce a size cap. (Only the request is buffered; the RESPONSE still
    // streams — that is the SSE-critical path.)
    let bodyBytes;
    if (hasBody) {
      const buf = await request.arrayBuffer();
      if (buf.byteLength > MAX_BODY_BYTES) {
        return jsonError(413, "request body too large", allowedOrigin);
      }
      bodyBytes = buf;
    }

    const upstreamRequest = new Request(UPSTREAM, {
      method,
      headers: buildUpstreamHeaders(request),
      body: hasBody ? bodyBytes : undefined,
      redirect: "manual", // never chase an upstream redirect to another host
    });

    let upstream;
    try {
      upstream = await fetch(upstreamRequest);
    } catch (_err) {
      return jsonError(502, "upstream fetch failed", allowedOrigin);
    }

    // 5) Re-wrap: stream the body through with a fresh curated header set + CORS.
    //    Status is passed through FAITHFULLY — the client depends on 200/202/404
    //    semantics (202 notifications, 404-with-session resets its session).
    const responseHeaders = corsHeaders(allowedOrigin);
    for (const [name, value] of upstream.headers) {
      if (PASSTHROUGH_RESPONSE_HEADERS.has(name.toLowerCase())) {
        responseHeaders.set(name, value);
      }
    }

    return new Response(upstream.body, {
      status: upstream.status,
      statusText: upstream.statusText,
      headers: responseHeaders,
    });
  },
};
