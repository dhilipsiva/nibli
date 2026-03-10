# nibli

**lo na xanri ke logji birti ciste**

ni'o la .nibli. cu logji birti ciste noi se zbasu fi lo ueb.asemblii. (WASI P2) .i la .nibli. cu fanva lo lojbo se cusku fi lo pamoi mekso logji .ije cu logji jalge fi lo se nitcu ke jersi sisku ciste .i ro jalge cu se krinu lo logji — noda se xanri .i noda se jibni

> *nibli* (lojbo): x1 logji nibli lo du'u x2 kei fi lo javni be x3

## ni'o lo pruce

```
lo lojbo cusku ──→ lo valsi cpacu ──→ lo gerna ciste (AST) ──→ lo smuni ciste (FOL IR) ──→ lo logji ciste (jersi sisku)
                        │                   │                         │                            │
                      logos              ke'a jmina               Skolem se cuxna          se nitcu jersi sisku
                    pagbu cpana        gerna tcidu             SkolemFn se birti        fatci vlaste + javni
```

ni'o mu lo ueb.asemblii. pagbu cu se lasna fi lo WIT jupku'a .ije se zbasu fi lo pa jukpa fasnu:

| pagbu | se zukte |
|-------|----------|
| **gerna** | lo lojbo cusku → AST → WIT pagbu kampu |
| **smuni** | lo AST pagbu kampu → FOL logji pagbu kampu |
| **logji** | lo FOL logji pagbu → se nitcu jersi sisku .e se jivna |
| **lasna** | lasna: gerna → smuni → logji |
| **gasnu** | lo samciste Wasmtime .e lo REPL .e lo TCP jikca ciste |

## ni'o lo cfari

### se nitcu

- [Nix](https://nixos.org/download.html) (ro tutci — rustc, cargo-component, wac, just, wasmtime — se zbasu fi lo `flake.nix`)

### zbasu je gasnu

```bash
# ko nerkla lo tutci canlu
nix --extra-experimental-features 'nix-command flakes' develop

# ko zbasu ro pagbu .ije lasna .ije cfari lo REPL
just run

# ko troci ro cipra
just test
```

### lo REPL se pilno

```
~/nibli〉lo gerku cu barda
[Fact #1] Asserted.

~/nibli〉? lo gerku cu barda
[Query] TRUE

~/nibli〉ro lo gerku cu danlu
[Fact #2] Asserted.

~/nibli〉? la .alis. gerku .ije ? la .alis. danlu
[Query] TRUE

~/nibli〉?! la .alis. danlu
[Proof]
  Derived (gerku → danlu): (Pred "danlu" (Cons (Const "alis") (Nil))) → TRUE
    Asserted: (Pred "gerku" (Cons (Const "alis") (Nil))) → TRUE

~/nibli〉?? da gerku
[Witnesses] da = alis

~/nibli〉:debug re lo gerku cu barda
[Logic] (Count "_v0" 2 (And (Pred "gerku" ...) (Pred "barda" ...)))

~/nibli〉:assert tenfa 8 2 3
[Fact #3] tenfa(8, 2, 3) asserted.

~/nibli〉:facts
[Facts] 3 active fact(s):
  #1: lo gerku cu barda (1 root(s))
  #2: ro lo gerku cu danlu (1 root(s))
  #3: :assert tenfa (1 root(s))

~/nibli〉:retract 1
[Retract] Fact #1 retracted. KB rebuilt.

~/nibli〉:load readme.lojban
[Fact #1] la .nibli. cu logji ciste
[Fact #2] la .nibli. cu birti ciste
...
[Load] Done: 82 asserted, 31 skipped, 0 errors

~/nibli〉:reset
[Reset] Knowledge base cleared.
```

## ni'o lo skami tutci

- **bangu:** Rust (stabli)
- **ueb.asemblii.:** WASI Preview 2 Component Model (cargo-component + wac)
- **se gasnu:** Wasmtime
- **logji ciste:** se nitcu jersi sisku (backward-chaining) joi fatci vlaste (fact index)
- **valsi cpacu:** Logos
- **vlaste:** Perfect Hash Function (PHF) noi se zbasu nenri lo fasnu
- **tutci canlu:** Nix flake
- **skami jikca:** TCP + JSON Lines (sampu protokol, ro bangu ka'e pilno)
- **fasnu gasnu:** Just

## ni'o lo lojbo se smuni

- lo gadri ke se smuni: `lo` (fatci da poi), `le` (lo se smuni poi mi jinvi), `la` (cmene → Constant); `ro lo` / `ro le` (ro da poi); `PA lo` / `PA le` / `su'o lo`
- lo sumti stuzi cmavo (`fa`/`fe`/`fi`/`fo`/`fu`), BAI tcita (`ri'a`, `ni'i`, `mu'i`, `ki'u`, `pi'o`, `ba'i`), `fi'o`...`fe'u`
- lo selbri: jicmu, tanru (Neo-Davidsonian nu'i ciste — lo nu fasnu ka'e se pilno fi lo ka cpacu lo drata intersektiv xlali), nunfanva (`se`/`te`/`ve`/`xe`), natfe (`na`), girzu (`ke`...`ke'e`), lujvo (`zei`), `be`...`bei`...`be'o`
- lo poi/noi/voi ke'a pe lo sumti, joi lo ka jmina lo se smuni
- lo sumti jo'u (`.e`/`.a`/`.o`/`.u` + `nai`), lo selbri jo'u (`je`/`ja`/`jo`/`ju`)
- lo bridi jo'u (lidne: `ge`...`gi`, `ga`...`gi`, `ganai`...`gi`; jersi: `.i je`/`ja`/`jo`/`ju` joi `na`/`nai`)
- lo nu'a (`nu`, `du'u`, `ka` joi `ce'u`, `ni`, `si'o`)
- lo tcika (`pu`/`ca`/`ba`) joi lo dunli satci ke tcika javni, lo ei/e'e ke deontic cinmo
- lo na se cusku bridi (zilkai `go'i`), lo go'i selbri
- lo `ma` preti sumti — se fanva fi lo da poi se jivna
- lo lu...li'u se cusku, lo li + PA namcu sumti

## ni'o lo logji ciste

- Skolem nunfanva (zilkai + se nitcu poi se jibni lo `ro` fi la SkolemFn + DepPair)
- ro lo `ro` javni cu se fanva fi lo jersi sisku javni (UniversalRuleRecord)
- se nitcu jersi sisku ciste joi lo fatci vlaste (asserted_sexps) joi lo javni se sisku
- lo namcu jivna: `zmadu` (>), `mleca` (<), `dunli` (==) fi lo `Num`
- lo skami jikca: `compute-backend` WIT protokol, `ComputeNode` IR klesi
- lo slabu namcu: `pilji` (pi'i), `sumji` (su'i), `dilcu` (fe'i) joi lo skami jikca
- lo TCP jikca: sampu JSON Lines protokol, lazni jikca, ri jikca
- lo skami jalge se jmina: lo jalge cu se jmina fi lo se slabu fatci (se krinu → skami → se krinu pruce)
- lo fatci se jmina: `assert-fact` WIT fasnu + `:assert` REPL fasnu
- lo na monotoni logji: lo fatci se vimcu fi lo fatci liste + ri zbasu; `:retract <id>` .e `:facts` REPL fasnu
- lo se birti se sisku: `query-find` cu se benji ro lo se birti sumti (`??` REPL lidne)
- lo krinu ciste: `query-entailment-with-proof` cu se benji lo krinu tricu (15 krinu klesi) — `?!` REPL lidne
- lo krefu nibli krinu: lo krinu tricu cu ri sisku fi lo `ro` javni; `Asserted` ke jicmu fatci cu se jinvi drata lo `Derived` ke se nibli jalge
- lo gerna ri zbasu: lo bridi poi se fliba cu se srera .ije cfari lo jersi bridi; lo se srera cu se cusku lo rajypau linsi stuzi
- lo tcika logji: `Past`/`Present`/`Future` fi lo fatci vlaste; lo tcika javni cu jmina lo tcika fi lo jicmu javni
- lo Neo-Davidsonian nu'i smuni: ro bridi cu se pagbu fi lo nu fasnu klesi + lo se zukte sumti; lo tanru cu te pilno lo nu fasnu ka'e
- lo junri je se jmina: `And(A, B)` se nibli ze'a lo re bridi cu pilno lo simxu `InDomain` sumti (se fanta lo cmalu explosi)
- lo WIT srera klesi: `nibli-error` (`syntax`/`semantic`/`reasoning`/`backend`); lo gerna srera cu se cusku lo linsi stuzi
- lo WASM se banro: lo REPL fasnu se banro; `NIBLI_FUEL` .e `:fuel` REPL fasnu
- lo satci se banro: `NIBLI_RUN_BOUND` (100 zilkai) .e `:saturate` REPL fasnu (WIT API se ponse)
- lo tcana se samtci: `:load <datnyvei>` cu jmina ro bridi fi lo `.lojban` datnyvei; lo `#` lerpoi cu se vimcu

## ni'o lo skami jikca

ni'o la .nibli. cu jikca lo drata skami jikca fi lo TCP joi JSON Lines protokol .i ro pruce (Python, Node.js, Rust, drata) ka'e se pilno

```bash
# lo pamoi skami canlu: ko cfari lo Python jikca
just backend

# lo remoi skami canlu: ko cfari la .nibli. joi lo jikca
just run-with-backend

# lo REPL nenri:
:compute tenfa                      # ko jmina lo tenfa fi lo skami jikca
li bi tenfa li re li ci             # ko cusku: 8 = 2^3
? li bi tenfa li re li ci           # ko preti: JETNU (se skami fi lo Python)
```

ni'o ko se pilno lo `NIBLI_COMPUTE_ADDR=host:port` a lo `:backend host:port` fi lo REPL .i vi lo na jikca lo slabu namcu ciste cu se pilno

## ni'o lo midju platu

ni'o ko viska lo `todo.md` fi lo roldza platu (pagbu 1-5) .e lo se zukte .e lo skami srera liste

## ni'o lo javni se curmi

ni'o ko viska lo `LICENSE` fi lo se cusku
