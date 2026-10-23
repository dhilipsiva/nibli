module
public import StdStrings
@[expose] public section

/- An explicit stream/digest boundary for standard collection hashing. The
   digest is a parameter: this does not claim to implement SipHash, randomness,
   collision resistance, or any Nibli quotation identity. Collection contracts
   expose equality and membership independently of physical hash buckets. -/
namespace NibliSelfCheck.StdHash

open Aeneas Aeneas.Std

abbrev Digest := List U8 → U64

structure State where
  digest : Digest
  input : List U8

def build (digest : Digest) : Result State := .ok ⟨digest, []⟩

def write (state : State) (chunk : Slice U8) : Result State :=
  .ok { state with input := state.input ++ chunk.val }

def finish (state : State) : Result U64 := .ok (state.digest state.input)

def interface : core.hash.Hasher State := { write, finish }

/-- Rust string hashing feeds UTF-8 bytes followed by the 0xff delimiter. -/
def hashString {H : Type} (hasher : core.hash.Hasher H) (s : String) (state : H) : Result H := do
  let view ← StdStrings.borrow s
  let state ← hasher.write state view
  hasher.write state (.from [255#u8] (by scalar_tac))

theorem build_spec (digest : Digest) :
    build digest ⦃ state => state.digest = digest ∧ state.input = [] ⦄ := by
  simp [build]

theorem write_spec (state : State) (chunk : Slice U8) :
    write state chunk ⦃ result => result.digest = state.digest ∧ result.input = state.input ++ chunk.val ⦄ := by
  simp [write]

theorem finish_spec (state : State) :
    finish state ⦃ result => result = state.digest state.input ⦄ := by
  simp [finish]

theorem hash_string_stream (s : String) (hfits : StdStrings.Fits s) (state : State) :
    hashString interface s state ⦃ result => result.digest = state.digest ∧
      result.input = state.input ++ StdStrings.bytes s ++ [255#u8] ⦄ := by
  unfold hashString
  step with StdStrings.borrow_spec s hfits as ⟨view, hview, hlength, hbytes⟩
  simp [interface, write, hbytes]

theorem hash_string_digest (s : String) (hfits : StdStrings.Fits s) (state : State) :
    (do let updated ← hashString interface s state; finish updated) ⦃ result =>
      result = state.digest (state.input ++ StdStrings.bytes s ++ [255#u8]) ⦄ := by
  step with hash_string_stream s hfits state as ⟨updated, hdigest, hinput⟩
  simp [finish, hdigest, hinput]

end NibliSelfCheck.StdHash
