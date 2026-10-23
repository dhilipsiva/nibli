module
public import Aeneas
@[expose] public section

/- Primitive-library models for the named stratifier. The contracts
   below prove properties of these definitions, not of Rust's standard-library
   implementation. The named extraction uses them through a reviewed boundary.
   Allocation success remains conditional on the library/resource boundary. -/
namespace NibliSelfCheck.StdStrings

open Aeneas Aeneas.Std

def bytes (s : String) : List U8 :=
  s.toByteArray.data.toList.map (fun byte =>
    ⟨byte.toNat, by cases byte; simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]; omega⟩)

def nativeBytes (s : Str) : ByteArray :=
  ⟨(s.val.map (fun byte => UInt8.ofNat byte.val)).toArray⟩

/-- Exact UTF-8 bytes, without normalization, case folding or NUL termination. -/
def Represents (view : Str) (s : String) : Prop := nativeBytes view = s.toByteArray

/-- Rust's byte-vector allocation limit, in the extracted target's word size. -/
def Fits (s : String) : Prop := s.utf8ByteSize ≤ Isize.max.toNat

instance (s : String) : Decidable (Fits s) := inferInstanceAs (Decidable (_ ≤ _))

def borrow (s : String) : Result Str :=
  if h : (bytes s).length ≤ Usize.max then .ok (.from (bytes s) h)
  else .fail .maximumSizeExceeded

def fromStr (view : Str) : Result String :=
  if h : (nativeBytes view).IsValidUTF8 then
    let s := String.ofByteArray (nativeBytes view) h
    if Fits s then .ok s else .fail .maximumSizeExceeded
  else .fail .undef

def pushStr (s : String) (view : Str) : Result String := do
  let suffix ← fromStr view
  if Fits (s ++ suffix) then .ok (s ++ suffix) else .fail .maximumSizeExceeded

def clone (s : String) : Result String :=
  if Fits s then .ok s else .fail .maximumSizeExceeded

def equal (left right : String) : Result Bool := .ok (decide (left = right))

/-- Rust string ordering compares unsigned UTF-8 bytes lexicographically. -/
def compareBytes (left right : String) : Result Ordering :=
  .ok (compare left.toByteArray.data.toList right.toByteArray.data.toList)

theorem bytes_length (s : String) : (bytes s).length = s.utf8ByteSize := by
  simp only [bytes, List.length_map, Array.length_toList]
  rfl

theorem bytes_round_trip (s : String) (h : (bytes s).length ≤ Usize.max) :
    Represents (.from (bytes s) h) s := by
  unfold Represents nativeBytes
  simp only [Slice.from_val, bytes, List.map_map]
  change { data := (s.toByteArray.data.toList.map (fun byte : UInt8 => UInt8.ofNat byte.toNat)).toArray } = s.toByteArray
  have hid : (fun byte : UInt8 => UInt8.ofNat byte.toNat) = id := by
    funext byte
    simp
  simp only [hid, List.map_id, Array.toArray_toList]

theorem represents_unique {view : Str} {left right : String}
    (hleft : Represents view left) (hright : Represents view right) : left = right := by
  exact String.toByteArray_inj.mp (hleft.symm.trans hright)

theorem borrow_spec (s : String) (h : Fits s) :
    borrow s ⦃ view => Represents view s ∧ view.length = s.utf8ByteSize ∧ view.val = bytes s ⦄ := by
  have hsize : (bytes s).length ≤ Usize.max := by
    rw [bytes_length]
    unfold Fits at h
    have hbound : Isize.max.toNat ≤ Usize.max := by
      have hbits := System.Platform.numBits_eq
      rcases hbits with hbits | hbits <;> simp [Isize.max, Isize.numBits, Usize.max, Usize.numBits, hbits]
    omega
  rw [borrow, dite_eq_left hsize]
  change (Result.ok (.from (bytes s) hsize) : Result (Slice U8))
    ⦃ view => Represents view s ∧ view.length = s.utf8ByteSize ∧ view.val = bytes s ⦄
  simp only [WP.spec_ok]
  exact ⟨bytes_round_trip s hsize, by simp [Slice.length, bytes_length], by simp⟩

theorem from_str_eq (view : Str) (s : String) (hview : Represents view s) (hfits : Fits s) :
    fromStr view = .ok s := by
  unfold Represents at hview
  have hvalid : (nativeBytes view).IsValidUTF8 := by rw [hview]; exact s.isValidUTF8
  have hstring : String.ofByteArray (nativeBytes view) hvalid = s := by
    apply String.toByteArray_inj.mp
    exact hview
  simp only [fromStr, hvalid, ↓reduceDIte, hstring, hfits, ↓reduceIte]

theorem from_str_spec (view : Str) (s : String) (hview : Represents view s) (hfits : Fits s) :
    fromStr view ⦃ result => result = s ⦄ := by
  rw [from_str_eq view s hview hfits]
  simp

theorem push_str_spec (s suffix : String) (view : Str)
    (hview : Represents view suffix) (hfits : Fits (s ++ suffix)) :
    pushStr s view ⦃ result => result = s ++ suffix ∧
      result.toByteArray = s.toByteArray ++ suffix.toByteArray ⦄ := by
  have hsuffix : Fits suffix := by
    unfold Fits at *
    rw [String.utf8ByteSize_append] at hfits
    omega
  unfold pushStr
  step with from_str_spec view suffix hview hsuffix as ⟨actual, hactual⟩
  subst actual
  simp [hfits, String.toByteArray_append]

theorem clone_spec (s : String) (h : Fits s) : clone s ⦃ result => result = s ⦄ := by
  simp [clone, h]

theorem equal_spec (left right : String) :
    equal left right ⦃ result => (result = true ↔ left = right) ⦄ := by
  simp [equal]

theorem compare_bytes_spec (left right : String) :
    compareBytes left right ⦃ result =>
      result = compare left.toByteArray.data.toList right.toByteArray.data.toList ⦄ := by
  simp [compareBytes]

theorem compare_bytes_equal_iff (left right : String) :
    compareBytes left right ⦃ result => (result = .eq ↔ left = right) ⦄ := by
  simp only [compareBytes, WP.spec_ok, Std.compare_eq_iff_eq, Array.toList_inj]
  constructor
  · intro h
    apply String.toByteArray_inj.mp
    cases hleft : left.toByteArray
    cases hright : right.toByteArray
    simp_all
  · intro h
    simp [h]

theorem from_str_invalid (view : Str) (h : ¬ (nativeBytes view).IsValidUTF8) :
    fromStr view = .fail .undef := by simp [fromStr, h]

theorem clone_too_large (s : String) (h : ¬ Fits s) :
    clone s = .fail .maximumSizeExceeded := by simp [clone, h]

theorem push_str_too_large (s suffix : String) (view : Str)
    (hview : Represents view suffix) (hsuffix : Fits suffix) (h : ¬ Fits (s ++ suffix)) :
    pushStr s view = .fail .maximumSizeExceeded := by
  simp [pushStr, from_str_eq view suffix hview hsuffix, h]

end NibliSelfCheck.StdStrings
