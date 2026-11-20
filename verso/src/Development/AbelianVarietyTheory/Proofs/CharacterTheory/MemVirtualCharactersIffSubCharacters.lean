import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAddStatement
open GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Take `⟨h0, hadd⟩` from `GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G`. Unfold `Virt`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Proceed by induction on `hf using AddSubgroup.closure_induction with`.

Consider the case `mem x hx => exact ⟨x, 0, hx, h0, (sub_zero x).symm⟩`. Consider the case `zero => exact ⟨0, 0, h0, h0, (sub_zero 0).symm⟩`. Consider the case `add x y _ _ ihx ihy`. Take `⟨a, b, ha, hb, rfl⟩` from `ihx`. Take `⟨c, d, hc, hd, rfl⟩` from `ihy`.

Conclude with `⟨a + c, b + d, hadd a c ha hc, hadd b d hb hd, by abel⟩`. Consider the case `neg x _ ih`. Take `⟨a, b, ha, hb, rfl⟩` from `ih`. Conclude with `⟨b, a, hb, ha, by abel⟩`. Introduce and unpack `⟨a, b, ha, hb, rfl⟩`.

Conclude with `AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ha) (AddSubgroup.subset_closure hb)`.
-/
theorem mem_virt_iff_sub (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L) :
    f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  obtain ⟨h0, hadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G
  unfold Virt
  constructor
  · intro hf
    induction hf using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨x, 0, hx, h0, (sub_zero x).symm⟩
    | zero => exact ⟨0, 0, h0, h0, (sub_zero 0).symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ihx
      obtain ⟨c, d, hc, hd, rfl⟩ := ihy
      exact ⟨a + c, b + d, hadd a c ha hc, hadd b d hb hd, by abel⟩
    | neg x _ ih =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ih
      exact ⟨b, a, hb, ha, by abel⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ha) (AddSubgroup.subset_closure hb)
end GlobalTheory.BI
