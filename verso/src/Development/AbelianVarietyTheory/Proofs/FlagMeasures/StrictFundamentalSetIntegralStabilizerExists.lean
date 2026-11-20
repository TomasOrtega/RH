import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

noncomputable section
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X Y u t`. Take `⟨K, hK⟩ : ∃ Ω, IsSFund X.B.I (ROinf t) Ω` from `Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u t`. Use `set Γ0 := Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) t.lam t.lam' t.lin with hΓ0`. Use `⟨K, hK.1, fun r _ => ?_⟩` and prove the remaining obligations. Take `⟨s0, hs0, hs0F⟩` from `hK.2.1 r`.

Use `⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩` and prove the remaining obligations. Establish `h2 : (s0 * s'⁻¹) * (s' * r) ∈ K` using `by simpa [mul_assoc] using hs0F`. Use `hK.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2` as an intermediate fact. Conclude with `(mul_inv_eq_one.1 this).symm`.
-/
theorem fundC_holds : FundC := by
  intro D X Y u t
  obtain ⟨K, hK⟩ : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u t
  set Γ0 := Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) t.lam t.lam' t.lin with hΓ0
  refine ⟨K, hK.1, fun r _ => ?_⟩
  obtain ⟨s0, hs0, hs0F⟩ := hK.2.1 r
  refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
  have h2 : (s0 * s'⁻¹) * (s' * r) ∈ K := by simpa [mul_assoc] using hs0F
  have := hK.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
  exact (mul_inv_eq_one.1 this).symm

end GlobalTheory.TypeAsm
