import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist

noncomputable section

namespace GlobalTheory.AdelicLatticeClosure

open NumberField IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Unfold `GlobalTheory.AdLat.hat1 at hz hw ⊢`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Proceed by induction on `hw using AddSubgroup.closure_induction with`.

Consider the case `mem w hw`. Take `⟨b, hb, y, hy, rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x * y, hJ x hx y hy, ?_⟩` and prove the remaining obligations. Conclude with `mul_mem (ha v) (hb v)`. Conclude with `Algebra.TensorProduct.tmul_mul_tmul a b x y`.

Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv => rw [mul_add]`. Conclude with `add_mem hu hv`. Consider the case `neg u _ hu => rw [mul_neg]`.

Conclude with `neg_mem hu`. Consider the case `zero => rw [zero_mul]`. Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv => rw [add_mul]`. Conclude with `add_mem hu hv`.

Consider the case `neg u _ hu => rw [neg_mul]`. Conclude with `neg_mem hu`.
-/
theorem adelic_hat_mul_of_mul_closed {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (J : Set E) (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J) {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F J) (hw : w ∈ GlobalTheory.AdLat.hat1 F J) :
    z * w ∈ GlobalTheory.AdLat.hat1 F J := by
  unfold GlobalTheory.AdLat.hat1 at hz hw ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x * y, hJ x hx y hy, ?_⟩
      · exact mul_mem (ha v) (hb v)
      · exact Algebra.TensorProduct.tmul_mul_tmul a b x y
    | zero => rw [mul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | neg u _ hu => rw [mul_neg]; exact neg_mem hu
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

/- English proof (translation)
Use `adelic_hat_mul_of_mul_closed _ ?_ hz hw` and prove the remaining obligations. Introduce `x hx y hy`. Take `⟨a, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hx`. Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hy`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨a * b, map_mul _ a b⟩`.
-/
theorem adelic_hat_one_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E))
    (hw : w ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) :
    z * w ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
  refine adelic_hat_mul_of_mul_closed _ ?_ hz hw
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
  exact (FractionalIdeal.mem_one_iff _).2 ⟨a * b, map_mul _ a b⟩

end GlobalTheory.AdelicLatticeClosure
