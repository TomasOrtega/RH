import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulVecEqZeroOfSubalgebra
open PowerSeries GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

/- English proof (translation)
Use `first`. Consider the case `(rename_i h_2 h_3 h_4 h_5 h_9 h_10 h_11 h_12; revert O S h_2 h_3 h_4 h_5 B ι κ h_9 h_10 h_11 h_12 M hM hinj w hw; exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra)`. Consider the case `exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra`. Consider the case `exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra`. Consider the case `(apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)`.

Consider the case `(intros; apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra ..)`.
-/
theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S] [Algebra O S]
    (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ ι S) (hM : ∀ i j, M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → M *ᵥ v = 0 → v = 0) (w : ι → S) (hw : M *ᵥ w = 0) :
    w = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_9 h_10 h_11 h_12; revert O S h_2 h_3 h_4 h_5 B ι κ h_9 h_10 h_11 h_12 M hM hinj w hw; exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra)
  | exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | (apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra ..)

end GlobalTheory.BK

/- English proof (translation)
Introduce `O K _ _ _ _ _ l e a _ ι κ μ _ _ _ _ _ _ P Q T F G hex`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`. Use function extensionality and compare the values at `τ`. Use `mulVec_eq_zero_of_subalgebra (A O K) (F.mat τ) (F.mem τ) ?_ (w τ) ?_` and prove the remaining obligations.

Introduce `v hv hMv`. Establish `hu : Pi.single τ v ∈ P.M` using `mem_tot.2 fun τ' => by`. Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Simplify using `using (mem_vecs.2 hv)`.

Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _`. Establish `h0 : F.app (Pi.single τ v) = 0`. Use function extensionality and compare the values at `τ'`. Rewrite using `[Hom.app_apply]`.

Distinguish the cases in `h : τ' = τ`. Substitute `h` using the available equality. Simplify using `using hMv`. Rewrite using `[Pi.single_eq_of_ne h, Matrix.mulVec_zero]`. Both sides reduce to the same expression.

Use `congrFun (hex.inj _ hu h0) τ` as an intermediate fact. Simplify using `using this`. Use `congrFun hw τ` as an intermediate fact. Rewrite `this` using `[Hom.app_apply]`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.BK.IsExactTriple.injective_app : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  intro O K _ _ _ _ _ l e a _ ι κ μ _ _ _ _ _ _ P Q T F G hex
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext τ
  refine mulVec_eq_zero_of_subalgebra (A O K) (F.mat τ) (F.mem τ) ?_ (w τ) ?_
  · intro v hv hMv
    have hu : Pi.single τ v ∈ P.M := mem_tot.2 fun τ' => by
      by_cases h : τ' = τ
      · subst h; simpa using (mem_vecs.2 hv)
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 : F.app (Pi.single τ v) = 0 := by
      funext τ'
      rw [Hom.app_apply]
      by_cases h : τ' = τ
      · subst h; simpa using hMv
      · rw [Pi.single_eq_of_ne h, Matrix.mulVec_zero]; rfl
    have := congrFun (hex.inj _ hu h0) τ
    simpa using this
  · have := congrFun hw τ
    rwa [Hom.app_apply] at this
