import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[toMK_inv]`. Use `hx.conjTranspose_mul_mul_same ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `h` using `congrArg (fun y => (toMK k)ᴴ.mulVec y) hab`. Simplify `h` using `only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec]`.
-/
theorem posDef_conj_toMK {ε : Fin n → Bool} (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

/- English proof (translation)
Unfold `muNext`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem muNext_add_smul (μ D : Fin n → ℤ) (t : ℤ) (i : Fin n) :
    muNext (μ + t • D) i = muNext μ i + t * muNext D i := by
  unfold muNext
  split_ifs <;> simp

/- English proof (translation)
Unfold `PhiM`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h0 : lead ((i : ℕ) + 1) y ≠ 0` using `hy i`. Rewrite using `[muNext_add_smul, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ h0]`.

Use `congr 1`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phiM_add_smul (μ D : Fin n → ℤ) (t : ℕ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ OmegaSet n) :
    PhiM (μ + (t : ℤ) • D) y = PhiM μ y * PhiM D y ^ t := by
  unfold PhiM
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : lead ((i : ℕ) + 1) y ≠ 0 := hy i
  rw [muNext_add_smul, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ h0]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `n ε μ t x hx k`. Establish `hy` using `posDef_conj_toMK k hx`. Establish `h1` using `phiM_posDef μ hy`. Establish `h2` using `phiM_posDef (Dz n) hy`. Use `⟨h1.1, ?_⟩` and prove the remaining obligations.

Unfold `phiK`. Rewrite using `[phiM_add_smul μ (Dz n) t (posSet_subset_omega hy)]`. Establish `e1 : PhiM μ (toMK k⁻¹ * x * toMK k) = ((PhiM μ (toMK k⁻¹ * x * toMK k)).re : ℂ)` using `Complex.ext (by simp) (by simp [h1.2])`. Establish `e2 : PhiM (Dz n) (toMK k⁻¹ * x * toMK k) = ((PhiM (Dz n) (toMK k⁻¹ * x * toMK k)).re : ℂ)` using `Complex.ext (by simp) (by simp [h2.2])`. Rewrite using `[e1, e2, ← Complex.ofReal_pow, ← Complex.ofReal_mul]`.

Simplify using `only [Complex.ofReal_re]`.
-/
theorem phiMul : PhiMul := by
  intro n ε μ t x hx k
  have hy := posDef_conj_toMK k hx
  have h1 := phiM_posDef μ hy
  have h2 := phiM_posDef (Dz n) hy
  refine ⟨h1.1, ?_⟩
  unfold phiK
  rw [phiM_add_smul μ (Dz n) t (posSet_subset_omega hy)]
  have e1 : PhiM μ (toMK k⁻¹ * x * toMK k) = ((PhiM μ (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h1.2])
  have e2 : PhiM (Dz n) (toMK k⁻¹ * x * toMK k) = ((PhiM (Dz n) (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h2.2])
  rw [e1, e2, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

end CompanionTheory.RgFd
