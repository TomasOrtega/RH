import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.PolDet

/- English proof (translation)
Simplify using `only [Matrix.det_apply', Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]`. Repeatedly rewrite using `[Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_sum_smul_eq {D : ℕ} (x : Fin D → ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    (∑ i, x i • H i).det =
      ∑ m : Fin D → Fin D, (∏ l, x (m l)) * (Matrix.of fun j l => H (m l) j l).det := by
  simp only [Matrix.det_apply', Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp_rw [Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

/- English proof (translation)
Use `set T := Finset.univ.image m with hT`. Establish `h1 : ∀ S : Finset (Fin D), ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) = (-1 : ℂ) ^ D * ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0)`. Introduce `S`. Rewrite using `[Finset.prod_ite_zero, Finset.prod_ite_zero]`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_ite, mul_one, mul_zero, Finset.mem_sdiff, Finset.mem_univ, true_and, hT, Finset.mem_image]`.

Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h i hi ⟨l, rfl⟩`. Conclude with `hi (h l trivial)`.

Introduce `h l _`. Assume the negation of the conclusion as `hl`. Conclude with `h (m l) hl ⟨l, rfl⟩`. Establish `h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) = ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0)`. Rewrite using `[Finset.prod_add, Finset.powerset_univ]`.

Simplify using `[Finset.prod_const]`. Establish `h3 : ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) = if Function.Surjective m then (-1 : ℂ) ^ D else 0`. Establish `: ∀ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) = if i ∈ T then (-1 : ℂ) else 0`. Apply the tactic sequence `intro i; by_cases hi : i ∈ T <;> simp [hi]`. Repeatedly rewrite using `[this]`.

Rewrite using `[Finset.prod_ite_zero]`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, true_implies, hT, Finset.mem_image, true_and]`. Conclude with `if_congr Iff.rfl rfl rfl`. Repeatedly rewrite using `[h1, mul_left_comm _ ((-1 : ℂ) ^ D), ← Finset.mul_sum, h2, h3]`. Apply the tactic sequence `split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]`.
-/
theorem coeff_eq {D : ℕ} (m : Fin D → Fin D) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) =
      if Function.Surjective m then 1 else 0 := by
  classical
  set T := Finset.univ.image m with hT
  have h1 : ∀ S : Finset (Fin D), ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) =
      (-1 : ℂ) ^ D * ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) := by
    intro S
    rw [Finset.prod_ite_zero, Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_ite, mul_one,
      mul_zero, Finset.mem_sdiff, Finset.mem_univ, true_and, hT, Finset.mem_image]
    congr 1
    apply propext
    constructor
    · rintro h i hi ⟨l, rfl⟩
      exact hi (h l trivial)
    · intro h l _
      by_contra hl
      exact h (m l) hl ⟨l, rfl⟩
  have h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card *
      ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) =
      ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) := by
    rw [Finset.prod_add, Finset.powerset_univ]
    simp [Finset.prod_const]
  have h3 : ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) =
      if Function.Surjective m then (-1 : ℂ) ^ D else 0 := by
    have : ∀ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) = if i ∈ T then (-1 : ℂ) else 0 := by
      intro i; by_cases hi : i ∈ T <;> simp [hi]
    simp_rw [this]
    rw [Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, true_implies,
      hT, Finset.mem_image, true_and]
    exact if_congr Iff.rfl rfl rfl
  simp_rw [h1, mul_left_comm _ ((-1 : ℂ) ^ D), ← Finset.mul_sum, h2, h3]
  split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]

/- English proof (translation)
Repeatedly rewrite using `[det_sum_smul_eq, Finset.mul_sum, ← mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_mul, coeff_eq, ite_mul, one_mul, zero_mul]`. Rewrite using `[← Finset.sum_filter]`. Use `symm`.

Use `Finset.sum_nbij (fun τ : Equiv.Perm (Fin D) => (τ : Fin D → Fin D)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ _`. Simplify using `using τ.surjective`. Introduce `τ _ σ _ h`. Conclude with `DFunLike.coe_injective h`.

Introduce `m hm`. Establish `hs : Function.Surjective m` using `by simpa using hm`. Conclude with `⟨Equiv.ofBijective m ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, by simp, rfl⟩`. Introduce `τ _`. Both sides reduce to the same expression.
-/
theorem polarisation_det (D : ℕ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det =
      ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := by
  classical
  simp_rw [det_sum_smul_eq, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, coeff_eq, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun τ : Equiv.Perm (Fin D) => (τ : Fin D → Fin D)) ?_ ?_ ?_ ?_
  · intro τ _
    simpa using τ.surjective
  · intro τ _ σ _ h
    exact DFunLike.coe_injective h
  · intro m hm
    have hs : Function.Surjective m := by simpa using hm
    exact ⟨Equiv.ofBijective m ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, by simp, rfl⟩
  · intro τ _
    rfl

end GlobalTheory.PolDet
