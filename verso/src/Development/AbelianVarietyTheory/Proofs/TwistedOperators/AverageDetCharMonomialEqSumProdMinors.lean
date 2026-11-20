import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAverageKillsFockComplementRelInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFockProjectionMaximalMinorsStatement

noncomputable section

open Classical MeasureTheory MvPolynomial

namespace GlobalTheory.MinorFrame.AvgCore

variable {ι : Type} [Fintype ι] {a d : ℕ}

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C c`. Introduce `Q`. Establish `h : ∀ G : ι → Fin a → Fin a → ℂ, colSub (d` using `d) (fun τ => Matrix.of (G τ)) (C c) = C c := by`. Introduce `G`.

Simplify using `[colSub, MvPolynomial.algebraMap_eq]`. Simplify using `only [h]`. Conclude with `continuous_const`. Consider the case `add p q hp hq`. Introduce `Q`.

Simplify using `only [map_add, add_mul]`. Conclude with `(hp Q).add (hq Q)`. Consider the case `mul_X p y hp`. Introduce `Q`. Establish `h : ∀ G : ι → Fin a → Fin a → ℂ, Λ (colSub (fun τ => Matrix.of (G τ)) (p * X y) * Q) = ∑ j' : Fin a, G y.1 j' y.2.2 * Λ (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j') * Q))`.

Introduce `G`. Establish `hX : colSub (d` using `d) (fun τ => Matrix.of (G τ)) (X y) = ∑ j' : Fin a, C (G y.1 j' y.2.2) * X (y.1, y.2.1, j') := by`. Simplify using `[colSub]`. Rewrite using `[map_mul (colSub (fun τ => Matrix.of (G τ))) p (X y), hX, Finset.mul_sum, Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[show colSub (fun τ => Matrix.of (G τ)) p * (C (G y.1 j y.2.2) * X (y.1, y.2.1, j)) * Q = C (G y.1 j y.2.2) * (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j) * Q)) by ring, ← smul_eq_C_mul, map_smul, smul_eq_mul]`. Simplify using `only [h]`. Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `Continuous.mul (by fun_prop) (hp _)`.
-/
theorem continuous_colSub_mul (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) : ∀ Q : Pol ι d a,
    Continuous (fun G : ι → Fin a → Fin a → ℂ => Λ (colSub (fun τ => Matrix.of (G τ)) P * Q)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, colSub (d := d) (fun τ => Matrix.of (G τ)) (C c) = C c := by
      intro G; simp [colSub, MvPolynomial.algebraMap_eq]
    simp only [h]
    exact continuous_const
  | add p q hp hq =>
    intro Q
    simp only [map_add, add_mul]
    exact (hp Q).add (hq Q)
  | mul_X p y hp =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, Λ (colSub (fun τ => Matrix.of (G τ)) (p * X y) * Q) =
        ∑ j' : Fin a, G y.1 j' y.2.2 * Λ (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j') * Q)) := by
      intro G
      have hX : colSub (d := d) (fun τ => Matrix.of (G τ)) (X y) =
          ∑ j' : Fin a, C (G y.1 j' y.2.2) * X (y.1, y.2.1, j') := by
        simp [colSub]
      rw [map_mul (colSub (fun τ => Matrix.of (G τ))) p (X y), hX, Finset.mul_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show colSub (fun τ => Matrix.of (G τ)) p * (C (G y.1 j y.2.2) * X (y.1, y.2.1, j)) * Q =
          C (G y.1 j y.2.2) * (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j) * Q)) by ring,
        ← smul_eq_C_mul, map_smul, smul_eq_mul]
    simp only [h]
    refine continuous_finset_sum _ fun j _ => ?_
    exact Continuous.mul (by fun_prop) (hp _)

/- English proof (translation)
Conclude with `CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary u.2)`.
-/
theorem norm_det_unitary (u : Matrix.unitaryGroup (Fin a) ℂ) : ‖(u : Matrix (Fin a) (Fin a) ℂ).det‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary u.2)

/- English proof (translation)
Set `F : (ι → Fin a → Fin a → ℂ) → ℂ` to `fun G => Λ (colSub (fun τ => Matrix.of (G τ)) P)`. Establish `hF : Continuous F` using `by simpa [F] using continuous_colSub_mul Λ P 1`. Set `e : K → (ι → Fin a → Fin a → ℂ)` to `fun g τ i j => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j`. Establish `he : Measurable e` using `measurable_pi_lambda _ fun τ => measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hmeas τ i j`. Establish `hFe : ∀ g, Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) = F (e g)` using `fun g => rfl`.

Establish `hdetc : ∀ τ, Continuous fun G : ι → Fin a → Fin a → ℂ => (Matrix.of (G τ)).det` using `fun τ => Continuous.matrix_det (continuous_apply τ)`. Establish `hdete : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det = (Matrix.of (e g τ)).det` using `fun g τ => rfl`. Take `⟨C, hC⟩` from `(isCompact_closedBall (0 : ι → Fin a → Fin a → ℂ) 1).exists_bound_of_continuousOn hF.continuousOn`. Establish `hball : ∀ g, e g ∈ Metric.closedBall (0 : ι → Fin a → Fin a → ℂ) 1`. Introduce `g`.

Rewrite using `[mem_closedBall_zero_iff]`. Use `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => entry_norm_bound_of_unitary (ρ g τ).2 i j` and prove the remaining obligations. Use `Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Use `Measurable.aestronglyMeasurable ?_` and prove the remaining obligations. Simplify using `only [hFe, hdete]`.

Use `Measurable.mul ?_ (hF.measurable.comp he)` and prove the remaining obligations. Use `Finset.measurable_prod _ fun τ _ => ?_` and prove the remaining obligations. Conclude with `Measurable.pow_const ((hdetc τ).measurable.comp he) _`. Rewrite using `[norm_mul, norm_prod]`. Simplify using `only [norm_zpow, norm_det_unitary, one_zpow, Finset.prod_const_one, one_mul, hFe]`.

Conclude with `hC _ (hball g)`.
-/
theorem integrable_avg {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hmeas : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (z : ι → ℤ)
    (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) :
    Integrable (fun g => (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (z τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)) ν := by
  let F : (ι → Fin a → Fin a → ℂ) → ℂ := fun G => Λ (colSub (fun τ => Matrix.of (G τ)) P)
  have hF : Continuous F := by simpa [F] using continuous_colSub_mul Λ P 1
  let e : K → (ι → Fin a → Fin a → ℂ) := fun g τ i j => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j
  have he : Measurable e := measurable_pi_lambda _ fun τ => measurable_pi_lambda _ fun i =>
    measurable_pi_lambda _ fun j => hmeas τ i j
  have hFe : ∀ g, Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) = F (e g) := fun g => rfl
  have hdetc : ∀ τ, Continuous fun G : ι → Fin a → Fin a → ℂ => (Matrix.of (G τ)).det :=
    fun τ => Continuous.matrix_det (continuous_apply τ)
  have hdete : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det = (Matrix.of (e g τ)).det := fun g τ => rfl
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ι → Fin a → Fin a → ℂ) 1).exists_bound_of_continuousOn hF.continuousOn
  have hball : ∀ g, e g ∈ Metric.closedBall (0 : ι → Fin a → Fin a → ℂ) 1 := by
    intro g
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => entry_norm_bound_of_unitary (ρ g τ).2 i j
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun g => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    simp only [hFe, hdete]
    refine Measurable.mul ?_ (hF.measurable.comp he)
    refine Finset.measurable_prod _ fun τ _ => ?_
    exact Measurable.pow_const ((hdetc τ).measurable.comp he) _
  · rw [norm_mul, norm_prod]
    simp only [norm_zpow, norm_det_unitary, one_zpow, Finset.prod_const_one, one_mul, hFe]
    exact hC _ (hball g)

/- English proof (translation)
Introduce `ι _ a d m`. Use `⟨fun τ => (-m τ).toNat, ?_⟩` and prove the remaining obligations. Introduce `K _ _ ν hP hInv ρ hmeas hsurj Λ k`. Use `haveI := hP`. Distinguish the cases in `hpos : 0 < a ∧ ∃ τ₀, 0 < m τ₀`.

Take `⟨ha, τ₀, hτ₀⟩` from `hpos`. Use `⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero a d m τ₀ ha hτ₀ ν hP hInv ρ hmeas hsurj Λ _]`. Simplify using the standard rewrite rules. Take `⟨M, r, U, hR⟩` from `GlobalTheory.T.exists_rational_fock_projection_maximal_minors (ι := ι) a d (fun τ => (-m τ).toNat) k`.

Use `⟨M, fun p => ((r p : ℚ) : ℂ), U, fun p => isAlgebraic_ratCast ℚ (r p), ?_⟩` and prove the remaining obligations. Use `set R : Pol ι d a := MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) with hRdef`. Establish `hperp : ∀ I ∈ inv a d (fun τ => (-m τ).toNat), Formalism.L2.DIV.fockS I R = 0`. Introduce `I hI`. Establish `hspan` using `GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors a d (fun τ => (-m τ).toNat) hI`.

Use `clear hI`. Use `show Formalism.L2.DIV.fockL I R = 0`. Proceed by induction on `hspan using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨T, rfl⟩ := hx`. Conclude with `hR T`.

Consider the case `zero => rw [map_zero, LinearMap.zero_apply]`. Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]`. Establish `h0` using `GlobalTheory.T.unitaryAverage_kills_fock_complement_relInvariants a d (fun τ => (-m τ).toNat) ν hP hInv ρ hmeas hsurj Λ R hperp`. Establish `hdet0 : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ≠ 0` using `fun g τ => by`.

Rewrite using `[← norm_ne_zero_iff, norm_det_unitary]`. Conclude with `one_ne_zero`. Establish `hD : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) = ∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))`. Introduce `g`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos a with ha | ha` into its components or cases. Substitute `ha` using the available equality. Simplify using `[Matrix.det_fin_zero]`. Establish `hm : m τ ≤ 0`. Assume the negation of the conclusion as `h`.

Conclude with `hpos ⟨ha, τ, by omega⟩`. Rewrite using `[Int.toNat_of_nonneg (by omega), neg_neg]`. Establish `hinv : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) * detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) = 1`. Introduce `g`. Unfold `detChar`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hdet0 g τ))]`. Establish `hmono : MvPolynomial.monomial k 1 = ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) + R`. Rewrite using `[hRdef]`.

Normalize the expressions using the abelian group laws. Establish `hpoint : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) * Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) = ∑ p, ((r p : ℚ) : ℂ) * Λ (prodMinors (U p)) + (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) * …`. Introduce `g`. Rewrite using `[hD g, hmono, map_add, map_sum, map_add, map_sum, mul_add, Finset.mul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, colSub_prodMinors, smul_smul, map_smul, smul_eq_mul]`. Rewrite using `[show (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) * ((((r p : ℚ) : ℂ) * detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) * Λ (prodMinors (U p))) = ((∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : …`. Use `(integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans ?_` and prove the remaining obligations. Rewrite using `[integral_add (integrable_const _) (integrable_avg ν ρ hmeas _ Λ R), integral_const, h0]`.

Simplify using the standard rewrite rules.
-/
theorem average_monomial_eq_sum_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ), ∃ n : ι → ℕ,
  ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) → Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℂ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), (∀ p, IsAlgebraic ℚ (r p)) ∧
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) ∂ν =
    ∑ p, r p * Λ (GlobalTheory.MinorFrame.prodMinors (U p)) := by
  intro ι _ a d m
  refine ⟨fun τ => (-m τ).toNat, ?_⟩
  intro K _ _ ν hP hInv ρ hmeas hsurj Λ k
  haveI := hP
  by_cases hpos : 0 < a ∧ ∃ τ₀, 0 < m τ₀
  · obtain ⟨ha, τ₀, hτ₀⟩ := hpos
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
    rw [GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero a d m τ₀ ha hτ₀ ν hP hInv ρ hmeas hsurj Λ _]
    simp
  obtain ⟨M, r, U, hR⟩ := GlobalTheory.T.exists_rational_fock_projection_maximal_minors (ι := ι) a d (fun τ => (-m τ).toNat) k
  refine ⟨M, fun p => ((r p : ℚ) : ℂ), U, fun p => isAlgebraic_ratCast ℚ (r p), ?_⟩
  set R : Pol ι d a := MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) with hRdef
  have hperp : ∀ I ∈ inv a d (fun τ => (-m τ).toNat), Formalism.L2.DIV.fockS I R = 0 := by
    intro I hI
    have hspan := GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors a d (fun τ => (-m τ).toNat) hI
    clear hI
    show Formalism.L2.DIV.fockL I R = 0
    induction hspan using Submodule.span_induction with
    | mem x hx => obtain ⟨T, rfl⟩ := hx; exact hR T
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
  have h0 := GlobalTheory.T.unitaryAverage_kills_fock_complement_relInvariants a d (fun τ => (-m τ).toNat) ν hP hInv ρ hmeas hsurj Λ R hperp
  have hdet0 : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun g τ => by
    rw [← norm_ne_zero_iff, norm_det_unitary]; exact one_ne_zero
  have hD : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) =
      ∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ)) := by
    intro g
    refine Finset.prod_congr rfl fun τ _ => ?_
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.det_fin_zero]
    · have hm : m τ ≤ 0 := by
        by_contra h
        exact hpos ⟨ha, τ, by omega⟩
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hinv : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
      detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
    intro g
    unfold detChar
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hdet0 g τ))]
  have hmono : MvPolynomial.monomial k 1 = ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) + R := by
    rw [hRdef]; abel
  have hpoint : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) =
      ∑ p, ((r p : ℚ) : ℂ) * Λ (prodMinors (U p)) +
        (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) R) := by
    intro g
    rw [hD g, hmono, map_add, map_sum, map_add, map_sum, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, colSub_prodMinors, smul_smul, map_smul, smul_eq_mul]
    rw [show (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
        ((((r p : ℚ) : ℂ) * detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          Λ (prodMinors (U p))) =
        ((∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          (((r p : ℚ) : ℂ) * Λ (prodMinors (U p))) by ring, hinv g, one_mul]
  refine (integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans ?_
  rw [integral_add (integrable_const _) (integrable_avg ν ρ hmeas _ Λ R), integral_const, h0]
  simp

end GlobalTheory.MinorFrame.AvgCore
