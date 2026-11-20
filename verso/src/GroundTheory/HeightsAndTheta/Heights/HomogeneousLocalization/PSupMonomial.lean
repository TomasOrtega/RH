import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry NumberField TensorProduct GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (∑ i, a i) with h0 | hpos` into its components or cases. Establish `ha : ∀ i, a i = 0` using `fun i => Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ i)`. Simplify using `[ha]`. Use `set n := ∑ i, a i with hn`. Establish `hnR : (0 : ℝ) < n` using `by exact_mod_cast hpos`.

Use `set w : ι → ℝ := fun i => (a i : ℝ) / n`. Use `set z : ι → ℝ := fun i => q i / a i`. Establish `hz : ∀ i, 0 ≤ z i` using `fun i => div_nonneg (hq i) (Nat.cast_nonneg _)`. Establish `hw : ∑ i, w i = 1`. Simplify using `only [w, ← Finset.sum_div]`.

Rewrite using `[← Nat.cast_sum, ← hn, div_self hnR.ne']`. Establish `hamgm` using `Real.geom_mean_le_arith_mean_weighted Finset.univ w z (fun i _ => div_nonneg (Nat.cast_nonneg _) hnR.le) hw (fun i _ => hz i)`. Establish `hsum : ∑ i, w i * z i ≤ (∑ i, q i) / n`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [w, z]`. Break down `eq_or_ne (a i : ℝ) 0 with h | h` into its components or cases. Rewrite using `[h]`. Simplify using `using div_nonneg (hq i) hnR.le`. Rewrite using `[div_mul_div_comm, mul_comm (a i : ℝ), mul_div_mul_right _ _ h]`.

Establish `key : (∏ i, z i ^ w i) ^ n = ∏ i, z i ^ a i`. Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (hz i), div_mul_cancel₀ _ hnR.ne', Real.rpow_natCast]`. Establish `h1 : ∏ i, z i ^ a i ≤ (∑ i, q i) ^ n / (n : ℝ) ^ n`.

Rewrite using `[← key, ← div_pow]`. Conclude with `pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _) (hamgm.trans hsum) n`. Establish `h2 : ∏ i, q i ^ a i = (∏ i, z i ^ a i) * ∏ i, (a i : ℝ) ^ a i`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [z]`. Break down `eq_or_ne (a i) 0 with h | h` into its components or cases. Simplify using `[h]`. Rewrite using `[div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr h))]`. Establish `hA : 0 ≤ ∏ i, (a i : ℝ) ^ a i` using `Finset.prod_nonneg fun i _ => by positivity`.

Establish `hN : 0 < (n : ℝ) ^ n` using `pow_pos hnR n`. Rewrite using `[h2]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma SupMonomial.pow_mul_prod_le {ι : Type*} [Fintype ι] (a : ι → ℕ) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) :
    ((∑ i, a i : ℕ) : ℝ) ^ (∑ i, a i) * ∏ i, q i ^ a i ≤
      (∑ i, q i) ^ (∑ i, a i) * ∏ i, (a i : ℝ) ^ a i := by
  rcases Nat.eq_zero_or_pos (∑ i, a i) with h0 | hpos
  · have ha : ∀ i, a i = 0 := fun i => Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ i)
    simp [ha]
  set n := ∑ i, a i with hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  set w : ι → ℝ := fun i => (a i : ℝ) / n
  set z : ι → ℝ := fun i => q i / a i
  have hz : ∀ i, 0 ≤ z i := fun i => div_nonneg (hq i) (Nat.cast_nonneg _)
  have hw : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div]
    rw [← Nat.cast_sum, ← hn, div_self hnR.ne']
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ w z
    (fun i _ => div_nonneg (Nat.cast_nonneg _) hnR.le) hw (fun i _ => hz i)
  have hsum : ∑ i, w i * z i ≤ (∑ i, q i) / n := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [w, z]
    rcases eq_or_ne (a i : ℝ) 0 with h | h
    · rw [h]; simpa using div_nonneg (hq i) hnR.le
    · rw [div_mul_div_comm, mul_comm (a i : ℝ), mul_div_mul_right _ _ h]
  have key : (∏ i, z i ^ w i) ^ n = ∏ i, z i ^ a i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i), div_mul_cancel₀ _ hnR.ne', Real.rpow_natCast]
  have h1 : ∏ i, z i ^ a i ≤ (∑ i, q i) ^ n / (n : ℝ) ^ n := by
    rw [← key, ← div_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _)
      (hamgm.trans hsum) n
  have h2 : ∏ i, q i ^ a i = (∏ i, z i ^ a i) * ∏ i, (a i : ℝ) ^ a i := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [z]
    rcases eq_or_ne (a i) 0 with h | h
    · simp [h]
    · rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr h))]
  have hA : 0 ≤ ∏ i, (a i : ℝ) ^ a i := Finset.prod_nonneg fun i _ => by positivity
  have hN : 0 < (n : ℝ) ^ n := pow_pos hnR n
  rw [h2]
  calc (n : ℝ) ^ n * ((∏ i, z i ^ a i) * ∏ i, (a i : ℝ) ^ a i)
      ≤ (n : ℝ) ^ n * ((∑ i, q i) ^ n / (n : ℝ) ^ n * ∏ i, (a i : ℝ) ^ a i) := by gcongr
    _ = (∑ i, q i) ^ n * ∏ i, (a i : ℝ) ^ a i := by field_simp

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _), div_pow, show (norm2 v ^ a.degree) ^ 2 = (norm2 v ^ 2) ^ a.degree by ring, euclideanNorm_sq, norm_prod, ← Finset.prod_pow]`. Simplify using `only [norm_pow, ← pow_mul, mul_comm (a _) 2]`. Both sides reduce to the same expression.
-/
lemma SupMonomial.sq_eq {N : ℕ} (a : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ) :
    (‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree) ^ 2 =
      (∏ i, (‖v i‖ ^ 2) ^ a i) / (∑ i, ‖v i‖ ^ 2) ^ a.degree := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _), div_pow,
    show (norm2 v ^ a.degree) ^ 2 = (norm2 v ^ 2) ^ a.degree by ring, euclideanNorm_sq, norm_prod,
    ← Finset.prod_pow]
  simp only [norm_pow, ← pow_mul, mul_comm (a _) 2]
  rfl

/- English proof (translation)
Establish `hx : 0 ≤ ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree` using `div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos hv).le _)`. Rewrite using `[← Real.sqrt_sq hx]`. Use `Real.sqrt_le_sqrt ?_` and prove the remaining obligations. Rewrite using `[SupMonomial.sq_eq]`. Establish `hS : 0 < (∑ i, ‖v i‖ ^ 2) ^ a.degree` using `pow_pos (normSq2_pos hv) _`.

Establish `hN : 0 < (a.degree : ℝ) ^ a.degree`. Break down `Nat.eq_zero_or_pos a.degree with h | h` into its components or cases. Simplify using `[h]`. Conclude with `pow_pos (by exact_mod_cast h) _`. Rewrite using `[div_le_div_iff₀ hS hN]`.

Use `SupMonomial.pow_mul_prod_le (fun i => a i) (fun i => ‖v i‖ ^ 2) (fun i => by positivity)` as an intermediate fact. Rewrite `this` using `[← Finsupp.degree_eq_sum]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma SupMonomial.le {N : ℕ} (a : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree ≤
      √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) := by
  have hx : 0 ≤ ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree :=
    div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos hv).le _)
  rw [← Real.sqrt_sq hx]
  refine Real.sqrt_le_sqrt ?_
  rw [SupMonomial.sq_eq]
  have hS : 0 < (∑ i, ‖v i‖ ^ 2) ^ a.degree := pow_pos (normSq2_pos hv) _
  have hN : 0 < (a.degree : ℝ) ^ a.degree := by
    rcases Nat.eq_zero_or_pos a.degree with h | h
    · simp [h]
    · exact pow_pos (by exact_mod_cast h) _
  rw [div_le_div_iff₀ hS hN]
  have := SupMonomial.pow_mul_prod_le (fun i => a i) (fun i => ‖v i‖ ^ 2) (fun i => by positivity)
  rw [← Finsupp.degree_eq_sum] at this
  linarith

/- English proof (translation)
Break down `Nat.eq_zero_or_pos a.degree with h0 | hpos` into its components or cases. Establish `ha : a = 0` using `(Finsupp.degree_eq_zero_iff a).mp h0`. Substitute `ha` using the available equality. Use `⟨Pi.single 0 1, by simp [funext_iff, Pi.single_apply], ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Use `set n := a.degree`. Establish `hnR : (0 : ℝ) < n` using `by exact_mod_cast hpos`. Take `⟨j, -, hj⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (show ∑ i, a i ≠ 0 by rw [← Finsupp.degree_eq_sum]; exact hpos.ne')`. Use `set v : Fin (N + 1) → ℂ := fun i => ((√((a i : ℝ) / n) : ℝ) : ℂ)`. Establish `hvi : ∀ i, ‖v i‖ ^ 2 = (a i : ℝ) / n` using `fun i => by`.

Simplify using `only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Conclude with `Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) hnR.le)`. Establish `hv : v ≠ 0` using `fun h => by`. Use `hvi j` as an intermediate fact. Rewrite `this` using `[h, Pi.zero_apply, norm_zero, zero_pow two_ne_zero, eq_comm, div_eq_zero_iff]`.

Conclude with `this.elim (fun h' => hj (by exact_mod_cast h')) hnR.ne'`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Establish `hx : 0 ≤ ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ n` using `div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos hv).le _)`. Rewrite using `[← Real.sqrt_sq hx, SupMonomial.sq_eq]`. Use `congr 1`.

Simplify using `only [hvi]`. Rewrite using `[← Finset.sum_div, ← Nat.cast_sum, ← Finsupp.degree_eq_sum, div_self hnR.ne', one_pow, div_one, Finset.prod_congr rfl fun i _ => div_pow (a i : ℝ) n (a i), Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]`.
-/
lemma SupMonomial.exists_eq {N : ℕ} (a : Fin (N + 1) →₀ ℕ) :
    ∃ v : Fin (N + 1) → ℂ, v ≠ 0 ∧
      ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree =
        √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) := by
  rcases Nat.eq_zero_or_pos a.degree with h0 | hpos
  · have ha : a = 0 := (Finsupp.degree_eq_zero_iff a).mp h0
    subst ha
    refine ⟨Pi.single 0 1, by simp [funext_iff, Pi.single_apply], ?_⟩
    simp
  set n := a.degree
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ i, a i ≠ 0 by rw [← Finsupp.degree_eq_sum]; exact hpos.ne')
  set v : Fin (N + 1) → ℂ := fun i => ((√((a i : ℝ) / n) : ℝ) : ℂ)
  have hvi : ∀ i, ‖v i‖ ^ 2 = (a i : ℝ) / n := fun i => by
    simp only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) hnR.le)
  have hv : v ≠ 0 := fun h => by
    have := hvi j
    rw [h, Pi.zero_apply, norm_zero, zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at this
    exact this.elim (fun h' => hj (by exact_mod_cast h')) hnR.ne'
  refine ⟨v, hv, ?_⟩
  have hx : 0 ≤ ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ n :=
    div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos hv).le _)
  rw [← Real.sqrt_sq hx, SupMonomial.sq_eq]
  congr 1
  simp only [hvi]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← Finsupp.degree_eq_sum, div_self hnR.ne', one_pow, div_one,
    Finset.prod_congr rfl fun i _ => div_pow (a i : ℝ) n (a i), Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]

/- English proof (translation)
Introduce `K _ _ N σ a`. Establish `hval : ∀ x : (self (𝓞 K) N).complexPoints (intEmb σ), fsFibreNorm a.degree (intEmb σ) x ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N a.degree) σ x ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A` using `𝓞 K) a rfl))) = CP.fsNormPoly a.degree (MvPolynomial.monomial a (1 : ℂ)) x.1 := by`. Introduce `x`. Rewrite using `[evalFibre_tmul, map_one, one_smul, h, MvPolynomial.map_monomial, map_one]`. Establish `hle : ∀ y : CP N, CP.fsNormPoly a.degree (MvPolynomial.monomial a (1 : ℂ)) y ≤ √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree)` using `fun y => SupMonomial.le a y.rep y.rep_nonzero`.

Take `⟨v, hv, hveq⟩` from `SupMonomial.exists_eq a`. Set `x₀ : (self (𝓞 K) N).complexPoints (intEmb σ)` to `selfPoint (intEmb σ) (Projectivization.mk ℂ v hv)`. Establish `: Nonempty ((self (𝓞 K) N).complexPoints (intEmb σ))` using `⟨x₀⟩`. Simplify using `only [fsSupNorm, hval]`. Use `le_antisymm (ciSup_le fun x => hle x.1) (le_ciSup_of_le ⟨√((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree), ?_⟩ x₀ (le_of_eq ?_))` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hle x.1`. Rewrite using `[← hveq]`. Conclude with `(CP.fsNormPoly_mk (MvPolynomial.isHomogeneous_monomial 1 rfl) v hv).symm`.
-/
theorem SupMonomial.proof (h : FSValue.Statement.{0}) : SupMonomial.Statement := by
  intro K _ _ N σ a
  have hval : ∀ x : (self (𝓞 K) N).complexPoints (intEmb σ),
      fsFibreNorm a.degree (intEmb σ) x ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N a.degree) σ x
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A := 𝓞 K) a rfl))) =
      CP.fsNormPoly a.degree (MvPolynomial.monomial a (1 : ℂ)) x.1 := by
    intro x
    rw [evalFibre_tmul, map_one, one_smul, h, MvPolynomial.map_monomial, map_one]
  have hle : ∀ y : CP N, CP.fsNormPoly a.degree (MvPolynomial.monomial a (1 : ℂ)) y ≤
      √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) :=
    fun y => SupMonomial.le a y.rep y.rep_nonzero
  obtain ⟨v, hv, hveq⟩ := SupMonomial.exists_eq a
  let x₀ : (self (𝓞 K) N).complexPoints (intEmb σ) := selfPoint (intEmb σ) (Projectivization.mk ℂ v hv)
  have : Nonempty ((self (𝓞 K) N).complexPoints (intEmb σ)) := ⟨x₀⟩
  simp only [fsSupNorm, hval]
  refine le_antisymm (ciSup_le fun x => hle x.1)
    (le_ciSup_of_le ⟨√((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree), ?_⟩ x₀ (le_of_eq ?_))
  · rintro _ ⟨x, rfl⟩
    exact hle x.1
  · rw [← hveq]
    exact (CP.fsNormPoly_mk (MvPolynomial.isHomogeneous_monomial 1 rfl) v hv).symm

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
