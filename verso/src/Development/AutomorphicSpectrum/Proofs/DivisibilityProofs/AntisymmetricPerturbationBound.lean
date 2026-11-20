import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormulaStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPowerStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBoundStatement
import Development.WeilBound.CoreStatements.FlagImmersions.DegLApply

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
open RootFieldNumerics

namespace GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Take `⟨h1, h2⟩` from `hl`. Rewrite `h1` using `[homogeneousSubmodule_one_eq_span_X]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℝ).1 h1`. Establish `hcoef : ∀ p, coeff (Finsupp.single p 1) l = c p`. Introduce `p`.

Rewrite using `[← hc, coeff_sum, Finset.sum_eq_single p]`. Simplify using the standard rewrite rules. Introduce `q _ hq`. Rewrite using `[coeff_smul, coeff_X', if_neg, smul_zero]`. Introduce `h`.

Conclude with `hq (Finsupp.single_left_injective one_ne_zero h)`. Simplify using the standard rewrite rules. Establish `hinv : ∀ τ (i k : Fin N), ((i : ℕ) < j ↔ (k : ℕ) < j) → c (τ, i) = c (τ, k)`. Introduce `τ i k hik`. Establish `hmem : Equiv.swap (τ, i) (τ, k) ∈ GroundTheory.Heights₂.Heights.antisymWeyl Ψ N j`.

Introduce `p`. Rewrite using `[Equiv.swap_apply_def]`. Use `split_ifs with e1 e2`. Substitute `e1` using the available equality. Conclude with `⟨rfl, hik.symm⟩`.

Substitute `e2` using the available equality. Conclude with `⟨rfl, hik⟩`. Conclude with `⟨rfl, Iff.rfl⟩`. Establish `h3` using `coeff_rename_mapDomain _ (Equiv.swap (τ, i) (τ, k)).injective l (Finsupp.single (τ, i) 1)`. Rewrite `h3` using `[h2 _ hmem, Finsupp.mapDomain_single, Equiv.swap_apply_left, hcoef, hcoef]`.

Conclude with `h3.symm`. Establish `ha : ∀ τ, ∃ a : ℝ, ∀ i : Fin N, (i : ℕ) < j → c (τ, i) = a`. Introduce `τ`. Distinguish the cases in `h : ∃ i : Fin N, (i : ℕ) < j`. Take `⟨i, hi⟩` from `h`.

Conclude with `⟨c (τ, i), fun k hk => hinv τ k i (by simp [hi, hk])⟩`. Conclude with `⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩`. Establish `hb : ∀ τ, ∃ b : ℝ, ∀ i : Fin N, ¬ (i : ℕ) < j → c (τ, i) = b`. Introduce `τ`. Distinguish the cases in `h : ∃ i : Fin N, ¬ (i : ℕ) < j`.

Take `⟨i, hi⟩` from `h`. Conclude with `⟨c (τ, i), fun k hk => hinv τ k i (iff_of_false hk hi)⟩`. Conclude with `⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩`. Use `choose a ha using ha`. Use `choose b hb using hb`.

Use `⟨a, b, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, map_sum, Fintype.sum_prod_type, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_eval, eval_X]`. Use `split_ifs with hi`. Rewrite using `[ha τ i hi]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hb τ i hi]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem inv_linear_eval (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (l : MvPolynomial (Ψ × Fin N) ℝ)
    (hl : l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j) :
    ∃ a b : Ψ → ℝ, ∀ x : Ψ × Fin N → ℝ, eval x l =
      ∑ τ, (a τ - b τ) * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i) +
        ∑ τ, b τ * ∑ i, x (τ, i) := by
  obtain ⟨h1, h2⟩ := hl
  rw [homogeneousSubmodule_one_eq_span_X] at h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h1
  have hcoef : ∀ p, coeff (Finsupp.single p 1) l = c p := by
    intro p
    rw [← hc, coeff_sum, Finset.sum_eq_single p]
    · simp
    · intro q _ hq
      rw [coeff_smul, coeff_X', if_neg, smul_zero]
      intro h
      exact hq (Finsupp.single_left_injective one_ne_zero h)
    · simp
  have hinv : ∀ τ (i k : Fin N), ((i : ℕ) < j ↔ (k : ℕ) < j) → c (τ, i) = c (τ, k) := by
    intro τ i k hik
    have hmem : Equiv.swap (τ, i) (τ, k) ∈ GroundTheory.Heights₂.Heights.antisymWeyl Ψ N j := by
      intro p
      rw [Equiv.swap_apply_def]
      split_ifs with e1 e2
      · subst e1
        exact ⟨rfl, hik.symm⟩
      · subst e2
        exact ⟨rfl, hik⟩
      · exact ⟨rfl, Iff.rfl⟩
    have h3 := coeff_rename_mapDomain _ (Equiv.swap (τ, i) (τ, k)).injective l (Finsupp.single (τ, i) 1)
    rw [h2 _ hmem, Finsupp.mapDomain_single, Equiv.swap_apply_left, hcoef, hcoef] at h3
    exact h3.symm
  have ha : ∀ τ, ∃ a : ℝ, ∀ i : Fin N, (i : ℕ) < j → c (τ, i) = a := by
    intro τ
    by_cases h : ∃ i : Fin N, (i : ℕ) < j
    · obtain ⟨i, hi⟩ := h
      exact ⟨c (τ, i), fun k hk => hinv τ k i (by simp [hi, hk])⟩
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  have hb : ∀ τ, ∃ b : ℝ, ∀ i : Fin N, ¬ (i : ℕ) < j → c (τ, i) = b := by
    intro τ
    by_cases h : ∃ i : Fin N, ¬ (i : ℕ) < j
    · obtain ⟨i, hi⟩ := h
      exact ⟨c (τ, i), fun k hk => hinv τ k i (iff_of_false hk hi)⟩
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose a ha using ha
  choose b hb using hb
  refine ⟨a, b, fun x => ?_⟩
  rw [← hc, map_sum, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eval, eval_X]
  split_ifs with hi
  · rw [ha τ i hi]
    ring
  · rw [hb τ i hi]
    ring

/- English proof (translation)
Use `⟨((dimFl Ψ N).factorial : ℝ) * ∏ _τ : Ψ, ∏ i : Fin N, ∏ k ∈ Finset.Ioi i, ((k : ℝ) - (i : ℝ))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Use `mul_pos (by positivity) (Finset.prod_pos fun _ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun k hk => inv_pos.2 (sub_pos.2 ?_))` and prove the remaining obligations. Conclude with `(Finset.mem_Ioi.1 hk)` after adjusting the coercions. Introduce `x`. Rewrite using `[(GlobalTheory.T.flag_degree_weight_formula Ψ N _).1, mul_assoc]`.

Use `congr 1`. Unfold `GroundTheory.Heights₂.Heights.antisymDelta`. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_filter]`. Use `Finset.prod_congr (by ext k; simp) fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, eval_X, eval_X, div_eq_inv_mul]`.
-/
theorem flagDeg_eq_delta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Ψ × Fin N → ℝ,
      flagDeg (fun τ i => x (τ, i) : Wt Ψ N) = c * eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) := by
  refine ⟨((dimFl Ψ N).factorial : ℝ) * ∏ _τ : Ψ, ∏ i : Fin N, ∏ k ∈ Finset.Ioi i, ((k : ℝ) - (i : ℝ))⁻¹, ?_, ?_⟩
  · refine mul_pos (by positivity) (Finset.prod_pos fun _ _ => Finset.prod_pos fun i _ =>
      Finset.prod_pos fun k hk => inv_pos.2 (sub_pos.2 ?_))
    exact_mod_cast (Finset.mem_Ioi.1 hk)
  · intro x
    rw [(GlobalTheory.T.flag_degree_weight_formula Ψ N _).1, mul_assoc]
    congr 1
    unfold GroundTheory.Heights₂.Heights.antisymDelta
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_filter]
    refine Finset.prod_congr (by ext k; simp) fun k _ => ?_
    rw [map_sub, eval_X, eval_X, div_eq_inv_mul]

/- English proof (translation)
Introduce `Ψ _ _ N j R v ε Pl l hv hP _ hl hε`. Take `⟨a, b, hab⟩` from `inv_linear_eval Ψ N j l hl`. Take `⟨c, hc0, hc⟩` from `flagDeg_eq_delta Ψ N`. Use `set K : ℝ := v * ((dimFl Ψ N : ℝ) + 1) * c with hK`. Establish `hK0 : K ≠ 0` using `by positivity`.

Use `⟨fun τ => a τ / K, fun τ => b τ / K, fun m hm => ?_⟩` and prove the remaining obligations. Set `Φ : RP Ψ N →ₗ[ℝ] ℝ` to `R + v • (∑ τ, (a τ / K - b τ / K) • Lin.shL j τ + ∑ τ, (b τ / K) • Lin.totL τ)`. Establish `hΦ : ∀ F, Φ F = R F + v * (∑ τ, (a τ / K - b τ / K) * Sh j τ F + ∑ τ, b τ / K * Tot τ F)`. Introduce `F`. Simplify using `only [Φ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Lin.shL_apply, Lin.totL_apply, smul_eq_mul]`.

Take `⟨P', -, hP', -, hle⟩` from `GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) Φ`. Establish `heq : P' = Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l`. Use `MvPolynomial.funext fun x => ?_` and prove the remaining obligations. Establish `e1 : (-∑ y, C (x y) * X y : RP Ψ N) = linRoot (fun τ i => x (τ, i) : Wt Ψ N)` using `rfl`. Establish `e2` using `hP (fun τ i => x (τ, i))`.

Rewrite using `[hP', e1, hΦ, map_sub, map_mul, hab, ← e2]`. Simplify using `only [(GlobalTheory.T.flag_shift_total_lin_root_power Ψ N j _ _).1, (GlobalTheory.T.flag_shift_total_lin_root_power Ψ N j _ _).2, hc]`. Rewrite using `[sub_eq_add_neg (eval x Pl)]`. Use `congr 1`. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hK' : v * ((dimFl Ψ N : ℝ) + 1) * c / K = 1` using `div_self hK0`. Generalize the expression as in `(∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i)) = s`. Generalize the expression as in `(∑ i, x (τ, i)) = t`. Generalize the expression as in `eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) = d`.

Take the linear combination `(-(d * ((a τ - b τ) * s + b τ * t))) * hK'`. Establish `h` using `hle m hm`. Rewrite `h` using `[hΦ, heq]`. Conclude with `h.trans (hε m)`.
-/
theorem cor_b_poly_functional : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (R : RP Ψ N →ₗ[ℝ] ℝ) (v ε : ℝ) (Pl l : MvPolynomial (Ψ × Fin N) ℝ), 0 < v → (∀ lam : Wt Ψ N, eval (fun x => lam x.1 x.2) Pl = R (linRoot lam ^ (dimFl Ψ N + 1))) → Pl.IsHomogeneous (dimFl Ψ N + 1) → l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j → (∀ m, |coeff m (Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l)| ≤ ε) → ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 → |R (monomial m 1) + v * (∑ τ, (α τ - β τ) * Sh j τ (monomial m 1) + ∑ τ, β τ * Tot τ (monomial m 1))| ≤ ε := by
  intro Ψ _ _ N j R v ε Pl l hv hP _ hl hε
  obtain ⟨a, b, hab⟩ := inv_linear_eval Ψ N j l hl
  obtain ⟨c, hc0, hc⟩ := flagDeg_eq_delta Ψ N
  set K : ℝ := v * ((dimFl Ψ N : ℝ) + 1) * c with hK
  have hK0 : K ≠ 0 := by positivity
  refine ⟨fun τ => a τ / K, fun τ => b τ / K, fun m hm => ?_⟩
  let Φ : RP Ψ N →ₗ[ℝ] ℝ :=
    R + v • (∑ τ, (a τ / K - b τ / K) • Lin.shL j τ + ∑ τ, (b τ / K) • Lin.totL τ)
  have hΦ : ∀ F, Φ F = R F + v * (∑ τ, (a τ / K - b τ / K) * Sh j τ F + ∑ τ, b τ / K * Tot τ F) := by
    intro F
    simp only [Φ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Lin.shL_apply,
      Lin.totL_apply, smul_eq_mul]
  obtain ⟨P', -, hP', -, hle⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) Φ
  have heq : P' = Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l := by
    refine MvPolynomial.funext fun x => ?_
    have e1 : (-∑ y, C (x y) * X y : RP Ψ N) = linRoot (fun τ i => x (τ, i) : Wt Ψ N) := rfl
    have e2 := hP (fun τ i => x (τ, i))
    rw [hP', e1, hΦ, map_sub, map_mul, hab, ← e2]
    simp only [(GlobalTheory.T.flag_shift_total_lin_root_power Ψ N j _ _).1, (GlobalTheory.T.flag_shift_total_lin_root_power Ψ N j _ _).2, hc]
    rw [sub_eq_add_neg (eval x Pl)]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hK' : v * ((dimFl Ψ N : ℝ) + 1) * c / K = 1 := div_self hK0
    generalize (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i)) = s
    generalize (∑ i, x (τ, i)) = t
    generalize eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) = d
    linear_combination (-(d * ((a τ - b τ) * s + b τ * t))) * hK'
  have h := hle m hm
  rw [hΦ, heq] at h
  exact h.trans (hε m)

end GlobalTheory.CompanionTheory.Ar.Top
