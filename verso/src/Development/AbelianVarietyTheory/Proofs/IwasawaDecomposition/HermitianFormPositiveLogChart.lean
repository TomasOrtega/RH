import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydisc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImaginaryPeriodLowerBoundLogStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicPeriodMatrixStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormPeriodLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientBoundPeriodBasisStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder

namespace GlobalTheory.PerCmp

/- English proof (translation)
Introduce `g r M hanti hdet hr`. Take `⟨d, e, f, -, hee, hfe, hsp⟩` from `exists_lagrangian_dual_in_coisotropic r M ⊤ hanti hdet (fun v _ => Submodule.mem_top)`. Take `⟨hli, hrd⟩` from `familyIsotropicDual_linearIndependent_and_card r d M e f hee hfe hsp`. Take `rfl : d = g` from `by omega`. Establish `hex : ∀ m : Fin r, ∃ c : Fin d ⊕ Fin d → ℝ, ∑ i, c i • Sum.elim e f i = Pi.single m 1` using `fun m => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hsp ▸ Submodule.mem_top)`.

Use `choose c hc using hex`. Use `⟨e, f, fun m k => c m (Sum.inl k), fun m k => c m (Sum.inr k), hee, hfe, ?_, fun m => ?_⟩` and prove the remaining obligations. Simplify using `using hli.comp Sum.inl Sum.inl_injective`. Rewrite using `[← hc m, Fintype.sum_sum_type]`. Simplify using the standard rewrite rules.
-/
theorem exists_symplectic_basis_coords : ∀ (g r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ), Mᵀ = -M → M.det ≠ 0 → r = 2 * g → ∃ (e f : Fin g → Fin r → ℝ) (P Q : Fin r → Fin g → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ LinearIndependent ℝ e ∧ ∀ m, (Pi.single m 1 : Fin r → ℝ) = ∑ k, P m k • e k + ∑ k, Q m k • f k := by
  intro g r M hanti hdet hr
  obtain ⟨d, e, f, -, hee, hfe, hsp⟩ :=
    exists_lagrangian_dual_in_coisotropic r M ⊤ hanti hdet (fun v _ => Submodule.mem_top)
  obtain ⟨hli, hrd⟩ := familyIsotropicDual_linearIndependent_and_card r d M e f hee hfe hsp
  obtain rfl : d = g := by omega
  have hex : ∀ m : Fin r, ∃ c : Fin d ⊕ Fin d → ℝ, ∑ i, c i • Sum.elim e f i = Pi.single m 1 :=
    fun m => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hsp ▸ Submodule.mem_top)
  choose c hc using hex
  refine ⟨e, f, fun m k => c m (Sum.inl k), fun m k => c m (Sum.inr k), hee, hfe, ?_, fun m => ?_⟩
  · simpa using hli.comp Sum.inl Sum.inl_injective
  · rw [← hc m, Fintype.sum_sum_type]
    simp

end GlobalTheory.PerCmp

set_option maxHeartbeats 1000000 in
open GlobalTheory.PerCmp in

/- English proof (translation)
Introduce `n a g r lam ρ M Hm hlam hpt hgrow`. Use `set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀def`. Establish `hs₀ : s₀ ∈ logDom n a`. Simplify using `only [logDom, Set.mem_setOf_eq, hs₀def]`. Apply the tactic sequence `intro k; split_ifs <;> norm_num`.

Take `⟨hli₀, hsp₀, hH₀, hpos₀, hM₀, -⟩` from `hpt s₀ hs₀`. Take `⟨hanti, hdet, hr⟩` from `hermForm_periods_alternating_nondeg g r (lam s₀) M (Hm s₀) hli₀ hsp₀ hH₀ hpos₀ hM₀`. Take `⟨e, f, P, Q, hee, hfe, heli, hPQ⟩` from `exists_symplectic_basis_coords g r M hanti hdet hr`. Establish `hImExp : ∀ t ∈ logDom n a, ∀ x y : Fin r → ℝ, (hermForm (Hm t) (∑ m, (x m : ℂ) • lam t m) (∑ m, (y m : ℂ) • lam t m)).im = x ⬝ᵥ M *ᵥ y`. Introduce `t ht x y`.

Take `⟨-, -, -, -, hM, -⟩` from `hpt t ht`. Establish `hc : ∀ (z : Fin r → ℝ), (∑ m, (z m : ℂ) • lam t m) = ∑ m, z m • lam t m` using `fun z => Finset.sum_congr rfl fun m _ => (Complex.coe_smul _ _)`. Rewrite using `[hc, hc]`. Use `show hermFormImBilin (Hm t) _ _ = _`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`.

Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum]`. Establish `hb : ∀ u w, hermFormImBilin (Hm t) u w = (hermForm (Hm t) u w).im` using `fun _ _ => rfl`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations. Simplify using `only [hb, hM]`.

Expand and normalize the polynomial expressions, which then agree. Use `set E : (Fin n → ℂ) → Fin g → Fin g → ℂ := fun t i => ∑ m, ((e i m : ℝ) : ℂ) • lam t m with hEdef`. Use `set F : (Fin n → ℂ) → Fin g → Fin g → ℂ := fun t i => ∑ m, ((f i m : ℝ) : ℂ) • lam t m with hFdef`. Establish `hlm : ∀ m, DifferentiableOn ℂ (fun t => lam t m) (logDom n a)` using `fun m => differentiableOn_pi.1 hlam m`. Establish `hEd : DifferentiableOn ℂ E (logDom n a)` using `differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum fun m _ => by have := hlm m; fun_prop`.

Establish `hFd : DifferentiableOn ℂ F (logDom n a)` using `differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum fun m _ => by have := hlm m; fun_prop`. Establish `hEE : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (E t i) (E t j)).im = 0` using `fun t ht i j => by`. Rewrite using `[hImExp t ht]`. Conclude with `hee i j`. Establish `hFE : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (F t i) (E t j)).im = if i = j then 1 else 0` using `fun t ht i j => by rw [hImExp t ht]; exact hfe i j`.

Establish `hFF : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (F t i) (F t j)).im = f i ⬝ᵥ M *ᵥ f j` using `fun t ht i j => hImExp t ht _ _`. Establish `hEli : ∀ t ∈ logDom n a, LinearIndependent ℝ (E t)`. Introduce `t ht`. Take `⟨hli, -⟩` from `hpt t ht`. Rewrite `hli`, `heli`, the goal using `[Fintype.linearIndependent_iff]`.

Introduce `c hc`. Establish `h1 : ∑ m, (∑ i, c i * e i m) • lam t m = 0`. Rewrite using `[← hc]`. Simplify using `only [hEdef, Finset.smul_sum, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.coe_smul, smul_smul]`. Establish `h2` using `hli _ h1`. Apply `heli c` to reduce the goal to its premises. Use function extensionality and compare the values at `m`.

Simplify `h2 m` using `[Finset.sum_apply]`. Establish `hdetE : ∀ t ∈ logDom n a, (Matrix.of fun k i => E t i k).det ≠ 0` using `fun t ht => det_ne_zero_of_real_indep_isotropic g (Hm t) (E t) (hpt t ht).2.2.2.1 (hEli t ht) (hEE t ht)`. Take `⟨τ, hτd, hτ⟩` from `GlobalTheory.T.exists_holomorphic_period_matrix n g (logDom n a) E F hEd hFd hdetE`. Establish `hRR : ∀ t ∈ logDom n a, _` using `fun t ht => riemann_relations_period_matrix g g (Hm t) (E t) (F t) (τ t) (hpt t ht).2.2.1 (hpt t ht).2.2.2.1 (hτ t ht) (hEE t ht) (hFE t ht)`. Take `⟨Cτ, kτ, hCτ⟩` from `period_matrix_polynomial_growth n a g τ (fun i j => ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ)) hτd (fun t ht => (hRR t ht).1) (fun t ht i j => by rw [(hRR t ht).2 i j, hFF t ht])`.

Take `⟨c₁, k₁, hc₁, hlow⟩` from `GlobalTheory.T.imaginary_period_lower_bound_log n a g τ hτd (fun t ht => (hRR t ht).1)`. Take `⟨Cl, kl, hCl⟩` from `hgrow`. Establish `hlamPQ : ∀ t, ∀ m, lam t m = ∑ k, (P m k : ℂ) • E t k + ∑ k, (Q m k : ℂ) • F t k`. Introduce `t m`. Establish `h` using `fun m' => congrFun (hPQ m) m'`.

Simplify using `only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h`. Simplify using `only [hEdef, hFdef, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun k m' => ((Q m k : ℂ) * (f k m' : ℂ)) • lam t m'), ← Finset.sum_add_distrib]`. Simplify using `only [← Finset.sum_smul, ← add_smul]`. Establish `h' : ∀ m', (∑ k, (P m k : ℂ) * (e k m' : ℂ) + ∑ k, (Q m k : ℂ) * (f k m' : ℂ)) = ((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℂ)`.

Introduce `m'`. Rewrite using `[h m']`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [h']`.

Simplify using `[Pi.single_apply]`. Use `set Cτ' := max Cτ 0 with hCτ'`. Use `set Cl' := max Cl 0 with hCl'`. Establish `hEn : ∀ t k, ‖E t k‖ ≤ r * ‖e‖ * ‖lam t‖`. Introduce `t k`.

Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ m ∈ Finset.univ, ‖((e k m : ℝ) : ℂ) • lam t m‖ ≤ ‖e‖ * ‖lam t‖`. Introduce `m _`. Rewrite using `[norm_smul, Complex.norm_real]`. Conclude with `mul_le_mul ((norm_le_pi_norm (e k) m).trans (norm_le_pi_norm e k)) (norm_le_pi_norm (lam t) m) (norm_nonneg _) (norm_nonneg _)`.

Use `(Finset.sum_le_sum this).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `[mul_assoc]`. Use `set X : ℝ := (g : ℝ) * ((r : ℝ) * ‖ρ‖ * (‖P‖ + (g : ℝ) * ‖Q‖ * Cτ')) with hX`. Use `set B : ℝ := (r : ℝ) * ‖e‖ * Cl' with hB`. Establish `hX0 : 0 ≤ X` using `by positivity`.

Establish `hB0 : 0 ≤ B` using `by positivity`. Use `set KU : ℝ := 2 * (g : ℝ) ^ 2 * X ^ 2 / c₁ with hKU`. Use `set KL : ℝ := ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2 / c₁ with hKL`. Establish `hKU0 : 0 ≤ KU` using `by positivity`. Establish `hKL0 : 0 ≤ KL` using `by positivity`.

Use `⟨KU + KL, k₁ + 2 * kτ + 2 * kl, by positivity, ?_⟩` and prove the remaining obligations. Introduce `t ht hle him w`. Use `set p : ℝ := 1 + ‖t‖ with hp`. Establish `hp1 : 1 ≤ p` using `by have := norm_nonneg t; linarith`. Establish `hp0 : 0 ≤ p` using `by linarith`.

Establish `hpk : ∀ j, j ≤ k₁ + 2 * kτ + 2 * kl → p ^ j ≤ p ^ (k₁ + 2 * kτ + 2 * kl)` using `fun j hj => pow_le_pow_right₀ hp1 hj`. Establish `hτt : ‖τ t‖ ≤ Cτ' * p ^ kτ` using `(hCτ t ht hle him).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))`. Establish `hlt : ‖lam t‖ ≤ Cl' * p ^ kl` using `(hCl t ht hle him).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))`. Establish `hCτ0 : 0 ≤ Cτ'` using `le_max_right _ _`. Establish `hCl0 : 0 ≤ Cl'` using `le_max_right _ _`.

Take `⟨av, hw, ha⟩` from `GlobalTheory.T.coefficient_bound_period_basis g r (lam t) ρ (E t) (F t) (τ t) P Q (hlamPQ t) (hτ t ht) (hpt t ht).2.2.2.2.2 w`. Take `⟨h1, h2⟩` from `GlobalTheory.T.hermitian_form_period_lower_bound g (Hm t) (E t) (F t) (τ t) c₁ (p ^ k₁) (Cτ' * p ^ kτ) (hpt t ht).2.2.1 (hpt t ht).2.2.2.1 (hτ t ht) (hEE t ht) (hFE t ht) hc₁ (fun v => hlow t ht hle v) hτt av`. Rewrite `h1`, `h2` using `[← hw]`. Use `set H := (hermForm (Hm t) w w).re with hH`. Establish `hH0 : 0 ≤ H`.

Distinguish the cases in `hw0 : w = 0`. Simplify using `[hH, hw0, hermForm]`. Conclude with `((hpt t ht).2.2.2.1 w hw0).le`. Establish `hA : ‖av‖ ≤ X * p ^ kτ * ‖w‖`. Use `ha.trans ?_` and prove the remaining obligations.

Establish `hin : ‖P‖ + (g : ℝ) * ‖Q‖ * ‖τ t‖ ≤ (‖P‖ + (g : ℝ) * ‖Q‖ * Cτ') * p ^ kτ`. Establish `hp' : 1 ≤ p ^ kτ` using `one_le_pow₀ hp1`. Establish `e1 : ‖P‖ ≤ ‖P‖ * p ^ kτ` using `le_mul_of_one_le_right (norm_nonneg _) hp'`. Establish `e2 : (g : ℝ) * ‖Q‖ * ‖τ t‖ ≤ (g : ℝ) * ‖Q‖ * (Cτ' * p ^ kτ)` using `mul_le_mul_of_nonneg_left hτt (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hw0` using `norm_nonneg w`. Combine the equalities or inequalities in the displayed calculation. Establish `hW : ‖w‖ ≤ g * ‖av‖ * (B * p ^ kl)`. Rewrite using `[hw]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Establish `: ∀ k ∈ Finset.univ, ‖av k • E t k‖ ≤ ‖av‖ * (B * p ^ kl)`. Introduce `k _`. Rewrite using `[norm_smul]`. Use `mul_le_mul (norm_le_pi_norm av k) ((hEn t k).trans ?_) (norm_nonneg _) (norm_nonneg _)` and prove the remaining obligations. Establish `h3 : (r : ℝ) * ‖e‖ * ‖lam t‖ ≤ (r : ℝ) * ‖e‖ * (Cl' * p ^ kl)` using `mul_le_mul_of_nonneg_left hlt (by positivity)`.

Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_le_sum this).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion.

Establish `hc : c₁ * KU = 2 * (g : ℝ) ^ 2 * X ^ 2` using `by rw [hKU]; field_simp`. Establish `hA2 : ‖av‖ ^ 2 ≤ X ^ 2 * p ^ (2 * kτ) * ‖w‖ ^ 2`. Use `pow_le_pow_left₀ (norm_nonneg _) hA 2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hmain : c₁ * H ≤ c₁ * (KU * p ^ (k₁ + 2 * kτ + 2 * kl) * ‖w‖ ^ 2)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpk _ (by omega)) (by positivity)) (by positivity)`. Use `_ = c₁ * (KU * p ^ (k₁ + 2 * kτ + 2 * kl) * ‖w‖ ^ 2) := by rw [← hc]; ring`. Use `le_of_mul_le_mul_left hmain hc₁` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)`. Establish `hc : c₁ * KL = ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2` using `by rw [hKL]; field_simp`. Establish `hW2 : ‖w‖ ^ 2 ≤ ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * ‖av‖ ^ 2`. Use `pow_le_pow_left₀ (norm_nonneg _) hW 2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `hmain : c₁ * ‖w‖ ^ 2 ≤ c₁ * (KL * p ^ (k₁ + 2 * kτ + 2 * kl) * H)`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[hW2, hc₁]`. Use `_ ≤ ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * (p ^ k₁ * ((g : ℝ) * (Cτ' * p ^ kτ)) ^ 2 * H) := by gcongr`. Use `_ = ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2 * p ^ (k₁ + 2 * kτ + 2 * kl) * H := by ring`.

Use `_ = c₁ * (KL * p ^ (k₁ + 2 * kτ + 2 * kl) * H) := by rw [← hc]; ring`. Use `le_of_mul_le_mul_left hmain hc₁` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)`.
-/
theorem GlobalTheory.hermForm_norm_comparison_of_periods : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), DifferentiableOn ℂ lam (logDom n a) → (∀ t ∈ logDom n a, LinearIndependent ℝ (lam t) ∧ Submodule.span ℝ (Set.range (lam t)) = ⊤ ∧ (Hm t).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) z z).re) ∧ (∀ i i', (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) (lam t i) (lam t i')).im = M i i') ∧ ∀ i, ∑ m, ρ i m • lam t m = Pi.single i 1) → (∃ (C : ℝ) (k : ℕ), ∀ t ∈ logDom n a, ‖logExp a t‖ ≤ 1 / 2 → (∀ i : Fin n, (i : ℕ) < a → |(t i).im| ≤ Real.pi) → ‖lam t‖ ≤ C * (1 + ‖t‖) ^ k) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ t ∈ logDom n a, ‖logExp a t‖ ≤ 1 / 2 → (∀ i : Fin n, (i : ℕ) < a → |(t i).im| ≤ Real.pi) → ∀ w : Fin g → ℂ, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) w w).re ≤ C * (1 + ‖t‖) ^ k * ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ C * (1 + ‖t‖) ^ k * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) w w).re := by
  intro n a g r lam ρ M Hm hlam hpt hgrow
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀def
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq, hs₀def]
    intro k; split_ifs <;> norm_num
  obtain ⟨hli₀, hsp₀, hH₀, hpos₀, hM₀, -⟩ := hpt s₀ hs₀
  obtain ⟨hanti, hdet, hr⟩ := hermForm_periods_alternating_nondeg g r (lam s₀) M (Hm s₀) hli₀ hsp₀ hH₀ hpos₀ hM₀
  obtain ⟨e, f, P, Q, hee, hfe, heli, hPQ⟩ := exists_symplectic_basis_coords g r M hanti hdet hr

  have hImExp : ∀ t ∈ logDom n a, ∀ x y : Fin r → ℝ,
      (hermForm (Hm t) (∑ m, (x m : ℂ) • lam t m) (∑ m, (y m : ℂ) • lam t m)).im = x ⬝ᵥ M *ᵥ y := by
    intro t ht x y
    obtain ⟨-, -, -, -, hM, -⟩ := hpt t ht
    have hc : ∀ (z : Fin r → ℝ), (∑ m, (z m : ℂ) • lam t m) = ∑ m, z m • lam t m := fun z =>
      Finset.sum_congr rfl fun m _ => (Complex.coe_smul _ _)
    rw [hc, hc]
    show hermFormImBilin (Hm t) _ _ = _
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    have hb : ∀ u w, hermFormImBilin (Hm t) u w = (hermForm (Hm t) u w).im := fun _ _ => rfl
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    simp only [hb, hM]; ring

  set E : (Fin n → ℂ) → Fin g → Fin g → ℂ := fun t i => ∑ m, ((e i m : ℝ) : ℂ) • lam t m with hEdef
  set F : (Fin n → ℂ) → Fin g → Fin g → ℂ := fun t i => ∑ m, ((f i m : ℝ) : ℂ) • lam t m with hFdef
  have hlm : ∀ m, DifferentiableOn ℂ (fun t => lam t m) (logDom n a) := fun m => differentiableOn_pi.1 hlam m
  have hEd : DifferentiableOn ℂ E (logDom n a) :=
    differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum fun m _ => by have := hlm m; fun_prop
  have hFd : DifferentiableOn ℂ F (logDom n a) :=
    differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum fun m _ => by have := hlm m; fun_prop
  have hEE : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (E t i) (E t j)).im = 0 := fun t ht i j => by
    rw [hImExp t ht]; exact hee i j
  have hFE : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (F t i) (E t j)).im = if i = j then 1 else 0 :=
    fun t ht i j => by rw [hImExp t ht]; exact hfe i j
  have hFF : ∀ t ∈ logDom n a, ∀ i j, (hermForm (Hm t) (F t i) (F t j)).im = f i ⬝ᵥ M *ᵥ f j :=
    fun t ht i j => hImExp t ht _ _
  have hEli : ∀ t ∈ logDom n a, LinearIndependent ℝ (E t) := by
    intro t ht
    obtain ⟨hli, -⟩ := hpt t ht
    rw [Fintype.linearIndependent_iff] at hli heli ⊢
    intro c hc
    have h1 : ∑ m, (∑ i, c i * e i m) • lam t m = 0 := by
      rw [← hc]
      simp only [hEdef, Finset.smul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.coe_smul, smul_smul]
    have h2 := hli _ h1
    apply heli c
    funext m
    simpa [Finset.sum_apply] using h2 m
  have hdetE : ∀ t ∈ logDom n a, (Matrix.of fun k i => E t i k).det ≠ 0 := fun t ht =>
    det_ne_zero_of_real_indep_isotropic g (Hm t) (E t) (hpt t ht).2.2.2.1 (hEli t ht) (hEE t ht)
  obtain ⟨τ, hτd, hτ⟩ := GlobalTheory.T.exists_holomorphic_period_matrix n g (logDom n a) E F hEd hFd hdetE
  have hRR : ∀ t ∈ logDom n a, _ := fun t ht =>
    riemann_relations_period_matrix g g (Hm t) (E t) (F t) (τ t) (hpt t ht).2.2.1 (hpt t ht).2.2.2.1
      (hτ t ht) (hEE t ht) (hFE t ht)
  obtain ⟨Cτ, kτ, hCτ⟩ := period_matrix_polynomial_growth n a g τ (fun i j => ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ)) hτd
    (fun t ht => (hRR t ht).1) (fun t ht i j => by rw [(hRR t ht).2 i j, hFF t ht])
  obtain ⟨c₁, k₁, hc₁, hlow⟩ := GlobalTheory.T.imaginary_period_lower_bound_log n a g τ hτd (fun t ht => (hRR t ht).1)
  obtain ⟨Cl, kl, hCl⟩ := hgrow
  have hlamPQ : ∀ t, ∀ m, lam t m = ∑ k, (P m k : ℂ) • E t k + ∑ k, (Q m k : ℂ) • F t k := by
    intro t m
    have h := fun m' => congrFun (hPQ m) m'
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [hEdef, hFdef, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun k m' => ((Q m k : ℂ) * (f k m' : ℂ)) • lam t m'), ← Finset.sum_add_distrib]
    simp only [← Finset.sum_smul, ← add_smul]
    have h' : ∀ m', (∑ k, (P m k : ℂ) * (e k m' : ℂ) + ∑ k, (Q m k : ℂ) * (f k m' : ℂ)) = ((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℂ) := by
      intro m'; rw [h m']; push_cast; rfl
    simp only [h']
    simp [Pi.single_apply]

  set Cτ' := max Cτ 0 with hCτ'
  set Cl' := max Cl 0 with hCl'
  have hEn : ∀ t k, ‖E t k‖ ≤ r * ‖e‖ * ‖lam t‖ := by
    intro t k
    refine (norm_sum_le _ _).trans ?_
    have : ∀ m ∈ Finset.univ, ‖((e k m : ℝ) : ℂ) • lam t m‖ ≤ ‖e‖ * ‖lam t‖ := by
      intro m _
      rw [norm_smul, Complex.norm_real]
      exact mul_le_mul ((norm_le_pi_norm (e k) m).trans (norm_le_pi_norm e k)) (norm_le_pi_norm (lam t) m)
        (norm_nonneg _) (norm_nonneg _)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    simp [mul_assoc]
  set X : ℝ := (g : ℝ) * ((r : ℝ) * ‖ρ‖ * (‖P‖ + (g : ℝ) * ‖Q‖ * Cτ')) with hX
  set B : ℝ := (r : ℝ) * ‖e‖ * Cl' with hB
  have hX0 : 0 ≤ X := by positivity
  have hB0 : 0 ≤ B := by positivity
  set KU : ℝ := 2 * (g : ℝ) ^ 2 * X ^ 2 / c₁ with hKU
  set KL : ℝ := ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2 / c₁ with hKL
  have hKU0 : 0 ≤ KU := by positivity
  have hKL0 : 0 ≤ KL := by positivity
  refine ⟨KU + KL, k₁ + 2 * kτ + 2 * kl, by positivity, ?_⟩
  intro t ht hle him w
  set p : ℝ := 1 + ‖t‖ with hp
  have hp1 : 1 ≤ p := by have := norm_nonneg t; linarith
  have hp0 : 0 ≤ p := by linarith
  have hpk : ∀ j, j ≤ k₁ + 2 * kτ + 2 * kl → p ^ j ≤ p ^ (k₁ + 2 * kτ + 2 * kl) :=
    fun j hj => pow_le_pow_right₀ hp1 hj
  have hτt : ‖τ t‖ ≤ Cτ' * p ^ kτ :=
    (hCτ t ht hle him).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hlt : ‖lam t‖ ≤ Cl' * p ^ kl :=
    (hCl t ht hle him).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hCτ0 : 0 ≤ Cτ' := le_max_right _ _
  have hCl0 : 0 ≤ Cl' := le_max_right _ _
  obtain ⟨av, hw, ha⟩ := GlobalTheory.T.coefficient_bound_period_basis g r (lam t) ρ (E t) (F t) (τ t) P Q (hlamPQ t) (hτ t ht) (hpt t ht).2.2.2.2.2 w
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hermitian_form_period_lower_bound g (Hm t) (E t) (F t) (τ t) c₁ (p ^ k₁) (Cτ' * p ^ kτ) (hpt t ht).2.2.1 (hpt t ht).2.2.2.1
    (hτ t ht) (hEE t ht) (hFE t ht) hc₁ (fun v => hlow t ht hle v) hτt av
  rw [← hw] at h1 h2
  set H := (hermForm (Hm t) w w).re with hH
  have hH0 : 0 ≤ H := by
    by_cases hw0 : w = 0
    · simp [hH, hw0, hermForm]
    · exact ((hpt t ht).2.2.2.1 w hw0).le
  have hA : ‖av‖ ≤ X * p ^ kτ * ‖w‖ := by
    refine ha.trans ?_
    have hin : ‖P‖ + (g : ℝ) * ‖Q‖ * ‖τ t‖ ≤ (‖P‖ + (g : ℝ) * ‖Q‖ * Cτ') * p ^ kτ := by
      have hp' : 1 ≤ p ^ kτ := one_le_pow₀ hp1
      have e1 : ‖P‖ ≤ ‖P‖ * p ^ kτ := le_mul_of_one_le_right (norm_nonneg _) hp'
      have e2 : (g : ℝ) * ‖Q‖ * ‖τ t‖ ≤ (g : ℝ) * ‖Q‖ * (Cτ' * p ^ kτ) :=
        mul_le_mul_of_nonneg_left hτt (by positivity)
      nlinarith
    have hw0 := norm_nonneg w
    calc (g : ℝ) * ((r : ℝ) * ‖ρ‖ * (‖P‖ + (g : ℝ) * ‖Q‖ * ‖τ t‖)) * ‖w‖
        ≤ (g : ℝ) * ((r : ℝ) * ‖ρ‖ * ((‖P‖ + (g : ℝ) * ‖Q‖ * Cτ') * p ^ kτ)) * ‖w‖ := by gcongr
      _ = X * p ^ kτ * ‖w‖ := by rw [hX]; ring
  have hW : ‖w‖ ≤ g * ‖av‖ * (B * p ^ kl) := by
    rw [hw]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.univ, ‖av k • E t k‖ ≤ ‖av‖ * (B * p ^ kl) := by
      intro k _
      rw [norm_smul]
      refine mul_le_mul (norm_le_pi_norm av k) ((hEn t k).trans ?_) (norm_nonneg _) (norm_nonneg _)
      have h3 : (r : ℝ) * ‖e‖ * ‖lam t‖ ≤ (r : ℝ) * ‖e‖ * (Cl' * p ^ kl) :=
        mul_le_mul_of_nonneg_left hlt (by positivity)
      calc (r : ℝ) * ‖e‖ * ‖lam t‖ ≤ (r : ℝ) * ‖e‖ * (Cl' * p ^ kl) := h3
        _ = B * p ^ kl := by rw [hB]; ring
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  constructor
  ·
    have hc : c₁ * KU = 2 * (g : ℝ) ^ 2 * X ^ 2 := by rw [hKU]; field_simp
    have hA2 : ‖av‖ ^ 2 ≤ X ^ 2 * p ^ (2 * kτ) * ‖w‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hA 2
      calc ‖av‖ ^ 2 ≤ (X * p ^ kτ * ‖w‖) ^ 2 := this
        _ = X ^ 2 * p ^ (2 * kτ) * ‖w‖ ^ 2 := by ring
    have hmain : c₁ * H ≤ c₁ * (KU * p ^ (k₁ + 2 * kτ + 2 * kl) * ‖w‖ ^ 2) := by
      calc c₁ * H ≤ 2 * (g : ℝ) ^ 2 * p ^ k₁ * ‖av‖ ^ 2 := h2
        _ ≤ 2 * (g : ℝ) ^ 2 * p ^ k₁ * (X ^ 2 * p ^ (2 * kτ) * ‖w‖ ^ 2) := by gcongr
        _ = 2 * (g : ℝ) ^ 2 * X ^ 2 * p ^ (k₁ + 2 * kτ) * ‖w‖ ^ 2 := by ring
        _ ≤ 2 * (g : ℝ) ^ 2 * X ^ 2 * p ^ (k₁ + 2 * kτ + 2 * kl) * ‖w‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpk _ (by omega)) (by positivity)) (by positivity)
        _ = c₁ * (KU * p ^ (k₁ + 2 * kτ + 2 * kl) * ‖w‖ ^ 2) := by rw [← hc]; ring
    have := le_of_mul_le_mul_left hmain hc₁
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  ·
    have hc : c₁ * KL = ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2 := by rw [hKL]; field_simp
    have hW2 : ‖w‖ ^ 2 ≤ ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * ‖av‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hW 2
      calc ‖w‖ ^ 2 ≤ (g * ‖av‖ * (B * p ^ kl)) ^ 2 := this
        _ = ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * ‖av‖ ^ 2 := by ring
    have hmain : c₁ * ‖w‖ ^ 2 ≤ c₁ * (KL * p ^ (k₁ + 2 * kτ + 2 * kl) * H) := by
      calc c₁ * ‖w‖ ^ 2 ≤ ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * (c₁ * ‖av‖ ^ 2) := by
            nlinarith [hW2, hc₁]
        _ ≤ ((g : ℝ) * B) ^ 2 * p ^ (2 * kl) * (p ^ k₁ * ((g : ℝ) * (Cτ' * p ^ kτ)) ^ 2 * H) := by gcongr
        _ = ((g : ℝ) * B) ^ 2 * ((g : ℝ) * Cτ') ^ 2 * p ^ (k₁ + 2 * kτ + 2 * kl) * H := by ring
        _ = c₁ * (KL * p ^ (k₁ + 2 * kτ + 2 * kl) * H) := by rw [← hc]; ring
    have := le_of_mul_le_mul_left hmain hc₁
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
