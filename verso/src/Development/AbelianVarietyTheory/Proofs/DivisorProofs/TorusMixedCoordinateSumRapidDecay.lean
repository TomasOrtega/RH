import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionHeisenbergWordSupLeLevelPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedThetaSeriesRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinateSupportIntegralAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCountStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TorusMixedDecay

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ σ : D.host.E →+* ℂ, 1 ≤ ‖σ y‖ := by`. Apply `NumberField.exists_conjugate_one_le_norm (K := D.host.E) (α := ⟨y, hy⟩)` to reduce the goal to its premises. Introduce `h`. Conclude with `h0 (congrArg Subtype.val h)`. Take `⟨τ, hτ⟩` from `(GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk φ)`.

Establish `: ‖φ y‖ = ‖tauE D τ y‖`. Rewrite using `[← InfinitePlace.apply, ← InfinitePlace.apply]`. Simplify using `only at hτ`. Rewrite using `[hτ]`. Rewrite `hφ` using `[this]`.

Conclude with `hφ.trans (Finset.single_le_sum (f := fun τ => ‖tauE D τ y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ τ))`.
-/
theorem one_le_sum_tauE (D : D7) (y : D.host.E) (hy : IsIntegral ℤ y) (h0 : y ≠ 0) :
    1 ≤ ∑ τ, ‖tauE D τ y‖ := by
  obtain ⟨φ, hφ⟩ : ∃ σ : D.host.E →+* ℂ, 1 ≤ ‖σ y‖ := by
    apply NumberField.exists_conjugate_one_le_norm (K := D.host.E) (α := ⟨y, hy⟩)
    intro h; exact h0 (congrArg Subtype.val h)
  obtain ⟨τ, hτ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk φ)
  have : ‖φ y‖ = ‖tauE D τ y‖ := by
    rw [← InfinitePlace.apply, ← InfinitePlace.apply]
    simp only at hτ
    rw [hτ]
  rw [this] at hφ
  exact hφ.trans (Finset.single_le_sum (f := fun τ => ‖tauE D τ y‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ τ))

/- English proof (translation)
Establish `hcomp : ∀ τ, compAt θ τ (ξ.map (incA D) : Mx D m r) = ξ.map (tauE D τ)`. Introduce `τ`. Use extensionality with `i j`. Conclude with `(hθ τ).1 (ξ i j)`. Apply the tactic sequence `have hentry : ∀ τ a b, ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) * diagonal (fun k => (t k : ℂ))) a b‖ = ‖tauE D τ (ξ a b)‖ * t b := by`.

Introduce `τ a b`. Rewrite using `[hcomp, Matrix.mul_diagonal, norm_mul, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ht b)]`. Simplify using `only [hentry]`. Establish `hL0 : (L : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hL.ne'`. Establish `h1` using `one_le_sum_tauE D _ (hint j i) (mul_ne_zero hL0 hj)`.

Simplify using `only [map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h1`. Rewrite `h1` using `[← Finset.mul_sum]`. Establish `hn : ∀ τ a b, 0 ≤ ‖tauE D τ (ξ a b)‖ * t b` using `fun τ a b => mul_nonneg (norm_nonneg _) (ht b).le`. Establish `h2 : (∑ τ, ‖tauE D τ (ξ j i)‖) * t i ≤ ∑ τ, ∑ a, ∑ b, ‖tauE D τ (ξ a b)‖ * t b`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hLr : (0 : ℝ) ≤ L` using `Nat.cast_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem coord_le {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ} (ξ : Matrix (Fin m) (Fin r) D.host.E)
    (L : ℕ) (hL : 0 < L) (hint : ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)) (t : Fin r → ℝ) (ht : ∀ i, 0 < t i)
    (i : Fin r) (j : Fin m) (hj : ξ j i ≠ 0) :
    t i ≤ (L : ℝ) * (1 + ∑ τ, ∑ a, ∑ b,
      ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) * diagonal (fun k => (t k : ℂ))) a b‖) := by
  have hcomp : ∀ τ, compAt θ τ (ξ.map (incA D) : Mx D m r) = ξ.map (tauE D τ) := by
    intro τ; ext i j; exact (hθ τ).1 (ξ i j)
  have hentry : ∀ τ a b, ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) *
      diagonal (fun k => (t k : ℂ))) a b‖ = ‖tauE D τ (ξ a b)‖ * t b := by
    intro τ a b
    rw [hcomp, Matrix.mul_diagonal, norm_mul, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ht b)]
  simp only [hentry]
  have hL0 : (L : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  have h1 := one_le_sum_tauE D _ (hint j i) (mul_ne_zero hL0 hj)
  simp only [map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h1
  rw [← Finset.mul_sum] at h1
  have hn : ∀ τ a b, 0 ≤ ‖tauE D τ (ξ a b)‖ * t b := fun τ a b => mul_nonneg (norm_nonneg _) (ht b).le
  have h2 : (∑ τ, ‖tauE D τ (ξ j i)‖) * t i ≤ ∑ τ, ∑ a, ∑ b, ‖tauE D τ (ξ a b)‖ * t b := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => ?_
    calc ‖tauE D τ (ξ j i)‖ * t i ≤ ∑ b, ‖tauE D τ (ξ j b)‖ * t b :=
          Finset.single_le_sum (f := fun b => ‖tauE D τ (ξ j b)‖ * t b) (fun b _ => hn τ j b) (Finset.mem_univ i)
      _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b, ‖tauE D τ (ξ a b)‖ * t b)
          (fun a _ => Finset.sum_nonneg fun b _ => hn τ a b) (Finset.mem_univ j)
  have hLr : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  calc t i = 1 * t i := (one_mul _).symm
    _ ≤ ((L : ℝ) * ∑ τ, ‖tauE D τ (ξ j i)‖) * t i := mul_le_mul_of_nonneg_right h1 (ht i).le
    _ = (L : ℝ) * ((∑ τ, ‖tauE D τ (ξ j i)‖) * t i) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hLr

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `D ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' c hc K₀ hK₀ hK₀c μ 𝓕 hμ τ₀ e`. Take `⟨N, A₄, C₄, hC₄, h4⟩` from `GlobalTheory.T.siegelCone_integral_matrix_lattice_count θ hθ X.rank r c hc`. Take `⟨k₂, C₂, hC₂, h2⟩` from `GlobalTheory.T.mixed_theta_series_rapid_decay ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' (N + r * e)`. Take `⟨k₁, B, C₁, hC₁, h1⟩` from `GlobalTheory.T.thetaFunction_heisenbergWord_sup_le_level_pow ψ hψ θ hθ V X K₀ hK₀ hK₀c μ 𝓕 hμ`. Take `⟨M, hM, h3⟩` from `GlobalTheory.T.mixedCoordinate_support_integral_at_level ψ hψ V X S₀ r d μ' 𝓕' hμ' K₀ hK₀ hK₀c`.

Use `set Wc : ℝ := ∑ k ∈ Finset.range (k₂ + 1), (Fintype.card (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool) : ℝ) ^ k with hWc`. Establish `hWc0 : 0 ≤ Wc` using `Finset.sum_nonneg fun _ _ => by positivity`. Use `⟨k₁ + k₂, B + A₄ + r * e, C₂ * Wc * C₁ * C₄ * (M : ℝ) ^ (A₄ + r * e), by positivity, ?_⟩` and prove the remaining obligations. Introduce `n hn Ψ hΨ hlev hvan t ht α hα hαc`. Use `set sob := GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k₁ + k₂) Ψ with hsob`.

Establish `hsob_ne : sob ≠ ⊤` using `GlobalTheory.Size.sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΨ _`. Establish `hw : GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k₂ Ψ ≤ ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob`. Unfold `GlobalTheory.Size.wordSum`. Establish `hk : ∀ k ∈ Finset.range (k₂ + 1), ∀ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool, GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ) ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob`. Introduce `k hk a`.

Use `(h1 n hn Ψ hΨ hlev (List.ofFn a)).trans ?_` and prove the remaining obligations. Rewrite using `[List.length_ofFn]`. Use `gcongr`. Conclude with `GlobalTheory.Size.wordSum_mono (by have := Finset.mem_range.1 hk; omega) Ψ`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[← Finset.sum_mul, hWc, ENNReal.ofReal_mul hWc0, ← mul_assoc]`. Use `congr 2`. Rewrite using `[ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Use `set L : ℕ := M * n with hL`. Use `set K₁ := ENNReal.ofReal C₂ * (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob) with hK₁`.

Use `set K := ENNReal.ofReal ((L : ℝ) ^ (r * e)) * K₁ with hK`. Establish `hLpos : 0 < L` using `Nat.mul_pos hM hn`. Establish `hpt : ∀ ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ENNReal.ofReal (∏ i, t i ^ e) * ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤ {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal …`. Introduce `ξ`. Distinguish the cases in `h0 : d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0 = 0`.

Rewrite using `[h0, enorm_zero, mul_zero]`. Conclude with `bot_le`. Establish `hfin : (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α).map (finPart D) = (ξ.map (incA D) : Mx D X.rank r).map (finPart D)`. Rewrite using `[Matrix.map_mul, hα, Matrix.mul_one]`. Establish `hint` using `h3 n hn Ψ hΨ hlev ξ _ hfin h0`.

Rewrite using `[Set.indicator_of_mem (show ξ ∈ {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} from hint)]`. Establish `hc' : ∀ τ, compAt θ τ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) = compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))`. Introduce `τ`. Rewrite using `[← hαc τ]`. Conclude with `Matrix.map_mul (f := ((θ τ).comp (infPart D)))`.

Establish `hb` using `h2 Ψ hΨ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α)`. Simplify using `only [hc'] at hb`. Establish `hcol : ∀ i, ∃ j, ξ j i ≠ 0`. Introduce `i`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Use `h0 (hvan _ i fun j => ?_)` and prove the remaining obligations. Rewrite using `[hc', Matrix.mul_diagonal]`. Establish `: compAt θ τ₀ (ξ.map (incA D) : Mx D X.rank r) j i = 0`. Simplify using `only [compAt, Matrix.map_apply, hcon j, map_zero]`.

Rewrite using `[this, zero_mul]`. Establish `hti : ∀ i, t i ≤ (L : ℝ) * (1 + ∑ τ, ∑ a, ∑ b, ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) a b‖)` using `fun i => by`. Take `⟨j, hj⟩` from `hcol i`. Conclude with `coord_le hθ ξ L hLpos hint t ht.1 i j hj`. Take `⟨s, hs⟩ : ∃ s : ℝ, s = 1 + ∑ τ, ∑ a, ∑ b, ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) a b‖` from `⟨_, rfl⟩`.

Establish `hs0 : 0 < s` using `by rw [hs]; positivity`. Rewrite `hb`, `hti`, the goal using `[← hs]`. Establish `hprod : ∏ i, t i ^ e ≤ (L : ℝ) ^ (r * e) * s ^ (r * e)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_pow, mul_comm e r]`.

Use `set P := ENNReal.ofReal (s ^ N) with hP`. Establish `hP0 : P ≠ 0`. Rewrite using `[hP, ne_eq, ENNReal.ofReal_eq_zero, not_le]`. Conclude with `pow_pos hs0 _`. Establish `hPt : P ≠ ⊤` using `ENNReal.ofReal_ne_top`.

Establish `hb1 : ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ * ENNReal.ofReal (s ^ (N + r * e)) ≤ K₁` using `hb.trans (by rw [hK₁]; gcongr)`. Establish `hb' : ENNReal.ofReal (∏ i, t i ^ e) * ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ * P ≤ K`. Generalize the expression as in `‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ = z at hb1 ⊢`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hP, pow_add, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ K := by rw [hK]; gcongr`. Rewrite using `[ENNReal.ofReal_inv_of_pos (pow_pos hs0 _), ← hP, ← ENNReal.div_eq_inv_mul]`. Conclude with `(ENNReal.le_div_iff_mul_le (Or.inl hP0) (Or.inl hPt)).2 hb'`. Establish `es : sob = ENNReal.ofReal sob.toReal` using `(ENNReal.ofReal_toReal hsob_ne).symm`.

Rewrite using `[← ENNReal.tsum_mul_left]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₂, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`. Rewrite using `[hL]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_mul_sum_mixS_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ (c : ℝ), 0 < c →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 → ∀ (τ₀ : D.what₂.Tau) (e : ℕ),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      (∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → d.mixS X ψ μ' 𝓕' Ψ x 0 = 0) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ α : Mx D r r, α.map (finPart D) = 1 →
        (∀ τ, compAt θ τ α = diagonal (fun i => (t i : ℂ))) →
        ENNReal.ofReal (∏ i, t i ^ e) *
          ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 k Ψ).toReal) := by
  intro D ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' c hc K₀ hK₀ hK₀c μ 𝓕 hμ τ₀ e
  obtain ⟨N, A₄, C₄, hC₄, h4⟩ := GlobalTheory.T.siegelCone_integral_matrix_lattice_count θ hθ X.rank r c hc
  obtain ⟨k₂, C₂, hC₂, h2⟩ := GlobalTheory.T.mixed_theta_series_rapid_decay ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' (N + r * e)
  obtain ⟨k₁, B, C₁, hC₁, h1⟩ := GlobalTheory.T.thetaFunction_heisenbergWord_sup_le_level_pow ψ hψ θ hθ V X K₀ hK₀ hK₀c μ 𝓕 hμ
  obtain ⟨M, hM, h3⟩ := GlobalTheory.T.mixedCoordinate_support_integral_at_level ψ hψ V X S₀ r d μ' 𝓕' hμ' K₀ hK₀ hK₀c
  set Wc : ℝ := ∑ k ∈ Finset.range (k₂ + 1),
    (Fintype.card (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool) : ℝ) ^ k with hWc
  have hWc0 : 0 ≤ Wc := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨k₁ + k₂, B + A₄ + r * e, C₂ * Wc * C₁ * C₄ * (M : ℝ) ^ (A₄ + r * e), by positivity, ?_⟩
  intro n hn Ψ hΨ hlev hvan t ht α hα hαc
  set sob := GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k₁ + k₂) Ψ with hsob
  have hsob_ne : sob ≠ ⊤ := GlobalTheory.Size.sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΨ _

  have hw : GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k₂ Ψ ≤
      ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob := by
    unfold GlobalTheory.Size.wordSum
    have hk : ∀ k ∈ Finset.range (k₂ + 1), ∀ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ) ≤
          ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob := by
      intro k hk a
      refine (h1 n hn Ψ hΨ hlev (List.ofFn a)).trans ?_
      rw [List.length_ofFn]
      gcongr
      exact GlobalTheory.Size.wordSum_mono (by have := Finset.mem_range.1 hk; omega) Ψ
    calc ∑ k ∈ Finset.range (k₂ + 1), ∑ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
          GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ)
        ≤ ∑ k ∈ Finset.range (k₂ + 1), ∑ _a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
          ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob :=
          Finset.sum_le_sum fun k hk' => Finset.sum_le_sum fun a _ => hk k hk' a
      _ = ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.sum_mul, hWc, ENNReal.ofReal_mul hWc0, ← mul_assoc]
          congr 2
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
          push_cast; rfl
  set L : ℕ := M * n with hL
  set K₁ := ENNReal.ofReal C₂ * (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob) with hK₁
  set K := ENNReal.ofReal ((L : ℝ) ^ (r * e)) * K₁ with hK
  have hLpos : 0 < L := Nat.mul_pos hM hn

  have hpt : ∀ ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
      ENNReal.ofReal (∏ i, t i ^ e) * ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ * K := by
    intro ξ
    by_cases h0 : d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0 = 0
    · rw [h0, enorm_zero, mul_zero]; exact bot_le
    have hfin : (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α).map (finPart D) =
        (ξ.map (incA D) : Mx D X.rank r).map (finPart D) := by
      rw [Matrix.map_mul, hα, Matrix.mul_one]
    have hint := h3 n hn Ψ hΨ hlev ξ _ hfin h0
    rw [Set.indicator_of_mem (show ξ ∈ {ξ : Matrix (Fin X.rank) (Fin r) D.host.E |
      ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} from hint)]
    have hc' : ∀ τ, compAt θ τ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) =
        compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ)) := by
      intro τ
      rw [← hαc τ]
      exact Matrix.map_mul (f := ((θ τ).comp (infPart D)))
    have hb := h2 Ψ hΨ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α)
    simp only [hc'] at hb
    have hcol : ∀ i, ∃ j, ξ j i ≠ 0 := by
      intro i
      by_contra hcon
      push_neg at hcon
      refine h0 (hvan _ i fun j => ?_)
      rw [hc', Matrix.mul_diagonal]
      have : compAt θ τ₀ (ξ.map (incA D) : Mx D X.rank r) j i = 0 := by
        simp only [compAt, Matrix.map_apply, hcon j, map_zero]
      rw [this, zero_mul]
    have hti : ∀ i, t i ≤ (L : ℝ) * (1 + ∑ τ, ∑ a, ∑ b,
        ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) a b‖) := fun i => by
      obtain ⟨j, hj⟩ := hcol i
      exact coord_le hθ ξ L hLpos hint t ht.1 i j hj
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 + ∑ τ, ∑ a, ∑ b,
        ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) a b‖ := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; positivity
    rw [← hs] at hb hti ⊢
    have hprod : ∏ i, t i ^ e ≤ (L : ℝ) ^ (r * e) * s ^ (r * e) := by
      calc ∏ i, t i ^ e ≤ ∏ _i : Fin r, ((L : ℝ) * s) ^ e :=
            Finset.prod_le_prod (fun i _ => pow_nonneg (ht.1 i).le _)
              (fun i _ => pow_le_pow_left₀ (ht.1 i).le (hti i) _)
        _ = _ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_pow, mul_comm e r]
    set P := ENNReal.ofReal (s ^ N) with hP
    have hP0 : P ≠ 0 := by
      rw [hP, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos hs0 _
    have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
    have hb1 : ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ *
        ENNReal.ofReal (s ^ (N + r * e)) ≤ K₁ :=
      hb.trans (by rw [hK₁]; gcongr)
    have hb' : ENNReal.ofReal (∏ i, t i ^ e) *
        ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ * P ≤ K := by
      generalize ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ = z at hb1 ⊢
      calc ENNReal.ofReal (∏ i, t i ^ e) * z * P
          ≤ ENNReal.ofReal ((L : ℝ) ^ (r * e) * s ^ (r * e)) * z * P := by
            gcongr
        _ = ENNReal.ofReal ((L : ℝ) ^ (r * e)) * (z * ENNReal.ofReal (s ^ (N + r * e))) := by
            rw [hP, pow_add, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
            ring
        _ ≤ K := by rw [hK]; gcongr
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hs0 _), ← hP, ← ENNReal.div_eq_inv_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hP0) (Or.inl hPt)).2 hb'
  have es : sob = ENNReal.ofReal sob.toReal := (ENNReal.ofReal_toReal hsob_ne).symm
  rw [← ENNReal.tsum_mul_left]
  calc ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        ENNReal.ofReal (∏ i, t i ^ e) * ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ
      ≤ ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ * K :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ) * K :=
        ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (C₄ * (L : ℝ) ^ A₄) * K := by gcongr; exact h4 L hLpos t ht
    _ = ENNReal.ofReal (C₄ * (L : ℝ) ^ A₄) * (ENNReal.ofReal ((L : ℝ) ^ (r * e)) * (ENNReal.ofReal C₂ *
          (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * ENNReal.ofReal sob.toReal))) := by rw [hK, hK₁, ← es]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₂, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hL]
      push_cast
      ring

end GlobalTheory.TorusMixedDecay

end
