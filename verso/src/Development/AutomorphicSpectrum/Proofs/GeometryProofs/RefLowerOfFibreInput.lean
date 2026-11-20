import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightBoundedUnitStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleHeightBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedFlagDegreeLowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OrthogonalFlagDegreeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalNormOutsideFiniteSet
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.RefLow

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Unfold `lineHt ptHt`. Rewrite using `[finsum_sum_mul (fun k => (A.a k : ℝ)) (fun k (v : FinitePlace L) => Real.log (⨆ i, v (w ⟨k, i⟩)))]`. Introduce `k`. Use `support_log_iSup_place_finite (y := fun i => w ⟨k, i⟩) ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hw k`.

Conclude with `Function.ne_iff.mpr ⟨i, hi⟩`.
-/
theorem lineHt_eq (A : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    lineHt A L w = (Module.finrank ℚ L : ℝ)⁻¹ *
      (∑ k, (A.a k : ℝ) * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) +
        ∑ σ : L →+* ℂ, Real.log (A.h fun p => σ (w p))) := by
  unfold lineHt ptHt
  rw [finsum_sum_mul (fun k => (A.a k : ℝ)) (fun k (v : FinitePlace L) => Real.log (⨆ i, v (w ⟨k, i⟩)))]
  intro k
  refine support_log_iSup_place_finite (y := fun i => w ⟨k, i⟩) ?_
  obtain ⟨i, hi⟩ := hw k
  exact Function.ne_iff.mpr ⟨i, hi⟩

/- English proof (translation)
Simplify using `only [lineHt_eq _ L w hw]`. Rewrite using `[← Finset.mul_sum, Finset.sum_add_distrib]`. Use `congr 2`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_mul]`. Use `congr 1`. Simplify using `[combLine, Finset.sum_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Establish `hz : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `hw k`. Conclude with `⟨i, (map_ne_zero σ).mpr hi⟩`. Establish `: (combLine l fun _ => 1).h (fun p => σ (w p)) = ∏ j, (l j).h fun p => σ (w p)`. Simplify using `[combLine]`.

Rewrite using `[this, Real.log_prod fun j _ => ((l j).pos _ hz).ne']`.
-/
theorem lineHt_combLine_one {J : Type} [Fintype J] (l : J → HermLine ι) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, ι k) → L) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    lineHt (combLine l fun _ => 1) L w = ∑ j, lineHt (l j) L w := by
  simp only [lineHt_eq _ L w hw]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  congr 2
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    simp [combLine, Finset.sum_apply]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hz : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hw k
      exact ⟨i, (map_ne_zero σ).mpr hi⟩
    have : (combLine l fun _ => 1).h (fun p => σ (w p)) = ∏ j, (l j).h fun p => σ (w p) := by
      simp [combLine]
    rw [this, Real.log_prod fun j _ => ((l j).pos _ hz).ne']

/- English proof (translation)
Establish `: (combLine l fun _ => 1).h = fun z => ∏ j, (l j).h z`. Use function extensionality and compare the values at `z`. Simplify using `[combLine]`. Unfold `IsSmoothHerm`. Rewrite using `[this]`.

Conclude with `contDiffOn_prod fun j _ => hl j`.
-/
theorem isSmoothHerm_combLine_one {J : Type} [Fintype J] (l : J → HermLine ι) (hl : ∀ j, IsSmoothHerm (l j)) :
    IsSmoothHerm (combLine l fun _ => 1) := by
  have : (combLine l fun _ => 1).h = fun z => ∏ j, (l j).h z := by
    funext z
    simp [combLine]
  unfold IsSmoothHerm
  rw [this]
  exact contDiffOn_prod fun j _ => hl j

end Lines

section Flags

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp`. Consider the case `succ r ih`. Rewrite using `[Fin.sum_univ_castSucc]`. Establish `h` using `ih fun i => g i.castSucc`.

Simplify using `only [Fin.succ_castSucc, h, Fin.succ_last, Fin.castSucc_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_succ_sub_castSucc {r : ℕ} (g : Fin (r + 1) → ℝ) :
    ∑ i : Fin r, (g i.succ - g i.castSucc) = g (Fin.last r) - g 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih fun i => g i.castSucc
    simp only [Fin.succ_castSucc, h, Fin.succ_last, Fin.castSucc_zero]
    ring

/- English proof (translation)
Establish `hb : F = ⊥` using `Submodule.finrank_eq_zero.1 h`. Rewrite using `[hb, HermitianBundle.normDegree, HermitianBundle.degree_bot, zero_div]`.
-/
theorem normDegree_rank_zero (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier) (h : E.rank F = 0) :
    E.normDegree F = 0 := by
  have hb : F = ⊥ := Submodule.finrank_eq_zero.1 h
  rw [hb, HermitianBundle.normDegree, HermitianBundle.degree_bot, zero_div]

/- English proof (translation)
Establish `h0 : E.normDegree (A.F 0) = 0` using `normDegree_rank_zero E _ (by simpa using A.rank 0)`. Use `sum_succ_sub_castSucc fun i => E.normDegree (A.F i)` as an intermediate fact. Simplify using `only [SatFlag.grDeg, SatFlag.top]`. Rewrite using `[this, h0, sub_zero]`.
-/
theorem normDegree_top {E : HermitianBundle.{0} K} {r : ℕ} (A : SatFlag E r) :
    E.normDegree A.top = ∑ i, A.grDeg i := by
  have h0 : E.normDegree (A.F 0) = 0 := normDegree_rank_zero E _ (by simpa using A.rank 0)
  have := sum_succ_sub_castSucc fun i => E.normDegree (A.F i)
  simp only [SatFlag.grDeg, SatFlag.top]
  rw [this, h0, sub_zero]

end Flags

section Core

variable {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K} {Ψ : Type} [Fintype Ψ] {a b : ℕ}

/- English proof (translation)
Use `(Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => h i).trans ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem abs_sum_fin_le {n : ℕ} (g : Fin n → ℝ) (C : ℝ) (h : ∀ i, |g i| ≤ C) : |∑ i, g i| ≤ n * C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => h i).trans ?_)
  simp

/- English proof (translation)
The claim follows from `|A.flatDeg τ - ∑ l, h (τ, l)| ≤ ((a : ℝ) + b) * C := by have e : A.flatDeg τ - ∑ l, h (τ, l) = -(∑ i, (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i)) - ∑ i, (h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev) := by have hr : ∑ i : Fin b, (A.S τ).grDeg i.rev = ∑ i, (A.S τ).grDeg i := Equiv. …`.
-/
theorem flatDeg_sub_le (A : FlagPair E Ψ a b) (h : Ψ × Fin (a + b) → ℝ) (C : ℝ)
    (hW : ∀ τ (i : Fin a), |h (τ, Fin.castAdd b i) - (A.W τ).grDeg i| ≤ C)
    (hS : ∀ τ (i : Fin b), |h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev| ≤ C) (τ : Ψ) :
    |A.flatDeg τ - ∑ l, h (τ, l)| ≤ ((a : ℝ) + b) * C := by
  have e : A.flatDeg τ - ∑ l, h (τ, l) =
      -(∑ i, (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i)) -
        ∑ i, (h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev) := by
    have hr : ∑ i : Fin b, (A.S τ).grDeg i.rev = ∑ i, (A.S τ).grDeg i :=
      Equiv.sum_comp Fin.revPerm fun i => (A.S τ).grDeg i
    rw [FlagPair.flatDeg, normDegree_top, normDegree_top, Fin.sum_univ_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hr]
    ring
  have h1 := abs_le.1 (abs_sum_fin_le _ C (hW τ))
  have h2 := abs_le.1 (abs_sum_fin_le _ C (hS τ))
  rw [e, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/- English proof (translation)
Establish `key : ∀ τ, -(∑ i : Fin a, mu τ (Fin.castAdd b i) * (A.W τ).grDeg i) + ∑ i : Fin b, mu τ (Fin.natAdd a i) * (A.S τ).grDeg i.rev ≤ -(∑ l, mu τ l * h (τ, l)) + ((a : ℝ) + b) * (2 * C)`. Introduce `τ`. Establish `e : -(∑ i : Fin a, mu τ (Fin.castAdd b i) * (A.W τ).grDeg i) + ∑ i : Fin b, mu τ (Fin.natAdd a i) * (A.S τ).grDeg i.rev + ∑ l, mu τ l * h (τ, l) = ∑ i : Fin a, mu τ (Fin.castAdd b i) * (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i) + ∑ i : Fin b, mu τ (Fin.natAdd a i) * (h (τ, Fin.na …`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `abs_sum_fin_le (fun i : Fin a => mu τ (Fin.castAdd b i) * (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i)) (2 * C) fun i => by`. Rewrite using `[abs_mul]`. Conclude with `mul_le_mul (hmu _ _) (hW τ i) (abs_nonneg _) (by norm_num)`. Establish `h2` using `abs_sum_fin_le (fun i : Fin b => mu τ (Fin.natAdd a i) * (h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev)) (2 * C) fun i => by`.

Rewrite using `[abs_mul]`. Conclude with `mul_le_mul (hmu _ _) (hS τ i) (abs_nonneg _) (by norm_num)`. Establish `h1'` using `(abs_le.1 h1).2`. Establish `h2'` using `(abs_le.1 h2).2`. Use the polynomial consequences of the given equalities and inequalities.

Unfold `FlagPair.lamDeg`. Use `(Finset.sum_le_sum fun τ _ => key τ).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, Finset.sum_neg_distrib]`. Simplify using the standard rewrite rules.
-/
theorem lamDeg_le (A : FlagPair E Ψ a b) (h : Ψ × Fin (a + b) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ τ (i : Fin a), |h (τ, Fin.castAdd b i) - (A.W τ).grDeg i| ≤ C)
    (hS : ∀ τ (i : Fin b), |h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev| ≤ C)
    (mu : Ψ → Fin (a + b) → ℝ) (hmu : ∀ τ i, |mu τ i| ≤ 2) :
    A.lamDeg mu ≤ -(∑ τ, ∑ l, mu τ l * h (τ, l)) + Fintype.card Ψ * (((a : ℝ) + b) * (2 * C)) := by
  have key : ∀ τ, -(∑ i : Fin a, mu τ (Fin.castAdd b i) * (A.W τ).grDeg i) +
      ∑ i : Fin b, mu τ (Fin.natAdd a i) * (A.S τ).grDeg i.rev ≤
      -(∑ l, mu τ l * h (τ, l)) + ((a : ℝ) + b) * (2 * C) := by
    intro τ
    have e : -(∑ i : Fin a, mu τ (Fin.castAdd b i) * (A.W τ).grDeg i) +
        ∑ i : Fin b, mu τ (Fin.natAdd a i) * (A.S τ).grDeg i.rev + ∑ l, mu τ l * h (τ, l) =
        ∑ i : Fin a, mu τ (Fin.castAdd b i) * (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i) +
        ∑ i : Fin b, mu τ (Fin.natAdd a i) * (h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev) := by
      rw [Fin.sum_univ_add]
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    have h1 := abs_sum_fin_le (fun i : Fin a =>
      mu τ (Fin.castAdd b i) * (h (τ, Fin.castAdd b i) - (A.W τ).grDeg i)) (2 * C) fun i => by
        rw [abs_mul]
        exact mul_le_mul (hmu _ _) (hW τ i) (abs_nonneg _) (by norm_num)
    have h2 := abs_sum_fin_le (fun i : Fin b =>
      mu τ (Fin.natAdd a i) * (h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev)) (2 * C) fun i => by
        rw [abs_mul]
        exact mul_le_mul (hmu _ _) (hS τ i) (abs_nonneg _) (by norm_num)
    have h1' := (abs_le.1 h1).2
    have h2' := (abs_le.1 h2).2
    nlinarith
  unfold FlagPair.lamDeg
  refine (Finset.sum_le_sum fun τ _ => key τ).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp

/- English proof (translation)
Establish `hf : ∀ τ, |A.flatDeg τ| ≤ Cs + ((a : ℝ) + b) * C`. Introduce `τ`. Establish `h1` using `abs_le.1 (flatDeg_sub_le A h C hW hS τ)`. Establish `h2` using `abs_le.1 (hs τ)`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]`. Use `⟨hf, ?_⟩` and prove the remaining obligations. Establish `hw : ∀ τ, -E.normDegree (A.W τ).top ≤ (a : ℝ) * (B + C)`. Introduce `τ`. Rewrite using `[normDegree_top, ← Finset.sum_neg_distrib]`.

Use `(Finset.sum_le_sum (g := fun _ => B + C) fun i _ => ?_).trans (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])` and prove the remaining obligations. Establish `h1` using `abs_le.1 (hW τ i)`. Establish `h2` using `abs_le.1 (hB (τ, Fin.castAdd b i))`. Combine the linear relations using `[h1.1, h1.2, h2.1, h2.2]`. Establish `h0` using `(GlobalTheory.T.orthogonal_flag_degree_comparison K E Ψ a b A hO).1`.

Establish `h1 : ∑ τ, A.flatDeg τ ≤ Fintype.card Ψ * (Cs + ((a : ℝ) + b) * C)`. Use `(Finset.sum_le_sum (g := fun _ => Cs + ((a : ℝ) + b) * C) fun τ _ => (le_abs_self _).trans (hf τ)).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `h2 : ∑ τ, -E.normDegree (A.W τ).top ≤ Fintype.card Ψ * ((a : ℝ) * (B + C))`. Use `(Finset.sum_le_sum (g := fun _ => (a : ℝ) * (B + C)) fun τ _ => hw τ).trans ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem flat_and_deg (A : FlagPair E Ψ a b) (hO : A.IsOrthFull) (h : Ψ × Fin (a + b) → ℝ) (C B Cs : ℝ)
    (hW : ∀ τ (i : Fin a), |h (τ, Fin.castAdd b i) - (A.W τ).grDeg i| ≤ C)
    (hS : ∀ τ (i : Fin b), |h (τ, Fin.natAdd a i) + (A.S τ).grDeg i.rev| ≤ C)
    (hB : ∀ r, |h r| ≤ B) (hs : ∀ τ, |∑ l, h (τ, l)| ≤ Cs) :
    (∀ τ, |A.flatDeg τ| ≤ Cs + ((a : ℝ) + b) * C) ∧
      -E.normDegree ⊤ ≤ Fintype.card Ψ * (Cs + ((a : ℝ) + b) * C) + 2 * (Fintype.card Ψ * ((a : ℝ) * (B + C))) := by
  have hf : ∀ τ, |A.flatDeg τ| ≤ Cs + ((a : ℝ) + b) * C := by
    intro τ
    have h1 := abs_le.1 (flatDeg_sub_le A h C hW hS τ)
    have h2 := abs_le.1 (hs τ)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨hf, ?_⟩
  have hw : ∀ τ, -E.normDegree (A.W τ).top ≤ (a : ℝ) * (B + C) := by
    intro τ
    rw [normDegree_top, ← Finset.sum_neg_distrib]
    refine (Finset.sum_le_sum (g := fun _ => B + C) fun i _ => ?_).trans
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
    have h1 := abs_le.1 (hW τ i)
    have h2 := abs_le.1 (hB (τ, Fin.castAdd b i))
    linarith [h1.1, h1.2, h2.1, h2.2]
  have h0 := (GlobalTheory.T.orthogonal_flag_degree_comparison K E Ψ a b A hO).1
  have h1 : ∑ τ, A.flatDeg τ ≤ Fintype.card Ψ * (Cs + ((a : ℝ) + b) * C) := by
    refine (Finset.sum_le_sum (g := fun _ => Cs + ((a : ℝ) + b) * C) fun τ _ => (le_abs_self _).trans (hf τ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ τ, -E.normDegree (A.W τ).top ≤ Fintype.card Ψ * ((a : ℝ) * (B + C)) := by
    refine (Finset.sum_le_sum (g := fun _ => (a : ℝ) * (B + C)) fun τ _ => hw τ).trans ?_
    simp
  linarith

end Core

section Root

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

/- English proof (translation)
Simplify using `[rootHt, Fintype.sum_option, RootModel.coef, RootModel.line]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rootHt_zero_one (R : RootModel Ψ N) (L : Type) [Field L] [NumberField L] (w : (Σ k, R.ι k) → L) :
    rootHt R 1 0 1 L w = lineHt R.A L w / R.kA := by
  simp [rootHt, Fintype.sum_option, RootModel.coef, RootModel.line]
  ring

/- English proof (translation)
Simplify using `[rootHt, Fintype.sum_option, RootModel.coef, RootModel.line, Fintype.sum_prod_type]`.
-/
theorem rootHt_mu_zero (R : RootModel Ψ N) (mu : Wt Ψ N) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, R.ι k) → L) :
    rootHt R 1 mu 0 L w = -∑ τ, ∑ l, mu τ l * lineHt (R.x 1 (τ, l)) L w := by
  simp [rootHt, Fintype.sum_option, RootModel.coef, RootModel.line, Fintype.sum_prod_type]

/- English proof (translation)
Establish `h1 : ‖mu τ‖ ≤ ‖mu‖` using `norm_le_pi_norm mu τ`. Establish `h2 : ‖mu τ i‖ ≤ ‖mu τ‖` using `norm_le_pi_norm (mu τ) i`. Rewrite `h2` using `[Real.norm_eq_abs]`. Conclude with `h2.trans h1`.
-/
theorem abs_entry_le (mu : Wt Ψ N) (τ : Ψ) (i : Fin N) : |mu τ i| ≤ ‖mu‖ := by
  have h1 : ‖mu τ‖ ≤ ‖mu‖ := norm_le_pi_norm mu τ
  have h2 : ‖mu τ i‖ ≤ ‖mu τ‖ := norm_le_pi_norm (mu τ) i
  rw [Real.norm_eq_abs] at h2
  exact h2.trans h1

end Root

/- English proof (translation)
Take `⟨C, hC0, hI⟩` from `hFi`. Take `⟨⟨K₀, hK₀⟩, hB⟩` from `GlobalTheory.T.ample_height_bounds R.K R.ι R.Ω R.y _ R.arith R.birational R.A R.A_smooth hA`. Use `choose n c hn hbd using fun r => hB (R.x 1 r) (R.x_smooth 1 r)`. Establish `hflat : ∀ τ, ∃ c' : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal R.y), |∑ l, lineHt (R.x 1 (τ, l)) L w| ≤ c'`. Introduce `τ`.

Take `⟨kk, u, c0, hk, hu, hv⟩` from `hFl τ`. Establish `ha : (combLine (fun l => R.x 1 (τ, l)) fun _ => 1).a = fun b => ∑ i, R.xdeg (τ, i) b`. Use function extensionality and compare the values at `b`. Simplify using `[combLine, Finset.sum_apply, R.x_deg]`. Take `⟨c', hc'⟩` from `GlobalTheory.T.line_height_bounded_unit R.K R.ι R.Ω R.y _ R.arith R.birational (combLine (fun l => R.x 1 (τ, l)) fun _ => 1) kk u c0 (isSmoothHerm_combLine_one _ fun l => R.x_smooth 1 _) hk (by rw [ha]; exact hu) (by rw [ha]; exact hv)`.

Use `⟨c', fun L _ _ w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[← lineHt_combLine_one _ L w hw.1]`. Conclude with `hc' L w hw`. Use `choose cf hcf using hflat`. Take `⟨K1, hK1⟩ : ∃ v, v = |K₀|` from `⟨_, rfl⟩`.

Establish `hK10 : 0 ≤ K1` using `hK1 ▸ abs_nonneg _`. Take `⟨nn, hnn⟩ : ∃ v, v = ∑ r, n r` from `⟨_, rfl⟩`. Take `⟨cc, hcc⟩ : ∃ v, v = ∑ r, |c r|` from `⟨_, rfl⟩`. Take `⟨Cs, hCs⟩ : ∃ v, v = ∑ τ, |cf τ|` from `⟨_, rfl⟩`. Establish `hnn0 : 0 ≤ nn` using `hnn ▸ Finset.sum_nonneg fun r _ => hn r`.

Establish `hcc0 : 0 ≤ cc` using `hcc ▸ Finset.sum_nonneg fun r _ => abs_nonneg _`. Establish `hCs0 : 0 ≤ Cs` using `hCs ▸ Finset.sum_nonneg fun r _ => abs_nonneg _`. Take `⟨f, hf⟩ : ∃ v : ℝ, v = Fintype.card Ψ` from `⟨_, rfl⟩`. Establish `hf0 : 0 ≤ f` using `hf ▸ Nat.cast_nonneg _`. Take `⟨a, ha⟩ : ∃ v : ℝ, v = ((j + 1 : ℕ) : ℝ)` from `⟨_, rfl⟩`.

Take `⟨b, hb⟩ : ∃ v : ℝ, v = ((k + 1 : ℕ) : ℝ)` from `⟨_, rfl⟩`. Establish `ha0 : 0 ≤ a` using `ha ▸ Nat.cast_nonneg _`. Establish `hb0 : 0 ≤ b` using `hb ▸ Nat.cast_nonneg _`. Take `⟨kA, hkA⟩ : ∃ v : ℝ, v = R.kA` from `⟨_, rfl⟩`. Establish `hkA1 : 1 ≤ kA` using `by rw [hkA]; exact_mod_cast R.kA_pos`.

Take `⟨Cf, hCf⟩ : ∃ v, v = Cs + (a + b) * C` from `⟨_, rfl⟩`. Establish `hCf0 : 0 ≤ Cf` using `by rw [hCf]; positivity`. Take `⟨n1, hn1⟩ : ∃ v, v = 2 * (f * (a * (nn * kA)))` from `⟨_, rfl⟩`. Establish `hn10 : 0 ≤ n1` using `by rw [hn1]; positivity`. Take `⟨C', hC'⟩ : ∃ v, v = f * Cf + 2 * (f * (a * (nn * K1 + cc + C)))` from `⟨_, rfl⟩`.

Establish `hC'0 : 0 ≤ C'` using `by rw [hC']; positivity`. Take `⟨Cm, hCm⟩ : ∃ v, v = C + C'` from `⟨_, rfl⟩`. Establish `hCm0 : 0 ≤ Cm` using `by rw [hCm]; positivity`. Take `⟨C₁, h11, hKC, hlog⟩` from `GlobalTheory.CompanionTheory.LogLin.exists_log_affine_le Cm n1 K1 hCm0 hn10 hK10`. Take `⟨Q, hQ⟩ : ∃ v, v = 4 * f * (a + b)` from `⟨_, rfl⟩`.

Take `⟨T, hT⟩ : ∃ v, v = 2 * f * Cf + 2 * f * (a + b) * C` from `⟨_, rfl⟩`. Establish `hQ0 : 0 ≤ Q` using `by rw [hQ]; positivity`. Establish `hT0 : 0 ≤ T` using `by rw [hT]; positivity`. Establish `hQC : 0 ≤ Q * C₁` using `mul_nonneg hQ0 (by linarith)`. Take `⟨D, hD⟩ : ∃ v, v = 1 + C₁ + Q * C₁ + T` from `⟨_, rfl⟩`.

Use `⟨D, by linarith, fun L _ _ w hw => ?_⟩` and prove the remaining obligations. Establish `hhA : -K1 ≤ lineHt R.A L w`. Establish `h1` using `hK₀ L w hw`. Establish `h2 : K₀ ≤ K1` using `hK1 ▸ le_abs_self _`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨x, hx⟩ : ∃ v, v = rootHt R 1 0 1 L w` from `⟨_, rfl⟩`. Establish `hxA : lineHt R.A L w = kA * x`. Rewrite using `[hx, rootHt_zero_one, ← hkA]`. Clear the denominators using the available nonvanishing facts. Establish `hxK : -K1 ≤ x`.

Rewrite `hhA` using `[hxA]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hxC : -C₁ ≤ x` using `by linarith`. Rewrite using `[← hx]`. Use `⟨by linarith, fun mu hd hmu => ?_⟩` and prove the remaining obligations.

Take `⟨L', iF, iN, φ, E, A, hO, hW, hS, hSl⟩` from `hI L w hw`. Establish `hbnd : ∀ r, |lineHt (R.x 1 r) L w| ≤ nn * (kA * x + K1) + cc`. Introduce `r`. Establish `h1` using `hbd r L w hw`. Establish `h2 : n r ≤ nn` using `hnn ▸ Finset.single_le_sum (f := n) (fun r _ => hn r) (Finset.mem_univ r)`.

Establish `h3 : |c r| ≤ cc` using `hcc ▸ Finset.single_le_sum (f := fun r => |c r|) (fun r _ => abs_nonneg _) (Finset.mem_univ r)`. Establish `h4 : 0 ≤ kA * x + K1` using `by rw [← hxA]; linarith`. Establish `h5 : n r * (kA * x + K1) ≤ nn * (kA * x + K1)` using `mul_le_mul_of_nonneg_right h2 h4`. Establish `h6` using `mul_nonneg (hn r) hK10`. Establish `h7` using `le_abs_self (c r)`.

Rewrite `h1` using `[hxA]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsum : ∀ τ, |∑ l, lineHt (R.x 1 (τ, l)) L w| ≤ Cs`. Introduce `τ`. Use `(hcf τ L w hw).trans ((le_abs_self _).trans ?_)` and prove the remaining obligations.

Conclude with `hCs ▸ Finset.single_le_sum (f := fun τ => |cf τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)`. Take `⟨hfl, hdeg⟩` from `flat_and_deg A hO (fun r => lineHt (R.x 1 r) L w) C _ Cs hW hS hbnd hsum`. Simplify using `only [← ha, ← hb, ← hf, ← hCf] at hfl hdeg`. Establish `hy : -E.normDegree ⊤ ≤ n1 * x + Cm`. Establish `e : f * Cf + 2 * (f * (a * (nn * (kA * x + K1) + cc + C))) = n1 * x + C'`.

Rewrite using `[hn1, hC']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hCm]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨y, hyy⟩ : ∃ v, v = max (-E.normDegree ⊤) 0` from `⟨_, rfl⟩`.

Establish `hp : 0 ≤ y` using `hyy ▸ le_max_right _ _`. Take `⟨m, hm⟩ : ∃ v, v = C * Real.log (2 + C + y) + C` from `⟨_, rfl⟩`. Establish `hl1 : 0 ≤ Real.log (2 + C + y)` using `Real.log_nonneg (by linarith)`. Establish `hm0 : 0 ≤ m` using `by rw [hm]; positivity`. Establish `hCCm : C ≤ Cm` using `by linarith`.

Establish `hl2 : Real.log (2 + C + y) ≤ Real.log (2 + Cm + y)` using `Real.log_le_log (by linarith) (by linarith)`. Establish `hmC : m ≤ C₁ * Real.log (2 + C₁ + x)`. Use `le_trans ?_ (hlog x _ hxK hy)` and prove the remaining obligations. Rewrite using `[← hyy, hm]`. Use `mul_le_mul hCCm hl2 hl1 hCm0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsl : E.slopeMax ≤ (m : EReal)`. Rewrite using `[hm, hyy]`. Conclude with `hSl`. Establish `hent : ∀ τ i, |mu τ i| ≤ 2` using `fun τ i => (abs_entry_le mu τ i).trans hmu`.

Establish `hlow` using `GlobalTheory.T.weighted_flag_degree_lower_bound L' E Ψ j k A mu 2 m Cf (fun τ a b hab => hd τ a b hab) hent hm0 hsl hfl`. Establish `hup` using `lamDeg_le A (fun r => lineHt (R.x 1 r) L w) C hC0 hW hS mu hent`. Simplify using `only [← ha, ← hb, ← hf] at hup`. Establish `hab : (j : ℝ) + 1 + ((k : ℝ) + 1) = a + b`. Rewrite using `[ha, hb]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hlow` using `[hab, ← hf]`. Rewrite using `[rootHt_mu_zero]`. Establish `hl3 : 0 ≤ Real.log (2 + C₁ + x)` using `Real.log_nonneg (by linarith)`.

Establish `hl4 : Real.log (2 + C₁ + x) ≤ Real.log (2 + D + x)` using `Real.log_le_log (by linarith) (by linarith)`. Establish `hDl : Q * C₁ * Real.log (2 + C₁ + x) ≤ D * Real.log (2 + D + x)` using `mul_le_mul (by linarith) hl4 hl3 (by linarith)`. Establish `hQm : Q * m ≤ Q * (C₁ * Real.log (2 + C₁ + x))` using `mul_le_mul_of_nonneg_left hmC hQ0`. Establish `e1 : f * (2 * 2 * (a + b) * m + 2 * Cf) = Q * m + 2 * f * Cf`. Rewrite using `[hQ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : f * ((a + b) * (2 * C)) = 2 * f * (a + b) * C` using `by ring`. Establish `e3 : Q * (C₁ * Real.log (2 + C₁ + x)) = Q * C₁ * Real.log (2 + C₁ + x)` using `by ring`. Rewrite `hlow` using `[e1]`. Rewrite `hup` using `[e2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem refLower_of_fibre (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (R : RootModel Ψ (j + 1 + (k + 1)))
    (hA : AmpleQ R.y R.A.a) (hFl : FlatUnit R) (hFi : FibreInput R) : RefLower R := by
  classical
  obtain ⟨C, hC0, hI⟩ := hFi
  obtain ⟨⟨K₀, hK₀⟩, hB⟩ := GlobalTheory.T.ample_height_bounds R.K R.ι R.Ω R.y _ R.arith R.birational R.A R.A_smooth hA
  choose n c hn hbd using fun r => hB (R.x 1 r) (R.x_smooth 1 r)
  have hflat : ∀ τ, ∃ c' : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal R.y),
      |∑ l, lineHt (R.x 1 (τ, l)) L w| ≤ c' := by
    intro τ
    obtain ⟨kk, u, c0, hk, hu, hv⟩ := hFl τ
    have ha : (combLine (fun l => R.x 1 (τ, l)) fun _ => 1).a = fun b => ∑ i, R.xdeg (τ, i) b := by
      funext b
      simp [combLine, Finset.sum_apply, R.x_deg]
    obtain ⟨c', hc'⟩ := GlobalTheory.T.line_height_bounded_unit R.K R.ι R.Ω R.y _ R.arith R.birational
      (combLine (fun l => R.x 1 (τ, l)) fun _ => 1) kk u c0
      (isSmoothHerm_combLine_one _ fun l => R.x_smooth 1 _) hk (by rw [ha]; exact hu) (by rw [ha]; exact hv)
    refine ⟨c', fun L _ _ w hw => ?_⟩
    rw [← lineHt_combLine_one _ L w hw.1]
    exact hc' L w hw
  choose cf hcf using hflat
  obtain ⟨K1, hK1⟩ : ∃ v, v = |K₀| := ⟨_, rfl⟩
  have hK10 : 0 ≤ K1 := hK1 ▸ abs_nonneg _
  obtain ⟨nn, hnn⟩ : ∃ v, v = ∑ r, n r := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ v, v = ∑ r, |c r| := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ v, v = ∑ τ, |cf τ| := ⟨_, rfl⟩
  have hnn0 : 0 ≤ nn := hnn ▸ Finset.sum_nonneg fun r _ => hn r
  have hcc0 : 0 ≤ cc := hcc ▸ Finset.sum_nonneg fun r _ => abs_nonneg _
  have hCs0 : 0 ≤ Cs := hCs ▸ Finset.sum_nonneg fun r _ => abs_nonneg _
  obtain ⟨f, hf⟩ : ∃ v : ℝ, v = Fintype.card Ψ := ⟨_, rfl⟩
  have hf0 : 0 ≤ f := hf ▸ Nat.cast_nonneg _
  obtain ⟨a, ha⟩ : ∃ v : ℝ, v = ((j + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ v : ℝ, v = ((k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ Nat.cast_nonneg _
  have hb0 : 0 ≤ b := hb ▸ Nat.cast_nonneg _
  obtain ⟨kA, hkA⟩ : ∃ v : ℝ, v = R.kA := ⟨_, rfl⟩
  have hkA1 : 1 ≤ kA := by rw [hkA]; exact_mod_cast R.kA_pos
  obtain ⟨Cf, hCf⟩ : ∃ v, v = Cs + (a + b) * C := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  obtain ⟨n1, hn1⟩ : ∃ v, v = 2 * (f * (a * (nn * kA))) := ⟨_, rfl⟩
  have hn10 : 0 ≤ n1 := by rw [hn1]; positivity
  obtain ⟨C', hC'⟩ : ∃ v, v = f * Cf + 2 * (f * (a * (nn * K1 + cc + C))) := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  obtain ⟨Cm, hCm⟩ : ∃ v, v = C + C' := ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  obtain ⟨C₁, h11, hKC, hlog⟩ := GlobalTheory.CompanionTheory.LogLin.exists_log_affine_le Cm n1 K1 hCm0 hn10 hK10
  obtain ⟨Q, hQ⟩ : ∃ v, v = 4 * f * (a + b) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ v, v = 2 * f * Cf + 2 * f * (a + b) * C := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hQC : 0 ≤ Q * C₁ := mul_nonneg hQ0 (by linarith)
  obtain ⟨D, hD⟩ : ∃ v, v = 1 + C₁ + Q * C₁ + T := ⟨_, rfl⟩
  refine ⟨D, by linarith, fun L _ _ w hw => ?_⟩

  have hhA : -K1 ≤ lineHt R.A L w := by
    have h1 := hK₀ L w hw
    have h2 : K₀ ≤ K1 := hK1 ▸ le_abs_self _
    linarith
  obtain ⟨x, hx⟩ : ∃ v, v = rootHt R 1 0 1 L w := ⟨_, rfl⟩
  have hxA : lineHt R.A L w = kA * x := by
    rw [hx, rootHt_zero_one, ← hkA]
    field_simp
  have hxK : -K1 ≤ x := by
    rw [hxA] at hhA
    nlinarith
  have hxC : -C₁ ≤ x := by linarith
  rw [← hx]
  refine ⟨by linarith, fun mu hd hmu => ?_⟩
  obtain ⟨L', iF, iN, φ, E, A, hO, hW, hS, hSl⟩ := hI L w hw
  have hbnd : ∀ r, |lineHt (R.x 1 r) L w| ≤ nn * (kA * x + K1) + cc := by
    intro r
    have h1 := hbd r L w hw
    have h2 : n r ≤ nn := hnn ▸ Finset.single_le_sum (f := n) (fun r _ => hn r) (Finset.mem_univ r)
    have h3 : |c r| ≤ cc :=
      hcc ▸ Finset.single_le_sum (f := fun r => |c r|) (fun r _ => abs_nonneg _) (Finset.mem_univ r)
    have h4 : 0 ≤ kA * x + K1 := by rw [← hxA]; linarith
    have h5 : n r * (kA * x + K1) ≤ nn * (kA * x + K1) := mul_le_mul_of_nonneg_right h2 h4
    have h6 := mul_nonneg (hn r) hK10
    have h7 := le_abs_self (c r)
    rw [hxA] at h1
    nlinarith
  have hsum : ∀ τ, |∑ l, lineHt (R.x 1 (τ, l)) L w| ≤ Cs := by
    intro τ
    refine (hcf τ L w hw).trans ((le_abs_self _).trans ?_)
    exact hCs ▸ Finset.single_le_sum (f := fun τ => |cf τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  obtain ⟨hfl, hdeg⟩ := flat_and_deg A hO (fun r => lineHt (R.x 1 r) L w) C _ Cs hW hS hbnd hsum
  simp only [← ha, ← hb, ← hf, ← hCf] at hfl hdeg
  have hy : -E.normDegree ⊤ ≤ n1 * x + Cm := by
    have e : f * Cf + 2 * (f * (a * (nn * (kA * x + K1) + cc + C))) = n1 * x + C' := by
      rw [hn1, hC']
      ring
    rw [hCm]
    linarith
  obtain ⟨y, hyy⟩ : ∃ v, v = max (-E.normDegree ⊤) 0 := ⟨_, rfl⟩
  have hp : 0 ≤ y := hyy ▸ le_max_right _ _
  obtain ⟨m, hm⟩ : ∃ v, v = C * Real.log (2 + C + y) + C := ⟨_, rfl⟩
  have hl1 : 0 ≤ Real.log (2 + C + y) := Real.log_nonneg (by linarith)
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hCCm : C ≤ Cm := by linarith
  have hl2 : Real.log (2 + C + y) ≤ Real.log (2 + Cm + y) := Real.log_le_log (by linarith) (by linarith)
  have hmC : m ≤ C₁ * Real.log (2 + C₁ + x) := by
    refine le_trans ?_ (hlog x _ hxK hy)
    rw [← hyy, hm]
    have := mul_le_mul hCCm hl2 hl1 hCm0
    linarith
  have hsl : E.slopeMax ≤ (m : EReal) := by
    rw [hm, hyy]
    exact hSl
  have hent : ∀ τ i, |mu τ i| ≤ 2 := fun τ i => (abs_entry_le mu τ i).trans hmu
  have hlow := GlobalTheory.T.weighted_flag_degree_lower_bound L' E Ψ j k A mu 2 m Cf (fun τ a b hab => hd τ a b hab) hent hm0 hsl hfl
  have hup := lamDeg_le A (fun r => lineHt (R.x 1 r) L w) C hC0 hW hS mu hent
  simp only [← ha, ← hb, ← hf] at hup
  have hab : (j : ℝ) + 1 + ((k : ℝ) + 1) = a + b := by
    rw [ha, hb]
    push_cast
    ring
  rw [hab, ← hf] at hlow
  rw [rootHt_mu_zero]
  have hl3 : 0 ≤ Real.log (2 + C₁ + x) := Real.log_nonneg (by linarith)
  have hl4 : Real.log (2 + C₁ + x) ≤ Real.log (2 + D + x) :=
    Real.log_le_log (by linarith) (by linarith)
  have hDl : Q * C₁ * Real.log (2 + C₁ + x) ≤ D * Real.log (2 + D + x) :=
    mul_le_mul (by linarith) hl4 hl3 (by linarith)
  have hQm : Q * m ≤ Q * (C₁ * Real.log (2 + C₁ + x)) := mul_le_mul_of_nonneg_left hmC hQ0
  have e1 : f * (2 * 2 * (a + b) * m + 2 * Cf) = Q * m + 2 * f * Cf := by
    rw [hQ]
    ring
  have e2 : f * ((a + b) * (2 * C)) = 2 * f * (a + b) * C := by ring
  have e3 : Q * (C₁ * Real.log (2 + C₁ + x)) = Q * C₁ * Real.log (2 + C₁ + x) := by ring
  rw [e1] at hlow
  rw [e2] at hup
  linarith

end GlobalTheory.CompanionTheory.Ar.Ht.RefLow
