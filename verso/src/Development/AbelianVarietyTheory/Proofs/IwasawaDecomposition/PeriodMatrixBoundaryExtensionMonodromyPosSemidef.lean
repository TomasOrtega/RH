import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonnegStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydiscStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerExt

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [logExp, Pi.add_apply]`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `[hj, Complex.exp_add]`.

Simplify using `[Pi.single_apply, hk]`.
-/
theorem logExp_add_single {n a : ℕ} (s : Fin n → ℂ) (j : Fin n) (hj : (j : ℕ) < a) :
    logExp a (s + Pi.single j (2 * Real.pi * Complex.I)) = logExp a s := by
  funext k
  simp only [logExp, Pi.add_apply]
  by_cases hk : k = j
  · subst hk
    simp [hj, Complex.exp_add]
  · simp [Pi.single_apply, hk]

/- English proof (translation)
Introduce `k`. Use `hs k` as an intermediate fact. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `only [if_pos hj] at this ⊢`.

Simplify using `using this`. Simplify `this` using `[Pi.single_apply, hk]`.
-/
theorem mem_logDom_add_single {n a : ℕ} {s : Fin n → ℂ} (hs : s ∈ logDom n a) (j : Fin n) (hj : (j : ℕ) < a) :
    s + Pi.single j (2 * Real.pi * Complex.I) ∈ logDom n a := by
  intro k
  have := hs k
  by_cases hk : k = j
  · subst hk
    simp only [if_pos hj] at this ⊢
    simpa using this
  · simpa [Pi.single_apply, hk] using this

/- English proof (translation)
Simplify using `[Matrix.mulVec_single, single_dotProduct]`.
-/
theorem quad_single {R : Type} [CommRing R] {g : ℕ} (M : Matrix (Fin g) (Fin g) R) (i : Fin g) :
    dotProduct (Pi.single i 1) (M.mulVec (Pi.single i 1)) = M i i := by
  simp [Matrix.mulVec_single, single_dotProduct]

/- English proof (translation)
Simplify using `only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single, single_dotProduct]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_add {R : Type} [CommRing R] {g : ℕ} (M : Matrix (Fin g) (Fin g) R) (i j : Fin g) :
    dotProduct (Pi.single i 1 + Pi.single j 1) (M.mulVec (Pi.single i 1 + Pi.single j 1)) =
      M i i + M i j + M j i + M j j := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single, single_dotProduct]
  simp
  ring

/- English proof (translation)
Use function extensionality and compare the values at `l`. Distinguish the cases in `h : l = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
theorem cast_single {g : ℕ} (i : Fin g) : (fun l => ((Pi.single i (1 : ℤ) : Fin g → ℤ) l : ℂ)) = Pi.single i 1 := by
  funext l
  by_cases h : l = i
  · subst h; simp
  · simp [Pi.single_apply, h]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Apply the tactic sequence `by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [Pi.single_apply, h1, h2]`.
-/
theorem cast_single_add {g : ℕ} (i j : Fin g) :
    (fun l => (((Pi.single i (1 : ℤ) + Pi.single j 1 : Fin g → ℤ)) l : ℂ)) = Pi.single i 1 + Pi.single j 1 := by
  funext l
  by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [Pi.single_apply, h1, h2]

/- English proof (translation)
Introduce `n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon`. Establish `hs₀ : ∃ s₀, s₀ ∈ logDom n a ∧ logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ₁`. Use `⟨fun k => if (k : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Distinguish the cases in `hk : (k : ℕ) < a`.

Simplify using `only [if_pos hk, Complex.ofReal_re]`. Conclude with `Real.log_neg (by positivity) (by linarith)`. Simplify using `[hk]`. Rewrite using `[mem_ball_zero_iff, pi_norm_lt_iff hρ]`. Introduce `k`.

Distinguish the cases in `hk : (k : ℕ) < a`. Simplify using `only [logExp, if_pos hk]`. Rewrite using `[← Complex.ofReal_exp, Real.exp_log (by positivity), Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[logExp, hk, hρ]`.

Take `⟨s₀, hs₀D, hs₀B⟩` from `hs₀`. Establish `hBsym : ∀ k, (B k).IsSymm`. Introduce `k`. Establish `hj : ((Fin.castLE ha k : Fin n) : ℕ) < a` using `by simp`. Establish `h1` using `hmon s₀ hs₀D hs₀B k`.

Establish `h2` using `(hsym _ (mem_logDom_add_single hs₀D _ hj) (by rw [logExp_add_single _ _ hj]; exact hs₀B)).1`. Establish `h3` using `(hsym s₀ hs₀D hs₀B).1`. Rewrite `h2` using `[h1]`. Use `Matrix.IsSymm.ext fun i j => ?_` and prove the remaining obligations. Establish `e1` using `congrFun (congrFun h2 i) j`.

Establish `e2` using `congrFun (congrFun h3 i) j`. Simplify using `only [Matrix.transpose_apply, Matrix.add_apply, Matrix.map_apply] at e1 e2`. Establish `: ((B k j i : ℤ) : ℂ) = B k i j` using `by rw [e2] at e1; exact add_left_cancel e1`. Conclude with `this` after adjusting the coercions. Establish `hnn` using `GlobalTheory.T.monodromy_matrix_dotProduct_nonneg_integral n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon`.

Use `⟨fun k => GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg g (B k) (hBsym k) (hnn k), ?_⟩` and prove the remaining obligations. Establish `hF : ∀ v : Fin g → ℤ, ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) …` using `fun v => GlobalTheory.T.periodQuadForm_extends_holomorphic_punctPolydisc n a g ha ρ₁ τ B v hρ hρ1 hdiff hsym hmon (fun k => hnn k v)`. Use `choose F hFd hFe using hF`. Set `e : Fin g → Fin g → ℤ` to `fun i => Pi.single i 1`. Use `⟨fun z => Matrix.of fun i j => if i = j then F (e i) z else (F (e i + e j) z - F (e i) z - F (e j) z) / 2, fun i j => ?_, fun z _ => ?_, fun s hs hsB => ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `hij : i = j`. Simplify using `only [if_pos hij]`. Conclude with `hFd _`. Simplify using `only [if_neg hij]`.

Establish `h1` using `hFd (e i + e j)`. Establish `h2` using `hFd (e i)`. Establish `h3` using `hFd (e j)`. Use `fun_prop`. Use `Matrix.IsSymm.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Both sides reduce to the same expression. Rewrite using `[if_neg (Ne.symm hij), if_neg hij, add_comm (e j)]`.

Expand and normalize the polynomial expressions, which then agree. Use `Matrix.ext fun i j => ?_ beta_reduce` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply]`. Establish `hsm : ∀ k, ((s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) i j = s (Fin.castLE ha k) / (2 * Real.pi * Complex.I) * ((B k i j : ℤ) : ℂ)` using `fun k => rfl`. Rewrite using `[Finset.sum_congr rfl fun k _ => hsm k]`.

Use `set c : ℂ := 2 * Real.pi * Complex.I`. Establish `hi` using `hFe (e i) s hs hsB`. Establish `hj` using `hFe (e j) s hs hsB`. Simplify using `only [e, cast_single, quad_single] at hi hj`. Establish `hsum1 : ∀ l, ∑ k, s (Fin.castLE ha k) * ((B k l l : ℤ) : ℂ) / c = ∑ k, s (Fin.castLE ha k) / c * ((B k l l : ℤ) : ℂ)` using `fun l => Finset.sum_congr rfl fun k _ => by ring`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[if_pos rfl]`. Establish `hee : F (e i) (logExp a s) = F (Pi.single i 1) (logExp a s)` using `rfl`. Rewrite using `[hee, ← hi, hsum1 i]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [if_neg hij]`. Establish `hp` using `hFe (e i + e j) s hs hsB`. Simplify using `only [e, cast_single_add, quad_add] at hp`. Establish `hsi : (τ s) j i = (τ s) i j` using `((hsym s hs hsB).1.apply i j)`.

Establish `hbi : ∀ k, B k j i = B k i j` using `fun k => (hBsym k).apply i j`. Establish `hsum2 : ∑ k, s (Fin.castLE ha k) * ((B k i i + B k i j + B k j i + B k j j : ℤ) : ℂ) / c = ∑ k, s (Fin.castLE ha k) * ((B k i i : ℤ) : ℂ) / c + 2 * ∑ k, s (Fin.castLE ha k) / c * ((B k i j : ℤ) : ℂ) + ∑ k, s (Fin.castLE ha k) * ((B k j j : ℤ) : ℂ) / c`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hbi k]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hp` using `[hsum2]`. Rewrite using `[← hp, ← hi, ← hj, hsi]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem periodMatrix_extension : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ ∃ τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (τ₀ z).IsSymm) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → τ s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ) := by
  intro n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon

  have hs₀ : ∃ s₀, s₀ ∈ logDom n a ∧ logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by
    refine ⟨fun k => if (k : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0, ?_, ?_⟩
    · intro k
      by_cases hk : (k : ℕ) < a
      · simp only [if_pos hk, Complex.ofReal_re]
        exact Real.log_neg (by positivity) (by linarith)
      · simp [hk]
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ]
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [logExp, if_pos hk]
        rw [← Complex.ofReal_exp, Real.exp_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      · simp [logExp, hk, hρ]
  obtain ⟨s₀, hs₀D, hs₀B⟩ := hs₀

  have hBsym : ∀ k, (B k).IsSymm := by
    intro k
    have hj : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
    have h1 := hmon s₀ hs₀D hs₀B k
    have h2 := (hsym _ (mem_logDom_add_single hs₀D _ hj) (by rw [logExp_add_single _ _ hj]; exact hs₀B)).1
    have h3 := (hsym s₀ hs₀D hs₀B).1
    rw [h1] at h2
    refine Matrix.IsSymm.ext fun i j => ?_
    have e1 := congrFun (congrFun h2 i) j
    have e2 := congrFun (congrFun h3 i) j
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.map_apply] at e1 e2
    have : ((B k j i : ℤ) : ℂ) = B k i j := by rw [e2] at e1; exact add_left_cancel e1
    exact_mod_cast this
  have hnn := GlobalTheory.T.monodromy_matrix_dotProduct_nonneg_integral n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon
  refine ⟨fun k => GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg g (B k) (hBsym k) (hnn k), ?_⟩
  have hF : ∀ v : Fin g → ℤ, ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧
      ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
        dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) -
          ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) =
            F (logExp a s) :=
    fun v => GlobalTheory.T.periodQuadForm_extends_holomorphic_punctPolydisc n a g ha ρ₁ τ B v hρ hρ1 hdiff hsym hmon (fun k => hnn k v)
  choose F hFd hFe using hF
  let e : Fin g → Fin g → ℤ := fun i => Pi.single i 1
  refine ⟨fun z => Matrix.of fun i j => if i = j then F (e i) z else (F (e i + e j) z - F (e i) z - F (e j) z) / 2,
    fun i j => ?_, fun z _ => ?_, fun s hs hsB => ?_⟩
  · simp only [Matrix.of_apply]
    by_cases hij : i = j
    · simp only [if_pos hij]; exact hFd _
    · simp only [if_neg hij]
      have h1 := hFd (e i + e j)
      have h2 := hFd (e i)
      have h3 := hFd (e j)
      fun_prop
  · refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.of_apply]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg (Ne.symm hij), if_neg hij, add_comm (e j)]
      ring
  · refine Matrix.ext fun i j => ?_
    beta_reduce
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply]
    have hsm : ∀ k, ((s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) i j =
        s (Fin.castLE ha k) / (2 * Real.pi * Complex.I) * ((B k i j : ℤ) : ℂ) := fun k => rfl
    rw [Finset.sum_congr rfl fun k _ => hsm k]
    set c : ℂ := 2 * Real.pi * Complex.I
    have hi := hFe (e i) s hs hsB
    have hj := hFe (e j) s hs hsB
    simp only [e, cast_single, quad_single] at hi hj
    have hsum1 : ∀ l, ∑ k, s (Fin.castLE ha k) * ((B k l l : ℤ) : ℂ) / c = ∑ k, s (Fin.castLE ha k) / c * ((B k l l : ℤ) : ℂ) :=
      fun l => Finset.sum_congr rfl fun k _ => by ring
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hee : F (e i) (logExp a s) = F (Pi.single i 1) (logExp a s) := rfl
      rw [hee, ← hi, hsum1 i]
      ring
    · simp only [if_neg hij]
      have hp := hFe (e i + e j) s hs hsB
      simp only [e, cast_single_add, quad_add] at hp
      have hsi : (τ s) j i = (τ s) i j := ((hsym s hs hsB).1.apply i j)
      have hbi : ∀ k, B k j i = B k i j := fun k => (hBsym k).apply i j
      have hsum2 : ∑ k, s (Fin.castLE ha k) * ((B k i i + B k i j + B k j i + B k j j : ℤ) : ℂ) / c =
          ∑ k, s (Fin.castLE ha k) * ((B k i i : ℤ) : ℂ) / c + 2 * ∑ k, s (Fin.castLE ha k) / c * ((B k i j : ℤ) : ℂ) +
            ∑ k, s (Fin.castLE ha k) * ((B k j j : ℤ) : ℂ) / c := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hbi k]; push_cast; ring
      rw [hsum2] at hp
      rw [← hp, ← hi, ← hj, hsi]
      ring

end GlobalTheory.ShFam.Hor.LogCh.PerExt
