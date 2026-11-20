import Formalism.GaussJetBounds.GenLogInverse
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WtGeProd

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

section General

variable {K : Type u} [NormedField K] {ι : Type v}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem monoWtGe_iff {pi : ℝ} {r : ι → ℝ} {wt : ℝ} {n : ι →₀ ℕ} {c : K} :
    MonoWtGe pi r wt n c ↔ ‖c‖ ≤ pi ^ (wt - dot n r) := Iff.rfl

/- English proof (translation)
Unfold `dot`. Conclude with `Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by push_cast; ring)`.
-/
theorem dot_add (m n : ι →₀ ℕ) (r : ι → ℝ) : dot (m + n) r = dot m r + dot n r := by
  classical
  unfold dot
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by push_cast; ring)

/- English proof (translation)
Simplify using `[dot]`.
-/
theorem dot_zero (r : ι → ℝ) : dot (0 : ι →₀ ℕ) r = 0 := by simp [dot]

/- English proof (translation)
Unfold `dot Finsupp.sum`. Conclude with `Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _)`.
-/
theorem dot_mono (n : ι →₀ ℕ) {r r' : ι → ℝ} (h : ∀ i, r i ≤ r' i) : dot n r ≤ dot n r' := by
  unfold dot Finsupp.sum
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _)

/- English proof (translation)
Introduce `n` and use `le_trans (monoWtGe_iff.mp (hf n)) (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith))`.
-/
theorem wtGe_mono {pi : ℝ} (h0 : 0 < pi) (h1 : pi ≤ 1) {r : ι → ℝ} {w w' : ℝ} (hw : w' ≤ w)
    {f : MvPowerSeries ι K} (hf : WtGe pi r w f) : WtGe pi r w' f := fun n =>
  le_trans (monoWtGe_iff.mp (hf n)) (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith))

/- English proof (translation)
Introduce `n`. Rewrite using `[monoWtGe_iff, MvPowerSeries.coeff_one]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[dot_zero]`.

Simplify using `using Real.rpow_nonneg h0.le _`.
-/
theorem wtGe_one {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) : WtGe pi r 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [monoWtGe_iff, MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp [dot_zero]
  · simpa using Real.rpow_nonneg h0.le _

variable [IsUltrametricDist K]

/- English proof (translation)
Introduce `n`. Rewrite using `[monoWtGe_iff, map_add]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `wtGe_mono h0 h1 (min_le_left w1 w2) hf n`. Conclude with `wtGe_mono h0 h1 (min_le_right w1 w2) hg n`.
-/
theorem wtGe_add {pi : ℝ} (h0 : 0 < pi) (h1 : pi ≤ 1) {r : ι → ℝ} {w1 w2 : ℝ}
    {f g : MvPowerSeries ι K} (hf : WtGe pi r w1 f) (hg : WtGe pi r w2 g) :
    WtGe pi r (min w1 w2) (f + g) := by
  intro n
  rw [monoWtGe_iff, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact wtGe_mono h0 h1 (min_le_left w1 w2) hf n
  · exact wtGe_mono h0 h1 (min_le_right w1 w2) hg n

/- English proof (translation)
Introduce `n`. Rewrite using `[monoWtGe_iff, map_sum]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _) fun i hi => h i hi n`.
-/
theorem wtGe_sum {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {α : Type w} (s : Finset α)
    (F : α → MvPowerSeries ι K) (h : ∀ i ∈ s, WtGe pi r wt (F i)) :
    WtGe pi r wt (∑ i ∈ s, F i) := by
  intro n
  rw [monoWtGe_iff, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
    fun i hi => h i hi n

/- English proof (translation)
Introduce `n`. Rewrite using `[monoWtGe_iff, MvPowerSeries.coeff_mul]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _) fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[norm_mul, ← hx, dot_add]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_add h0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wtGe_mul {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {w1 w2 : ℝ}
    {f g : MvPowerSeries ι K} (hf : WtGe pi r w1 f) (hg : WtGe pi r w2 g) :
    WtGe pi r (w1 + w2) (f * g) := by
  classical
  intro n
  rw [monoWtGe_iff, MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
    fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [norm_mul, ← hx, dot_add]
  calc ‖MvPowerSeries.coeff x.1 f‖ * ‖MvPowerSeries.coeff x.2 g‖
      ≤ pi ^ (w1 - dot x.1 r) * pi ^ (w2 - dot x.2 r) :=
        mul_le_mul (hf x.1) (hg x.2) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (w1 + w2 - (dot x.1 r + dot x.2 r)) := by
        rw [← Real.rpow_add h0]; congr 1; ring

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qk29.wtGe_prod .. | (apply UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (intros; …`.
-/
theorem wtGe_prod {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ)
    (F : α → MvPowerSeries ι K) (h : ∀ i ∈ s, WtGe pi r (wt i) (F i)) :
    WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by
  first | exact UpperTheory.Reformulated.B.Qk29.wtGe_prod .. | (apply UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α s wt F h | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α s wt F | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α s wt | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α s | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using wtGe_one (K := K) h0 r`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Use `wtGe_mul h0 ih hf` as an intermediate fact.

Use `push_cast`. Rewrite using `[add_mul, one_mul]` and apply the resulting hypothesis.
-/
theorem wtGe_pow {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) (k : ℕ) : WtGe pi r (k * wt) (f ^ k) := by
  induction k with
  | zero => simpa using wtGe_one (K := K) h0 r
  | succ k ih =>
    rw [pow_succ]
    have := wtGe_mul h0 ih hf
    push_cast
    rwa [add_mul, one_mul]

end General

/- English proof (translation)
Distinguish the cases in `hfin : (Function.support g).Finite`. Rewrite using `[finsum_eq_sum g hfin]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)`. Rewrite using `[finsum_of_infinite_support hfin]`. Simplify using `using hC`.
-/
theorem norm_finsum_le_of {K : Type u} [NormedField K] [IsUltrametricDist K] {α : Type v}
    {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) : ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

/- English proof (translation)
Introduce `K _ _ pi h0 h1 σ τ _ a r r' wt f ha0 ha hf`. Establish `hs : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha0`. Establish `hp : ∀ d : σ →₀ ℕ, WtGe pi r' (dot d r) (d.prod fun s e => a s ^ e)`. Introduce `d`. Use `wtGe_prod h0 d.support (fun s => (d s : ℝ) * r s) (fun s => a s ^ d s) fun s _ => wtGe_pow h0 (ha s) (d s)` as an intermediate fact.

Simplify `this` using `[dot, Finsupp.sum, Finsupp.prod]`. Introduce `m`. Rewrite using `[monoWtGe_iff, MvPowerSeries.coeff_subst hs]`. Use `norm_finsum_le_of (Real.rpow_nonneg h0.le _) fun d => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem substitution_weight_bound : SubstWt.{u, v, w} := by
  intro K _ _ pi h0 h1 σ τ _ a r r' wt f ha0 ha hf
  classical
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hp : ∀ d : σ →₀ ℕ, WtGe pi r' (dot d r) (d.prod fun s e => a s ^ e) := by
    intro d
    have := wtGe_prod h0 d.support (fun s => (d s : ℝ) * r s) (fun s => a s ^ d s)
      fun s _ => wtGe_pow h0 (ha s) (d s)
    simpa [dot, Finsupp.sum, Finsupp.prod] using this
  intro m
  rw [monoWtGe_iff, MvPowerSeries.coeff_subst hs]
  refine norm_finsum_le_of (Real.rpow_nonneg h0.le _) fun d => ?_
  rw [smul_eq_mul, norm_mul]
  calc ‖MvPowerSeries.coeff d f‖ * ‖MvPowerSeries.coeff m (d.prod fun s e => a s ^ e)‖
      ≤ pi ^ (wt - dot d r) * pi ^ (dot d r - dot m r') :=
        mul_le_mul (hf d) (hp d m) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (wt - dot m r') := by rw [← Real.rpow_add h0]; congr 1; ring

/- English proof (translation)
Introduce `K _ pi h0 h1 ι r r' wt hr`. Establish `key : ∀ (n : ι →₀ ℕ) (c : K), MonoWtGe pi r wt n c → MonoWtGe pi r' wt n c` using `fun n c hc => le_trans (monoWtGe_iff.mp hc) (Real.rpow_le_rpow_of_exponent_ge h0 h1.le (by linarith [dot_mono n hr]))`. Conclude with `⟨fun f hf n => key n _ (hf n), fun κ f hf n hn => key n _ (hf n hn)⟩`.
-/
theorem radical_weight_monotone : RadMono.{u, v} := by
  intro K _ pi h0 h1 ι r r' wt hr
  have key : ∀ (n : ι →₀ ℕ) (c : K), MonoWtGe pi r wt n c → MonoWtGe pi r' wt n c :=
    fun n c hc => le_trans (monoWtGe_iff.mp hc)
      (Real.rpow_le_rpow_of_exponent_ge h0 h1.le (by linarith [dot_mono n hr]))
  exact ⟨fun f hf n => key n _ (hf n), fun κ f hf n hn => key n _ (hf n hn)⟩

end Formalism.DworkPowerSeriesWeights
