import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TorsionTranslate

/- English proof (translation)
Establish `h : (n : ℂ) * x = k` using `by exact_mod_cast h₀`. Establish `h1 : ee x ^ n = 1`. Unfold `ee`. Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k, ← h]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `(mem_algebraicClosure_iff).2 ?_` and prove the remaining obligations. Use `IsAlgebraic.of_pow hn ?_` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `isAlgebraic_one`.
-/
theorem ee_mem_Qbar (x : ℝ) (n : ℕ) (hn : 0 < n) (k : ℤ) (h₀ : (n : ℝ) * x = k) : ee x ∈ Qbar := by
  have h : (n : ℂ) * x = k := by exact_mod_cast h₀
  have h1 : ee x ^ n = 1 := by
    unfold ee
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k, ← h]
    congr 1
    ring
  refine (mem_algebraicClosure_iff).2 ?_
  refine IsAlgebraic.of_pow hn ?_
  rw [h1]
  exact isAlgebraic_one

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left, Hf_conj D T (m' • y) x, ← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left, Hf_conj D T y x]`. Simplify using `[mul_assoc]`.
-/
theorem Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (m m' : ℕ) (x y : VC D N N') :
    Hf D T (m • x) (m' • y) = (m * m' : ℕ) * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left, Hf_conj D T (m' • y) x, ← Nat.cast_smul_eq_nsmul ℂ,
    Hf_smul_left, Hf_conj D T y x]
  simp [mul_assoc]

/- English proof (translation)
Introduce `D cc δ hC N N' r b hb F hF t m hm ht`. Establish `hint` using `(GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N' (LaB D (tor0 D cc δ) b) (Or.inl ⟨r, b, hb, rfl⟩)).2.2.1`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨s, ⟨m', hm', hs⟩, rfl⟩` from `hG`.

Take `⟨k, hk⟩` from `hint _ ht _ hs`. Rewrite `hk` using `[Hf_nsmul]`. Establish `hk' : ((m * m' : ℕ) : ℝ) * (Hf D (tor0 D cc δ) t s).im = k`. Rewrite using `[← hk]`. Simplify using the standard rewrite rules.

Establish `hq : ee (-(Hf D (tor0 D cc δ) t s).im / 2) ∈ Qbar`. Use `ee_mem_Qbar _ (2 * (m * m')) (by positivity) (-k) ?_` and prove the remaining obligations. Move the coercions through the operations in `at hk' ⊢`. Take the linear combination `-hk'`. Establish `: U D (tor0 D cc δ) t (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂))) = (⟨_, hq⟩ : Qbar) • U D (tor0 D cc δ) (t + s) (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂))`.

Use function extensionality and compare the values at `z`. Rewrite using `[U_U]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨t + s, ⟨m * m', by positivity, ?_⟩, rfl⟩)` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_nsmul]`. Conclude with `AddSubgroup.nsmul_mem _ ht _`. Rewrite using `[mul_nsmul']`.

Conclude with `AddSubgroup.nsmul_mem _ hs _`. Consider the case `zero`. Establish `: U D (tor0 D cc δ) t (0 : VC D N N' → ℂ) = 0`. Use function extensionality and compare the values at `z`. Simplify using `[U]`.

Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add G G' _ _ h h'`. Establish `: U D (tor0 D cc δ) t (G + G') = U D (tor0 D cc δ) t G + U D (tor0 D cc δ) t G'`. Use function extensionality and compare the values at `z`.

Simplify using `[U, add_mul]`. Rewrite using `[this]`. Conclude with `add_mem h h'`. Consider the case `smul a G _ h`. Establish `: U D (tor0 D cc δ) t (a • G) = a • U D (tor0 D cc δ) t G`.

Use function extensionality and compare the values at `z`. Express the relevant statement in the definitionally equal form `U D (tor0 D cc δ) t (fun z => (a : ℂ) * G z) z = (a : ℂ) * U D (tor0 D cc δ) t G z`. Simplify using `only [U]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem translate_mem : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, ∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → U D (tor0 D cc δ) t F ∈ Tr D (tor0 D cc δ) b := by
  intro D cc δ hC N N' r b hb F hF t m hm ht
  have hint := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N'
    (LaB D (tor0 D cc δ) b) (Or.inl ⟨r, b, hb, rfl⟩)).2.2.1
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨s, ⟨m', hm', hs⟩, rfl⟩ := hG
    obtain ⟨k, hk⟩ := hint _ ht _ hs
    rw [Hf_nsmul] at hk
    have hk' : ((m * m' : ℕ) : ℝ) * (Hf D (tor0 D cc δ) t s).im = k := by
      rw [← hk]; simp
    have hq : ee (-(Hf D (tor0 D cc δ) t s).im / 2) ∈ Qbar := by
      refine ee_mem_Qbar _ (2 * (m * m')) (by positivity) (-k) ?_
      push_cast at hk' ⊢
      linear_combination -hk'
    have : U D (tor0 D cc δ) t (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂))) =
        (⟨_, hq⟩ : Qbar) • U D (tor0 D cc δ) (t + s) (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂)) := by
      funext z
      rw [U_U]
      rfl
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨t + s, ⟨m * m', by positivity, ?_⟩, rfl⟩)
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_nsmul]; exact AddSubgroup.nsmul_mem _ ht _
    · rw [mul_nsmul']; exact AddSubgroup.nsmul_mem _ hs _
  | zero =>
    have : U D (tor0 D cc δ) t (0 : VC D N N' → ℂ) = 0 := by
      funext z; simp [U]
    rw [this]; exact zero_mem _
  | add G G' _ _ h h' =>
    have : U D (tor0 D cc δ) t (G + G') = U D (tor0 D cc δ) t G + U D (tor0 D cc δ) t G' := by
      funext z; simp [U, add_mul]
    rw [this]; exact add_mem h h'
  | smul a G _ h =>
    have : U D (tor0 D cc δ) t (a • G) = a • U D (tor0 D cc δ) t G := by
      funext z
      change U D (tor0 D cc δ) t (fun z => (a : ℂ) * G z) z = (a : ℂ) * U D (tor0 D cc δ) t G z
      simp only [U]; ring
    rw [this]; exact Submodule.smul_mem _ _ h

end GlobalTheory.TorsionTranslate
