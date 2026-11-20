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
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (m m' : ℕ) (x y : VC D N N') :
    Hf D T (m • x) (m' • y) = (m * m' : ℕ) * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left, Hf_conj D T (m' • y) x, ← Nat.cast_smul_eq_nsmul ℂ,
    Hf_smul_left, Hf_conj D T y x]
  simp [mul_assoc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
