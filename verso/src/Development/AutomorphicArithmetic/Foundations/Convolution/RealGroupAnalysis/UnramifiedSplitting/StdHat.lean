import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem psi_add' {K : Type} [Field K] [NumberField K] (a b : A K) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem psi_neg_one {K : Type} [Field K] [NumberField K] {a : A K} (h : ψ (-a) = 1) : ψ a = 1 := by
  have h0 : ψ (0 : A K) = 1 := by simp [ψ]
  have h1 := psi_add' a (-a)
  rw [add_neg_cancel, h, mul_one, h0] at h1
  exact h1.symm

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem isInt_zero {K : Type} [Field K] [NumberField K] (v : P K) : IsInt (0 : Kv v) := by
  simp [IsInt]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem isInt_mul {K : Type} [Field K] [NumberField K] {v : P K} {a b : Kv v}
    (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  unfold IsInt at *
  rw [map_mul]
  exact mul_le_one' ha hb

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
private theorem isInt_neg {K : Type} [Field K] [NumberField K] {v : P K} {a : Kv v}
    (ha : IsInt a) : IsInt (-a) := by
  unfold IsInt at *
  rwa [Valuation.map_neg]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.R2.H.stdHat :
    ∀ (K : Type) [Field K] [NumberField K] (δ : K) (v : P K), Gd δ v → ∀ φ : V4 K → ℂ, Std v φ → Std v (hat φ) := by
  intro K _ _ δ v hG φ hφ
  obtain ⟨hadd, hmul, hcp, -, -, -, -, -, -, -⟩ := sgLaws K v
  have hsg0 : sg v 0 = 0 := by simpa using hadd 0 0

  have hshift : ∀ (x : V4 K) (s : A K) (c : Kv v), IsInt c →
      φ (Function.update x 1 (s + sg v c)) = φ (Function.update x 1 s) := by
    intro x s c hc
    have h1 : Function.update x 1 (s + sg v c) =
        fun i => Function.update x 1 s i + sg v (Function.update (0 : Fin 4 → Kv v) 1 c i) := by
      funext i
      by_cases hi : i = 1
      · subst hi; simp
      · simp [Function.update_of_ne hi, hsg0]
    rw [h1]
    refine hφ.2 _ _ fun i => ?_
    by_cases hi : i = 1
    · subst hi; simpa using hc
    · simpa [Function.update_of_ne hi] using isInt_zero v
  refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
  · by_cases hi : i = 1
    · subst hi
      refine hG.psi.2.2 (cp v (x 1)) fun c hc => ?_
      have key : hat φ x = ψ (-(sg v c * x 1)) * hat φ x := by
        calc hat φ x = ∫ s, φ (Function.update x 1 (s + sg v c)) * ψ (-((s + sg v c) * x 1)) ∂(adeleMeasure K) :=
              (integral_add_right_eq_self
                (fun s => φ (Function.update x 1 s) * ψ (-(s * x 1))) (sg v c)).symm
          _ = ∫ s, ψ (-(sg v c * x 1)) * (φ (Function.update x 1 s) * ψ (-(s * x 1))) ∂(adeleMeasure K) := by
              congr 1
              funext s
              rw [hshift x s c hc, show -((s + sg v c) * x 1) = -(s * x 1) + -(sg v c * x 1) by ring, psi_add']
              ring
          _ = ψ (-(sg v c * x 1)) * hat φ x := integral_const_mul _ _
      have h1 : ψ (-(sg v c * x 1)) = 1 := by
        have h2 : (ψ (-(sg v c * x 1)) - 1) * hat φ x = 0 := by
          rw [sub_mul, one_mul, ← key, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hx)
      have h3 := psi_neg_one h1
      rw [mul_comm (sg v c), hmul, mul_comm] at h3
      exact h3
    · have ex : ∃ s, φ (Function.update x 1 s) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx (by simp [hat, h])
      obtain ⟨s, hs⟩ := ex
      have := hφ.1 _ hs i
      rwa [Function.update_of_ne hi] at this
  · unfold hat
    congr 1
    funext s
    have h1 : Function.update (fun i => x i + sg v (y i)) 1 s =
        fun i => Function.update x 1 s i + sg v (Function.update y 1 0 i) := by
      funext i
      by_cases hi : i = 1
      · subst hi; simp [hsg0]
      · simp [Function.update_of_ne hi]
    have h2 : φ (Function.update (fun i => x i + sg v (y i)) 1 s) = φ (Function.update x 1 s) := by
      rw [h1]
      refine hφ.2 _ _ fun i => ?_
      by_cases hi : i = 1
      · subst hi; simpa using isInt_zero v
      · simpa [Function.update_of_ne hi] using hy i
    rw [h2]
    by_cases h0 : φ (Function.update x 1 s) = 0
    · simp [h0]
    · have hs : IsInt (cp v s) := by simpa using hφ.1 _ h0 1
      have h3 : ψ (-(s * sg v (y 1))) = 1 := by
        rw [← neg_mul, hmul]
        exact hG.psi.2.1 _ (isInt_mul (by rw [map_neg]; exact isInt_neg hs) (hy 1))
      show φ (Function.update x 1 s) * ψ (-(s * (x 1 + sg v (y 1)))) = φ (Function.update x 1 s) * ψ (-(s * x 1))
      rw [show -(s * (x 1 + sg v (y 1))) = -(s * x 1) + -(s * sg v (y 1)) by ring, psi_add', h3, mul_one]
