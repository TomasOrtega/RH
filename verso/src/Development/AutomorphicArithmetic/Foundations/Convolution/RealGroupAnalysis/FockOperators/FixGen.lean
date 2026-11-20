import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem psi_add {F : Type} [Field F] [NumberField F] (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem quaternaryForm_add_left {F : Type} [Field F] [NumberField F] (δ : F) (y a v : V4 F) :
    B4 δ (y + a) v = B4 δ y v + B4 δ a v := by
  simp only [B4, Pi.add_apply]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem bilinearFour_comm {F : Type} [Field F] [NumberField F] (δ : F) (y v : V4 F) :
    B4 δ y v = B4 δ v y := by
  simp only [B4]
  ring

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
private theorem quadraticForm_shift_expand {F : Type} [Field F] [NumberField F] (δ : F) (b : A F) (hb : b.2 = 0) (a v : V4 F)
    (ha : ∀ i, (a i).1 = 0) : b * q4 δ (v + a) = b * q4 δ v := by
  have h : ∀ i, b * a i = 0 := fun i => Prod.ext (by
    change b.1 * (a i).1 = 0
    rw [ha i, mul_zero]) (by
    change b.2 * (a i).2 = 0
    rw [hb, zero_mul])
  simp only [q4, Pi.add_apply]
  linear_combination (2 * v 2 + a 2) * h 2 - rt δ * (2 * v 3 + a 3) * h 3 - v 1 * h 0 - (v 0 + a 0) * h 1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion repeatedly using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.fixGen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) Λ, ∀ φ ∈ Fix D.δ Λ, W.Om (wW F) φ ∈ Fix D.δ Λ ∧ ∀ b : A F, b.2 = 0 → W.Om (nU b) φ ∈ Fix D.δ Λ := by
  intro F E _ _ _ _ _ _ _ D W Λ φ hφ
  refine ⟨?_, fun b hb => ?_⟩
  · intro a ha v
    refine ⟨?_, ?_⟩
    · rw [W.Om_w, W.Om_w]
      unfold ft4
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have h := (hφ a ha y).2
      change φ.1 y * ψ (B4 D.δ y (v + a)) = φ.1 y * ψ (B4 D.δ y v)
      have e : B4 D.δ y (v + a) = B4 D.δ y v + B4 D.δ a y := by
        rw [bilinearFour_comm D.δ y (v + a), quaternaryForm_add_left, bilinearFour_comm D.δ v y]
      rw [e, psi_add]
      calc φ.1 y * (ψ (B4 D.δ y v) * ψ (B4 D.δ a y))
          = ψ (B4 D.δ y v) * (ψ (B4 D.δ a y) * φ.1 y) := by ring
        _ = φ.1 y * ψ (B4 D.δ y v) := by rw [h]; ring
    · rw [W.Om_w]
      unfold ft4
      rw [← integral_const_mul]
      have key : ∀ y, ψ (B4 D.δ a v) * (φ.1 y * ψ (B4 D.δ y v)) =
          φ.1 (y + a) * ψ (B4 D.δ (y + a) v) := fun y => by
        rw [quaternaryForm_add_left, psi_add, (hφ a ha y).1]
        ring
      simp_rw [key]
      exact integral_add_right_eq_self (μ := adeleMeasurePi F) (fun y => φ.1 y * ψ (B4 D.δ y v)) a
  · intro a ha v
    have ha1 : ∀ i, (a i).1 = 0 := fun i => (ha i).1
    refine ⟨?_, ?_⟩
    · rw [W.Om_n, W.Om_n, quadraticForm_shift_expand D.δ b hb a v ha1, (hφ a ha v).1]
    · rw [W.Om_n, mul_left_comm, (hφ a ha v).2]
