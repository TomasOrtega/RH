import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramEmpty

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem fibre_eq_dirac_of_unique {V X : Type} [MeasurableSpace V] [MeasurableSpace X] [Subsingleton V]
    [Subsingleton X] (μ : Measure V) (ν : Measure X) (m : X → Measure V) (x₀ : V)
    (hμ : μ Set.univ = 1) (hν : ν Set.univ = 1)
    (h : ∀ φ : V → ℝ≥0∞, Measurable φ → ∫⁻ v, φ v ∂μ = ∫⁻ b, ∫⁻ v, φ v ∂(m b) ∂ν) (S : X) :
    m S = Measure.dirac x₀ := by
  have h1 := h (fun _ => 1) measurable_const
  have hc : (fun b => ∫⁻ _, (1 : ℝ≥0∞) ∂(m b)) = fun _ => m S Set.univ := by
    funext b
    rw [Subsingleton.elim b S]
    simp
  rw [hc] at h1
  simp only [lintegral_const, one_mul, hμ, hν, mul_one] at h1
  ext s _
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [Subsingleton.eq_univ_of_nonempty hs, ← h1]
    simp

end GlobalTheory.CompanionTheory.SW.GramEmpty

open GlobalTheory.CompanionTheory.SW.GramEmpty in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  intro F E _ _ _ _ _ σ _ M J _ R _ _ _ _ _ _ d b lam _ m hm S
  obtain ⟨-, h2, -⟩ := hm
  haveI : Subsingleton (HermR R σ 0) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI : IsEmpty {p : Fin 0 × Fin 0 // p.1 < p.2} := ⟨fun p => p.1.1.elim0⟩
  have hU : {X : Fin 0 → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} = Set.univ := by
    ext X
    simp
  have hμ : coordW R b lam 0 M Set.univ = 1 := by
    unfold coordW
    rw [Measure.pi_of_empty]
    simp
  have hν : coordHerm R σ b lam 0 Set.univ = 1 := by
    unfold coordHerm
    rw [Measure.comap_apply _ (Function.injective_of_subsingleton _)
      (fun s _ => Subsingleton.measurableSet) _ MeasurableSet.univ]
    have : (Set.univ : Set ((Fin 0 → R) × ({p : Fin 0 × Fin 0 // p.1 < p.2} → R ⊗[F] E))) =
        Set.univ ×ˢ Set.univ := by simp
    rw [Set.image_univ_of_surjective, this, Measure.prod_prod, Measure.pi_of_empty, Measure.pi_of_empty]
    · simp
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
  refine fibre_eq_dirac_of_unique _ _ m _ hμ hν (fun φ hφ => ?_) S
  have := h2 φ hφ
  rw [hU, Measure.restrict_univ] at this
  exact this
