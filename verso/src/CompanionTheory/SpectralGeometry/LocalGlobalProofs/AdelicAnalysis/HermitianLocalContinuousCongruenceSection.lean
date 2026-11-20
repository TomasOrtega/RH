import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOrbitLocalSectionSubgroupStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR n S hS`. Take `⟨Q, o, -, -, ho, hform⟩` from `GlobalTheory.T.hermitian_orbit_local_section_subgroup F E σ hσ R hR n S hS`. Establish `hc : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[cT]`. Simplify using `[cT, Matrix.one_apply, h, Ne.symm h]`. Establish `ho1 : o 1 = S`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hform]`. Simplify using `[hc]`. Establish `hinv : Function.LeftInverse (Function.invFun o) o` using `Function.leftInverse_invFun ho.injective`. Use `⟨Set.range o, fun S' => ((Function.invFun o S' : Q) : GL (Fin n) (R ⊗[F] E)), ho.isOpen_range, ⟨1, ho1⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hcont : ContinuousOn (Function.invFun o) (Set.range o)`.

Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `h1 : (fun y : Set.range o => Function.invFun o y.1) = ho.isEmbedding.toHomeomorph.symm`. Use function extensionality and compare the values at `y`. Take `⟨_, x, rfl⟩` from `y`. Use `show Function.invFun o (o x) = _`.

Rewrite using `[hinv x]`. Conclude with `ho.isEmbedding.toHomeomorph.eq_symm_apply.2 (Subtype.ext rfl)`. Establish `h2 : Continuous (fun y : Set.range o => Function.invFun o y.1)`. Rewrite using `[h1]`. Conclude with `Homeomorph.continuous _`.

Conclude with `h2`. Conclude with `continuous_subtype_val.comp_continuousOn hcont`. Use `show ((Function.invFun o S : Q) : GL (Fin n) (R ⊗[F] E)) = 1`. Rewrite using `[← ho1, hinv 1]`. Both sides reduce to the same expression.

Introduce and unpack `_ ⟨x, rfl⟩`. Simplify using `only [hinv x]`. Conclude with `hform x`.
-/
theorem exists_local_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → GL (Fin n) (R ⊗[F] E)), IsOpen B ∧ S ∈ B ∧ ContinuousOn g B ∧ g S = 1 ∧ ∀ S' ∈ B, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR n S hS
  obtain ⟨Q, o, -, -, ho, hform⟩ := GlobalTheory.T.hermitian_orbit_local_section_subgroup F E σ hσ R hR n S hS
  have hc : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have ho1 : o 1 = S := by
    apply Subtype.ext
    rw [hform]
    simp [hc]
  have hinv : Function.LeftInverse (Function.invFun o) o := Function.leftInverse_invFun ho.injective
  refine ⟨Set.range o, fun S' => ((Function.invFun o S' : Q) : GL (Fin n) (R ⊗[F] E)),
    ho.isOpen_range, ⟨1, ho1⟩, ?_, ?_, ?_⟩
  · have hcont : ContinuousOn (Function.invFun o) (Set.range o) := by
      rw [continuousOn_iff_continuous_restrict]
      have h1 : (fun y : Set.range o => Function.invFun o y.1) = ho.isEmbedding.toHomeomorph.symm := by
        funext y
        obtain ⟨_, x, rfl⟩ := y
        show Function.invFun o (o x) = _
        rw [hinv x]
        exact ho.isEmbedding.toHomeomorph.eq_symm_apply.2 (Subtype.ext rfl)
      have h2 : Continuous (fun y : Set.range o => Function.invFun o y.1) := by
        rw [h1]
        exact Homeomorph.continuous _
      exact h2
    exact continuous_subtype_val.comp_continuousOn hcont
  · show ((Function.invFun o S : Q) : GL (Fin n) (R ⊗[F] E)) = 1
    rw [← ho1, hinv 1]
    rfl
  · rintro _ ⟨x, rfl⟩
    simp only [hinv x]
    exact hform x

end GlobalTheory.CompanionTheory.SW
