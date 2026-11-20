import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

/- English proof (translation)
Introduce `R _ _ hR x`. Take `⟨htr, -, -, -, -, -, hval, U, -, hq⟩` from `hR`. Set `h : R ≃ₜ R` to `{ toFun := fun y => y * (x : R) invFun := fun y => y * ((x⁻¹ : Rˣ) : R) left_inv := fun y => by simp [mul_assoc] right_inv := fun y => by simp [mul_assoc] continuous_toFun := continuous_id.mul continuous_const continuous_invFun := continuous_id.mul continuous_const }`. Set `f : U → R` to `fun u => (((u : Rˣ) ^ 2 : Rˣ) : R) * (x : R)`. Establish `hf : IsOpenEmbedding f` using `h.isOpenEmbedding.comp (hval.comp hq)`.

Establish `hf1 : f 1 = (x : R)` using `by simp [f]`. Set `a : R → Rˣ` to `fun y => if y ∈ Set.range f then ((Function.invFun f y : U) : Rˣ) else 1`. Establish `haf : ∀ u : U, a (f u) = (u : Rˣ)`. Introduce `u`. Establish `: Function.invFun f (f u) = u` using `Function.leftInverse_invFun hf.injective u`.

Simplify using `only [a, Set.mem_range_self, if_true, this]`. Use `⟨Set.range f, a, hf.isOpen_range, ⟨1, hf1⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Rewrite using `[← hf.continuousAt_iff]`.

Establish `: a ∘ f = fun u : U => (u : Rˣ)` using `funext haf`. Rewrite using `[this]`. Conclude with `continuous_subtype_val.continuousAt`. Introduce `y hy`. Simplify using `only [a, if_neg hy]`.

Introduce and unpack `_ ⟨u, rfl⟩`. Rewrite using `[haf]`. Simplify using `[f]`. Use `haf 1` as an intermediate fact. Rewrite `this` using `[hf1]`.

Simplify using `using this`.
-/
theorem exists_sqrt_near_unit : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ,
    ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧
      (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  classical
  intro R _ _ hR x
  obtain ⟨htr, -, -, -, -, -, hval, U, -, hq⟩ := hR

  let h : R ≃ₜ R :=
    { toFun := fun y => y * (x : R)
      invFun := fun y => y * ((x⁻¹ : Rˣ) : R)
      left_inv := fun y => by simp [mul_assoc]
      right_inv := fun y => by simp [mul_assoc]
      continuous_toFun := continuous_id.mul continuous_const
      continuous_invFun := continuous_id.mul continuous_const }
  let f : U → R := fun u => (((u : Rˣ) ^ 2 : Rˣ) : R) * (x : R)
  have hf : IsOpenEmbedding f :=
    h.isOpenEmbedding.comp (hval.comp hq)
  have hf1 : f 1 = (x : R) := by simp [f]
  let a : R → Rˣ := fun y => if y ∈ Set.range f then ((Function.invFun f y : U) : Rˣ) else 1
  have haf : ∀ u : U, a (f u) = (u : Rˣ) := by
    intro u
    have : Function.invFun f (f u) = u := Function.leftInverse_invFun hf.injective u
    simp only [a, Set.mem_range_self, if_true, this]
  refine ⟨Set.range f, a, hf.isOpen_range, ⟨1, hf1⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hf.continuousAt_iff]
    have : a ∘ f = fun u : U => (u : Rˣ) := funext haf
    rw [this]
    exact continuous_subtype_val.continuousAt
  · intro y hy
    simp only [a, if_neg hy]
  · rintro _ ⟨u, rfl⟩
    rw [haf]
    simp [f]
  · have := haf 1
    rw [hf1] at this
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
