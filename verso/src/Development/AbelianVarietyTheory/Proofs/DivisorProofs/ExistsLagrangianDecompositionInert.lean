import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticesUnramifiedPlaceNoHypothesis
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertWitt

def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  LinearMap.range (LinearMap.pi fun i : Fin n => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ i`. Conclude with `(y i).2`. Introduce `h`. Use `⟨fun i => ⟨x i, h i⟩, funext fun i => rfl⟩` and prove the remaining obligations.
-/
theorem mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (x : Fin n → E) :
    x ∈ stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (y i).2
  · intro h
    refine ⟨fun i => ⟨x i, h i⟩, funext fun i => rfl⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[stdLat, LinearMap.range_eq_map]`. Conclude with `(Module.Finite.fg_top).map _`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `hx : x = ∑ i, x i • Pi.single i (1 : E)`. Use extensionality with `j`. Simplify using `[Pi.single_apply]`. Rewrite using `[hx]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations.

Use `(mem_stdLat _).2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[Pi.single_apply, h]`.
-/
theorem stdLat_isLattice (E : Type) [Field E] [NumberField E] (n : ℕ) : (stdLat E n).IsLattice E := by
  refine ⟨?_, ?_⟩
  · rw [stdLat, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, x i • Pi.single i (1 : E) := by
      ext j; simp [Pi.single_apply]
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine (mem_stdLat _).2 fun j => ?_
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero

end GlobalTheory.InertWitt
