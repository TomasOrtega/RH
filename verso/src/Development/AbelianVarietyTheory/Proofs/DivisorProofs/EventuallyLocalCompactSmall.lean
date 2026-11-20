import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

namespace GlobalTheory.GLTwoHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) = ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E))`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]`. Rewrite using `[h]`. Conclude with `Valued.isOpen_integer _`.
-/
theorem isOpen_adicCompletionIntegers_loc (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

/- English proof (translation)
Set `s : (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) → FiniteAdeleRing (𝓞 E) E` to `RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E) (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) cofinite`. Establish `hs : Continuous s` using `(RestrictedProduct.isOpenEmbedding_structureMap isOpen_adicCompletionIntegers_loc).continuous`. Establish `hs0 : s 0 = 0` using `rfl`. Establish `h1 : s ⁻¹' N ∈ 𝓝 (0 : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E)` using `hs.continuousAt.preimage_mem_nhds (by rw [hs0]; exact hN)`. Rewrite `h1` using `[nhds_pi, Filter.mem_pi']`.

Take `⟨I, t, ht, hIt⟩` from `h1`. Use `Filter.mem_of_superset I.finite_toSet.compl_mem_cofinite fun w hw y hy => ?_` and prove the remaining obligations. Establish `hx : s (Pi.single w ⟨y, hy⟩) = singleNU w y`. Use `Subtype.ext (funext fun u => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((Pi.single w (⟨y, hy⟩ : w.adicCompletionIntegers E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) u : u.adicCompletion E) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E u (GlobalTheory.AdelicU.singleFin w y)`.

Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self, Pi.single_eq_same]`. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_ne h, Pi.single_eq_of_ne h]`. Both sides reduce to the same expression.

Rewrite using `[← hx]`. Use `hIt fun u hu => ?_` and prove the remaining obligations. Establish `hne : u ≠ w` using `fun e => hw (e ▸ hu : w ∈ (I : Set _))`. Rewrite using `[Pi.single_eq_of_ne hne]`. Conclude with `mem_of_mem_nhds (ht u)`.
-/
theorem eventually_singleNU_mem {N : Set (FiniteAdeleRing (𝓞 E) E)} (hN : N ∈ 𝓝 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ y ∈ w.adicCompletionIntegers E, singleNU w y ∈ N := by
  classical
  let s : (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) → FiniteAdeleRing (𝓞 E) E :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) cofinite
  have hs : Continuous s :=
    (RestrictedProduct.isOpenEmbedding_structureMap isOpen_adicCompletionIntegers_loc).continuous
  have hs0 : s 0 = 0 := rfl
  have h1 : s ⁻¹' N ∈ 𝓝 (0 : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) :=
    hs.continuousAt.preimage_mem_nhds (by rw [hs0]; exact hN)
  rw [nhds_pi, Filter.mem_pi'] at h1
  obtain ⟨I, t, ht, hIt⟩ := h1
  refine Filter.mem_of_superset I.finite_toSet.compl_mem_cofinite fun w hw y hy => ?_
  have hx : s (Pi.single w ⟨y, hy⟩) = singleNU w y := by
    refine Subtype.ext (funext fun u => ?_)
    change ((Pi.single w (⟨y, hy⟩ : w.adicCompletionIntegers E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) u : u.adicCompletion E) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E u (GlobalTheory.AdelicU.singleFin w y)
    by_cases h : u = w
    · subst h
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, Pi.single_eq_same]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, Pi.single_eq_of_ne h]
      rfl
  rw [← hx]
  refine hIt fun u hu => ?_
  have hne : u ≠ w := fun e => hw (e ▸ hu : w ∈ (I : Set _))
  rw [Pi.single_eq_of_ne hne]
  exact mem_of_mem_nhds (ht u)

end GlobalTheory.GLTwoHecke
