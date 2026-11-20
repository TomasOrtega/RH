import Mathlib
import Formalism.UnipotentAdelicQuotients.ClassNumberFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

open NumberField IsDedekindDomain

namespace GlobalTheory.LocusOpenCompact

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simpa using continuous_const`. Consider the case `add p q hp hq => simp only [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]`.

Conclude with `hp.mul (hf i)`.
-/
theorem continuous_aeval_comp {F A X σ : Type} [CommRing F] [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X] (f : X → σ → A)
    (hf : ∀ i, Continuous fun x => f x i) (P : MvPolynomial σ F) :
    Continuous fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hf i)

/- English proof (translation)
Establish `e : HeckeCharacterZeroLocus.zeroLocusGL S A = ⋂ P ∈ S, {g : GL (Fin n) A | MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0}`. Use extensionality with `g`. Simplify using `only [HeckeCharacterZeroLocus.zeroLocusGL, Set.mem_iInter]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Establish `hv : Continuous fun g : GL (Fin n) A => (g : Matrix (Fin n) (Fin n) A)` using `Units.continuous_val`. Conclude with `continuous_aeval_comp (X := GL (Fin n) A) (fun g (ij : Fin n × Fin n) => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) (fun ij => hv.matrix_elem ij.1 ij.2) P`.
-/
theorem isClosed_zeroLocusGL {F : Type} [Field F] {n : ℕ}
    (S : Set (MvPolynomial (Fin n × Fin n) F)) (A : Type) [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosed (HeckeCharacterZeroLocus.zeroLocusGL S A) := by
  have e : HeckeCharacterZeroLocus.zeroLocusGL S A = ⋂ P ∈ S, {g : GL (Fin n) A | MvPolynomial.aeval
      (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0} := by
    ext g; simp only [HeckeCharacterZeroLocus.zeroLocusGL, Set.mem_iInter]; rfl
  rw [e]
  refine isClosed_biInter fun P _ => isClosed_eq ?_ continuous_const
  have hv : Continuous fun g : GL (Fin n) A => (g : Matrix (Fin n) (Fin n) A) :=
    Units.continuous_val
  exact continuous_aeval_comp (X := GL (Fin n) A)
    (fun g (ij : Fin n × Fin n) => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2)
    (fun ij => hv.matrix_elem ij.1 ij.2) P

/- English proof (translation)
Introduce `F _ _ n S hS`. Establish `: T2Space (FiniteAdeleRing (𝓞 F) F)` using `inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))`. Take `⟨U, hUo, hUc⟩` from `GlobalTheory.GLIntegral.exists_isOpen_isCompact F n`. Use `⟨U.subgroupOf _, hUo.preimage continuous_subtype_val, ?_⟩` and prove the remaining obligations. Conclude with `(isClosed_zeroLocusGL S (FiniteAdeleRing (𝓞 F) F)).isClosedEmbedding_subtypeVal.isCompact_preimage hUc`.
-/
theorem exists_isOpen_isCompact : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S), ∃ U : Subgroup (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) ∧ IsCompact (U : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) := by
  intro F _ _ n S hS
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  obtain ⟨U, hUo, hUc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact F n
  refine ⟨U.subgroupOf _, hUo.preimage continuous_subtype_val, ?_⟩
  exact (isClosed_zeroLocusGL S (FiniteAdeleRing (𝓞 F) F)).isClosedEmbedding_subtypeVal.isCompact_preimage hUc

end GlobalTheory.LocusOpenCompact
