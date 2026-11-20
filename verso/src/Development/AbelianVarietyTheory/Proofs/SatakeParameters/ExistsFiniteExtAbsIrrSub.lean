import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedOfIsIrrSubOfIsAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedByRepMatricesOfScalarExtensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubrepIsoSummandOfIsInternalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInternalStableDecompositionDescendsToSubfiStatement
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SplitField

/- English proof (translation)
Introduce `K Γ ι _ _ _ a ρ hss`. Establish `hdec` using `fun j => GlobalTheory.semisimple_matrix_rep_decomp (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j)) (hss j)`. Use `choose n Vs hint hirr using hdec`. Set `b : ∀ j m, Module.Basis (Fin (Module.finrank (AlgebraicClosure K) (Vs j m))) (AlgebraicClosure K) (Vs j m)` to `fun j m => Module.finBasis (AlgebraicClosure K) (Vs j m)`. Set `S : Set (AlgebraicClosure K)` to `Set.range (fun p : (Σ j, Σ m : Fin (n j), Fin (Module.finrank (AlgebraicClosure K) (Vs j m)) × Fin a) => ((b p.1 p.2.1 p.2.2.1 : Vs p.1 p.2.1) : Fin a → AlgebraicClosure K) p.2.2.2)`.

Take `⟨K', _, _, _, f, hf, hS⟩` from `exists_finite_field S (Set.finite_range _)`. Use `⟨K', inferInstance, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Introduce `j`. Use `set τ := mapRep (algebraMap K K') (ρ j) with hτ`. Establish `hcomp : mapRep f τ = mapRep (algebraMap K (AlgebraicClosure K)) (ρ j)`.

Rewrite using `[hτ, mapRep_mapRep]`. Use `congr 1`. Conclude with `RingHom.ext hf`. Establish `hsp : ∀ m, Vs j m ≤ Submodule.span (AlgebraicClosure K) ((fun v => f ∘ v) '' {v : Fin a → K' | f ∘ v ∈ Vs j m})`. Introduce `m`.

Establish `h1 : Vs j m = Submodule.span _ (Set.range fun k => ((b j m k : Vs j m) : Fin a → AlgebraicClosure K))`. Use `congrArg (Submodule.map (Vs j m).subtype) (b j m).span_eq` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype]`. Use `this.symm.trans ?_` and prove the remaining obligations. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Use `conv_lhs => rw [h1]`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Establish `hc : ∀ i, ∃ c : K', f c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) i` using `fun i => hS ⟨⟨j, m, k, i⟩, rfl⟩`.

Use `choose c hc using hc`. Establish `hfc : f ∘ c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K)` using `funext hc`. Use `Submodule.subset_span ⟨c, ?_, ?_⟩` and prove the remaining obligations. Use `show f ∘ c ∈ Vs j m`. Rewrite using `[hfc]`.

Conclude with `(b j m k).2`. Conclude with `hfc`. Take `⟨Us, hUi, hUs⟩` from `GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield f τ (Vs j) (hint j) (fun m => hcomp ▸ (hirr j m).2.1) hsp`. Establish `hES : ∀ m, EndSpanned τ (Us m)`. Introduce `m`.

Apply `GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension f τ (Us m)` to reduce the goal to its premises. Rewrite using `[(hUs m).2, hcomp]`. Conclude with `GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' _ _ (hirr j m)`. Establish `hne : ∀ m, Us m ≠ ⊥`. Introduce `m h`.

Apply `(hirr j m).1` to reduce the goal to its premises. Rewrite using `[← (hUs m).2, h]`. Simplify using the standard rewrite rules. Establish `hUirr : ∀ m, IsIrrSub τ (Us m)` using `fun m => isIrrSub_of_endSpanned τ (Us m) (hne m) (hUs m).1 (hES m)`. Introduce `W hW`.

Take `⟨m, hm⟩` from `GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal τ Us hUi hUirr W hW`. Conclude with `absIrrSub_of_endSpanned τ W hW.1 hW.2.1 (endSpanned_of_isoSub τ W (Us m) hW.2.1 hm (hES m))`.
-/
theorem exists_finite_ext_absIrrSub : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  intro K Γ ι _ _ _ a ρ hss
  classical
  have hdec := fun j => GlobalTheory.semisimple_matrix_rep_decomp (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j)) (hss j)
  choose n Vs hint hirr using hdec
  let b : ∀ j m, Module.Basis (Fin (Module.finrank (AlgebraicClosure K) (Vs j m))) (AlgebraicClosure K) (Vs j m) :=
    fun j m => Module.finBasis (AlgebraicClosure K) (Vs j m)
  let S : Set (AlgebraicClosure K) := Set.range (fun p : (Σ j, Σ m : Fin (n j), Fin (Module.finrank (AlgebraicClosure K) (Vs j m)) × Fin a) =>
    ((b p.1 p.2.1 p.2.2.1 : Vs p.1 p.2.1) : Fin a → AlgebraicClosure K) p.2.2.2)
  obtain ⟨K', _, _, _, f, hf, hS⟩ := exists_finite_field S (Set.finite_range _)
  refine ⟨K', inferInstance, inferInstance, inferInstance, ?_⟩
  intro j
  set τ := mapRep (algebraMap K K') (ρ j) with hτ
  have hcomp : mapRep f τ = mapRep (algebraMap K (AlgebraicClosure K)) (ρ j) := by
    rw [hτ, mapRep_mapRep]
    congr 1
    exact RingHom.ext hf
  have hsp : ∀ m, Vs j m ≤ Submodule.span (AlgebraicClosure K) ((fun v => f ∘ v) '' {v : Fin a → K' | f ∘ v ∈ Vs j m}) := by
    intro m
    have h1 : Vs j m = Submodule.span _ (Set.range fun k => ((b j m k : Vs j m) : Fin a → AlgebraicClosure K)) := by
      have := congrArg (Submodule.map (Vs j m).subtype) (b j m).span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
      refine this.symm.trans ?_
      rw [← Set.range_comp]; rfl
    conv_lhs => rw [h1]
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hc : ∀ i, ∃ c : K', f c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) i :=
      fun i => hS ⟨⟨j, m, k, i⟩, rfl⟩
    choose c hc using hc
    have hfc : f ∘ c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) := funext hc
    refine Submodule.subset_span ⟨c, ?_, ?_⟩
    · show f ∘ c ∈ Vs j m
      rw [hfc]; exact (b j m k).2
    · exact hfc
  obtain ⟨Us, hUi, hUs⟩ := GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield f τ (Vs j) (hint j) (fun m => hcomp ▸ (hirr j m).2.1) hsp
  have hES : ∀ m, EndSpanned τ (Us m) := by
    intro m
    apply GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension f τ (Us m)
    rw [(hUs m).2, hcomp]
    exact GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' _ _ (hirr j m)
  have hne : ∀ m, Us m ≠ ⊥ := by
    intro m h
    apply (hirr j m).1
    rw [← (hUs m).2, h]
    simp
  have hUirr : ∀ m, IsIrrSub τ (Us m) := fun m => isIrrSub_of_endSpanned τ (Us m) (hne m) (hUs m).1 (hES m)
  intro W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal τ Us hUi hUirr W hW
  exact absIrrSub_of_endSpanned τ W hW.1 hW.2.1 (endSpanned_of_isoSub τ W (Us m) hW.2.1 hm (hES m))
end GlobalTheory.SplitField
