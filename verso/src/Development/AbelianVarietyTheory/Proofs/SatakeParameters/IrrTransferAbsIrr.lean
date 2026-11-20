import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqBotOrTopOfSpanEqTop
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section
namespace GlobalTheory.IrrTransfer

open Matrix

/- English proof (translation)
Use `letI : Algebra k K := ι.toAlgebra`. Establish `: Nonempty (Fin r)` using `⟨⟨0, hr⟩⟩`. Establish `hirr : IsIrrSub (mapRep ι rb) ⊤` using `⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => h W hW⟩`. Establish `hs` using `GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr`. Apply `GlobalTheory.BurnsideField.span_eq_top_of_span_map (K := K)` to reduce the goal to its premises.

Use `hs using 3` and compare the differences between its conclusion and the goal. Use extensionality with `g a b`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]`.
-/
theorem span_top_of_irred_algClosed {Γ : Type} [Group Γ] {k K : Type} [Field k] [Field K] [IsAlgClosed K]
    {r : ℕ} (hr : 1 ≤ r) (rb : Γ →* GL (Fin r) k) (ι : k →+* K)
    (h : ∀ W : Submodule K (Fin r → K), IsInv (mapRep ι rb) W → W = ⊥ ∨ W = ⊤) :
    Submodule.span k (Set.range fun g => (rb g : Matrix (Fin r) (Fin r) k)) = ⊤ := by
  letI : Algebra k K := ι.toAlgebra
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hirr : IsIrrSub (mapRep ι rb) ⊤ :=
    ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => h W hW⟩
  have hs := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  apply GlobalTheory.BurnsideField.span_eq_top_of_span_map (K := K)
  convert hs using 3
  ext g a b
  simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `u _`. Rewrite using `[pi_eq_sum_univ' u]`. Use `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single a 1, trivial, ?_⟩)` and prove the remaining obligations. Use extensionality with `c`.

Distinguish the cases in `hc : c = a`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hc]`.
-/
theorem span_image_top (k' : Type) [Field k'] (n : ℕ) :
    Submodule.span (AlgebraicClosure k')
      ((fun v : Fin n → k' => (algebraMap k' (AlgebraicClosure k')) ∘ v) ''
        ((⊤ : Submodule k' (Fin n → k')) : Set (Fin n → k'))) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [pi_eq_sum_univ' u]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single a 1, trivial, ?_⟩)
  ext c
  by_cases hc : c = a
  · subst hc; simp
  · simp [Pi.single_eq_of_ne hc]

/- English proof (translation)
Establish `hsp` using `span_top_of_irred_algClosed hr rb ι h`. Use `letI : Algebra k (AlgebraicClosure k') := ((algebraMap k' (AlgebraicClosure k')).comp φ).toAlgebra`. Establish `hirr` using `GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (K := AlgebraicClosure k') _ hsp`. Establish `: Nonempty (Fin r)` using `⟨⟨0, hr⟩⟩`. Rewrite using `[AbsIrrSub, span_image_top]`.

Use `⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => hirr W fun g v hv => ?_⟩` and prove the remaining obligations. Use `hW g v hv` as an intermediate fact. Simplify `this` using `[mapRep, Matrix.map_map, RingHom.algebraMap_toAlgebra]`.
-/
theorem absIrr_of_algClosed {Γ : Type} [Group Γ] {k K k' : Type} [Field k] [Field K] [IsAlgClosed K]
    [Field k'] {r : ℕ} (hr : 1 ≤ r) (rb : Γ →* GL (Fin r) k) (ι : k →+* K)
    (h : ∀ W : Submodule K (Fin r → K), IsInv (mapRep ι rb) W → W = ⊥ ∨ W = ⊤) (φ : k →+* k') :
    AbsIrrSub (mapRep φ rb) ⊤ := by
  have hsp := span_top_of_irred_algClosed hr rb ι h
  letI : Algebra k (AlgebraicClosure k') := ((algebraMap k' (AlgebraicClosure k')).comp φ).toAlgebra
  have hirr := GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (K := AlgebraicClosure k') _ hsp
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [AbsIrrSub, span_image_top]
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => hirr W fun g v hv => ?_⟩
  have := hW g v hv
  simpa [mapRep, Matrix.map_map, RingHom.algebraMap_toAlgebra] using this

end GlobalTheory.IrrTransfer

namespace GlobalTheory.StringRepresentationDecomposition

/- English proof (translation)
Introduce `l _ Γ _ k k' _ _ r hr rb ι h φ`. Conclude with `GlobalTheory.IrrTransfer.absIrr_of_algClosed hr rb ι (fun W hW => h W fun g _ v hv => hW g v hv) φ`.
-/
theorem irr_transfer_absIrr : ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {k k' : Type} [Field k] [Field k']
    {r : ℕ}, 1 ≤ r → ∀ (rb : Γ →* GL (Fin r) k) (ι : k →+* Formalism.CyclotomicNorms.Fbar l),
    Formalism.CyclotomicNorms.IrredOn (mapRep ι rb) ⊤ → ∀ φ : k →+* k', AbsIrrSub (mapRep φ rb) ⊤ := by
  intro l _ Γ _ k k' _ _ r hr rb ι h φ
  exact GlobalTheory.IrrTransfer.absIrr_of_algClosed hr rb ι (fun W hW => h W fun g _ v hv => hW g v hv) φ

end GlobalTheory.StringRepresentationDecomposition
