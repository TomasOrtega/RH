import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PendOf.CenEig

/- English proof (translation)
Establish `h : typeSum D i o ≤ (typeSum D i o).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c)`. Use `iSup₂_le fun P hP G hG => ?_` and prove the remaining obligations. Conclude with `(le_biSup (D.naut.typeV i) hP : D.naut.typeV i P ≤ typeSum D i o) (hC i P c G hG)`. Conclude with `h hF`.
-/
theorem onMt_mem_typeSum (D : D7) (i : D.nd.Loc) (hC : OnMtPreservesTypeV D) (c : MonoidAlgebra ℂ (G0g D.nd))
    (o : Option (D.nd.X i)) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (hF : F ∈ typeSum D i o) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c F ∈ typeSum D i o := by
  have h : typeSum D i o ≤ (typeSum D i o).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c) := by
    refine iSup₂_le fun P hP G hG => ?_
    exact (le_biSup (D.naut.typeV i) hP : D.naut.typeV i P ≤ typeSum D i o) (hC i P c G hG)
  exact h hF

/- English proof (translation)
Establish `hvtop : w ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y`. Rewrite using `[Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]`. Conclude with `Submodule.mem_top`. Take `⟨f, hf, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ w).1 hvtop`. Establish `hΦv : S.Φ w = ∑ y ∈ f.support, S.Φ (f y)`.

Rewrite using `[← hsum, Finsupp.sum, map_sum]`. Establish `hind` using `GlobalTheory.PendOf.PrTypeProof.typeSum_indep D i`. Establish `key : ∀ y, y ≠ x → f y = 0`. Introduce `y hy`. Distinguish the cases in `hs : y ∈ f.support`.

Establish `e : S.Φ (f y) = S.Φ w - ∑ y' ∈ f.support.erase y, S.Φ (f y')`. Rewrite using `[hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]`. Establish `m2 : S.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o`. Rewrite using `[e]`. Use `Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun y' hy' => ?_)` and prove the remaining obligations.

Conclude with `Submodule.mem_iSup_of_mem (some x) (Submodule.mem_iSup_of_mem (fun e' => hy (Option.some_injective _ e').symm) hw)`. Use `Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (S.eig y' _ (hf y')))` and prove the remaining obligations. Conclude with `fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')`. Establish `h0 : S.Φ (f y) = 0` using `(Submodule.disjoint_def.1 (hind (some y))) _ (S.eig y _ (hf y)) m2`. Conclude with `S.inj (h0.trans (map_zero S.Φ).symm)`.

Conclude with `Finsupp.notMem_support_iff.1 hs`. Rewrite using `[← hsum, Finsupp.sum]`. Use `Submodule.sum_mem _ fun y _ => ?_` and prove the remaining obligations. Distinguish the cases in `hyp : y = x`. Substitute `hyp` using the available equality.

Conclude with `hf y`. Rewrite using `[key y hyp]`. Conclude with `Submodule.zero_mem _`.
-/
theorem mem_heckeEig_of_mem_typeSum (D : D7) (i : D.nd.Loc) (S : Sec D i) (x : D.nd.X i)
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) (hw : S.Φ w ∈ typeSum D i (some x)) :
    w ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  classical
  have hvtop : w ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ w).1 hvtop
  have hΦv : S.Φ w = ∑ y ∈ f.support, S.Φ (f y) := by
    rw [← hsum, Finsupp.sum, map_sum]
  have hind := GlobalTheory.PendOf.PrTypeProof.typeSum_indep D i
  have key : ∀ y, y ≠ x → f y = 0 := by
    intro y hy
    by_cases hs : y ∈ f.support
    · have e : S.Φ (f y) = S.Φ w - ∑ y' ∈ f.support.erase y, S.Φ (f y') := by
        rw [hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : S.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o := by
        rw [e]
        refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun y' hy' => ?_)
        · exact Submodule.mem_iSup_of_mem (some x)
            (Submodule.mem_iSup_of_mem (fun e' => hy (Option.some_injective _ e').symm) hw)
        · refine Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (S.eig y' _ (hf y')))
          exact fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')
      have h0 : S.Φ (f y) = 0 := (Submodule.disjoint_def.1 (hind (some y))) _ (S.eig y _ (hf y)) m2
      exact S.inj (h0.trans (map_zero S.Φ).symm)
    · exact Finsupp.notMem_support_iff.1 hs
  rw [← hsum, Finsupp.sum]
  refine Submodule.sum_mem _ fun y _ => ?_
  by_cases hyp : y = x
  · subst hyp; exact hf y
  · rw [key y hyp]
    exact Submodule.zero_mem _

/- English proof (translation)
Introduce `D i S hC c x u w hu hw`. Use `mem_heckeEig_of_mem_typeSum D i S x w ?_` and prove the remaining obligations. Rewrite using `[hw]`. Conclude with `onMt_mem_typeSum D i hC c _ _ (S.eig x u hu)`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D → ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x : D.nd.X i) (u w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)), u ∈ heckeEig (D.nd.T i) (D.nd.act i) x → S.Φ w = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ u) → w ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  intro D i S hC c x u w hu hw
  refine mem_heckeEig_of_mem_typeSum D i S x w ?_
  rw [hw]
  exact onMt_mem_typeSum D i hC c _ _ (S.eig x u hu)

end GlobalTheory.PendOf.CenEig

end
