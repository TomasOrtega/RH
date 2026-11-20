import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.PrTypeProof

/- English proof (translation)
Introduce `o`. Establish `hd : Disjoint {P | D.naut.ptV i P = o} {P | D.naut.ptV i P ≠ o}` using `Set.disjoint_left.2 fun P h h' => h' h`. Use `((D.naut.typeV_indep i).disjoint_biSup_biSup hd).mono_right ?_` and prove the remaining obligations. Use `iSup₂_le fun o' ho' => iSup₂_le fun P hP => ?_` and prove the remaining obligations. Conclude with `le_biSup (D.naut.typeV i) (show P ∈ {P | D.naut.ptV i P ≠ o} from fun e => ho' (hP.symm.trans e))`.
-/
theorem typeSum_indep (D : D7) (i : D.nd.Loc) : iSupIndep (typeSum D i) := by
  intro o
  have hd : Disjoint {P | D.naut.ptV i P = o} {P | D.naut.ptV i P ≠ o} :=
    Set.disjoint_left.2 fun P h h' => h' h
  refine ((D.naut.typeV_indep i).disjoint_biSup_biSup hd).mono_right ?_
  refine iSup₂_le fun o' ho' => iSup₂_le fun P hP => ?_
  exact le_biSup (D.naut.typeV i) (show P ∈ {P | D.naut.ptV i P ≠ o} from fun e => ho' (hP.symm.trans e))

/- English proof (translation)
The claim follows from `le_biSup (D.naut.typeV i) (show P ∈ {Q | D.naut.ptV i Q = D.naut.ptV i P} from rfl)`.
-/
theorem typeV_le_typeSum (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) :
    D.naut.typeV i P ≤ typeSum D i (D.naut.ptV i P) :=
  le_biSup (D.naut.typeV i) (show P ∈ {Q | D.naut.ptV i Q = D.naut.ptV i P} from rfl)

/- English proof (translation)
Introduce `D hS i PI x hx`. Set `s` to `(hS i).some`. Use `set v := D.nd.prMt i x with hvdef`. Establish `hvtop : v ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y`. Rewrite using `[Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]`.

Conclude with `Submodule.mem_top`. Take `⟨f, hf, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ v).1 hvtop`. Establish `hΦv : s.Φ v = ∑ y ∈ f.support, s.Φ (f y)`. Rewrite using `[← hsum, Finsupp.sum, map_sum]`. Establish `hn` using `s.split x`.

Establish `hind` using `typeSum_indep D i`. Establish `hjx : D.what₂.jMt _ _ x ∈ typeSum D i (D.naut.ptV i PI)` using `typeV_le_typeSum D i PI hx`. Establish `key : ∀ y, some y ≠ D.naut.ptV i PI → f y = 0`. Introduce `y hy`. Distinguish the cases in `hs : y ∈ f.support`.

Establish `e : s.Φ (f y) = (D.what₂.jMt _ _ x - (D.what₂.jMt _ _ x - s.Φ v)) - ∑ y' ∈ f.support.erase y, s.Φ (f y')`. Rewrite using `[sub_sub_cancel, hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]`. Establish `m2 : s.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o`. Rewrite using `[e]`. Use `Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.sum_mem _ fun y' hy' => ?_)` and prove the remaining obligations.

Conclude with `Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (Ne.symm hy) hjx)`. Conclude with `Submodule.mem_iSup_of_mem none (Submodule.mem_iSup_of_mem (by simp) hn)`. Use `Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (s.eig y' _ (hf y')))` and prove the remaining obligations. Conclude with `fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')`. Establish `h0 : s.Φ (f y) = 0` using `(Submodule.disjoint_def.1 (hind (some y))) _ (s.eig y _ (hf y)) m2`.

Conclude with `s.inj (h0.trans (map_zero s.Φ).symm)`. Conclude with `Finsupp.notMem_support_iff.1 hs`. Use `⟨fun p hp => ?_, fun hp => ?_⟩` and prove the remaining obligations. Rewrite using `[← hsum, Finsupp.sum]`. Use `Submodule.sum_mem _ fun y _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hyp : y = p`. Substitute `hyp` using the available equality. Conclude with `hf y`. Rewrite using `[key y (by rw [hp]; exact fun e => hyp (Option.some_injective _ e))]`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[← hsum, Finsupp.sum]`. Conclude with `Finset.sum_eq_zero fun y _ => key y (by rw [hp]; simp)`.
-/
theorem main : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → PrType D := by
  intro D hS i PI x hx
  classical
  let s := (hS i).some
  set v := D.nd.prMt i x with hvdef
  have hvtop : v ∈ ⨆ y, heckeEig (D.nd.T i) (D.nd.act i) y := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ v).1 hvtop
  have hΦv : s.Φ v = ∑ y ∈ f.support, s.Φ (f y) := by
    rw [← hsum, Finsupp.sum, map_sum]
  have hn := s.split x
  have hind := typeSum_indep D i
  have hjx : D.what₂.jMt _ _ x ∈ typeSum D i (D.naut.ptV i PI) := typeV_le_typeSum D i PI hx
  have key : ∀ y, some y ≠ D.naut.ptV i PI → f y = 0 := by
    intro y hy
    by_cases hs : y ∈ f.support
    · have e : s.Φ (f y) = (D.what₂.jMt _ _ x - (D.what₂.jMt _ _ x - s.Φ v)) -
          ∑ y' ∈ f.support.erase y, s.Φ (f y') := by
        rw [sub_sub_cancel, hΦv, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : s.Φ (f y) ∈ ⨆ (o) (_ : o ≠ some y), typeSum D i o := by
        rw [e]
        refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.sum_mem _ fun y' hy' => ?_)
        · exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (Ne.symm hy) hjx)
        · exact Submodule.mem_iSup_of_mem none (Submodule.mem_iSup_of_mem (by simp) hn)
        · refine Submodule.mem_iSup_of_mem (some y') (Submodule.mem_iSup_of_mem ?_ (s.eig y' _ (hf y')))
          exact fun e' => Finset.ne_of_mem_erase hy' (Option.some_injective _ e')
      have h0 : s.Φ (f y) = 0 := (Submodule.disjoint_def.1 (hind (some y))) _ (s.eig y _ (hf y)) m2
      exact s.inj (h0.trans (map_zero s.Φ).symm)
    · exact Finsupp.notMem_support_iff.1 hs
  refine ⟨fun p hp => ?_, fun hp => ?_⟩
  · rw [← hsum, Finsupp.sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hyp : y = p
    · subst hyp; exact hf y
    · rw [key y (by rw [hp]; exact fun e => hyp (Option.some_injective _ e))]
      exact Submodule.zero_mem _
  · rw [← hsum, Finsupp.sum]
    exact Finset.sum_eq_zero fun y _ => key y (by rw [hp]; simp)

end GlobalTheory.PendOf.PrTypeProof

end
