import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.Dblock.SzFinProof

/- English proof (translation)
Use `delta PositivityTheory.Rg.BcB.cW GlobalTheory.CuspRep.pLoc GlobalTheory.CuspRep.pFin`. Establish `h` using `RestrictedProduct.eventually _ _ (RingHom.snd (InfiniteAdeleRing E) (Af E) a)`. Use `(Filter.eventually_cofinite.mp h).subset ?_` and prove the remaining obligations. Introduce `w hw`. Simplify using `only [Set.mem_ofPred_eq, RingHom.comp_apply, RestrictedProduct.evalRingHom_apply] at hw ⊢`.

Introduce `hmem`. Conclude with `absurd hw (not_lt.mpr (Valued.toNormedField.norm_le_one_iff.mpr ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem)))`.
-/
theorem finite_one_lt_norm_cW {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : Ad E) :
    {w : HeightOneSpectrum (𝓞 E) | 1 < ‖cW w a‖}.Finite := by
  delta PositivityTheory.Rg.BcB.cW GlobalTheory.CuspRep.pLoc GlobalTheory.CuspRep.pFin
  have h := RestrictedProduct.eventually _ _ (RingHom.snd (InfiniteAdeleRing E) (Af E) a)
  refine (Filter.eventually_cofinite.mp h).subset ?_
  intro w hw
  simp only [Set.mem_ofPred_eq, RingHom.comp_apply, RestrictedProduct.evalRingHom_apply] at hw ⊢
  intro hmem
  exact absurd hw (not_lt.mpr (Valued.toNormedField.norm_le_one_iff.mpr
    ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem)))

/- English proof (translation)
Introduce `E _ _ _ ι κ _ _ A`. Use `(Set.Finite.biUnion (s := (Set.univ : Set (ι × κ))) Set.finite_univ fun p _ => finite_one_lt_norm_cW (A p.1 p.2)).subset ?_` and prove the remaining obligations. Introduce `w hw`. Express the relevant statement in the definitionally equal form `1 < ⨆ p : ι × κ, ‖(A.map (PositivityTheory.Rg.BcB.cW w)) p.1 p.2‖ at hw`. Break down `isEmpty_or_nonempty (ι × κ) with hι | hι` into its components or cases.

Rewrite `hw` using `[Real.iSup_of_isEmpty]`. Conclude with `absurd hw (by norm_num)`. Take `⟨p, hp⟩` from `exists_lt_of_lt_ciSup hw`. Conclude with `Set.mem_biUnion (Set.mem_univ p) hp`.
-/
theorem szFin : SzFin := by
  intro E _ _ _ ι κ _ _ A
  refine (Set.Finite.biUnion (s := (Set.univ : Set (ι × κ))) Set.finite_univ
    fun p _ => finite_one_lt_norm_cW (A p.1 p.2)).subset ?_
  intro w hw
  change 1 < ⨆ p : ι × κ, ‖(A.map (PositivityTheory.Rg.BcB.cW w)) p.1 p.2‖ at hw
  rcases isEmpty_or_nonempty (ι × κ) with hι | hι
  · rw [Real.iSup_of_isEmpty] at hw
    exact absurd hw (by norm_num)
  · obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hw
    exact Set.mem_biUnion (Set.mem_univ p) hp

end GlobalTheory.CompanionTheory.Dblock.SzFinProof
