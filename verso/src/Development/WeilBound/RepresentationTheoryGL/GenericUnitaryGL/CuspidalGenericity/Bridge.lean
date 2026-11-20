import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.CuspidalGenericity.Direct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.BZSeg.Cusp

/- English proof (translation)
Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Conclude with `bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.ext (Subsingleton.elim _ _))`.
-/
theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.ext (Subsingleton.elim _ _))

/- English proof (translation)
Introduce `N V _ _ π hN _ hirr hc`. Take `⟨ψ, hψc, hψ1⟩` from `exists_continuous_addChar_ne_one k`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`. Conclude with `⟨ψ, hψc, hψ1, GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct k ψ hψc hψ1 M V π hc (nontrivial_of_isIrreducible π hirr)⟩`.
-/
theorem cuspGeneric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZSeg.CuspGeneric k := by
  intro N V _ _ π hN _ hirr hc
  obtain ⟨ψ, hψc, hψ1⟩ := exists_continuous_addChar_ne_one k
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact ⟨ψ, hψc, hψ1, GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct k ψ hψc hψ1 M V π hc (nontrivial_of_isIrreducible π hirr)⟩

end GlobalTheory.BZSeg.Cusp

end
