import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkSegSocle

/- English proof (translation)
The claim follows from `(GlobalTheory.T.segment_term_injective hA Δ).comp Fin.rev_injective`.
-/
theorem dec_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Function.Injective (dec Δ) :=
  (GlobalTheory.T.segment_term_injective hA Δ).comp Fin.rev_injective

/- English proof (translation)
Establish `hinj` using `dec_injective hA Δ`. Establish `hsub : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ⊆ {Equiv.refl _}`. Introduce `e he`. Simplify using `only [Set.mem_setOf_eq] at he`. Rewrite using `[Set.mem_singleton_iff]`.

Conclude with `Equiv.ext fun a => (hinj (he a)).symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ncard_perm_dec_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Set.ncard {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ≤ 1 := by
  have hinj := dec_injective hA Δ
  have hsub : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ⊆ {Equiv.refl _} := by
    intro e he
    simp only [Set.mem_setOf_eq] at he
    rw [Set.mem_singleton_iff]
    exact Equiv.ext fun a => (hinj (he a)).symm
  calc _ ≤ ({Equiv.refl _} : Set (Fin Δ.len ≃ Fin Δ.len)).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_singleton _)
    _ = 1 := Set.ncard_singleton _

/- English proof (translation)
Introduce `k _ _ _ _ hA Δ N hd`. Apply `GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA (dec Δ) hd` to reduce the goal to its premises. Establish `hc : ∀ a, (dec Δ a).IsCusp` using `fun a => Δ.isCusp_term (Fin.rev a)`. Rewrite using `[GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (dec Δ) (dec Δ) hd hd hc hc]`. Conclude with `ncard_perm_dec_le_one hA Δ` after adjusting the coercions.
-/
theorem exists_isSocle_prodIrr_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  intro k _ _ _ _ hA Δ N hd
  apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA (dec Δ) hd
  have hc : ∀ a, (dec Δ a).IsCusp := fun a => Δ.isCusp_term (Fin.rev a)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (dec Δ) (dec Δ) hd hd hc hc]
  exact_mod_cast ncard_perm_dec_le_one hA Δ

end GlobalTheory.CompanionTheory.LkSegSocle

end
