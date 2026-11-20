import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsotHom

/- English proof (translation)
Introduce `D V S θ M n P π`. Use `set e := GlobalTheory.KapIsot.eqv P with he`. Establish `hσ : ∀ κ (x : π.S), ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (e κ) x = GlobalTheory.OccRowVec.finRep π κ x` using `fun κ x => by show GlobalTheory.OccRowVec.finRep π (e.symm (e κ)) x = _`. Rewrite using `[MulEquiv.symm_apply_apply]`. Establish `hact : ∀ κ (T : MMap M), principalLevelFrame.actM P M κ T = finRep M (e κ) T` using `fun κ T => by`.

Use `MultilinearMap.ext fun v => funext fun g => ?_` and prove the remaining obligations. Rewrite using `[principalLevelFrame.actM_apply, finRep_apply]`. Both sides reduce to the same expression. Establish `hle : principalLevelFrame.Minf θ P M ≤ allMaps θ M` using `iSup_le fun N => GlobalTheory.PartDims.mult_le θ M fun k hk => hk.elim`. Apply `le_antisymm` to reduce the goal to its premises.

Use `iSup₂_le fun Φ hΦ => ?_` and prove the remaining obligations. Use `le_iSup₂_of_le (f := fun f (_ : f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (finRep M) (allMaps θ M)) => LinearMap.range f) Φ ⟨fun s => hle (hΦ.2 ⟨s, rfl⟩), fun g s => ?_⟩ le_rfl` and prove the remaining obligations. Take `⟨κ, rfl⟩` from `e.surjective g`. Rewrite using `[hσ, ← hact]`. Conclude with `hΦ.1 κ s`.

Use `iSup₂_le fun f hf => ?_` and prove the remaining obligations. Establish `hfe : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π f`. Introduce `κ x`. Establish `h1` using `hf.2 (e κ) x`. Rewrite `h1` using `[hσ, ← hact]`.

Conclude with `h1`. Establish `hfr : LinearMap.range f ≤ principalLevelFrame.Minf θ P M`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨N, hN, hfix⟩` from `π.smooth x x.2`. Take `⟨N, rfl⟩ : ∃ N', N = N' + 1` from `⟨N - 1, by omega⟩`.

Use `Submodule.mem_iSup_of_mem N (Submodule.subset_span ?_)` and prove the remaining obligations. Establish `h1` using `(GlobalTheory.MultMem.mem_mult_iff ..).1 (hf.1 x)`. Use `⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩` and prove the remaining obligations. Introduce and unpack `v _ ⟨κ, hκ, rfl⟩ g`. Establish `h2` using `hfe κ x`.

Rewrite `h2` using `[show (⟨Formalism.L2.NG.rt D.host.E n κ x, π.stable κ x x.2⟩ : π.S) = x from Subtype.ext (hfix κ hκ)]`. Rewrite using `[one_mul]`. Conclude with `(congrArg (fun T : MMap M => T v g) h2).symm`. Conclude with `le_iSup₂_of_le (f := fun (Φ : π.S →ₗ[ℂ] MMap M) (_ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π Φ ∧ LinearMap.range Φ ≤ principalLevelFrame.Minf θ P M) => LinearMap.range Φ) f ⟨hfe, hfr⟩ le_rfl`.
-/
theorem isotIn_eq_iSup_homInto : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f := by
  intro D V S θ M n P π
  classical
  set e := GlobalTheory.KapIsot.eqv P with he
  have hσ : ∀ κ (x : π.S), ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (e κ) x = GlobalTheory.OccRowVec.finRep π κ x := fun κ x => by
    show GlobalTheory.OccRowVec.finRep π (e.symm (e κ)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hact : ∀ κ (T : MMap M), principalLevelFrame.actM P M κ T = finRep M (e κ) T := fun κ T => by
    refine MultilinearMap.ext fun v => funext fun g => ?_
    rw [principalLevelFrame.actM_apply, finRep_apply]
    rfl
  have hle : principalLevelFrame.Minf θ P M ≤ allMaps θ M := iSup_le fun N => GlobalTheory.PartDims.mult_le θ M fun k hk => hk.elim
  apply le_antisymm
  · refine iSup₂_le fun Φ hΦ => ?_
    refine le_iSup₂_of_le (f := fun f (_ : f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (finRep M) (allMaps θ M)) => LinearMap.range f) Φ ⟨fun s => hle (hΦ.2 ⟨s, rfl⟩), fun g s => ?_⟩ le_rfl
    obtain ⟨κ, rfl⟩ := e.surjective g
    rw [hσ, ← hact]
    exact hΦ.1 κ s
  · refine iSup₂_le fun f hf => ?_
    have hfe : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π f := by
      intro κ x
      have h1 := hf.2 (e κ) x
      rw [hσ, ← hact] at h1
      exact h1
    have hfr : LinearMap.range f ≤ principalLevelFrame.Minf θ P M := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨N, hN, hfix⟩ := π.smooth x x.2
      obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      refine Submodule.mem_iSup_of_mem N (Submodule.subset_span ?_)
      have h1 := (GlobalTheory.MultMem.mem_mult_iff ..).1 (hf.1 x)
      refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
      rintro v _ ⟨κ, hκ, rfl⟩ g
      have h2 := hfe κ x
      rw [show (⟨Formalism.L2.NG.rt D.host.E n κ x, π.stable κ x x.2⟩ : π.S) = x from Subtype.ext (hfix κ hκ)] at h2
      rw [one_mul]
      exact (congrArg (fun T : MMap M => T v g) h2).symm
    exact le_iSup₂_of_le (f := fun (Φ : π.S →ₗ[ℂ] MMap M) (_ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π Φ ∧ LinearMap.range Φ ≤ principalLevelFrame.Minf θ P M) => LinearMap.range Φ) f ⟨hfe, hfr⟩ le_rfl

end GlobalTheory.IsotHom
