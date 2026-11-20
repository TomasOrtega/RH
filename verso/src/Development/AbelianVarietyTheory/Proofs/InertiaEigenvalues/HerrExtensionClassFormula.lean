import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitVectorOfUnitFor

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.HerrExtClass

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D HW F`. Unfold `Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass Formalism.MainNotions.RamifiedCoefficientChains.adm16`. Introduce `l _ K s LL h`. Use `show Formalism.MainNotions.RamifiedCoefficientChains.HerrExt ((HW l).W K s LL h)`. Establish `hA` using `GlobalTheory.Decompl.fontaine_and_decompletion D HW F`.

Establish `hU` using `GlobalTheory.WachUnit.unitVector D HW F l K s LL h`. Take `⟨e, e₀, hspan, hT, hj, hN, hEE, hφ, hγ, htf⟩` from `hU`. Use `⟨e, (e₀ : ((HW l).W K s LL h).one.V), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨by rw [hN]; exact Submodule.subset_span rfl, hN, hEE, hφ, hγ, hT⟩`. Introduce `T Tp ι π κ hκ hcoc x c hx w h1 h2`.

Take `⟨hS, t, htT, hπt, hκt⟩` from `hcoc`. Set `yt : ↥Tp.L.T` to `⟨_, Tp.L.T.smul_mem c htT⟩`. Set `z : ↥((HW l).W K s LL h).one.L.T` to `⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩`. Establish `hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V)`. Use `(π.f.restrictScalars ↥(OL LL)).map_smul c t` as an intermediate fact.

Simplify using `only [LinearMap.restrictScalars_apply] at this`. Rewrite using `[this, hπt]`. Establish `he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z`. Rewrite using `[hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]`. Both sides reduce to the same expression.

Establish `hcκ` using `(latticeCocycles T.L).smul_mem c hκ`. Set `cr : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))` to `⟨_, Formalism.MainNotions.DeltaInvariantLattices.resFun_Z1T _ T _ hcκ⟩`. Establish `hc : ∀ g : ↥((HW l).W K s LL h).GKs, ι.f ((cr : ↥((HW l).W K s LL h).GKs → T.V) g) = Tp.ρ (g : ↥(GK K)) (yt : Tp.V) - (yt : Tp.V)`. Introduce `g`. Establish `e1` using `(ι.f.restrictScalars ↥(OL LL)).map_smul c (κ (g : ↥(GK K)))`.

Establish `e2` using `((Tp.ρ (g : ↥(GK K))).restrictScalars ↥(OL LL)).map_smul c t`. Simplify using `only [LinearMap.restrictScalars_apply] at e1 e2`. Simplify using `only [cr, yt, Formalism.MainNotions.DeltaInvariantLattices.resFun, LinearMap.funLeft_apply, Pi.smul_apply]`. Rewrite using `[e1, hκt, e2]`. Conclude with `@smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ (g : ↥(GK K))) t) t`.

Establish `key` using `GlobalTheory.Cyc.dict_ext_Ks D HW F hA l K s LL h T Tp ((HW l).W K s LL h).one ι π hS ((HW l).W K s LL h).one_triv yt z x hz he w h1 h2 cr hc`. Use `Eq.trans key ?_` and prove the remaining obligations. Unfold `Formalism.MainNotions.RamifiedCoefficientChains.clsK Formalism.MainNotions.DeltaInvariantLattices.res`. Rewrite using `[Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]`. Use `congr 1`.

Introduce `_ hp2 T Tp ι π κ hκ hcoc x c hx hδ w h1 h2`. Take `⟨hS, t, htT, hπt, hκt⟩` from `hcoc`. Set `yt : ↥Tp.L.T` to `⟨_, Tp.L.T.smul_mem c htT⟩`. Set `z : ↥((HW l).W K s LL h).one.L.T` to `⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩`. Establish `hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V)`.

Use `(π.f.restrictScalars ↥(OL LL)).map_smul c t` as an intermediate fact. Simplify using `only [LinearMap.restrictScalars_apply] at this`. Rewrite using `[this, hπt]`. Establish `he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z`. Rewrite using `[hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]`.

Both sides reduce to the same expression. Establish `hcκ` using `(latticeCocycles T.L).smul_mem c hκ`. Set `cr : ↥(latticeCocycles T.L)` to `⟨_, hcκ⟩`. Establish `hc : ∀ g : ↥(GK K), ι.f ((cr : ↥(GK K) → T.V) g) = Tp.ρ g (yt : Tp.V) - (yt : Tp.V)`. Introduce `g`.

Establish `e1` using `(ι.f.restrictScalars ↥(OL LL)).map_smul c (κ g)`. Establish `e2` using `((Tp.ρ g).restrictScalars ↥(OL LL)).map_smul c t`. Simplify using `only [LinearMap.restrictScalars_apply] at e1 e2`. Simplify using `only [cr, yt, Pi.smul_apply]`. Rewrite using `[e1, hκt, e2]`.

Conclude with `@smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ g) t) t`. Establish `hi : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) = 2 → ∃ i : ↥K.1, i ^ 2 = -1` using `fun h2' => absurd h2' hp2`. Establish `key` using `GlobalTheory.ExtDict.dict_K D HW F hA l K s LL h hi T Tp ((HW l).W K s LL h).one ι π hS ((HW l).W K s LL h).one_triv yt z x hz he hδ w h1 h2 cr hc`. Use `Eq.trans key ?_` and prove the remaining obligations. Unfold `Formalism.MainNotions.RamifiedCoefficientChains.clsK`.

Rewrite using `[← Submodule.Quotient.mk_smul]`. Both sides reduce to the same expression.
-/
theorem herr_extension_class_formula : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass Formalism.MainNotions.RamifiedCoefficientChains.adm16
  intro l _ K s LL h
  show Formalism.MainNotions.RamifiedCoefficientChains.HerrExt ((HW l).W K s LL h)
  have hA := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have hU := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  obtain ⟨e, e₀, hspan, hT, hj, hN, hEE, hφ, hγ, htf⟩ := hU
  refine ⟨e, (e₀ : ((HW l).W K s LL h).one.V), ?_, ?_, ?_⟩
  · exact ⟨by rw [hN]; exact Submodule.subset_span rfl, hN, hEE, hφ, hγ, hT⟩
  · intro T Tp ι π κ hκ hcoc x c hx w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)) := ⟨_, Formalism.MainNotions.DeltaInvariantLattices.resFun_Z1T _ T _ hcκ⟩
    have hc : ∀ g : ↥((HW l).W K s LL h).GKs, ι.f ((cr : ↥((HW l).W K s LL h).GKs → T.V) g) = Tp.ρ (g : ↥(GK K)) (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ (g : ↥(GK K)))
      have e2 := ((Tp.ρ (g : ↥(GK K))).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Formalism.MainNotions.DeltaInvariantLattices.resFun, LinearMap.funLeft_apply, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ (g : ↥(GK K))) t) t
    have key := GlobalTheory.Cyc.dict_ext_Ks D HW F hA l K s LL h T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK Formalism.MainNotions.DeltaInvariantLattices.res
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
  · intro _ hp2 T Tp ι π κ hκ hcoc x c hx hδ w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles T.L) := ⟨_, hcκ⟩
    have hc : ∀ g : ↥(GK K), ι.f ((cr : ↥(GK K) → T.V) g) = Tp.ρ g (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ g)
      have e2 := ((Tp.ρ g).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ g) t) t
    have hi : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) = 2 → ∃ i : ↥K.1, i ^ 2 = -1 :=
      fun h2' => absurd h2' hp2
    have key := GlobalTheory.ExtDict.dict_K D HW F hA l K s LL h hi T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he hδ w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK
    rw [← Submodule.Quotient.mk_smul]
    rfl

end GlobalTheory.HerrExtClass
