import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphBC

open GlobalTheory.PRep GlobalTheory.DefU

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.locU_equiv_GL E n w hw`. Establish `hp : Function.Surjective ((cLoc w).comp (locU n w).subtype)` using `fun g => ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩`. Take `⟨φ, hφ, hφ0, hφK⟩` from `hu`. Assume the negation of the conclusion as `hns`. Establish `hfix : ∀ v, (∀ k ∈ GlobalTheory.LFun.KGL w n, σ k v = v) → v = 0`.

Introduce `v hv`. Assume the negation of the conclusion as `hv0`. Conclude with `hns ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩)`. Take `⟨hσirr, f, hf0, hfm, hf⟩` from `hc`. Set `Ψ : AutSub E n` to `⟨π, hπ⟩`.

Establish `hirr : Representation.IsIrreducible (σ.comp ((cLoc w).comp (locU n w).subtype))`. Take `⟨h0, h1⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr`. Use `(GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hp g`. Conclude with `hY x v hv`.

Set `F : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype)) (Ψ.rep.comp (locU n w).subtype)` to `⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩`. Establish `hF0 : F ≠ 0` using `fun h => hf0 (LinearMap.ext fun v => by`. Use `congrArg Subtype.val (DFunLike.congr_fun h v)` as an intermediate fact. Conclude with `this)`. Take `⟨r, -, -, hr⟩` from `GlobalTheory.DefU.LocRet.exists_ret E n w`.

Establish `htop` using `(GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V X X Ψ.rep (locU n w).subtype (σ.comp ((cLoc w).comp (locU n w).subtype)) (σ.comp ((cLoc w).comp (locU n w).subtype)) Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1`. Set `fi : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype)) (Ψ.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA E n → ℂ)` to `fun i => π.subtype ∘ₗ i.toLinearMap`. Establish `hfi : ∀ i g u, fi i ((σ.comp ((cLoc w).comp (locU n w).subtype)) g u) = (RU E n).comp (locU n w).subtype g (fi i u)` using `fun i g u => congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g u)`. Establish `hmem : φ ∈ ⨆ i, LinearMap.range (fi i)`. Establish `: φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype)) (Ψ.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap).map π.subtype`.

Rewrite using `[htop]`. Conclude with `⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩`. Simplify using `only [fi, LinearMap.range_comp]`. Rewrite `this` using `[Submodule.map_iSup]`. Then use the resulting hypothesis. Establish `key` using `GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ((RU E n).comp (locU n w).subtype) (σ.comp ((cLoc w).comp (locU n w).subtype)) hirr fi hfi (((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype) : Subgroup (locU n w)) : Set (locU n w)) ⊥ (fun i v hv => by`.

Establish `hv' : v = 0` using `hfix v fun k hk => by`. Take `⟨x, rfl⟩` from `hp k`. Conclude with `hv x hk`. Rewrite using `[hv', map_zero]`. Conclude with `Submodule.zero_mem _)`.

Use the proof step `(fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) φ (fun k hk => hφK k.1 k.2 hk) hmem`. Conclude with `hφ0 ((Submodule.mem_bot ℂ).1 key)`.
-/
theorem isSpherical_of_isCompAlong_split {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X)
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ) (hu : IsUnramU π w) :
    GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w n) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  have hp : Function.Surjective ((cLoc w).comp (locU n w).subtype) := fun g =>
    ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  by_contra hns
  have hfix : ∀ v, (∀ k ∈ GlobalTheory.LFun.KGL w n, σ k v = v) → v = 0 := by
    intro v hv
    by_contra hv0
    exact hns ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩)
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hc
  let Ψ : AutSub E n := ⟨π, hπ⟩
  have hirr : Representation.IsIrreducible (σ.comp ((cLoc w).comp (locU n w).subtype)) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype)) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V X X Ψ.rep (locU n w).subtype
    (σ.comp ((cLoc w).comp (locU n w).subtype)) (σ.comp ((cLoc w).comp (locU n w).subtype))
    Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
      (Ψ.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA E n → ℂ) := fun i => π.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp ((cLoc w).comp (locU n w).subtype)) g u) =
      (RU E n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
        (Ψ.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap).map π.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ((RU E n).comp (locU n w).subtype)
    (σ.comp ((cLoc w).comp (locU n w).subtype)) hirr fi hfi
    (((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype) : Subgroup (locU n w)) : Set (locU n w)) ⊥
    (fun i v hv => by
      have hv' : v = 0 := hfix v fun k hk => by
        obtain ⟨x, rfl⟩ := hp k
        exact hv x hk
      rw [hv', map_zero]
      exact Submodule.zero_mem _)
    (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) φ (fun k hk => hφK k.1 k.2 hk) hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 key)

/- English proof (translation)
Introduce `E _ _ _ hE n π hπ c a d h P ρ m σ hp hsh hsplit w hu i τ hτ`. It suffices to establish `hB : ∃ B, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ B by`. Take `⟨B, hB⟩` from `hB`. Establish `h1` using `(GlobalTheory.BcSpehCompare.hasSat_iff (hp.loc i w) B).2 hB`. Conclude with `((GlobalTheory.BcSpehCompare.hasSat_iff hτ B).1 h1).1`.

Distinguish the cases in `hw : IsSplitAt w`. Establish `hc` using `hsplit w hw`. Establish `hs : GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w n)` using `isSpherical_of_isCompAlong_split hπ hw _ hc hu`. Establish `hsm : GlobalTheory.PRep.IsSmooth (locProd h w (σ · w))` using `GlobalTheory.SmGL.isSmooth_parInd _ _`. Establish `hirr : (locProd h w (σ · w)).IsIrreducible` using `hc.1`.

Take `⟨T, hT⟩` from `GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible hsm hirr hs`. Take `⟨S, hS, -⟩` from `GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hp.pos i).2) (fun i => (hsh i w).2.2) T hT`. Conclude with `⟨S i, hS i⟩`. Take `⟨s, ϖ, q, α, h1, h2, h3⟩` from `GlobalTheory.BcSpehCompare.exists_hasSatAt hE hπ hw hu`. Take `⟨S, hS, -⟩` from `hp.inert w s ϖ q h1 h2 α h3`.

Conclude with `⟨S i, hS i⟩`.
-/
theorem isSpherical_of_isUnramU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ)
      (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)),
      GlobalTheory.BcSpeh.Parts π a d h P ρ m →
      (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) →
      (∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))) →
      ∀ w, IsUnramU π w → ∀ i (τ : SmIrr (GL (Fin (a i)) (w.adicCompletion E))), (P i).IsLocComp w τ →
        GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (a i)) := by
  intro E _ _ _ hE n π hπ c a d h P ρ m σ hp hsh hsplit w hu i τ hτ
  suffices hB : ∃ B, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ B by
    obtain ⟨B, hB⟩ := hB
    have h1 := (GlobalTheory.BcSpehCompare.hasSat_iff (hp.loc i w) B).2 hB
    exact ((GlobalTheory.BcSpehCompare.hasSat_iff hτ B).1 h1).1
  by_cases hw : IsSplitAt w
  · have hc := hsplit w hw
    have hs : GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w n) :=
      isSpherical_of_isCompAlong_split hπ hw _ hc hu
    have hsm : GlobalTheory.PRep.IsSmooth (locProd h w (σ · w)) := GlobalTheory.SmGL.isSmooth_parInd _ _
    have hirr : (locProd h w (σ · w)).IsIrreducible := hc.1
    obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible hsm hirr hs
    obtain ⟨S, hS, -⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hp.pos i).2)
      (fun i => (hsh i w).2.2) T hT
    exact ⟨S i, hS i⟩
  · obtain ⟨s, ϖ, q, α, h1, h2, h3⟩ := GlobalTheory.BcSpehCompare.exists_hasSatAt hE hπ hw hu
    obtain ⟨S, hS, -⟩ := hp.inert w s ϖ q h1 h2 α h3
    exact ⟨S i, hS i⟩

end GlobalTheory.SphBC
