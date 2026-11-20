import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLevelSphericalOffSet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOntoDecomp

/- English proof (translation)
Introduce `hP D hfd c hc j hj s hs`. Establish `hmul : ∀ k ∈ s.J, ∀ k' ∈ s.J, (1 : GA D s.V → ℂ) (k * k') = (1 : GA D s.V → ℂ) k * (1 : GA D s.V → ℂ) k'` using `fun _ _ _ _ => by simp`. Establish `hops` using `GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M s.J (1 : GA D s.V → ℂ) c.S GlobalTheory.ChainOntoSph.exists_unif_of_F hc.inf hmul hs.split`. Take `⟨hLU, -, hH⟩` from `hops`. Distinguish the cases in `hsm : ∀ τ, s.M.sm τ ≠ ⊥`.

Use `swap`. Use `push_neg at hsm`. Take `⟨τ, hτ⟩` from `hsm`. Use `Submodule.eq_top_iff'.2 fun u => ?_` and prove the remaining obligations. Establish `h0 : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0`.

Use `MultilinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.zero_apply]`. Establish `hv : ((v τ : s.M.sm τ) : s.M.H τ) = 0` using `(Submodule.eq_bot_iff _).1 hτ _ (v τ).2`. Conclude with `MultilinearMap.map_coord_zero (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) τ (Subtype.ext hv)`. Establish `h1` using `LinearEquiv.apply_symm_apply PiTensorProduct.lift (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))`.

Rewrite `h1` using `[h0, map_zero]`. Establish `: u = 0` using `Subtype.ext h1.symm`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `hschur` using `GlobalTheory.MultFinite.schurMult (θ := c.θ) (M := s.M) (J := (s.J : Set (GA D s.V))) (χ := (1 : GA D s.V → ℂ)) hP s.ν s.fd`.

Use `haveI := hs.haar`. Establish `hright : s.ν.IsMulRightInvariant` using `Formalism.IndefR.Eqv.unimodGA_holds s.V s.ν hs.haar`. Take `⟨hlin, hpos⟩` from `GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) s.ν s.fd hc.inf hs.haar hs.fund hschur hsm`. Take `⟨v0, hv0⟩` from `GlobalTheory.SchurConst.exists_vec s.M hsm`. Establish `hspec : ∀ T ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ), ∀ T' ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ), IsMultIP s.M s.ν s.fd T T' (ipM s.M s.ν s.fd T T')` using `fun T hT T' hT' => ipM_spec _ _ _ _ _ (hschur hc.inf hs.haar hs.fund T hT T' hT')`.

Set `φ` to `Submodule.equivMapOfInjective (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap (LinearEquiv.injective _) (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))`. Use `haveI : FiniteDimensional ℂ ((Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)).map (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap) := hfd c hc j hj s hs`. Use `haveI : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) := LinearEquiv.finiteDimensional φ.symm`. Set `I` to `{t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D s.V) // Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S t.1 t.2.1 t.2.2}`. Set `op : I → Module.End ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))` to `fun t => (heckeOn s.M t.1.2.2).restrict fun T hT => (hH _ _ _ t.2).1 T hT`.

Establish `hcomm : ∀ i j, Commute (op i) (op j)` using `fun i j => by`. Use `LinearMap.ext fun T => Subtype.ext ?_` and prove the remaining obligations. Conclude with `(hH _ _ _ i.2).2.1 _ _ _ j.2 T T.2`. Establish `hadj : ∀ i, ∃ i', ∀ x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ), ipM s.M s.ν s.fd (op i x : MMap s.M) y = ipM s.M s.ν s.fd x (op i' y : MMap s.M)` using `fun i => by`. Take `⟨R', h', hip⟩` from `(hH _ _ _ i.2).2.2`.

Use `⟨⟨(i.1.1, dualLab i.1.2.1, R'), h'⟩, fun x y => ?_⟩` and prove the remaining obligations. Establish `h1` using `hspec _ ((hH _ _ _ i.2).1 x x.2) y y.2`. Establish `h2` using `(hip s.ν s.fd hs.haar hright hs.fund hschur x x.2 y y.2 _).1 h1`. Establish `h3` using `hspec x x.2 _ ((hH _ _ _ h').1 y y.2)`. Conclude with `hasPeterssonInner_unique s.M s.ν s.fd _ _ v0 hv0 h2 h3`.

Establish `htop` using `GlobalTheory.OntoDecomp.iSup_jointEigenspace_eq_top (fun x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => ipM s.M s.ν s.fd x y) (fun x y z a => (hlin x x.2 y y.2 z z.2 a).1) (fun x y => (hlin x x.2 y y.2 y y.2 0).2) (fun x hx => hpos x x.2 fun h => hx (Subtype.ext …`. Establish `hsub : ∀ x : I → ℂ, ∀ T ∈ ⨅ i, (op i).eigenspace (x i), ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (T : MMap s.M) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S e` using `by classical`. Introduce `x T hT`. Use `⟨fun P d => if h : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_partFull]`.

Use `⟨T.2, fun P d R hR v => ?_⟩` and prove the remaining obligations. Establish `hex : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R` using `⟨R, hR⟩`. Rewrite using `[dif_pos hex]`. Establish `hlevT` using `((GlobalTheory.MultMem.mem_mult_iff ..).1 T.2).lev v`. Rewrite using `[hLU P d R hex.choose hR hex.choose_spec _ hlevT]`.

Establish `h1` using `(Submodule.mem_iInf _).1 hT ⟨(P, d, hex.choose), hex.choose_spec⟩`. Rewrite `h1` using `[Module.End.mem_eigenspace_iff]`. Conclude with `congrArg (fun U : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => (U : MMap s.M) v) h1`. Rewrite using `[eq_top_iff]`. Introduce and unpack `u -`.

Take `⟨T, rfl⟩` from `φ.surjective u`. Establish `hT : T ∈ (⊤ : Submodule ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)))` using `trivial`. Rewrite `hT` using `[← htop]`. Use `Submodule.iSup_induction (fun x : I → ℂ => ⨅ i, (op i).eigenspace (x i)) (motive := fun T => φ T ∈ Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s. …` and prove the remaining obligations. Introduce `x T hT`.

Take `⟨e, he⟩` from `hsub x T hT`. Use `Submodule.subset_span ⟨e, ?_⟩` and prove the remaining obligations. Establish `: ((φ T : s.CC c) : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = PiTensorProduct.lift (T : MMap s.M)` using `rfl`. Rewrite using `[this, LinearEquiv.symm_apply_apply]`. Conclude with `he`.

Rewrite using `[map_zero]`. Conclude with `zero_mem _`. Introduce `a b ha hb`. Rewrite using `[map_add]`. Conclude with `add_mem ha hb`.
-/
theorem cc_span_partFull : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e} = ⊤ := by
  classical
  intro hP D hfd c hc j hj s hs
  have hmul : ∀ k ∈ s.J, ∀ k' ∈ s.J, (1 : GA D s.V → ℂ) (k * k') = (1 : GA D s.V → ℂ) k * (1 : GA D s.V → ℂ) k' :=
    fun _ _ _ _ => by simp
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M s.J (1 : GA D s.V → ℂ) c.S
    GlobalTheory.ChainOntoSph.exists_unif_of_F hc.inf hmul hs.split
  obtain ⟨hLU, -, hH⟩ := hops
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  swap
  · push_neg at hsm
    obtain ⟨τ, hτ⟩ := hsm
    refine Submodule.eq_top_iff'.2 fun u => ?_
    have h0 : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0 := by
      refine MultilinearMap.ext fun v => ?_
      rw [MultilinearMap.zero_apply]
      have hv : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := (Submodule.eq_bot_iff _).1 hτ _ (v τ).2
      exact MultilinearMap.map_coord_zero (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) τ
        (Subtype.ext hv)
    have h1 := LinearEquiv.apply_symm_apply PiTensorProduct.lift (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
    rw [h0, map_zero] at h1
    have : u = 0 := Subtype.ext h1.symm
    rw [this]
    exact zero_mem _
  have hschur := GlobalTheory.MultFinite.schurMult (θ := c.θ) (M := s.M) (J := (s.J : Set (GA D s.V)))
    (χ := (1 : GA D s.V → ℂ)) hP s.ν s.fd
  haveI := hs.haar
  have hright : s.ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds s.V s.ν hs.haar
  obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M (s.J : Set (GA D s.V))
    (1 : GA D s.V → ℂ) s.ν s.fd hc.inf hs.haar hs.fund hschur hsm
  obtain ⟨v0, hv0⟩ := GlobalTheory.SchurConst.exists_vec s.M hsm
  have hspec : ∀ T ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      ∀ T' ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      IsMultIP s.M s.ν s.fd T T' (ipM s.M s.ν s.fd T T') := fun T hT T' hT' =>
    ipM_spec _ _ _ _ _ (hschur hc.inf hs.haar hs.fund T hT T' hT')
  let φ := Submodule.equivMapOfInjective (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap
    (LinearEquiv.injective _) (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))
  haveI : FiniteDimensional ℂ ((Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)).map
      (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap) := hfd c hc j hj s hs
  haveI : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) :=
    LinearEquiv.finiteDimensional φ.symm
  let I := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D s.V) //
    Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S t.1 t.2.1 t.2.2}
  let op : I → Module.End ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) := fun t =>
    (heckeOn s.M t.1.2.2).restrict fun T hT => (hH _ _ _ t.2).1 T hT
  have hcomm : ∀ i j, Commute (op i) (op j) := fun i j => by
    refine LinearMap.ext fun T => Subtype.ext ?_
    exact (hH _ _ _ i.2).2.1 _ _ _ j.2 T T.2
  have hadj : ∀ i, ∃ i', ∀ x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      ipM s.M s.ν s.fd (op i x : MMap s.M) y = ipM s.M s.ν s.fd x (op i' y : MMap s.M) := fun i => by
    obtain ⟨R', h', hip⟩ := (hH _ _ _ i.2).2.2
    refine ⟨⟨(i.1.1, dualLab i.1.2.1, R'), h'⟩, fun x y => ?_⟩
    have h1 := hspec _ ((hH _ _ _ i.2).1 x x.2) y y.2
    have h2 := (hip s.ν s.fd hs.haar hright hs.fund hschur x x.2 y y.2 _).1 h1
    have h3 := hspec x x.2 _ ((hH _ _ _ h').1 y y.2)
    exact hasPeterssonInner_unique s.M s.ν s.fd _ _ v0 hv0 h2 h3
  have htop := GlobalTheory.OntoDecomp.iSup_jointEigenspace_eq_top
    (fun x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => ipM s.M s.ν s.fd x y)
    (fun x y z a => (hlin x x.2 y y.2 z z.2 a).1) (fun x y => (hlin x x.2 y y.2 y y.2 0).2)
    (fun x hx => hpos x x.2 fun h => hx (Subtype.ext h)) op hcomm hadj
  have hsub : ∀ x : I → ℂ, ∀ T ∈ ⨅ i, (op i).eigenspace (x i), ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (T : MMap s.M) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S e := by
    classical
    intro x T hT
    refine ⟨fun P d => if h : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R
      then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0, ?_⟩
    rw [mem_partFull]
    refine ⟨T.2, fun P d R hR v => ?_⟩
    have hex : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R := ⟨R, hR⟩
    rw [dif_pos hex]
    have hlevT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 T.2).lev v
    rw [hLU P d R hex.choose hR hex.choose_spec _ hlevT]
    have h1 := (Submodule.mem_iInf _).1 hT ⟨(P, d, hex.choose), hex.choose_spec⟩
    rw [Module.End.mem_eigenspace_iff] at h1
    exact congrArg (fun U : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => (U : MMap s.M) v) h1
  rw [eq_top_iff]
  rintro u -
  obtain ⟨T, rfl⟩ := φ.surjective u
  have hT : T ∈ (⊤ : Submodule ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))) := trivial
  rw [← htop] at hT
  refine Submodule.iSup_induction (fun x : I → ℂ => ⨅ i, (op i).eigenspace (x i))
    (motive := fun T => φ T ∈ Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e}) hT ?_ ?_ ?_
  · intro x T hT
    obtain ⟨e, he⟩ := hsub x T hT
    refine Submodule.subset_span ⟨e, ?_⟩
    have : ((φ T : s.CC c) : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = PiTensorProduct.lift (T : MMap s.M) := rfl
    rw [this, LinearEquiv.symm_apply_apply]
    exact he
  · rw [map_zero]; exact zero_mem _
  · intro a b ha hb; rw [map_add]; exact add_mem ha hb

end GlobalTheory.EvenOntoDecomp

end
