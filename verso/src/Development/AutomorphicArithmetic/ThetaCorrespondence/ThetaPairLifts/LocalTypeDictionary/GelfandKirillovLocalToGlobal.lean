import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearCuspFormFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearCuspFormFamilyStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.GKGlobalise
/- English proof (translation)
Introduce `hP D θ V S M hθ F ⟨haut, hcusp, hK, hL⟩`. Establish `hHC` using `hP.harishChandraModules`. Establish `hCW` using `hP.casselmanWallach`. Establish `hk : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ = GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)` using `fun τ => (kFin_eq M τ).symm`. Set `e : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)` to `fun τ => (LinearEquiv.ofEq _ _ (hk τ)).toLinearMap`.

Set `T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M` to `F.compLinearMap e`. Establish `hupd : ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) τ (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), T₀ (Function.update u τ w) = F (Function.update (fun τ' => e τ' (u τ')) τ (e τ w))`. Introduce `u τ w`. Use `show F (fun τ' => e τ' (Function.update u τ w τ')) = _`. Use `congr 1`.

Use function extensionality and compare the values at `τ'`. Conclude with `Function.apply_update (fun τ => e τ) u τ w τ'`. Establish `hGK : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M ∅ 1 0 ∅ T₀`. Use `⟨fun u => (haut _).toIsAutFun, fun u => (haut _).smooth, fun u => hcusp _, fun u => ?_, fun u => GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ (haut _), fun u k hk => by simp at hk, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.restrict_zero]`.

Conclude with `memLp_measure_zero`. Introduce `τ k hkm u w hw`. Rewrite using `[hupd]`. Conclude with `hK τ k (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ hkm) hkm (fun τ' => e τ' (u τ')) (e τ w) hw`. Introduce `τ X hX u w hw`.

Rewrite using `[hupd]`. Use `hL τ X hX (fun τ' => e τ' (u τ')) (e τ w) ?_` and prove the remaining obligations. Establish `hsm : (u τ : M.H τ) ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (GlobalTheory.SmVec.trRep (M.σ τ) (M.fr τ))`. Rewrite using `[← GlobalTheory.SmVec.sm_eq]`. Conclude with `kFin_le_sm hHC M τ (u τ).2`.

Establish `h1` using `GlobalTheory.SmVec.hasDerivAt_dRep hsm (X := X) hX`. Use `show HasDerivAt _ (w : M.H τ) 0`. Rewrite using `[hw]`. Conclude with `h1`. Take `⟨U, N, hU, hTU⟩` from `GlobalTheory.T.exists_common_level_growth_exponent_gKMap hHC D θ hθ V S M ∅ 1 0 ∅ T₀ hGK`.

Take `⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩` from `GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU`. Use `choose π dπ hπ using hπ`. Establish `hmem : ∀ u, T₀ u ∈ LinearMap.range ι` using `fun u => by`. Establish `ha` using `hGK.1 u`. Take `⟨x, hx⟩` from `(hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hGK.2.1 u, hGK.2.2.1 u, (hTU u).2⟩`.

Conclude with `⟨x, hx⟩`. Set `eι` to `LinearEquiv.ofInjective ι hinj`. Set `T₀' : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E` to `eι.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)`. Establish `hT₀' : ∀ u, ι (T₀' u) = T₀ u` using `fun u => by`. Establish `h1` using `congrArg Subtype.val (eι.apply_symm_apply ⟨T₀ u, hmem u⟩)`.

Rewrite `h1` using `[LinearEquiv.ofInjective_apply]`. Conclude with `h1`. Establish `hK' : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u)`. Introduce `τ k hk u w hw`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[(hπ τ).2.1 k (GlobalTheory.GKExt.kset_sub hk), hT₀', hT₀']`. Establish `hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k` using `GlobalTheory.GKExt.conj_back (M.fr_unit τ)`. Establish `hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ`. Express the relevant statement in the definitionally equal form `M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)`. Rewrite using `[hk']`.

Conclude with `hk`. Use `(hGK.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl` and prove the remaining obligations. Rewrite using `[hw]`. Use `show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _`. Rewrite using `[hk']`.

Establish `hL' : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) → T₀' (Function.update u τ w) = dπ τ X (T₀' u)`. Introduce `τ X hX u w hw`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[(hπ τ).2.2 X hX, hT₀', hT₀']`. Establish `hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X`.

Use function extensionality and compare the values at `y`. Unfold `dRep`. Use `congr 1`. Use function extensionality and compare the values at `t`. Use `show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _`.

Rewrite using `[GlobalTheory.GKExt.exp_conj_inv (M.fr_unit τ), GlobalTheory.GKExt.conj_back (M.fr_unit τ)]`. Conclude with `hGK.2.2.2.2.2.2.2 τ _ (GlobalTheory.GKExt.conj_mem_lieAt M τ hX) u w (by rw [hw, hd])`. Establish `hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'), (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g)`. Introduce `τ τ' hne g hg g' hg'`. Use extensionality with `x`.

Apply `hinj` to reduce the goal to its premises. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]`. Use function extensionality and compare the values at `y`. Simplify using `only [rTr, mul_assoc]`.

Conclude with `congrArg (fun z => ι x (y * z)) (GlobalTheory.T.realPlacePoint_commute_of_ne_place D θ hθ V τ τ' hne _ (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _ (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))`. Take `⟨TE, hTE1, hTE2, hTE3⟩` from `GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK' hL'`. Take `⟨hequiv, hcont⟩` from `GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3`. Set `T : Formalism.IndefR.Mult.MMap M` to `ι.compMultilinearMap TE`. Establish `hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀` using `fun v u h => by show ι (TE v) = T₀ u`.

Rewrite using `[hTE1 v u h, hT₀']`. Establish `hMult : Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T`. Use `⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1, fun v k hk => by simp at hk, hequiv, hcont⟩` and prove the remaining obligations. Conclude with `GlobalTheory.T.isSmoothAutomorphicForm_multMap_value hHC D θ hθ V S M T U N hU (fun v => by`. Establish `h` using `(hrange (ι (TE v))).1 ⟨TE v, rfl⟩`.

Conclude with `⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont`. Use `⟨T, hMult, fun u => ?_⟩` and prove the remaining obligations. Set `ue : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M` to `fun τ => ⟨(u τ : M.H τ), by rw [← kFin_eq M τ]; exact (u τ).2⟩`. Use `⟨fun τ => ⟨(u τ : M.H τ), kFin_le_sm hHC M τ (ue τ).2⟩, fun τ => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hext _ ue (fun τ => rfl)]`.

Use `show F (fun τ => e τ (ue τ)) = F u`. Use `congr 1`.
-/
theorem gelfandKirillov_local_to_global : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ F : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ),
      (∀ u, IsAutFunSm θ V (F u)) ∧ (∀ u, IsCuspFun V (F u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F (Function.update u τ w) = Rder θ V τ X (F u)) →
      ∃ T : Formalism.IndefR.Mult.MMap M, Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T ∧
        ∀ u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) = u τ) ∧ T v = F u := by
  intro hP D θ V S M hθ F ⟨haut, hcusp, hK, hL⟩
  have hHC := hP.harishChandraModules
  have hCW := hP.casselmanWallach
  have hk : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ = GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) := fun τ => (kFin_eq M τ).symm
  let e : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) :=
    fun τ => (LinearEquiv.ofEq _ _ (hk τ)).toLinearMap
  let T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M := F.compLinearMap e
  have hupd : ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) τ (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
      T₀ (Function.update u τ w) = F (Function.update (fun τ' => e τ' (u τ')) τ (e τ w)) := by
    intro u τ w
    show F (fun τ' => e τ' (Function.update u τ w τ')) = _
    congr 1
    funext τ'
    exact Function.apply_update (fun τ => e τ) u τ w τ'
  have hGK : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M ∅ 1 0 ∅ T₀ := by
    refine ⟨fun u => (haut _).toIsAutFun, fun u => (haut _).smooth, fun u => hcusp _,
      fun u => ?_, fun u => GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ (haut _),
      fun u k hk => by simp at hk, ?_, ?_⟩
    · rw [Measure.restrict_zero]; exact memLp_measure_zero
    · intro τ k hkm u w hw
      rw [hupd]
      exact hK τ k (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ hkm) hkm (fun τ' => e τ' (u τ')) (e τ w) hw
    · intro τ X hX u w hw
      rw [hupd]
      refine hL τ X hX (fun τ' => e τ' (u τ')) (e τ w) ?_
      have hsm : (u τ : M.H τ) ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (GlobalTheory.SmVec.trRep (M.σ τ) (M.fr τ)) := by
        rw [← GlobalTheory.SmVec.sm_eq]; exact kFin_le_sm hHC M τ (u τ).2
      have h1 := GlobalTheory.SmVec.hasDerivAt_dRep hsm (X := X) hX
      show HasDerivAt _ (w : M.H τ) 0
      rw [hw]
      exact h1
  obtain ⟨U, N, hU, hTU⟩ := GlobalTheory.T.exists_common_level_growth_exponent_gKMap hHC D θ hθ V S M ∅ 1 0 ∅ T₀ hGK
  obtain ⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩ :=
    GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU
  choose π dπ hπ using hπ
  have hmem : ∀ u, T₀ u ∈ LinearMap.range ι := fun u => by
    have ha := hGK.1 u
    obtain ⟨x, hx⟩ := (hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hGK.2.1 u, hGK.2.2.1 u, (hTU u).2⟩
    exact ⟨x, hx⟩
  let eι := LinearEquiv.ofInjective ι hinj
  let T₀' : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E :=
    eι.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)
  have hT₀' : ∀ u, ι (T₀' u) = T₀ u := fun u => by
    have h1 := congrArg Subtype.val (eι.apply_symm_apply ⟨T₀ u, hmem u⟩)
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  have hK' : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
      (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u) := by
    intro τ k hk u w hw
    apply hinj
    rw [(hπ τ).2.1 k (GlobalTheory.GKExt.kset_sub hk), hT₀', hT₀']
    have hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := GlobalTheory.GKExt.conj_back (M.fr_unit τ)
    have hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
      change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
      rw [hk']; exact hk
    refine (hGK.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl
    rw [hw]
    show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _
    rw [hk']
  have hL' : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M)
      (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) →
      T₀' (Function.update u τ w) = dπ τ X (T₀' u) := by
    intro τ X hX u w hw
    apply hinj
    rw [(hπ τ).2.2 X hX, hT₀', hT₀']
    have hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X := by
      funext y
      unfold dRep
      congr 1
      funext t
      show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _
      rw [GlobalTheory.GKExt.exp_conj_inv (M.fr_unit τ), GlobalTheory.GKExt.conj_back (M.fr_unit τ)]
    exact hGK.2.2.2.2.2.2.2 τ _ (GlobalTheory.GKExt.conj_mem_lieAt M τ hX) u w (by rw [hw, hd])
  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'),
      (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g) := by
    intro τ τ' hne g hg g' hg'
    ext x
    apply hinj
    simp only [ContinuousLinearMap.comp_apply]
    rw [(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]
    funext y
    simp only [rTr, mul_assoc]
    exact congrArg (fun z => ι x (y * z)) (GlobalTheory.T.realPlacePoint_commute_of_ne_place D θ hθ V τ τ' hne _
      (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _
      (GlobalTheory.GKExt.conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))
  obtain ⟨TE, hTE1, hTE2, hTE3⟩ := GlobalTheory.T.multilinear_gKMap_extends_to_smooth_vectors hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK' hL'
  obtain ⟨hequiv, hcont⟩ := GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp
    (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3
  let T : Formalism.IndefR.Mult.MMap M := ι.compMultilinearMap TE
  have hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ := fun v u h => by
    show ι (TE v) = T₀ u
    rw [hTE1 v u h, hT₀']
  have hMult : Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T := by
    refine ⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1, fun v k hk => by simp at hk, hequiv, hcont⟩
    exact GlobalTheory.T.isSmoothAutomorphicForm_multMap_value hHC D θ hθ V S M T U N hU (fun v => by
      have h := (hrange (ι (TE v))).1 ⟨TE v, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont
  refine ⟨T, hMult, fun u => ?_⟩
  let ue : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M := fun τ => ⟨(u τ : M.H τ), by rw [← kFin_eq M τ]; exact (u τ).2⟩
  refine ⟨fun τ => ⟨(u τ : M.H τ), kFin_le_sm hHC M τ (ue τ).2⟩, fun τ => rfl, ?_⟩
  rw [hext _ ue (fun τ => rfl)]
  show F (fun τ => e τ (ue τ)) = F u
  congr 1
end GlobalTheory.GKGlobalise
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global | exact _root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global | (intros; apply _root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.gelfandKirillov_globalization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ F : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ),
      (∀ u, IsAutFunSm θ V (F u)) ∧ (∀ u, IsCuspFun V (F u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F (Function.update u τ w) = Rder θ V τ X (F u)) →
      ∃ T : Formalism.IndefR.Mult.MMap M, Formalism.IndefR.Mult.IsMultMap θ M ∅ 1 T ∧
        ∀ u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) = u τ) ∧ T v = F u := by
  first | exact @_root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global | exact _root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global | (intros; apply _root_.GlobalTheory.GKGlobalise.gelfandKirillov_local_to_global <;> assumption)
end
