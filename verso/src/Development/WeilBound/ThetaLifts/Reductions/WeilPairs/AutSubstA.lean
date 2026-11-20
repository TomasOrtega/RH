import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSubstitutionThetaHeisenbergUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFdPosFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.SubstA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

/- English proof (translation)
Take `⟨γ', -, e⟩` from `h`. Conclude with `⟨γ'.1, (congrArg Units.val e).symm⟩`.
-/
theorem exists_mtF_eq {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : GAF σ J} (h : γ ∈ GQF σ J) :
    ∃ m : Matrix (Fin n) (Fin n) E, mtF σ J γ = m.map (incAF F E) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

/- English proof (translation)
Rewrite using `[← GlobalTheory.WeilPartsF.actOF_mul, inv_mul_cancel, inv_mul_cancel, GlobalTheory.FinLatF.actOF_one]`.
-/
theorem actOF_inv_actOF (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    actOF σ JS JT g⁻¹ h⁻¹ (actOF σ JS JT g h x) = x := by
  rw [← GlobalTheory.WeilPartsF.actOF_mul, inv_mul_cancel, inv_mul_cancel, GlobalTheory.FinLatF.actOF_one]

/- English proof (translation)
Unfold `actOF`. Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`.
-/
theorem continuous_actOF (g : GAF σ JS) (h : GAF σ JT) : Continuous (actOF (nS := nS) (nT := nT) σ JS JT g h) := by
  unfold actOF
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/- English proof (translation)
Take `⟨m, hm⟩` from `exists_mtF_eq ((GQF σ JS).inv_mem hγ)`. Take `⟨m', hm'⟩` from `exists_mtF_eq hγ'`. Use `⟨m' * x * m, ?_⟩` and prove the remaining obligations. Unfold `actOF ratWF`. Rewrite using `[hm, hm', Matrix.map_mul, Matrix.map_mul]`.
-/
theorem exists_actOF_ratWF {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT)
    (x : Matrix (Fin nT) (Fin nS) E) : ∃ y, actOF σ JS JT γ γ' (ratWF (F := F) x) = ratWF y := by
  obtain ⟨m, hm⟩ := exists_mtF_eq ((GQF σ JS).inv_mem hγ)
  obtain ⟨m', hm'⟩ := exists_mtF_eq hγ'
  refine ⟨m' * x * m, ?_⟩
  unfold actOF ratWF
  rw [hm, hm', Matrix.map_mul, Matrix.map_mul]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Take `⟨z, hz⟩` from `exists_actOF_ratWF hγ hγ' y`. Conclude with `⟨z, hz.symm⟩`.
-/
theorem actOF_mem_ratLF {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT) {x : WOF F E nS nT}
    (hx : x ∈ ratLF F E nS nT) : actOF σ JS JT γ γ' x ∈ ratLF F E nS nT := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := exists_actOF_ratWF hγ hγ' y
  exact ⟨z, hz.symm⟩

/- English proof (translation)
Unfold `symplOHF`. Rewrite using `[PositivityTheory.ThKW.LatA.symplOF_actOF hS]`.
-/
theorem symplOHF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF
  rw [PositivityTheory.ThKW.LatA.symplOF_actOF hS]

/- English proof (translation)
Set `A : WOF F E nS nT →+ WOF F E nS nT` to `AddMonoidHom.mk' (actOF σ JS JT γ γ') (GlobalTheory.FinLatF.actOF_add γ γ')`. Establish `hA : Continuous (actOF (nS` using `nS) (nT := nT) σ JS JT γ γ') := continuous_actOF γ γ'`. Use `⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩` and prove the remaining obligations. Take `⟨y, e⟩` from `exists_actOF_ratWF hγ hγ' x show f (actOF σ JS JT γ γ' (ratWF x + w)) = _`. Rewrite using `[GlobalTheory.FinLatF.actOF_add, ← symplOHF_actOF hS γ γ', e, hf.quasi]`.

Take `⟨U, hU, h⟩` from `hf.level`. Use `⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Establish `e` using `congrFun (h _ hu (GlobalTheory.FinLatF.actOF_mem_finSubF γ γ' h0)) (actOF σ JS JT γ γ' w)`. Unfold `heisOF at e ⊢`.

Rewrite using `[← e, ← symplOHF_actOF hS γ γ' w u]`. Conclude with `congrArg (fun x => _ * f x) (GlobalTheory.FinLatF.actOF_add γ γ' w u)`. Establish `h3 : ∀ t, (actOF σ JS JT γ γ' (L t)).map (finPartF F E) = 0` using `fun t => by`. Unfold `actOF`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]`.

Use `hf.smooth k (A.comp L) (hA.comp h1) h3 (actOF σ JS JT γ γ' w)` as an intermediate fact. Simplify using `only [GlobalTheory.FinLatF.actOF_add]`. Conclude with `this`.
-/
theorem isThetaFunOF_comp (hS : IsHermND σ JS) {ψ : AddChar (AF F) ℂ} {f : WOF F E nS nT → ℂ}
    (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT) :
    IsThetaFunOF σ JS JT ξ₀ ψ fun w => f (actOF σ JS JT γ γ' w) := by
  let A : WOF F E nS nT →+ WOF F E nS nT := AddMonoidHom.mk' (actOF σ JS JT γ γ') (GlobalTheory.FinLatF.actOF_add γ γ')
  have hA : Continuous (actOF (nS := nS) (nT := nT) σ JS JT γ γ') := continuous_actOF γ γ'
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨y, e⟩ := exists_actOF_ratWF hγ hγ' x
    show f (actOF σ JS JT γ γ' (ratWF x + w)) = _
    rw [GlobalTheory.FinLatF.actOF_add, ← symplOHF_actOF hS γ γ', e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu (GlobalTheory.FinLatF.actOF_mem_finSubF γ γ' h0)) (actOF σ JS JT γ γ' w)
    unfold heisOF at e ⊢
    rw [← e, ← symplOHF_actOF hS γ γ' w u]
    exact congrArg (fun x => _ * f x) (GlobalTheory.FinLatF.actOF_add γ γ' w u)
  · have h3 : ∀ t, (actOF σ JS JT γ γ' (L t)).map (finPartF F E) = 0 := fun t => by
      unfold actOF
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    have := hf.smooth k (A.comp L) (hA.comp h1) h3 (actOF σ JS JT γ γ' w)
    simp only [GlobalTheory.FinLatF.actOF_add]
    exact this

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `: LocallyCompactSpace (AF F)` using `GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Establish `: SecondCountableTopology (AF F)` using `GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Establish `: T2Space (AF F)` using `GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Establish `: IsModuleTopology (AF F) (AF F ⊗[F] E)` using `⟨rfl⟩`.

Establish `: IsTopologicalRing (AF F ⊗[F] E)` using `IsModuleTopology.isTopologicalRing (AF F) _`. Take `⟨e'⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Establish `: LocallyCompactSpace (AF F ⊗[F] E)` using `e'.isClosedEmbedding.locallyCompactSpace`. Establish `: SecondCountableTopology (AF F ⊗[F] E)` using `e'.secondCountableTopology`. Establish `: T2Space (AF F ⊗[F] E)` using `e'.isEmbedding.t2Space`.

Establish `: LocallyCompactSpace (WOF F E nS nT)` using `inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AF F ⊗[F] E))`. Establish `: SecondCountableTopology (WOF F E nS nT)` using `inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AF F ⊗[F] E))`. Establish `: T2Space (WOF F E nS nT)` using `inferInstanceAs (T2Space (Fin nT → Fin nS → AF F ⊗[F] E))`. Use `haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩`. Use `haveI tZ : IsTopologicalAddGroup (WOF F E nS nT) := inferInstance`.

Establish `hdisc : DiscreteTopology (ratLF F E nS nT)`. Take `⟨U, hU, hx⟩` from `GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F) (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)`. Establish `hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈ nhds (0 : WOF F E nS nT)` using `set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU`. Use `discreteTopology_of_isOpen_singleton_zero ?_` and prove the remaining obligations. Rewrite using `[isOpen_singleton_iff_nhds_eq_pure]`.

Use `le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)` and prove the remaining obligations. Establish `hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0` using `continuous_subtype_val.continuousAt`. Use `Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_` and prove the remaining obligations. Introduce and unpack `⟨_, y, rfl⟩ hy`. Establish `hy0 : y = 0`.

Use function extensionality and compare the values at `i j`. Conclude with `hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))`. Substitute `hy0` using the available equality. Conclude with `Subtype.ext (map_zero _)`. Use `haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`.

Take `⟨K, hK, hx⟩` from `GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F) (GlobalTheory.AdeleCocompact.exists_compact_adele F)`. Use `choose c hc using hx`. Establish `hcov : ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K)` using `fun x => ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩`. Establish `hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) : Set (WOF F E nS nT))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK`. Establish `hfin` using `@GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (WOF F E nS nT) _ _ tZ _ _ (ratLF F E nS nT) _ _ hKc hcov μ hμ 𝓕 h𝓕`.

Conclude with `@GlobalTheory.RatSubst.setLIntegral_comp_addEquiv (WOF F E nS nT) _ _ tZ _ _ _ _ (ratLF F E nS nT) _ e he hes hΓ μ hμ 𝓕 h𝓕 hfin.ne φ hφ`.
-/
theorem setLIntegral_comp (e : WOF F E nS nT ≃+ WOF F E nS nT) (he : Continuous e) (hes : Continuous e.symm)
    (hΓ : ∀ x, e x ∈ ratLF F E nS nT ↔ x ∈ ratLF F E nS nT) (μ : Measure (WOF F E nS nT)) (hμ : μ.IsAddHaarMeasure)
    {𝓕 : Set (WOF F E nS nT)} (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ) (φ : WOF F E nS nT → ENNReal)
    (hφ : ∀ γ ∈ ratLF F E nS nT, ∀ x, φ (γ + x) = φ x) : ∫⁻ w in 𝓕, φ (e w) ∂μ = ∫⁻ w in 𝓕, φ w ∂μ := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e'⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AF F ⊗[F] E) := e'.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AF F ⊗[F] E) := e'.secondCountableTopology
  have : T2Space (AF F ⊗[F] E) := e'.isEmbedding.t2Space
  have : LocallyCompactSpace (WOF F E nS nT) :=
    inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AF F ⊗[F] E))
  have : SecondCountableTopology (WOF F E nS nT) :=
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AF F ⊗[F] E))
  have : T2Space (WOF F E nS nT) := inferInstanceAs (T2Space (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI tZ : IsTopologicalAddGroup (WOF F E nS nT) := inferInstance
  have hdisc : DiscreteTopology (ratLF F E nS nT) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hcov : ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈
      (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :=
    fun x => ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have hfin := @GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (WOF F E nS nT) _ _ tZ _ _ (ratLF F E nS nT) _ _
    hKc hcov μ hμ 𝓕 h𝓕
  exact @GlobalTheory.RatSubst.setLIntegral_comp_addEquiv (WOF F E nS nT) _ _ tZ _ _ _ _ (ratLF F E nS nT) _ e he hes hΓ μ hμ 𝓕 h𝓕
    hfin.ne φ hφ

end PositivityTheory.ThKW.SubstA

end
