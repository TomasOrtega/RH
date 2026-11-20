import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct

/- English proof (translation)
Introduce `N hN`. Establish `hev : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ (L : Set V), c • y ∈ N`. Apply `hLc.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `y _`. Establish `hc : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y))` using `continuous_smul.tendsto _`.

Rewrite `hc` using `[zero_smul]`. Conclude with `hc hN`. Take `⟨k, hk⟩` from `(hπ.eventually hev).exists`. Establish `hpk : π ^ k ≠ 0` using `pow_ne_zero k h0`. Establish `he : ((L.map (DistribMulAction.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) = (fun x => π ^ k • x) '' (L : Set V)` using `AddSubgroup.coe_map _ _`.

Use `⟨L.map (DistribMulAction.toAddMonoidHom V (π ^ k)), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `(Homeomorph.smulOfNeZero (π ^ k) hpk).isOpenMap _ hLo`. Rewrite using `[he]`. Conclude with `hLc.image (continuous_const_smul _)`.

Rewrite using `[he]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hk y hy`.
-/
theorem hasCOSub_of_lat {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : HasCOSub V := by
  intro N hN
  have hev : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ (L : Set V), c • y ∈ N := by
    apply hLc.eventually_forall_of_forall_eventually
    intro y _
    have hc : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.tendsto _
    rw [zero_smul] at hc
    exact hc hN
  obtain ⟨k, hk⟩ := (hπ.eventually hev).exists
  have hpk : π ^ k ≠ 0 := pow_ne_zero k h0
  have he : ((L.map (DistribMulAction.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := AddSubgroup.coe_map _ _
  refine ⟨L.map (DistribMulAction.toAddMonoidHom V (π ^ k)), ?_, ?_, ?_⟩
  · rw [he]
    exact (Homeomorph.smulOfNeZero (π ^ k) hpk).isOpenMap _ hLo
  · rw [he]
    exact hLc.image (continuous_const_smul _)
  · rw [he]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Establish `hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)`. Rewrite using `[v.valuedAdicCompletion_eq_valuation' π, hπ]`. Use `⟨π, fun h => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[h, map_zero]`.

Conclude with `WithZero.exp_ne_zero hv.symm`. Establish `h1 : Valued.v (π : v.adicCompletion F) < 1`. Rewrite using `[hv]`. Evaluate the decidable proposition. Establish `hlt : ‖(π : v.adicCompletion F)‖ < 1` using `Valued.toNormedField.norm_lt_one_iff.2 h1`.

Conclude with `tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt`.
-/
theorem exists_pow_tendsto_zero_Fv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  refine ⟨π, fun h => ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
      rw [hv]
      decide
    have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt

def latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) where
  carrier := latV (M := M) (n := a) b v
  add_mem' := by
    intro x y hx hy
    simp only [latV, Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [Pi.add_apply, map_add, Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [latV, Set.mem_setOf_eq]
    intro i j k
    simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [latV, Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Take `⟨π, h0, hπ⟩` from `exists_pow_tendsto_zero_Fv v`. Conclude with `hasCOSub_of_lat (latSub (Module.finBasis F E) v a M) (PositiveNearLattice.isClopen_latV (Module.finBasis F E) v a M).isOpen (PositiveNearLattice.isCompact_latV (Module.finBasis F E) v a M) π h0 hπ`.
-/
theorem tensNA_holds : TensNA := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact hasCOSub_of_lat (latSub (Module.finBasis F E) v a M)
    (PositiveNearLattice.isClopen_latV (Module.finBasis F E) v a M).isOpen
    (PositiveNearLattice.isCompact_latV (Module.finBasis F E) v a M) π h0 hπ

def scaledB (𝕜 : Type) {V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (L : AddSubgroup V)
    (Λ : AddSubgroup V) : Prop :=
  ∃ c : 𝕜, c ≠ 0 ∧ Λ = L.map (DistribMulAction.toAddMonoidHom V c)

/- English proof (translation)
Introduce `N hN`. Establish `hev : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ (L : Set V), c • y ∈ N`. Apply `hLc.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `y _`. Establish `hc : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y))` using `continuous_smul.tendsto _`.

Rewrite `hc` using `[zero_smul]`. Conclude with `hc hN`. Take `⟨k, hk⟩` from `(hπ.eventually hev).exists`. Establish `hpk : π ^ k ≠ 0` using `pow_ne_zero k h0`. Establish `he : ((L.map (DistribMulAction.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) = (fun x => π ^ k • x) '' (L : Set V)` using `AddSubgroup.coe_map _ _`.

Use `⟨L.map (DistribMulAction.toAddMonoidHom V (π ^ k)), ⟨π ^ k, hpk, rfl⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `(Homeomorph.smulOfNeZero (π ^ k) hpk).isOpenMap _ hLo`. Rewrite using `[he]`. Conclude with `hLc.image (continuous_const_smul _)`.

Rewrite using `[he]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hk y hy`.
-/
theorem isCOBasis_scaled {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : IsCOBasis (scaledB 𝕜 L) := by
  intro N hN
  have hev : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ (L : Set V), c • y ∈ N := by
    apply hLc.eventually_forall_of_forall_eventually
    intro y _
    have hc : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.tendsto _
    rw [zero_smul] at hc
    exact hc hN
  obtain ⟨k, hk⟩ := (hπ.eventually hev).exists
  have hpk : π ^ k ≠ 0 := pow_ne_zero k h0
  have he : ((L.map (DistribMulAction.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := AddSubgroup.coe_map _ _
  refine ⟨L.map (DistribMulAction.toAddMonoidHom V (π ^ k)), ⟨π ^ k, hpk, rfl⟩, ?_, ?_, ?_⟩
  · rw [he]
    exact (Homeomorph.smulOfNeZero (π ^ k) hpk).isOpenMap _ hLo
  · rw [he]
    exact hLc.image (continuous_const_smul _)
  · rw [he]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

/- English proof (translation)
Take `⟨π, h0, hπ⟩` from `exists_pow_tendsto_zero_Fv v`. Conclude with `isCOBasis_scaled (latSub b v a M) (PositiveNearLattice.isClopen_latV b v a M).isOpen (PositiveNearLattice.isCompact_latV b v a M) π h0 hπ`.
-/
theorem isCOBasis_latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    IsCOBasis (scaledB (Fv F v) (latSub b v a M)) := by
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact isCOBasis_scaled (latSub b v a M) (PositiveNearLattice.isClopen_latV b v a M).isOpen
    (PositiveNearLattice.isCompact_latV b v a M) π h0 hπ

def DensVLat : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
      DensCosB (scaledB (Fv F v) (latSub b v a M)) μv (gramR (Fv F v) σ J) Subtype.val νv
        {X | LinearIndependent (Fv F v ⊗[F] E) X}

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν`. Take `⟨_t1, t2, _t3, _t4, _t5, _t6, _t7⟩` from `(hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Use `hμ.1` as an intermediate fact. Use `hν.1` as an intermediate fact.

Establish `: BorelSpace (Fv F v ⊗[F] E)` using `⟨rfl⟩`. Establish `: BorelSpace (HermR (Fv F v) σ a)` using `⟨rfl⟩`. Establish `: T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))` using `inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))`. Establish `: IsTopologicalAddGroup (Fv F v ⊗[F] E)` using `IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)`. Conclude with `densLC_of_cosB _ _ (isCOBasis_latSub (Module.finBasis F E) v a M) (hC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν _ (Module.finBasis F E))`.
-/
theorem densVLC_of_lat (hT : TensAll) (hC : DensVLat) : DensVLC := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, _t3, _t4, _t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  exact densLC_of_cosB _ _ (isCOBasis_latSub (Module.finBasis F E) v a M)
    (hC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν _ (Module.finBasis F E))

/- English proof (translation)
The claim follows from `densV_of hT tensNA_holds (densVLC_of_lat hT hC)`.
-/
theorem densV_of_lat (hT : TensAll) (hC : DensVLat) : DensV :=
  densV_of hT tensNA_holds (densVLC_of_lat hT hC)

end PI.VolStabS
