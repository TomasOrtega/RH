import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MeasurableSetBallSet

open NumberField Module Filter Topology

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Use `haveI : IsEmpty {w : InfinitePlace K // w.IsReal} := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩`. Take `⟨b, hbL, ho⟩` from `BallB.exists_orth_basis_mem hK hs hd hL`. Establish `hBL : Submodule.span (𝓞 K) (Set.range b) ≤ L` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)`. Take `⟨N, hN, hNx⟩` from `LocF.exists_zsmul_le hL (BallB.isLattice_span b)`. Establish `hlat1 : BallD.lat b (Submodule.span (𝓞 K) (Set.range b)) = Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))` using `BallD.lat_span b`.

Establish `hle : Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) ≤ BallD.lat b L`. Rewrite using `[← hlat1]`. Introduce `y hy`. Rewrite `hy`, the goal using `[BallD.mem_lat]`. Take `⟨x, hx, rfl⟩` from `hy`.

Conclude with `⟨x, hBL hx, rfl⟩`. Establish `hNy : ∀ y ∈ BallD.lat b L, N • y ∈ Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))`. Introduce `y hy`. Rewrite using `[← hlat1]`. Rewrite `hy`, the goal using `[BallD.mem_lat]`.

Take `⟨x, hx, rfl⟩` from `hy`. Conclude with `⟨N • x, hNx x hx, map_zsmul (BallD.emb b) N x⟩`. Establish `hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re` using `fun w i => hd (b i) (b.ne_zero i) w.1.embedding`. Take `⟨hidx, hT⟩` from `BallA.tendsto_card_of_le (μ := MeasureTheory.volume) (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) (BallD.lat b L) hle hN hNy (BallD.isBounded_ballSet hA) BallD.measurableSet_ballSet (BallD.convex_ballSet hA)`. Establish `hfr : finrank ℝ (Fin (finrank K V) → NumberField.mixedEmbedding.mixedSpace K) = 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V`.

Rewrite using `[Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, NumberField.mixedEmbedding.finrank, finrank_eq_two_fDeg hK]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcov : ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume = Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V)`. Rewrite using `[BallC.covolume_piBasis, covolume_integerLattice_eq hK, Fintype.card_fin, ← pow_mul]`. Establish `hidx' : (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex (BallD.lat b L).toAddSubgroup = (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup`.

Rewrite using `[← hlat1]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ (BallD.emb_injective b)`. Establish `hI0 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0`. Rewrite using `[← hidx']`. Conclude with `hidx`.

Establish `hnorm` using `BallB.normD_mul_relIndex hK hLi b hbL hI0`. Establish `hgdet` using `BallB.prod_place_gdet hK hs hd b ho`. Establish `hvol` using `BallD.volume_ballSet hA`. Establish `hP : 0 < ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re` using `Finset.prod_pos fun w _ => Finset.prod_pos fun i _ => hA w i`. Establish `hIr : ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0`.

Conclude with `hI0` after adjusting the coercions. Establish `hND : normD h L ≠ 0`. Introduce `h0`. Rewrite `hnorm` using `[h0, zero_mul, hgdet]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hV : Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) ≠ 0` using `pow_ne_zero _ (vInv_pos K).ne'`. Establish `hlim : MeasureTheory.volume.real (BallD.ballSet h b) * ((Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex (BallD.lat b L).toAddSubgroup : ℝ) / ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureT …`. Rewrite using `[hvol, hcov, hidx', ← hgdet, ← hnorm, nrComplexPlaces_eq_fDeg hK]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← hlim]`.

Use `Tendsto.congr' ?_ hT` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with j hj`. Rewrite using `[BallD.card_eq hK ho L hj, hfr]`.
-/
theorem tendsto_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    Tendsto (fun j : ℕ => (ballCount h L ((j : ℝ) ^ 2) : ℝ) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L))) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  obtain ⟨b, hbL, ho⟩ := BallB.exists_orth_basis_mem hK hs hd hL
  have hBL : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
  obtain ⟨N, hN, hNx⟩ := LocF.exists_zsmul_le hL (BallB.isLattice_span b)
  have hlat1 : BallD.lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := BallD.lat_span b
  have hle : Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) ≤ BallD.lat b L := by
    rw [← hlat1]
    intro y hy
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hBL hx, rfl⟩
  have hNy : ∀ y ∈ BallD.lat b L,
      N • y ∈ Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := by
    intro y hy
    rw [← hlat1]
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨N • x, hNx x hx, map_zsmul (BallD.emb b) N x⟩
  have hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re :=
    fun w i => hd (b i) (b.ne_zero i) w.1.embedding
  obtain ⟨hidx, hT⟩ := BallA.tendsto_card_of_le (μ := MeasureTheory.volume)
    (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) (BallD.lat b L) hle hN hNy
    (BallD.isBounded_ballSet hA) BallD.measurableSet_ballSet (BallD.convex_ballSet hA)
  have hfr : finrank ℝ (Fin (finrank K V) → NumberField.mixedEmbedding.mixedSpace K) = 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      NumberField.mixedEmbedding.finrank, finrank_eq_two_fDeg hK]
    ring
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    rw [BallC.covolume_piBasis, covolume_integerLattice_eq hK, Fintype.card_fin, ← pow_mul]
  have hidx' : (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
      (BallD.lat b L).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [← hlat1]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (BallD.emb_injective b)
  have hI0 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [← hidx']; exact hidx
  have hnorm := BallB.normD_mul_relIndex hK hLi b hbL hI0
  have hgdet := BallB.prod_place_gdet hK hs hd b ho
  have hvol := BallD.volume_ballSet hA
  have hP : 0 < ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re :=
    Finset.prod_pos fun w _ => Finset.prod_pos fun i _ => hA w i
  have hIr : ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hI0
  have hND : normD h L ≠ 0 := by
    intro h0
    rw [h0, zero_mul, hgdet] at hnorm
    linarith
  have hV : Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) ≠ 0 := pow_ne_zero _ (vInv_pos K).ne'
  have hlim : MeasureTheory.volume.real (BallD.ballSet h b) *
      ((Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
        (BallD.lat b L).toAddSubgroup : ℝ) /
      ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L) := by
    rw [hvol, hcov, hidx', ← hgdet, ← hnorm, nrComplexPlaces_eq_fDeg hK]
    field_simp
  rw [← hlim]
  refine Tendsto.congr' ?_ hT
  filter_upwards [eventually_gt_atTop 0] with j hj
  rw [BallD.card_eq hK ho L hj, hfr]

end Formalism.HermitianLattices.Ext.L3
