import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPointsOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedPointsNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

/- English proof (translation)
Introduce `y hy` and use `⟨hy, d, ContinuousLinearMap.id ℂ _, ball c ε, ball c ε, id, isOpen_ball, isOpen_ball, hy, analyticOnNhd_id, fun _ _ => rfl, by simp⟩`.
-/
theorem isRegularPointOf_ball {d : ℕ} (c : Fin d → ℂ) (ε : ℝ) :
    ∀ y ∈ ball c ε, IsRegularPointOf (ball c ε) y := fun y hy =>
  ⟨hy, d, ContinuousLinearMap.id ℂ _, ball c ε, ball c ε, id, isOpen_ball, isOpen_ball, hy,
    analyticOnNhd_id, fun _ _ => rfl, by simp⟩

/- English proof (translation)
Introduce `σ _ X x d A hX hirr hiso hinj`. Take `⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩` from `hPF σ X x d A hX hirr hiso hinj`. Take `⟨M, hM, hMsh⟩` from `hSh σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz`. Establish `hnear` using `hNear σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz`. Use `⟨δ, hδ, hδ0, fun W hW => ?_⟩` and prove the remaining obligations.

Take `⟨W₀, hW₀, hiso'⟩` from `hiso`. Take `⟨Nn, k, f, hNo, hxN, hf, hXN⟩` from `hX`. Take `⟨r, hr, hrsub⟩` from `Metric.mem_nhds_iff.mp (inter_mem (inter_mem hW hM) (inter_mem hW₀ (hNo.mem_nhds hxN)))`. Establish `hr2 : 0 < r / 2` using `half_pos hr`. Establish `hcb : closedBall x (r / 2) ⊆ (W ∩ M) ∩ (W₀ ∩ Nn)` using `(closedBall_subset_ball (half_lt_self hr)).trans hrsub`.

Use `set K : Set (σ → ℂ) := closedBall x (r / 2) ∩ ⋂ i, (closedBall x (r / 2) ∩ f i ⁻¹' {0}) with hK`. Establish `hKc : IsCompact K`. Use `(isCompact_closedBall x (r / 2)).of_isClosed_subset ?_ inter_subset_left` and prove the remaining obligations. Use `isClosed_closedBall.inter (isClosed_iInter fun i => ?_)` and prove the remaining obligations. Conclude with `((hf i).continuousOn.mono fun z hz => (hcb hz).2.2).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton`.

Establish `hKmem : ∀ z, z ∈ K ↔ z ∈ closedBall x (r / 2) ∧ z ∈ X`. Introduce `z`. Simplify using `only [hK, mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, h0⟩`.

Establish `: z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0}` using `⟨(hcb hz).2.2, fun i => (h0 i).2⟩`. Rewrite `this` using `[← hXN]`. Conclude with `⟨hz, this.1⟩`. Introduce and unpack `⟨hz, hzX⟩`. Establish `: z ∈ X ∩ Nn` using `⟨hzX, (hcb hz).2.2⟩`.

Rewrite `this` using `[hXN]`. Conclude with `⟨hz, fun i => ⟨hz, this.2 i⟩⟩`. Establish `hSc : IsCompact (K ∩ sphere x (r / 2))` using `hKc.inter_right isClosed_sphere`. Establish `hAS : A x ∉ A '' (K ∩ sphere x (r / 2))`. Introduce and unpack `⟨z, ⟨hzK, hzs⟩, hAz⟩`.

Establish `hzx : z = x` using `hiso' z ⟨((hKmem z).mp hzK).2, (hcb ((hKmem z).mp hzK).1).2.1⟩ hAz`. Rewrite `hzs` using `[hzx, mem_sphere, dist_self]`. Conclude with `hr2.ne hzs`. Take `⟨ε₁, hε₁, hε₁S⟩` from `Metric.isOpen_iff.mp (hSc.image A.continuous).isClosed.isOpen_compl (A x) hAS`. Take `⟨ε₂, hε₂, hε₂a⟩` from `hδ.exists_ball_analyticOnNhd`.

Use `set D := ball (A x) (min ε₁ ε₂) with hD`. Establish `hε : 0 < min ε₁ ε₂` using `lt_min hε₁ hε₂`. Establish `hDa : AnalyticOnNhd ℂ δ D` using `hε₂a.mono (ball_subset_ball (min_le_right _ _))`. Use `set T := D \ {y | δ y = 0} with hT`. Establish `hTo : IsOpen T` using `hDa.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton`.

Establish `hTc : IsPreconnected T`. Use `hConn (Fin d) D δ (convex_ball _ _).isPreconnected (isRegularPointOf_ball _ _) hDa ?_` and prove the remaining obligations. Take `⟨y, hy0, hyD⟩` from `((Filter.not_eventually.mp hδ0).and_eventually (ball_mem_nhds _ hε)).exists`. Conclude with `⟨y, hyD, hy0⟩`. Use `set u : Set (Fin d → ℂ) := T ∩ A '' (X ∩ ball x (r / 2)) with hu`.

Establish `huo : IsOpen u`. Use `isOpen_iff_mem_nhds.mpr ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩`. Take `⟨O, V, g, hO, hV, hzV, hg, hAg, hXV⟩` from `hMsh z ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.2⟩ hyT.2`. Take `⟨t₀, ht₀, hgt₀⟩ : z ∈ g '' O` from `hXV ▸ ⟨hzX, hzV⟩`.

Establish `hAz : A z = t₀` using `by rw [← hgt₀]; exact hAg t₀ ht₀`. Rewrite `hyT`, the goal using `[hAz]`. Establish `hpre : g ⁻¹' (V ∩ ball x (r / 2)) ∈ 𝓝 t₀` using `(hg t₀ ht₀).continuousAt.preimage_mem_nhds ((hV.inter isOpen_ball).mem_nhds (hgt₀ ▸ ⟨hzV, hzb⟩))`. Use `filter_upwards [hTo.mem_nhds hyT, hO.mem_nhds ht₀, hpre] with t ht htO htg`. Establish `hgX : g t ∈ X ∩ V` using `hXV ▸ ⟨t, htO, rfl⟩`.

Conclude with `⟨ht, g t, ⟨hgX.1, htg.2⟩, hAg t htO⟩`. Establish `hune : (T ∩ u).Nonempty`. Establish `hU : ball x (r / 2) ∩ A ⁻¹' D ∈ 𝓝 x` using `inter_mem (ball_mem_nhds x hr2) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))`. Take `⟨z, ⟨hzX, hzb, hzD⟩, hδz, -⟩` from `hnear _ hU`. Conclude with `⟨A z, ⟨hzD, hδz⟩, ⟨hzD, hδz⟩, z, ⟨hzX, hzb⟩, rfl⟩`.

Establish `hucl : closure u ∩ T ⊆ u`. Introduce and unpack `y ⟨hycl, hyT⟩`. Establish `hsubK : u ⊆ A '' K`. Introduce and unpack `_ ⟨-, z, ⟨hzX, hzb⟩, rfl⟩`. Conclude with `⟨z, (hKmem z).mpr ⟨ball_subset_closedBall hzb, hzX⟩, rfl⟩`.

Take `⟨z, hzK, rfl⟩` from `(hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsubK hycl`. Take `⟨hzcb, hzX⟩` from `(hKmem z).mp hzK`. Establish `hzb : z ∈ ball x (r / 2)`. Use `mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hzcb) fun hzs => ?_)` and prove the remaining obligations. Conclude with `hε₁S (ball_subset_ball (min_le_left _ _) hyT.1) ⟨z, ⟨hzK, mem_sphere.mpr hzs⟩, rfl⟩`.

Conclude with `⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩`. Establish `hTu : T ⊆ u` using `hTc.subset_of_closure_inter_subset huo hune hucl`. Use `filter_upwards [ball_mem_nhds (A x) hε] with y hy hδy`. Take `⟨-, z, ⟨hzX, hzb⟩, hzy⟩` from `hTu ⟨hy, hδy⟩`. Conclude with `⟨z, ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.1⟩, hzy⟩`.
-/
theorem IrreducibleGermPointsOffDiscriminant.proof (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement) (hNear : PrimitiveFormSheetedPointsNear.Statement)
    (hConn : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermPointsOffDiscriminant.Statement := by
  intro σ _ X x d A hX hirr hiso hinj
  obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩ := hPF σ X x d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  have hnear := hNear σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  refine ⟨δ, hδ, hδ0, fun W hW => ?_⟩
  obtain ⟨W₀, hW₀, hiso'⟩ := hiso
  obtain ⟨Nn, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hW hM) (inter_mem hW₀ (hNo.mem_nhds hxN)))
  have hr2 : 0 < r / 2 := half_pos hr
  have hcb : closedBall x (r / 2) ⊆ (W ∩ M) ∩ (W₀ ∩ Nn) := (closedBall_subset_ball (half_lt_self hr)).trans hrsub

  set K : Set (σ → ℂ) := closedBall x (r / 2) ∩ ⋂ i, (closedBall x (r / 2) ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x (r / 2)).of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).2.2).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKmem : ∀ z, z ∈ K ↔ z ∈ closedBall x (r / 2) ∧ z ∈ X := by
    intro z
    simp only [hK, mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, h0⟩
      have : z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0} := ⟨(hcb hz).2.2, fun i => (h0 i).2⟩
      rw [← hXN] at this
      exact ⟨hz, this.1⟩
    · rintro ⟨hz, hzX⟩
      have : z ∈ X ∩ Nn := ⟨hzX, (hcb hz).2.2⟩
      rw [hXN] at this
      exact ⟨hz, fun i => ⟨hz, this.2 i⟩⟩
  have hSc : IsCompact (K ∩ sphere x (r / 2)) := hKc.inter_right isClosed_sphere
  have hAS : A x ∉ A '' (K ∩ sphere x (r / 2)) := by
    rintro ⟨z, ⟨hzK, hzs⟩, hAz⟩
    have hzx : z = x := hiso' z ⟨((hKmem z).mp hzK).2, (hcb ((hKmem z).mp hzK).1).2.1⟩ hAz
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr2.ne hzs
  obtain ⟨ε₁, hε₁, hε₁S⟩ := Metric.isOpen_iff.mp (hSc.image A.continuous).isClosed.isOpen_compl (A x) hAS
  obtain ⟨ε₂, hε₂, hε₂a⟩ := hδ.exists_ball_analyticOnNhd
  set D := ball (A x) (min ε₁ ε₂) with hD
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ D := hε₂a.mono (ball_subset_ball (min_le_right _ _))

  set T := D \ {y | δ y = 0} with hT
  have hTo : IsOpen T := hDa.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hTc : IsPreconnected T := by
    refine hConn (Fin d) D δ (convex_ball _ _).isPreconnected (isRegularPointOf_ball _ _) hDa ?_
    obtain ⟨y, hy0, hyD⟩ := ((Filter.not_eventually.mp hδ0).and_eventually (ball_mem_nhds _ hε)).exists
    exact ⟨y, hyD, hy0⟩

  set u : Set (Fin d → ℂ) := T ∩ A '' (X ∩ ball x (r / 2)) with hu
  have huo : IsOpen u := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro y ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
    obtain ⟨O, V, g, hO, hV, hzV, hg, hAg, hXV⟩ := hMsh z ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.2⟩ hyT.2
    obtain ⟨t₀, ht₀, hgt₀⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
    have hAz : A z = t₀ := by rw [← hgt₀]; exact hAg t₀ ht₀
    rw [hAz] at hyT ⊢
    have hpre : g ⁻¹' (V ∩ ball x (r / 2)) ∈ 𝓝 t₀ :=
      (hg t₀ ht₀).continuousAt.preimage_mem_nhds ((hV.inter isOpen_ball).mem_nhds (hgt₀ ▸ ⟨hzV, hzb⟩))
    filter_upwards [hTo.mem_nhds hyT, hO.mem_nhds ht₀, hpre] with t ht htO htg
    have hgX : g t ∈ X ∩ V := hXV ▸ ⟨t, htO, rfl⟩
    exact ⟨ht, g t, ⟨hgX.1, htg.2⟩, hAg t htO⟩
  have hune : (T ∩ u).Nonempty := by
    have hU : ball x (r / 2) ∩ A ⁻¹' D ∈ 𝓝 x :=
      inter_mem (ball_mem_nhds x hr2) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
    obtain ⟨z, ⟨hzX, hzb, hzD⟩, hδz, -⟩ := hnear _ hU
    exact ⟨A z, ⟨hzD, hδz⟩, ⟨hzD, hδz⟩, z, ⟨hzX, hzb⟩, rfl⟩
  have hucl : closure u ∩ T ⊆ u := by
    rintro y ⟨hycl, hyT⟩
    have hsubK : u ⊆ A '' K := by
      rintro _ ⟨-, z, ⟨hzX, hzb⟩, rfl⟩
      exact ⟨z, (hKmem z).mpr ⟨ball_subset_closedBall hzb, hzX⟩, rfl⟩
    obtain ⟨z, hzK, rfl⟩ := (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsubK hycl
    obtain ⟨hzcb, hzX⟩ := (hKmem z).mp hzK
    have hzb : z ∈ ball x (r / 2) := by
      refine mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hzcb) fun hzs => ?_)
      exact hε₁S (ball_subset_ball (min_le_left _ _) hyT.1) ⟨z, ⟨hzK, mem_sphere.mpr hzs⟩, rfl⟩
    exact ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
  have hTu : T ⊆ u := hTc.subset_of_closure_inter_subset huo hune hucl
  filter_upwards [ball_mem_nhds (A x) hε] with y hy hδy
  obtain ⟨-, z, ⟨hzX, hzb⟩, hzy⟩ := hTu ⟨hy, hδy⟩
  exact ⟨z, ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.1⟩, hzy⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
