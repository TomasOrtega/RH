import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StProjHoloLocal
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLocalOrbitChart
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicInverse
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

/- English proof (translation)
Take `⟨j, hj⟩` from `A.cover (e.symm u)`. Establish `h1 : AnalyticAt ℂ (A.chart j ∘ e.symm) u` using `(he j).2 u ⟨hu, hj⟩`. Establish `h2 : AnalyticAt ℂ (g ∘ (A.chart j).symm) ((A.chart j ∘ e.symm) u)`. Use `hg j _ ⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations. Use `show (A.chart j).symm (A.chart j (e.symm u)) ∈ U`.

Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `huU`. Establish `h3 : g ∘ e.symm =ᶠ[𝓝 u] (g ∘ (A.chart j).symm) ∘ (A.chart j ∘ e.symm)`. Establish `: ∀ᶠ u' in 𝓝 u, e.symm u' ∈ (A.chart j).source` using `(e.continuousAt_symm hu).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)`. Use `filter_upwards [this] with u' hu'`.

Simplify using `only [Function.comp, (A.chart j).left_inv hu']`. Conclude with `(h2.comp h1).differentiableAt.congr_of_eventuallyEq h3`.
-/
theorem holoOn_comp_compatChart_symm {d : ℕ} {X : Type} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas d X} {e : OpenPartialHomeomorph X (Fin d → ℂ)}
    (he : ReciprocityTheory.AnForm.M.IsCompatChart A e) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {u : Fin d → ℂ} (hu : u ∈ e.target) (huU : e.symm u ∈ U) :
    DifferentiableAt ℂ (g ∘ e.symm) u := by
  obtain ⟨j, hj⟩ := A.cover (e.symm u)
  have h1 : AnalyticAt ℂ (A.chart j ∘ e.symm) u := (he j).2 u ⟨hu, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart j).symm) ((A.chart j ∘ e.symm) u) := by
    refine hg j _ ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j (e.symm u)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact huU
  have h3 : g ∘ e.symm =ᶠ[𝓝 u] (g ∘ (A.chart j).symm) ∘ (A.chart j ∘ e.symm) := by
    have : ∀ᶠ u' in 𝓝 u, e.symm u' ∈ (A.chart j).source :=
      (e.continuousAt_symm hu).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
    filter_upwards [this] with u' hu'
    simp only [Function.comp, (A.chart j).left_inv hu']
  exact (h2.comp h1).differentiableAt.congr_of_eventuallyEq h3

/- English proof (translation)
Introduce `II Ψ _ K _ ι _ Ω _ _ E _ _ D M e he z hz hze`. Take `⟨N, hNo, hzN, κ, hκ, hκt, hκs⟩` from `hL K ι Ω D.y D.n D.arith D.smoothGeneric z hz`. Take `⟨U, hUo, hxU, s, hs, hsh⟩` from `M.sections (M.proj z)`. Take `⟨c, hc, hcz⟩` from `(M.fibre z hz _ (hs _ hxU).1).1 (hs _ hxU).2.symm`. Establish `hsxN : s (M.proj z) ∈ N` using `by rw [hcz]; exact (hκt z hzN c hc).1`.

Establish `hκsx : κ (s (M.proj z)) = κ z` using `by rw [hcz]; exact (hκt z hzN c hc).2`. Establish `hsd : ∀ u ∈ e.target, e.symm u ∈ U → DifferentiableAt ℂ (s ∘ e.symm) u` using `fun u hu huU => differentiableAt_pi.2 fun p => holoOn_comp_compatChart_symm he (hsh p) hu huU`. Establish `hex : e (M.proj z) ∈ e.target` using `e.map_source hze`. Establish `hexU : e.symm (e (M.proj z)) ∈ U` using `by rw [e.left_inv hze]; exact hxU`. Establish `hTn : e.target ∩ e.symm ⁻¹' U ∩ (s ∘ e.symm) ⁻¹' N ∈ 𝓝 (e (M.proj z))`.

Use `Filter.inter_mem (Filter.inter_mem (e.open_target.mem_nhds hex) ?_) ?_` and prove the remaining obligations. Conclude with `(e.continuousAt_symm hex).preimage_mem_nhds (hUo.mem_nhds hexU)`. Use `(hsd _ hex hexU).continuousAt.preimage_mem_nhds (hNo.mem_nhds ?_) show s (e.symm (e (M.proj z))) ∈ N` and prove the remaining obligations. Rewrite using `[e.left_inv hze]`. Conclude with `hsxN`.

Take `⟨T, hTsub, hTo, hxT⟩` from `mem_nhds_iff.1 hTn`. Establish `hψd : DifferentiableOn ℂ (κ ∘ s ∘ e.symm) T` using `fun u hu => ((hκ _ (hTsub hu).2).differentiableAt.comp u (hsd u (hTsub hu).1.1 (hTsub hu).1.2)).differentiableWithinAt`. Establish `hψi : Set.InjOn (κ ∘ s ∘ e.symm) T`. Introduce `u hu u' hu' h`. Establish `h1` using `hs _ (hTsub hu).1.2`.

Establish `h2` using `hs _ (hTsub hu').1.2`. Take `⟨c', hc', hcc⟩` from `hκs _ ⟨(hTsub hu).2, h1.1⟩ _ ⟨(hTsub hu').2, h2.1⟩ h`. Establish `hp : M.proj (s (e.symm u)) = M.proj (s (e.symm u'))` using `(M.fibre _ h1.1 _ h2.1).2 ⟨c', hc', hcc⟩`. Rewrite `hp` using `[h1.2, h2.2]`. Conclude with `e.symm.injOn (hTsub hu).1.1 (hTsub hu').1.1 hp`.

Take `⟨hψo, g, hg, hgψ⟩` from `hO D.n T (κ ∘ s ∘ e.symm) hTo hψd hψi`. Take `⟨O, hOo, hOeq⟩` from `continuousOn_iff'.1 M.cont (e.source ∩ e ⁻¹' T) (e.isOpen_inter_preimage hTo)`. Use `⟨O ∩ (N ∩ κ ⁻¹' ((κ ∘ s ∘ e.symm) '' T)), hOo.inter (hκ.continuousOn.isOpen_inter_preimage hNo hψo), ?_, g ∘ κ, ?_, ?_⟩` and prove the remaining obligations. Use `⟨?_, hzN, e (M.proj z), hxT, ?_⟩` and prove the remaining obligations. Establish `hz' : z ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y)` using `⟨⟨hze, hxT⟩, hz⟩`.

Rewrite `hz'` using `[hOeq]`. Conclude with `hz'.1`. Use `show κ (s (e.symm (e (M.proj z)))) = κ z`. Rewrite using `[e.left_inv hze]`. Conclude with `hκsx`.

Introduce `w hw`. Conclude with `((hg.differentiableAt (hψo.mem_nhds hw.2.2)).comp w (hκ w hw.2.1).differentiableAt).differentiableWithinAt`. Introduce and unpack `z' ⟨⟨hz'O, hz'N, -⟩, hz'⟩`. Establish `hp : z' ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y)`. Rewrite using `[hOeq]`.

Conclude with `⟨hz'O, hz'⟩`. Take `⟨⟨hpe, hpT⟩, -⟩` from `hp`. Use `⟨hpe, ?_⟩` and prove the remaining obligations. Establish `hpU : M.proj z' ∈ U`. Establish `h` using `(hTsub hpT).1.2`.

Rewrite `h` using `[Set.mem_preimage, e.left_inv hpe]`. Then use the resulting hypothesis. Take `⟨c', hc', hcc⟩` from `(M.fibre z' hz' _ (hs _ hpU).1).1 (hs _ hpU).2.symm`. Establish `hκ' : κ (s (M.proj z')) = κ z'` using `by rw [hcc]; exact (hκt z' hz'N c' hc').2`. Establish `hψz : (κ ∘ s ∘ e.symm) (e (M.proj z')) = κ z'` using `by show κ (s (e.symm (e (M.proj z')))) = κ z'`. Rewrite using `[e.left_inv hpe]`.

Conclude with `hκ'`. Use `show e (M.proj z') = g (κ z')`. Rewrite using `[← hψz, hgψ _ hpT]`.
-/
theorem ProjHoloLocal.proof (hL : LocalOrbitChart.Statement)
    (hO : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement) : ProjHoloLocal.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D M e he z hz hze

  obtain ⟨N, hNo, hzN, κ, hκ, hκt, hκs⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z hz

  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections (M.proj z)
  obtain ⟨c, hc, hcz⟩ := (M.fibre z hz _ (hs _ hxU).1).1 (hs _ hxU).2.symm
  have hsxN : s (M.proj z) ∈ N := by rw [hcz]; exact (hκt z hzN c hc).1
  have hκsx : κ (s (M.proj z)) = κ z := by rw [hcz]; exact (hκt z hzN c hc).2
  have hsd : ∀ u ∈ e.target, e.symm u ∈ U → DifferentiableAt ℂ (s ∘ e.symm) u := fun u hu huU =>
    differentiableAt_pi.2 fun p => holoOn_comp_compatChart_symm he (hsh p) hu huU

  have hex : e (M.proj z) ∈ e.target := e.map_source hze
  have hexU : e.symm (e (M.proj z)) ∈ U := by rw [e.left_inv hze]; exact hxU
  have hTn : e.target ∩ e.symm ⁻¹' U ∩ (s ∘ e.symm) ⁻¹' N ∈ 𝓝 (e (M.proj z)) := by
    refine Filter.inter_mem (Filter.inter_mem (e.open_target.mem_nhds hex) ?_) ?_
    · exact (e.continuousAt_symm hex).preimage_mem_nhds (hUo.mem_nhds hexU)
    · refine (hsd _ hex hexU).continuousAt.preimage_mem_nhds (hNo.mem_nhds ?_)
      show s (e.symm (e (M.proj z))) ∈ N
      rw [e.left_inv hze]
      exact hsxN
  obtain ⟨T, hTsub, hTo, hxT⟩ := mem_nhds_iff.1 hTn
  have hψd : DifferentiableOn ℂ (κ ∘ s ∘ e.symm) T := fun u hu =>
    ((hκ _ (hTsub hu).2).differentiableAt.comp u
      (hsd u (hTsub hu).1.1 (hTsub hu).1.2)).differentiableWithinAt
  have hψi : Set.InjOn (κ ∘ s ∘ e.symm) T := by
    intro u hu u' hu' h
    have h1 := hs _ (hTsub hu).1.2
    have h2 := hs _ (hTsub hu').1.2
    obtain ⟨c', hc', hcc⟩ := hκs _ ⟨(hTsub hu).2, h1.1⟩ _ ⟨(hTsub hu').2, h2.1⟩ h
    have hp : M.proj (s (e.symm u)) = M.proj (s (e.symm u')) :=
      (M.fibre _ h1.1 _ h2.1).2 ⟨c', hc', hcc⟩
    rw [h1.2, h2.2] at hp
    exact e.symm.injOn (hTsub hu).1.1 (hTsub hu').1.1 hp

  obtain ⟨hψo, g, hg, hgψ⟩ := hO D.n T (κ ∘ s ∘ e.symm) hTo hψd hψi

  obtain ⟨O, hOo, hOeq⟩ :=
    continuousOn_iff'.1 M.cont (e.source ∩ e ⁻¹' T) (e.isOpen_inter_preimage hTo)
  refine ⟨O ∩ (N ∩ κ ⁻¹' ((κ ∘ s ∘ e.symm) '' T)),
    hOo.inter (hκ.continuousOn.isOpen_inter_preimage hNo hψo), ?_, g ∘ κ, ?_, ?_⟩
  · refine ⟨?_, hzN, e (M.proj z), hxT, ?_⟩
    · have hz' : z ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := ⟨⟨hze, hxT⟩, hz⟩
      rw [hOeq] at hz'
      exact hz'.1
    · show κ (s (e.symm (e (M.proj z)))) = κ z
      rw [e.left_inv hze]
      exact hκsx
  · intro w hw
    exact ((hg.differentiableAt (hψo.mem_nhds hw.2.2)).comp w
      (hκ w hw.2.1).differentiableAt).differentiableWithinAt
  · rintro z' ⟨⟨hz'O, hz'N, -⟩, hz'⟩
    have hp : z' ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := by
      rw [hOeq]
      exact ⟨hz'O, hz'⟩
    obtain ⟨⟨hpe, hpT⟩, -⟩ := hp
    refine ⟨hpe, ?_⟩
    have hpU : M.proj z' ∈ U := by
      have h := (hTsub hpT).1.2
      rwa [Set.mem_preimage, e.left_inv hpe] at h
    obtain ⟨c', hc', hcc⟩ := (M.fibre z' hz' _ (hs _ hpU).1).1 (hs _ hpU).2.symm
    have hκ' : κ (s (M.proj z')) = κ z' := by rw [hcc]; exact (hκt z' hz'N c' hc').2
    have hψz : (κ ∘ s ∘ e.symm) (e (M.proj z')) = κ z' := by
      show κ (s (e.symm (e (M.proj z')))) = κ z'
      rw [e.left_inv hpe]
      exact hκ'
    show e (M.proj z') = g (κ z')
    rw [← hψz, hgψ _ hpT]

end GroundTheory.Heights₂.Heights.LowerBoundFree
