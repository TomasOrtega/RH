import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfIsAnalyticSubset

namespace GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions

noncomputable section

/- English proof (translation)
Take `⟨U, g, j, hU, ⟨z0, hz0⟩, hmaps, han, hinj⟩` from `h`. Establish `hgc : ∀ z ∈ U, ContinuousAt g z`. Introduce `z hz`. Establish `h0 : ContinuousAt (A.chart j ∘ g) z` using `(han z hz).continuousAt`. Establish `h1 : ContinuousAt ((A.chart j).symm ∘ (A.chart j ∘ g)) z` using `ContinuousAt.comp (g := (A.chart j).symm) (f := A.chart j ∘ g) ((A.chart j).continuousAt_symm ((A.chart j).map_source (hmaps hz).2)) h0`.

Use `h1.congr ?_` and prove the remaining obligations. Use `filter_upwards [hU.mem_nhds hz] with w hw`. Simplify using `[(A.chart j).left_inv (hmaps hw).2]`. Use `haveI : Countable F := hF.countable.to_subtype`. Set `f : Option F → Set (Fin k → ℂ)` to `fun i => match i with`.

Consider the case `none => Uᶜ`. Consider the case `some C => closure (U ∩ g ⁻¹' (C : Set X))`. Establish `hfc : ∀ i, IsClosed (f i)`. Introduce `i`. Consider the cases of `i with`.

Consider the case `none => exact hU.isClosed_compl`. Consider the case `some C => exact isClosed_closure`. Establish `hfu : ⋃ i, f i = Set.univ`. Use `Set.eq_univ_of_forall fun p => ?_` and prove the remaining obligations. Distinguish the cases in `hp : p ∈ U`.

Take `⟨C, hC, hpC⟩` from `(hmaps hp).1.1`. Conclude with `Set.mem_iUnion.2 ⟨some ⟨C, hC⟩, subset_closure ⟨hp, hpC⟩⟩`. Conclude with `Set.mem_iUnion.2 ⟨none, hp⟩`. Establish `hd` using `dense_iUnion_interior_of_closed hfc hfu`. Take `⟨p, hpU, hp⟩` from `hd.inter_open_nonempty U hU ⟨z0, hz0⟩`.

Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hp`. Consider the cases of `i with`. Consider the case `none => exact absurd hpU (interior_subset hi)`. Consider the case `some C`. Use `⟨C, C.2, U ∩ interior (f (some C)), g, j, hU.inter isOpen_interior, ⟨p, hpU, hi⟩, fun z hz => ⟨⟨?_, (hmaps hz.1).1.2⟩, (hmaps hz.1).2⟩, han.mono Set.inter_subset_left, fun z hz => hinj z hz.1⟩` and prove the remaining obligations.

Establish `hz' : z ∈ closure (U ∩ g ⁻¹' (C : Set X))` using `interior_subset hz.2`. Use `mem_closure_image (hgc z hz.1) hz'` as an intermediate fact. Establish `hsub : g '' (U ∩ g ⁻¹' (C : Set X)) ⊆ (C : Set X)`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hy.2`.

Conclude with `(hcl C C.2).closure_subset_iff.2 hsub this`.
-/
theorem hasHoloImm_of_finite_closed_cover {d : ℕ} {X : Type} [TopologicalSpace X]
    {A : FinHolAtlas d X} {F : Set (Set X)} (hF : F.Finite)
    (hcl : ∀ C ∈ F, IsClosed C) {R : Set X} {k : ℕ} (h : HasHoloImm A (⋃₀ F ∩ R) k) :
    ∃ C ∈ F, HasHoloImm A (C ∩ R) k := by
  obtain ⟨U, g, j, hU, ⟨z0, hz0⟩, hmaps, han, hinj⟩ := h
  have hgc : ∀ z ∈ U, ContinuousAt g z := by
    intro z hz
    have h0 : ContinuousAt (A.chart j ∘ g) z := (han z hz).continuousAt
    have h1 : ContinuousAt ((A.chart j).symm ∘ (A.chart j ∘ g)) z :=
      ContinuousAt.comp (g := (A.chart j).symm) (f := A.chart j ∘ g)
        ((A.chart j).continuousAt_symm ((A.chart j).map_source (hmaps hz).2)) h0
    refine h1.congr ?_
    filter_upwards [hU.mem_nhds hz] with w hw
    simp [(A.chart j).left_inv (hmaps hw).2]
  haveI : Countable F := hF.countable.to_subtype
  let f : Option F → Set (Fin k → ℂ) := fun i => match i with
    | none => Uᶜ
    | some C => closure (U ∩ g ⁻¹' (C : Set X))
  have hfc : ∀ i, IsClosed (f i) := by
    intro i; cases i with
    | none => exact hU.isClosed_compl
    | some C => exact isClosed_closure
  have hfu : ⋃ i, f i = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    by_cases hp : p ∈ U
    · obtain ⟨C, hC, hpC⟩ := (hmaps hp).1.1
      exact Set.mem_iUnion.2 ⟨some ⟨C, hC⟩, subset_closure ⟨hp, hpC⟩⟩
    · exact Set.mem_iUnion.2 ⟨none, hp⟩
  have hd := dense_iUnion_interior_of_closed hfc hfu
  obtain ⟨p, hpU, hp⟩ := hd.inter_open_nonempty U hU ⟨z0, hz0⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
  cases i with
  | none => exact absurd hpU (interior_subset hi)
  | some C =>
    refine ⟨C, C.2, U ∩ interior (f (some C)), g, j, hU.inter isOpen_interior, ⟨p, hpU, hi⟩,
      fun z hz => ⟨⟨?_, (hmaps hz.1).1.2⟩, (hmaps hz.1).2⟩,
      han.mono Set.inter_subset_left, fun z hz => hinj z hz.1⟩
    have hz' : z ∈ closure (U ∩ g ⁻¹' (C : Set X)) := interior_subset hz.2
    have := mem_closure_image (hgc z hz.1) hz'
    have hsub : g '' (U ∩ g ⁻¹' (C : Set X)) ⊆ (C : Set X) := by
      rintro _ ⟨y, hy, rfl⟩; exact hy.2
    exact (hcl C C.2).closure_subset_iff.2 hsub this

/- English proof (translation)
Take `⟨χ, -, hwχ, κ, -, hWχ, hsec⟩` from `hsnc w`. Take `⟨a, ha, hχa⟩` from `((hWχ k).le ⟨hw, hwχ⟩).2`. Take `⟨-, u, -, -, heq⟩` from `hsec i`. Rewrite using `[heq w hwχ]`. Use `mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ k) ?_)` and prove the remaining obligations.

Simplify using `only [ha, hχa]`. Conclude with `zero_pow (by omega)`.
-/
theorem jointSNC_vanish {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {B : FinHolAtlas n Y} {μ : Y → X} {q r : ℕ} {L : Fin q → LocPot X} {t : Fin q → X → X → ℂ}
    {W : Fin r → Set Y} {e : Fin q → Fin r → ℕ} (hsnc : IsJointSNC B μ L t W e) {k : Fin r}
    {i : Fin q} (hik : 1 ≤ e i k) {w : Y} (hw : w ∈ W k) : t i (μ w) (μ w) = 0 := by
  obtain ⟨χ, -, hwχ, κ, -, hWχ, hsec⟩ := hsnc w
  obtain ⟨a, ha, hχa⟩ := ((hWχ k).le ⟨hw, hwχ⟩).2
  obtain ⟨-, u, -, -, heq⟩ := hsec i
  rw [heq w hwχ]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ k) ?_)
  simp only [ha, hχa]
  exact zero_pow (by omega)

/- English proof (translation)
Use `set j0 := chartIdx A (μ w) with hj0def`. Establish `hj0 : μ w ∈ (A.chart j0).source` using `Classical.choose_spec (A.cover (μ w))`. Use `set i0 := chartIdx B w`. Establish `hi0 : w ∈ (B.chart i0).source` using `Classical.choose_spec (B.cover w)`. Use `set F : (Fin (n' + 1) → ℂ) → (Fin d → ℂ) := fun z => A.chart j0 (μ (χ.symm z)) with hFdef`.

Use `set O : Set (Fin (n' + 1) → ℂ) := χ.target ∩ χ.symm ⁻¹' ((B.chart i0).source ∩ μ ⁻¹' (A.chart j0).source) with hOdef`. Establish `hO : IsOpen O` using `χ.isOpen_inter_preimage_symm ((B.chart i0).open_source.inter ((A.chart j0).open_source.preimage hμ.1))`. Establish `hp0 : χ w ∈ O` using `⟨χ.map_source hwχ, by simpa [χ.left_inv hwχ] using ⟨hi0, hj0⟩⟩`. Establish `hFA : AnalyticOnNhd ℂ F O`. Introduce `z hz`.

Establish `hq : AnalyticAt ℂ (B.chart i0 ∘ χ.symm) z` using `(hχ i0).2 z ⟨hz.1, hz.2.1⟩`. Establish `hh : AnalyticAt ℂ (A.chart j0 ∘ μ ∘ (B.chart i0).symm) ((B.chart i0 ∘ χ.symm) z)` using `hμ.2 i0 j0 _ ⟨(B.chart i0).map_source hz.2.1, by`. Simplify `hz.2.2⟩` using `[Set.mem_preimage, (B.chart i0).left_inv hz.2.1]`. Use `(hh.comp hq).congr ?_` and prove the remaining obligations. Use `filter_upwards [hO.mem_nhds hz] with z' hz'`.

Simplify using `[hFdef, (B.chart i0).left_inv hz'.2.1]`. Use `set K := LinearMap.ker (LinearMap.proj a : (Fin (n' + 1) → ℂ) →ₗ[ℂ] ℂ) with hKdef`. Establish `hK : Module.finrank ℂ K = n'`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (LinearMap.proj a : (Fin (n' + 1) → ℂ) →ₗ[ℂ] ℂ)`. Establish `h2 : LinearMap.range (LinearMap.proj a : (Fin (n' + 1) → ℂ) →ₗ[ℂ] ℂ) = ⊤` using `LinearMap.range_eq_top.2 fun c => ⟨Pi.single a c, by simp⟩`.

Rewrite `h1` using `[h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun]`. Rewrite using `[hKdef]`. Use linear arithmetic over natural numbers and integers. Set `eK : (Fin n' → ℂ) ≃ₗ[ℂ] K` to `LinearEquiv.ofFinrankEq _ _ (by rw [hK, Module.finrank_fin_fun])`. Set `ι : (Fin n' → ℂ) →L[ℂ] (Fin (n' + 1) → ℂ)` to `LinearMap.toContinuousLinearMap (K.subtype ∘ₗ eK.toLinearMap)`.

Establish `hιa : ∀ z, ι z a = 0` using `fun z => (eK z).2`. Establish `hwa : χ w a = 0` using `(hV.le ⟨hw, hwχ⟩).2`. Use `set G : (Fin n' → ℂ) → (Fin (n' + 1) → ℂ) := fun z => χ w + ι z with hGdef`. Establish `hGc : Continuous G` using `continuous_const.add ι.continuous`. Establish `hGA : ∀ z, AnalyticAt ℂ G z` using `fun z => analyticAt_const.add (ι.analyticAt z)`.

Establish `hGd : ∀ z, fderiv ℂ G z = ι` using `fun z => by`. Rewrite using `[hGdef, fderiv_const_add, ContinuousLinearMap.fderiv]`. Use `set U0 := G ⁻¹' O with hU0def`. Establish `hU0 : IsOpen U0` using `hO.preimage hGc`. Establish `hFGA : AnalyticOnNhd ℂ (F ∘ G) U0` using `fun z hz => (hFA (G z) hz).comp (hGA z)`.

Establish `hDc : ContinuousOn (fderiv ℂ (F ∘ G)) U0` using `hFGA.fderiv.continuousOn`. Establish `hD : ∀ z ∈ U0, fderiv ℂ (F ∘ G) z = (fderiv ℂ F (G z)).comp ι` using `fun z hz => by`. Rewrite using `[fderiv_comp z ((hFA (G z) hz).differentiableAt) (hGA z).differentiableAt, hGd]`. Establish `hG0 : G 0 = χ w` using `by simp [hGdef]`. Establish `h0U0 : (0 : Fin n' → ℂ) ∈ U0` using `by simp only [hU0def, Set.mem_preimage, hG0]; exact hp0`.

Establish `hinjK : Function.Injective (((fderiv ℂ F (χ w) : (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) : (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp K.subtype)`. Rewrite using `[← LinearMap.ker_eq_bot]`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (((fderiv ℂ F (χ w) : (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) : (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp K.subtype)`. Rewrite `h1` using `[hK]`. Establish `h2 : Module.finrank ℂ (LinearMap.ker (((fderiv ℂ F (χ w) : (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) : (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp K.subtype)) = 0`.

Use `hrank` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `Submodule.finrank_eq_zero.1 h2`. Establish `hinj0 : Function.Injective (fderiv ℂ (F ∘ G) 0)`. Rewrite using `[hD 0 h0U0, hG0]`.

Establish `: ⇑((fderiv ℂ F (χ w)).comp ι) = (((fderiv ℂ F (χ w) : (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) : (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp K.subtype) ∘ eK`. Use function extensionality and compare the values at `z`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hinjK.comp eK.injective`.

Use `set U := U0 ∩ (fderiv ℂ (F ∘ G)) ⁻¹' {L | Function.Injective L} with hUdef`. Establish `hU : IsOpen U` using `hDc.isOpen_inter_preimage hU0 ContinuousLinearMap.isOpen_injective`. Use `⟨U, fun z => μ (χ.symm (G z)), j0, hU, ⟨0, h0U0, hinj0⟩, fun z hz => ⟨?_, hz.1.2.2⟩, fun z hz => hFGA z hz.1, fun z hz => hz.2⟩` and prove the remaining obligations. Apply `hVT` to reduce the goal to its premises. Establish `hGz : G z ∈ χ.target` using `hz.1.1`.

Use `(hV.ge ⟨χ.map_target hGz, ?_⟩).1` and prove the remaining obligations. Rewrite using `[χ.right_inv hGz]`. Simplify using `[hGdef, hwa, hιa]`.
-/
theorem hasHoloImm_of_rank {d n' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas d X) (B : FinHolAtlas (n' + 1) Y) (μ : Y → X) (hμ : HoloMap B A μ)
    (V : Set Y) (T : Set X) (hVT : ∀ w' ∈ V, μ w' ∈ T) (w : Y)
    (χ : OpenPartialHomeomorph Y (Fin (n' + 1) → ℂ)) (a : Fin (n' + 1)) (hχ : IsCompatChart B χ)
    (hw : w ∈ V) (hwχ : w ∈ χ.source) (hV : V ∩ χ.source = {w' ∈ χ.source | χ w' a = 0})
    (hrank : n' ≤ Module.finrank ℂ (LinearMap.range
      (((fderiv ℂ (fun z => A.chart (chartIdx A (μ w)) (μ (χ.symm z))) (χ w) :
          (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) : (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp
        (LinearMap.ker (LinearMap.proj a : (Fin (n' + 1) → ℂ) →ₗ[ℂ] ℂ)).subtype))) :
    HasHoloImm A T n' := by
  set j0 := chartIdx A (μ w) with hj0def
  have hj0 : μ w ∈ (A.chart j0).source := Classical.choose_spec (A.cover (μ w))
  set i0 := chartIdx B w
  have hi0 : w ∈ (B.chart i0).source := Classical.choose_spec (B.cover w)
  set F : (Fin (n' + 1) → ℂ) → (Fin d → ℂ) := fun z => A.chart j0 (μ (χ.symm z)) with hFdef
  set O : Set (Fin (n' + 1) → ℂ) :=
    χ.target ∩ χ.symm ⁻¹' ((B.chart i0).source ∩ μ ⁻¹' (A.chart j0).source) with hOdef
  have hO : IsOpen O := χ.isOpen_inter_preimage_symm
    ((B.chart i0).open_source.inter ((A.chart j0).open_source.preimage hμ.1))
  have hp0 : χ w ∈ O := ⟨χ.map_source hwχ, by simpa [χ.left_inv hwχ] using ⟨hi0, hj0⟩⟩
  have hFA : AnalyticOnNhd ℂ F O := by
    intro z hz
    have hq : AnalyticAt ℂ (B.chart i0 ∘ χ.symm) z := (hχ i0).2 z ⟨hz.1, hz.2.1⟩
    have hh : AnalyticAt ℂ (A.chart j0 ∘ μ ∘ (B.chart i0).symm) ((B.chart i0 ∘ χ.symm) z) :=
      hμ.2 i0 j0 _ ⟨(B.chart i0).map_source hz.2.1, by
        simpa [Set.mem_preimage, (B.chart i0).left_inv hz.2.1] using hz.2.2⟩
    refine (hh.comp hq).congr ?_
    filter_upwards [hO.mem_nhds hz] with z' hz'
    simp [hFdef, (B.chart i0).left_inv hz'.2.1]

  set K := LinearMap.ker (LinearMap.proj a : (Fin (n' + 1) → ℂ) →ₗ[ℂ] ℂ) with hKdef
  have hK : Module.finrank ℂ K = n' := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj a : (Fin (n' + 1) → ℂ) →ₗ[ℂ] ℂ)
    have h2 : LinearMap.range (LinearMap.proj a : (Fin (n' + 1) → ℂ) →ₗ[ℂ] ℂ) = ⊤ :=
      LinearMap.range_eq_top.2 fun c => ⟨Pi.single a c, by simp⟩
    rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
    rw [hKdef]; omega
  let eK : (Fin n' → ℂ) ≃ₗ[ℂ] K := LinearEquiv.ofFinrankEq _ _ (by rw [hK, Module.finrank_fin_fun])
  let ι : (Fin n' → ℂ) →L[ℂ] (Fin (n' + 1) → ℂ) :=
    LinearMap.toContinuousLinearMap (K.subtype ∘ₗ eK.toLinearMap)
  have hιa : ∀ z, ι z a = 0 := fun z => (eK z).2
  have hwa : χ w a = 0 := (hV.le ⟨hw, hwχ⟩).2
  set G : (Fin n' → ℂ) → (Fin (n' + 1) → ℂ) := fun z => χ w + ι z with hGdef
  have hGc : Continuous G := continuous_const.add ι.continuous
  have hGA : ∀ z, AnalyticAt ℂ G z := fun z => analyticAt_const.add (ι.analyticAt z)
  have hGd : ∀ z, fderiv ℂ G z = ι := fun z => by
    rw [hGdef, fderiv_const_add, ContinuousLinearMap.fderiv]
  set U0 := G ⁻¹' O with hU0def
  have hU0 : IsOpen U0 := hO.preimage hGc
  have hFGA : AnalyticOnNhd ℂ (F ∘ G) U0 := fun z hz => (hFA (G z) hz).comp (hGA z)
  have hDc : ContinuousOn (fderiv ℂ (F ∘ G)) U0 := hFGA.fderiv.continuousOn
  have hD : ∀ z ∈ U0, fderiv ℂ (F ∘ G) z = (fderiv ℂ F (G z)).comp ι := fun z hz => by
    rw [fderiv_comp z ((hFA (G z) hz).differentiableAt) (hGA z).differentiableAt, hGd]

  have hG0 : G 0 = χ w := by simp [hGdef]
  have h0U0 : (0 : Fin n' → ℂ) ∈ U0 := by simp only [hU0def, Set.mem_preimage, hG0]; exact hp0
  have hinjK : Function.Injective
      (((fderiv ℂ F (χ w) : (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) :
        (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp K.subtype) := by
    rw [← LinearMap.ker_eq_bot]
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (((fderiv ℂ F (χ w) : (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) :
        (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp K.subtype)
    rw [hK] at h1
    have h2 : Module.finrank ℂ (LinearMap.ker (((fderiv ℂ F (χ w) :
        (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) : (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp
        K.subtype)) = 0 := by
      have := hrank
      omega
    exact Submodule.finrank_eq_zero.1 h2
  have hinj0 : Function.Injective (fderiv ℂ (F ∘ G) 0) := by
    rw [hD 0 h0U0, hG0]
    have : ⇑((fderiv ℂ F (χ w)).comp ι) = (((fderiv ℂ F (χ w) : (Fin (n' + 1) → ℂ) →L[ℂ] (Fin d → ℂ)) :
        (Fin (n' + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp K.subtype) ∘ eK := by
      funext z; rfl
    rw [this]
    exact hinjK.comp eK.injective

  set U := U0 ∩ (fderiv ℂ (F ∘ G)) ⁻¹' {L | Function.Injective L} with hUdef
  have hU : IsOpen U := hDc.isOpen_inter_preimage hU0 ContinuousLinearMap.isOpen_injective
  refine ⟨U, fun z => μ (χ.symm (G z)), j0, hU, ⟨0, h0U0, hinj0⟩, fun z hz => ⟨?_, hz.1.2.2⟩,
    fun z hz => hFGA z hz.1, fun z hz => hz.2⟩
  apply hVT
  have hGz : G z ∈ χ.target := hz.1.1
  refine (hV.ge ⟨χ.map_target hGz, ?_⟩).1
  rw [χ.right_inv hGz]
  simp [hGdef, hwa, hιa]

end

end GlobalTheory.LogResInt
