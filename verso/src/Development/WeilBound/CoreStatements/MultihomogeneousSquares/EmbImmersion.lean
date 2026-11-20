import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.WeilBound.CoreStatements.CentralCharts.PotLoc

noncomputable section

namespace SquareStatements

open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

/- English proof (translation)
Introduce `j t ht`. Take `⟨k, hk⟩` from `B.cover (ψ ((A.chart j).symm t))`. Establish `hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source))` using `(A.chart j).isOpen_inter_preimage_symm ((B.chart k).open_source.preimage hψ.1)`. Establish `hm : t ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source)` using `⟨ht.1, hk⟩`. Establish `hgk : AnalyticAt ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) t` using `hψ.2 j k t hm`.

Establish `hF : AnalyticAt ℂ (g ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) t)`. Use `hg k _ ⟨(B.chart k).map_source hk, ?_⟩` and prove the remaining obligations. Use `show (B.chart k).symm (B.chart k (ψ ((A.chart j).symm t))) ∈ V`. Rewrite using `[(B.chart k).left_inv hk]`. Conclude with `ht.2`.

Use `(hF.comp hgk).congr ?_` and prove the remaining obligations. Use `filter_upwards [hO.mem_nhds hm] with u hu`. Simplify using `only [Function.comp_apply, (B.chart k).left_inv hu.2]`.
-/
theorem emb_holoOn {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X)
    (B : FinHolAtlas e Y) (ψ : X → Y) (hψ : HoloMap A B ψ) (V : Set Y) (g : Y → ℂ) (hg : B.HoloOn V g) :
    A.HoloOn (ψ ⁻¹' V) (g ∘ ψ) := by
  intro j t ht
  obtain ⟨k, hk⟩ := B.cover (ψ ((A.chart j).symm t))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source)) :=
    (A.chart j).isOpen_inter_preimage_symm ((B.chart k).open_source.preimage hψ.1)
  have hm : t ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source) := ⟨ht.1, hk⟩
  have hgk : AnalyticAt ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) t := hψ.2 j k t hm
  have hF : AnalyticAt ℂ (g ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) t) := by
    refine hg k _ ⟨(B.chart k).map_source hk, ?_⟩
    show (B.chart k).symm (B.chart k (ψ ((A.chart j).symm t))) ∈ V
    rw [(B.chart k).left_inv hk]
    exact ht.2
  refine (hF.comp hgk).congr ?_
  filter_upwards [hO.mem_nhds hm] with u hu
  simp only [Function.comp_apply, (B.chart k).left_inv hu.2]

/- English proof (translation)
Establish `hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source))` using `(A.chart j).isOpen_inter_preimage_symm ((B.chart k).open_source.preimage hψ.1)`. Establish `hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source)`. Use `⟨(A.chart j).map_source hx, ?_⟩` and prove the remaining obligations. Use `show ψ ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source`. Rewrite using `[(A.chart j).left_inv hx]`.

Conclude with `hk`. Establish `hg : AnalyticAt ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)` using `hψ.2 j k _ hm`. Establish `hgt : (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x) = B.chart k (ψ x)`. Simplify using `only [Function.comp_apply, (A.chart j).left_inv hx]`. Establish `hh : AnalyticAt ℂ (A.chart j ∘ π ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))`.

Rewrite using `[hgt]`. Use `hπ.2 k j _ ⟨(B.chart k).map_source hk, ?_⟩` and prove the remaining obligations. Use `show π ((B.chart k).symm (B.chart k (ψ x))) ∈ (A.chart j).source`. Rewrite using `[(B.chart k).left_inv hk, h1]`. Conclude with `hx`.

Establish `hid : (A.chart j ∘ π ∘ (B.chart k).symm) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j x)] id` using `by filter_upwards [hO.mem_nhds hm] with u hu`. Simplify using `only [Function.comp_apply, id, (B.chart k).left_inv hu.2, h1, (A.chart j).right_inv hu.1]`. Establish `hfg : (fun y => f (ψ ((A.chart j).symm y))) =ᶠ[𝓝 (A.chart j x)] (fun y => f ((B.chart k).symm y)) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm)` using `by filter_upwards [hO.mem_nhds hm] with u hu`. Simplify using `only [Function.comp_apply, (B.chart k).left_inv hu.2]`. Establish `hcomp : (fderiv ℂ (A.chart j ∘ π ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).comp (fderiv ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)) = ContinuousLinearMap.id ℂ _`.

Rewrite using `[← fderiv_comp _ hh.differentiableAt hg.differentiableAt, hid.fderiv_eq, fderiv_id]`. Rewrite `hf` using `[← hgt]`. Rewrite using `[hfg.fderiv_eq, eq_bot_iff]`. Introduce `v hv`. Establish `hv' : fderiv ℂ ((fun y => f ((B.chart k).symm y)) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm)) (A.chart j x) v = 0` using `hv`.

Rewrite using `[Submodule.mem_bot]`. Distinguish the cases in `hF : DifferentiableAt ℂ (fun y => f ((B.chart k).symm y)) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))`. Rewrite `hv'` using `[fderiv_comp _ hF hg.differentiableAt]`. Establish `h0 : fderiv ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x) v ∈ (fderiv ℂ (fun y => f ((B.chart k).symm y)) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).ker` using `hv'`. Rewrite `h0` using `[hf, Submodule.mem_bot]`.

Use `congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) hcomp` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply, h0, map_zero, ContinuousLinearMap.id_apply] at this`. Conclude with `this.symm`. Establish `h0 : v ∈ (fderiv ℂ (fun y => f ((B.chart k).symm y)) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).ker`. Establish `: fderiv ℂ (fun y => f ((B.chart k).symm y)) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)) v = 0`.

Rewrite using `[fderiv_zero_of_not_differentiableAt hF]`. Both sides reduce to the same expression. Conclude with `this`. Rewrite `h0` using `[hf, Submodule.mem_bot]`. Conclude with `h0`.
-/
theorem emb_immersion {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (ψ : X → Y) (π : Y → X)
    (hψ : HoloMap A B ψ) (hπ : HoloMap B A π) (h1 : ∀ x, π (ψ x) = x) (f : Y → W) (x : X) (j : Fin A.n)
    (k : Fin B.n) (hx : x ∈ (A.chart j).source) (hk : ψ x ∈ (B.chart k).source)
    (hf : (fderiv ℂ (fun y => f ((B.chart k).symm y)) (B.chart k (ψ x))).ker = ⊥) :
    (fderiv ℂ (fun y => f (ψ ((A.chart j).symm y))) (A.chart j x)).ker = ⊥ := by
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source)) :=
    (A.chart j).isOpen_inter_preimage_symm ((B.chart k).open_source.preimage hψ.1)
  have hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ ⁻¹' (B.chart k).source) := by
    refine ⟨(A.chart j).map_source hx, ?_⟩
    show ψ ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
    rw [(A.chart j).left_inv hx]
    exact hk
  have hg : AnalyticAt ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x) := hψ.2 j k _ hm
  have hgt : (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x) = B.chart k (ψ x) := by
    simp only [Function.comp_apply, (A.chart j).left_inv hx]
  have hh : AnalyticAt ℂ (A.chart j ∘ π ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)) := by
    rw [hgt]
    refine hπ.2 k j _ ⟨(B.chart k).map_source hk, ?_⟩
    show π ((B.chart k).symm (B.chart k (ψ x))) ∈ (A.chart j).source
    rw [(B.chart k).left_inv hk, h1]
    exact hx
  have hid : (A.chart j ∘ π ∘ (B.chart k).symm) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j x)] id := by
    filter_upwards [hO.mem_nhds hm] with u hu
    simp only [Function.comp_apply, id, (B.chart k).left_inv hu.2, h1, (A.chart j).right_inv hu.1]
  have hfg : (fun y => f (ψ ((A.chart j).symm y))) =ᶠ[𝓝 (A.chart j x)]
      (fun y => f ((B.chart k).symm y)) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm) := by
    filter_upwards [hO.mem_nhds hm] with u hu
    simp only [Function.comp_apply, (B.chart k).left_inv hu.2]
  have hcomp : (fderiv ℂ (A.chart j ∘ π ∘ (B.chart k).symm) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).comp
      (fderiv ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)) = ContinuousLinearMap.id ℂ _ := by
    rw [← fderiv_comp _ hh.differentiableAt hg.differentiableAt, hid.fderiv_eq, fderiv_id]
  rw [← hgt] at hf
  rw [hfg.fderiv_eq, eq_bot_iff]
  intro v hv
  have hv' : fderiv ℂ ((fun y => f ((B.chart k).symm y)) ∘ (B.chart k ∘ ψ ∘ (A.chart j).symm)) (A.chart j x) v = 0 :=
    hv
  rw [Submodule.mem_bot]
  by_cases hF : DifferentiableAt ℂ (fun y => f ((B.chart k).symm y))
      ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))
  · rw [fderiv_comp _ hF hg.differentiableAt] at hv'
    have h0 : fderiv ℂ (B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x) v ∈
        (fderiv ℂ (fun y => f ((B.chart k).symm y)) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).ker :=
      hv'
    rw [hf, Submodule.mem_bot] at h0
    have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) hcomp
    simp only [ContinuousLinearMap.comp_apply, h0, map_zero, ContinuousLinearMap.id_apply] at this
    exact this.symm
  · have h0 : v ∈ (fderiv ℂ (fun y => f ((B.chart k).symm y))
        ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x))).ker := by
      have : fderiv ℂ (fun y => f ((B.chart k).symm y)) ((B.chart k ∘ ψ ∘ (A.chart j).symm) (A.chart j x)) v = 0 := by
        rw [fderiv_zero_of_not_differentiableAt hF]
        rfl
      exact this
    rw [hf, Submodule.mem_bot] at h0
    exact h0

/- English proof (translation)
Introduce `K _ ι _ P e σ S Re β b hJ hdeg hbr hβ hβP hbd`. Establish `hd` using `Re.degree`. Rewrite `hd` using `[hdeg, hbr]`. Establish `hbij : Function.Bijective Re.π`. Use `⟨fun x y hxy => ?_, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `Set.ncard_eq_one.1 (hd.2.2.2.2.1 (Re.π x) (by simp))`. Establish `hx : x ∈ Re.π ⁻¹' {Re.π x}` using `rfl`. Establish `hy : y ∈ Re.π ⁻¹' {Re.π x}` using `hxy.symm`. Rewrite `hx`, `hy` using `[ha]`. Conclude with `hx.trans hy.symm`.

Take `⟨a, ha⟩` from `Set.ncard_eq_one.1 (hd.2.2.2.2.1 x (by simp))`. Establish `: a ∈ Re.π ⁻¹' {x}` using `by rw [ha]; rfl`. Conclude with `⟨a, this⟩`. Take `⟨ψ, hψ, h1, h2⟩` from `AnalyticReference.exists_inv S.A Re.R.A Re.π ∅ Re.holo hd hbij`. Establish `hmc : ∀ z, z ∉ mcPts Re.J`.

Introduce `z hz`. Rewrite `hz` using `[hJ]`. Use `hz.2 1 Submodule.mem_top` as an intermediate fact. Simplify using `at this`. Establish `hI : imageZ (id : (Σ k, ι k) → Σ k, ι k) P = P`.

Use extensionality with `f`. Simplify using `[imageZ]`. Use `⟨K, inferInstance, ι, inferInstance, id, id, fun x => ψ ⁻¹' Re.R.U (ψ x), fun x y => Re.R.lift (ψ x) (ψ y), β, b, ⟨Function.injective_id, Function.injective_id, fun _ => rfl, fun q _ => ⟨q, rfl⟩⟩, ⟨fun x => (Re.R.isOpen_U _).preimage hψ.1, fun x => Re.R.mem_U (ψ x), fun x p => em …` and prove the remaining obligations. Introduce `x y hy`. Rewrite using `[hI]`.

Conclude with `Re.R.mem (ψ x) (ψ y) hy`. Introduce `x x' y hy`. Conclude with `Re.R.compat (ψ x) (ψ x') (ψ y) hy`. Introduce `z hz`. Rewrite `hz` using `[hI]`.

Take `⟨x', hx'⟩` from `Re.R.surj z hz (hmc z)`. Use `⟨Re.π x', ?_⟩` and prove the remaining obligations. Use `show SameOrbit (Re.R.lift (ψ (Re.π x')) (ψ (Re.π x'))) z`. Rewrite using `[h2]`. Conclude with `hx'`.

Introduce `x x' h`. Use `Re.R.inj (ψ x) (ψ x') (hmc _) h` as an intermediate fact. Rewrite using `[← h1 x, ← h1 x', this]`. Introduce `x p hp j hj`. Take `⟨k, hk⟩` from `Re.R.A.cover (ψ x)`.

Conclude with `emb_immersion S.A Re.R.A ψ Re.π hψ Re.holo h1 (fun u => affCoord p (Re.R.lift (ψ x) u)) x j k hj hk (Re.R.immersion (ψ x) (hmc _) p hp k hk)`. Introduce `x show SameOrbit (Re.R.lift (ψ (Re.π x)) (ψ (Re.π x))) fun p => Re.R.lift x x p`. Rewrite using `[h2]`. Conclude with `⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩`. Rewrite using `[hI]`.

Conclude with `hβP`. Introduce `x hx`. Conclude with `hbd (ψ x) (by rw [h1]; exact hx)`.
-/
theorem stEmb : StEmb := by
  intro K _ ι _ P e σ S Re β b hJ hdeg hbr hβ hβP hbd
  have hd := Re.degree
  rw [hdeg, hbr] at hd
  have hbij : Function.Bijective Re.π := by
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 (Re.π x) (by simp))
      have hx : x ∈ Re.π ⁻¹' {Re.π x} := rfl
      have hy : y ∈ Re.π ⁻¹' {Re.π x} := hxy.symm
      rw [ha] at hx hy
      exact hx.trans hy.symm
    · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 x (by simp))
      have : a ∈ Re.π ⁻¹' {x} := by rw [ha]; rfl
      exact ⟨a, this⟩
  obtain ⟨ψ, hψ, h1, h2⟩ := AnalyticReference.exists_inv S.A Re.R.A Re.π ∅ Re.holo hd hbij
  have hmc : ∀ z, z ∉ mcPts Re.J := by
    intro z hz
    rw [hJ] at hz
    have := hz.2 1 Submodule.mem_top
    simp at this
  have hI : imageZ (id : (Σ k, ι k) → Σ k, ι k) P = P := by
    ext f
    simp [imageZ]
  refine ⟨K, inferInstance, ι, inferInstance, id, id, fun x => ψ ⁻¹' Re.R.U (ψ x),
    fun x y => Re.R.lift (ψ x) (ψ y), β, b,
    ⟨Function.injective_id, Function.injective_id, fun _ => rfl, fun q _ => ⟨q, rfl⟩⟩,
    ⟨fun x => (Re.R.isOpen_U _).preimage hψ.1, fun x => Re.R.mem_U (ψ x),
      fun x p => emb_holoOn S.A Re.R.A ψ hψ _ _ (Re.R.holo (ψ x) p), ?_, ?_, ?_, ?_, ?_⟩, ?_, hβ, ?_, ?_⟩
  · intro x y hy
    rw [hI]
    exact Re.R.mem (ψ x) (ψ y) hy
  · intro x x' y hy
    exact Re.R.compat (ψ x) (ψ x') (ψ y) hy
  · intro z hz
    rw [hI] at hz
    obtain ⟨x', hx'⟩ := Re.R.surj z hz (hmc z)
    refine ⟨Re.π x', ?_⟩
    show SameOrbit (Re.R.lift (ψ (Re.π x')) (ψ (Re.π x'))) z
    rw [h2]
    exact hx'
  · intro x x' h
    have := Re.R.inj (ψ x) (ψ x') (hmc _) h
    rw [← h1 x, ← h1 x', this]
  · intro x p hp j hj
    obtain ⟨k, hk⟩ := Re.R.A.cover (ψ x)
    exact emb_immersion S.A Re.R.A ψ Re.π hψ Re.holo h1 (fun u => affCoord p (Re.R.lift (ψ x) u)) x j k hj hk
      (Re.R.immersion (ψ x) (hmc _) p hp k hk)
  · intro x
    show SameOrbit (Re.R.lift (ψ (Re.π x)) (ψ (Re.π x))) fun p => Re.R.lift x x p
    rw [h2]
    exact ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩
  · rw [hI]
    exact hβP
  · intro x hx
    exact hbd (ψ x) (by rw [h1]; exact hx)

end SquareStatements
