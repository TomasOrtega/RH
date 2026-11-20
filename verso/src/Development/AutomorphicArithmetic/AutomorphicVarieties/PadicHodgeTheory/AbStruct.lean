import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import GroundTheory.LocalFields.PrincipalUnitsRank
import GroundTheory.LocalFields.MainTheorem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalClassFieldTheoryOfOpenEmbedding
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalFieldUnitsStructureTheorem

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Establish `hnb : ∀ a : A, (Filter.comap θ (𝓝 a)).NeBot` using `fun a => Filter.comap_neBot fun t ht => by`. Take `⟨_, hx, y, rfl⟩` from `mem_closure_iff_nhds.1 (hd a) t ht`. Conclude with `⟨y, hx⟩`. Establish `hbasis : ∀ W ∈ 𝓝 (1 : B), ∃ U : OpenNormalSubgroup B, (U.toSubgroup : Set B) ⊆ W`. Introduce `W hW`.

Take `⟨O, hOW, hO, h1⟩` from `mem_nhds_iff.1 hW`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1`. Conclude with `⟨U, fun x hx => hOW (hU hx)⟩`. Establish `hV : ∀ U : OpenNormalSubgroup B, ∃ V : Subgroup A, IsOpen (V : Set A) ∧ V.comap θ = U.toSubgroup.comap f`. Introduce `U`.

Apply `hE` to reduce the goal to its premises. Conclude with `U.toOpenSubgroup.isOpen.preimage hf`. Set `g : M →* B ⧸ U.toSubgroup` to `(QuotientGroup.mk' _).comp f`. Establish `hker : U.toSubgroup.comap f = g.ker`. Use extensionality with `x`.

Simplify using `[g, QuotientGroup.eq_one_iff]`. Rewrite using `[hker]`. Use `infer_instance`. Use `choose V hVo hVc using hV`. Establish `hmem : ∀ U y, θ y ∈ V U ↔ f y ∈ U.toSubgroup`.

Introduce `U y`. Use `SetLike.ext_iff.1 (hVc U) y` as an intermediate fact. Simplify using `using this`. Establish `hUc : ∀ U : OpenNormalSubgroup B, IsClosed (U.toSubgroup : Set B)` using `fun U => U.toOpenSubgroup.isClosed`. Establish `htend : ∀ (F : Filter M) (b : B), (∀ U : OpenNormalSubgroup B, ∀ᶠ y in F, b⁻¹ * f y ∈ U.toSubgroup) → Filter.Tendsto f F (𝓝 b)`.

Introduce `F b h W hW`. Establish `hW' : (fun x => b * x) ⁻¹' W ∈ 𝓝 (1 : B)` using `(continuous_mul_left b).continuousAt.preimage_mem_nhds (by simpa using hW)`. Take `⟨U, hU⟩` from `hbasis _ hW'`. Use `Filter.mem_map.2 ?_` and prove the remaining obligations. Use `filter_upwards [h U] with y hy`.

Simplify using `using hU hy`. Establish `hNo : ∀ (a : A) U, IsOpen ((fun x => a⁻¹ * x) ⁻¹' (V U : Set A))` using `fun a U => (hVo U).preimage (continuous_mul_left a⁻¹)`. Establish `hNa : ∀ (a : A) U, a ∈ (fun x => a⁻¹ * x) ⁻¹' (V U : Set A)`. Introduce `a U`. Simplify using `[one_mem]`.

Establish `hlim : ∀ a : A, ∃ b : B, Filter.Tendsto f (Filter.comap θ (𝓝 a)) (𝓝 b)`. Introduce `a`. Use `haveI := hnb a`. Take `⟨b, -, hb⟩` from `isCompact_univ.exists_clusterPt (f := Filter.map f (Filter.comap θ (𝓝 a))) (Filter.le_principal_iff.2 Filter.univ_mem)`. Use `⟨b, htend _ _ fun U => ?_⟩` and prove the remaining obligations.

Take `⟨y0, hy0⟩` from `hd.exists_mem_open (hNo a U) ⟨a, hNa a U⟩`. Establish `hev : ∀ᶠ y in Filter.comap θ (𝓝 a), (f y0)⁻¹ * f y ∈ U.toSubgroup` using `by filter_upwards [Filter.preimage_mem_comap ((hNo a U).mem_nhds (hNa a U))] with y hy`. Establish `h1 : θ (y0⁻¹ * y) ∈ V U`. Use `(V U).mul_mem ((V U).inv_mem hy0) hy` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Rewrite `h1` using `[hmem]`. Simplify using `using h1`. Establish `hbC : (f y0)⁻¹ * b ∈ U.toSubgroup`. Establish `hC : IsClosed ((fun x => (f y0)⁻¹ * x) ⁻¹' (U.toSubgroup : Set B))` using `(hUc U).preimage (continuous_mul_left _)`. Conclude with `hC.closure_subset (hb.mem_closure_of_mem (s := (fun x => (f y0)⁻¹ * x) ⁻¹' (U.toSubgroup : Set B)) hev)`.

Use `filter_upwards [hev] with y hy`. Use `U.toSubgroup.mul_mem (U.toSubgroup.inv_mem hbC) hy` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Use `choose F0 hF using hlim`. Establish `hθ : ∀ y, F0 (θ y) = f y`.

Introduce `y`. Use `haveI := hnb (θ y)`. Use `tendsto_nhds_unique (hF (θ y)) (htend _ _ fun U => ?_)` and prove the remaining obligations. Use `filter_upwards [Filter.preimage_mem_comap ((hNo (θ y) U).mem_nhds (hNa (θ y) U))] with z hz`. Establish `h1 : θ (y⁻¹ * z) ∈ V U` using `by simpa using hz`.

Rewrite `h1` using `[hmem]`. Simplify using `using h1`. Establish `hmul : ∀ a b, F0 (a * b) = F0 a * F0 b`. Introduce `a b`. Use `haveI := hnb a`.

Use `haveI := hnb b`. Establish `hP : Filter.Tendsto (fun p : M × M => p.1 * p.2) (Filter.comap θ (𝓝 a) ×ˢ Filter.comap θ (𝓝 b)) (Filter.comap θ (𝓝 (a * b)))`. Rewrite using `[Filter.tendsto_comap_iff]`. Establish `: Filter.Tendsto (fun p : M × M => θ p.1 * θ p.2) (Filter.comap θ (𝓝 a) ×ˢ Filter.comap θ (𝓝 b)) (𝓝 (a * b))` using `(Filter.tendsto_comap.comp Filter.tendsto_fst).mul (Filter.tendsto_comap.comp Filter.tendsto_snd)`. Simplify `this` using `[Function.comp_def]`.

Establish `h1` using `(hF (a * b)).comp hP`. Establish `h2 : Filter.Tendsto (fun p : M × M => f p.1 * f p.2) (Filter.comap θ (𝓝 a) ×ˢ Filter.comap θ (𝓝 b)) (𝓝 (F0 a * F0 b))` using `((hF a).comp Filter.tendsto_fst).mul ((hF b).comp Filter.tendsto_snd)`. Use `tendsto_nhds_unique h1 ?_` and prove the remaining obligations. Simplify `h2` using `[Function.comp_def]`. Set `F : A →* B` to `{ toFun := F0 map_one' := by simpa using hθ 1 map_mul' := hmul }`.

Use `⟨F, ?_, hθ⟩` and prove the remaining obligations. Use `continuous_of_continuousAt_one F ?_` and prove the remaining obligations. Introduce `W hW`. Rewrite `hW` using `[map_one]`. Take `⟨U, hU⟩` from `hbasis _ hW`.

Use `Filter.mem_map.2 (Filter.mem_of_superset ((hVo U).mem_nhds (one_mem _)) fun x hx => hU ?_)` and prove the remaining obligations. Establish `hev : ∀ᶠ y in Filter.comap θ (𝓝 x), f y ∈ U.toSubgroup` using `by filter_upwards [Filter.preimage_mem_comap ((hVo U).mem_nhds hx)] with y hy`. Conclude with `(hmem U y).1 hy`. Use `haveI := hnb x`. Conclude with `(hUc U).mem_of_tendsto (hF x) hev`.
-/
private theorem as_ext {M A B : Type} [CommGroup M] [TopologicalSpace M] [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] [T2Space A] [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B] (θ : M →* A) (hd : DenseRange θ)
    (hE : ∀ H : Subgroup M, IsOpen (H : Set M) → H.FiniteIndex →
      ∃ V : Subgroup A, IsOpen (V : Set A) ∧ V.comap θ = H)
    (f : M →* B) (hf : Continuous f) : ∃ F : A →* B, Continuous F ∧ ∀ y, F (θ y) = f y := by
  classical
  have hnb : ∀ a : A, (Filter.comap θ (𝓝 a)).NeBot := fun a =>
    Filter.comap_neBot fun t ht => by
      obtain ⟨_, hx, y, rfl⟩ := mem_closure_iff_nhds.1 (hd a) t ht
      exact ⟨y, hx⟩
  have hbasis : ∀ W ∈ 𝓝 (1 : B), ∃ U : OpenNormalSubgroup B, (U.toSubgroup : Set B) ⊆ W := by
    intro W hW
    obtain ⟨O, hOW, hO, h1⟩ := mem_nhds_iff.1 hW
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
    exact ⟨U, fun x hx => hOW (hU hx)⟩
  have hV : ∀ U : OpenNormalSubgroup B, ∃ V : Subgroup A, IsOpen (V : Set A) ∧
      V.comap θ = U.toSubgroup.comap f := by
    intro U
    apply hE
    · exact U.toOpenSubgroup.isOpen.preimage hf
    · let g : M →* B ⧸ U.toSubgroup := (QuotientGroup.mk' _).comp f
      have hker : U.toSubgroup.comap f = g.ker := by
        ext x
        simp [g, QuotientGroup.eq_one_iff]
      rw [hker]
      infer_instance
  choose V hVo hVc using hV
  have hmem : ∀ U y, θ y ∈ V U ↔ f y ∈ U.toSubgroup := by
    intro U y
    have := SetLike.ext_iff.1 (hVc U) y
    simpa using this
  have hUc : ∀ U : OpenNormalSubgroup B, IsClosed (U.toSubgroup : Set B) :=
    fun U => U.toOpenSubgroup.isClosed
  have htend : ∀ (F : Filter M) (b : B),
      (∀ U : OpenNormalSubgroup B, ∀ᶠ y in F, b⁻¹ * f y ∈ U.toSubgroup) → Filter.Tendsto f F (𝓝 b) := by
    intro F b h W hW
    have hW' : (fun x => b * x) ⁻¹' W ∈ 𝓝 (1 : B) :=
      (continuous_mul_left b).continuousAt.preimage_mem_nhds (by simpa using hW)
    obtain ⟨U, hU⟩ := hbasis _ hW'
    refine Filter.mem_map.2 ?_
    filter_upwards [h U] with y hy
    simpa using hU hy
  have hNo : ∀ (a : A) U, IsOpen ((fun x => a⁻¹ * x) ⁻¹' (V U : Set A)) :=
    fun a U => (hVo U).preimage (continuous_mul_left a⁻¹)
  have hNa : ∀ (a : A) U, a ∈ (fun x => a⁻¹ * x) ⁻¹' (V U : Set A) := by
    intro a U
    simp [one_mem]
  have hlim : ∀ a : A, ∃ b : B, Filter.Tendsto f (Filter.comap θ (𝓝 a)) (𝓝 b) := by
    intro a
    haveI := hnb a
    obtain ⟨b, -, hb⟩ := isCompact_univ.exists_clusterPt (f := Filter.map f (Filter.comap θ (𝓝 a)))
      (Filter.le_principal_iff.2 Filter.univ_mem)
    refine ⟨b, htend _ _ fun U => ?_⟩
    obtain ⟨y0, hy0⟩ := hd.exists_mem_open (hNo a U) ⟨a, hNa a U⟩
    have hev : ∀ᶠ y in Filter.comap θ (𝓝 a), (f y0)⁻¹ * f y ∈ U.toSubgroup := by
      filter_upwards [Filter.preimage_mem_comap ((hNo a U).mem_nhds (hNa a U))] with y hy
      have h1 : θ (y0⁻¹ * y) ∈ V U := by
        have := (V U).mul_mem ((V U).inv_mem hy0) hy
        simpa [mul_assoc] using this
      rw [hmem] at h1
      simpa using h1
    have hbC : (f y0)⁻¹ * b ∈ U.toSubgroup := by
      have hC : IsClosed ((fun x => (f y0)⁻¹ * x) ⁻¹' (U.toSubgroup : Set B)) :=
        (hUc U).preimage (continuous_mul_left _)
      exact hC.closure_subset (hb.mem_closure_of_mem (s := (fun x => (f y0)⁻¹ * x) ⁻¹' (U.toSubgroup : Set B)) hev)
    filter_upwards [hev] with y hy
    have := U.toSubgroup.mul_mem (U.toSubgroup.inv_mem hbC) hy
    simpa [mul_assoc] using this
  choose F0 hF using hlim
  have hθ : ∀ y, F0 (θ y) = f y := by
    intro y
    haveI := hnb (θ y)
    refine tendsto_nhds_unique (hF (θ y)) (htend _ _ fun U => ?_)
    filter_upwards [Filter.preimage_mem_comap ((hNo (θ y) U).mem_nhds (hNa (θ y) U))] with z hz
    have h1 : θ (y⁻¹ * z) ∈ V U := by simpa using hz
    rw [hmem] at h1
    simpa using h1
  have hmul : ∀ a b, F0 (a * b) = F0 a * F0 b := by
    intro a b
    haveI := hnb a
    haveI := hnb b
    have hP : Filter.Tendsto (fun p : M × M => p.1 * p.2)
        (Filter.comap θ (𝓝 a) ×ˢ Filter.comap θ (𝓝 b)) (Filter.comap θ (𝓝 (a * b))) := by
      rw [Filter.tendsto_comap_iff]
      have : Filter.Tendsto (fun p : M × M => θ p.1 * θ p.2)
          (Filter.comap θ (𝓝 a) ×ˢ Filter.comap θ (𝓝 b)) (𝓝 (a * b)) :=
        (Filter.tendsto_comap.comp Filter.tendsto_fst).mul (Filter.tendsto_comap.comp Filter.tendsto_snd)
      simpa [Function.comp_def] using this
    have h1 := (hF (a * b)).comp hP
    have h2 : Filter.Tendsto (fun p : M × M => f p.1 * f p.2)
        (Filter.comap θ (𝓝 a) ×ˢ Filter.comap θ (𝓝 b)) (𝓝 (F0 a * F0 b)) :=
      ((hF a).comp Filter.tendsto_fst).mul ((hF b).comp Filter.tendsto_snd)
    refine tendsto_nhds_unique h1 ?_
    simpa [Function.comp_def] using h2
  let F : A →* B :=
    { toFun := F0
      map_one' := by simpa using hθ 1
      map_mul' := hmul }
  refine ⟨F, ?_, hθ⟩
  refine continuous_of_continuousAt_one F ?_
  intro W hW
  rw [map_one] at hW
  obtain ⟨U, hU⟩ := hbasis _ hW
  refine Filter.mem_map.2 (Filter.mem_of_superset ((hVo U).mem_nhds (one_mem _)) fun x hx => hU ?_)
  have hev : ∀ᶠ y in Filter.comap θ (𝓝 x), f y ∈ U.toSubgroup := by
    filter_upwards [Filter.preimage_mem_comap ((hVo U).mem_nhds hx)] with y hy
    exact (hmem U y).1 hy
  haveI := hnb x
  exact (hUc U).mem_of_tendsto (hF x) hev

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Establish `hn : (fun y => x⁻¹ * y) ⁻¹' (f.ker : Set M) ∈ 𝓝 x`. Apply `(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Simplify using `using hf.mem_nhds (one_mem f.ker)`. Establish `hx : ∀ᶠ y in 𝓝 x, f x = f y` using `by filter_upwards [hn] with y hy`.

Establish `hy' : f (x⁻¹ * y) = 1` using `hy`. Rewrite `hy'` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `hy'`. Conclude with `continuousAt_const.congr hx`.
-/
private theorem as_cont {M B : Type} [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (f : M →* B) (hf : IsOpen (f.ker : Set M)) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hn : (fun y => x⁻¹ * y) ⁻¹' (f.ker : Set M) ∈ 𝓝 x := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using hf.mem_nhds (one_mem f.ker)
  have hx : ∀ᶠ y in 𝓝 x, f x = f y := by
    filter_upwards [hn] with y hy
    have hy' : f (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'
  exact continuousAt_const.congr hx

open GroundTheory.LocalField.Abstract in
/- English proof (translation)
Establish `hT : IsClosed (θ '' (v.ker : Set M))` using `(hv.image hc).isClosed`. Establish `hx' : x ∈ closure (θ '' (v.ker : Set M))`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `O hO`. Establish `hO1 : (fun z => x * z) ⁻¹' O ∈ 𝓝 (1 : A)` using `(continuous_mul_left x).continuousAt.preimage_mem_nhds (by simpa using hO)`.

Take `⟨O', hO'O, hO'o, h1O'⟩` from `mem_nhds_iff.1 hO1`. Take `⟨V, hVo, hVO⟩` from `hb O' hO'o h1O'`. Use `haveI : Finite (A ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo`. Establish `hNpos : 0 < V.index` using `Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)`. Set `Np : ℕ+` to `⟨V.index, hNpos⟩`.

Set `S : Set A` to `{a | ProfiniteInteger.proj Np (Multiplicative.toAdd (D a)) = 0}`. Establish `hSo : IsOpen S` using `(isOpen_discrete {(0 : ZMod (Np : ℕ))}).preimage ((ProfiniteInteger.continuous_proj Np).comp (continuous_toAdd.comp hD))`. Set `W` to `(fun z => x⁻¹ * z) ⁻¹' ((V : Set A) ∩ S)`. Establish `hWo : IsOpen W` using `(hVo.inter hSo).preimage (continuous_mul_left _)`. Establish `hxW : x ∈ W` using `by simp [W, S, one_mem]`.

Take `⟨y, hgV, hgS⟩` from `hd.exists_mem_open hWo ⟨x, hxW⟩`. Establish `hdiv : (V.index : ℤ) ∣ Multiplicative.toAdd (v y)`. Establish `hDy : D (θ y) = D (x⁻¹ * θ y)` using `by rw [map_mul, map_inv, hx, inv_one, one_mul]`. Establish `h1 : ProfiniteInteger.proj Np (Multiplicative.toAdd (D (x⁻¹ * θ y))) = 0` using `hgS`. Rewrite `h1` using `[← hDy, hDv, toAdd_ofAdd, map_intCast]`.

Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1`. Take `⟨k, hk⟩` from `hdiv`. Use `⟨θ (y * ϖ ^ (-((V.index : ℤ) * k))), ?_, ⟨_, ?_, rfl⟩⟩` and prove the remaining obligations. Establish `hin : x⁻¹ * θ (y * ϖ ^ (-((V.index : ℤ) * k))) ∈ V`. Rewrite using `[map_mul, map_zpow, ← mul_assoc]`.

Use `V.mul_mem hgV ?_` and prove the remaining obligations. Establish `hp : θ ϖ ^ V.index ∈ V` using `Subgroup.pow_index_mem V (θ ϖ)`. Establish `he : θ ϖ ^ (-((V.index : ℤ) * k)) = (θ ϖ ^ V.index) ^ (-k)`. Rewrite using `[← zpow_natCast, ← zpow_mul, neg_mul_eq_mul_neg]`. Rewrite using `[he]`.

Conclude with `V.zpow_mem hp _`. Use `hO'O (hVO hin)` as an intermediate fact. Simplify using `using this`. Rewrite using `[SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_zpow, hϖ]`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises.

Simplify using `[toAdd_zpow, hk]`. Take `⟨u, hu, hux⟩` from `hT.closure_subset hx'`. Conclude with `⟨u, (MonoidHom.mem_ker).1 hu, hux⟩`.
-/
private theorem as_ker {M A : Type} [CommGroup M] [TopologicalSpace M] [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] [T2Space A] (θ : M →* A) (hc : Continuous θ) (hd : DenseRange θ)
    (hb : ∀ O : Set A, IsOpen O → 1 ∈ O → ∃ V : Subgroup A, IsOpen (V : Set A) ∧ (V : Set A) ⊆ O)
    (v : M →* Multiplicative ℤ) (ϖ : M) (hϖ : v ϖ = .ofAdd 1) (hv : IsCompact (v.ker : Set M))
    (D : A →* Multiplicative ProfiniteInteger) (hD : Continuous D)
    (hDv : ∀ y, D (θ y) = .ofAdd (((v y).toAdd : ℤ) : ProfiniteInteger)) (x : A) (hx : D x = 1) :
    ∃ u, v u = 1 ∧ θ u = x := by
  classical
  have hT : IsClosed (θ '' (v.ker : Set M)) := (hv.image hc).isClosed
  have hx' : x ∈ closure (θ '' (v.ker : Set M)) := by
    rw [mem_closure_iff_nhds]
    intro O hO
    have hO1 : (fun z => x * z) ⁻¹' O ∈ 𝓝 (1 : A) :=
      (continuous_mul_left x).continuousAt.preimage_mem_nhds (by simpa using hO)
    obtain ⟨O', hO'O, hO'o, h1O'⟩ := mem_nhds_iff.1 hO1
    obtain ⟨V, hVo, hVO⟩ := hb O' hO'o h1O'
    haveI : Finite (A ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo
    have hNpos : 0 < V.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    let Np : ℕ+ := ⟨V.index, hNpos⟩
    let S : Set A := {a | ProfiniteInteger.proj Np (Multiplicative.toAdd (D a)) = 0}
    have hSo : IsOpen S := (isOpen_discrete {(0 : ZMod (Np : ℕ))}).preimage
      ((ProfiniteInteger.continuous_proj Np).comp (continuous_toAdd.comp hD))
    let W := (fun z => x⁻¹ * z) ⁻¹' ((V : Set A) ∩ S)
    have hWo : IsOpen W := (hVo.inter hSo).preimage (continuous_mul_left _)
    have hxW : x ∈ W := by simp [W, S, one_mem]
    obtain ⟨y, hgV, hgS⟩ := hd.exists_mem_open hWo ⟨x, hxW⟩
    have hdiv : (V.index : ℤ) ∣ Multiplicative.toAdd (v y) := by
      have hDy : D (θ y) = D (x⁻¹ * θ y) := by rw [map_mul, map_inv, hx, inv_one, one_mul]
      have h1 : ProfiniteInteger.proj Np (Multiplicative.toAdd (D (x⁻¹ * θ y))) = 0 := hgS
      rw [← hDy, hDv, toAdd_ofAdd, map_intCast] at h1
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨θ (y * ϖ ^ (-((V.index : ℤ) * k))), ?_, ⟨_, ?_, rfl⟩⟩
    · have hin : x⁻¹ * θ (y * ϖ ^ (-((V.index : ℤ) * k))) ∈ V := by
        rw [map_mul, map_zpow, ← mul_assoc]
        refine V.mul_mem hgV ?_
        have hp : θ ϖ ^ V.index ∈ V := Subgroup.pow_index_mem V (θ ϖ)
        have he : θ ϖ ^ (-((V.index : ℤ) * k)) = (θ ϖ ^ V.index) ^ (-k) := by
          rw [← zpow_natCast, ← zpow_mul, neg_mul_eq_mul_neg]
        rw [he]
        exact V.zpow_mem hp _
      have := hO'O (hVO hin)
      simpa using this
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_zpow, hϖ]
      apply Multiplicative.toAdd.injective
      simp [toAdd_zpow, hk]
  obtain ⟨u, hu, hux⟩ := hT.closure_subset hx'
  exact ⟨u, (MonoidHom.mem_ker).1 hu, hux⟩

/- English proof (translation)
Establish `: {a : ℤ_[l] | (l : ℤ_[l]) ^ n ∣ a} = ((IsLocalRing.maximalIdeal ℤ_[l]) ^ n : Ideal ℤ_[l])`. Use extensionality with `a`. Simplify using `[PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Rewrite using `[this]`. Conclude with `Ideal.isOpen_pow_of_isMaximal _ n`.
-/
private theorem as_open {l : ℕ} [Fact l.Prime] (n : ℕ) : IsOpen {a : ℤ_[l] | (l : ℤ_[l]) ^ n ∣ a} := by
  have : {a : ℤ_[l] | (l : ℤ_[l]) ^ n ∣ a} = ((IsLocalRing.maximalIdeal ℤ_[l]) ^ n : Ideal ℤ_[l]) := by
    ext a
    simp [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rw [this]
  exact Ideal.isOpen_pow_of_isMaximal _ n

open GroundTheory.LocalField.Abstract in
/- English proof (translation)
Use `haveI : T2Space M := T2Space.of_injective_continuous hi hc`. Take `⟨π, hπc, hπθ⟩` from `as_ext θ hd hE p hp`. Set `va : M →* Multiplicative ℤ_[l]` to `(AddMonoidHom.toMultiplicative (Int.castAddHom ℤ_[l])).comp v`. Establish `hva : Continuous va`. Use `as_cont va (Subgroup.isOpen_mono (fun y hy => ?_) hv')` and prove the remaining obligations.

Rewrite `hy`, the goal using `[MonoidHom.mem_ker]`. Simplify using `[va, hy]`. Take `⟨a, hac, haθ⟩` from `as_ext θ hd hE va hva`. Establish `htc : Continuous t` using `as_cont t ht`. Take `⟨mM, hmc, hmθ⟩` from `as_ext θ hd hE t htc`.

Establish `hθl : ∀ x : ↥(CommGroup.primaryComponent M l), (θ.comp (CommGroup.primaryComponent M l).subtype) x ∈ CommGroup.primaryComponent A l`. Introduce and unpack `⟨x, k, hk⟩`. Conclude with `⟨k, by simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]; rw [← map_pow, hk, map_one]⟩`. Set `θl : ↥(CommGroup.primaryComponent M l) →* ↥(CommGroup.primaryComponent A l)` to `(θ.comp (CommGroup.primaryComponent M l).subtype).codRestrict _ hθl`. Establish `hθlv : ∀ x, (θl x : A) = θ x` using `fun x => rfl`.

Set `m : A →* ↥(CommGroup.primaryComponent A l)` to `θl.comp mM`. Establish `hmker : IsOpen (m.ker : Set A)`. Establish `e0 : IsOpen (mM.ker : Set A)` using `(isOpen_discrete {(1 : ↥(CommGroup.primaryComponent M l))}).preimage hmc`. Use `Subgroup.isOpen_mono (fun x hx => ?_) e0` and prove the remaining obligations. Rewrite `hx`, the goal using `[MonoidHom.mem_ker]`.

Simplify using `[m, hx]`. Establish `hmθ' : ∀ y, m (θ y) = θl (t y)` using `fun y => by simp [m, hmθ]`. Establish `hπt : ∀ g ∈ CommGroup.primaryComponent A l, π g = 1`. Introduce and unpack `g ⟨k, hk⟩`. Establish `e1 : π g ^ l ^ k = 1` using `by rw [← map_pow, hk, map_one]`.

Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `e2` using `congrFun (congrArg Multiplicative.toAdd e1) i`. Simplify using `only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply] at e2`. Simplify using `using (smul_eq_zero.1 e2).resolve_left (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)`.

Establish `hat : ∀ g ∈ CommGroup.primaryComponent A l, a g = 1`. Introduce and unpack `g ⟨k, hk⟩`. Establish `e1 : a g ^ l ^ k = 1` using `by rw [← map_pow, hk, map_one]`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Establish `e2` using `congrArg Multiplicative.toAdd e1`.

Simplify using `only [toAdd_pow, toAdd_one] at e2`. Simplify using `using (smul_eq_zero.1 e2).resolve_left (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)`. Establish `hDa : ∀ g, D g = 1 → a g = 1`. Introduce `g hg`. Take `⟨u, hu, rfl⟩` from `as_ker θ hc hd hb v ϖ hϖ hv D hD hDv g hg`.

Rewrite using `[haθ]`. Simplify using `[va, hu]`. Establish `hasurj : Function.Surjective a`. Establish `hR : IsClosed {w : ℤ_[l] | Multiplicative.ofAdd w ∈ Set.range a}` using `(isCompact_range hac).isClosed.preimage continuous_ofAdd`. Introduce `z`.

Establish `e1 : Multiplicative.toAdd z ∈ {w : ℤ_[l] | Multiplicative.ofAdd w ∈ Set.range a}`. Use `hR.closure_subset_iff.2 ?_ (PadicInt.denseRange_intCast _)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨θ (ϖ ^ k), ?_⟩` and prove the remaining obligations. Rewrite using `[haθ]`.

Simplify using `[va, hϖ]`. Simplify using `using e1`. Establish `hsep : ∀ (Y : Type) [CommGroup Y] [Finite Y], IsPGroup l Y → ∀ f : A →* Y, IsOpen (f.ker : Set A) → ∀ g, π g = 1 → a g = 1 → m g = 1 → f g = 1`. Introduce `Y _ _ hY f hf g hπ ha hm`. Take `⟨n, hn⟩` from `(IsPGroup.iff_card).1 hY`.

Set `Wπ : Set A` to `{x | ∀ i, (l : ℤ_[l]) ^ n ∣ (Multiplicative.toAdd (π x)) i}`. Establish `hWπ : IsOpen Wπ`. Establish `e1 : Wπ = ⋂ i, (fun x => (Multiplicative.toAdd (π x)) i) ⁻¹' {z | (l : ℤ_[l]) ^ n ∣ z}`. Use `ext`. Simplify using `[Wπ]`.

Rewrite using `[e1]`. Conclude with `isOpen_iInter_of_finite fun i => (as_open n).preimage ((continuous_apply i).comp (continuous_toAdd.comp hπc))`. Set `Wa : Set A` to `{x | (l : ℤ_[l]) ^ n ∣ Multiplicative.toAdd (a x)}`. Establish `hWa : IsOpen Wa` using `(as_open n).preimage (continuous_toAdd.comp hac)`. Set `O : Set A` to `((fun x => g⁻¹ * x) ⁻¹' (f.ker : Set A)) ∩ Wπ ∩ Wa ∩ (m.ker : Set A)`.

Establish `hOo : IsOpen O` using `(((hf.preimage (continuous_mul_left _)).inter hWπ).inter hWa).inter hmker`. Establish `hgO : g ∈ O`. Use `⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `[one_mem]`. Simplify using `[Wπ, hπ]`.

Simplify using `[Wa, ha]`. Conclude with `hm`. Take `⟨y, ⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩⟩` from `hd.exists_mem_open hOo ⟨g, hgO⟩`. Establish `hp' : ∀ i, (l : ℤ_[l]) ^ n ∣ (Multiplicative.toAdd (p y)) i`. Introduce `i`.

Establish `e1` using `hy2 i`. Rewrite `e1` using `[hπθ]`. Then use the resulting hypothesis. Establish `hv'' : (l : ℤ) ^ n ∣ Multiplicative.toAdd (v y)`. Establish `e1 : (l : ℤ_[l]) ^ n ∣ Multiplicative.toAdd (a (θ y))` using `hy3`. Rewrite `e1` using `[haθ]`.

Establish `e2 : (l : ℤ_[l]) ^ n ∣ ((Multiplicative.toAdd (v y) : ℤ) : ℤ_[l])` using `by simpa [va] using e1`. Rewrite `e2` using `[← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_int_le_pow_iff_dvd]`. Conclude with `e2` after adjusting the coercions. Establish `ht' : t y = 1`. Establish `e1 : m (θ y) = 1` using `hy4`.

Rewrite `e1` using `[hmθ']`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hi` to reduce the goal to its premises. Establish `e2` using `congrArg Subtype.val e1`. Simplify `e2` using `[hθlv]`.

Take `⟨z, rfl⟩` from `h3 n y hp' hv'' ht'`. Establish `e1 : f (θ (z ^ l ^ n)) = 1` using `by rw [map_pow, map_pow, ← hn, pow_card_eq_one']`. Establish `e2 : f (g⁻¹ * θ (z ^ l ^ n)) = 1` using `hy1`. Rewrite `e2` using `[map_mul, e1, mul_one, map_inv, inv_eq_one]`. Conclude with `e2`.

Establish `hsepA : ∀ h ∈ CommGroup.primaryComponent A l, (∀ (Y : Type) [CommGroup Y] [Finite Y], IsPGroup l Y → ∀ f : A →* Y, IsOpen (f.ker : Set A) → f h = 1) → h = 1`. Introduce and unpack `h ⟨j, hj⟩ hall`. Assume the negation of the conclusion as `hne`. Take `⟨V, hVo, hVsub⟩` from `hb {h}ᶜ isOpen_compl_singleton (Ne.symm hne)`. Use `haveI : Finite (A ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo`.

Take `⟨e, e', hle', he⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := A ⧸ V)).ne' l (Fact.out : l.Prime).one_lt.ne'`. Set `φ : A ⧸ V →* A ⧸ V` to `powMonoidHom e'`. Set `f : A →* φ.range` to `φ.rangeRestrict.comp (QuotientGroup.mk' V)`. Establish `hY : IsPGroup l φ.range`. Introduce and unpack `⟨_, x, rfl⟩`.

Use `⟨e, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [φ, powMonoidHom_apply, SubmonoidClass.coe_pow, OneMemClass.coe_one]`. Rewrite using `[← pow_mul, mul_comm, ← he, pow_card_eq_one']`. Establish `hfo : IsOpen (f.ker : Set A)`. Use `Subgroup.isOpen_mono (fun x hx => ?_) hVo` and prove the remaining obligations.

Rewrite using `[MonoidHom.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[f, φ, (QuotientGroup.eq_one_iff x).2 hx]`. Establish `hfh` using `hall _ hY f hfo`. Establish `e1 : (QuotientGroup.mk' V h) ^ e' = 1`.

Establish `e0` using `congrArg Subtype.val hfh`. Simplify `e0` using `[f, φ]`. Establish `e2 : (QuotientGroup.mk' V h) ^ (l ^ j) = 1` using `by rw [← map_pow, hj, map_one]`. Establish `hcop : Nat.Coprime (l ^ j) e'` using `Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hle')`. Establish `e3 : QuotientGroup.mk' V h = 1`.

Rewrite using `[← orderOf_eq_one_iff]`. Conclude with `Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e1)`. Conclude with `hVsub ((QuotientGroup.eq_one_iff h).1 e3) (Set.mem_singleton h)`. Establish `hmm : ∀ g, m (m g : A) = m g`. Introduce `g`.

Establish `e1 : (m g : A) = θ (mM g)` using `rfl`. Rewrite using `[e1, hmθ']`. Rewrite using `[(h1 (mM g)).2]`. Both sides reduce to the same expression. Establish `hmid : ∀ g ∈ CommGroup.primaryComponent A l, (m g : A) = g`.

Introduce `g hg`. Establish `hh : g * (m g : A)⁻¹ ∈ CommGroup.primaryComponent A l` using `mul_mem hg (inv_mem (m g).2)`. Establish `e1 : g * (m g : A)⁻¹ = 1`. Use `hsepA _ hh fun Y _ _ hY f hf => hsep Y hY f hf _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, hπt g hg, hπt _ (m g).2, inv_one, mul_one]`.

Rewrite using `[map_mul, map_inv, hat g hg, hat _ (m g).2, inv_one, mul_one]`. Rewrite using `[map_mul, map_inv, hmm, mul_inv_cancel]`. Conclude with `(mul_inv_eq_one.1 e1).symm`. Establish `hsurj : Function.Surjective θl`. Introduce `x`.

Conclude with `⟨mM x, Subtype.ext (hmid x x.2)⟩`. Use `⟨Finite.of_surjective θl hsurj, isCyclic_of_surjective θl hsurj, π, a, m, hπc, hac, hmker, fun g hg => ⟨hπt g hg, hat g hg, hmid g hg⟩, hDa, hasurj, ?_, hsep⟩` and prove the remaining obligations. Introduce `x τ`. Take `⟨τ', rfl⟩` from `hsurj τ`. Take `⟨y, e1, e2, e3⟩` from `h2 x τ'`.

Use `⟨θ y, ?_, by rw [hπθ, e2], by rw [hmθ', e3]⟩` and prove the remaining obligations. Rewrite using `[hDv, e1]`. Simplify using the standard rewrite rules.
-/
private theorem as_core {l : ℕ} [Fact l.Prime] {d : ℕ} {M A : Type} [CommGroup M] [TopologicalSpace M]
    [IsTopologicalGroup M] [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] [T2Space A] (θ : M →* A) (hc : Continuous θ)
    (hi : Function.Injective θ) (hd : DenseRange θ)
    (hE : ∀ H : Subgroup M, IsOpen (H : Set M) → H.FiniteIndex →
      ∃ V : Subgroup A, IsOpen (V : Set A) ∧ V.comap θ = H)
    (hb : ∀ O : Set A, IsOpen O → 1 ∈ O → ∃ V : Subgroup A, IsOpen (V : Set A) ∧ (V : Set A) ⊆ O)
    (v : M →* Multiplicative ℤ) (ϖ : M) (hϖ : v ϖ = .ofAdd 1) (hv : IsCompact (v.ker : Set M))
    (hv' : IsOpen (v.ker : Set M))
    (D : A →* Multiplicative ProfiniteInteger) (hD : Continuous D)
    (hDv : ∀ y, D (θ y) = .ofAdd (((v y).toAdd : ℤ) : ProfiniteInteger))
    [Finite ↥(CommGroup.primaryComponent M l)] [IsCyclic ↥(CommGroup.primaryComponent M l)]
    (p : M →* Multiplicative (Fin d → ℤ_[l])) (t : M →* ↥(CommGroup.primaryComponent M l))
    (hp : Continuous p) (ht : IsOpen (t.ker : Set M))
    (h1 : ∀ y : ↥(CommGroup.primaryComponent M l), p y = 1 ∧ t y = y)
    (h2 : ∀ x τ, ∃ y, v y = 1 ∧ p y = x ∧ t y = τ)
    (h3 : ∀ (n : ℕ) y, (∀ i, (l : ℤ_[l]) ^ n ∣ (p y).toAdd i) → (l : ℤ) ^ n ∣ (v y).toAdd → t y = 1 →
      ∃ z, y = z ^ l ^ n) :
    Finite ↥(CommGroup.primaryComponent A l) ∧ IsCyclic ↥(CommGroup.primaryComponent A l) ∧
    ∃ (π : A →* Multiplicative (Fin d → ℤ_[l])) (a : A →* Multiplicative ℤ_[l])
      (m : A →* ↥(CommGroup.primaryComponent A l)), Continuous π ∧ Continuous a ∧ IsOpen (m.ker : Set A) ∧
      (∀ g ∈ CommGroup.primaryComponent A l, π g = 1 ∧ a g = 1 ∧ (m g : A) = g) ∧
      (∀ g, D g = 1 → a g = 1) ∧ Function.Surjective a ∧ (∀ x τ, ∃ g, D g = 1 ∧ π g = x ∧ m g = τ) ∧
      ∀ (Y : Type) [CommGroup Y] [Finite Y], IsPGroup l Y → ∀ f : A →* Y, IsOpen (f.ker : Set A) →
        ∀ g, π g = 1 → a g = 1 → m g = 1 → f g = 1 := by
  classical
  haveI : T2Space M := T2Space.of_injective_continuous hi hc
  obtain ⟨π, hπc, hπθ⟩ := as_ext θ hd hE p hp
  let va : M →* Multiplicative ℤ_[l] := (AddMonoidHom.toMultiplicative (Int.castAddHom ℤ_[l])).comp v
  have hva : Continuous va := by
    refine as_cont va (Subgroup.isOpen_mono (fun y hy => ?_) hv')
    rw [MonoidHom.mem_ker] at hy ⊢
    simp [va, hy]
  obtain ⟨a, hac, haθ⟩ := as_ext θ hd hE va hva
  have htc : Continuous t := as_cont t ht
  obtain ⟨mM, hmc, hmθ⟩ := as_ext θ hd hE t htc
  have hθl : ∀ x : ↥(CommGroup.primaryComponent M l),
      (θ.comp (CommGroup.primaryComponent M l).subtype) x ∈ CommGroup.primaryComponent A l := by
    rintro ⟨x, k, hk⟩
    exact ⟨k, by simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]; rw [← map_pow, hk, map_one]⟩
  let θl : ↥(CommGroup.primaryComponent M l) →* ↥(CommGroup.primaryComponent A l) :=
    (θ.comp (CommGroup.primaryComponent M l).subtype).codRestrict _ hθl
  have hθlv : ∀ x, (θl x : A) = θ x := fun x => rfl
  let m : A →* ↥(CommGroup.primaryComponent A l) := θl.comp mM
  have hmker : IsOpen (m.ker : Set A) := by
    have e0 : IsOpen (mM.ker : Set A) :=
      (isOpen_discrete {(1 : ↥(CommGroup.primaryComponent M l))}).preimage hmc
    refine Subgroup.isOpen_mono (fun x hx => ?_) e0
    rw [MonoidHom.mem_ker] at hx ⊢
    simp [m, hx]
  have hmθ' : ∀ y, m (θ y) = θl (t y) := fun y => by simp [m, hmθ]
  have hπt : ∀ g ∈ CommGroup.primaryComponent A l, π g = 1 := by
    rintro g ⟨k, hk⟩
    have e1 : π g ^ l ^ k = 1 := by rw [← map_pow, hk, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    have e2 := congrFun (congrArg Multiplicative.toAdd e1) i
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply] at e2
    simpa using (smul_eq_zero.1 e2).resolve_left (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have hat : ∀ g ∈ CommGroup.primaryComponent A l, a g = 1 := by
    rintro g ⟨k, hk⟩
    have e1 : a g ^ l ^ k = 1 := by rw [← map_pow, hk, map_one]
    apply Multiplicative.toAdd.injective
    have e2 := congrArg Multiplicative.toAdd e1
    simp only [toAdd_pow, toAdd_one] at e2
    simpa using (smul_eq_zero.1 e2).resolve_left (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have hDa : ∀ g, D g = 1 → a g = 1 := by
    intro g hg
    obtain ⟨u, hu, rfl⟩ := as_ker θ hc hd hb v ϖ hϖ hv D hD hDv g hg
    rw [haθ]
    simp [va, hu]
  have hasurj : Function.Surjective a := by
    have hR : IsClosed {w : ℤ_[l] | Multiplicative.ofAdd w ∈ Set.range a} :=
      (isCompact_range hac).isClosed.preimage continuous_ofAdd
    intro z
    have e1 : Multiplicative.toAdd z ∈ {w : ℤ_[l] | Multiplicative.ofAdd w ∈ Set.range a} := by
      refine hR.closure_subset_iff.2 ?_ (PadicInt.denseRange_intCast _)
      rintro _ ⟨k, rfl⟩
      refine ⟨θ (ϖ ^ k), ?_⟩
      rw [haθ]
      simp [va, hϖ]
    simpa using e1
  have hsep : ∀ (Y : Type) [CommGroup Y] [Finite Y], IsPGroup l Y → ∀ f : A →* Y,
      IsOpen (f.ker : Set A) → ∀ g, π g = 1 → a g = 1 → m g = 1 → f g = 1 := by
    intro Y _ _ hY f hf g hπ ha hm
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hY
    let Wπ : Set A := {x | ∀ i, (l : ℤ_[l]) ^ n ∣ (Multiplicative.toAdd (π x)) i}
    have hWπ : IsOpen Wπ := by
      have e1 : Wπ = ⋂ i, (fun x => (Multiplicative.toAdd (π x)) i) ⁻¹' {z | (l : ℤ_[l]) ^ n ∣ z} := by
        ext
        simp [Wπ]
      rw [e1]
      exact isOpen_iInter_of_finite fun i =>
        (as_open n).preimage ((continuous_apply i).comp (continuous_toAdd.comp hπc))
    let Wa : Set A := {x | (l : ℤ_[l]) ^ n ∣ Multiplicative.toAdd (a x)}
    have hWa : IsOpen Wa := (as_open n).preimage (continuous_toAdd.comp hac)
    let O : Set A := ((fun x => g⁻¹ * x) ⁻¹' (f.ker : Set A)) ∩ Wπ ∩ Wa ∩ (m.ker : Set A)
    have hOo : IsOpen O :=
      (((hf.preimage (continuous_mul_left _)).inter hWπ).inter hWa).inter hmker
    have hgO : g ∈ O := by
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · simp [one_mem]
      · simp [Wπ, hπ]
      · simp [Wa, ha]
      · exact hm
    obtain ⟨y, ⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩⟩ := hd.exists_mem_open hOo ⟨g, hgO⟩
    have hp' : ∀ i, (l : ℤ_[l]) ^ n ∣ (Multiplicative.toAdd (p y)) i := by
      intro i
      have e1 := hy2 i
      rwa [hπθ] at e1
    have hv'' : (l : ℤ) ^ n ∣ Multiplicative.toAdd (v y) := by
      have e1 : (l : ℤ_[l]) ^ n ∣ Multiplicative.toAdd (a (θ y)) := hy3
      rw [haθ] at e1
      have e2 : (l : ℤ_[l]) ^ n ∣ ((Multiplicative.toAdd (v y) : ℤ) : ℤ_[l]) := by simpa [va] using e1
      rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
        PadicInt.norm_int_le_pow_iff_dvd] at e2
      exact_mod_cast e2
    have ht' : t y = 1 := by
      have e1 : m (θ y) = 1 := hy4
      rw [hmθ'] at e1
      apply Subtype.ext
      apply hi
      have e2 := congrArg Subtype.val e1
      simpa [hθlv] using e2
    obtain ⟨z, rfl⟩ := h3 n y hp' hv'' ht'
    have e1 : f (θ (z ^ l ^ n)) = 1 := by rw [map_pow, map_pow, ← hn, pow_card_eq_one']
    have e2 : f (g⁻¹ * θ (z ^ l ^ n)) = 1 := hy1
    rw [map_mul, e1, mul_one, map_inv, inv_eq_one] at e2
    exact e2
  have hsepA : ∀ h ∈ CommGroup.primaryComponent A l, (∀ (Y : Type) [CommGroup Y] [Finite Y],
      IsPGroup l Y → ∀ f : A →* Y, IsOpen (f.ker : Set A) → f h = 1) → h = 1 := by
    rintro h ⟨j, hj⟩ hall
    by_contra hne
    obtain ⟨V, hVo, hVsub⟩ := hb {h}ᶜ isOpen_compl_singleton (Ne.symm hne)
    haveI : Finite (A ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo
    obtain ⟨e, e', hle', he⟩ := Nat.exists_eq_pow_mul_and_not_dvd
      (Nat.card_pos (α := A ⧸ V)).ne' l (Fact.out : l.Prime).one_lt.ne'
    let φ : A ⧸ V →* A ⧸ V := powMonoidHom e'
    let f : A →* φ.range := φ.rangeRestrict.comp (QuotientGroup.mk' V)
    have hY : IsPGroup l φ.range := by
      rintro ⟨_, x, rfl⟩
      refine ⟨e, Subtype.ext ?_⟩
      simp only [φ, powMonoidHom_apply, SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← pow_mul, mul_comm, ← he, pow_card_eq_one']
    have hfo : IsOpen (f.ker : Set A) := by
      refine Subgroup.isOpen_mono (fun x hx => ?_) hVo
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      simp [f, φ, (QuotientGroup.eq_one_iff x).2 hx]
    have hfh := hall _ hY f hfo
    have e1 : (QuotientGroup.mk' V h) ^ e' = 1 := by
      have e0 := congrArg Subtype.val hfh
      simpa [f, φ] using e0
    have e2 : (QuotientGroup.mk' V h) ^ (l ^ j) = 1 := by rw [← map_pow, hj, map_one]
    have hcop : Nat.Coprime (l ^ j) e' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hle')
    have e3 : QuotientGroup.mk' V h = 1 := by
      rw [← orderOf_eq_one_iff]
      exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e1)
    exact hVsub ((QuotientGroup.eq_one_iff h).1 e3) (Set.mem_singleton h)
  have hmm : ∀ g, m (m g : A) = m g := by
    intro g
    have e1 : (m g : A) = θ (mM g) := rfl
    rw [e1, hmθ']
    rw [(h1 (mM g)).2]
    rfl
  have hmid : ∀ g ∈ CommGroup.primaryComponent A l, (m g : A) = g := by
    intro g hg
    have hh : g * (m g : A)⁻¹ ∈ CommGroup.primaryComponent A l :=
      mul_mem hg (inv_mem (m g).2)
    have e1 : g * (m g : A)⁻¹ = 1 := by
      refine hsepA _ hh fun Y _ _ hY f hf => hsep Y hY f hf _ ?_ ?_ ?_
      · rw [map_mul, map_inv, hπt g hg, hπt _ (m g).2, inv_one, mul_one]
      · rw [map_mul, map_inv, hat g hg, hat _ (m g).2, inv_one, mul_one]
      · rw [map_mul, map_inv, hmm, mul_inv_cancel]
    exact (mul_inv_eq_one.1 e1).symm
  have hsurj : Function.Surjective θl := by
    intro x
    exact ⟨mM x, Subtype.ext (hmid x x.2)⟩
  refine ⟨Finite.of_surjective θl hsurj, isCyclic_of_surjective θl hsurj, π, a, m, hπc, hac, hmker,
    fun g hg => ⟨hπt g hg, hat g hg, hmid g hg⟩, hDa, hasurj, ?_, hsep⟩
  intro x τ
  obtain ⟨τ', rfl⟩ := hsurj τ
  obtain ⟨y, e1, e2, e3⟩ := h2 x τ'
  refine ⟨θ y, ?_, by rw [hπθ, e2], by rw [hmθ', e3]⟩
  rw [hDv, e1]
  simp

/- English proof (translation)
Introduce `l _ G _ _ _ φ hφ`. Use `haveI : T2Space G := T2Space.of_injective_continuous hφ.injective hφ.continuous`. Use `haveI : CompactSpace G := by`. Establish `hcl : IsClosed (Set.range φ)`. Establish `ho : IsOpen (φ.range : Set (GQ l))` using `by simpa using hφ.isOpen_range`.

Simplify using `using Subgroup.isClosed_of_isOpen φ.range ho`. Conclude with `⟨hφ.isEmbedding.isCompact_iff.2 (by simpa [Set.image_univ] using hcl.isCompact)⟩`. Establish `hbG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O → ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ O`. Introduce `O hO h1`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hφ.isOpenMap O hO) ⟨1, h1, map_one φ⟩`.

Use `⟨U.toSubgroup.comap φ, U.toOpenSubgroup.isOpen.preimage hφ.continuous, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hyx⟩` from `hU hx`. Conclude with `hφ.injective hyx ▸ hy`. Use `haveI : IsClosed ((commutator G).topologicalClosure : Set G) := Subgroup.isClosed_topologicalClosure _`. Set `q : G →* TopologicalAbelianization G` to `QuotientGroup.mk' (commutator G).topologicalClosure`.

Establish `hqc : Continuous q` using `QuotientGroup.continuous_mk`. Establish `hqs : Function.Surjective q` using `QuotientGroup.mk'_surjective _`. Establish `hqo : IsOpenMap q` using `QuotientGroup.isOpenMap_coe`. Establish `hbA : ∀ O : Set (TopologicalAbelianization G), IsOpen O → 1 ∈ O → ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ (V : Set (TopologicalAbelianization G)) ⊆ O`. Introduce `O hO h1`.

Take `⟨U, hUo, hU⟩` from `hbG _ (hO.preimage hqc) (by simpa using h1)`. Use `⟨U.map q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_map]`. Conclude with `hqo _ hUo`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `hU hx`. Take `⟨K, _, _, _, _, _, _, _, hidx, θ, D, hc, hi, hd, hE, hD, hDv, hIq⟩` from `UpperTheory.local_class_field_theory_of_open_embedding φ hφ`. Take `⟨ϖ0, hϖ0⟩` from `IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation K).integer`. Set `v : Kˣ →* Multiplicative ℤ` to `(MonoidHom.fst _ _).comp (GroundTheory.LocalField.unitsEquivIntProd hϖ0).toMonoidHom`. Establish `hvdef : ∀ y : Kˣ, v y = Multiplicative.ofAdd (GroundTheory.LocalField.ord (y : K))` using `fun y => GroundTheory.LocalField.unitsEquivIntProd_fst hϖ0 y`.

Establish `hϖ : v (GroundTheory.LocalField.uniformizerUnit hϖ0) = Multiplicative.ofAdd 1`. Rewrite using `[hvdef, GroundTheory.LocalField.coe_uniformizerUnit, GroundTheory.LocalField.ord_uniformizer hϖ0]`. Establish `hker : v.ker = GroundTheory.LocalField.unitFiltrationUnits K 0`. Use extensionality with `y`. Rewrite using `[MonoidHom.mem_ker, GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff, hvdef, ← map_one (ValuativeRel.valuation K), ← GroundTheory.LocalField.normalizedValuation_eq_iff, map_one, GroundTheory.LocalField.normalizedValuation_eq_exp_ord y.ne_zero]`.

Simplify using the standard rewrite rules. Take `⟨hfin, p, t, hp, ht, h1, h2, h3⟩` from `UpperTheory.localField_units_structure_theorem K l`. Use `haveI := hfin`. Use `haveI : IsCyclic ↥(CommGroup.primaryComponent Kˣ l) := inferInstance`. Take `⟨hAf, hAc, πA, aA, mA, hπc, hac, hmo, hA1, hA2, hA3, hA4, hA5⟩` from `as_core (l := l) θ hc hi hd hE hbA v _ hϖ (by rw [hker]; exact GroundTheory.LocalField.isCompact_unitFiltrationUnits 0) (by rw [hker]; exact GroundTheory.LocalField.isOpen_unitFiltrationUnits 0) D hD (fun y => by rw [hDv, hvdef, toAdd_ofAdd]) p t hp ht h1 (fun x τ => by`.

Take `⟨y, e1, e2, e3⟩` from `h2 x τ`. Conclude with `⟨y, by rw [hvdef, e1]; rfl, e2, e3⟩)`. Use the proof step `(fun n y e1 e2 e3 => h3 n y e1 (by rwa [hvdef, toAdd_ofAdd] at e2) e3)`. Rewrite using `[hidx]`. Use `⟨hAf, hAc, πA.comp q, aA.comp q, mA.comp q, hπc.comp hqc, hac.comp hqc, hmo.preimage hqc, fun g hg => hA1 (q g) hg, fun g hg => hA2 (q g) ((hIq g).1 hg), hA3.comp hqs, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x τ`. Take `⟨g', e1, e2, e3⟩` from `hA4 x τ`. Take `⟨g, rfl⟩` from `hqs g'`. Conclude with `⟨g, (hIq g).2 e1, e2, e3⟩`. Introduce `Y _ _ hY f hf g e1 e2 e3`.

Establish `hle : (commutator G).topologicalClosure ≤ f.ker`. Establish `hcl : IsClosed (f.ker : Set G)` using `Subgroup.isClosed_of_isOpen _ hf`. Conclude with `Subgroup.topologicalClosure_minimal _ (GroundTheory.LocalField.commutator_le_ker_of_comm f) hcl`. Set `f' : TopologicalAbelianization G →* Y` to `QuotientGroup.lift _ f hle`. Establish `hf' : IsOpen (f'.ker : Set (TopologicalAbelianization G))`.

Establish `e0 : (f'.ker : Set (TopologicalAbelianization G)) = q '' (f.ker : Set G)`. Use extensionality with `z`. Take `⟨z, rfl⟩` from `hqs z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Conclude with `⟨z, hz, rfl⟩`. Introduce and unpack `⟨w, hw, hwz⟩`. Rewrite using `[← hwz]`. Conclude with `hw`. Rewrite using `[e0]`.

Conclude with `hqo _ hf`. Conclude with `hA5 Y hY f' hf' (q g) e1 e2 e3`.
-/
theorem UpperTheory.V.Loc.abStruct :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), Finite ↥(CommGroup.primaryComponent (TopologicalAbelianization G) l) ∧ IsCyclic ↥(CommGroup.primaryComponent (TopologicalAbelianization G) l) ∧ ∃ (π : G →* Multiplicative (Fin φ.range.index → ℤ_[l])) (a : G →* Multiplicative ℤ_[l]) (m : G →* ↥(CommGroup.primaryComponent (TopologicalAbelianization G) l)), Continuous π ∧ Continuous a ∧ IsOpen (m.ker : Set G) ∧ (∀ g : G, (QuotientGroup.mk' _ g : TopologicalAbelianization G) ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l → π g = 1 ∧ a g = 1 ∧ (m g : TopologicalAbelianization G) = QuotientGroup.mk' _ g) ∧ (∀ g, φ g ∈ Iq l → a g = 1) ∧ Function.Surjective a ∧ (∀ x t, ∃ g, φ g ∈ Iq l ∧ π g = x ∧ m g = t) ∧ ∀ (Y : Type) [CommGroup Y] [Finite Y], IsPGroup l Y → ∀ f : G →* Y, IsOpen (f.ker : Set G) → ∀ g, π g = 1 → a g = 1 → m g = 1 → f g = 1 := by
  intro l _ G _ _ _ φ hφ
  classical
  haveI : T2Space G := T2Space.of_injective_continuous hφ.injective hφ.continuous
  haveI : CompactSpace G := by
    have hcl : IsClosed (Set.range φ) := by
      have ho : IsOpen (φ.range : Set (GQ l)) := by simpa using hφ.isOpen_range
      simpa using Subgroup.isClosed_of_isOpen φ.range ho
    exact ⟨hφ.isEmbedding.isCompact_iff.2 (by simpa [Set.image_univ] using hcl.isCompact)⟩
  have hbG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O → ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ O := by
    intro O hO h1
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hφ.isOpenMap O hO)
      ⟨1, h1, map_one φ⟩
    refine ⟨U.toSubgroup.comap φ, U.toOpenSubgroup.isOpen.preimage hφ.continuous, fun x hx => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hU hx
    exact hφ.injective hyx ▸ hy
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) := Subgroup.isClosed_topologicalClosure _
  let q : G →* TopologicalAbelianization G := QuotientGroup.mk' (commutator G).topologicalClosure
  have hqc : Continuous q := QuotientGroup.continuous_mk
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hbA : ∀ O : Set (TopologicalAbelianization G), IsOpen O → 1 ∈ O →
      ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧
        (V : Set (TopologicalAbelianization G)) ⊆ O := by
    intro O hO h1
    obtain ⟨U, hUo, hU⟩ := hbG _ (hO.preimage hqc) (by simpa using h1)
    refine ⟨U.map q, ?_, ?_⟩
    · rw [Subgroup.coe_map]
      exact hqo _ hUo
    · rintro _ ⟨x, hx, rfl⟩
      exact hU hx
  obtain ⟨K, _, _, _, _, _, _, _, hidx, θ, D, hc, hi, hd, hE, hD, hDv, hIq⟩ := UpperTheory.local_class_field_theory_of_open_embedding φ hφ
  obtain ⟨ϖ0, hϖ0⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation K).integer
  let v : Kˣ →* Multiplicative ℤ := (MonoidHom.fst _ _).comp (GroundTheory.LocalField.unitsEquivIntProd hϖ0).toMonoidHom
  have hvdef : ∀ y : Kˣ, v y = Multiplicative.ofAdd (GroundTheory.LocalField.ord (y : K)) := fun y =>
    GroundTheory.LocalField.unitsEquivIntProd_fst hϖ0 y
  have hϖ : v (GroundTheory.LocalField.uniformizerUnit hϖ0) = Multiplicative.ofAdd 1 := by
    rw [hvdef, GroundTheory.LocalField.coe_uniformizerUnit, GroundTheory.LocalField.ord_uniformizer hϖ0]
  have hker : v.ker = GroundTheory.LocalField.unitFiltrationUnits K 0 := by
    ext y
    rw [MonoidHom.mem_ker, GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff, hvdef,
      ← map_one (ValuativeRel.valuation K), ← GroundTheory.LocalField.normalizedValuation_eq_iff, map_one,
      GroundTheory.LocalField.normalizedValuation_eq_exp_ord y.ne_zero]
    simp
  obtain ⟨hfin, p, t, hp, ht, h1, h2, h3⟩ := UpperTheory.localField_units_structure_theorem K l
  haveI := hfin
  haveI : IsCyclic ↥(CommGroup.primaryComponent Kˣ l) := inferInstance
  obtain ⟨hAf, hAc, πA, aA, mA, hπc, hac, hmo, hA1, hA2, hA3, hA4, hA5⟩ :=
    as_core (l := l) θ hc hi hd hE hbA v _ hϖ (by rw [hker]; exact GroundTheory.LocalField.isCompact_unitFiltrationUnits 0)
      (by rw [hker]; exact GroundTheory.LocalField.isOpen_unitFiltrationUnits 0) D hD
      (fun y => by rw [hDv, hvdef, toAdd_ofAdd]) p t hp ht h1
      (fun x τ => by
        obtain ⟨y, e1, e2, e3⟩ := h2 x τ
        exact ⟨y, by rw [hvdef, e1]; rfl, e2, e3⟩)
      (fun n y e1 e2 e3 => h3 n y e1 (by rwa [hvdef, toAdd_ofAdd] at e2) e3)
  rw [hidx]
  refine ⟨hAf, hAc, πA.comp q, aA.comp q, mA.comp q, hπc.comp hqc, hac.comp hqc, hmo.preimage hqc,
    fun g hg => hA1 (q g) hg, fun g hg => hA2 (q g) ((hIq g).1 hg), hA3.comp hqs, ?_, ?_⟩
  · intro x τ
    obtain ⟨g', e1, e2, e3⟩ := hA4 x τ
    obtain ⟨g, rfl⟩ := hqs g'
    exact ⟨g, (hIq g).2 e1, e2, e3⟩
  · intro Y _ _ hY f hf g e1 e2 e3
    have hle : (commutator G).topologicalClosure ≤ f.ker := by
      have hcl : IsClosed (f.ker : Set G) := Subgroup.isClosed_of_isOpen _ hf
      exact Subgroup.topologicalClosure_minimal _ (GroundTheory.LocalField.commutator_le_ker_of_comm f) hcl
    let f' : TopologicalAbelianization G →* Y := QuotientGroup.lift _ f hle
    have hf' : IsOpen (f'.ker : Set (TopologicalAbelianization G)) := by
      have e0 : (f'.ker : Set (TopologicalAbelianization G)) = q '' (f.ker : Set G) := by
        ext z
        obtain ⟨z, rfl⟩ := hqs z
        constructor
        · intro hz
          exact ⟨z, hz, rfl⟩
        · rintro ⟨w, hw, hwz⟩
          rw [← hwz]
          exact hw
      rw [e0]
      exact hqo _ hf
    exact hA5 Y hY f' hf' (q g) e1 e2 e3
