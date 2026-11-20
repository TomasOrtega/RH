import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatEventuallyInvariantOfContinuousAct

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter

namespace GlobalTheory.SBInduced

variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]

omit [IsTopologicalGroup G] in

/- English proof (translation)
Establish `hc' : ∀ g, Continuous fun x => r x g` using `fun g => hc.comp (Continuous.prodMk_left g)`. Set `e : X ≃ₜ X` to `{ toFun := fun x => r x g invFun := fun x => r x g⁻¹ left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1] right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1] continuous_toFun := hc' g continuous_invFun := hc' g⁻¹ }`. Conclude with `e.isClosedEmbedding.comp hj`.
-/
theorem isClosedEmbedding_translate (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) (g : G) : IsClosedEmbedding fun y => r (j y) g := by
  have hc' : ∀ g, Continuous fun x => r x g := fun g => hc.comp (Continuous.prodMk_left g)
  let e : X ≃ₜ X :=
    { toFun := fun x => r x g
      invFun := fun x => r x g⁻¹
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := hc' g
      continuous_invFun := hc' g⁻¹ }
  exact e.isClosedEmbedding.comp hj

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Set `e : X × K ≃ₜ X × K` to `{ toFun := fun p => (r p.1 p.2, p.2) invFun := fun p => (r p.1 (p.2 : G)⁻¹, p.2) left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1] right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1] continuous_toFun := (hc.comp (continuous_fst.prodMk (continuous_subtype_val. …`. Establish `hcl : IsClosedMap fun p : Y × K => r (j p.1) p.2` using `(isClosedMap_fst_of_compactSpace (X := X) (Y := K)).comp (e.isClosedMap.comp (hj.prodMap (IsClosedEmbedding.id (X := K))).isClosedMap)`. Use `hcl.isQuotientMap (hc.comp ((hj.continuous.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))) fun x => ?_` and prove the remaining obligations. Take `⟨y, c, hc, rfl⟩` from `hs x`.

Conclude with `⟨(y, ⟨c, hc⟩), rfl⟩`.
-/
theorem isQuotientMap_sweep (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) :
    IsQuotientMap fun p : Y × K => r (j p.1) p.2 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let e : X × K ≃ₜ X × K :=
    { toFun := fun p => (r p.1 p.2, p.2)
      invFun := fun p => (r p.1 (p.2 : G)⁻¹, p.2)
      left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
      right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
      continuous_toFun := (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk
        continuous_snd
      continuous_invFun := (hc.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd).inv)).prodMk continuous_snd }
  have hcl : IsClosedMap fun p : Y × K => r (j p.1) p.2 :=
    (isClosedMap_fst_of_compactSpace (X := X) (Y := K)).comp
      (e.isClosedMap.comp (hj.prodMap (IsClosedEmbedding.id (X := K))).isClosedMap)
  refine hcl.isQuotientMap (hc.comp ((hj.continuous.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))) fun x => ?_
  obtain ⟨y, c, hc, rfl⟩ := hs x
  exact ⟨(y, ⟨c, hc⟩), rfl⟩

/- English proof (translation)
Establish `hq` using `isQuotientMap_sweep r h1 hm hc hj hK hs`. Use `choose y c hcK hx using hs`. Set `φ : X → ℂ` to `fun x => (H (c x)).1 (y x)`. Establish `hφ : ∀ g z, φ (r (j z) g) = (H g).1 z` using `fun g z => hfib _ _ _ _ (hx _).symm`. Establish `hnear : ∀ g : G, ∀ᶠ z in 𝓝 g, H z = H g` using `fun g => by`.

Establish `hc : Tendsto (fun z : G => g⁻¹ * z) (𝓝 g) (𝓝 1)` using `Continuous.tendsto' (by fun_prop) _ _ (by simp)`. Conclude with `(hc.eventually hU).mono fun z hz => by simpa using hz g`. Establish `hlc : IsLocallyConstant fun p : Y × G => (H p.2).1 p.1`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `p`.

Use `filter_upwards [(continuous_snd.tendsto p).eventually (hnear p.2), (continuous_fst.tendsto p).eventually ((H p.2).2.1.eventually_eq p.1)] with z h₁ h₂`. Rewrite using `[h₁, h₂]`. Use `⟨⟨φ, fun s => ?_, ?_⟩, hφ⟩` and prove the remaining obligations. Rewrite using `[← hq.isOpen_preimage]`. Use `(hlc.comp_continuous (f := fun p : Y × K => (p.1, (p.2 : G))) (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) s` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `p`. Simplify using `only [Set.mem_preimage, hφ, Function.comp_apply]`. Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun x => {z | H z = H x}) fun x _ => hnear x`. Establish `hC : IsCompact (⋃ g ∈ t, tsupport (H g).1)` using `t.isCompact_biUnion fun g _ => (H g).2.2`.

Use `HasCompactSupport.intro (((hC.image hj.continuous).prod hK).image hc) fun x hxn => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Apply `hxn` to reduce the goal to its premises. Take `⟨g, hg, hcg⟩` from `Set.mem_iUnion₂.1 (ht (hcK x))`. Use `⟨(j (y x), c x), ⟨⟨y x, Set.mem_iUnion₂.2 ⟨g, hg, subset_tsupport _ ?_⟩, rfl⟩, hcK x⟩, (hx x).symm⟩` and prove the remaining obligations.

Rewrite using `[← show H (c x) = H g from hcg]`. Conclude with `h0`.
-/
theorem descend [T2Space X] (r : X → G → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : Continuous (fun p : X × G => r p.1 p.2))
    {j : Y → X} (hj : IsClosedEmbedding j) {K : Set G} (hK : IsCompact K)
    (hs : ∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) (H : G → SB Y)
    (hU : ∀ᶠ u in 𝓝 (1 : G), ∀ g, H (g * u) = H g)
    (hfib : ∀ y g y' g', r (j y) g = r (j y') g' → (H g).1 y = (H g').1 y') :
    ∃ Φ : SB X, ∀ g y, Φ.1 (r (j y) g) = (H g).1 y := by
  have hq := isQuotientMap_sweep r h1 hm hc hj hK hs
  choose y c hcK hx using hs
  let φ : X → ℂ := fun x => (H (c x)).1 (y x)
  have hφ : ∀ g z, φ (r (j z) g) = (H g).1 z := fun g z => hfib _ _ _ _ (hx _).symm
  have hnear : ∀ g : G, ∀ᶠ z in 𝓝 g, H z = H g := fun g => by
    have hc : Tendsto (fun z : G => g⁻¹ * z) (𝓝 g) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact (hc.eventually hU).mono fun z hz => by simpa using hz g
  have hlc : IsLocallyConstant fun p : Y × G => (H p.2).1 p.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    filter_upwards [(continuous_snd.tendsto p).eventually (hnear p.2),
      (continuous_fst.tendsto p).eventually ((H p.2).2.1.eventually_eq p.1)] with z h₁ h₂
    rw [h₁, h₂]
  refine ⟨⟨φ, fun s => ?_, ?_⟩, hφ⟩
  · rw [← hq.isOpen_preimage]
    have := (hlc.comp_continuous (f := fun p : Y × K => (p.1, (p.2 : G)))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) s
    convert this using 1
    ext p
    simp only [Set.mem_preimage, hφ, Function.comp_apply]
  · obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {z | H z = H x}) fun x _ => hnear x
    have hC : IsCompact (⋃ g ∈ t, tsupport (H g).1) :=
      t.isCompact_biUnion fun g _ => (H g).2.2
    refine HasCompactSupport.intro (((hC.image hj.continuous).prod hK).image hc) fun x hxn => ?_
    by_contra h0
    apply hxn
    obtain ⟨g, hg, hcg⟩ := Set.mem_iUnion₂.1 (ht (hcK x))
    refine ⟨(j (y x), c x), ⟨⟨y x, Set.mem_iUnion₂.2 ⟨g, hg, subset_tsupport _ ?_⟩, rfl⟩, hcK x⟩,
      (hx x).symm⟩
    rw [← show H (c x) = H g from hcg]
    exact h0

/- English proof (translation)
Introduce `G X Y W _ _ _ _ _ _ _ _ r h1 hm hc j hj P K hK hs s hsP hP χ hχ σ ev hev`. Establish `hχ' : ∀ᶠ u in 𝓝 (1 : G), χ u = 1` using `IsOpen.mem_nhds hχ (one_mem χ.ker)`. Establish `hce` using `isClosedEmbedding_translate r h1 hm hc hj`. Set `A : SB X → G → SB Y` to `fun Φ g => (χ g : ℂ) • ⟨fun y => Φ.1 (r (j y) g), Φ.2.1.comp_continuous (hce g).continuous, Φ.2.2.comp_isClosedEmbedding (hce g)⟩`. Establish `hA : ∀ Φ g y, (A Φ g).1 y = (χ g : ℂ) * Φ.1 (r (j y) g)` using `fun _ _ _ => rfl`.

Establish `hext : ∀ w w' : W, (∀ y, (ev w).1 y = (ev w').1 y) → w = w'` using `fun w w' h => ev.injective (Subtype.ext (funext h))`. Set `T : SB X →ₗ[ℂ] smoothPart (ind P σ)` to `{ toFun := fun Φ => ⟨⟨fun g => ev.symm (A Φ g), fun p g => hext _ _ fun y => by`. Rewrite using `[hev, ev.apply_symm_apply, ev.apply_symm_apply, hA, hA, hm, hsP, map_mul, Units.val_mul, mul_assoc]⟩,`. Use `mem_smoothPart_of_nhds (by filter_upwards [hχ', GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action G X r h1 hm hc Φ] with u hu hu'`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations.

Use `show ev.symm (A Φ (g * u)) = ev.symm (A Φ g)`. Use `congr 1`. Use `Subtype.ext (funext fun y => ?_)` and prove the remaining obligations. Rewrite using `[hA, hA, map_mul, hu, mul_one, hm, hu'])⟩`. Use the proof step `map_add' := fun Φ Ψ => Subtype.ext (Subtype.ext (funext fun g => by show ev.symm (A (Φ + Ψ) g) = ev.symm (A Φ g) + ev.symm (A Ψ g)`.

Rewrite using `[← map_add]`. Use `congr 1`. Conclude with `Subtype.ext (funext fun y => mul_add _ _ _)))`. Use the proof step `map_smul' := fun a Φ => Subtype.ext (Subtype.ext (funext fun g => by show ev.symm (A (a • Φ) g) = a • ev.symm (A Φ g)`. Rewrite using `[← map_smul]`.

Use `congr 1`. Conclude with `Subtype.ext (funext fun y => mul_left_comm _ _ _))) }`. Establish `hT : ∀ Φ g y, (ev ((T Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g)` using `fun Φ g y => by show (ev (ev.symm (A Φ g))).1 y = _`. Rewrite using `[ev.apply_symm_apply, hA]`. Establish `hinj : Function.Injective T` using `fun Φ Ψ h => Subtype.ext (funext fun x => by`.

Take `⟨y, c, -, rfl⟩` from `hs x`. Use `hT Φ c y` as an intermediate fact. Rewrite `this` using `[h, hT]`. Conclude with `(mul_left_cancel₀ (χ c).ne_zero this).symm)`. Establish `hsurj : Function.Surjective T` using `fun F => by`.

Establish `hF : ∀ᶠ u in 𝓝 (1 : G), ∀ x, F.1.1 (x * u) = F.1.1 x` using `Filter.mem_of_superset (IsOpen.mem_nhds F.2 (by simp)) fun g hg x => congrFun (congrArg Subtype.val (show ind P σ g F.1 = F.1 from hg)) x`. Take `⟨Φ, hΦ⟩` from `descend r h1 hm hc hj hK hs (fun g => (χ g : ℂ)⁻¹ • ev (F.1.1 g)) (by filter_upwards [hχ', hF] with u hu hu' g`. Rewrite using `[hu', map_mul, hu, mul_one])`. Use the proof step `(fun y g y' g' h => by`. Establish `h2 : r (j y) (g * g'⁻¹) = j y'` using `by rw [hm, h, ← hm, mul_inv_cancel, h1]`.

Establish `hp` using `hP _ _ _ h2`. Establish `h3 : s y ⟨_, hp⟩ = y'` using `hj.injective ((hsP y ⟨_, hp⟩).symm.trans h2)`. Establish `h4` using `F.1.2 ⟨_, hp⟩ g'`. Rewrite `h4` using `[show ((⟨_, hp⟩ : P) : G) * g' = g from inv_mul_cancel_right g g']`. Use `show (χ g : ℂ)⁻¹ * (ev (F.1.1 g)).1 y = (χ g' : ℂ)⁻¹ * (ev (F.1.1 g')).1 y'`.

Rewrite using `[h4, hev, h3]`. Simplify using `[← mul_assoc])`. Use `⟨Φ, Subtype.ext (Subtype.ext (funext fun g => hext _ _ fun y => ?_))⟩` and prove the remaining obligations. Rewrite using `[hT, hΦ]`. Conclude with `mul_inv_cancel_left₀ (χ g).ne_zero _`.

Conclude with `⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩`.
-/
theorem sb_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  intro G X Y W _ _ _ _ _ _ _ _ r h1 hm hc j hj P K hK hs s hsP hP χ hχ σ ev hev
  have hχ' : ∀ᶠ u in 𝓝 (1 : G), χ u = 1 := IsOpen.mem_nhds hχ (one_mem χ.ker)
  have hce := isClosedEmbedding_translate r h1 hm hc hj
  let A : SB X → G → SB Y := fun Φ g => (χ g : ℂ) • ⟨fun y => Φ.1 (r (j y) g),
    Φ.2.1.comp_continuous (hce g).continuous, Φ.2.2.comp_isClosedEmbedding (hce g)⟩
  have hA : ∀ Φ g y, (A Φ g).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun _ _ _ => rfl
  have hext : ∀ w w' : W, (∀ y, (ev w).1 y = (ev w').1 y) → w = w' := fun w w' h =>
    ev.injective (Subtype.ext (funext h))
  let T : SB X →ₗ[ℂ] smoothPart (ind P σ) :=
    { toFun := fun Φ => ⟨⟨fun g => ev.symm (A Φ g), fun p g => hext _ _ fun y => by
          rw [hev, ev.apply_symm_apply, ev.apply_symm_apply, hA, hA, hm, hsP, map_mul, Units.val_mul,
            mul_assoc]⟩,
        mem_smoothPart_of_nhds (by
          filter_upwards [hχ', GlobalTheory.schwartzBruhat_eventually_invariant_of_continuous_action G X r h1 hm hc Φ] with u hu hu'
          refine Subtype.ext (funext fun g => ?_)
          show ev.symm (A Φ (g * u)) = ev.symm (A Φ g)
          congr 1
          refine Subtype.ext (funext fun y => ?_)
          rw [hA, hA, map_mul, hu, mul_one, hm, hu'])⟩
      map_add' := fun Φ Ψ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (Φ + Ψ) g) = ev.symm (A Φ g) + ev.symm (A Ψ g)
        rw [← map_add]
        congr 1
        exact Subtype.ext (funext fun y => mul_add _ _ _)))
      map_smul' := fun a Φ => Subtype.ext (Subtype.ext (funext fun g => by
        show ev.symm (A (a • Φ) g) = a • ev.symm (A Φ g)
        rw [← map_smul]
        congr 1
        exact Subtype.ext (funext fun y => mul_left_comm _ _ _))) }
  have hT : ∀ Φ g y, (ev ((T Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := fun Φ g y => by
    show (ev (ev.symm (A Φ g))).1 y = _
    rw [ev.apply_symm_apply, hA]
  have hinj : Function.Injective T := fun Φ Ψ h => Subtype.ext (funext fun x => by
    obtain ⟨y, c, -, rfl⟩ := hs x
    have := hT Φ c y
    rw [h, hT] at this
    exact (mul_left_cancel₀ (χ c).ne_zero this).symm)
  have hsurj : Function.Surjective T := fun F => by
    have hF : ∀ᶠ u in 𝓝 (1 : G), ∀ x, F.1.1 (x * u) = F.1.1 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds F.2 (by simp)) fun g hg x =>
        congrFun (congrArg Subtype.val (show ind P σ g F.1 = F.1 from hg)) x
    obtain ⟨Φ, hΦ⟩ := descend r h1 hm hc hj hK hs (fun g => (χ g : ℂ)⁻¹ • ev (F.1.1 g))
      (by
        filter_upwards [hχ', hF] with u hu hu' g
        rw [hu', map_mul, hu, mul_one])
      (fun y g y' g' h => by
        have h2 : r (j y) (g * g'⁻¹) = j y' := by rw [hm, h, ← hm, mul_inv_cancel, h1]
        have hp := hP _ _ _ h2
        have h3 : s y ⟨_, hp⟩ = y' := hj.injective ((hsP y ⟨_, hp⟩).symm.trans h2)
        have h4 := F.1.2 ⟨_, hp⟩ g'
        rw [show ((⟨_, hp⟩ : P) : G) * g' = g from inv_mul_cancel_right g g'] at h4
        show (χ g : ℂ)⁻¹ * (ev (F.1.1 g)).1 y = (χ g' : ℂ)⁻¹ * (ev (F.1.1 g')).1 y'
        rw [h4, hev, h3]
        simp [← mul_assoc])
    refine ⟨Φ, Subtype.ext (Subtype.ext (funext fun g => hext _ _ fun y => ?_))⟩
    rw [hT, hΦ]
    exact mul_inv_cancel_left₀ (χ g).ne_zero _
  exact ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

end GlobalTheory.SBInduced
