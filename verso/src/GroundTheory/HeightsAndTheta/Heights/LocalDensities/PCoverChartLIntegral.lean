import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsCoverInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm.M MeasureTheory Topology

noncomputable section

namespace CoverChartLIntegral

variable {e : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Establish `h1 : IsOpen (hmaps.restrict '' (Subtype.val ⁻¹' O : Set M₀))` using `hcov.isOpenMap _ (hO.preimage continuous_subtype_val)`. Establish `h2` using `hΔ.isOpen_compl.isOpenMap_subtype_val _ h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨_, ⟨⟨x, hOM hx⟩, hx, rfl⟩, rfl⟩`. Introduce and unpack `⟨_, ⟨p, hp, rfl⟩, rfl⟩`. Conclude with `⟨p, hp, rfl⟩`.
-/
theorem isOpen_image_of_cover {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)}
    (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ) (hcov : IsCoveringMap hmaps.restrict)
    (O : Set X) (hO : IsOpen O) (hOM : O ⊆ M₀) : IsOpen (q '' O) := by
  have h1 : IsOpen (hmaps.restrict '' (Subtype.val ⁻¹' O : Set M₀)) :=
    hcov.isOpenMap _ (hO.preimage continuous_subtype_val)
  have h2 := hΔ.isOpen_compl.isOpenMap_subtype_val _ h1
  convert h2 using 1
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hOM hx⟩, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

/- English proof (translation)
Use `set f := hmaps.restrict with hf`. Use `set I := f ⁻¹' {(⟨z, hz⟩ : (Δᶜ : Set (Fin e → ℂ)))} with hI`. Take `⟨hdisc, U', hzU', hU'o, hfU'o, H, hH⟩` from `hcov ⟨z, hz⟩`. Establish `himg : Subtype.val '' I = M₀ ∩ q ⁻¹' {z}`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩`. Use `⟨p.2, ?_⟩` and prove the remaining obligations. Establish `hp' : f p = ⟨z, hz⟩` using `hp`. Use `show q p = z`.

Conclude with `congrArg Subtype.val hp'`. Introduce and unpack `⟨hx, hqx⟩`. Conclude with `⟨⟨x, hx⟩, Subtype.ext hqx, rfl⟩`. Establish `hIe : I.encard = d`. Rewrite using `[← Subtype.val_injective.encard_image, himg, hfib z hz]`.

Establish `: Finite I` using `(Set.finite_of_encard_eq_coe hIe).to_subtype`. Establish `hcard : Nat.card I = d`. Rewrite using `[Nat.card_coe_set_eq, Set.ncard_def, hIe]`. Both sides reduce to the same expression. Set `eI : Fin d ≃ I` to `((Finite.equivFin I).trans (finCongr hcard)).symm`.

Establish `hqH : ∀ p : f ⁻¹' U', q ((p : M₀) : X) = (H p).1.1.1` using `fun p => by`. Rewrite using `[hH p]`. Both sides reduce to the same expression. Set `W : Fin d → Set X` to `fun i => Subtype.val '' (Subtype.val '' {p : f ⁻¹' U' | (H p).2 = eI i} : Set M₀)`. Establish `hmemW : ∀ i x, x ∈ W i ↔ ∃ p : f ⁻¹' U', (H p).2 = eI i ∧ ((p : M₀) : X) = x`.

Introduce `i x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨p, hp, rfl⟩, rfl⟩`. Conclude with `⟨p, hp, rfl⟩`. Introduce and unpack `⟨p, hp, rfl⟩`.

Conclude with `⟨_, ⟨p, hp, rfl⟩, rfl⟩`. Use `⟨Subtype.val '' U', hΔ.isOpen_compl.isOpenMap_subtype_val _ hU'o, ⟨_, hzU', rfl⟩, fun u ⟨u', _, hu⟩ => hu ▸ u'.2, W, fun i => ?_, fun i x hx => ?_, fun i k hik => ?_, fun x hx hqx => ?_, fun i => ⟨fun x hx => ?_, fun x hx x' hx' hxx => ?_, fun u hu => ?_⟩⟩` and prove the remaining obligations. Establish `hS : IsOpen {p : f ⁻¹' U' | (H p).2 = eI i}` using `(isOpen_discrete {eI i}).preimage (continuous_snd.comp H.continuous)`. Conclude with `hM.isOpenMap_subtype_val _ (hfU'o.isOpenMap_subtype_val _ hS)`. Take `⟨p, -, rfl⟩` from `(hmemW i x).1 hx`.

Conclude with `(p : M₀).2`. Use `Set.disjoint_left.2 fun x hx hx' => hik ?_` and prove the remaining obligations. Take `⟨p, hp, rfl⟩` from `(hmemW i x).1 hx`. Take `⟨p', hp', hpp⟩` from `(hmemW k _).1 hx'`. Establish `: p' = p` using `Subtype.val_injective (Subtype.val_injective hpp)`.

Rewrite `hp'` using `[this, hp]`. Conclude with `eI.injective hp'`. Take `⟨u', hu', hu⟩` from `hqx`. Establish `hfx : f ⟨x, hx⟩ = u'` using `Subtype.ext hu.symm`. Set `p : f ⁻¹' U'` to `⟨⟨x, hx⟩, show f ⟨x, hx⟩ ∈ U' by rw [hfx]; exact hu'⟩`.

Use `⟨eI.symm (H p).2, (hmemW _ x).2 ⟨p, ?_, rfl⟩⟩` and prove the remaining obligations. Conclude with `(eI.apply_symm_apply _).symm`. Take `⟨p, -, rfl⟩` from `(hmemW i x).1 hx`. Rewrite using `[hqH p]`. Conclude with `⟨(H p).1.1, (H p).1.2, rfl⟩`.

Take `⟨p, hp, rfl⟩` from `(hmemW i x).1 hx`. Take `⟨p', hp', rfl⟩` from `(hmemW i x').1 hx'`. Rewrite `hxx` using `[hqH p, hqH p']`. Establish `h1 : (H p).1 = (H p').1` using `Subtype.val_injective (Subtype.val_injective hxx)`. Establish `h2 : H p = H p'` using `Prod.ext h1 (hp.trans hp'.symm)`.

Rewrite using `[H.injective h2]`. Take `⟨u', hu', rfl⟩` from `hu`. Set `p : f ⁻¹' U'` to `H.symm (⟨u', hu'⟩, eI i)`. Establish `hHp : H p = (⟨u', hu'⟩, eI i)` using `H.apply_symm_apply _`. Use `⟨((p : M₀) : X), (hmemW i _).2 ⟨p, by rw [hHp], rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hqH p, hHp]`.
-/
theorem exists_sheets {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)} {d : ℕ}
    (hM : IsOpen M₀) (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ)
    (hcov : IsCoveringMap hmaps.restrict) (hfib : ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d)
    (z : Fin e → ℂ) (hz : z ∉ Δ) :
    ∃ U : Set (Fin e → ℂ), IsOpen U ∧ z ∈ U ∧ U ⊆ Δᶜ ∧ ∃ W : Fin d → Set X,
      (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ M₀) ∧ Pairwise (Function.onFun Disjoint W) ∧
      (∀ x ∈ M₀, q x ∈ U → ∃ i, x ∈ W i) ∧ ∀ i, Set.BijOn q (W i) U := by
  set f := hmaps.restrict with hf
  set I := f ⁻¹' {(⟨z, hz⟩ : (Δᶜ : Set (Fin e → ℂ)))} with hI
  obtain ⟨hdisc, U', hzU', hU'o, hfU'o, H, hH⟩ := hcov ⟨z, hz⟩
  have himg : Subtype.val '' I = M₀ ∩ q ⁻¹' {z} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_⟩
      have hp' : f p = ⟨z, hz⟩ := hp
      show q p = z
      exact congrArg Subtype.val hp'
    · rintro ⟨hx, hqx⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hqx, rfl⟩
  have hIe : I.encard = d := by
    rw [← Subtype.val_injective.encard_image, himg, hfib z hz]
  have : Finite I := (Set.finite_of_encard_eq_coe hIe).to_subtype
  have hcard : Nat.card I = d := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hIe]; rfl
  let eI : Fin d ≃ I := ((Finite.equivFin I).trans (finCongr hcard)).symm
  have hqH : ∀ p : f ⁻¹' U', q ((p : M₀) : X) = (H p).1.1.1 := fun p => by
    rw [hH p]; rfl
  let W : Fin d → Set X := fun i =>
    Subtype.val '' (Subtype.val '' {p : f ⁻¹' U' | (H p).2 = eI i} : Set M₀)
  have hmemW : ∀ i x, x ∈ W i ↔ ∃ p : f ⁻¹' U', (H p).2 = eI i ∧ ((p : M₀) : X) = x := by
    intro i x
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  refine ⟨Subtype.val '' U', hΔ.isOpen_compl.isOpenMap_subtype_val _ hU'o, ⟨_, hzU', rfl⟩,
    fun u ⟨u', _, hu⟩ => hu ▸ u'.2, W, fun i => ?_, fun i x hx => ?_, fun i k hik => ?_,
    fun x hx hqx => ?_, fun i => ⟨fun x hx => ?_, fun x hx x' hx' hxx => ?_, fun u hu => ?_⟩⟩
  · have hS : IsOpen {p : f ⁻¹' U' | (H p).2 = eI i} :=
      (isOpen_discrete {eI i}).preimage (continuous_snd.comp H.continuous)
    exact hM.isOpenMap_subtype_val _ (hfU'o.isOpenMap_subtype_val _ hS)
  · obtain ⟨p, -, rfl⟩ := (hmemW i x).1 hx
    exact (p : M₀).2
  · refine Set.disjoint_left.2 fun x hx hx' => hik ?_
    obtain ⟨p, hp, rfl⟩ := (hmemW i x).1 hx
    obtain ⟨p', hp', hpp⟩ := (hmemW k _).1 hx'
    have : p' = p := Subtype.val_injective (Subtype.val_injective hpp)
    rw [this, hp] at hp'
    exact eI.injective hp'
  · obtain ⟨u', hu', hu⟩ := hqx
    have hfx : f ⟨x, hx⟩ = u' := Subtype.ext hu.symm
    let p : f ⁻¹' U' := ⟨⟨x, hx⟩, show f ⟨x, hx⟩ ∈ U' by rw [hfx]; exact hu'⟩
    refine ⟨eI.symm (H p).2, (hmemW _ x).2 ⟨p, ?_, rfl⟩⟩
    exact (eI.apply_symm_apply _).symm
  · obtain ⟨p, -, rfl⟩ := (hmemW i x).1 hx
    rw [hqH p]
    exact ⟨(H p).1.1, (H p).1.2, rfl⟩
  · obtain ⟨p, hp, rfl⟩ := (hmemW i x).1 hx
    obtain ⟨p', hp', rfl⟩ := (hmemW i x').1 hx'
    rw [hqH p, hqH p'] at hxx
    have h1 : (H p).1 = (H p').1 := Subtype.val_injective (Subtype.val_injective hxx)
    have h2 : H p = H p' := Prod.ext h1 (hp.trans hp'.symm)
    rw [H.injective h2]
  · obtain ⟨u', hu', rfl⟩ := hu
    let p : f ⁻¹' U' := H.symm (⟨u', hu'⟩, eI i)
    have hHp : H p = (⟨u', hu'⟩, eI i) := H.apply_symm_apply _
    refine ⟨((p : M₀) : X), (hmemW i _).2 ⟨p, by rw [hHp], rfl⟩, ?_⟩
    rw [hqH p, hHp]

/- English proof (translation)
Use `⟨Function.invFunOn q W, ?_, fun u hu => Function.invFunOn_pos (hbij.surjOn hu), fun x hx => hbij.injOn.leftInvOn_invFunOn hx⟩` and prove the remaining obligations. Rewrite using `[continuousOn_iff']`. Introduce `t ht`. Use `⟨q '' (W ∩ t), hopen _ (hW.inter ht) Set.inter_subset_left, ?_⟩` and prove the remaining obligations. Use extensionality with `u`.

Simplify using `only [Set.mem_inter_iff, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hut, hu⟩`. Establish `h` using `Function.invFunOn_pos (hbij.surjOn hu)`. Conclude with `⟨⟨_, ⟨h.1, hut⟩, h.2⟩, hu⟩`.

Introduce and unpack `⟨⟨x, ⟨hxW, hxt⟩, rfl⟩, hu⟩`. Use `⟨?_, hu⟩` and prove the remaining obligations. Use `show Function.invFunOn q W (q x) ∈ t`. Rewrite using `[hbij.injOn.leftInvOn_invFunOn hxW]`. Conclude with `hxt`.
-/
theorem exists_section [Nonempty X] {q : X → Fin e → ℂ} {W : Set X} {U : Set (Fin e → ℂ)}
    (hopen : ∀ O : Set X, IsOpen O → O ⊆ W → IsOpen (q '' O)) (hW : IsOpen W)
    (hbij : Set.BijOn q W U) :
    ∃ s : (Fin e → ℂ) → X, ContinuousOn s U ∧ (∀ u ∈ U, s u ∈ W ∧ q (s u) = u) ∧
      ∀ x ∈ W, s (q x) = x := by
  refine ⟨Function.invFunOn q W, ?_, fun u hu => Function.invFunOn_pos (hbij.surjOn hu),
    fun x hx => hbij.injOn.leftInvOn_invFunOn hx⟩
  rw [continuousOn_iff']
  intro t ht
  refine ⟨q '' (W ∩ t), hopen _ (hW.inter ht) Set.inter_subset_left, ?_⟩
  ext u
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hut, hu⟩
    have h := Function.invFunOn_pos (hbij.surjOn hu)
    exact ⟨⟨_, ⟨h.1, hut⟩, h.2⟩, hu⟩
  · rintro ⟨⟨x, ⟨hxW, hxt⟩, rfl⟩, hu⟩
    refine ⟨?_, hu⟩
    show Function.invFunOn q W (q x) ∈ t
    rw [hbij.injOn.leftInvOn_invFunOn hxW]
    exact hxt

/- English proof (translation)
Take `⟨U, hUo, hzU, hUΔ, W, hWo, hWM, hWd, hWc, hbij⟩` from `exists_sheets hM hΔ hmaps hcov hfib z.1 z.2`. Establish `hs` using `fun i => exists_section (fun O hO hOW => isOpen_image_of_cover hΔ hmaps hcov O hO (hOW.trans (hWM i))) (hWo i) (hbij i)`. Use `choose s hsc hsU hsW using hs`. Conclude with `⟨U, hUo, hzU, hUΔ, W, s, hWo, hWM, hWd, hWc, hsc, hsU, fun i x hx => ⟨(hbij i).mapsTo hx, hsW i x hx⟩⟩`.
-/
theorem exists_local_data [Nonempty X] {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)}
    {d : ℕ} (hM : IsOpen M₀) (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ)
    (hcov : IsCoveringMap hmaps.restrict) (hfib : ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d)
    (z : (Δᶜ : Set (Fin e → ℂ))) :
    ∃ U : Set (Fin e → ℂ), IsOpen U ∧ (z : Fin e → ℂ) ∈ U ∧ U ⊆ Δᶜ ∧ ∃ W : Fin d → Set X,
      ∃ s : Fin d → (Fin e → ℂ) → X,
      (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ M₀) ∧ Pairwise (Function.onFun Disjoint W) ∧
      (∀ x ∈ M₀, q x ∈ U → ∃ i, x ∈ W i) ∧ (∀ i, ContinuousOn (s i) U) ∧
      (∀ i, ∀ u ∈ U, s i u ∈ W i ∧ q (s i u) = u) ∧
      (∀ i, ∀ x ∈ W i, q x ∈ U ∧ s i (q x) = x) := by
  obtain ⟨U, hUo, hzU, hUΔ, W, hWo, hWM, hWd, hWc, hbij⟩ :=
    exists_sheets hM hΔ hmaps hcov hfib z.1 z.2
  have hs := fun i => exists_section
    (fun O hO hOW => isOpen_image_of_cover hΔ hmaps hcov O hO (hOW.trans (hWM i))) (hWo i) (hbij i)
  choose s hsc hsU hsW using hs
  exact ⟨U, hUo, hzU, hUΔ, W, s, hWo, hWM, hWd, hWc, hsc, hsU,
    fun i x hx => ⟨(hbij i).mapsTo hx, hsW i x hx⟩⟩

/- English proof (translation)
The claim follows from `analyticAt_pi_iff.2 fun i => hholo i j y hy`.
-/
theorem analyticAt_chart {A : FinHolAtlas e X} (j : Fin A.n) {q : X → Fin e → ℂ} {M₀ : Set X}
    (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) y :=
  analyticAt_pi_iff.2 fun i => hholo i j y hy

/- English proof (translation)
Use `set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W with hO`. Establish `hOo : IsOpen O` using `(A.chart j).isOpen_inter_preimage_symm hWo`. Establish `hc : ContinuousOn (q ∘ (A.chart j).symm) O` using `fun y hy => (analyticAt_chart j hholo ⟨hy.1, hWM hy.2⟩).continuousAt.continuousWithinAt`. Establish `h1 : MeasurableSet (O.domRestrict (q ∘ (A.chart j).symm) ⁻¹' B)` using `hc.domRestrict.measurable hB`. Establish `h2` using `hOo.measurableSet.subtype_image h1`.

Rewrite `h2` using `[Set.domRestrict_eq, Set.preimage_comp, Subtype.image_preimage_coe]`. Then use the resulting hypothesis.
-/
theorem measurableSet_piece {A : FinHolAtlas e X} (j : Fin A.n) {q : X → Fin e → ℂ} {M₀ : Set X}
    (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {W : Set X} (hWo : IsOpen W) (hWM : W ⊆ M₀)
    {B : Set (Fin e → ℂ)} (hB : MeasurableSet B) :
    MeasurableSet (((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) ∩
      (q ∘ (A.chart j).symm) ⁻¹' B) := by
  set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W with hO
  have hOo : IsOpen O := (A.chart j).isOpen_inter_preimage_symm hWo
  have hc : ContinuousOn (q ∘ (A.chart j).symm) O := fun y hy =>
    (analyticAt_chart j hholo ⟨hy.1, hWM hy.2⟩).continuousAt.continuousWithinAt
  have h1 : MeasurableSet (O.domRestrict (q ∘ (A.chart j).symm) ⁻¹' B) :=
    hc.domRestrict.measurable hB
  have h2 := hOo.measurableSet.subtype_image h1
  rwa [Set.domRestrict_eq, Set.preimage_comp, Subtype.image_preimage_coe] at h2

/- English proof (translation)
Use `set φ := A.chart j with hφ`. Use `set D := (φ.target ∩ φ.symm ⁻¹' W) ∩ (q ∘ φ.symm) ⁻¹' B with hD`. Establish `hDm : MeasurableSet D` using `measurableSet_piece j hholo hWo hWM hB`. Establish `hτ : ∀ y ∈ D, AnalyticAt ℂ (q ∘ φ.symm) y` using `fun y hy => analyticAt_chart j hholo ⟨hy.1.1, hWM hy.1.2⟩`. Establish `hder : ∀ y ∈ D, HasFDerivWithinAt (q ∘ φ.symm) ((fderiv ℂ (q ∘ φ.symm) y).restrictScalars ℝ) D y` using `fun y hy => ((hτ y hy).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`.

Establish `hinj : Set.InjOn (q ∘ φ.symm) D`. Introduce `y hy y' hy' hyy`. Establish `h1 : φ.symm y = φ.symm y'`. Rewrite using `[← (hsW _ hy.1.2).2, ← (hsW _ hy'.1.2).2]`. Conclude with `congrArg s hyy`.

Rewrite using `[← φ.right_inv hy.1.1, ← φ.right_inv hy'.1.1, h1]`. Use `set G : (Fin e → ℂ) → ENNReal := fun u => ENNReal.ofReal (χ.χ j (s u)) * g u with hG`. Establish `hcv` using `lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDm hder hinj G`. Use `set T := U ∩ s ⁻¹' φ.source with hT`. Establish `hTo : IsOpen T` using `hsc.isOpen_inter_preimage hUo φ.open_source`.

Establish `himg : (q ∘ φ.symm) '' D = B ∩ T`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `hU` using `hsW _ hy.1.2`.

Use `⟨hy.2, hU.1, ?_⟩` and prove the remaining obligations. Use `show s (q (φ.symm y)) ∈ φ.source`. Rewrite using `[hU.2]`. Conclude with `φ.map_target hy.1.1`. Introduce and unpack `⟨huB, huU, hus⟩`.

Establish `hus' : s u ∈ φ.source` using `hus`. Use `⟨φ (s u), ⟨⟨φ.map_source hus', ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show φ.symm (φ (s u)) ∈ W`. Rewrite using `[φ.left_inv hus']`. Conclude with `(hsU u (hBU huB)).1`.

Use `show q (φ.symm (φ (s u))) ∈ B`. Rewrite using `[φ.left_inv hus', (hsU u (hBU huB)).2]`. Conclude with `huB`. Use `show q (φ.symm (φ (s u))) = u`. Rewrite using `[φ.left_inv hus', (hsU u (hBU huB)).2]`.

Establish `hrest : ∫⁻ u in B \ T, G u = 0`. Rewrite using `[setLIntegral_congr_fun (hB.diff hTo.measurableSet) (g := fun _ => 0) ?_, lintegral_zero]`. Introduce and unpack `u ⟨huB, huT⟩`. Establish `hns : s u ∉ φ.source` using `fun h => huT ⟨hBU huB, h⟩`. Establish `h0 : χ.χ j (s u) = 0` using `image_eq_zero_of_notMem_tsupport fun h => hns (χ.tsupport_subset j h)`.

Simplify using `only [hG, h0, ENNReal.ofReal_zero, zero_mul]`. Establish `hBT : ∫⁻ u in B, G u = ∫⁻ u in B ∩ T, G u`. Rewrite using `[← lintegral_inter_add_sdiff G B hTo.measurableSet, hrest, add_zero]`. Rewrite using `[hBT, ← himg, hcv]`. Use `setLIntegral_congr_fun hDm fun y hy => ?_` and prove the remaining obligations.

Establish `hs : s (q (φ.symm y)) = φ.symm y` using `(hsW _ hy.1.2).2`. Simplify using `only [hG, degree_det_restrictScalars, Function.comp_apply]`. Rewrite using `[hs, abs_of_nonneg (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem piece_eq {A : FinHolAtlas e X} (χ : ChartPartition A) (j : Fin A.n) {q : X → Fin e → ℂ}
    {M₀ : Set X} (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {W : Set X} (hWo : IsOpen W)
    (hWM : W ⊆ M₀) {U B : Set (Fin e → ℂ)} (hUo : IsOpen U) (hB : MeasurableSet B)
    (hBU : B ⊆ U) {s : (Fin e → ℂ) → X} (hsc : ContinuousOn s U)
    (hsU : ∀ u ∈ U, s u ∈ W ∧ q (s u) = u) (hsW : ∀ x ∈ W, q x ∈ U ∧ s (q x) = x)
    (g : (Fin e → ℂ) → ENNReal) :
    ∫⁻ y in ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) ∩ (q ∘ (A.chart j).symm) ⁻¹' B,
        ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
          ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) =
      ∫⁻ u in B, ENNReal.ofReal (χ.χ j (s u)) * g u := by
  set φ := A.chart j with hφ
  set D := (φ.target ∩ φ.symm ⁻¹' W) ∩ (q ∘ φ.symm) ⁻¹' B with hD
  have hDm : MeasurableSet D := measurableSet_piece j hholo hWo hWM hB
  have hτ : ∀ y ∈ D, AnalyticAt ℂ (q ∘ φ.symm) y := fun y hy =>
    analyticAt_chart j hholo ⟨hy.1.1, hWM hy.1.2⟩
  have hder : ∀ y ∈ D, HasFDerivWithinAt (q ∘ φ.symm)
      ((fderiv ℂ (q ∘ φ.symm) y).restrictScalars ℝ) D y := fun y hy =>
    ((hτ y hy).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn (q ∘ φ.symm) D := by
    intro y hy y' hy' hyy
    have h1 : φ.symm y = φ.symm y' := by
      rw [← (hsW _ hy.1.2).2, ← (hsW _ hy'.1.2).2]
      exact congrArg s hyy
    rw [← φ.right_inv hy.1.1, ← φ.right_inv hy'.1.1, h1]
  set G : (Fin e → ℂ) → ENNReal := fun u => ENNReal.ofReal (χ.χ j (s u)) * g u with hG
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDm hder hinj G
  set T := U ∩ s ⁻¹' φ.source with hT
  have hTo : IsOpen T := hsc.isOpen_inter_preimage hUo φ.open_source
  have himg : (q ∘ φ.symm) '' D = B ∩ T := by
    ext u
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hU := hsW _ hy.1.2
      refine ⟨hy.2, hU.1, ?_⟩
      show s (q (φ.symm y)) ∈ φ.source
      rw [hU.2]
      exact φ.map_target hy.1.1
    · rintro ⟨huB, huU, hus⟩
      have hus' : s u ∈ φ.source := hus
      refine ⟨φ (s u), ⟨⟨φ.map_source hus', ?_⟩, ?_⟩, ?_⟩
      · show φ.symm (φ (s u)) ∈ W
        rw [φ.left_inv hus']
        exact (hsU u (hBU huB)).1
      · show q (φ.symm (φ (s u))) ∈ B
        rw [φ.left_inv hus', (hsU u (hBU huB)).2]
        exact huB
      · show q (φ.symm (φ (s u))) = u
        rw [φ.left_inv hus', (hsU u (hBU huB)).2]
  have hrest : ∫⁻ u in B \ T, G u = 0 := by
    rw [setLIntegral_congr_fun (hB.diff hTo.measurableSet) (g := fun _ => 0) ?_, lintegral_zero]
    rintro u ⟨huB, huT⟩
    have hns : s u ∉ φ.source := fun h => huT ⟨hBU huB, h⟩
    have h0 : χ.χ j (s u) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hns (χ.tsupport_subset j h)
    simp only [hG, h0, ENNReal.ofReal_zero, zero_mul]
  have hBT : ∫⁻ u in B, G u = ∫⁻ u in B ∩ T, G u := by
    rw [← lintegral_inter_add_sdiff G B hTo.measurableSet, hrest, add_zero]
  rw [hBT, ← himg, hcv]
  refine setLIntegral_congr_fun hDm fun y hy => ?_
  have hs : s (q (φ.symm y)) = φ.symm y := (hsW _ hy.1.2).2
  simp only [hG, degree_det_restrictScalars, Function.comp_apply]
  rw [hs, abs_of_nonneg (by positivity)]
  ring

/- English proof (translation)
Introduce `e X _ _ A χ q M₀ Δ d hyp g hg`. Take `⟨hM, hholo, hΔ, ⟨hmaps, hcov⟩, hfib⟩` from `hyp`. Break down `M₀.eq_empty_or_nonempty with hM0 | ⟨x0, hx0⟩` into its components or cases. Establish `hd : (d : ENNReal) * ∫⁻ z in Δᶜ, g z = 0`. Distinguish the cases in `hne : (Δᶜ : Set (Fin e → ℂ)).Nonempty`.

Take `⟨z, hz⟩` from `hne`. Establish `h` using `hfib z hz`. Rewrite `h` using `[hM0, Set.empty_inter, Set.encard_empty]`. Establish `hd0 : d = 0` using `by exact_mod_cast h.symm`. Simplify using `[hd0]`.

Rewrite using `[Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, lintegral_zero_measure, mul_zero]`. Rewrite using `[hd]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hM0, Set.preimage_empty, Set.inter_empty, Measure.restrict_empty, lintegral_zero_measure]`. Establish `: Nonempty X` using `⟨x0⟩`.

Establish `: Nonempty (Δᶜ : Set (Fin e → ℂ))` using `⟨⟨q x0, hmaps hx0⟩⟩`. Use `choose U hUo hzU hUΔ W s hWo hWM hWd hWc hsc hsU hsW using exists_local_data hM hΔ hmaps hcov hfib`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun z : (Δᶜ : Set (Fin e → ℂ)) => U z) fun z => hUo z`. Take `⟨c, hc⟩` from `Set.countable_iff_exists_subset_range.1 hTc`. Use `set Un : ℕ → Set (Fin e → ℂ) := fun n => U (c n) with hUn`.

Use `set B := disjointed Un with hBdef`. Establish `hBm : ∀ n, MeasurableSet (B n)` using `MeasurableSet.disjointed fun n => (hUo (c n)).measurableSet`. Establish `hBU : ∀ n, B n ⊆ U (c n)` using `disjointed_subset Un`. Establish `hBd : Pairwise (Function.onFun Disjoint B)` using `disjoint_disjointed Un`. Establish `hBcov : (⋃ n, B n) = Δᶜ`.

Rewrite using `[iUnion_disjointed]`. Use `subset_antisymm (Set.iUnion_subset fun n => hUΔ (c n)) fun z hz => ?_` and prove the remaining obligations. Establish `hz' : z ∈ ⋃ w, U w` using `Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩`. Rewrite `hz'` using `[← hTU]`. Take `⟨w, hw, hzw⟩` from `Set.mem_iUnion₂.1 hz'`.

Take `⟨n, rfl⟩` from `hc hw`. Conclude with `Set.mem_iUnion.2 ⟨n, hzw⟩`. Establish `hchart : ∀ j : Fin A.n, ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀, ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) * ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) = ∑' p : ℕ × Fin d, ∫⁻ …`. Introduce `j`. Use `set D : ℕ × Fin d → Set (Fin e → ℂ) := fun p => ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W (c p.1) p.2) ∩ (q ∘ (A.chart j).symm) ⁻¹' B p.1 with hD`.

Establish `hDu : (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀ = ⋃ p, D p`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hyt, hyM⟩`. Establish `hq : q ((A.chart j).symm y) ∈ ⋃ n, B n` using `by rw [hBcov]; exact hmaps hyM`.

Take `⟨n, hn⟩` from `Set.mem_iUnion.1 hq`. Take `⟨i, hi⟩` from `hWc (c n) _ hyM (hBU n hn)`. Conclude with `Set.mem_iUnion.2 ⟨(n, i), ⟨hyt, hi⟩, hn⟩`. Introduce `hy`. Take `⟨p, hp⟩` from `Set.mem_iUnion.1 hy`.

Conclude with `⟨hp.1.1, hWM _ _ hp.1.2⟩`. Establish `hDd : Pairwise (Function.onFun Disjoint D)`. Introduce and unpack `⟨n, i⟩ ⟨n', i'⟩ hne`. Use `Set.disjoint_left.2 fun y hy hy' => ?_` and prove the remaining obligations. Distinguish the cases in `hn : n = n'`.

Substitute `hn` using the available equality. Establish `hi : i ≠ i'` using `fun h => hne (by rw [h])`. Conclude with `Set.disjoint_left.1 (hWd (c n) hi) hy.1.2 hy'.1.2`. Conclude with `Set.disjoint_left.1 (hBd hn) hy.2 hy'.2`. Rewrite using `[hDu, lintegral_iUnion (fun p => measurableSet_piece j hholo (hWo _ _) (hWM _ _) (hBm _)) hDd]`.

Use `tsum_congr fun p => ?_` and prove the remaining obligations. Conclude with `piece_eq χ j hholo (hWo _ _) (hWM _ _) (hUo _) (hBm _) (hBU _) (hsc _ _) (hsU _ _) (hsW _ _) g`. Establish `hsum : ∀ p : ℕ × Fin d, ∑ j, ∫⁻ u in B p.1, ENNReal.ofReal (χ.χ j (s (c p.1) p.2 u)) * g u = ∫⁻ u in B p.1, g u`. Introduce `p`. Rewrite using `[← lintegral_finsetSum']`.

Use `lintegral_congr fun u => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun j _ => χ.nonneg j _, χ.sum_eq_one, ENNReal.ofReal_one, one_mul]`. Introduce `j _`. Establish `hχc : Continuous (χ.χ j)` using `PLC.continuous_of_smooth A (χ.smooth j)`. Establish `h1 : AEMeasurable (fun u => χ.χ j (s (c p.1) p.2 u)) (volume.restrict (U (c p.1)))` using `(hχc.comp_continuousOn (hsc _ _)).aemeasurable (hUo _).measurableSet`.

Conclude with `((ENNReal.measurable_ofReal.comp_aemeasurable h1).mono_measure (Measure.restrict_mono (hBU _) le_rfl)).mul hg.aemeasurable`. Repeatedly rewrite using `[hchart]`. Rewrite using `[← Summable.tsum_finsetSum fun j _ => ENNReal.summable]`. Repeatedly rewrite using `[hsum]`. Rewrite using `[ENNReal.tsum_prod']`.

Repeatedly rewrite using `[tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[ENNReal.tsum_mul_left, ← lintegral_iUnion hBm hBd, hBcov]`.
-/
theorem proof : CoverChartLIntegral.Statement := by
  intro e X _ _ A χ q M₀ Δ d hyp g hg
  obtain ⟨hM, hholo, hΔ, ⟨hmaps, hcov⟩, hfib⟩ := hyp
  rcases M₀.eq_empty_or_nonempty with hM0 | ⟨x0, hx0⟩
  · have hd : (d : ENNReal) * ∫⁻ z in Δᶜ, g z = 0 := by
      by_cases hne : (Δᶜ : Set (Fin e → ℂ)).Nonempty
      · obtain ⟨z, hz⟩ := hne
        have h := hfib z hz
        rw [hM0, Set.empty_inter, Set.encard_empty] at h
        have hd0 : d = 0 := by exact_mod_cast h.symm
        simp [hd0]
      · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, lintegral_zero_measure,
          mul_zero]
    rw [hd]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hM0, Set.preimage_empty, Set.inter_empty, Measure.restrict_empty, lintegral_zero_measure]
  have : Nonempty X := ⟨x0⟩
  have : Nonempty (Δᶜ : Set (Fin e → ℂ)) := ⟨⟨q x0, hmaps hx0⟩⟩
  choose U hUo hzU hUΔ W s hWo hWM hWd hWc hsc hsU hsW using
    exists_local_data hM hΔ hmaps hcov hfib

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : (Δᶜ : Set (Fin e → ℂ)) => U z) fun z => hUo z
  obtain ⟨c, hc⟩ := Set.countable_iff_exists_subset_range.1 hTc
  set Un : ℕ → Set (Fin e → ℂ) := fun n => U (c n) with hUn
  set B := disjointed Un with hBdef
  have hBm : ∀ n, MeasurableSet (B n) :=
    MeasurableSet.disjointed fun n => (hUo (c n)).measurableSet
  have hBU : ∀ n, B n ⊆ U (c n) := disjointed_subset Un
  have hBd : Pairwise (Function.onFun Disjoint B) := disjoint_disjointed Un
  have hBcov : (⋃ n, B n) = Δᶜ := by
    rw [iUnion_disjointed]
    refine subset_antisymm (Set.iUnion_subset fun n => hUΔ (c n)) fun z hz => ?_
    have hz' : z ∈ ⋃ w, U w := Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩
    rw [← hTU] at hz'
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 hz'
    obtain ⟨n, rfl⟩ := hc hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩

  have hchart : ∀ j : Fin A.n,
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀,
          ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
            ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
              (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) =
        ∑' p : ℕ × Fin d, ∫⁻ u in B p.1, ENNReal.ofReal (χ.χ j (s (c p.1) p.2 u)) * g u := by
    intro j
    set D : ℕ × Fin d → Set (Fin e → ℂ) := fun p =>
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W (c p.1) p.2) ∩
        (q ∘ (A.chart j).symm) ⁻¹' B p.1 with hD
    have hDu : (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀ = ⋃ p, D p := by
      ext y
      constructor
      · rintro ⟨hyt, hyM⟩
        have hq : q ((A.chart j).symm y) ∈ ⋃ n, B n := by rw [hBcov]; exact hmaps hyM
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hq
        obtain ⟨i, hi⟩ := hWc (c n) _ hyM (hBU n hn)
        exact Set.mem_iUnion.2 ⟨(n, i), ⟨hyt, hi⟩, hn⟩
      · intro hy
        obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hy
        exact ⟨hp.1.1, hWM _ _ hp.1.2⟩
    have hDd : Pairwise (Function.onFun Disjoint D) := by
      rintro ⟨n, i⟩ ⟨n', i'⟩ hne
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      by_cases hn : n = n'
      · subst hn
        have hi : i ≠ i' := fun h => hne (by rw [h])
        exact Set.disjoint_left.1 (hWd (c n) hi) hy.1.2 hy'.1.2
      · exact Set.disjoint_left.1 (hBd hn) hy.2 hy'.2
    rw [hDu, lintegral_iUnion (fun p => measurableSet_piece j hholo (hWo _ _) (hWM _ _) (hBm _))
      hDd]
    refine tsum_congr fun p => ?_
    exact piece_eq χ j hholo (hWo _ _) (hWM _ _) (hUo _) (hBm _) (hBU _) (hsc _ _) (hsU _ _)
      (hsW _ _) g

  have hsum : ∀ p : ℕ × Fin d,
      ∑ j, ∫⁻ u in B p.1, ENNReal.ofReal (χ.χ j (s (c p.1) p.2 u)) * g u = ∫⁻ u in B p.1, g u := by
    intro p
    rw [← lintegral_finsetSum']
    · refine lintegral_congr fun u => ?_
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun j _ => χ.nonneg j _, χ.sum_eq_one,
        ENNReal.ofReal_one, one_mul]
    · intro j _
      have hχc : Continuous (χ.χ j) := PLC.continuous_of_smooth A (χ.smooth j)
      have h1 : AEMeasurable (fun u => χ.χ j (s (c p.1) p.2 u)) (volume.restrict (U (c p.1))) :=
        (hχc.comp_continuousOn (hsc _ _)).aemeasurable (hUo _).measurableSet
      exact ((ENNReal.measurable_ofReal.comp_aemeasurable h1).mono_measure
        (Measure.restrict_mono (hBU _) le_rfl)).mul hg.aemeasurable
  simp_rw [hchart]
  rw [← Summable.tsum_finsetSum fun j _ => ENNReal.summable]
  simp_rw [hsum]
  rw [ENNReal.tsum_prod']
  simp_rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left, ← lintegral_iUnion hBm hBd, hBcov]

end CoverChartLIntegral

end

end GroundTheory.Heights₂.Heights.FourB
