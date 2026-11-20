import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

noncomputable section

namespace GlobalTheory.ArcPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Conv GlobalTheory.Points
open scoped LaurentSeries PowerSeries

def upI : Filter ℂ := comap Complex.im atTop

/- English proof (translation)
Rewrite using `[upI, eventually_comap]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨T, hT⟩` from `eventually_atTop.1 h`. Conclude with `⟨T, fun w hw => hT _ hw.le w rfl⟩`.

Introduce and unpack `⟨T, hT⟩ filter_upwards [eventually_gt_atTop T] with t ht w hw using hT w (hw ▸ ht)`.
-/
theorem eventually_upI {p : ℂ → Prop} : (∀ᶠ w in upI, p w) ↔ ∃ T : ℝ, ∀ w : ℂ, T < w.im → p w := by
  rw [upI, eventually_comap]
  constructor
  · intro h
    obtain ⟨T, hT⟩ := eventually_atTop.1 h
    exact ⟨T, fun w hw => hT _ hw.le w rfl⟩
  · rintro ⟨T, hT⟩
    filter_upwards [eventually_gt_atTop T] with t ht w hw using hT w (hw ▸ ht)

def sumRing (w : ℂ) : Subring (ℂ⸨X⸩ × ℂ) where
  carrier := {q | HasSum (fun m : ℤ => q.1.coeff m * eTwoPi w ^ m) q.2}
  mul_mem' {a b} ha hb := by
    have h := hasSum_mul_laurent (eTwoPi_ne_zero w) ha.summable hb.summable
    rw [lsum, lsum, ha.tsum_eq, hb.tsum_eq] at h
    exact h
  one_mem' := by simpa using hasSum_single_laurent 0 1 (eTwoPi w)
  add_mem' {a b} ha hb := by simpa [add_mul] using HasSum.add ha hb
  zero_mem' := by simpa using hasSum_zero
  neg_mem' {a} ha := by simpa using HasSum.neg ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_sumRing {w : ℂ} {s : ℂ⸨X⸩} {x : ℂ} :
    (s, x) ∈ sumRing w ↔ HasSum (fun m : ℤ => s.coeff m * eTwoPi w ^ m) x := Iff.rfl

/- English proof (translation)
Rewrite using `[← Prod.mk_add_mk]`. Conclude with `add_mem h h'`.
-/
theorem add_mem_sumRing {w : ℂ} {s t : ℂ⸨X⸩} {x y : ℂ} (h : (s, x) ∈ sumRing w)
    (h' : (t, y) ∈ sumRing w) : (s + t, x + y) ∈ sumRing w := by
  rw [← Prod.mk_add_mk]
  exact add_mem h h'

/- English proof (translation)
Rewrite using `[← Prod.mk_mul_mk]`. Conclude with `mul_mem h h'`.
-/
theorem mul_mem_sumRing {w : ℂ} {s t : ℂ⸨X⸩} {x y : ℂ} (h : (s, x) ∈ sumRing w)
    (h' : (t, y) ∈ sumRing w) : (s * t, x * y) ∈ sumRing w := by
  rw [← Prod.mk_mul_mk]
  exact mul_mem h h'

/- English proof (translation)
Rewrite using `[← Prod.neg_mk]`. Conclude with `neg_mem h`.
-/
theorem neg_mem_sumRing {w : ℂ} {s : ℂ⸨X⸩} {x : ℂ} (h : (s, x) ∈ sumRing w) :
    (-s, -x) ∈ sumRing w := by
  rw [← Prod.neg_mk]
  exact neg_mem h

/- English proof (translation)
The claim follows from `sumsAt_iff.symm`.
-/
theorem mem_sumRing_coe {w : ℂ} {s : ℂ⟦X⟧} {x : ℂ} :
    (HahnSeries.ofPowerSeries ℤ ℂ s, x) ∈ sumRing w ↔ SumsAt s w x := sumsAt_iff.symm

/- English proof (translation)
Take `⟨T, hT⟩` from `eventually_upI.1 h`. Conclude with `mem_convLaurent_iff_halfRing.2 ⟨T, fun w hw => (mem_sumRing.1 (hT w hw)).summable⟩`.
-/
theorem mem_convLaurent_of_eventually {s : ℂ⸨X⸩} {v : ℂ → ℂ}
    (h : ∀ᶠ w in upI, (s, v w) ∈ sumRing w) : s ∈ convLaurent := by
  obtain ⟨T, hT⟩ := eventually_upI.1 h
  exact mem_convLaurent_iff_halfRing.2 ⟨T, fun w hw => (mem_sumRing.1 (hT w hw)).summable⟩

/- English proof (translation)
Use `filter_upwards [h, eventually_upI.2 (exists_lsum_eTwoPi_ne_zero (mem_convLaurent_of_eventually h) h0)] with w h1 h2`. Rewrite `h2` using `[lsum, (mem_sumRing.1 h1).tsum_eq]`. Then use the resulting hypothesis.
-/
theorem eventually_ne_zero {s : ℂ⸨X⸩} {v : ℂ → ℂ}
    (h : ∀ᶠ w in upI, (s, v w) ∈ sumRing w) (h0 : s ≠ 0) : ∀ᶠ w in upI, v w ≠ 0 := by
  filter_upwards [h, eventually_upI.2
    (exists_lsum_eTwoPi_ne_zero (mem_convLaurent_of_eventually h) h0)] with w h1 h2
  rwa [lsum, (mem_sumRing.1 h1).tsum_eq] at h2

/- English proof (translation)
Establish `hs : s ∈ convLaurent`. Use `mul_mem (mem_convLaurent_of_eventually hst) (convLaurent.inv_mem (mem_convLaurent_of_eventually ht))` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right₀ h0]`. Then use the resulting hypothesis. Take `⟨T, hT⟩` from `mem_convLaurent_iff_halfRing.1 hs`. Use `filter_upwards [hst, ht, eventually_ne_zero ht h0, eventually_upI.2 ⟨T, hT⟩] with w h1 h2 h3 h4`.

Establish `h5 : (s, lsum s (eTwoPi w)) ∈ sumRing w` using `h4.hasSum`. Establish `h6` using `(mem_sumRing.1 (mul_mem_sumRing h5 h2)).unique (mem_sumRing.1 h1)`. Rewrite `h5` using `[mul_right_cancel₀ h3 h6]`. Then use the resulting hypothesis.
-/
theorem eventually_of_mul {s t : ℂ⸨X⸩} {v u : ℂ → ℂ}
    (hst : ∀ᶠ w in upI, (s * t, v w * u w) ∈ sumRing w) (ht : ∀ᶠ w in upI, (t, u w) ∈ sumRing w)
    (h0 : t ≠ 0) : ∀ᶠ w in upI, (s, v w) ∈ sumRing w := by
  have hs : s ∈ convLaurent := by
    have := mul_mem (mem_convLaurent_of_eventually hst)
      (convLaurent.inv_mem (mem_convLaurent_of_eventually ht))
    rwa [mul_inv_cancel_right₀ h0] at this
  obtain ⟨T, hT⟩ := mem_convLaurent_iff_halfRing.1 hs
  filter_upwards [hst, ht, eventually_ne_zero ht h0, eventually_upI.2 ⟨T, hT⟩] with w h1 h2 h3 h4
  have h5 : (s, lsum s (eTwoPi w)) ∈ sumRing w := h4.hasSum
  have h6 := (mem_sumRing.1 (mul_mem_sumRing h5 h2)).unique (mem_sumRing.1 h1)
  rwa [mul_right_cancel₀ h3 h6] at h5

/- English proof (translation)
Set `p : PrimeSpectrum ℂ⸨X⸩` to `default`. Take `⟨h, hle, hp⟩` from `hU.exists_basicOpen_le (V := V) ⟨y p, hV (x := p) trivial⟩ (hy (x := p) trivial)`. Establish `hyh : ⊤ ≤ y ⁻¹ᵁ Z.basicOpen h`. Introduce `q _`. Take `rfl : q = p` from `Subsingleton.elim (α := PrimeSpectrum ℂ⸨X⸩) _ _`.

Conclude with `hp`. Establish `h0 : valR y U h ≠ 0` using `((le_preimage_basicOpen_iff y hy h).1 hyh).ne_zero`. Establish `hzh : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ Z.basicOpen h` using `by filter_upwards [hz, eventually_ne_zero (hf h) h0] with w h1 h2`. Conclude with `(le_preimage_basicOpen_iff _ h1 h).2 h2.isUnit`. Use `⟨hzh.mono fun w hw => le_preimage_mono _ hle hw, fun f => ?_⟩` and prove the remaining obligations.

Use `haveI := hU.isLocalization_basicOpen h`. Take `⟨n, b, hb⟩` from `IsLocalization.Away.surj h ((Z.presheaf.map (homOfLE hle).op).hom f)`. Establish `hb' : (Z.presheaf.map (homOfLE hle).op).hom f * (Z.presheaf.map (homOfLE (Z.basicOpen_le h)).op).hom h ^ n = (Z.presheaf.map (homOfLE (Z.basicOpen_le h)).op).hom b` using `hb`. Establish `key : ∀ {C : Type} [CommRing C] (x : Sp C ⟶ Z), ⊤ ≤ x ⁻¹ᵁ Z.basicOpen h → valR x V f * valR x U h ^ n = valR x U b`. Introduce `C _ x hx`.

Rewrite using `[← valR_res x hle hx, ← valR_res x (Z.basicOpen_le h) hx, ← valR_res x (Z.basicOpen_le h) hx, ← valR_pow x _ hx, ← valR_mul x _ hx, hb']`. Use `eventually_of_mul (t := valR y U h ^ n) (u := fun w => valR (z w) U h ^ n) ?_ ?_ (pow_ne_zero n h0)` and prove the remaining obligations. Use `filter_upwards [hzh, hf b] with w h1 h2`. Rewrite using `[key y hyh, key _ h1]` and apply the resulting hypothesis. Use `filter_upwards [hf h] with w h1 using pow_mem h1 n`.
-/
theorem eventually_of_affine {Z : Scheme.{0}} (y : Sp ℂ⸨X⸩ ⟶ Z) (z : ℂ → (Sp ℂ ⟶ Z))
    {U : Z.Opens} (hU : IsAffineOpen U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (hz : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ U)
    (hf : ∀ f : Γ(Z, U), ∀ᶠ w in upI, (valR y U f, valR (z w) U f) ∈ sumRing w)
    {V : Z.Opens} (hV : ⊤ ≤ y ⁻¹ᵁ V) :
    (∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ V) ∧
      ∀ f : Γ(Z, V), ∀ᶠ w in upI, (valR y V f, valR (z w) V f) ∈ sumRing w := by
  let p : PrimeSpectrum ℂ⸨X⸩ := default
  obtain ⟨h, hle, hp⟩ := hU.exists_basicOpen_le (V := V) ⟨y p, hV (x := p) trivial⟩
    (hy (x := p) trivial)
  have hyh : ⊤ ≤ y ⁻¹ᵁ Z.basicOpen h := by
    intro q _
    obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum ℂ⸨X⸩) _ _
    exact hp
  have h0 : valR y U h ≠ 0 := ((le_preimage_basicOpen_iff y hy h).1 hyh).ne_zero
  have hzh : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ Z.basicOpen h := by
    filter_upwards [hz, eventually_ne_zero (hf h) h0] with w h1 h2
    exact (le_preimage_basicOpen_iff _ h1 h).2 h2.isUnit
  refine ⟨hzh.mono fun w hw => le_preimage_mono _ hle hw, fun f => ?_⟩
  haveI := hU.isLocalization_basicOpen h
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj h ((Z.presheaf.map (homOfLE hle).op).hom f)
  have hb' : (Z.presheaf.map (homOfLE hle).op).hom f *
      (Z.presheaf.map (homOfLE (Z.basicOpen_le h)).op).hom h ^ n =
      (Z.presheaf.map (homOfLE (Z.basicOpen_le h)).op).hom b := hb
  have key : ∀ {C : Type} [CommRing C] (x : Sp C ⟶ Z), ⊤ ≤ x ⁻¹ᵁ Z.basicOpen h →
      valR x V f * valR x U h ^ n = valR x U b := by
    intro C _ x hx
    rw [← valR_res x hle hx, ← valR_res x (Z.basicOpen_le h) hx, ← valR_res x (Z.basicOpen_le h) hx,
      ← valR_pow x _ hx, ← valR_mul x _ hx, hb']
  refine eventually_of_mul (t := valR y U h ^ n) (u := fun w => valR (z w) U h ^ n) ?_ ?_
    (pow_ne_zero n h0)
  · filter_upwards [hzh, hf b] with w h1 h2
    rwa [key y hyh, key _ h1]
  · filter_upwards [hf h] with w h1 using pow_mem h1 n

/- English proof (translation)
Use `haveI : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance`. Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U) le_top le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hU)`. Establish `hy' : ⊤ ≤ y ⁻¹ᵁ (g ⁻¹ᵁ U)` using `hy`. Establish `hz' : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ (g ⁻¹ᵁ U)` using `hz`. Use `eventually_of_affine y z (hU.preimage g) hy' hz' (fun r => ?_) hV` and prove the remaining obligations.

Establish `hr` using `(CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)`. Proceed by induction on `hr using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨a, rfl⟩ | ⟨b, rfl⟩` into its components or cases. Use `filter_upwards [hz', hf a] with w h1 h2`.

Rewrite using `[valR_appLE _ _ _ hy', valR_appLE _ _ _ h1]` and apply the resulting hypothesis. Take `⟨b, rfl⟩` from `(Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective b filter_upwards [hz', hzt] with w h1 h2`. Rewrite using `[valR_appLE _ _ _ hy', valR_appLE _ _ _ h1, hyt, h2]`. Establish `e1` using `valR_specMap (CommRingCat.ofHom τ) b`. Establish `e2` using `valR_specMap (CommRingCat.ofHom σ) b`.

Establish `e3 : (τ b, σ b) ∈ sumRing w`. Rewrite using `[hτ]`. Conclude with `mem_sumRing_coe.2 (hasSum_C _ _)`. Conclude with `(congrArg (· ∈ sumRing w) (congrArg₂ Prod.mk e1 e2)).mpr e3`. Consider the case `zero => filter_upwards [hz'] with w h1`.

Rewrite using `[valR_zero _ _ hy', valR_zero _ _ h1]`. Conclude with `zero_mem _`. Consider the case `one => filter_upwards [hz'] with w h1`. Rewrite using `[valR_one _ _ hy', valR_one _ _ h1]`. Conclude with `one_mem _`.

Consider the case `add a b _ _ ha hb => filter_upwards [hz', ha, hb] with w h1 h2 h3`. Rewrite using `[valR_add _ _ hy', valR_add _ _ h1]`. Conclude with `add_mem_sumRing h2 h3`. Consider the case `neg a _ ha => filter_upwards [hz', ha] with w h1 h2`. Rewrite using `[valR_neg _ _ hy', valR_neg _ _ h1]`.

Conclude with `neg_mem_sumRing h2`. Consider the case `mul a b _ _ ha hb => filter_upwards [hz', ha, hb] with w h1 h2 h3`. Rewrite using `[valR_mul _ _ hy', valR_mul _ _ h1]`. Conclude with `mul_mem_sumRing h2 h3`.
-/
theorem eventually_of_isPullback {Y Z : Scheme.{0}} {O F : Type} [CommRing O] [CommRing F]
    {β : O →+* F} {g : Z ⟶ Y} {s : Y ⟶ Sp O} {t : Z ⟶ Sp F} (H : IsPullback g t s (spMap β))
    (y : Sp ℂ⸨X⸩ ⟶ Z) (z : ℂ → (Sp ℂ ⟶ Z)) (σ : F →+* ℂ) (τ : F →+* ℂ⸨X⸩)
    (hτ : ∀ x, τ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (σ x)))
    (hyt : y ≫ t = spMap τ) (hzt : ∀ᶠ w in upI, z w ≫ t = spMap σ)
    {U : Y.Opens} (hU : IsAffineOpen U) (hy : ⊤ ≤ (y ≫ g) ⁻¹ᵁ U)
    (hz : ∀ᶠ w in upI, ⊤ ≤ (z w ≫ g) ⁻¹ᵁ U)
    (hf : ∀ f : Γ(Y, U), ∀ᶠ w in upI, (valR (y ≫ g) U f, valR (z w ≫ g) U f) ∈ sumRing w)
    {V : Z.Opens} (hV : ⊤ ≤ y ⁻¹ᵁ V) :
    (∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ V) ∧
      ∀ f : Γ(Z, V), ∀ᶠ w in upI, (valR y V f, valR (z w) V f) ∈ sumRing w := by
  haveI : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hy' : ⊤ ≤ y ⁻¹ᵁ (g ⁻¹ᵁ U) := hy
  have hz' : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ (g ⁻¹ᵁ U) := hz
  refine eventually_of_affine y z (hU.preimage g) hy' hz' (fun r => ?_) hV
  have hr := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · filter_upwards [hz', hf a] with w h1 h2
      rwa [valR_appLE _ _ _ hy', valR_appLE _ _ _ h1]
    · obtain ⟨b, rfl⟩ :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective b
      filter_upwards [hz', hzt] with w h1 h2
      rw [valR_appLE _ _ _ hy', valR_appLE _ _ _ h1, hyt, h2]
      have e1 := valR_specMap (CommRingCat.ofHom τ) b
      have e2 := valR_specMap (CommRingCat.ofHom σ) b
      have e3 : (τ b, σ b) ∈ sumRing w := by
        rw [hτ]
        exact mem_sumRing_coe.2 (hasSum_C _ _)
      exact (congrArg (· ∈ sumRing w) (congrArg₂ Prod.mk e1 e2)).mpr e3
  | zero =>
    filter_upwards [hz'] with w h1
    rw [valR_zero _ _ hy', valR_zero _ _ h1]
    exact zero_mem _
  | one =>
    filter_upwards [hz'] with w h1
    rw [valR_one _ _ hy', valR_one _ _ h1]
    exact one_mem _
  | add a b _ _ ha hb =>
    filter_upwards [hz', ha, hb] with w h1 h2 h3
    rw [valR_add _ _ hy', valR_add _ _ h1]
    exact add_mem_sumRing h2 h3
  | neg a _ ha =>
    filter_upwards [hz', ha] with w h1 h2
    rw [valR_neg _ _ hy', valR_neg _ _ h1]
    exact neg_mem_sumRing h2
  | mul a b _ _ ha hb =>
    filter_upwards [hz', ha, hb] with w h1 h2 h3
    rw [valR_mul _ _ hy', valR_mul _ _ h1]
    exact mul_mem_sumRing h2 h3

/- English proof (translation)
Establish `e : ⊤ ≤ k ⁻¹ᵁ k.opensRange` using `k.preimage_opensRange.ge`. Establish `hsurj : ∀ r : R, ∃ f : Γ(Z, k.opensRange), ∀ {C : Type} [CommRing C] (ψ : R →+* C), valR (spMap ψ ≫ k) k.opensRange f = ψ r`. Introduce `r`. Establish `hiso : IsIso (k.appLE k.opensRange ⊤ e)`. Use `k.isIso_app k.opensRange le_rfl` as an intermediate fact.

Rewrite using `[Scheme.Hom.appLE]`. Establish `: IsIso (homOfLE e)` using `(isIso_iff_of_thin _).2 ⟨homOfLE le_top⟩`. Use `infer_instance`. Take `⟨f, hf⟩` from `(asIso (k.appLE k.opensRange ⊤ e)).commRingCatIsoToRingEquiv.surjective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)`. Use `⟨f, fun ψ => ?_⟩` and prove the remaining obligations.

Rewrite using `[← valR_appLE _ k e (le_preimage_top _)]`. Conclude with `(congrArg (valR (spMap ψ) ⊤) hf).trans (valR_specMap (CommRingCat.ofHom ψ) r)`. Use `choose sec hsec using hsurj`. Take `⟨S, hS⟩` from `Algebra.FiniteType.out (R := F) (A := R)`. Use `filter_upwards [hzt, hz, (eventually_all_finset S).2 fun r _ => hf (sec r)] with w h1 h2 h3`.

Establish `hr : Set.range (z w) ⊆ Set.range k`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `h2 (x := q) trivial`. Set `ψ : R →+* ℂ` to `(Spec.preimage (IsOpenImmersion.lift k (z w) hr)).hom`. Establish `hψ : spMap ψ ≫ k = z w`.

Rewrite using `[← IsOpenImmersion.lift_fac k (z w) hr]`. Use `congr 1`. Conclude with `Spec.map_preimage _`. Establish `hσ : ∀ x, ψ (algebraMap F R x) = σ x`. Rewrite `h1` using `[← hψ, Category.assoc, hk, ← Spec.map_comp]`.

Conclude with `fun x => congrArg (fun a => a.hom x) (Spec.map_injective h1)`. Use `⟨ψ, hψ, hσ, fun f => ?_⟩` and prove the remaining obligations. Establish `hf' : f ∈ Algebra.adjoin F (S : Set R)` using `hS.ge Algebra.mem_top`. Proceed by induction on `hf' using Algebra.adjoin_induction with`. Consider the case `mem r hr'`.

Use `h3 r hr'` as an intermediate fact. Rewrite `this` using `[← hψ, hsec, hsec]`. Then use the resulting hypothesis. Consider the case `algebraMap x`. Rewrite using `[hφ, hσ]`. Conclude with `mem_sumRing_coe.2 (hasSum_C _ _)`.

Consider the case `add a b _ _ ha hb`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem_sumRing ha hb`. Consider the case `mul a b _ _ ha hb`. Rewrite using `[map_mul, map_mul]`.

Conclude with `mul_mem_sumRing ha hb`.
-/
theorem eventually_chart {Z : Scheme.{0}} {F R : Type} [CommRing F] [CommRing R] [Algebra F R]
    [Algebra.FiniteType F R] (t : Z ⟶ Sp F) (k : Sp R ⟶ Z) [IsOpenImmersion k]
    (hk : k ≫ t = spMap (algebraMap F R)) (φ : R →+* ℂ⸨X⸩) (σ : F →+* ℂ)
    (hφ : ∀ x, φ (algebraMap F R x) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (σ x)))
    (z : ℂ → (Sp ℂ ⟶ Z)) (hzt : ∀ᶠ w in upI, z w ≫ t = spMap σ)
    (hz : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ k.opensRange)
    (hf : ∀ f : Γ(Z, k.opensRange), ∀ᶠ w in upI,
      (valR (spMap φ ≫ k) k.opensRange f, valR (z w) k.opensRange f) ∈ sumRing w) :
    ∀ᶠ w in upI, ∃ ψ : R →+* ℂ, spMap ψ ≫ k = z w ∧ (∀ x, ψ (algebraMap F R x) = σ x) ∧
      ∀ f, (φ f, ψ f) ∈ sumRing w := by
  have e : ⊤ ≤ k ⁻¹ᵁ k.opensRange := k.preimage_opensRange.ge
  have hsurj : ∀ r : R, ∃ f : Γ(Z, k.opensRange), ∀ {C : Type} [CommRing C] (ψ : R →+* C),
      valR (spMap ψ ≫ k) k.opensRange f = ψ r := by
    intro r
    have hiso : IsIso (k.appLE k.opensRange ⊤ e) := by
      have := k.isIso_app k.opensRange le_rfl
      rw [Scheme.Hom.appLE]
      have : IsIso (homOfLE e) := (isIso_iff_of_thin _).2 ⟨homOfLE le_top⟩
      infer_instance
    obtain ⟨f, hf⟩ := (asIso (k.appLE k.opensRange ⊤ e)).commRingCatIsoToRingEquiv.surjective
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
    refine ⟨f, fun ψ => ?_⟩
    rw [← valR_appLE _ k e (le_preimage_top _)]
    exact (congrArg (valR (spMap ψ) ⊤) hf).trans (valR_specMap (CommRingCat.ofHom ψ) r)
  choose sec hsec using hsurj
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := F) (A := R)
  filter_upwards [hzt, hz, (eventually_all_finset S).2 fun r _ => hf (sec r)] with w h1 h2 h3
  have hr : Set.range (z w) ⊆ Set.range k := by
    rintro _ ⟨q, rfl⟩
    exact h2 (x := q) trivial
  let ψ : R →+* ℂ := (Spec.preimage (IsOpenImmersion.lift k (z w) hr)).hom
  have hψ : spMap ψ ≫ k = z w := by
    rw [← IsOpenImmersion.lift_fac k (z w) hr]
    congr 1
    exact Spec.map_preimage _
  have hσ : ∀ x, ψ (algebraMap F R x) = σ x := by
    rw [← hψ, Category.assoc, hk, ← Spec.map_comp] at h1
    exact fun x => congrArg (fun a => a.hom x) (Spec.map_injective h1)
  refine ⟨ψ, hψ, hσ, fun f => ?_⟩
  have hf' : f ∈ Algebra.adjoin F (S : Set R) := hS.ge Algebra.mem_top
  induction hf' using Algebra.adjoin_induction with
  | mem r hr' =>
    have := h3 r hr'
    rwa [← hψ, hsec, hsec] at this
  | algebraMap x =>
    rw [hφ, hσ]
    exact mem_sumRing_coe.2 (hasSum_C _ _)
  | add a b _ _ ha hb =>
    rw [map_add, map_add]
    exact add_mem_sumRing ha hb
  | mul a b _ _ ha hb =>
    rw [map_mul, map_mul]
    exact mul_mem_sumRing ha hb

end GlobalTheory.ArcPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ p j φ hσ hχ _ hj hjs hφ`. Establish `hex : ∀ w : ℂ, Ha.T < w.im → ∃ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ yF ≫ pullback.snd _ _ = spMap σ`. Introduce `w hw`. Use `⟨pullback.lift (Fu.u Ha.i (Ha.Pw w)) (spMap σ) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩` and prove the remaining obligations. Rewrite using `[Fu.over_σ _ _ (Ha.period w hw), ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `hex' : ∀ w : ℂ, ∃ yF : Sp ℂ ⟶ Xo.XF c, Ha.T < w.im → yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ yF ≫ pullback.snd _ _ = spMap σ`. Introduce `w`. Distinguish the cases in `hw : Ha.T < w.im`. Take `⟨yF, h⟩` from `hex w hw`.

Conclude with `⟨yF, fun _ => h⟩`. Take `⟨yF, -⟩` from `hex (((Ha.T + 1 : ℝ) : ℂ) * Complex.I) (by simp)`. Conclude with `⟨yF, fun h => absurd h hw⟩`. Use `choose yF hyF using hex'`. Establish `hyF'` using `GlobalTheory.ArcPoint.eventually_upI.2 ⟨Ha.T, hyF⟩`.

Use `haveI := Y.jQ_open`. Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Y.X) (U := ⊤) (x := χ (IsLocalRing.closedPoint (PowerSeries ℂ))) trivial`. Establish `hχU : ⊤ ≤ χ ⁻¹ᵁ U` using `(Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (PowerSeries ℂ)) χ hxU).ge`. Establish `hpt : ∀ f : Γ(Y.X, U), ∀ᶠ w in GlobalTheory.ArcPoint.upI, ⊤ ≤ (yF w ≫ Y.j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (yF w ≫ Y.j) U f)`. Introduce `f`.

Use `filter_upwards [hyF', GlobalTheory.ArcPoint.eventually_upI.2 (Ha.point U f hχU)] with w h1 h2`. Conclude with `h2 _ h1.1 h1.2`. Establish `hk : (j ≫ Y.jQ) ≫ pullback.snd _ _ = spMap (algebraMap c.F p.R)`. Rewrite using `[Category.assoc, Y.jQ_over, hjs]`. Establish `hφσ : ∀ x, φ.toRingHom (algebraMap c.F p.R x) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (σ x))` using `fun x => (φ.commutes x).trans (hσ x)`.

Establish `hzt : ∀ᶠ w in GlobalTheory.ArcPoint.upI, (yF w ≫ Y.jQ) ≫ pullback.snd _ _ = spMap σ` using `hyF'.mono fun w h => by rw [Category.assoc, Y.jQ_over, h.2]`. Establish `hφ' : (spMap φ.toRingHom ≫ j ≫ Y.jQ) ≫ pullback.fst _ _ = spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ`. Rewrite using `[← hφ]`. Simplify using `only [Category.assoc, Model.j]`. Establish `hz' : ∀ w, (yF w ≫ Y.jQ) ≫ pullback.fst _ _ = yF w ≫ Y.j` using `fun w => Category.assoc _ _ _`.

Take `⟨h1, h2⟩` from `GlobalTheory.ArcPoint.eventually_of_isPullback (IsPullback.of_hasPullback Y.s (spMap β)) (spMap φ.toRingHom ≫ j ≫ Y.jQ) (fun w => yF w ≫ Y.jQ) σ (φ.toRingHom.comp (algebraMap c.F p.R)) hφσ (by rw [Category.assoc, hk, ← Spec.map_comp]; rfl) hzt hU (by rw [hφ']; exact fun q _ => hχ …`. Rewrite using `[hφ', hz', GlobalTheory.Points.valR_spMap_comp _ _ _ hχU]`. Conclude with `GlobalTheory.ArcPoint.mem_sumRing_coe.2 h.2)`. Use the proof step `(V := (j ≫ Y.jQ).opensRange) (fun q _ => ⟨spMap φ.toRingHom q, rfl⟩)`. Establish `h3` using `GlobalTheory.ArcPoint.eventually_chart (pullback.snd Y.s (spMap β)) (j ≫ Y.jQ) hk φ.toRingHom σ hφσ (fun w => yF w ≫ Y.jQ) hzt h1 h2`.

Use `GlobalTheory.ArcPoint.eventually_upI.1 ?_` and prove the remaining obligations. Use `filter_upwards [h3, hyF'] with w ⟨ψ, e1, e2, e3⟩ h`. Use `⟨{ toRingHom := (show p.R →+* CAt σ from ψ), commutes' := e2 }, ?_, e3⟩` and prove the remaining obligations. Establish `e4 : spMap ψ ≫ j = yF w`. Rewrite using `[← cancel_mono Y.jQ, Category.assoc]`.

Conclude with `e1`. Establish `e5 : spMap ψ ≫ j ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w)`. Rewrite using `[← Category.assoc, e4, h.1]`. Conclude with `e5`.
-/
theorem GlobalTheory.ArcPoint.chart_coordinates_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (φ : p.R →ₐ[c.F] ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F p.R) → spMap φ.toRingHom ≫ j ≫ Y.j = spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∃ ψ : p.R →ₐ[c.F] CAt σ, spMap ψ.toRingHom ≫ j ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ ∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (toC (ψ f)) := by
  intro E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ p j φ hσ hχ _ hj hjs hφ
  have hex : ∀ w : ℂ, Ha.T < w.im → ∃ yF : Sp ℂ ⟶ Xo.XF c,
      yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ yF ≫ pullback.snd _ _ = spMap σ := by
    intro w hw
    refine ⟨pullback.lift (Fu.u Ha.i (Ha.Pw w)) (spMap σ) ?_, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
    rw [Fu.over_σ _ _ (Ha.period w hw), ← Spec.map_comp]
    rfl
  have hex' : ∀ w : ℂ, ∃ yF : Sp ℂ ⟶ Xo.XF c, Ha.T < w.im →
      yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ yF ≫ pullback.snd _ _ = spMap σ := by
    intro w
    by_cases hw : Ha.T < w.im
    · obtain ⟨yF, h⟩ := hex w hw
      exact ⟨yF, fun _ => h⟩
    · obtain ⟨yF, -⟩ := hex (((Ha.T + 1 : ℝ) : ℂ) * Complex.I) (by simp)
      exact ⟨yF, fun h => absurd h hw⟩
  choose yF hyF using hex'
  have hyF' := GlobalTheory.ArcPoint.eventually_upI.2 ⟨Ha.T, hyF⟩
  haveI := Y.jQ_open
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y.X) (U := ⊤)
    (x := χ (IsLocalRing.closedPoint (PowerSeries ℂ))) trivial
  have hχU : ⊤ ≤ χ ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (PowerSeries ℂ)) χ hxU).ge
  have hpt : ∀ f : Γ(Y.X, U), ∀ᶠ w in GlobalTheory.ArcPoint.upI, ⊤ ≤ (yF w ≫ Y.j) ⁻¹ᵁ U ∧
      SumsAt (valR χ U f) w (valAt' (yF w ≫ Y.j) U f) := by
    intro f
    filter_upwards [hyF', GlobalTheory.ArcPoint.eventually_upI.2 (Ha.point U f hχU)] with w h1 h2
    exact h2 _ h1.1 h1.2
  have hk : (j ≫ Y.jQ) ≫ pullback.snd _ _ = spMap (algebraMap c.F p.R) := by
    rw [Category.assoc, Y.jQ_over, hjs]
  have hφσ : ∀ x, φ.toRingHom (algebraMap c.F p.R x) =
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (σ x)) := fun x => (φ.commutes x).trans (hσ x)
  have hzt : ∀ᶠ w in GlobalTheory.ArcPoint.upI, (yF w ≫ Y.jQ) ≫ pullback.snd _ _ = spMap σ :=
    hyF'.mono fun w h => by rw [Category.assoc, Y.jQ_over, h.2]
  have hφ' : (spMap φ.toRingHom ≫ j ≫ Y.jQ) ≫ pullback.fst _ _ =
      spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ := by
    rw [← hφ]
    simp only [Category.assoc, Model.j]
  have hz' : ∀ w, (yF w ≫ Y.jQ) ≫ pullback.fst _ _ = yF w ≫ Y.j := fun w => Category.assoc _ _ _
  obtain ⟨h1, h2⟩ := GlobalTheory.ArcPoint.eventually_of_isPullback (IsPullback.of_hasPullback Y.s (spMap β))
    (spMap φ.toRingHom ≫ j ≫ Y.jQ) (fun w => yF w ≫ Y.jQ) σ
    (φ.toRingHom.comp (algebraMap c.F p.R)) hφσ
    (by rw [Category.assoc, hk, ← Spec.map_comp]; rfl) hzt hU
    (by rw [hφ']; exact fun q _ => hχU (x := spMap _ q) trivial)
    ((hpt 0).mono fun w h => by rw [hz']; exact h.1)
    (fun f => (hpt f).mono fun w h => by
      rw [hφ', hz', GlobalTheory.Points.valR_spMap_comp _ _ _ hχU]
      exact GlobalTheory.ArcPoint.mem_sumRing_coe.2 h.2)
    (V := (j ≫ Y.jQ).opensRange) (fun q _ => ⟨spMap φ.toRingHom q, rfl⟩)
  have h3 := GlobalTheory.ArcPoint.eventually_chart (pullback.snd Y.s (spMap β)) (j ≫ Y.jQ) hk φ.toRingHom σ
    hφσ (fun w => yF w ≫ Y.jQ) hzt h1 h2
  refine GlobalTheory.ArcPoint.eventually_upI.1 ?_
  filter_upwards [h3, hyF'] with w ⟨ψ, e1, e2, e3⟩ h
  refine ⟨{ toRingHom := (show p.R →+* CAt σ from ψ), commutes' := e2 }, ?_, e3⟩
  have e4 : spMap ψ ≫ j = yF w := by
    rw [← cancel_mono Y.jQ, Category.assoc]
    exact e1
  have e5 : spMap ψ ≫ j ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) := by
    rw [← Category.assoc, e4, h.1]
  exact e5
