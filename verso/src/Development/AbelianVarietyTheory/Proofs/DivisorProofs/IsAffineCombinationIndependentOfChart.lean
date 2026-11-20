import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChartStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

open GlobalTheory.SecGlue

namespace GlobalTheory.SecGlue.ChartIndep

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {f g : Sp S ⟶ Y}
    (e : f = g) (hf : f ⁻¹ᵁ V = ⊤) (hg : g ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hf x = chartHom V g hg x := by
  subst e; rfl

/- English proof (translation)
Unfold `chartHom`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE (spMap g) f V ⊤ ⊤ hf.ge le_top]`. Establish `h1 : Scheme.Hom.appLE (spMap g) ⊤ ⊤ le_top = (spMap g).appTop`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.

Establish `h2` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)`. Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `((Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom.comp ((Spec.map (CommRingCat.ofHom g)).appTop.hom.comp (f.appLE V ⊤ hf.ge).hom)) x = _`. Rewrite using `[← RingHom.comp_assoc, ← CommRingCat.hom_comp, h2]`. Both sides reduce to the same expression.
-/
theorem chartHom_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (f : Sp S ⟶ Y) (hf : f ⁻¹ᵁ V = ⊤) (hgf : (spMap g ≫ f) ⁻¹ᵁ V = ⊤)
    (x : Γ(Y, V)) : chartHom V (spMap g ≫ f) hgf x = g (chartHom V f hf x) := by
  unfold chartHom
  rw [← Scheme.Hom.appLE_comp_appLE (spMap g) f V ⊤ ⊤ hf.ge le_top]
  have h1 : Scheme.Hom.appLE (spMap g) ⊤ ⊤ le_top = (spMap g).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  rw [h1]
  change ((Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom.comp
    ((Spec.map (CommRingCat.ofHom g)).appTop.hom.comp (f.appLE V ⊤ hf.ge).hom)) x = _
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, h2]
  rfl

/- English proof (translation)
Unfold `chartHom`. Rewrite using `[← Scheme.Hom.map_appLE f hW.ge (homOfLE hWV).op]`. Both sides reduce to the same expression.
-/
theorem chartHom_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) (hV : f ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hV x = chartHom W f hW (Y.presheaf.map (homOfLE hWV).op x) := by
  unfold chartHom
  rw [← Scheme.Hom.map_appLE f hW.ge (homOfLE hWV).op]
  rfl

/- English proof (translation)
The claim follows from `top_le_iff.mp (hW.ge.trans (Scheme.Hom.preimage_mono f hWV))`.
-/
theorem lands_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) : f ⁻¹ᵁ V = ⊤ :=
  top_le_iff.mp (hW.ge.trans (Scheme.Hom.preimage_mono f hWV))

/- English proof (translation)
Take `⟨hu, hc, hw, hx⟩` from `h`. Use `⟨lands_mono hWV u hu, lands_mono hWV c hc, fun i => lands_mono hWV (w i) (hw i), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[chartHom_mono hWV c hc, chartHom_mono hWV u hu, hx]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[chartHom_mono hWV (w i) (hw i)]`.
-/
theorem comb_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (h : IsCombIn W u c w a) : IsCombIn V u c w a := by
  obtain ⟨hu, hc, hw, hx⟩ := h
  refine ⟨lands_mono hWV u hu, lands_mono hWV c hc, fun i => lands_mono hWV (w i) (hw i), fun x => ?_⟩
  rw [chartHom_mono hWV c hc, chartHom_mono hWV u hu, hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartHom_mono hWV (w i) (hw i)]

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue.ChartIndep

variable {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (s : S)

noncomputable def locMap : Localization.Away s →+* Localization ((Submonoid.powers s).map q) :=
  IsLocalization.map (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ q (Submonoid.le_comap_map _)

/- English proof (translation)
The claim follows from `IsLocalization.map_eq (M := Submonoid.powers s) (S := Localization.Away s) (T := (Submonoid.powers s).map q) _ x`.
-/
theorem locMap_alg (x : S) :
    locMap q s (algebraMap S (Localization.Away s) x) =
      algebraMap T (Localization ((Submonoid.powers s).map q)) (q x) :=
  IsLocalization.map_eq (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ x

/- English proof (translation)
The claim follows from `IsLocalization.map_surjective_of_surjective (Submonoid.powers s) (Localization.Away s) (Localization ((Submonoid.powers s).map q)) hq`.
-/
theorem locMap_surj (hq : Function.Surjective q) : Function.Surjective (locMap q s) :=
  IsLocalization.map_surjective_of_surjective (Submonoid.powers s) (Localization.Away s)
    (Localization ((Submonoid.powers s).map q)) hq

/- English proof (translation)
Establish `hprod : ∀ a b : S, a ∈ RingHom.ker q → b ∈ RingHom.ker q → a * b = 0`. Introduce `a b ha hb`. Establish `: a * b ∈ RingHom.ker q ^ 2` using `by rw [pow_two]; exact Ideal.mul_mem_mul ha hb`. Rewrite `this` using `[hk]`. Conclude with `(Submodule.mem_bot S).mp this`.

Establish `hform : ∀ x ∈ RingHom.ker (locMap q s), ∃ (k : S) (m : Submonoid.powers s), k ∈ RingHom.ker q ∧ x = IsLocalization.mk' (Localization.Away s) k m`. Introduce `x hx`. Take `⟨⟨k, m⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers s) x`. Rewrite `hx` using `[RingHom.mem_ker]`. Simplify using `only [locMap] at hx`.

Rewrite `hx` using `[IsLocalization.map_mk' (M := Submonoid.powers s) (S := Localization.Away s) (T := (Submonoid.powers s).map q), IsLocalization.mk'_eq_zero_iff]`. Take `⟨⟨m', hm'⟩, hm'k⟩` from `hx`. Take `⟨m'', hm'', rfl⟩` from `Submonoid.mem_map.mp hm'`. Use `⟨m'' * k, ⟨m'', hm''⟩ * m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_mul]`.

Conclude with `hm'k`. Simplify using `only`. Rewrite using `[IsLocalization.mk'_eq_iff_eq]`. Simplify using `only [Submonoid.coe_mul]`. Put the polynomial expressions in normal form.

Rewrite using `[pow_two, eq_bot_iff, Ideal.mul_le]`. Introduce `x hx y hy`. Take `⟨k, m, hk1, rfl⟩` from `hform x hx`. Take `⟨k', m', hk2, rfl⟩` from `hform y hy`. Rewrite using `[← IsLocalization.mk'_mul, hprod k k' hk1 hk2, IsLocalization.mk'_zero]`.

Conclude with `Submodule.zero_mem _`.
-/
theorem locMap_ker (hk : RingHom.ker q ^ 2 = ⊥) : RingHom.ker (locMap q s) ^ 2 = ⊥ := by
  have hprod : ∀ a b : S, a ∈ RingHom.ker q → b ∈ RingHom.ker q → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ RingHom.ker q ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hk] at this
    exact (Submodule.mem_bot S).mp this

  have hform : ∀ x ∈ RingHom.ker (locMap q s), ∃ (k : S) (m : Submonoid.powers s),
      k ∈ RingHom.ker q ∧ x = IsLocalization.mk' (Localization.Away s) k m := by
    intro x hx
    obtain ⟨⟨k, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) x
    rw [RingHom.mem_ker] at hx
    simp only [locMap] at hx
    rw [IsLocalization.map_mk' (M := Submonoid.powers s) (S := Localization.Away s)
      (T := (Submonoid.powers s).map q), IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨m', hm'⟩, hm'k⟩ := hx
    obtain ⟨m'', hm'', rfl⟩ := Submonoid.mem_map.mp hm'
    refine ⟨m'' * k, ⟨m'', hm''⟩ * m, ?_, ?_⟩
    · rw [RingHom.mem_ker, map_mul]; exact hm'k
    · simp only
      rw [IsLocalization.mk'_eq_iff_eq]
      simp only [Submonoid.coe_mul]
      ring_nf
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨k, m, hk1, rfl⟩ := hform x hx
  obtain ⟨k', m', hk2, rfl⟩ := hform y hy
  rw [← IsLocalization.mk'_mul, hprod k k' hk1 hk2, IsLocalization.mk'_zero]
  exact Submodule.zero_mem _

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue.ChartIndep

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_preimage]`. Use `top_le_iff.mp fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Hom.mem_preimage]`. Apply `hs` to reduce the goal to its premises. Introduce `hx`.

Express the relevant statement in the definitionally equal form `s ∈ Ideal.comap (algebraMap S (Localization.Away s)) x.asIdeal at hx`. Rewrite `hx` using `[Ideal.mem_comap]`. Conclude with `x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.Away.algebraMap_isUnit s))`.
-/
theorem lands_loc {Y : Scheme.{0}} (W : Y.Opens) {S : Type} [CommRing S] (s : S) (f : Sp S ⟶ Y)
    (hs : ∀ p : Sp S, s ∉ p.asIdeal → p ∈ f ⁻¹ᵁ W) :
    (spMap (algebraMap S (Localization.Away s)) ≫ f) ⁻¹ᵁ W = ⊤ := by
  rw [Scheme.Hom.comp_preimage]
  refine top_le_iff.mp fun x _ => ?_
  rw [Scheme.Hom.mem_preimage]
  apply hs
  intro hx
  change s ∈ Ideal.comap (algebraMap S (Localization.Away s)) x.asIdeal at hx
  rw [Ideal.mem_comap] at hx
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.Away.algebraMap_isUnit s))

/- English proof (translation)
Assume the negation of the conclusion as `hD`. Set `I : Ideal S` to `LinearMap.ker (LinearMap.toSpanSingleton S S D)`. Establish `hI : I ≠ ⊤`. Introduce `hI`. Establish `: (1 : S) ∈ I` using `hI ▸ Submodule.mem_top`.

Simplify using `[I] at this`. Conclude with `hD this`. Take `⟨p, hp, hIp⟩` from `Ideal.exists_le_maximal I hI`. Take `⟨s, hs, hsD⟩` from `h p hp`. Take `⟨⟨m, hm⟩, hmD⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ D).mp hsD`.

Take `⟨n, rfl⟩` from `hm`. Establish `: s ^ n ∈ I` using `by simp [I]; exact hmD`. Conclude with `hs (hp.isPrime.mem_of_pow_mem n (hIp this))`.
-/
theorem eq_zero_of_loc {S : Type} [CommRing S] (D : S)
    (h : ∀ p : Ideal S, p.IsMaximal → ∃ s ∉ p, algebraMap S (Localization.Away s) D = 0) : D = 0 := by
  by_contra hD
  let I : Ideal S := LinearMap.ker (LinearMap.toSpanSingleton S S D)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : S) ∈ I := hI ▸ Submodule.mem_top
    simp [I] at this
    exact hD this
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsD⟩ := h p hp
  obtain ⟨⟨m, hm⟩, hmD⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ D).mp hsD
  obtain ⟨n, rfl⟩ := hm
  have : s ^ n ∈ I := by simp [I]; exact hmD
  exact hs (hp.isPrime.mem_of_pow_mem n (hIp this))

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue

open ChartIndep

/- English proof (translation)
Introduce `Y V V' hV _hV' S T _ _ q hq hk ι _ u c w a hw hcomb hu'`. Establish `hqc : spMap q ≫ c = spMap q ≫ u`. Establish `h1` using `GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S T q ι u c w a hcomb`. Use `GlobalTheory.T.isAffineCombinationInChart_unique Y V hV T ι (spMap q ≫ u) _ _ (fun i => spMap q ≫ w i) (fun i => q (a i)) h1 ?_` and prove the remaining obligations. Take `⟨hu1, _, hw1, _⟩` from `h1`.

Use `⟨hu1, hu1, hw1, fun x => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ i, chartHom V (spMap q ≫ w i) (hw1 i) x - chartHom V (spMap q ≫ u) hu1 x = 0` using `fun i => by rw [chartHom_congr V (hw i) (hw1 i) hu1 x, sub_self]`. Simplify using `[h0]`. Establish `hc' : c ⁻¹ᵁ V' = ⊤` using `by rw [← GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u c hqc.symm V']; exact hu'`. Establish `hw' : ∀ i, w i ⁻¹ᵁ V' = ⊤` using `fun i => by`.

Rewrite using `[← GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u (w i) (hw i).symm V']`. Conclude with `hu'`. Establish `hWsame : ∀ W : Y.Opens, c ⁻¹ᵁ W = u ⁻¹ᵁ W ∧ ∀ i, w i ⁻¹ᵁ W = u ⁻¹ᵁ W` using `fun W => ⟨(GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u c hqc.symm W).symm, fun i => (GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u (w i) (hw i).symm W).symm⟩`. Take `⟨hu, _, _, _⟩` from `hcomb`. Use `⟨hu', hc', hw', fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_loc` to reduce the goal to its premises. Introduce `p hp`. Set `P : Sp S` to `⟨p, hp.isPrime⟩`. Establish `hPV : u P ∈ V ⊓ V'`.

Use `⟨(Scheme.Hom.mem_preimage u).mp ?_, (Scheme.Hom.mem_preimage u).mp ?_⟩` and prove the remaining obligations. Rewrite using `[hu]`. Discharge the goal by the elementary cases of `trivial`. Rewrite using `[hu']`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨W, hWaff, hPW, hWle⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) hPV`. Take `⟨_, ⟨s, rfl⟩, hPs, hsW⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens (R := S)).exists_subset_of_mem_open (a := P) (u := ((u ⁻¹ᵁ W : (Sp S).Opens) : Set (Sp S))) ((Scheme.Hom.mem_preimage u).mpr hPW) (u ⁻¹ᵁ W).isOpen`. Use `⟨s, hPs, ?_⟩` and prove the remaining obligations. Use `set g := algebraMap S (Localization.Away s) with hg`. Establish `landW : ∀ f : Sp S ⟶ Y, f ⁻¹ᵁ W = u ⁻¹ᵁ W → (spMap g ≫ f) ⁻¹ᵁ W = ⊤`.

Introduce `f hf`. Use `lands_loc W s f fun p hp' => ?_` and prove the remaining obligations. Rewrite using `[hf]`. Conclude with `hsW hp'`. Use `set qs := locMap q s`.

Establish `hsq : spMap qs ≫ spMap g = spMap (algebraMap T (Localization ((Submonoid.powers s).map q))) ≫ spMap q`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `y`. Conclude with `locMap_alg q s y`.

Establish `hws : ∀ i, spMap qs ≫ (spMap g ≫ w i) = spMap qs ≫ (spMap g ≫ u)` using `fun i => by`. Rewrite using `[← Category.assoc, hsq, Category.assoc, hw i, ← Category.assoc, ← hsq, Category.assoc]`. Take `⟨d, hd, -, -⟩` from `GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart Y W hWaff (Localization.Away s) _ qs (locMap_surj q s hq) (locMap_ker q s hk) ι (spMap g ≫ u) (fun i => spMap g ≫ w i) (fun i => g (a i)) (landW u rfl) hws`. Establish `hcs` using `GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S (Localization.Away s) g ι u c w a ⟨hu, by assumption, by assumption, by assumption⟩`. Establish `hdc : d = spMap g ≫ c` using `GlobalTheory.T.isAffineCombinationInChart_unique Y V hV _ ι _ _ _ _ _ (comb_mono (hWle.trans inf_le_left) _ _ _ _ hd) hcs`.

Establish `hV'd` using `comb_mono (hWle.trans inf_le_right) _ _ _ _ hd`. Rewrite `hV'd` using `[hdc]`. Take `⟨h1, h2, h3, hx⟩` from `hV'd`. Establish `hxx` using `hx x`. Establish `hsum : ∑ i, g (a i) * (chartHom V' (spMap g ≫ w i) (h3 i) x - chartHom V' (spMap g ≫ u) h1 x) = g (∑ i, a i * (chartHom V' (w i) (hw' i) x - chartHom V' u hu' x))`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[chartHom_comp V' g (w i) (hw' i) (h3 i), chartHom_comp V' g u hu' h1, map_mul, map_sub]`. Rewrite `hxx` using `[hsum, chartHom_comp V' g c hc' h2, chartHom_comp V' g u hu' h1]`. Rewrite using `[map_sub, map_add, hxx, sub_self]`.
-/
theorem isCombIn_of_chart : ∀ (Y : Scheme.{0}) (V V' : Y.Opens), IsAffineOpen V → IsAffineOpen V' →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    (∀ i, spMap q ≫ w i = spMap q ≫ u) → GlobalTheory.SecGlue.IsCombIn V u c w a → u ⁻¹ᵁ V' = ⊤ →
    GlobalTheory.SecGlue.IsCombIn V' u c w a := by
  intro Y V V' hV _hV' S T _ _ q hq hk ι _ u c w a hw hcomb hu'

  have hqc : spMap q ≫ c = spMap q ≫ u := by
    have h1 := GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S T q ι u c w a hcomb
    refine GlobalTheory.T.isAffineCombinationInChart_unique Y V hV T ι (spMap q ≫ u) _ _ (fun i => spMap q ≫ w i) (fun i => q (a i)) h1 ?_
    obtain ⟨hu1, _, hw1, _⟩ := h1
    refine ⟨hu1, hu1, hw1, fun x => ?_⟩
    have h0 : ∀ i, chartHom V (spMap q ≫ w i) (hw1 i) x - chartHom V (spMap q ≫ u) hu1 x = 0 :=
      fun i => by rw [chartHom_congr V (hw i) (hw1 i) hu1 x, sub_self]
    simp [h0]

  have hc' : c ⁻¹ᵁ V' = ⊤ := by rw [← GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u c hqc.symm V']; exact hu'
  have hw' : ∀ i, w i ⁻¹ᵁ V' = ⊤ := fun i => by
    rw [← GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u (w i) (hw i).symm V']; exact hu'
  have hWsame : ∀ W : Y.Opens, c ⁻¹ᵁ W = u ⁻¹ᵁ W ∧ ∀ i, w i ⁻¹ᵁ W = u ⁻¹ᵁ W := fun W =>
    ⟨(GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u c hqc.symm W).symm,
      fun i => (GlobalTheory.T.preimage_eq_of_square_zero_thickening S T q hq hk Y u (w i) (hw i).symm W).symm⟩
  obtain ⟨hu, _, _, _⟩ := hcomb
  refine ⟨hu', hc', hw', fun x => ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_loc
  intro p hp
  let P : Sp S := ⟨p, hp.isPrime⟩
  have hPV : u P ∈ V ⊓ V' := by
    refine ⟨(Scheme.Hom.mem_preimage u).mp ?_, (Scheme.Hom.mem_preimage u).mp ?_⟩
    · rw [hu]; trivial
    · rw [hu']; trivial
  obtain ⟨W, hWaff, hPW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) hPV
  obtain ⟨_, ⟨s, rfl⟩, hPs, hsW⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := S)).exists_subset_of_mem_open
    (a := P) (u := ((u ⁻¹ᵁ W : (Sp S).Opens) : Set (Sp S)))
    ((Scheme.Hom.mem_preimage u).mpr hPW) (u ⁻¹ᵁ W).isOpen
  refine ⟨s, hPs, ?_⟩
  set g := algebraMap S (Localization.Away s) with hg
  have landW : ∀ f : Sp S ⟶ Y, f ⁻¹ᵁ W = u ⁻¹ᵁ W → (spMap g ≫ f) ⁻¹ᵁ W = ⊤ := by
    intro f hf
    refine lands_loc W s f fun p hp' => ?_
    rw [hf]
    exact hsW hp'
  set qs := locMap q s
  have hsq : spMap qs ≫ spMap g =
      spMap (algebraMap T (Localization ((Submonoid.powers s).map q))) ≫ spMap q := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    exact locMap_alg q s y
  have hws : ∀ i, spMap qs ≫ (spMap g ≫ w i) = spMap qs ≫ (spMap g ≫ u) := fun i => by
    rw [← Category.assoc, hsq, Category.assoc, hw i, ← Category.assoc, ← hsq, Category.assoc]
  obtain ⟨d, hd, -, -⟩ := GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart Y W hWaff (Localization.Away s) _ qs (locMap_surj q s hq)
    (locMap_ker q s hk) ι (spMap g ≫ u) (fun i => spMap g ≫ w i) (fun i => g (a i)) (landW u rfl) hws
  have hcs := GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S (Localization.Away s) g ι u c w a ⟨hu, by assumption, by assumption, by assumption⟩
  have hdc : d = spMap g ≫ c :=
    GlobalTheory.T.isAffineCombinationInChart_unique Y V hV _ ι _ _ _ _ _ (comb_mono (hWle.trans inf_le_left) _ _ _ _ hd) hcs
  have hV'd := comb_mono (hWle.trans inf_le_right) _ _ _ _ hd
  rw [hdc] at hV'd
  obtain ⟨h1, h2, h3, hx⟩ := hV'd
  have hxx := hx x
  have hsum : ∑ i, g (a i) * (chartHom V' (spMap g ≫ w i) (h3 i) x - chartHom V' (spMap g ≫ u) h1 x) =
      g (∑ i, a i * (chartHom V' (w i) (hw' i) x - chartHom V' u hu' x)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [chartHom_comp V' g (w i) (hw' i) (h3 i), chartHom_comp V' g u hu' h1, map_mul, map_sub]
  rw [hsum, chartHom_comp V' g c hc' h2, chartHom_comp V' g u hu' h1] at hxx
  rw [map_sub, map_add, hxx, sub_self]

end GlobalTheory.SecGlue
