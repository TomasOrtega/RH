import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionAppLESurjectiveAndKer

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ClosedFibre

variable (R : Type) [CommRing R] (I : Ideal R)

abbrev baseIncl (e : ℕ) : Spec (CommRingCat.of (R ⧸ I ^ (0 + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ e + 1))))

/- English proof (translation)
Simplify using `only [baseIncl, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]`.
-/
theorem baseIncl_comp (e : ℕ) : baseIncl R I e ≫ thick R I e = thick R I 0 := by
  simp only [baseIncl, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

def incl (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    (thickObj R I 0 G).left ⟶ (thickObj R I e G).left :=
  pullback.map G.hom (thick R I 0) G.hom (thick R I e) (𝟙 _) (baseIncl R I e) (𝟙 _)
    (by simp) (by simp [baseIncl_comp])

/- English proof (translation)
The claim follows from `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`.
-/
theorem incl_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    incl R I e G ≫ (fstG I e G).left = (fstG I 0 G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem incl_snd (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    incl R I e G ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I 0) ≫ baseIncl R I e :=
  pullback.lift_snd _ _ _

/- English proof (translation)
Use `IsPullback.of_right ?_ (incl_snd R I e G) (IsPullback.of_hasPullback G.hom (thick R I e))` and prove the remaining obligations. Establish `h1 : incl R I e G ≫ pullback.fst G.hom (thick R I e) = pullback.fst G.hom (thick R I 0)` using `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`. Rewrite using `[h1, baseIncl_comp]`. Conclude with `IsPullback.of_hasPullback G.hom (thick R I 0)`.
-/
theorem isPullback_incl (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    IsPullback (incl R I e G) (pullback.snd G.hom (thick R I 0)) (pullback.snd G.hom (thick R I e))
      (baseIncl R I e) := by
  refine IsPullback.of_right ?_ (incl_snd R I e G) (IsPullback.of_hasPullback G.hom (thick R I e))
  have h1 : incl R I e G ≫ pullback.fst G.hom (thick R I e) = pullback.fst G.hom (thick R I 0) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [h1, baseIncl_comp]
  exact IsPullback.of_hasPullback G.hom (thick R I 0)

end GlobalTheory.ClosedFibre

namespace GlobalTheory.ClosedFibre

variable (R : Type) [CommRing R] (I : Ideal R)

/- English proof (translation)
Establish `hc : (fstG I e G).left ≫ G.hom = pullback.snd G.hom (thick R I e) ≫ thick R I e` using `pullback.condition`. Rewrite using `[hc]`. Establish `h` using `congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))).hom a)`. Simplify using `only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h ⊢`. Use `erw [← h]`.

Both sides reduce to the same expression.
-/
theorem cst_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) (V : (thickObj R I e G).left.Opens) (a : R) :
    GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V a =
      GlobalTheory.AbLaw.cst (pullback.snd G.hom (thick R I e)) V (Ideal.Quotient.mk (I ^ (e + 1)) a) := by
  have hc : (fstG I e G).left ≫ G.hom = pullback.snd G.hom (thick R I e) ≫ thick R I e := pullback.condition
  rw [hc]
  have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))).hom a)
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom] at h ⊢
  erw [← h]
  rfl

/- English proof (translation)
Rewrite using `[cst_fst, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]`.
-/
theorem cst_eq_zero (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    (V : (thickObj R I e G).left.Opens) (a : R) (ha : a ∈ I ^ (e + 1)) :
    GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V a = 0 := by
  rw [cst_fst, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/- English proof (translation)
Establish `hq : incl R I e G ≫ ((fstG I e G).left ≫ G.hom) = (fstG I 0 G).left ≫ G.hom`. Rewrite using `[← Category.assoc, incl_fst]`. Rewrite using `[← hq]`. Simplify using `only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]`. Use `congr($((incl R I e G).naturality (homOfLE (le_top : V ≤ ⊤)).op).hom (((fstG I e G).left ≫ G.hom).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)))` as an intermediate fact.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Conclude with `this.trans rfl`.
-/
theorem app_cst (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    (V : (thickObj R I e G).left.Opens) (a : R) :
    (Scheme.Hom.app (incl R I e G) V).hom (GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V a) =
      GlobalTheory.AbLaw.cst ((fstG I 0 G).left ≫ G.hom) (incl R I e G ⁻¹ᵁ V) a := by
  have hq : incl R I e G ≫ ((fstG I e G).left ≫ G.hom) = (fstG I 0 G).left ≫ G.hom := by
    rw [← Category.assoc, incl_fst]
  rw [← hq]
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  have := congr($((incl R I e G).naturality (homOfLE (le_top : V ≤ ⊤)).op).hom
    (((fstG I e G).left ≫ G.hom).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.trans rfl

/- English proof (translation)
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `h : I ^ (e + 1) ≤ I ^ (0 + 1)` using `Ideal.pow_le_pow_right (by omega)`. Establish `hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1))) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h))`. Rewrite using `[range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]`. Introduce `a ha`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `ha' : a ∈ I ^ (0 + 1)`. Simplify `ha` using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite `ha'` using `[zero_add, pow_one]`. Use `x.2.mem_of_pow_mem (e + 1) ?_` and prove the remaining obligations.

Establish `: Ideal.Quotient.mk (I ^ (e + 1)) a ^ (e + 1) = 0`. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.pow_mem_pow ha' _`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`.

Conclude with `hx`.
-/
theorem surjective_baseIncl (e : ℕ) : Surjective (baseIncl R I e) := by
  refine ⟨fun x => ?_⟩
  have h : I ^ (e + 1) ≤ I ^ (0 + 1) := Ideal.pow_le_pow_right (by omega)
  have hx : (x : PrimeSpectrum (R ⧸ I ^ (e + 1))) ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective h)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (0 + 1) := by
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using ha
    rw [zero_add, pow_one] at ha'
    refine x.2.mem_of_pow_mem (e + 1) ?_
    have : Ideal.Quotient.mk (I ^ (e + 1)) a ^ (e + 1) = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow ha' _
    rw [this]
    exact Ideal.zero_mem _
  exact hx

/- English proof (translation)
The claim follows from `(MorphismProperty.of_isPullback (P := @Surjective) (isPullback_incl R I e G).flip (surjective_baseIncl R I e)).surj`.
-/
theorem incl_surjective (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    Function.Surjective ⇑(incl R I e G) :=
  (MorphismProperty.of_isPullback (P := @Surjective) (isPullback_incl R I e G).flip
    (surjective_baseIncl R I e)).surj

/- English proof (translation)
Establish `H` using `isPullback_incl R I e G`. Establish `po` using `(GlobalTheory.AbLaw.isPushout_cst H hV (V' := incl R I e G ⁻¹ᵁ V) rfl).flip`. Establish `hsurj : Function.Surjective (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ e + 1) : I ^ (e + 1) ≤ I ^ (0 + 1)))).hom` using `Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ e + 1))`. Take `⟨h1, h2⟩` from `GlobalTheory.TorsionChart.pushout_inl_surjective_and_ker po hsurj`. Rewrite `h1`, `h2` using `[← Scheme.Hom.app_eq_appLE]`.

Use `⟨GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback H hV, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker, Ideal.map_map]`. Establish `hc : (GlobalTheory.AbLaw.cst (pullback.snd G.hom (thick R I e)) V).comp (Ideal.Quotient.mk (I ^ (e + 1))) = GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V` using `RingHom.ext fun a => (cst_fst R I e G V a).symm`. Rewrite using `[hc, zero_add, pow_one]`.
-/
theorem app_incl (e : ℕ) (G : Over (Spec (CommRingCat.of R))) (V : (thickObj R I e G).left.Opens)
    (hV : IsAffineOpen V) :
    IsAffineOpen (incl R I e G ⁻¹ᵁ V) ∧ Function.Surjective (Scheme.Hom.app (incl R I e G) V).hom ∧
      RingHom.ker (Scheme.Hom.app (incl R I e G) V).hom ≤
        Ideal.map (GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V) I := by
  have H := isPullback_incl R I e G
  have po := (GlobalTheory.AbLaw.isPushout_cst H hV (V' := incl R I e G ⁻¹ᵁ V) rfl).flip
  have hsurj : Function.Surjective (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ e + 1) : I ^ (e + 1) ≤ I ^ (0 + 1)))).hom :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ e + 1))
  obtain ⟨h1, h2⟩ := GlobalTheory.TorsionChart.pushout_inl_surjective_and_ker po hsurj
  rw [← Scheme.Hom.app_eq_appLE] at h1 h2
  refine ⟨GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback H hV, h1, ?_⟩
  rw [h2, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker, Ideal.map_map]
  have hc : (GlobalTheory.AbLaw.cst (pullback.snd G.hom (thick R I e)) V).comp (Ideal.Quotient.mk (I ^ (e + 1))) =
      GlobalTheory.AbLaw.cst ((fstG I e G).left ≫ G.hom) V :=
    RingHom.ext fun a => (cst_fst R I e G V a).symm
  rw [hc, zero_add, pow_one]

end GlobalTheory.ClosedFibre

namespace GlobalTheory.ClosedFibre

open MvPolynomial in

/- English proof (translation)
Substitute `hD` using the available equality. Establish `hev : ∀ P : MvPolynomial (Fin m) R, eval₂ (GlobalTheory.AbLaw.cst p (X.basicOpen h)) (fun l => GlobalTheory.AbLaw.rs X hle (r l)) P = GlobalTheory.AbLaw.rs X hle (eval₂ (GlobalTheory.AbLaw.cst p N₀) r P)`. Introduce `P`. Rewrite using `[MvPolynomial.hom_eval₂]`. Use `congr 1`.

Conclude with `RingHom.ext fun a => (GlobalTheory.AbLaw.rs_cst p hle a).symm`. Establish `hl` using `hN₀.isLocalization_basicOpen h`. Take `⟨⟨a, ⟨s, hs⟩⟩, has⟩` from `IsLocalization.surj (Submonoid.powers h) g`. Establish `hsu : IsUnit (GlobalTheory.AbLaw.rs X hle s)` using `IsLocalization.map_units (M := Submonoid.powers h) Γ(X, X.basicOpen h) ⟨s, hs⟩`. Take `⟨Pa, Qa, hQa, ha⟩` from `hgen a`.

Take `⟨Ps, Qs, hQs, hsq⟩` from `hgen s`. Use `⟨Pa * Qs, Ps * Qa, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂_mul, hev, hev, ← hsq, map_mul]`. Conclude with `(hsu.mul (hQs.map _)).mul (hQa.map _)`. Simplify using `only [MvPolynomial.eval₂_mul, hev]`.

Rewrite using `[← hsq, ← ha]`. Simplify using `only [map_mul]`. Establish `has' : g * GlobalTheory.AbLaw.rs X hle s = GlobalTheory.AbLaw.rs X hle a` using `has`. Rewrite using `[← has']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gen_basicOpen {X : Scheme.{0}} {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) {N₀ : X.Opens}
    (hN₀ : IsAffineOpen N₀) {m : ℕ} (r : Fin m → Γ(X, N₀))
    (hgen : ∀ g : Γ(X, N₀), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst p N₀) r Q) ∧
      g * eval₂ (GlobalTheory.AbLaw.cst p N₀) r Q = eval₂ (GlobalTheory.AbLaw.cst p N₀) r P)
    (h : Γ(X, N₀)) (D : X.Opens) (hle : D ≤ N₀) (hD : D = X.basicOpen h) (g : Γ(X, D)) :
    ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (eval₂ (GlobalTheory.AbLaw.cst p D) (fun l => GlobalTheory.AbLaw.rs X hle (r l)) Q) ∧
      g * eval₂ (GlobalTheory.AbLaw.cst p D) (fun l => GlobalTheory.AbLaw.rs X hle (r l)) Q =
        eval₂ (GlobalTheory.AbLaw.cst p D) (fun l => GlobalTheory.AbLaw.rs X hle (r l)) P := by
  subst hD
  have hev : ∀ P : MvPolynomial (Fin m) R, eval₂ (GlobalTheory.AbLaw.cst p (X.basicOpen h))
      (fun l => GlobalTheory.AbLaw.rs X hle (r l)) P = GlobalTheory.AbLaw.rs X hle (eval₂ (GlobalTheory.AbLaw.cst p N₀) r P) := by
    intro P
    rw [MvPolynomial.hom_eval₂]
    congr 1
    exact RingHom.ext fun a => (GlobalTheory.AbLaw.rs_cst p hle a).symm
  have hl := hN₀.isLocalization_basicOpen h
  obtain ⟨⟨a, ⟨s, hs⟩⟩, has⟩ := IsLocalization.surj (Submonoid.powers h) g
  have hsu : IsUnit (GlobalTheory.AbLaw.rs X hle s) := IsLocalization.map_units (M := Submonoid.powers h)
    Γ(X, X.basicOpen h) ⟨s, hs⟩
  obtain ⟨Pa, Qa, hQa, ha⟩ := hgen a
  obtain ⟨Ps, Qs, hQs, hsq⟩ := hgen s
  refine ⟨Pa * Qs, Ps * Qa, ?_, ?_⟩
  · rw [MvPolynomial.eval₂_mul, hev, hev, ← hsq, map_mul]
    exact (hsu.mul (hQs.map _)).mul (hQa.map _)
  · simp only [MvPolynomial.eval₂_mul, hev]
    rw [← hsq, ← ha]
    simp only [map_mul]
    have has' : g * GlobalTheory.AbLaw.rs X hle s = GlobalTheory.AbLaw.rs X hle a := has
    rw [← has']
    ring

end GlobalTheory.ClosedFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ G L k s₀ i hyp e w hw hunit`. Establish `hjp : GlobalTheory.ClosedFibre.incl R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) 0 G).left` using `GlobalTheory.ClosedFibre.incl_fst R _ e G`. Take `⟨w₀, rfl⟩` from `GlobalTheory.ClosedFibre.incl_surjective R (maximalIdeal R) e G w`. Use `set jm := GlobalTheory.ClosedFibre.incl R (maximalIdeal R) e G with hjdef`. Use `set pe : (thickObj R (maximalIdeal R) e G).left ⟶ G.left := (fstG (maximalIdeal R) e G).left with hpe`.

Use `set p₀ : (thickObj R (maximalIdeal R) 0 G).left ⟶ G.left := (fstG (maximalIdeal R) 0 G).left with hp₀`. Establish `hgc : ∀ (y : (thickObj R (maximalIdeal R) 0 G).left) (s : H0 L k), pe (jm y) ∈ secChart L i → secGerm p₀ y s i = (jm.stalkMap y).hom (secGerm pe (jm y) s i)`. Introduce `y s hy`. Rewrite using `[← hjp]`. Conclude with `secGerm_comp jm pe y s hy`.

Establish `hw₀ : p₀ w₀ ∈ secChart L i`. Rewrite using `[← hjp, Scheme.Hom.comp_apply]`. Conclude with `hw`. Establish `hu₀ : IsUnit (secGerm p₀ w₀ s₀ i)` using `by rw [hgc w₀ s₀ hw]; exact hunit.map _`. Take `⟨N₀, m, σ, r₀, hwN₀, hN₀, hN₀le, hgerm₀, hgen₀⟩` from `hyp w₀ hw₀ hu₀`.

Take `⟨a, ha⟩ : ∃ a, a = (pe.app (secChart L i)).hom (s₀.f i)` from `⟨_, rfl⟩`. Establish `hmemU₁ : ∀ y : (thickObj R (maximalIdeal R) e G).left, (hy : pe y ∈ secChart L i) → (y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen a ↔ IsUnit (secGerm pe y s₀ i))`. Introduce `y hy`. Rewrite using `[Scheme.mem_basicOpen _ a y hy, ha]`. Conclude with `(iff_of_eq (congrArg IsUnit (gs_eq pe y _ hy (s₀.f i)))).symm`.

Establish `hwU₁` using `(hmemU₁ _ hw).2 hunit`. Take `⟨V, hV, hwV, hVle⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 (thickObj R (maximalIdeal R) e G).left.isBasis_affineOpens hwU₁`. Establish `hV' : IsAffineOpen V` using `hV`. Take `⟨hVaff, hVsurj, -⟩` from `GlobalTheory.ClosedFibre.app_incl R (maximalIdeal R) e G V hV'`. Take `⟨f₀, g₀, hfg, hw₀f⟩` from `exists_basicOpen_le_affine_inter hN₀ hVaff w₀ ⟨hwN₀, hwV⟩`.

Take `⟨F, hF⟩` from `hVsurj g₀`. Establish `hNaff : IsAffineOpen ((thickObj R (maximalIdeal R) e G).left.basicOpen F)` using `hV'.basicOpen F`. Establish `hjN : jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F = (thickObj R (maximalIdeal R) 0 G).left.basicOpen f₀`. Rewrite using `[Scheme.preimage_basicOpen, hF, hfg]`. Establish `hwN : jm w₀ ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F` using `by show w₀ ∈ jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F`.

Rewrite using `[hjN]`. Conclude with `hw₀f`. Establish `hNU₁ : (thickObj R (maximalIdeal R) e G).left.basicOpen F ≤ (thickObj R (maximalIdeal R) e G).left.basicOpen a` using `((thickObj R (maximalIdeal R) e G).left.basicOpen_le F).trans hVle`. Establish `hU₁c : (thickObj R (maximalIdeal R) e G).left.basicOpen a ≤ pe ⁻¹ᵁ secChart L i` using `(thickObj R (maximalIdeal R) e G).left.basicOpen_le a`. Establish `hDN₀ : jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F ≤ N₀`.

Rewrite using `[hjN]`. Conclude with `(thickObj R (maximalIdeal R) 0 G).left.basicOpen_le f₀`. Establish `hu₁ : IsUnit (GlobalTheory.AbLaw.rs _ hU₁c a)` using `(thickObj R (maximalIdeal R) e G).left.toRingedSpace.isUnit_res_basicOpen a`. Set `ρ : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, (thickObj R (maximalIdeal R) e G).left.basicOpen a)` to `fun l => GlobalTheory.AbLaw.rs _ hU₁c ((pe.app (secChart L i)).hom ((σ l).f i)) * ↑(hu₁.unit⁻¹)`. Set `r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, (thickObj R (maximalIdeal R) e G).left.basicOpen F)` to `fun l => GlobalTheory.AbLaw.rs _ hNU₁ (ρ l)`.

Establish `hρ : ∀ l, ρ l * GlobalTheory.AbLaw.rs _ hU₁c a = GlobalTheory.AbLaw.rs _ hU₁c ((pe.app (secChart L i)).hom ((σ l).f i))`. Introduce `l`. Simplify using `only [ρ]`. Rewrite using `[_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]`. Establish `hg1 : ∀ y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen a, ∀ x : Γ((thickObj R (maximalIdeal R) e G).left, pe ⁻¹ᵁ secChart L i), gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y ((thickObj R (maximalIdeal R) e G).left.basicOpen a) (GlobalTheory.AbLaw.rs _ hU₁c x) = gs (𝟙 (thi …` using `fun y hy x => gs_res (𝟙 _) y hU₁c hy x`.

Establish `hg2 : ∀ (y : (thickObj R (maximalIdeal R) e G).left) (hy : pe y ∈ secChart L i) (b : Γ(G.left, secChart L i)), gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y (pe ⁻¹ᵁ secChart L i) ((pe.app (secChart L i)).hom b) = gs pe y (secChart L i) b`. Introduce `y hy b`. Rewrite using `[gs_pull (𝟙 (thickObj R (maximalIdeal R) e G).left) pe y _ hy, Category.id_comp]`. Establish `hsa : ∀ (y : (thickObj R (maximalIdeal R) e G).left) (hy : pe y ∈ secChart L i), gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y (pe ⁻¹ᵁ secChart L i) a = secGerm pe y s₀ i`. Introduce `y hy`.

Rewrite using `[ha]`. Conclude with `hg2 y hy _`. Establish `hgermN : ∀ y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F, IsUnit (secGerm pe y s₀ i) ∧ ∀ l, secGerm pe y (σ l) i = gs (𝟙 _) y ((thickObj R (maximalIdeal R) e G).left.basicOpen F) (r l) * secGerm pe y s₀ i`. Introduce `y hy`. Establish `hy₁` using `hNU₁ hy`.

Establish `hyc` using `hU₁c hy₁`. Use `⟨(hmemU₁ y hyc).1 hy₁, fun l => ?_⟩` and prove the remaining obligations. Establish `e1` using `congrArg (gs (𝟙 _) y ((thickObj R (maximalIdeal R) e G).left.basicOpen a)) (hρ l)`. Rewrite `e1` using `[gs_mul _ _ _ hy₁, hg1 y hy₁, hg1 y hy₁, hsa y hyc]`. Express the relevant statement in the definitionally equal form `gs pe y _ _ = _ * gs pe y _ _`.

Rewrite using `[← hg2 y hyc ((σ l).f i), ← e1]`. Simplify using `only [r]`. Rewrite using `[gs_res (𝟙 _) y hNU₁ hy]`. Use `⟨(thickObj R (maximalIdeal R) e G).left.basicOpen F, m, σ, r, hwN, hNaff, hNU₁.trans hU₁c, hgermN, fun g => ?_⟩` and prove the remaining obligations. Establish `hjr : ∀ l, (jm.app _).hom (r l) = GlobalTheory.AbLaw.rs _ hDN₀ (r₀ l)`.

Introduce `l`. Apply `fn_ext` to reduce the goal to its premises. Introduce `y hy`. Establish `hyN₀` using `hDN₀ hy`. Establish `hyN : jm y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F` using `hy`.

Establish `hyc : pe (jm y) ∈ secChart L i` using `hU₁c (hNU₁ hyN)`. Rewrite using `[gs_pull (𝟙 _) jm y _ hyN, Category.id_comp, gs_res (𝟙 _) y hDN₀ hy]`. Use `(hgerm₀ y hyN₀).1.mul_left_injective ?_` and prove the remaining obligations. Use `show gs jm y _ (r l) * secGerm p₀ y s₀ i = gs (𝟙 _) y N₀ (r₀ l) * secGerm p₀ y s₀ i`. Rewrite using `[← (hgerm₀ y hyN₀).2 l, hgc y (σ l) hyc, hgc y s₀ hyc, (hgermN (jm y) hyN).2 l, map_mul, gs_stalkMap jm y _ hyN]`.

Establish `hjc : (jm.app _).hom.comp (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) = GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) (jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F)` using `RingHom.ext fun x => GlobalTheory.ClosedFibre.app_cst R (maximalIdeal R) e G _ x`. Establish `hjev : ∀ P : MvPolynomial (Fin m) R, (jm.app _).hom (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r P) = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) (jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOp …`. Introduce `P`. Rewrite using `[MvPolynomial.hom_eval₂, hjc]`. Simplify using `only [hjr]`.

Take `⟨P, Q, hQ, hPQ⟩` from `GlobalTheory.ClosedFibre.gen_basicOpen (p₀ ≫ G.hom) hN₀ r₀ hgen₀ f₀ _ hDN₀ hjN ((jm.app _).hom g)`. Take `⟨-, hNsurj, hNker⟩` from `GlobalTheory.ClosedFibre.app_incl R (maximalIdeal R) e G _ hNaff`. Establish `hnil : ∀ x ∈ Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) (maximalIdeal R), IsNilpotent x`. Introduce `x hx`. Use `⟨e + 1, ?_⟩` and prove the remaining obligations.

Establish `h1 : x ^ (e + 1) ∈ Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) (maximalIdeal R ^ (e + 1))`. Rewrite using `[Ideal.map_pow]`. Conclude with `Ideal.pow_mem_pow hx _`. Establish `h0 : Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) (maximalIdeal R ^ (e + 1)) = ⊥`. Rewrite using `[Ideal.map_eq_bot_iff_le_ker]`.

Introduce `x hx`. Conclude with `RingHom.mem_ker.2 (GlobalTheory.ClosedFibre.cst_eq_zero R (maximalIdeal R) e G _ x hx)`. Rewrite `h1` using `[h0]`. Conclude with `h1`. Use `⟨P, Q, ?_, ?_⟩` and prove the remaining obligations.

Establish `hQ' : IsUnit ((jm.app _).hom (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r Q))`. Rewrite using `[hjev]`. Conclude with `hQ`. Take `⟨v, hv⟩` from `hQ'.exists_right_inv`. Take `⟨v', rfl⟩` from `hNsurj v`.

Establish `hk : MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r Q * v' - 1 ∈ RingHom.ker (jm.app _).hom`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_one, hv, sub_self]`. Establish `hu` using `(hnil _ (hNker hk)).isUnit_one_add`. Rewrite `hu` using `[add_sub_cancel]`. Conclude with `isUnit_of_mul_isUnit_left hu`.

Apply `hNker` to reduce the goal to its premises. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, hjev, hjev, hPQ, sub_self]`.
-/
theorem GlobalTheory.Mum.ratio_gen_mod_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k : ℕ) (s₀ : H0 L k) (i : Fin 1 → L.ι), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (e : ℕ) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  intro R _ _ _ G L k s₀ i hyp e w hw hunit
  have hjp : GlobalTheory.ClosedFibre.incl R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) e G).left =
      (fstG (maximalIdeal R) 0 G).left := GlobalTheory.ClosedFibre.incl_fst R _ e G
  obtain ⟨w₀, rfl⟩ := GlobalTheory.ClosedFibre.incl_surjective R (maximalIdeal R) e G w
  set jm := GlobalTheory.ClosedFibre.incl R (maximalIdeal R) e G with hjdef
  set pe : (thickObj R (maximalIdeal R) e G).left ⟶ G.left := (fstG (maximalIdeal R) e G).left with hpe
  set p₀ : (thickObj R (maximalIdeal R) 0 G).left ⟶ G.left := (fstG (maximalIdeal R) 0 G).left with hp₀

  have hgc : ∀ (y : (thickObj R (maximalIdeal R) 0 G).left) (s : H0 L k), pe (jm y) ∈ secChart L i →
      secGerm p₀ y s i = (jm.stalkMap y).hom (secGerm pe (jm y) s i) := by
    intro y s hy
    rw [← hjp]
    exact secGerm_comp jm pe y s hy
  have hw₀ : p₀ w₀ ∈ secChart L i := by
    rw [← hjp, Scheme.Hom.comp_apply]; exact hw
  have hu₀ : IsUnit (secGerm p₀ w₀ s₀ i) := by rw [hgc w₀ s₀ hw]; exact hunit.map _
  obtain ⟨N₀, m, σ, r₀, hwN₀, hN₀, hN₀le, hgerm₀, hgen₀⟩ := hyp w₀ hw₀ hu₀

  obtain ⟨a, ha⟩ : ∃ a, a = (pe.app (secChart L i)).hom (s₀.f i) := ⟨_, rfl⟩
  have hmemU₁ : ∀ y : (thickObj R (maximalIdeal R) e G).left, (hy : pe y ∈ secChart L i) →
      (y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen a ↔ IsUnit (secGerm pe y s₀ i)) := by
    intro y hy
    rw [Scheme.mem_basicOpen _ a y hy, ha]
    exact (iff_of_eq (congrArg IsUnit (gs_eq pe y _ hy (s₀.f i)))).symm
  have hwU₁ := (hmemU₁ _ hw).2 hunit
  obtain ⟨V, hV, hwV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 (thickObj R (maximalIdeal R) e G).left.isBasis_affineOpens hwU₁
  have hV' : IsAffineOpen V := hV
  obtain ⟨hVaff, hVsurj, -⟩ := GlobalTheory.ClosedFibre.app_incl R (maximalIdeal R) e G V hV'
  obtain ⟨f₀, g₀, hfg, hw₀f⟩ := exists_basicOpen_le_affine_inter hN₀ hVaff w₀ ⟨hwN₀, hwV⟩
  obtain ⟨F, hF⟩ := hVsurj g₀
  have hNaff : IsAffineOpen ((thickObj R (maximalIdeal R) e G).left.basicOpen F) := hV'.basicOpen F
  have hjN : jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F =
      (thickObj R (maximalIdeal R) 0 G).left.basicOpen f₀ := by
    rw [Scheme.preimage_basicOpen, hF, hfg]
  have hwN : jm w₀ ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F := by
    show w₀ ∈ jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F
    rw [hjN]; exact hw₀f
  have hNU₁ : (thickObj R (maximalIdeal R) e G).left.basicOpen F ≤
      (thickObj R (maximalIdeal R) e G).left.basicOpen a :=
    ((thickObj R (maximalIdeal R) e G).left.basicOpen_le F).trans hVle
  have hU₁c : (thickObj R (maximalIdeal R) e G).left.basicOpen a ≤ pe ⁻¹ᵁ secChart L i :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le a
  have hDN₀ : jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F ≤ N₀ := by
    rw [hjN]; exact (thickObj R (maximalIdeal R) 0 G).left.basicOpen_le f₀

  have hu₁ : IsUnit (GlobalTheory.AbLaw.rs _ hU₁c a) :=
    (thickObj R (maximalIdeal R) e G).left.toRingedSpace.isUnit_res_basicOpen a
  let ρ : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, (thickObj R (maximalIdeal R) e G).left.basicOpen a) :=
    fun l => GlobalTheory.AbLaw.rs _ hU₁c ((pe.app (secChart L i)).hom ((σ l).f i)) * ↑(hu₁.unit⁻¹)
  let r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, (thickObj R (maximalIdeal R) e G).left.basicOpen F) :=
    fun l => GlobalTheory.AbLaw.rs _ hNU₁ (ρ l)
  have hρ : ∀ l, ρ l * GlobalTheory.AbLaw.rs _ hU₁c a = GlobalTheory.AbLaw.rs _ hU₁c ((pe.app (secChart L i)).hom ((σ l).f i)) := by
    intro l
    simp only [ρ]
    rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  have hg1 : ∀ y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen a,
      ∀ x : Γ((thickObj R (maximalIdeal R) e G).left, pe ⁻¹ᵁ secChart L i),
      gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y ((thickObj R (maximalIdeal R) e G).left.basicOpen a)
        (GlobalTheory.AbLaw.rs _ hU₁c x) = gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y (pe ⁻¹ᵁ secChart L i) x :=
    fun y hy x => gs_res (𝟙 _) y hU₁c hy x
  have hg2 : ∀ (y : (thickObj R (maximalIdeal R) e G).left) (hy : pe y ∈ secChart L i) (b : Γ(G.left, secChart L i)),
      gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y (pe ⁻¹ᵁ secChart L i) ((pe.app (secChart L i)).hom b) =
        gs pe y (secChart L i) b := by
    intro y hy b
    rw [gs_pull (𝟙 (thickObj R (maximalIdeal R) e G).left) pe y _ hy, Category.id_comp]
  have hsa : ∀ (y : (thickObj R (maximalIdeal R) e G).left) (hy : pe y ∈ secChart L i),
      gs (𝟙 (thickObj R (maximalIdeal R) e G).left) y (pe ⁻¹ᵁ secChart L i) a = secGerm pe y s₀ i := by
    intro y hy
    rw [ha]; exact hg2 y hy _
  have hgermN : ∀ y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F, IsUnit (secGerm pe y s₀ i) ∧
      ∀ l, secGerm pe y (σ l) i = gs (𝟙 _) y ((thickObj R (maximalIdeal R) e G).left.basicOpen F) (r l) *
        secGerm pe y s₀ i := by
    intro y hy
    have hy₁ := hNU₁ hy
    have hyc := hU₁c hy₁
    refine ⟨(hmemU₁ y hyc).1 hy₁, fun l => ?_⟩
    have e1 := congrArg (gs (𝟙 _) y ((thickObj R (maximalIdeal R) e G).left.basicOpen a)) (hρ l)
    rw [gs_mul _ _ _ hy₁, hg1 y hy₁, hg1 y hy₁, hsa y hyc] at e1
    change gs pe y _ _ = _ * gs pe y _ _
    rw [← hg2 y hyc ((σ l).f i), ← e1]
    simp only [r]
    rw [gs_res (𝟙 _) y hNU₁ hy]
  refine ⟨(thickObj R (maximalIdeal R) e G).left.basicOpen F, m, σ, r, hwN, hNaff, hNU₁.trans hU₁c, hgermN,
    fun g => ?_⟩

  have hjr : ∀ l, (jm.app _).hom (r l) = GlobalTheory.AbLaw.rs _ hDN₀ (r₀ l) := by
    intro l
    apply fn_ext
    intro y hy
    have hyN₀ := hDN₀ hy
    have hyN : jm y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen F := hy
    have hyc : pe (jm y) ∈ secChart L i := hU₁c (hNU₁ hyN)
    rw [gs_pull (𝟙 _) jm y _ hyN, Category.id_comp, gs_res (𝟙 _) y hDN₀ hy]
    refine (hgerm₀ y hyN₀).1.mul_left_injective ?_
    show gs jm y _ (r l) * secGerm p₀ y s₀ i = gs (𝟙 _) y N₀ (r₀ l) * secGerm p₀ y s₀ i
    rw [← (hgerm₀ y hyN₀).2 l, hgc y (σ l) hyc, hgc y s₀ hyc, (hgermN (jm y) hyN).2 l, map_mul,
      gs_stalkMap jm y _ hyN]
  have hjc : (jm.app _).hom.comp (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) =
      GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) (jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F) :=
    RingHom.ext fun x => GlobalTheory.ClosedFibre.app_cst R (maximalIdeal R) e G _ x
  have hjev : ∀ P : MvPolynomial (Fin m) R,
      (jm.app _).hom (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r P) =
      MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) (jm ⁻¹ᵁ (thickObj R (maximalIdeal R) e G).left.basicOpen F))
        (fun l => GlobalTheory.AbLaw.rs _ hDN₀ (r₀ l)) P := by
    intro P
    rw [MvPolynomial.hom_eval₂, hjc]
    simp only [hjr]
  obtain ⟨P, Q, hQ, hPQ⟩ := GlobalTheory.ClosedFibre.gen_basicOpen (p₀ ≫ G.hom) hN₀ r₀ hgen₀ f₀ _ hDN₀ hjN ((jm.app _).hom g)
  obtain ⟨-, hNsurj, hNker⟩ := GlobalTheory.ClosedFibre.app_incl R (maximalIdeal R) e G _ hNaff
  have hnil : ∀ x ∈ Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F))
      (maximalIdeal R), IsNilpotent x := by
    intro x hx
    refine ⟨e + 1, ?_⟩
    have h1 : x ^ (e + 1) ∈ Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F))
        (maximalIdeal R ^ (e + 1)) := by
      rw [Ideal.map_pow]; exact Ideal.pow_mem_pow hx _
    have h0 : Ideal.map (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F))
        (maximalIdeal R ^ (e + 1)) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      intro x hx
      exact RingHom.mem_ker.2 (GlobalTheory.ClosedFibre.cst_eq_zero R (maximalIdeal R) e G _ x hx)
    rw [h0] at h1
    exact h1
  refine ⟨P, Q, ?_, ?_⟩
  · have hQ' : IsUnit ((jm.app _).hom (MvPolynomial.eval₂
        (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r Q)) := by
      rw [hjev]; exact hQ
    obtain ⟨v, hv⟩ := hQ'.exists_right_inv
    obtain ⟨v', rfl⟩ := hNsurj v
    have hk : MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (pe ≫ G.hom) ((thickObj R (maximalIdeal R) e G).left.basicOpen F)) r Q
        * v' - 1 ∈ RingHom.ker (jm.app _).hom := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, hv, sub_self]
    have hu := (hnil _ (hNker hk)).isUnit_one_add
    rw [add_sub_cancel] at hu
    exact isUnit_of_mul_isUnit_left hu
  · apply hNker
    rw [RingHom.mem_ker, map_sub, map_mul, hjev, hjev, hPQ, sub_self]
