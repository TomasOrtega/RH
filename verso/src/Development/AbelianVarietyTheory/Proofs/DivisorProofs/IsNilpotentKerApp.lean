import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutAppLEOfIsPullbackOfIsAffine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.NilThicken

/- English proof (translation)
Use `set J : Ideal B := Ideal.map a.hom (RingHom.ker c.hom)`. Set `π : B ⟶ CommRingCat.of (B ⧸ J)` to `CommRingCat.ofHom (Ideal.Quotient.mk J)`. Set `e` to `RingHom.quotientKerEquivOfSurjective hc`. Set `σ : C ⟶ CommRingCat.of (B ⧸ J)` to `CommRingCat.ofHom ((Ideal.quotientMap J a.hom (Ideal.le_comap_map)).comp e.symm.toRingHom)`. Establish `w : a ≫ π = c ≫ σ`.

Use extensionality with `x`. Establish `hx : e.symm (c.hom x) = Ideal.Quotient.mk _ x`. Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `[π, σ, hx]`.

Introduce `x hx`. Establish `h1 : (b ≫ h.desc π σ w).hom x = π.hom x` using `by rw [h.inl_desc]`. Rewrite `h1` using `[CommRingCat.comp_apply, (RingHom.mem_ker).mp hx, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h1.symm`.
-/
theorem ker_inl_le_map_ker_of_isPushout {A B C D : CommRingCat.{0}} {a : A ⟶ B} {c : A ⟶ C}
    {b : B ⟶ D} {d : C ⟶ D} (h : IsPushout a c b d) (hc : Function.Surjective c.hom) :
    RingHom.ker b.hom ≤ Ideal.map a.hom (RingHom.ker c.hom) := by
  set J : Ideal B := Ideal.map a.hom (RingHom.ker c.hom)
  let π : B ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let e := RingHom.quotientKerEquivOfSurjective hc
  let σ : C ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom
    ((Ideal.quotientMap J a.hom (Ideal.le_comap_map)).comp e.symm.toRingHom)
  have w : a ≫ π = c ≫ σ := by
    ext x
    have hx : e.symm (c.hom x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp [π, σ, hx]
  intro x hx
  have h1 : (b ≫ h.desc π σ w).hom x = π.hom x := by rw [h.inl_desc]
  rw [CommRingCat.comp_apply, (RingHom.mem_ker).mp hx, map_zero] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

/- English proof (translation)
Introduce `R₁ R₀ g Y₁ Y₀ p₁ p₀ i hpb hg hnil U hU`. Establish `P` using `GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y₁ Y₀ (Spec R₁) (Spec R₀) i p₀ p₁ (Spec.map g) hpb inferInstance inferInstance U hU`. Establish `hnat` using `Scheme.ΓSpecIso_naturality g`. Use `set c := (Spec.map g).appTop`. Establish `hcker : RingHom.ker c.hom = Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom)`.

Use extensionality with `x`. Simplify using `only [RingHom.mem_ker, Ideal.mem_comap]`. Use `congrArg (fun φ => φ.hom x) hnat` as an intermediate fact. Simplify using `only [CommRingCat.comp_apply] at this`. Rewrite using `[← this]`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite using `[h0, map_zero]`. Introduce `h0`. Establish `hinj` using `((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom)).1`.

Conclude with `hinj (by rw [h0, map_zero])`. Establish `hcs : Function.Surjective c.hom`. Introduce `y`. Take `⟨r, hr⟩` from `hg ((Scheme.ΓSpecIso R₀).hom y)`. Take `⟨x, hx⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).2 r`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Use `congrArg (fun φ => φ.hom x) hnat` as an intermediate fact. Simplify using `only [CommRingCat.comp_apply] at this`. Apply `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom).1` to reduce the goal to its premises. Rewrite using `[this, hx, hr]`.

Take `⟨n, hn⟩` from `hnil`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hle` using `ker_inl_le_map_ker_of_isPushout P hcs`. Establish `hJ : (Ideal.map (p₁.appLE ⊤ U (fun _ _ => trivial)).hom (RingHom.ker c.hom)) ^ n = ⊥`. Rewrite using `[← Ideal.map_pow, hcker]`.

Establish `h2 : (Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom)) ^ n = ⊥`. Apply `le_bot_iff.mp` to reduce the goal to its premises. Use `(Ideal.le_comap_pow _ n).trans ?_` and prove the remaining obligations. Rewrite using `[show RingHom.ker g.hom ^ n = ⊥ from hn]`. Introduce `x hx`.

Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot]`. Rewrite using `[Ideal.mem_bot]`. Conclude with `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).1 (by rw [hx, map_zero])`. Rewrite using `[h2, Ideal.map_bot]`. Conclude with `le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans hJ.le)`.
-/
theorem isNilpotent_ker_app :
    ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁)
      (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) →
      Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → ∀ U : Y₁.Opens, IsAffineOpen U →
      IsNilpotent (RingHom.ker (i.app U).hom) := by
  intro R₁ R₀ g Y₁ Y₀ p₁ p₀ i hpb hg hnil U hU
  have P := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y₁ Y₀ (Spec R₁) (Spec R₀)
    i p₀ p₁ (Spec.map g) hpb inferInstance inferInstance U hU
  have hnat := Scheme.ΓSpecIso_naturality g
  set c := (Spec.map g).appTop
  have hcker : RingHom.ker c.hom = Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom) := by
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    have := congrArg (fun φ => φ.hom x) hnat
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0
      have hinj := ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom)).1
      exact hinj (by rw [h0, map_zero])
  have hcs : Function.Surjective c.hom := by
    intro y
    obtain ⟨r, hr⟩ := hg ((Scheme.ΓSpecIso R₀).hom y)
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).2 r
    refine ⟨x, ?_⟩
    have := congrArg (fun φ => φ.hom x) hnat
    simp only [CommRingCat.comp_apply] at this
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom).1
    rw [this, hx, hr]
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have hle := ker_inl_le_map_ker_of_isPushout P hcs
  have hJ : (Ideal.map (p₁.appLE ⊤ U (fun _ _ => trivial)).hom (RingHom.ker c.hom)) ^ n = ⊥ := by
    rw [← Ideal.map_pow, hcker]
    have h2 : (Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom)) ^ n = ⊥ := by
      apply le_bot_iff.mp
      refine (Ideal.le_comap_pow _ n).trans ?_
      rw [show RingHom.ker g.hom ^ n = ⊥ from hn]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [Ideal.mem_bot]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).1 (by rw [hx, map_zero])
    rw [h2, Ideal.map_bot]
  exact le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans hJ.le)

end GlobalTheory.NilThicken
