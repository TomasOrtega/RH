import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

noncomputable section

namespace StalkLocB

variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))

def secH : MvPolynomial (Fin n) ℂ →+* Γ(W, V) :=
  V.topIso.hom.hom.comp (iso.hom.appTop.hom.comp
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom.comp (Ideal.Quotient.mk K)))

/- English proof (translation)
Establish `h1 : Function.Surjective V.topIso.hom.hom` using `(V.topIso.commRingCatIsoToRingEquiv).surjective`. Use `haveI : IsIso iso.hom.appTop := by`. Rewrite using `[← Scheme.Γ_map_op]`. Conclude with `(Scheme.Γ.mapIso iso.op).isIso_hom`. Establish `h2 : Function.Surjective iso.hom.appTop.hom` using `(asIso iso.hom.appTop).commRingCatIsoToRingEquiv.surjective`.

Establish `h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom` using `(Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).symm.commRingCatIsoToRingEquiv.surjective`. Conclude with `h1.comp (h2.comp (h3.comp Ideal.Quotient.mk_surjective))`.
-/
theorem secH_surjective : Function.Surjective (secH V K iso) := by
  have h1 : Function.Surjective V.topIso.hom.hom := (V.topIso.commRingCatIsoToRingEquiv).surjective
  haveI : IsIso iso.hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso iso.op).isIso_hom
  have h2 : Function.Surjective iso.hom.appTop.hom :=
    (asIso iso.hom.appTop).commRingCatIsoToRingEquiv.surjective
  have h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom :=
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp (h2.comp (h3.comp Ideal.Quotient.mk_surjective))

def phiH : (MvPolynomial (Fin n) ℂ ⧸ K) →+* Γ(W, V) :=
  V.topIso.hom.hom.comp (iso.hom.appTop.hom.comp
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom)

/- English proof (translation)
Establish `h1 : Function.Bijective V.topIso.hom.hom` using `(V.topIso.commRingCatIsoToRingEquiv).bijective`. Use `haveI : IsIso iso.hom.appTop := by`. Rewrite using `[← Scheme.Γ_map_op]`. Conclude with `(Scheme.Γ.mapIso iso.op).isIso_hom`. Establish `h2 : Function.Bijective iso.hom.appTop.hom` using `(asIso iso.hom.appTop).commRingCatIsoToRingEquiv.bijective`.

Establish `h3 : Function.Bijective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom` using `(Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).symm.commRingCatIsoToRingEquiv.bijective`. Conclude with `h1.comp (h2.comp h3)`.
-/
theorem phiH_bijective : Function.Bijective (phiH V K iso) := by
  have h1 : Function.Bijective V.topIso.hom.hom := (V.topIso.commRingCatIsoToRingEquiv).bijective
  haveI : IsIso iso.hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso iso.op).isIso_hom
  have h2 : Function.Bijective iso.hom.appTop.hom :=
    (asIso iso.hom.appTop).commRingCatIsoToRingEquiv.bijective
  have h3 : Function.Bijective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv.hom :=
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).symm.commRingCatIsoToRingEquiv.bijective
  exact h1.comp (h2.comp h3)

def phiE : (MvPolynomial (Fin n) ℂ ⧸ K) ≃+* Γ(W, V) :=
  RingEquiv.ofBijective _ (phiH_bijective V K iso)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phiE_mk (f : MvPolynomial (Fin n) ℂ) :
    phiE V K iso (Ideal.Quotient.mk K f) = secH V K iso f := rfl

/- English proof (translation)
Establish `hSpec : IsUnit ((Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))).presheaf.germ ⊤ (iso.hom.base v) trivial ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f))) ↔ Ideal.Quotient.mk K f ∉ (iso.hom.base v).asIdeal`. Establish `key` using `Scheme.mem_basicOpen (Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))) ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f)) (iso.hom.base v) trivial`. Rewrite `key` using `[basicOpen_eq_of_affine]`. Conclude with `key.symm.trans (PrimeSpectrum.mem_basicOpen _ _)`. Establish `hMap : ∀ ρ, IsUnit (V.toScheme.presheaf.germ ⊤ v trivial (iso.hom.appTop ρ)) ↔ IsUnit ((Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))).presheaf.germ ⊤ (iso.hom.base v) trivial ρ)`.

Introduce `ρ`. Express the relevant statement in the definitionally equal form `IsUnit (V.toScheme.presheaf.germ ((TopologicalSpace.Opens.map iso.hom.base).obj ⊤) v trivial (iso.hom.app ⊤ ρ)) ↔ _`. Rewrite using `[← Scheme.Hom.germ_stalkMap_apply iso.hom ⊤ v trivial ρ]`. Use `haveI : IsLocalHom (iso.hom.stalkMap v).hom := iso.hom.toLRSHom.prop v`. Conclude with `isUnit_map_iff (iso.hom.stalkMap v).hom _`.

Establish `hOpen : ∀ τ, IsUnit (W.presheaf.germ V v.1 v.2 (V.topIso.hom τ)) ↔ IsUnit (V.toScheme.presheaf.germ ⊤ v trivial τ)`. Introduce `τ`. Rewrite using `[Scheme.Opens.topIso_hom]`. Use `erw [TopCat.Presheaf.germ_res_apply]`. Establish `h` using `congrArg (fun g => CommRingCat.Hom.hom g τ) (Scheme.Opens.germ_stalkIso_hom V (V := ⊤) v trivial)`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at h`. Use `Iff.trans ?_ (MulEquiv.isUnit_map (V.stalkIso v).commRingCatIsoToRingEquiv.toMulEquiv)` and prove the remaining obligations. Conclude with `iff_of_eq (congrArg IsUnit h.symm)`. Use `show IsUnit (W.presheaf.germ V v.1 v.2 (V.topIso.hom (iso.hom.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f))))) ↔ _`. Rewrite using `[hOpen, hMap, hSpec]`.
-/
theorem isUnit_germ_secH_iff (v : V) (f : MvPolynomial (Fin n) ℂ) :
    IsUnit (W.presheaf.germ V v.1 v.2 (secH V K iso f)) ↔
      Ideal.Quotient.mk K f ∉ (iso.hom.base v).asIdeal := by

  have hSpec : IsUnit ((Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))).presheaf.germ ⊤ (iso.hom.base v) trivial
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f))) ↔
      Ideal.Quotient.mk K f ∉ (iso.hom.base v).asIdeal := by
    have key := Scheme.mem_basicOpen (Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f)) (iso.hom.base v) trivial
    rw [basicOpen_eq_of_affine] at key
    exact key.symm.trans (PrimeSpectrum.mem_basicOpen _ _)

  have hMap : ∀ ρ, IsUnit (V.toScheme.presheaf.germ ⊤ v trivial (iso.hom.appTop ρ)) ↔
      IsUnit ((Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))).presheaf.germ ⊤ (iso.hom.base v) trivial ρ) := by
    intro ρ
    change IsUnit (V.toScheme.presheaf.germ ((TopologicalSpace.Opens.map iso.hom.base).obj ⊤) v trivial
      (iso.hom.app ⊤ ρ)) ↔ _
    rw [← Scheme.Hom.germ_stalkMap_apply iso.hom ⊤ v trivial ρ]
    haveI : IsLocalHom (iso.hom.stalkMap v).hom := iso.hom.toLRSHom.prop v
    exact isUnit_map_iff (iso.hom.stalkMap v).hom _

  have hOpen : ∀ τ, IsUnit (W.presheaf.germ V v.1 v.2 (V.topIso.hom τ)) ↔
      IsUnit (V.toScheme.presheaf.germ ⊤ v trivial τ) := by
    intro τ
    rw [Scheme.Opens.topIso_hom]
    erw [TopCat.Presheaf.germ_res_apply]
    have h := congrArg (fun g => CommRingCat.Hom.hom g τ)
      (Scheme.Opens.germ_stalkIso_hom V (V := ⊤) v trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    refine Iff.trans ?_ (MulEquiv.isUnit_map (V.stalkIso v).commRingCatIsoToRingEquiv.toMulEquiv)
    exact iff_of_eq (congrArg IsUnit h.symm)
  show IsUnit (W.presheaf.germ V v.1 v.2 (V.topIso.hom (iso.hom.appTop
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K f))))) ↔ _
  rw [hOpen, hMap, hSpec]

variable {K iso} in
/- English proof (translation)
Establish `h` using `congrArg (fun g => CommRingCat.Hom.hom g ((Scheme.ΓSpecIso (.of ℂ)).inv c)) (congrArg Scheme.Hom.appTop hover)`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h`. Establish `hnat` using `congrArg (fun g => CommRingCat.Hom.hom g c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat`. Rewrite `h` using `[← hnat]`.

Use `show V.topIso.hom (iso.hom.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv (Ideal.Quotient.mk K (C c)))) = _`. Establish `hc : Ideal.Quotient.mk K (C c) = algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K) c` using `rfl`. Rewrite using `[hc]`. Use `erw [h]`. Rewrite using `[Scheme.Opens.topIso_hom, Scheme.Hom.appTop, Scheme.Opens.ι_app]`.

Use `erw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem secH_C (s : W ⟶ Spec (.of ℂ))
    (hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
      V.ι ≫ s) (c : ℂ) :
    secH V K iso (C c) = W.presheaf.map (homOfLE le_top : V ⟶ ⊤).op
      (s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) := by
  have h := congrArg (fun g => CommRingCat.Hom.hom g ((Scheme.ΓSpecIso (.of ℂ)).inv c))
    (congrArg Scheme.Hom.appTop hover)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  have hnat := congrArg (fun g => CommRingCat.Hom.hom g c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  rw [← hnat] at h
  show V.topIso.hom (iso.hom.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) ℂ ⧸ K))).inv
    (Ideal.Quotient.mk K (C c)))) = _
  have hc : Ideal.Quotient.mk K (C c) = algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K) c := rfl
  rw [hc]
  erw [h]
  rw [Scheme.Opens.topIso_hom, Scheme.Hom.appTop, Scheme.Opens.ι_app]
  erw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

variable {K iso} in
/- English proof (translation)
Rewrite using `[secH_C V s hover c, TopCat.Presheaf.germ_res_apply]`.
-/
theorem germ_secH_C (s : W ⟶ Spec (.of ℂ))
    (hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
      V.ι ≫ s) (x : W) (hx : x ∈ V) (c : ℂ) :
    W.presheaf.germ V x hx (secH V K iso (C c)) =
      W.presheaf.germ ⊤ x trivial (s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) := by
  rw [secH_C V s hover c, TopCat.Presheaf.germ_res_apply]

variable {K iso} in

/- English proof (translation)
Use `set x : W := v.1 with hxdef`. Establish `hV : IsAffineOpen V` using `IsAffine.of_isIso iso.hom`. Establish `hunit : ∀ f, IsUnit (W.presheaf.germ V x v.2 (secH V K iso f)) ↔ eval p f ≠ 0`. Introduce `f`. Rewrite using `[isUnit_germ_secH_iff, ← Ideal.mem_comap, hp]`.

Simplify using `[ptIdeal, RingHom.mem_ker]`. Set `γ : ℂ →+* W.presheaf.stalk x` to `(W.presheaf.germ ⊤ x trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom)`. Establish `hγ : ∀ c, γ c = W.presheaf.germ V x v.2 (secH V K iso (C c))` using `fun c => (germ_secH_C V s hover x v.2 c).symm`. Establish `KC : ∀ t : W.presheaf.stalk x, ∃ c : ℂ, t - γ c ∈ IsLocalRing.maximalIdeal _`. Introduce `t`.

Set `_` to `TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨x, v.2⟩`. Use `hV.isLocalization_stalk ⟨x, v.2⟩` as an intermediate fact. Use `set Q := (hV.primeIdealOf ⟨x, v.2⟩).asIdeal`. Take `⟨⟨a, b⟩, rfl⟩` from `IsLocalization.mk'_surjective Q.primeCompl t`. Take `⟨f, rfl⟩` from `secH_surjective V K iso a`.

Take `⟨g, hg⟩` from `secH_surjective V K iso (b : Γ(W, V))`. Establish `hb : algebraMap Γ(W, V) (W.presheaf.stalk x) b ∉ IsLocalRing.maximalIdeal _`. Rewrite using `[IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) Q]`. Conclude with `b.2`. Establish `hgb : W.presheaf.germ V x v.2 (secH V K iso g) = algebraMap Γ(W, V) _ b`.

Rewrite using `[hg]`. Both sides reduce to the same expression. Establish `hg0 : eval p g ≠ 0`. Rewrite using `[← hunit, hgb]`. Assume the negation of the conclusion as `h`.

Conclude with `hb ((IsLocalRing.mem_maximalIdeal _).2 h)`. Use `⟨eval p f / eval p g, ?_⟩` and prove the remaining obligations. Establish `hspec` using `IsLocalization.mk'_spec (W.presheaf.stalk x) (secH V K iso f) b`. Establish `hfa : algebraMap Γ(W, V) (W.presheaf.stalk x) (secH V K iso f) = W.presheaf.germ V x v.2 (secH V K iso f)` using `rfl`. Establish `hzero : W.presheaf.germ V x v.2 (secH V K iso (f - C (eval p f / eval p g) * g)) ∈ IsLocalRing.maximalIdeal _`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]`. Simplify using `[eval_sub, eval_mul, eval_C, div_mul_cancel₀ _ hg0]`. Establish `hprod : (IsLocalization.mk' (W.presheaf.stalk x) (secH V K iso f) b - γ (eval p f / eval p g)) * algebraMap Γ(W, V) _ b = W.presheaf.germ V x v.2 (secH V K iso (f - C (eval p f / eval p g) * g))`. Rewrite using `[sub_mul, hspec, hfa, hγ, ← hgb, map_sub, map_sub, map_mul, map_mul]`. Rewrite `hzero` using `[← hprod]`.

Conclude with `((IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_or_mem hzero).resolve_right hb`. Use `closure_subset_iff_isClosed.mp ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hxy : x ⤳ y` using `specializes_iff_mem_closure.2 hy`. Take `⟨U, hU, hyU, -⟩` from `exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : W.Opens) from trivial)`.

Establish `hxU : x ∈ U` using `hxy.mem_open U.isOpen hyU`. Set `_` to `TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨x, hxU⟩`. Use `hU.isLocalization_stalk ⟨x, hxU⟩` as an intermediate fact. Use `set P := hU.primeIdealOf ⟨x, hxU⟩`. Set `β : ℂ →+* Γ(W, U)` to `(W.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom)`.

Establish `hβ : ∀ c, W.presheaf.germ U x hxU (β c) = γ c` using `fun c => TopCat.Presheaf.germ_res_apply _ _ _ _ _`. Establish `hmax : P.asIdeal.IsMaximal`. Rewrite using `[Ideal.isMaximal_iff]`. Use `⟨(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, fun J b hPJ hb hbJ => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `KC (W.presheaf.germ U x hxU b)`.

Establish `hmem : b - β c ∈ P.asIdeal`. Rewrite using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) P.asIdeal]`. Use `show W.presheaf.germ U x hxU (b - β c) ∈ _`. Rewrite using `[map_sub, hβ]`. Conclude with `hc`.

Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Apply `hb` to reduce the goal to its premises. Simplify using `using hmem`. Establish `hβJ : β c ∈ J`.

Establish `h1` using `J.sub_mem hbJ (hPJ hmem)`. Simplify using `using h1`. Establish `hu : IsUnit (β c)` using `(isUnit_iff_ne_zero.2 hc0).map β`. Rewrite using `[Ideal.eq_top_of_isUnit_mem J hβJ hu]`. Conclude with `Submodule.mem_top`.

Establish `hcl : IsClosed ({P} : Set (PrimeSpectrum Γ(W, U)))` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal P).2 hmax`. Establish `hsp : (⟨x, hxU⟩ : U) ⤳ ⟨y, hyU⟩` using `(subtype_specializes_iff _ _).2 hxy`. Establish `hsp' : P ⤳ hU.primeIdealOf ⟨y, hyU⟩` using `hsp.map hU.isoSpec.hom.continuous`. Establish `heq : hU.primeIdealOf ⟨y, hyU⟩ = P`. Use `specializes_iff_mem_closure.1 hsp'` as an intermediate fact.

Rewrite `this` using `[hcl.closure_eq]`. Then use the resulting hypothesis. Establish `hyx : (⟨y, hyU⟩ : U) = ⟨x, hxU⟩` using `hU.isoSpec.hom.isOpenEmbedding.injective heq`. Conclude with `congrArg Subtype.val hyx`.
-/
theorem isClosed_of_comap_eq (s : W ⟶ Spec (.of ℂ))
    (hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
      V.ι ≫ s) (v : V) (p : Fin n → ℂ)
    (hp : (iso.hom.base v).asIdeal.comap (Ideal.Quotient.mk K) = ptIdeal p) :
    IsClosed ({v.1} : Set W) := by
  set x : W := v.1 with hxdef
  have hV : IsAffineOpen V := IsAffine.of_isIso iso.hom
  have hunit : ∀ f, IsUnit (W.presheaf.germ V x v.2 (secH V K iso f)) ↔ eval p f ≠ 0 := by
    intro f
    rw [isUnit_germ_secH_iff, ← Ideal.mem_comap, hp]
    simp [ptIdeal, RingHom.mem_ker]
  let γ : ℂ →+* W.presheaf.stalk x := (W.presheaf.germ ⊤ x trivial).hom.comp
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom)
  have hγ : ∀ c, γ c = W.presheaf.germ V x v.2 (secH V K iso (C c)) :=
    fun c => (germ_secH_C V s hover x v.2 c).symm
  have KC : ∀ t : W.presheaf.stalk x, ∃ c : ℂ, t - γ c ∈ IsLocalRing.maximalIdeal _ := by
    intro t
    let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨x, v.2⟩
    have := hV.isLocalization_stalk ⟨x, v.2⟩
    set Q := (hV.primeIdealOf ⟨x, v.2⟩).asIdeal
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl t
    obtain ⟨f, rfl⟩ := secH_surjective V K iso a
    obtain ⟨g, hg⟩ := secH_surjective V K iso (b : Γ(W, V))
    have hb : algebraMap Γ(W, V) (W.presheaf.stalk x) b ∉ IsLocalRing.maximalIdeal _ := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) Q]
      exact b.2
    have hgb : W.presheaf.germ V x v.2 (secH V K iso g) = algebraMap Γ(W, V) _ b := by
      rw [hg]; rfl
    have hg0 : eval p g ≠ 0 := by
      rw [← hunit, hgb]
      by_contra h
      exact hb ((IsLocalRing.mem_maximalIdeal _).2 h)
    refine ⟨eval p f / eval p g, ?_⟩
    have hspec := IsLocalization.mk'_spec (W.presheaf.stalk x) (secH V K iso f) b
    have hfa : algebraMap Γ(W, V) (W.presheaf.stalk x) (secH V K iso f) =
        W.presheaf.germ V x v.2 (secH V K iso f) := rfl
    have hzero : W.presheaf.germ V x v.2 (secH V K iso (f - C (eval p f / eval p g) * g)) ∈
        IsLocalRing.maximalIdeal _ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
      simp [eval_sub, eval_mul, eval_C, div_mul_cancel₀ _ hg0]
    have hprod : (IsLocalization.mk' (W.presheaf.stalk x) (secH V K iso f) b -
        γ (eval p f / eval p g)) * algebraMap Γ(W, V) _ b =
        W.presheaf.germ V x v.2 (secH V K iso (f - C (eval p f / eval p g) * g)) := by
      rw [sub_mul, hspec, hfa, hγ, ← hgb, map_sub, map_sub, map_mul, map_mul]
    rw [← hprod] at hzero
    exact ((IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_or_mem hzero).resolve_right hb
  refine closure_subset_iff_isClosed.mp ?_
  intro y hy
  have hxy : x ⤳ y := specializes_iff_mem_closure.2 hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : W.Opens) from trivial)
  have hxU : x ∈ U := hxy.mem_open U.isOpen hyU
  let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  set P := hU.primeIdealOf ⟨x, hxU⟩
  let β : ℂ →+* Γ(W, U) := (W.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
    (s.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom)
  have hβ : ∀ c, W.presheaf.germ U x hxU (β c) = γ c := fun c =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hmax : P.asIdeal.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, fun J b hPJ hb hbJ => ?_⟩
    obtain ⟨c, hc⟩ := KC (W.presheaf.germ U x hxU b)
    have hmem : b - β c ∈ P.asIdeal := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) P.asIdeal]
      show W.presheaf.germ U x hxU (b - β c) ∈ _
      rw [map_sub, hβ]
      exact hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hb
      simpa using hmem
    have hβJ : β c ∈ J := by
      have h1 := J.sub_mem hbJ (hPJ hmem)
      simpa using h1
    have hu : IsUnit (β c) := (isUnit_iff_ne_zero.2 hc0).map β
    rw [Ideal.eq_top_of_isUnit_mem J hβJ hu]
    exact Submodule.mem_top
  have hcl : IsClosed ({P} : Set (PrimeSpectrum Γ(W, U))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).2 hmax
  have hsp : (⟨x, hxU⟩ : U) ⤳ ⟨y, hyU⟩ := (subtype_specializes_iff _ _).2 hxy
  have hsp' : P ⤳ hU.primeIdealOf ⟨y, hyU⟩ := hsp.map hU.isoSpec.hom.continuous
  have heq : hU.primeIdealOf ⟨y, hyU⟩ = P := by
    have := specializes_iff_mem_closure.1 hsp'
    rwa [hcl.closure_eq] at this
  have hyx : (⟨y, hyU⟩ : U) = ⟨x, hxU⟩ := hU.isoSpec.hom.isOpenEmbedding.injective heq
  exact congrArg Subtype.val hyx

end StalkLocB
end
end ReciprocityTheory.AnForm.R
