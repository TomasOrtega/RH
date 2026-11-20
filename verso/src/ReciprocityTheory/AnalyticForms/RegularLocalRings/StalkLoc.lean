import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLocA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLocB

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

noncomputable section

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

variable (s) in

structure AffPres where

  V : W.Opens

  n : ℕ

  K : Ideal (MvPolynomial (Fin n) ℂ)

  iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))
  hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
    V.ι ≫ s

namespace AffPres

variable (P : AffPres s)

def secHom : MvPolynomial (Fin P.n) ℂ →+* Γ(W, P.V) :=
  P.V.topIso.hom.hom.comp (P.iso.hom.appTop.hom.comp
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom.comp (Ideal.Quotient.mk P.K)))

def ptOf (x : W) (hx : x ∈ P.V) : Ideal (MvPolynomial (Fin P.n) ℂ) :=
  (P.iso.hom.base ⟨x, hx⟩).asIdeal.comap (Ideal.Quotient.mk P.K)

def coord (x : W) (hx : x ∈ P.V) : Fin P.n → ℂ :=
  fun j => Classical.epsilon fun c : ℂ => X j - C c ∈ P.ptOf x hx

/- English proof (translation)
Establish `hcV : IsClosed ({⟨x, hx⟩} : Set P.V)`. Establish `h1 : ({⟨x, hx⟩} : Set P.V) = Subtype.val ⁻¹' {x}`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[Set.mem_singleton_iff.mp h]`. Conclude with `Set.mem_singleton x`. Introduce `h`. Conclude with `Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp (Set.mem_preimage.mp h)))`. Rewrite using `[h1]`.

Conclude with `hc.preimage continuous_subtype_val`. Establish `hcy : IsClosed ({P.iso.hom.base ⟨x, hx⟩} : Set (Spec (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))))`. Establish `h` using `(Scheme.homeoOfIso P.iso).isClosedMap _ hcV`. Use `first`. Consider the case `(convert h using 1; exact Set.image_singleton.symm)`.

Consider the case `(convert h using 1; ext z; simp)`. Consider the case `(simp only [Set.image_singleton] at h; exact h)`. Establish `hmax : (P.iso.hom.base ⟨x, hx⟩).asIdeal.IsMaximal` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hcy`. Establish `hmax' : (P.ptOf x hx).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Take `⟨q, hq⟩` from `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hmax'`.

Establish `hq' : P.ptOf x hx = ptIdeal q`. Rewrite using `[hq]`. Use extensionality with `h`. Rewrite using `[MvPolynomial.mem_vanishingIdeal_singleton_iff]`. Simplify using `only [ptIdeal, RingHom.mem_ker]`.

Use `first`. Consider the case `rw [MvPolynomial.coe_aeval_eq_eval]`. Consider the case `exact Iff.rfl`. Consider the case `simp [MvPolynomial.aeval_eq_eval]`. Establish `hcoord : P.coord x hx = q`.

Use function extensionality and compare the values at `j`. Establish `hex : ∃ c : ℂ, X j - C c ∈ P.ptOf x hx`. Use `⟨q j, ?_⟩` and prove the remaining obligations. Rewrite using `[hq']`. Simplify using `[ptIdeal]`.

Establish `hspec` using `Classical.epsilon_spec hex`. Establish `h2 : X j - C (P.coord x hx j) ∈ ptIdeal q` using `hq'.le hspec`. Simplify using `only [ptIdeal, RingHom.mem_ker] at h2`. Simplify using `only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at h2`. Conclude with `(sub_eq_zero.mp h2).symm`.

Rewrite using `[hq', hcoord]`.
-/
theorem ptOf_eq_ptIdeal (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    P.ptOf x hx = ptIdeal (P.coord x hx) := by
  classical
  have hcV : IsClosed ({⟨x, hx⟩} : Set P.V) := by
    have h1 : ({⟨x, hx⟩} : Set P.V) = Subtype.val ⁻¹' {x} := by
      ext z
      constructor
      · intro h
        rw [Set.mem_singleton_iff.mp h]
        exact Set.mem_singleton x
      · intro h
        exact Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp (Set.mem_preimage.mp h)))
    rw [h1]
    exact hc.preimage continuous_subtype_val
  have hcy : IsClosed ({P.iso.hom.base ⟨x, hx⟩} :
      Set (Spec (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))) := by
    have h := (Scheme.homeoOfIso P.iso).isClosedMap _ hcV
    first
    | (convert h using 1; exact Set.image_singleton.symm)
    | (convert h using 1; ext z; simp)
    | (simp only [Set.image_singleton] at h; exact h)
  have hmax : (P.iso.hom.base ⟨x, hx⟩).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hcy
  have hmax' : (P.ptOf x hx).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨q, hq⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hmax'
  have hq' : P.ptOf x hx = ptIdeal q := by
    rw [hq]
    ext h
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp only [ptIdeal, RingHom.mem_ker]
    first
    | rw [MvPolynomial.coe_aeval_eq_eval]
    | exact Iff.rfl
    | simp [MvPolynomial.aeval_eq_eval]
  have hcoord : P.coord x hx = q := by
    funext j
    have hex : ∃ c : ℂ, X j - C c ∈ P.ptOf x hx := by
      refine ⟨q j, ?_⟩
      rw [hq']
      simp [ptIdeal]
    have hspec := Classical.epsilon_spec hex
    have h2 : X j - C (P.coord x hx j) ∈ ptIdeal q := hq'.le hspec
    simp only [ptIdeal, RingHom.mem_ker] at h2
    simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at h2
    exact (sub_eq_zero.mp h2).symm
  rw [hq', hcoord]

/- English proof (translation)
Introduce `h hh`. Establish `hmem : h ∈ P.ptOf x hx` using `by show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base ⟨x, hx⟩).asIdeal`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hh]`. Conclude with `Ideal.zero_mem _`. Rewrite `hmem` using `[P.ptOf_eq_ptIdeal x hx hc]`.

Simplify using `only [ptIdeal, RingHom.mem_ker] at hmem`. Conclude with `hmem`.
-/
theorem eval_coord_eq_zero (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    ∀ h ∈ P.K, eval (P.coord x hx) h = 0 := by
  intro h hh
  have hmem : h ∈ P.ptOf x hx := by
    show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base ⟨x, hx⟩).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hh]
    exact Ideal.zero_mem _
  rw [P.ptOf_eq_ptIdeal x hx hc] at hmem
  simp only [ptIdeal, RingHom.mem_ker] at hmem
  exact hmem

/- English proof (translation)
Establish `hK : P.K ≤ ptIdeal p`. Introduce `h hh`. Simplify using `only [ptIdeal, RingHom.mem_ker]`. Conclude with `hp h hh`. Set `y : Spec (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))` to `(⟨ptQ P.K p, ptQ_isPrime hK⟩ : PrimeSpectrum (MvPolynomial (Fin P.n) ℂ ⧸ P.K))`.

Set `v : P.V` to `(Scheme.homeoOfIso P.iso).symm y`. Establish `hv : P.iso.hom.base v = y` using `(Scheme.homeoOfIso P.iso).apply_symm_apply y`. Establish `hcoordEq : ∀ (z : W) (hz : z ∈ P.V), IsClosed {z} → P.ptOf z hz = ptIdeal p → P.coord z hz = p`. Introduce `z hz hzc h`. Establish `h' : ptIdeal (P.coord z hz) = ptIdeal p` using `(P.ptOf_eq_ptIdeal z hz hzc).symm.trans h`.

Use function extensionality and compare the values at `j`. Establish `hm : X j - C (p j) ∈ ptIdeal (P.coord z hz)`. Rewrite using `[h']`. Simplify using `[ptIdeal]`. Simplify using `only [ptIdeal, RingHom.mem_ker] at hm`.

Simplify using `only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at hm`. Conclude with `sub_eq_zero.mp hm`. Establish `hptv : P.ptOf v.1 v.2 = ptIdeal p`. Use extensionality with `h`. Use `show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base v).asIdeal ↔ _`.

Rewrite using `[hv]`. Conclude with `mk_mem_ptQ hK h`. Establish `hclv : IsClosed ({v.1} : Set W)` using `StalkLocB.isClosed_of_comap_eq (s := s) (hover := P.hover) (v := v) (p := p) (hp := hptv)`. Use `⟨v.1, ⟨v.2, hclv, hcoordEq v.1 v.2 hclv hptv⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `x' ⟨hx', hcl', hco'⟩`.

Establish `h1 : P.ptOf x' hx' = ptIdeal p` using `by rw [P.ptOf_eq_ptIdeal x' hx' hcl', hco']`. Establish `h2 : P.iso.hom.base ⟨x', hx'⟩ = y`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show _ = ptQ P.K p`. Unfold `ptQ`.

Rewrite using `[← h1]`. Conclude with `(Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm`. Establish `h3 : (⟨x', hx'⟩ : P.V) = v` using `(Scheme.homeoOfIso P.iso).injective (h2.trans hv.symm)`. Conclude with `congrArg Subtype.val h3`.
-/
theorem existsUnique_closed_coord (p : Fin P.n → ℂ) (hp : ∀ h ∈ P.K, eval p h = 0) :
    ∃! x : W, ∃ hx : x ∈ P.V, IsClosed {x} ∧ P.coord x hx = p := by
  classical
  have hK : P.K ≤ ptIdeal p := by
    intro h hh
    simp only [ptIdeal, RingHom.mem_ker]
    exact hp h hh
  let y : Spec (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)) :=
    (⟨ptQ P.K p, ptQ_isPrime hK⟩ : PrimeSpectrum (MvPolynomial (Fin P.n) ℂ ⧸ P.K))
  let v : P.V := (Scheme.homeoOfIso P.iso).symm y
  have hv : P.iso.hom.base v = y := (Scheme.homeoOfIso P.iso).apply_symm_apply y
  have hcoordEq : ∀ (z : W) (hz : z ∈ P.V), IsClosed {z} → P.ptOf z hz = ptIdeal p →
      P.coord z hz = p := by
    intro z hz hzc h
    have h' : ptIdeal (P.coord z hz) = ptIdeal p := (P.ptOf_eq_ptIdeal z hz hzc).symm.trans h
    funext j
    have hm : X j - C (p j) ∈ ptIdeal (P.coord z hz) := by
      rw [h']
      simp [ptIdeal]
    simp only [ptIdeal, RingHom.mem_ker] at hm
    simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at hm
    exact sub_eq_zero.mp hm
  have hptv : P.ptOf v.1 v.2 = ptIdeal p := by
    ext h
    show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base v).asIdeal ↔ _
    rw [hv]
    exact mk_mem_ptQ hK h
  have hclv : IsClosed ({v.1} : Set W) :=
    StalkLocB.isClosed_of_comap_eq (s := s) (hover := P.hover) (v := v) (p := p) (hp := hptv)
  refine ⟨v.1, ⟨v.2, hclv, hcoordEq v.1 v.2 hclv hptv⟩, ?_⟩
  rintro x' ⟨hx', hcl', hco'⟩
  have h1 : P.ptOf x' hx' = ptIdeal p := by rw [P.ptOf_eq_ptIdeal x' hx' hcl', hco']
  have h2 : P.iso.hom.base ⟨x', hx'⟩ = y := by
    apply PrimeSpectrum.ext
    show _ = ptQ P.K p
    unfold ptQ
    rw [← h1]
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  have h3 : (⟨x', hx'⟩ : P.V) = v := (Scheme.homeoOfIso P.iso).injective (h2.trans hv.symm)
  exact congrArg Subtype.val h3

/- English proof (translation)
Use `set p := P.coord x hx`. Establish `hpt` using `P.ptOf_eq_ptIdeal x hx hc`. Establish `hK : P.K ≤ ptIdeal p` using `(le_ptIdeal_iff' _ _).2 (P.eval_coord_eq_zero x hx hc)`. Establish `hV : IsAffineOpen P.V` using `IsAffine.of_isIso P.iso.hom`. Set `_` to `TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨x, hx⟩ : P.V)`.

Use `hV.isLocalization_stalk ⟨x, hx⟩` as an intermediate fact. Use `set Q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal`. Set `_` to `ptQ_isPrime hK`. Establish `hloc : IsLocalization (ptQ P.K p).primeCompl (locRing P.K p)` using `isLocalization_locRing hK`. Establish `hQ : ∀ f, P.secHom f ∈ Q ↔ f ∈ ptIdeal p`.

Introduce `f`. Rewrite using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) Q]`. Express the relevant statement in the definitionally equal form `W.presheaf.germ P.V x hx (P.secHom f) ∈ _ ↔ _`. Establish `hu` using `StalkLocB.isUnit_germ_secH_iff P.V P.K P.iso ⟨x, hx⟩ f`. Express the relevant statement in the definitionally equal form `IsUnit (W.presheaf.germ P.V x hx (P.secHom f)) ↔ _ at hu`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu, not_not, ← Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `f ∈ P.ptOf x hx ↔ _`. Rewrite using `[hpt]`. Set `e : Γ(W, P.V) ≃+* (MvPolynomial (Fin P.n) ℂ ⧸ P.K)` to `(StalkLocB.phiE P.V P.K P.iso).symm`. Establish `he : ∀ f, e (P.secHom f) = Ideal.Quotient.mk P.K f` using `fun f => (StalkLocB.phiE P.V P.K P.iso).symm_apply_apply (Ideal.Quotient.mk P.K f)`.

Establish `H : Q.primeCompl.map e.toMonoidHom = (ptQ P.K p).primeCompl`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Take `⟨f, rfl⟩` from `StalkLocB.secH_surjective P.V P.K P.iso a`.

Use `show e (P.secHom f) ∉ ptQ P.K p`. Rewrite using `[he, mk_mem_ptQ hK, ← hQ]`. Conclude with `ha`. Introduce `hy`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Use `⟨P.secHom f, ?_, he f⟩` and prove the remaining obligations. Use `show P.secHom f ∉ Q`. Rewrite using `[hQ, ← mk_mem_ptQ hK]`. Conclude with `hy`. Use `⟨IsLocalization.ringEquivOfRingEquiv (W.presheaf.stalk x) (locRing P.K p) e H, fun f => ?_⟩` and prove the remaining obligations.

Establish `h1` using `IsLocalization.ringEquivOfRingEquiv_eq (S := W.presheaf.stalk x) (Q := locRing P.K p) H (P.secHom f)`. Rewrite `h1` using `[he, algebraMap_quot_mk]`. Conclude with `h1`.
-/
theorem exists_stalkEquiv (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    ∃ ψ : W.presheaf.stalk x ≃+* locRing P.K (P.coord x hx), ∀ f : MvPolynomial (Fin P.n) ℂ,
      ψ (W.presheaf.germ P.V x hx (P.secHom f)) = algebraMap _ (locRing P.K (P.coord x hx)) f := by
  set p := P.coord x hx
  have hpt := P.ptOf_eq_ptIdeal x hx hc
  have hK : P.K ≤ ptIdeal p := (le_ptIdeal_iff' _ _).2 (P.eval_coord_eq_zero x hx hc)
  have hV : IsAffineOpen P.V := IsAffine.of_isIso P.iso.hom
  let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨x, hx⟩ : P.V)
  have := hV.isLocalization_stalk ⟨x, hx⟩
  set Q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let _ := ptQ_isPrime hK
  have hloc : IsLocalization (ptQ P.K p).primeCompl (locRing P.K p) := isLocalization_locRing hK
  have hQ : ∀ f, P.secHom f ∈ Q ↔ f ∈ ptIdeal p := by
    intro f
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) Q]
    change W.presheaf.germ P.V x hx (P.secHom f) ∈ _ ↔ _
    have hu := StalkLocB.isUnit_germ_secH_iff P.V P.K P.iso ⟨x, hx⟩ f
    change IsUnit (W.presheaf.germ P.V x hx (P.secHom f)) ↔ _ at hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu, not_not, ← Ideal.mem_comap]
    change f ∈ P.ptOf x hx ↔ _
    rw [hpt]
  let e : Γ(W, P.V) ≃+* (MvPolynomial (Fin P.n) ℂ ⧸ P.K) := (StalkLocB.phiE P.V P.K P.iso).symm
  have he : ∀ f, e (P.secHom f) = Ideal.Quotient.mk P.K f := fun f =>
    (StalkLocB.phiE P.V P.K P.iso).symm_apply_apply (Ideal.Quotient.mk P.K f)
  have H : Q.primeCompl.map e.toMonoidHom = (ptQ P.K p).primeCompl := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨f, rfl⟩ := StalkLocB.secH_surjective P.V P.K P.iso a
      show e (P.secHom f) ∉ ptQ P.K p
      rw [he, mk_mem_ptQ hK, ← hQ]
      exact ha
    · intro hy
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨P.secHom f, ?_, he f⟩
      show P.secHom f ∉ Q
      rw [hQ, ← mk_mem_ptQ hK]
      exact hy
  refine ⟨IsLocalization.ringEquivOfRingEquiv (W.presheaf.stalk x) (locRing P.K p) e H, fun f => ?_⟩
  have h1 := IsLocalization.ringEquivOfRingEquiv_eq (S := W.presheaf.stalk x) (Q := locRing P.K p) H
    (P.secHom f)
  rw [he, algebraMap_quot_mk] at h1
  exact h1

def stalkEquiv (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    W.presheaf.stalk x ≃+* locRing P.K (P.coord x hx) :=
  Classical.choose (P.exists_stalkEquiv x hx hc)

/- English proof (translation)
The claim follows from `Classical.choose_spec (P.exists_stalkEquiv x hx hc) f`.
-/
theorem stalkEquiv_germ (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) (f : MvPolynomial (Fin P.n) ℂ) :
    P.stalkEquiv x hx hc (W.presheaf.germ P.V x hx (P.secHom f)) =
      algebraMap _ (locRing P.K (P.coord x hx)) f := Classical.choose_spec (P.exists_stalkEquiv x hx hc) f

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h haveI := h first`. Consider the case `exact IsRegularLocalRing.of_ringEquiv (P.stalkEquiv x hx hc)`. Consider the case `exact IsRegularLocalRing.of_ringEquiv (e := P.stalkEquiv x hx hc)`. Introduce `h haveI := h first`.

Consider the case `exact IsRegularLocalRing.of_ringEquiv (P.stalkEquiv x hx hc).symm`. Consider the case `exact IsRegularLocalRing.of_ringEquiv (e := (P.stalkEquiv x hx hc).symm)`.
-/
theorem isRegularLocalRing_stalk_iff (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    IsRegularLocalRing (W.presheaf.stalk x) ↔ IsRegularLocalRing (locRing P.K (P.coord x hx)) := by
  constructor
  · intro h
    haveI := h
    first
    | exact IsRegularLocalRing.of_ringEquiv (P.stalkEquiv x hx hc)
    | exact IsRegularLocalRing.of_ringEquiv (e := P.stalkEquiv x hx hc)
  · intro h
    haveI := h
    first
    | exact IsRegularLocalRing.of_ringEquiv (P.stalkEquiv x hx hc).symm
    | exact IsRegularLocalRing.of_ringEquiv (e := (P.stalkEquiv x hx hc).symm)

/- English proof (translation)
Conclude with `ringKrullDim_eq_of_ringEquiv (P.stalkEquiv x hx hc)`.
-/
theorem ringKrullDim_stalk (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    ringKrullDim (W.presheaf.stalk x) = ringKrullDim (locRing P.K (P.coord x hx)) := by
  exact ringKrullDim_eq_of_ringEquiv (P.stalkEquiv x hx hc)

/- English proof (translation)
Establish `hK : P.K ≤ ptIdeal (P.coord x hx)`. Rewrite using `[← P.ptOf_eq_ptIdeal x hx hc]`. Introduce `h hh`. Use `show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base ⟨x, hx⟩).asIdeal`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hh]`.

Conclude with `Ideal.zero_mem _`. Use `haveI := isLocalRing_locRing hK`. Rewrite using `[← maximalIdeal_locRing hK]`. Conclude with `IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _)`.
-/
theorem map_maximalIdeal_stalk (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    (IsLocalRing.maximalIdeal (W.presheaf.stalk x)).map (P.stalkEquiv x hx hc) =
      Ideal.map (algebraMap _ (locRing P.K (P.coord x hx))) (ptIdeal (P.coord x hx)) := by
  have hK : P.K ≤ ptIdeal (P.coord x hx) := by
    rw [← P.ptOf_eq_ptIdeal x hx hc]
    intro h hh
    show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base ⟨x, hx⟩).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hh]
    exact Ideal.zero_mem _
  haveI := isLocalRing_locRing hK
  rw [← maximalIdeal_locRing hK]
  exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _)

/- English proof (translation)
Unfold `FinalTheorems.Rsp`. Rewrite using `[← P.ringKrullDim_stalk x hx hc, ← P.map_maximalIdeal_stalk x hx hc]`. Establish `hspan : Ideal.span (Set.range fun l => P.stalkEquiv x hx hc (r l)) = (Ideal.span (Set.range r)).map (P.stalkEquiv x hx hc)`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[hspan]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by rw [h1], h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨?_, h2⟩` and prove the remaining obligations. Establish `h3` using `congrArg (Ideal.comap (P.stalkEquiv x hx hc)) h1`. Rewrite `h3` using `[Ideal.comap_map_of_bijective _ (P.stalkEquiv x hx hc).bijective, Ideal.comap_map_of_bijective _ (P.stalkEquiv x hx hc).bijective]`. Then use the resulting hypothesis.
-/
theorem rsp_iff (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) {e : ℕ} (r : Fin e → W.presheaf.stalk x) :
    FinalTheorems.Rsp (W.presheaf.stalk x) e r ↔
      Ideal.span (Set.range fun l => P.stalkEquiv x hx hc (r l)) =
        Ideal.map (algebraMap _ (locRing P.K (P.coord x hx))) (ptIdeal (P.coord x hx)) ∧
      (e : WithBot ℕ∞) = ringKrullDim (locRing P.K (P.coord x hx)) := by
  unfold FinalTheorems.Rsp
  rw [← P.ringKrullDim_stalk x hx hc, ← P.map_maximalIdeal_stalk x hx hc]
  have hspan : Ideal.span (Set.range fun l => P.stalkEquiv x hx hc (r l)) =
      (Ideal.span (Set.range r)).map (P.stalkEquiv x hx hc) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1], h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 := congrArg (Ideal.comap (P.stalkEquiv x hx hc)) h1
    rwa [Ideal.comap_map_of_bijective _ (P.stalkEquiv x hx hc).bijective,
      Ideal.comap_map_of_bijective _ (P.stalkEquiv x hx hc).bijective] at h3

end AffPres

/- English proof (translation)
Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective t`. Take `⟨⟨a, ⟨b, hb⟩⟩, rfl⟩` from `IsLocalization.mk'_surjective (ptIdeal p).primeCompl y`. Establish `hb' : b ∉ ptIdeal p` using `hb`. Use `⟨a, b, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hb'` to reduce the goal to its premises. Simplify using `only [ptIdeal, RingHom.mem_ker]`. Conclude with `h`. Use `first`. Consider the case `rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← map_mul, IsLocalization.mk'_spec]`.

Consider the case `(show Ideal.Quotient.mk _ (IsLocalization.mk' _ a ⟨b, hb⟩) * Ideal.Quotient.mk _ (algebraMap _ _ b) = Ideal.Quotient.mk _ (algebraMap _ _ a)`. Rewrite using `[← map_mul, IsLocalization.mk'_spec])`.
-/
theorem exists_mk_locRing {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (t : locRing K p) : ∃ a b : MvPolynomial (Fin n) ℂ, eval p b ≠ 0 ∧
      t * algebraMap _ (locRing K p) b = algebraMap _ (locRing K p) a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (ptIdeal p).primeCompl y
  have hb' : b ∉ ptIdeal p := hb
  refine ⟨a, b, ?_, ?_⟩
  · intro h
    apply hb'
    simp only [ptIdeal, RingHom.mem_ker]
    exact h
  · first
    | rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
        IsLocalization.mk'_spec]
    | (show Ideal.Quotient.mk _ (IsLocalization.mk' _ a ⟨b, hb⟩) *
          Ideal.Quotient.mk _ (algebraMap _ _ b) = Ideal.Quotient.mk _ (algebraMap _ _ a)
       rw [← map_mul, IsLocalization.mk'_spec])

end

end ReciprocityTheory.AnForm.R
