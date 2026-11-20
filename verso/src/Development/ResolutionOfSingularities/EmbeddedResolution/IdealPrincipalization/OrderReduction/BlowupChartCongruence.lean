import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupChartPreimages
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

universe u

section

variable {B A : Type u} [CommRing B] [CommRing A]

def eqModIdealSet (f g : B →+* A) (J : Ideal A) : Set B := {b | f b - g b ∈ J}

/- English proof (translation)
Use `show f 1 - g 1 ∈ J`. Rewrite using `[map_one, map_one, sub_self]`. Conclude with `J.zero_mem`.
-/
private theorem one_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) :
    (1 : B) ∈ eqModIdealSet f g J := by
  show f 1 - g 1 ∈ J
  rw [map_one, map_one, sub_self]
  exact J.zero_mem

/- English proof (translation)
Use `show f 0 - g 0 ∈ J`. Rewrite using `[map_zero, map_zero, sub_self]`. Conclude with `J.zero_mem`.
-/
private theorem zero_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) :
    (0 : B) ∈ eqModIdealSet f g J := by
  show f 0 - g 0 ∈ J
  rw [map_zero, map_zero, sub_self]
  exact J.zero_mem

/- English proof (translation)
Use `show f (x + y) - g (x + y) ∈ J`. Rewrite using `[map_add, map_add]`. Establish `hrw : f x + f y - (g x + g y) = (f x - g x) + (f y - g y)` using `by ring`. Rewrite using `[hrw]`. Conclude with `J.add_mem hx hy`.
-/
private theorem add_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) {x y : B}
    (hx : x ∈ eqModIdealSet f g J) (hy : y ∈ eqModIdealSet f g J) : x + y ∈ eqModIdealSet f g J := by
  show f (x + y) - g (x + y) ∈ J
  rw [map_add, map_add]
  have hrw : f x + f y - (g x + g y) = (f x - g x) + (f y - g y) := by ring
  rw [hrw]
  exact J.add_mem hx hy

/- English proof (translation)
Use `show f (-x) - g (-x) ∈ J`. Rewrite using `[map_neg, map_neg]`. Establish `hrw : -f x - -g x = -(f x - g x)` using `by ring`. Rewrite using `[hrw]`. Conclude with `J.neg_mem hx`.
-/
private theorem neg_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) {x : B}
    (hx : x ∈ eqModIdealSet f g J) : -x ∈ eqModIdealSet f g J := by
  show f (-x) - g (-x) ∈ J
  rw [map_neg, map_neg]
  have hrw : -f x - -g x = -(f x - g x) := by ring
  rw [hrw]
  exact J.neg_mem hx

/- English proof (translation)
Use `show f (x * y) - g (x * y) ∈ J`. Rewrite using `[map_mul, map_mul]`. Establish `hrw : f x * f y - g x * g y = f x * (f y - g y) + (f x - g x) * g y` using `by ring`. Rewrite using `[hrw]`. Conclude with `J.add_mem (J.mul_mem_left _ hy) (J.mul_mem_right _ hx)`.
-/
private theorem mul_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) {x y : B}
    (hx : x ∈ eqModIdealSet f g J) (hy : y ∈ eqModIdealSet f g J) : x * y ∈ eqModIdealSet f g J := by
  show f (x * y) - g (x * y) ∈ J
  rw [map_mul, map_mul]
  have hrw : f x * f y - g x * g y = f x * (f y - g y) + (f x - g x) * g y := by ring
  rw [hrw]
  exact J.add_mem (J.mul_mem_left _ hy) (J.mul_mem_right _ hx)

def eqModIdealSubring (f g : B →+* A) (J : Ideal A) : Subring B where
  carrier := eqModIdealSet f g J
  one_mem' := one_mem_eqModIdealSet f g J
  zero_mem' := zero_mem_eqModIdealSet f g J
  add_mem' := add_mem_eqModIdealSet f g J
  neg_mem' := neg_mem_eqModIdealSet f g J
  mul_mem' := mul_mem_eqModIdealSet f g J

/- English proof (translation)
Establish `hsub : Subring.closure S ≤ eqModIdealSubring f g J` using `Subring.closure_le.mpr (fun x hx => hmem x hx)`. Rewrite `hsub` using `[hS]`. Conclude with `hsub (Subring.mem_top b)`.
-/
theorem sub_mem_ideal_of_subring_closure_eq_top (f g : B →+* A) (J : Ideal A) (S : Set B)
    (hS : Subring.closure S = ⊤) (hmem : ∀ b ∈ S, f b - g b ∈ J) (b : B) :
    f b - g b ∈ J := by
  have hsub : Subring.closure S ≤ eqModIdealSubring f g J :=
    Subring.closure_le.mpr (fun x hx => hmem x hx)
  rw [hS] at hsub
  exact hsub (Subring.mem_top b)

end

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eq_mul_pow_zero {M : Type u} [CommRing M] (x c : M) : x = x * c ^ 0 := by ring

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mul_add_mul_eq_add_mul {M : Type u} [CommRing M] (x y c : M) :
    x * c + y * c = (x + y) * c := by ring

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
private theorem self_sub_self_eq_zero {M : Type u} [CommRing M] (x : M) : x - x = 0 := by ring

/- English proof (translation)
Rewrite using `[Localization.mk_eq_mk_iff]`. Use `Localization.r_of_eq ?_` and prove the remaining obligations. Simplify using `[h]`.
-/
private theorem localization_mk_eq_mk_one_of_eq_mul {M : Type u} [CommMonoid M] {S : Submonoid M}
    (x y d : M) (hd : d ∈ S) (h : x = d * y) :
    Localization.mk x ⟨d, hd⟩ = Localization.mk y (1 : ↥S) := by
  rw [Localization.mk_eq_mk_iff]
  refine Localization.r_of_eq ?_
  simp [h]

section

variable {R : Type u} [CommRing R]

/- English proof (translation)
Rewrite using `[Blowup.chartRingHom_apply]`. Both sides reduce to the same expression.
-/
private theorem val_chartRingHom (I : Ideal R) (a : I) (t : R) :
    HomogeneousLocalization.val (Blowup.chartRingHom I a t)
      = Localization.mk (↑(Blowup.reesDegreeZeroEquiv I t) : ↥(reesAlgebra I))
          (1 : ↥(Submonoid.powers (Blowup.reesGenerator I a))) := by
  rw [Blowup.chartRingHom_apply]
  rfl

/- English proof (translation)
Take `⟨m, hm⟩` from `HomogeneousLocalization.den_mem z`. Establish `hden : HomogeneousLocalization.den z = Blowup.reesGenerator I a ^ m` using `hm.symm`. Establish `hdencoe : ((HomogeneousLocalization.den z : ↥(reesAlgebra I)) : Polynomial R) = Polynomial.monomial m ((a : R) ^ m)`. Rewrite using `[hden, SubmonoidClass.coe_pow, Blowup.reesGenerator_coe, Polynomial.monomial_pow, one_mul]`. Establish `hpow : (Blowup.chartRingHom I a) ((a : R) ^ m) = (Blowup.chartRingHom I a) (a : R) ^ m` using `map_pow (Blowup.chartRingHom I a) (a : R) m`.

Distinguish the cases in `hdeg : HomogeneousLocalization.deg z = m`. Establish `hnum : HomogeneousLocalization.num z ∈ Blowup.reesGrading I m`. Rewrite using `[← hdeg]`. Conclude with `HomogeneousLocalization.num_mem_deg z`. Take `⟨s, hs, hseq⟩` from `(Blowup.mem_reesGrading_iff_monomial I m (HomogeneousLocalization.num z)).mp hnum`.

Use `⟨m, s, hs, ?_⟩` and prove the remaining obligations. Establish `key : (HomogeneousLocalization.num z) * (↑(Blowup.reesDegreeZeroEquiv I ((a : R) ^ m)) : ↥(reesAlgebra I)) = (HomogeneousLocalization.den z) * (↑(Blowup.reesDegreeZeroEquiv I s) : ↥(reesAlgebra I))`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulMemClass.coe_mul, hseq, hdencoe, Blowup.reesDegreeZeroEquiv_coe_coe]`. Rewrite using `[mul_comm (Polynomial.monomial m s) (Polynomial.C ((a : R) ^ m)), Polynomial.C_mul_monomial, mul_comm (Polynomial.monomial m ((a : R) ^ m)) (Polynomial.C s), Polynomial.C_mul_monomial, mul_comm ((a : R) ^ m) s]`.

Rewrite using `[← hpow]`. Apply `HomogeneousLocalization.val_injective (Submonoid.powers (Blowup.reesGenerator I a))` to reduce the goal to its premises. Rewrite using `[HomogeneousLocalization.val_mul, val_chartRingHom, val_chartRingHom, HomogeneousLocalization.eq_num_div_den z, Localization.mk_mul, mul_one]`. Conclude with `localization_mk_eq_mk_one_of_eq_mul _ _ _ _ key`. Establish `hzero : (a : R) ^ m = 0`.

Establish `h1` using `(Blowup.mem_reesGrading_iff_coeff I (HomogeneousLocalization.deg z) (HomogeneousLocalization.den z)).mp (HomogeneousLocalization.den_mem_deg z) m (fun h => hdeg h.symm)`. Rewrite `h1` using `[hdencoe]`. Simplify using `using h1`. Use `⟨m, 0, Ideal.zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[← hpow, hzero, map_zero]`.

Conclude with `mul_zero z`.
-/
private theorem exists_pow_mul_eq (I : Ideal R) (a : I)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    ∃ (n : ℕ) (r : R), r ∈ I ^ n ∧
      z * Blowup.chartRingHom I a (a : R) ^ n = Blowup.chartRingHom I a r := by
  obtain ⟨m, hm⟩ := HomogeneousLocalization.den_mem z
  have hden : HomogeneousLocalization.den z = Blowup.reesGenerator I a ^ m := hm.symm
  have hdencoe : ((HomogeneousLocalization.den z : ↥(reesAlgebra I)) : Polynomial R)
      = Polynomial.monomial m ((a : R) ^ m) := by
    rw [hden, SubmonoidClass.coe_pow, Blowup.reesGenerator_coe, Polynomial.monomial_pow, one_mul]
  have hpow : (Blowup.chartRingHom I a) ((a : R) ^ m) = (Blowup.chartRingHom I a) (a : R) ^ m :=
    map_pow (Blowup.chartRingHom I a) (a : R) m
  by_cases hdeg : HomogeneousLocalization.deg z = m
  · have hnum : HomogeneousLocalization.num z ∈ Blowup.reesGrading I m := by
      rw [← hdeg]
      exact HomogeneousLocalization.num_mem_deg z
    obtain ⟨s, hs, hseq⟩ :=
      (Blowup.mem_reesGrading_iff_monomial I m (HomogeneousLocalization.num z)).mp hnum
    refine ⟨m, s, hs, ?_⟩
    have key : (HomogeneousLocalization.num z)
          * (↑(Blowup.reesDegreeZeroEquiv I ((a : R) ^ m)) : ↥(reesAlgebra I))
        = (HomogeneousLocalization.den z) * (↑(Blowup.reesDegreeZeroEquiv I s) : ↥(reesAlgebra I)) := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, hseq, hdencoe, Blowup.reesDegreeZeroEquiv_coe_coe]
      rw [mul_comm (Polynomial.monomial m s) (Polynomial.C ((a : R) ^ m)),
        Polynomial.C_mul_monomial,
        mul_comm (Polynomial.monomial m ((a : R) ^ m)) (Polynomial.C s),
        Polynomial.C_mul_monomial, mul_comm ((a : R) ^ m) s]
    rw [← hpow]
    apply HomogeneousLocalization.val_injective (Submonoid.powers (Blowup.reesGenerator I a))
    rw [HomogeneousLocalization.val_mul, val_chartRingHom, val_chartRingHom,
      HomogeneousLocalization.eq_num_div_den z, Localization.mk_mul, mul_one]
    exact localization_mk_eq_mk_one_of_eq_mul _ _ _ _ key
  · have hzero : (a : R) ^ m = 0 := by
      have h1 := (Blowup.mem_reesGrading_iff_coeff I (HomogeneousLocalization.deg z)
        (HomogeneousLocalization.den z)).mp (HomogeneousLocalization.den_mem_deg z) m
        (fun h => hdeg h.symm)
      rw [hdencoe] at h1
      simpa using h1
    refine ⟨m, 0, Ideal.zero_mem _, ?_⟩
    rw [← hpow, hzero, map_zero]
    exact mul_zero z

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `r _`. Use `⟨Blowup.chartRingHom I a r, Subring.subset_closure (Or.inl ⟨r, rfl⟩), ?_⟩` and prove the remaining obligations. Conclude with `eq_mul_pow_zero (M := HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) _ _`.

Consider the case `succ n ih`. Introduce `r hr`. Rewrite `hr` using `[pow_succ]`. Use `Submodule.mul_induction_on hr ?_ ?_` and prove the remaining obligations. Introduce `s hs b hb`.

Take `⟨w, hw, hweq⟩` from `ih s hs`. Establish `hbb : Blowup.chartRingHom I a b = Blowup.chartFraction I a ⟨b, hb⟩ * Blowup.chartRingHom I a (a : R)` using `Blowup.chartRingHom_coe_eq_chartFraction_mul I a ⟨b, hb⟩`. Use `⟨w * Blowup.chartFraction I a ⟨b, hb⟩, Subring.mul_mem _ hw (Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, rfl⟩)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hweq, hbb]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩`. Use `⟨wx + wy, Subring.add_mem _ hwx hwy, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hx, hy]`. Conclude with `mul_add_mul_eq_add_mul wx wy _`.
-/
private theorem exists_mem_closure_chartRingHom_eq_mul_pow (I : Ideal R) (a : I) (n : ℕ) :
    ∀ r ∈ I ^ n, ∃ w ∈ Subring.closure
        (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a)),
      Blowup.chartRingHom I a r = w * Blowup.chartRingHom I a (a : R) ^ n := by
  induction n with
  | zero =>
    intro r _
    refine ⟨Blowup.chartRingHom I a r, Subring.subset_closure (Or.inl ⟨r, rfl⟩), ?_⟩
    exact eq_mul_pow_zero (M := HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) _ _
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro s hs b hb
      obtain ⟨w, hw, hweq⟩ := ih s hs
      have hbb : Blowup.chartRingHom I a b
          = Blowup.chartFraction I a ⟨b, hb⟩ * Blowup.chartRingHom I a (a : R) :=
        Blowup.chartRingHom_coe_eq_chartFraction_mul I a ⟨b, hb⟩
      refine ⟨w * Blowup.chartFraction I a ⟨b, hb⟩,
        Subring.mul_mem _ hw (Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, rfl⟩)), ?_⟩
      rw [map_mul, hweq, hbb]
      ring
    · rintro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
      refine ⟨wx + wy, Subring.add_mem _ hwx hwy, ?_⟩
      rw [map_add, hx, hy]
      exact mul_add_mul_eq_add_mul wx wy _

/- English proof (translation)
Rewrite using `[Subring.eq_top_iff']`. Introduce `z`. Take `⟨n, r, hr, hz⟩` from `exists_pow_mul_eq I a z`. Take `⟨w, hw, hweq⟩` from `exists_mem_closure_chartRingHom_eq_mul_pow I a n r hr`. Establish `e1 : (z - w) * Blowup.chartRingHom I a (a : R) ^ n = z * Blowup.chartRingHom I a (a : R) ^ n - w * Blowup.chartRingHom I a (a : R) ^ n` using `sub_mul z w _`.

Establish `h0 : (z - w) * Blowup.chartRingHom I a (a : R) ^ n = 0`. Rewrite using `[e1, hz, ← hweq]`. Conclude with `self_sub_self_eq_zero (M := HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) _`. Establish `hnzd : Blowup.chartRingHom I a (a : R) ^ n ∈ nonZeroDivisors (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a))` using `pow_mem (Blowup.chartRingHom_mem_nonZeroDivisors I a) n`. Establish `hzw : z - w = 0` using `(mem_nonZeroDivisors_iff.mp hnzd).2 _ h0`.

Establish `hzeq : z = w` using `sub_eq_zero.mp hzw`. Rewrite using `[hzeq]`. Conclude with `hw`.
-/
theorem closure_chartRingHom_union_chartFraction_eq_top (I : Ideal R) (a : I) :
    Subring.closure
        (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a)) = ⊤ := by
  rw [Subring.eq_top_iff']
  intro z
  obtain ⟨n, r, hr, hz⟩ := exists_pow_mul_eq I a z
  obtain ⟨w, hw, hweq⟩ := exists_mem_closure_chartRingHom_eq_mul_pow I a n r hr
  have e1 : (z - w) * Blowup.chartRingHom I a (a : R) ^ n
      = z * Blowup.chartRingHom I a (a : R) ^ n - w * Blowup.chartRingHom I a (a : R) ^ n :=
    sub_mul z w _
  have h0 : (z - w) * Blowup.chartRingHom I a (a : R) ^ n = 0 := by
    rw [e1, hz, ← hweq]
    exact self_sub_self_eq_zero
      (M := HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) _
  have hnzd : Blowup.chartRingHom I a (a : R) ^ n
      ∈ nonZeroDivisors (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :=
    pow_mem (Blowup.chartRingHom_mem_nonZeroDivisors I a) n
  have hzw : z - w = 0 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  have hzeq : z = w := sub_eq_zero.mp hzw
  rw [hzeq]
  exact hw

/- English proof (translation)
Take `⟨c, hc, hcEq⟩` from `Ideal.mem_span_singleton_mul.mp (hcongr (a : R))`. Take `⟨d, hd, hdEq⟩` from `Ideal.mem_span_singleton_mul.mp (hcongr (b : R))`. Establish `hone : (1 : A) - u ∈ 𝔟`. Establish `h1 : σ (a : R) - σ' (a : R) = σ (a : R) * c` using `hcEq.symm`. Rewrite `h1` using `[hu]`.

Establish `h0 : ((1 : A) - u - c) * σ (a : R) = 0` using `by linear_combination h1`. Establish `h2` using `(mem_nonZeroDivisors_iff.mp hnzd).2 _ h0`. Establish `h3 : (1 : A) - u = c` using `by linear_combination h2`. Rewrite using `[h3]`. Conclude with `hc`.

Establish `hb1 : σ (b : R) = φ (Blowup.chartFraction I a b) * σ (a : R)`. Rewrite using `[← hφ (b : R), ← hφ (a : R), ← map_mul, Blowup.chartRingHom_coe_eq_chartFraction_mul I a b]`. Establish `hb2 : σ' (b : R) = φ' (Blowup.chartFraction I a b) * σ' (a : R)`. Rewrite using `[← hφ' (b : R), ← hφ' (a : R), ← map_mul, Blowup.chartRingHom_coe_eq_chartFraction_mul I a b]`. Establish `h2 : σ (b : R) - σ' (b : R) = σ (a : R) * d` using `hdEq.symm`.

Rewrite `h2` using `[hb1, hb2, hu]`. Establish `h0 : (φ (Blowup.chartFraction I a b) - u * φ' (Blowup.chartFraction I a b) - d) * σ (a : R) = 0`. Take the linear combination `h2`. Establish `h3` using `(mem_nonZeroDivisors_iff.mp hnzd).2 _ h0`. Establish `hfin : φ (Blowup.chartFraction I a b) - φ' (Blowup.chartFraction I a b) = d - (1 - u) * φ' (Blowup.chartFraction I a b)` using `by linear_combination h3`.

Rewrite using `[hfin]`. Conclude with `𝔟.sub_mem hd (𝔟.mul_mem_right _ hone)`.
-/
theorem chartFraction_sub_mem_of_congr {A : Type u} [CommRing A] (I : Ideal R) (a : I)
    (φ φ' : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a) →+* A)
    (σ σ' : R →+* A) (𝔟 : Ideal A)
    (hφ : ∀ r : R, φ (Blowup.chartRingHom I a r) = σ r)
    (hφ' : ∀ r : R, φ' (Blowup.chartRingHom I a r) = σ' r)
    (hcongr : ∀ r : R, σ r - σ' r ∈ Ideal.span {σ (a : R)} * 𝔟)
    (hnzd : σ (a : R) ∈ nonZeroDivisors A)
    (u : A) (hu : σ' (a : R) = u * σ (a : R)) (b : I) :
    φ (Blowup.chartFraction I a b) - φ' (Blowup.chartFraction I a b) ∈ 𝔟 := by
  obtain ⟨c, hc, hcEq⟩ := Ideal.mem_span_singleton_mul.mp (hcongr (a : R))
  obtain ⟨d, hd, hdEq⟩ := Ideal.mem_span_singleton_mul.mp (hcongr (b : R))
  have hone : (1 : A) - u ∈ 𝔟 := by
    have h1 : σ (a : R) - σ' (a : R) = σ (a : R) * c := hcEq.symm
    rw [hu] at h1
    have h0 : ((1 : A) - u - c) * σ (a : R) = 0 := by linear_combination h1
    have h2 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
    have h3 : (1 : A) - u = c := by linear_combination h2
    rw [h3]
    exact hc
  have hb1 : σ (b : R) = φ (Blowup.chartFraction I a b) * σ (a : R) := by
    rw [← hφ (b : R), ← hφ (a : R), ← map_mul, Blowup.chartRingHom_coe_eq_chartFraction_mul I a b]
  have hb2 : σ' (b : R) = φ' (Blowup.chartFraction I a b) * σ' (a : R) := by
    rw [← hφ' (b : R), ← hφ' (a : R), ← map_mul, Blowup.chartRingHom_coe_eq_chartFraction_mul I a b]
  have h2 : σ (b : R) - σ' (b : R) = σ (a : R) * d := hdEq.symm
  rw [hb1, hb2, hu] at h2
  have h0 : (φ (Blowup.chartFraction I a b) - u * φ' (Blowup.chartFraction I a b) - d) * σ (a : R) = 0 := by
    linear_combination h2
  have h3 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  have hfin : φ (Blowup.chartFraction I a b) - φ' (Blowup.chartFraction I a b)
      = d - (1 - u) * φ' (Blowup.chartFraction I a b) := by linear_combination h3
  rw [hfin]
  exact 𝔟.sub_mem hd (𝔟.mul_mem_right _ hone)

end

section

variable {R : Type u} [CommRing R]

/- English proof (translation)
Rewrite using `[Blowup.sectionsRingHom_apply, Blowup.sectionsRingHom_apply]`. Use `conv_rhs => rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]`.
-/
private theorem sectionsRingHom_comp {A : Type u} [CommRing A] {Z W : Scheme.{u}} (p : Z ⟶ W)
    (ρ : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) (V' : Z.Opens)
    (hle : V' ≤ (Opens.map p.base).obj V) (r : A) :
    Blowup.sectionsRingHom (p ≫ ρ) V' r
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE p V V' hle)) (Blowup.sectionsRingHom ρ V r) := by
  rw [Blowup.sectionsRingHom_apply, Blowup.sectionsRingHom_apply]
  conv_rhs => rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/- English proof (translation)
Rewrite `hx` using `[Scheme.IdealSheafData.subschemeι_app 𝔞 V, CommRingCat.comp_apply]`. Establish `h2` using `congrArg (CommRingCat.Hom.hom (𝔞.subschemeObjIso V).hom) hx`. Rewrite `h2` using `[← CommRingCat.comp_apply, Iso.inv_hom_id]`. Simplify `h2` using `[Ideal.Quotient.eq_zero_iff_mem]`.
-/
private theorem mem_ideal_of_app_subschemeι_eq_zero {W : Scheme.{u}} (𝔞 : W.IdealSheafData) (V : W.affineOpens)
    (x : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hx : (CommRingCat.Hom.hom (Scheme.Hom.app 𝔞.subschemeι (V : W.Opens))) x = 0) :
    x ∈ 𝔞.ideal V := by
  rw [Scheme.IdealSheafData.subschemeι_app 𝔞 V, CommRingCat.comp_apply] at hx
  have h2 := congrArg (CommRingCat.Hom.hom (𝔞.subschemeObjIso V).hom) hx
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id] at h2
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h2

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.subschemeι_app 𝔞 V, CommRingCat.comp_apply]`. Simplify using `[Ideal.Quotient.eq_zero_iff_mem.mpr hx]`.
-/
private theorem app_subschemeι_eq_zero_of_mem_ideal {W : Scheme.{u}} (𝔞 : W.IdealSheafData)
    (V : W.affineOpens) {x : ↥(W.presheaf.obj (Opposite.op (V : W.Opens)))}
    (hx : x ∈ 𝔞.ideal V) :
    (CommRingCat.Hom.hom (Scheme.Hom.app 𝔞.subschemeι (V : W.Opens))) x = 0 := by
  rw [Scheme.IdealSheafData.subschemeι_app 𝔞 V, CommRingCat.comp_apply]
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]

/- English proof (translation)
The claim follows from `Scheme.Hom.appLE_eq_app (f := f)`.
-/
private theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : (⊤ : X.Opens) ≤ (Opens.map f.base).obj ⊤) :
    Scheme.Hom.appLE f ⊤ ⊤ e = Scheme.Hom.appTop f :=
  Scheme.Hom.appLE_eq_app (f := f)

/- English proof (translation)
Substitute `hfg` using the available equality. Both sides reduce to the same expression.
-/
private theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ (Opens.map f.base).obj U)
    (e' : V ≤ (Opens.map g.base).obj U) :
    Scheme.Hom.appLE f U V e = Scheme.Hom.appLE g U V e' := by
  subst hfg
  rfl

/- English proof (translation)
Apply `mem_ideal_of_app_subschemeι_eq_zero` to reduce the goal to its premises. Establish `h1 : Blowup.sectionsRingHom (𝔞.subschemeι ≫ ρ) ((Opens.map 𝔞.subschemeι.base).obj (V : W.Opens)) r = Blowup.sectionsRingHom (𝔞.subschemeι ≫ ρ') ((Opens.map 𝔞.subschemeι.base).obj (V : W.Opens)) r`. Rewrite using `[hagree]`. Rewrite `h1` using `[sectionsRingHom_comp 𝔞.subschemeι ρ (V : W.Opens) _ le_rfl r, sectionsRingHom_comp 𝔞.subschemeι ρ' (V : W.Opens) _ le_rfl r]`. Rewrite using `[Scheme.Hom.app_eq_appLE, map_sub, h1]`.

Conclude with `sub_self _`.
-/
theorem sectionsRingHom_sub_mem_ideal {A : Type u} [CommRing A] {W : Scheme.{u}}
    (ρ ρ' : W ⟶ Spec (CommRingCat.of A)) (𝔞 : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (V : W.affineOpens) (r : A) :
    Blowup.sectionsRingHom ρ (V : W.Opens) r - Blowup.sectionsRingHom ρ' (V : W.Opens) r ∈ 𝔞.ideal V := by
  apply mem_ideal_of_app_subschemeι_eq_zero
  have h1 : Blowup.sectionsRingHom (𝔞.subschemeι ≫ ρ)
        ((Opens.map 𝔞.subschemeι.base).obj (V : W.Opens)) r
      = Blowup.sectionsRingHom (𝔞.subschemeι ≫ ρ')
        ((Opens.map 𝔞.subschemeι.base).obj (V : W.Opens)) r := by
    rw [hagree]
  rw [sectionsRingHom_comp 𝔞.subschemeι ρ (V : W.Opens) _ le_rfl r,
    sectionsRingHom_comp 𝔞.subschemeι ρ' (V : W.Opens) _ le_rfl r] at h1
  rw [Scheme.Hom.app_eq_appLE, map_sub, h1]
  exact sub_self _

/- English proof (translation)
Establish `hchartle : (⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).Opens) ≤ (Opens.map (Blowup.affineBlowupChart I a).base).obj ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤)` using `fun x _ => ⟨x, trivial, rfl⟩`. Establish `hsec : (CommRingCat.Hom.hom (Scheme.Hom.appLE (Blowup.affineBlowupChart I a) ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle)) ((CommRingCat.Hom.hom (Blowup.chartSectionsIso I a).hom) z) = (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Homogene …`. Rewrite using `[Blowup.chartSectionsIso_hom_apply, ← CommRingCat.comp_apply, show Scheme.Hom.appLE (Blowup.affineBlowupChart I a) ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle = (Scheme.Hom.appIso (Blowup.affineBlowupChart I a) ⊤).hom from (Scheme.Hom.appIso_hom' ( …`. Establish `hlift` using `IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) (p ≫ k) hrange`. Establish `etop : (⊤ : T.Opens) ≤ (Opens.map (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) (p ≫ k) hrange).base).obj ⊤`.

Simplify using the standard rewrite rules. Establish `hmain : Scheme.Hom.appLE (Blowup.affineBlowupChart I a) ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle ≫ Scheme.Hom.appLE (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) (p ≫ k) hrange) ⊤ ⊤ etop = Scheme.Hom.appLE k ((Scheme.Hom.opensFunctor (Blo …`. Rewrite using `[Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]`. Conclude with `appLE_congr_hom hlift _ _ _ _`. Rewrite `hmain` using `[appLE_top_top _ etop]`.

Establish `happ` using `congrArg (fun m : _ ⟶ _ => (CommRingCat.Hom.hom m) ((CommRingCat.Hom.hom (Blowup.chartSectionsIso I a).hom) z)) hmain`. Simplify using `only [CommRingCat.comp_apply] at happ`. Rewrite `happ` using `[hsec, ← Blowup.chartSectionsRingHom_apply]`. Conclude with `happ`.
-/
private theorem appTop_lift_affineBlowupChart_apply (I : Ideal R) {W : Scheme.{u}} (k : W ⟶ Blowup.affineBlowup I) (a : I)
    {T : Scheme.{u}} (p : T ⟶ W) (V : W.Opens)
    (hk : V ≤ (Opens.map k.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hψ : (⊤ : T.Opens) ≤ (Opens.map p.base).obj V)
    (hrange : Set.range ⇑(p ≫ k).base ⊆ Set.range ⇑(Blowup.affineBlowupChart I a).base)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    (CommRingCat.Hom.hom (Scheme.Hom.appTop
        (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) (p ≫ k) hrange)))
      ((CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv) z)
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE p V ⊤ hψ))
          (Blowup.chartSectionsRingHom I k a V hk z) := by
  have hchartle : (⊤ : (Spec (CommRingCat.of
        (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).Opens)
      ≤ (Opens.map (Blowup.affineBlowupChart I a).base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) :=
    fun x _ => ⟨x, trivial, rfl⟩
  have hsec : (CommRingCat.Hom.hom (Scheme.Hom.appLE (Blowup.affineBlowupChart I a)
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle))
        ((CommRingCat.Hom.hom (Blowup.chartSectionsIso I a).hom) z)
      = (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv) z := by
    rw [Blowup.chartSectionsIso_hom_apply, ← CommRingCat.comp_apply,
      show Scheme.Hom.appLE (Blowup.affineBlowupChart I a)
          ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle
        = (Scheme.Hom.appIso (Blowup.affineBlowupChart I a) ⊤).hom from
          (Scheme.Hom.appIso_hom' (Blowup.affineBlowupChart I a) ⊤).symm,
      Iso.inv_hom_id, CommRingCat.id_apply]
  have hlift := IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) (p ≫ k) hrange
  have etop : (⊤ : T.Opens)
      ≤ (Opens.map (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) (p ≫ k) hrange).base).obj ⊤ := by
    simp
  have hmain : Scheme.Hom.appLE (Blowup.affineBlowupChart I a)
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ⊤ hchartle
        ≫ Scheme.Hom.appLE (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) (p ≫ k) hrange) ⊤ ⊤ etop
      = Scheme.Hom.appLE k ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) V hk
        ≫ Scheme.Hom.appLE p V ⊤ hψ := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom hlift _ _ _ _
  rw [appLE_top_top _ etop] at hmain
  have happ := congrArg (fun m : _ ⟶ _ =>
      (CommRingCat.Hom.hom m) ((CommRingCat.Hom.hom (Blowup.chartSectionsIso I a).hom) z)) hmain
  simp only [CommRingCat.comp_apply] at happ
  rw [hsec, ← Blowup.chartSectionsRingHom_apply] at happ
  exact happ

/- English proof (translation)
Rewrite using `[← Category.assoc, ← Category.assoc]`. Establish `hψ : (⊤ : (Scheme.Opens.toScheme ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).Opens) ≤ (Opens.map (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι).base).obj (V : W.Opens)`. Introduce `x _`. Simplify using the standard rewrite rules. Establish `hι : (⊤ : (Scheme.Opens.toScheme ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).Opens) ≤ (Opens.map (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).base).obj ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))`.

Introduce `x _`. Simplify using the standard rewrite rules. Establish `hrange : ∀ (k : W ⟶ Blowup.affineBlowup I), (V : W.Opens) ≤ (Opens.map k.base).obj ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) → Set.range ⇑((Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι) ≫ k).base ⊆ Set.range ⇑(Blowup.affin …`. Introduce `k hk`. Introduce and unpack `y ⟨x, rfl⟩`.

Establish `h3 : k.base (𝔟.subschemeι.base x.1) ∈ Scheme.Hom.opensRange (Blowup.affineBlowupChart I a)`. Rewrite using `[← Scheme.Hom.image_top_eq_opensRange]`. Conclude with `hk x.2`. Take `⟨q, hq⟩` from `h3`. Conclude with `⟨q, hq⟩`.

Establish `hkill : ∀ x ∈ 𝔟.ideal V, (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι) (V : W.Opens) ⊤ hψ)) x = 0`. Introduce `x hx`. Establish `hcomp : Scheme.Hom.appLE 𝔟.subschemeι (V : W.Opens) ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) le_rfl ≫ Scheme.Hom.appLE (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))) ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ⊤ hι = Scheme.Hom.appLE (Scheme.Ope …`. Rewrite using `[Scheme.Hom.appLE_comp_appLE]`. Establish `h2` using `congrArg (fun m : _ ⟶ _ => (CommRingCat.Hom.hom m) x) hcomp`.

Simplify using `only [CommRingCat.comp_apply] at h2`. Rewrite `h2` using `[Scheme.Hom.appLE_eq_app, app_subschemeι_eq_zero_of_mem_ideal 𝔟 V hx, map_zero]`. Conclude with `h2.symm`. Establish `happ : Scheme.Hom.appTop (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV)) = Scheme.Hom.appTop (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV'))`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `y`. Establish `hy : (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv) ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a …`. Rewrite using `[← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]`. Take `⟨z, rfl⟩ : ∃ z, (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv) z = y` from `⟨_, hy⟩`.

Rewrite using `[appTop_lift_affineBlowupChart_apply I h a (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι) (V : W.Opens) hV hψ (hrange h hV) z, appTop_lift_affineBlowupChart_apply I h' a (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subsc …`. Establish `hz` using `hkill _ (hcongr z)`. Rewrite `hz` using `[map_sub]`. Conclude with `sub_eq_zero.mp hz`. Establish `hfin : IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV) = IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV')`.

Establish `hcomp : IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV) ≫ (Spec (CommRingCat.of (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).toSpecΓ = IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV') ≫ (Spec (CommRing …`. Rewrite using `[Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, happ]`. Conclude with `(cancel_mono _).mp hcomp`. Rewrite using `[← IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) _ (hrange h hV), ← IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) _ (hrange h' hV'), hfin]`.
-/
theorem comp_eq_of_chartSectionsRingHom_sub_mem (I : Ideal R) {W : Scheme.{u}}
    (h h' : W ⟶ Blowup.affineBlowup I) (a : I) (𝔟 : W.IdealSheafData) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hV' : (V : W.Opens) ≤ (Opens.map h'.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hcongr : ∀ z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a),
      Blowup.chartSectionsRingHom I h a (V : W.Opens) hV z - Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV' z
        ∈ 𝔟.ideal V) :
    Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι ≫ h
      = Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι ≫ h' := by
  rw [← Category.assoc, ← Category.assoc]
  have hψ : (⊤ : (Scheme.Opens.toScheme
        ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).Opens)
      ≤ (Opens.map (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))
            ≫ 𝔟.subschemeι).base).obj (V : W.Opens) := by
    intro x _
    simp
  have hι : (⊤ : (Scheme.Opens.toScheme
        ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).Opens)
      ≤ (Opens.map (Scheme.Opens.ι
          ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))).base).obj
        ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) := by
    intro x _
    simp
  have hrange : ∀ (k : W ⟶ Blowup.affineBlowup I),
      (V : W.Opens) ≤ (Opens.map k.base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) →
      Set.range ⇑((Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))
          ≫ 𝔟.subschemeι) ≫ k).base ⊆ Set.range ⇑(Blowup.affineBlowupChart I a).base := by
    intro k hk
    rintro y ⟨x, rfl⟩
    have h3 : k.base (𝔟.subschemeι.base x.1)
        ∈ Scheme.Hom.opensRange (Blowup.affineBlowupChart I a) := by
      rw [← Scheme.Hom.image_top_eq_opensRange]
      exact hk x.2
    obtain ⟨q, hq⟩ := h3
    exact ⟨q, hq⟩
  have hkill : ∀ x ∈ 𝔟.ideal V,
      (CommRingCat.Hom.hom (Scheme.Hom.appLE
        (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι)
        (V : W.Opens) ⊤ hψ)) x = 0 := by
    intro x hx
    have hcomp : Scheme.Hom.appLE 𝔟.subschemeι (V : W.Opens)
          ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) le_rfl
        ≫ Scheme.Hom.appLE (Scheme.Opens.ι
            ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)))
            ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ⊤ hι
        = Scheme.Hom.appLE (Scheme.Opens.ι
            ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι)
            (V : W.Opens) ⊤ hψ := by
      rw [Scheme.Hom.appLE_comp_appLE]
    have h2 := congrArg (fun m : _ ⟶ _ => (CommRingCat.Hom.hom m) x) hcomp
    simp only [CommRingCat.comp_apply] at h2
    rw [Scheme.Hom.appLE_eq_app, app_subschemeι_eq_zero_of_mem_ideal 𝔟 V hx, map_zero] at h2
    exact h2.symm
  have happ : Scheme.Hom.appTop (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV))
      = Scheme.Hom.appTop (IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV')) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro y
    have hy : (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv)
        ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).hom) y) = y := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    obtain ⟨z, rfl⟩ : ∃ z, (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
        (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).inv) z = y :=
      ⟨_, hy⟩
    rw [appTop_lift_affineBlowupChart_apply I h a (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))
        ≫ 𝔟.subschemeι) (V : W.Opens) hV hψ (hrange h hV) z,
      appTop_lift_affineBlowupChart_apply I h' a (Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens))
        ≫ 𝔟.subschemeι) (V : W.Opens) hV' hψ (hrange h' hV') z]
    have hz := hkill _ (hcongr z)
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  have hfin : IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV)
      = IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV') := by
    have hcomp : IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h hV)
          ≫ (Spec (CommRingCat.of
              (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).toSpecΓ
        = IsOpenImmersion.lift (Blowup.affineBlowupChart I a) _ (hrange h' hV')
          ≫ (Spec (CommRingCat.of
              (HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)))).toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, happ]
    exact (cancel_mono _).mp hcomp
  rw [← IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) _ (hrange h hV),
    ← IsOpenImmersion.lift_fac (Blowup.affineBlowupChart I a) _ (hrange h' hV'), hfin]

/- English proof (translation)
Establish `h1` using `sectionsRingHom_sub_mem_ideal ρ ρ' 𝔞 hagree V r`. Rewrite `h1` using `[← hfac]`. Rewrite using `[← hspan]`. Conclude with `h1`.
-/
private theorem sectionsRingHom_sub_mem_span_mul_of_agree (I : Ideal R) {W : Scheme.{u}}
    (ρ ρ' : W ⟶ Spec (CommRingCat.of R)) (𝔞 𝔟₁ : W.IdealSheafData) (V : W.affineOpens)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (hfac : (Blowup.specIdealSheaf I).comap ρ * 𝔟₁ = 𝔞)
    (s : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hspan : ((Blowup.specIdealSheaf I).comap ρ).ideal V = Ideal.span {s})
    (r : R) :
    Blowup.sectionsRingHom ρ (V : W.Opens) r - Blowup.sectionsRingHom ρ' (V : W.Opens) r
      ∈ Ideal.span {s} * 𝔟₁.ideal V := by
  have h1 := sectionsRingHom_sub_mem_ideal ρ ρ' 𝔞 hagree V r
  rw [← hfac] at h1
  rw [← hspan]
  exact h1

/- English proof (translation)
Use `sub_mem_ideal_of_subring_closure_eq_top (Blowup.chartSectionsRingHom I h a (V : W.Opens) hV) (Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV') (𝔟₁.ideal V) (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a)) (closure_chartRingHom_union_chartFraction …` and prove the remaining obligations. Introduce and unpack `b (⟨r, rfl⟩ | ⟨b0, rfl⟩)`. Rewrite using `[Blowup.chartSectionsRingHom_chartRingHom, Blowup.chartSectionsRingHom_chartRingHom]`. Conclude with `(Ideal.mem_inf.mp (Ideal.mul_le_inf (hcongr r))).2`. Conclude with `chartFraction_sub_mem_of_congr I a (Blowup.chartSectionsRingHom I h a (V : W.Opens) hV) (Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV') (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens)) (Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V …`.
-/
private theorem chartSectionsRingHom_sub_mem (I : Ideal R) {W : Scheme.{u}}
    (h h' : W ⟶ Blowup.affineBlowup I) (𝔟₁ : W.IdealSheafData) (a : I) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hV' : (V : W.Opens) ≤ (Opens.map h'.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hnzd : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (u : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hu : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      = u * Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R))
    (hcongr : ∀ r : R, Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) r
        - Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) r
      ∈ Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)}
          * 𝔟₁.ideal V)
    (z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a)) :
    Blowup.chartSectionsRingHom I h a (V : W.Opens) hV z - Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV' z
      ∈ 𝔟₁.ideal V := by
  refine sub_mem_ideal_of_subring_closure_eq_top (Blowup.chartSectionsRingHom I h a (V : W.Opens) hV)
    (Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV') (𝔟₁.ideal V)
    (Set.range ⇑(Blowup.chartRingHom I a) ∪ Set.range (Blowup.chartFraction I a))
    (closure_chartRingHom_union_chartFraction_eq_top I a) ?_ z
  rintro b (⟨r, rfl⟩ | ⟨b0, rfl⟩)
  · rw [Blowup.chartSectionsRingHom_chartRingHom, Blowup.chartSectionsRingHom_chartRingHom]
    exact (Ideal.mem_inf.mp (Ideal.mul_le_inf (hcongr r))).2
  · exact chartFraction_sub_mem_of_congr I a (Blowup.chartSectionsRingHom I h a (V : W.Opens) hV)
      (Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV')
      (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens))
      (Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens)) (𝔟₁.ideal V)
      (Blowup.chartSectionsRingHom_chartRingHom I h a (V : W.Opens) hV)
      (Blowup.chartSectionsRingHom_chartRingHom I h' a (V : W.Opens) hV')
      hcongr hnzd u hu b0

/- English proof (translation)
Establish `hmem : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R) ∈ Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)}`. Rewrite using `[← hspan, hpull, Blowup.comap_specIdealSheaf_ideal_eq_span I h' a V hV']`. Conclude with `Ideal.mem_span_singleton_self _`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.mp hmem`. Use `comp_eq_of_chartSectionsRingHom_sub_mem I h h' a 𝔟₁ V hV hV' (fun z => ?_)` and prove the remaining obligations.

Use `chartSectionsRingHom_sub_mem I h h' 𝔟₁ a V hV hV' hnzd u hu.symm (fun r => ?_) z` and prove the remaining obligations. Conclude with `sectionsRingHom_sub_mem_span_mul_of_agree I (h ≫ Blowup.AffineBlowup.toSpec I) (h' ≫ Blowup.AffineBlowup.toSpec I) 𝔞 𝔟₁ V hagree hfac (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)) hspan r`.
-/
theorem comp_eq_on_chart_of_mul_eq_of_agree (I : Ideal R) {W : Scheme.{u}}
    (h h' : W ⟶ Blowup.affineBlowup I) (𝔞 𝔟₁ : W.IdealSheafData) (a : I) (V : W.affineOpens)
    (hagree : 𝔞.subschemeι ≫ (h ≫ Blowup.AffineBlowup.toSpec I)
      = 𝔞.subschemeι ≫ (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hpull : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)
      = (Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hfac : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁ = 𝔞)
    (hV : (V : W.Opens) ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hV' : (V : W.Opens) ≤ (Opens.map h'.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hnzd : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hspan : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V
      = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)}) :
    Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟₁.subschemeι ≫ h
      = Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟₁.subschemeι ≫ h' := by
  have hmem : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      ∈ Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)} := by
    rw [← hspan, hpull, Blowup.comap_specIdealSheaf_ideal_eq_span I h' a V hV']
    exact Ideal.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
  refine comp_eq_of_chartSectionsRingHom_sub_mem I h h' a 𝔟₁ V hV hV' (fun z => ?_)
  refine chartSectionsRingHom_sub_mem I h h' 𝔟₁ a V hV hV' hnzd u hu.symm (fun r => ?_) z
  exact sectionsRingHom_sub_mem_span_mul_of_agree I (h ≫ Blowup.AffineBlowup.toSpec I) (h' ≫ Blowup.AffineBlowup.toSpec I) 𝔞 𝔟₁ V
    hagree hfac (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)) hspan r

/- English proof (translation)
Take `⟨a, V, hwV, hVchart, hnzdV⟩` from `Blowup.exists_chart_affineOpen_mem_nonZeroDivisors I h hcart w`. Establish `hspanV : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)}` using `Blowup.comap_specIdealSheaf_ideal_eq_span I h a V hVchart`. Establish `hsub` using `sectionsRingHom_sub_mem_ideal (h ≫ Blowup.AffineBlowup.toSpec I) (h' ≫ Blowup.AffineBlowup.toSpec I) 𝔞 hagree V (a : R)`. Establish `hmul : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁).ideal V = ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V * 𝔟₁.ideal V` using `rfl`. Rewrite `hsub` using `[← hfac, hmul, hspanV]`.

Take `⟨c, hc, hceq⟩` from `Ideal.mem_span_singleton_mul.mp hsub`. Use `set f : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))) := 1 - c with hfdef`. Establish `hf'' : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R) = Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R) * f`. Rewrite using `[hfdef]`. Take the linear combination `hceq`.

Establish `hle : W.basicOpen f ≤ (V : W.Opens)` using `W.basicOpen_le f`. Establish `haff : IsAffineOpen (W.basicOpen f)` using `V.2.basicOpen f`. Establish `hlechart : W.basicOpen f ≤ (Opens.map h.base).obj ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤)` using `le_trans hle hVchart`. Establish `hsp : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal ⟨W.basicOpen f, haff⟩ = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)}` using `Blowup.comap_specIdealSheaf_ideal_eq_span I h a ⟨W.basicOpen f, haff⟩ hlechart`. Establish `hresσ : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R) = (CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op)) (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R))` using `Blowup.sectionsRingHom_restrict (h ≫ Blowup.AffineBlowup.toSpec I) hle (a : R)`.

Establish `hresσ' : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R) = (CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op)) (Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R))` using `Blowup.sectionsRingHom_restrict (h' ≫ Blowup.AffineBlowup.toSpec I) hle (a : R)`. Establish `hloc : IsLocalization.Away f ↥(W.presheaf.obj (Opposite.op (W.basicOpen f)))` using `V.2.isLocalization_basicOpen f`. Establish `hunit : IsUnit ((CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op)) f)` using `IsLocalization.map_units (S := ↥(W.presheaf.obj (Opposite.op (W.basicOpen f)))) (M := Submonoid.powers f) ⟨f, Submonoid.mem_powers f⟩`. Establish `hnzdres : algebraMap ↥(W.presheaf.obj (Opposite.op (V : W.Opens))) ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))) (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)) ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (W.basicOpen f)))`. Establish `hcomap` using `IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers f) (S := ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))))`.

Conclude with `hcomap hnzdV`. Establish `hnzdfinal : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R) ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (W.basicOpen f)))`. Rewrite using `[hresσ]`. Conclude with `hnzdres`. Establish `hcart' : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I))`.

Rewrite using `[← hpull]`. Conclude with `hcart`. Establish `hspanbo' : ((Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I)).ideal ⟨W.basicOpen f, haff⟩ = Ideal.span {Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)}`. Rewrite using `[← hpull, hsp, hresσ, hresσ', hf'', map_mul]`. Conclude with `(Ideal.span_singleton_mul_right_unit hunit _).symm`.

Establish `hpre : (Opens.map 𝔟₁.subschemeι.base).obj (W.basicOpen f) = (Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens)`. Rewrite using `[Scheme.preimage_basicOpen]`. Establish `happ : (CategoryTheory.ConcreteCategory.hom (Scheme.Hom.app 𝔟₁.subschemeι (V : W.Opens))) f = 1` using `by show (CommRingCat.Hom.hom (Scheme.Hom.app 𝔟₁.subschemeι (V : W.Opens))) f = 1`. Rewrite using `[hfdef, map_sub, map_one, app_subschemeι_eq_zero_of_mem_ideal 𝔟₁ V hc, sub_zero]`. Rewrite using `[happ, Scheme.basicOpen_one]`.

Use `⟨a, V, ⟨W.basicOpen f, haff⟩, hwV, hpre, hlechart, ?_, hnzdfinal, hsp⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hmemrange` using `Blowup.mem_opensRange_affineBlowupChart_of_ideal_eq_span I h' hcart' x a ⟨⟨W.basicOpen f, haff⟩, hx, hspanbo'⟩`. Rewrite `hmemrange` using `[← Scheme.Hom.image_top_eq_opensRange]`. Conclude with `hmemrange`.
-/
theorem exists_common_chart_affineOpen (I : Ideal R) {W : Scheme.{u}}
    (h h' : W ⟶ Blowup.affineBlowup I) (𝔞 𝔟₁ : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ (h ≫ Blowup.AffineBlowup.toSpec I)
      = 𝔞.subschemeι ≫ (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hpull : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)
      = (Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)))
    (hfac : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁ = 𝔞)
    (w : ↥W) :
    ∃ (a : I) (V V' : W.affineOpens),
      w ∈ (V : W.Opens) ∧
      (Opens.map 𝔟₁.subschemeι.base).obj (V' : W.Opens)
        = (Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens) ∧
      (V' : W.Opens) ≤ (Opens.map h.base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ∧
      (V' : W.Opens) ≤ (Opens.map h'.base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ∧
      Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V' : W.Opens) (a : R)
        ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V' : W.Opens))) ∧
      ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V'
        = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V' : W.Opens) (a : R)} := by
  obtain ⟨a, V, hwV, hVchart, hnzdV⟩ := Blowup.exists_chart_affineOpen_mem_nonZeroDivisors I h hcart w
  have hspanV : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V
      = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)} :=
    Blowup.comap_specIdealSheaf_ideal_eq_span I h a V hVchart
  have hsub := sectionsRingHom_sub_mem_ideal (h ≫ Blowup.AffineBlowup.toSpec I)
    (h' ≫ Blowup.AffineBlowup.toSpec I) 𝔞 hagree V (a : R)
  have hmul : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁).ideal V
      = ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V * 𝔟₁.ideal V := rfl
  rw [← hfac, hmul, hspanV] at hsub
  obtain ⟨c, hc, hceq⟩ := Ideal.mem_span_singleton_mul.mp hsub
  set f : ↥(W.presheaf.obj (Opposite.op (V : W.Opens))) := 1 - c with hfdef
  have hf'' : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      = Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R) * f := by
    rw [hfdef]
    linear_combination hceq
  have hle : W.basicOpen f ≤ (V : W.Opens) := W.basicOpen_le f
  have haff : IsAffineOpen (W.basicOpen f) := V.2.basicOpen f
  have hlechart : W.basicOpen f ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) := le_trans hle hVchart
  have hsp : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen f, haff⟩
      = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)} :=
    Blowup.comap_specIdealSheaf_ideal_eq_span I h a ⟨W.basicOpen f, haff⟩ hlechart
  have hresσ : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)
      = (CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op))
          (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)) :=
    Blowup.sectionsRingHom_restrict (h ≫ Blowup.AffineBlowup.toSpec I) hle (a : R)
  have hresσ' : Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)
      = (CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op))
          (Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)) :=
    Blowup.sectionsRingHom_restrict (h' ≫ Blowup.AffineBlowup.toSpec I) hle (a : R)
  have hloc : IsLocalization.Away f ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))) :=
    V.2.isLocalization_basicOpen f
  have hunit : IsUnit ((CommRingCat.Hom.hom (W.presheaf.map (homOfLE hle).op)) f) :=
    IsLocalization.map_units
      (S := ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))))
      (M := Submonoid.powers f) ⟨f, Submonoid.mem_powers f⟩
  have hnzdres : algebraMap ↥(W.presheaf.obj (Opposite.op (V : W.Opens)))
        ↥(W.presheaf.obj (Opposite.op (W.basicOpen f)))
        (Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R))
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))) := by
    have hcomap := IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers f)
      (S := ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))))
    exact hcomap hnzdV
  have hnzdfinal : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (W.basicOpen f))) := by
    rw [hresσ]
    exact hnzdres
  have hcart' : Blowup.IsLocallyGeneratedByNonZeroDivisor
      ((Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I)) := by
    rw [← hpull]
    exact hcart
  have hspanbo' : ((Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen f, haff⟩
      = Ideal.span {Blowup.sectionsRingHom (h' ≫ Blowup.AffineBlowup.toSpec I) (W.basicOpen f) (a : R)} := by
    rw [← hpull, hsp, hresσ, hresσ', hf'', map_mul]
    exact (Ideal.span_singleton_mul_right_unit hunit _).symm
  have hpre : (Opens.map 𝔟₁.subschemeι.base).obj (W.basicOpen f)
      = (Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens) := by
    rw [Scheme.preimage_basicOpen]
    have happ : (CategoryTheory.ConcreteCategory.hom
        (Scheme.Hom.app 𝔟₁.subschemeι (V : W.Opens))) f = 1 := by
      show (CommRingCat.Hom.hom (Scheme.Hom.app 𝔟₁.subschemeι (V : W.Opens))) f = 1
      rw [hfdef, map_sub, map_one, app_subschemeι_eq_zero_of_mem_ideal 𝔟₁ V hc, sub_zero]
    rw [happ, Scheme.basicOpen_one]
  refine ⟨a, V, ⟨W.basicOpen f, haff⟩, hwV, hpre, hlechart, ?_, hnzdfinal, hsp⟩
  intro x hx
  have hmemrange := Blowup.mem_opensRange_affineBlowupChart_of_ideal_eq_span I h' hcart' x a
    ⟨⟨W.basicOpen f, haff⟩, hx, hspanbo'⟩
  rw [← Scheme.Hom.image_top_eq_opensRange] at hmemrange
  exact hmemrange

/- English proof (translation)
Substitute `hh` using the available equality. Substitute `hh'` using the available equality. Use `choose a V V' hw hpre hVh hVh' hn hs using exists_common_chart_affineOpen I h h' 𝔞 𝔟₁ hagree hpull hcart hfac`. Establish `hcov : ∀ z : ↥(𝔟₁.subscheme), ∃ (w : ↥W) (y : ↥((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))), (Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))).base y = z`. Introduce `z`.

Conclude with `⟨𝔟₁.subschemeι.base z, ⟨z, hw (𝔟₁.subschemeι.base z)⟩, rfl⟩`. Use `Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers (↥W) (fun w => Scheme.Opens.toScheme ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))) (fun w => Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))) hcov) _ _ ?_` and prove the remaining obligations. Introduce `w`. Use `show Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens))) ≫ (𝔟₁.subschemeι ≫ h) = Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens))) ≫ (𝔟₁.subschemeι ≫ h')`. Rewrite using `[← hpre w]`.

Conclude with `comp_eq_on_chart_of_mul_eq_of_agree I h h' 𝔞 𝔟₁ (a w) (V' w) hagree hpull hfac (hVh w) (hVh' w) (hn w) (hs w)`.
-/
theorem subschemeι_comp_eq_of_affineBlowup_lifts (I : Ideal R) {W : Scheme.{u}}
    (ρ ρ' : W ⟶ Spec (CommRingCat.of R)) (𝔞 𝔟₁ : W.IdealSheafData)
    (h h' : W ⟶ Blowup.affineBlowup I)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (hpull : (Blowup.specIdealSheaf I).comap ρ = (Blowup.specIdealSheaf I).comap ρ')
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Blowup.specIdealSheaf I).comap ρ))
    (hfac : (Blowup.specIdealSheaf I).comap ρ * 𝔟₁ = 𝔞)
    (hh : h ≫ Blowup.AffineBlowup.toSpec I = ρ)
    (hh' : h' ≫ Blowup.AffineBlowup.toSpec I = ρ') :
    𝔟₁.subschemeι ≫ h = 𝔟₁.subschemeι ≫ h' := by
  subst hh
  subst hh'
  choose a V V' hw hpre hVh hVh' hn hs using
    exists_common_chart_affineOpen I h h' 𝔞 𝔟₁ hagree hpull hcart hfac
  have hcov : ∀ z : ↥(𝔟₁.subscheme), ∃ (w : ↥W)
      (y : ↥((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))),
      (Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))).base y = z := by
    intro z
    exact ⟨𝔟₁.subschemeι.base z, ⟨z, hw (𝔟₁.subschemeι.base z)⟩, rfl⟩
  refine Scheme.Cover.hom_ext
    (Scheme.Cover.mkOfCovers (↥W)
      (fun w => Scheme.Opens.toScheme
        ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens))))
      (fun w => Scheme.Opens.ι
        ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))) hcov) _ _ ?_
  intro w
  show Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))
        ≫ (𝔟₁.subschemeι ≫ h)
      = Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj ((V w : W.Opens)))
        ≫ (𝔟₁.subschemeι ≫ h')
  rw [← hpre w]
  exact comp_eq_on_chart_of_mul_eq_of_agree I h h' 𝔞 𝔟₁ (a w) (V' w) hagree hpull hfac
    (hVh w) (hVh' w) (hn w) (hs w)

end

end FunctorialResolution.EmbeddedResolution
