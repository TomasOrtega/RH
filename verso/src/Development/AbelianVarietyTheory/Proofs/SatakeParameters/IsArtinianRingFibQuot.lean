import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
open GlobalTheory.PD

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra R S := (f : R →+* S).toAlgebra`. Use `haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)`. Use `haveI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S`. Use `haveI : Algebra.IsIntegral R S := ⟨hi⟩`. Use `haveI : Module.Finite R S := Algebra.IsIntegral.finite`.

Take `⟨G, hG⟩` from `Module.Finite.fg_top (R := R) (M := S)`. Use `⟨⟨G.image (Ideal.Quotient.mk I), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `q -`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective q`.

Establish `hs : s ∈ Submodule.span R (G : Set S)` using `hG ▸ Submodule.mem_top`. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul r a _ ha`. Take `⟨c, hc⟩` from `hc r`. Establish `e : Ideal.Quotient.mk I (r • a) = c • Ideal.Quotient.mk I a`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap]`.

Use `congr 1`. Conclude with `Ideal.Quotient.eq.2 hc`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem finite_quotient_of_integral {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra.FiniteType k S] (f : R →ₐ[k] S) (hi : (f : R →+* S).IsIntegral) (I : Ideal S)
    (hc : ∀ r, ∃ c : k, f r - algebraMap k S c ∈ I) : Module.Finite k (S ⧸ I) := by
  classical
  letI : Algebra R S := (f : R →+* S).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  haveI : Algebra.IsIntegral R S := ⟨hi⟩
  haveI : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨⟨G.image (Ideal.Quotient.mk I), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hs : s ∈ Submodule.span R (G : Set S) := hG ▸ Submodule.mem_top
  induction hs using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    obtain ⟨c, hc⟩ := hc r
    have e : Ideal.Quotient.mk I (r • a) = c • Ideal.Quotient.mk I a := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap]
      congr 1
      exact Ideal.Quotient.eq.2 hc
    rw [e]
    exact Submodule.smul_mem _ _ ha

end GlobalTheory

namespace GlobalTheory.PD

/- English proof (translation)
Introduce `k K _ _ _ F _ _ _ _ d x h`. Use `haveI := h.smooth 0`. Use `set I := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) with hI`. Set `f : rA k x {0} →ₐ[k] rB k K x {0}` to `((IsScalarTower.toAlgHom k F K).comp (rA k x {0}).val).codRestrict (rB k K x {0}) (fun a => (integralClosure (rA k x {0}) K).algebraMap_mem a)`. Establish `hi : (f : rA k x {0} →+* rB k K x {0}).IsIntegral`.

Introduce `s`. Take `⟨p, hm, hp⟩` from `s.2`. Use `⟨p, hm, Subtype.val_injective ?_⟩` and prove the remaining obligations. Establish `e` using `Polynomial.hom_eval₂ p (f : rA k x {0} →+* rB k K x {0}) (rB k K x {0}).val.toRingHom s`. Use `e.trans ?_` and prove the remaining obligations.

Conclude with `hp`. Establish `hc : ∀ r, ∃ c : k, f r - algebraMap k _ c ∈ I`. Introduce and unpack `⟨r, hr⟩`. Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem y hy`.

Take `⟨i, hi0, j, rfl⟩` from `hy`. Rewrite `hi0` using `[Finset.mem_singleton]`. Substitute `hi0` using the available equality. Consider the cases of `j using Fin.cases with`. Consider the case `zero`.

Use `⟨1, ?_⟩` and prove the remaining obligations. Use `I.zero_mem using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_one, sub_eq_zero]`. Use `Subtype.ext ?_` and prove the remaining obligations. Use `show algebraMap F K (x 0 / x 0) = 1`.

Rewrite using `[div_self (h.pd.ne 0), map_one]`. Consider the case `succ j`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, sub_zero]`. Conclude with `Ideal.subset_span ⟨j, rfl⟩`.

Consider the case `algebraMap r`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `: f ⟨algebraMap k F r, _⟩ = algebraMap k _ r` using `f.commutes r`. Rewrite using `[this, sub_self]`. Conclude with `I.zero_mem`.

Consider the case `add a b ha hb iha ihb`. Take `⟨c₁, h₁⟩` from `iha`. Take `⟨c₂, h₂⟩` from `ihb`. Use `⟨c₁ + c₂, ?_⟩` and prove the remaining obligations. Establish `: f ⟨a + b, add_mem ha hb⟩ = f ⟨a, ha⟩ + f ⟨b, hb⟩` using `map_add f ⟨a, ha⟩ ⟨b, hb⟩`.

Rewrite using `[this, map_add]`. Use `add_mem h₁ h₂ using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul a b ha hb iha ihb`. Take `⟨c₁, h₁⟩` from `iha`.

Take `⟨c₂, h₂⟩` from `ihb`. Use `⟨c₁ * c₂, ?_⟩` and prove the remaining obligations. Establish `: f ⟨a * b, mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩` using `map_mul f ⟨a, ha⟩ ⟨b, hb⟩`. Rewrite using `[this, map_mul]`. Use `add_mem (I.mul_mem_right (f ⟨b, hb⟩) h₁) (I.mul_mem_left (algebraMap k _ c₁) h₂) using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use `haveI := GlobalTheory.finite_quotient_of_integral f hi I hc`. Conclude with `IsArtinianRing.of_finite k _`.
-/
theorem isArtinianRing_fib_quot : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  intro k K _ _ _ F _ _ _ _ d x h
  haveI := h.smooth 0
  set I := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) with hI
  let f : rA k x {0} →ₐ[k] rB k K x {0} :=
    ((IsScalarTower.toAlgHom k F K).comp (rA k x {0}).val).codRestrict (rB k K x {0})
      (fun a => (integralClosure (rA k x {0}) K).algebraMap_mem a)
  have hi : (f : rA k x {0} →+* rB k K x {0}).IsIntegral := by
    intro s
    obtain ⟨p, hm, hp⟩ := s.2
    refine ⟨p, hm, Subtype.val_injective ?_⟩
    have e := Polynomial.hom_eval₂ p (f : rA k x {0} →+* rB k K x {0}) (rB k K x {0}).val.toRingHom s
    refine e.trans ?_
    exact hp
  have hc : ∀ r, ∃ c : k, f r - algebraMap k _ c ∈ I := by
    rintro ⟨r, hr⟩
    induction hr using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi0, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi0
      subst hi0
      cases j using Fin.cases with
      | zero =>
        refine ⟨1, ?_⟩
        convert I.zero_mem using 1
        rw [map_one, sub_eq_zero]
        refine Subtype.ext ?_
        show algebraMap F K (x 0 / x 0) = 1
        rw [div_self (h.pd.ne 0), map_one]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero, sub_zero]
        exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap r =>
      refine ⟨r, ?_⟩
      have : f ⟨algebraMap k F r, _⟩ = algebraMap k _ r := f.commutes r
      rw [this, sub_self]
      exact I.zero_mem
    | add a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ + c₂, ?_⟩
      have : f ⟨a + b, add_mem ha hb⟩ = f ⟨a, ha⟩ + f ⟨b, hb⟩ := map_add f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_add]
      convert add_mem h₁ h₂ using 1
      ring
    | mul a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ * c₂, ?_⟩
      have : f ⟨a * b, mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩ := map_mul f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_mul]
      convert add_mem (I.mul_mem_right (f ⟨b, hb⟩) h₁) (I.mul_mem_left (algebraMap k _ c₁) h₂) using 1
      ring
  haveI := GlobalTheory.finite_quotient_of_integral f hi I hc
  exact IsArtinianRing.of_finite k _

end GlobalTheory.PD
