import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

noncomputable section

open GlobalTheory.LatVal (Sz)
open Polynomial

namespace GlobalTheory.QFam.SzRing

variable (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])

abbrev nval : Valuation ℂ_[l] NNReal := NormedField.valuation

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `Iff.rfl`.
-/
theorem mem_integer_iff (y : ℂ_[l]) : y ∈ (nval l).integer ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
  exact Iff.rfl

def szRing : Subring ℂ :=
  ((nval l).integer.comap lam).map (algebraicClosure ℚ ℂ).val.toRingHom

/- English proof (translation)
Unfold `szRing Sz`. Rewrite using `[Real.rpow_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, (mem_integer_iff l _).1 hy⟩`.

Introduce and unpack `⟨h, hy⟩`. Conclude with `⟨⟨x, h⟩, (mem_integer_iff l _).2 hy, rfl⟩`.
-/
theorem mem_szRing (x : ℂ) : x ∈ szRing l lam ↔ Sz l lam 0 x := by
  unfold szRing Sz
  rw [Real.rpow_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (mem_integer_iff l _).1 hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨x, h⟩, (mem_integer_iff l _).2 hy, rfl⟩

def toAlg : szRing l lam →+* algebraicClosure ℚ ℂ :=
  (szRing l lam).subtype.codRestrict (algebraicClosure ℚ ℂ) fun r => ((mem_szRing l lam r.1).1 r.2).1

/- English proof (translation)
Take `⟨h, hr⟩` from `(mem_szRing l lam r.1).1 r.2`. Rewrite `hr` using `[Real.rpow_zero]`. Conclude with `(mem_integer_iff l _).2 hr`.
-/
theorem lam_toAlg_mem (r : szRing l lam) : (lam.comp (toAlg l lam)) r ∈ (nval l).integer := by
  obtain ⟨h, hr⟩ := (mem_szRing l lam r.1).1 r.2
  rw [Real.rpow_zero] at hr
  exact (mem_integer_iff l _).2 hr

/- English proof (translation)
Take `⟨p, hp, hpx⟩` from `hx`. Establish `hc : (algebraMap (algebraicClosure ℚ ℂ) ℂ).comp (toAlg l lam) = algebraMap (szRing l lam) ℂ` using `RingHom.ext fun _ => rfl`. Establish `h1 : IsIntegral (algebraicClosure ℚ ℂ) x` using `⟨p.map (toAlg l lam), hp.map _, by rw [eval₂_map, hc, hpx]⟩`. Establish `: Algebra.IsIntegral ℚ (algebraicClosure ℚ ℂ)` using `⟨fun y => (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val Subtype.val_injective).1 (mem_algebraicClosure_iff'.1 y.2)⟩`. Establish `h2 : x ∈ algebraicClosure ℚ ℂ` using `mem_algebraicClosure_iff'.2 (isIntegral_trans x h1)`.

Establish `h3 : eval₂ (toAlg l lam) ⟨x, h2⟩ p = 0`. Apply `(algebraMap (algebraicClosure ℚ ℂ) ℂ).injective` to reduce the goal to its premises. Rewrite using `[hom_eval₂, hc, map_zero]`. Conclude with `hpx`. Establish `h4 : eval₂ (lam.comp (toAlg l lam)) (lam ⟨x, h2⟩) p = 0`.

Rewrite using `[← hom_eval₂, h3, map_zero]`. Set `g : szRing l lam →+* (nval l).integer` to `(lam.comp (toAlg l lam)).codRestrict (nval l).integer (lam_toAlg_mem l lam)`. Establish `hg : (algebraMap (nval l).integer ℂ_[l]).comp g = lam.comp (toAlg l lam)` using `RingHom.ext fun _ => rfl`. Establish `h5 : IsIntegral (nval l).integer (lam ⟨x, h2⟩)` using `⟨p.map g, hp.map _, by rw [eval₂_map, hg, h4]⟩`. Establish `h6` using `(Valuation.integer.integers (nval l)).mem_of_integral h5`.

Rewrite using `[mem_szRing]`. Use `⟨h2, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_zero]`. Conclude with `(mem_integer_iff l _).1 h6`.
-/
theorem mem_szRing_of_isIntegral (x : ℂ) (hx : IsIntegral (szRing l lam) x) : x ∈ szRing l lam := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hc : (algebraMap (algebraicClosure ℚ ℂ) ℂ).comp (toAlg l lam) = algebraMap (szRing l lam) ℂ :=
    RingHom.ext fun _ => rfl
  have h1 : IsIntegral (algebraicClosure ℚ ℂ) x :=
    ⟨p.map (toAlg l lam), hp.map _, by rw [eval₂_map, hc, hpx]⟩
  have : Algebra.IsIntegral ℚ (algebraicClosure ℚ ℂ) :=
    ⟨fun y => (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val Subtype.val_injective).1
      (mem_algebraicClosure_iff'.1 y.2)⟩
  have h2 : x ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff'.2 (isIntegral_trans x h1)
  have h3 : eval₂ (toAlg l lam) ⟨x, h2⟩ p = 0 := by
    apply (algebraMap (algebraicClosure ℚ ℂ) ℂ).injective
    rw [hom_eval₂, hc, map_zero]
    exact hpx
  have h4 : eval₂ (lam.comp (toAlg l lam)) (lam ⟨x, h2⟩) p = 0 := by
    rw [← hom_eval₂, h3, map_zero]
  let g : szRing l lam →+* (nval l).integer :=
    (lam.comp (toAlg l lam)).codRestrict (nval l).integer (lam_toAlg_mem l lam)
  have hg : (algebraMap (nval l).integer ℂ_[l]).comp g = lam.comp (toAlg l lam) :=
    RingHom.ext fun _ => rfl
  have h5 : IsIntegral (nval l).integer (lam ⟨x, h2⟩) :=
    ⟨p.map g, hp.map _, by rw [eval₂_map, hg, h4]⟩
  have h6 := (Valuation.integer.integers (nval l)).mem_of_integral h5
  rw [mem_szRing]
  refine ⟨h2, ?_⟩
  rw [Real.rpow_zero]
  exact (mem_integer_iff l _).1 h6

end GlobalTheory.QFam.SzRing

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.QFam.SzRing.szRing l lam, GlobalTheory.QFam.SzRing.mem_szRing l lam, GlobalTheory.QFam.SzRing.mem_szRing_of_isIntegral l lam⟩`.
-/
theorem GlobalTheory.QFam.exists_szRing (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) :
    ∃ R : Subring ℂ, (∀ x, x ∈ R ↔ Sz l lam 0 x) ∧ ∀ x, IsIntegral R x → x ∈ R :=
  ⟨GlobalTheory.QFam.SzRing.szRing l lam, GlobalTheory.QFam.SzRing.mem_szRing l lam,
    GlobalTheory.QFam.SzRing.mem_szRing_of_isIntegral l lam⟩
