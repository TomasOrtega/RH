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
Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_integer_iff (y : ℂ_[l]) : y ∈ (nval l).integer ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
  exact Iff.rfl

def szRing : Subring ℂ :=
  ((nval l).integer.comap lam).map (algebraicClosure ℚ ℂ).val.toRingHom

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
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
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem lam_toAlg_mem (r : szRing l lam) : (lam.comp (toAlg l lam)) r ∈ (nval l).integer := by
  obtain ⟨h, hr⟩ := (mem_szRing l lam r.1).1 r.2
  rw [Real.rpow_zero] at hr
  exact (mem_integer_iff l _).2 hr

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Supply the required witnesses or components.
-/
theorem GlobalTheory.QFam.exists_szRing (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) :
    ∃ R : Subring ℂ, (∀ x, x ∈ R ↔ Sz l lam 0 x) ∧ ∀ x, IsIntegral R x → x ∈ R :=
  ⟨GlobalTheory.QFam.SzRing.szRing l lam, GlobalTheory.QFam.SzRing.mem_szRing l lam,
    GlobalTheory.QFam.SzRing.mem_szRing_of_isIntegral l lam⟩
