import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoSidedShiftSeriesHasSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisSeriesTermsMemPrimePowStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply', ih, (GlobalTheory.CrisMaps.phiA_extends l).alg]`. Use `congr 1`.

Use `(GlobalTheory.RingIface.phiA_teich l (z ^ l ^ j)).trans ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, ← pow_succ]`.
-/
theorem iter_tm {l : ℕ} [Fact l.Prime] (j : ℕ) (z : Fl l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[j] (algebraMap (Ainf l) (Acris l) (tm z)) =
      algebraMap (Ainf l) (Acris l) (tm (z ^ l ^ j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, (GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    refine (GlobalTheory.RingIface.phiA_teich l (z ^ l ^ j)).trans ?_
    rw [← pow_mul, ← pow_succ]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using e`. Consider the case `succ k ih`. Apply `ih` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero]`.

Apply `(GlobalTheory.MemLoc.acris_basic l).2.1` to reduce the goal to its premises. Take the linear combination `e`.
-/
theorem acris_cancel {l : ℕ} [Fact l.Prime] (k : ℕ) (u v : Acris l)
    (e : (l : Acris l) ^ k * u = (l : Acris l) ^ k * v) : u = v := by
  induction k with
  | zero => simpa using e
  | succ k ih =>
    apply ih
    rw [← sub_eq_zero]
    apply (GlobalTheory.MemLoc.acris_basic l).2.1
    linear_combination e

/- English proof (translation)
Introduce `l _ h x h2 hx`. Take `⟨-, -, -, hpw_comp, hpw_nat, -, -⟩` from `GlobalTheory.T.tiltFrobeniusIntegerPower_laws l`. Take `⟨c, hdvd, hc⟩` from `GlobalTheory.T.acris_series_terms_mem_prime_pow l h x h2 hx`. Use `haveI := (GlobalTheory.MemLoc.acris_basic l).1`. Establish `hφl : ∀ (j : ℕ) (k : ℕ) (a : Acris l), (⇑(GlobalTheory.MemLoc.phiA l))^[j] ((l : Acris l) ^ k * a) = (l : Acris l) ^ k * (⇑(GlobalTheory.MemLoc.phiA l))^[j] a`.

Introduce `j k a`. Rewrite using `[← RingHom.coe_pow, map_mul, map_pow, map_natCast]`. Establish `hpwj : ∀ (n : ℤ) (j : ℕ), pw (n * h) x ^ l ^ j = pw (n * h + j) x`. Introduce `n j`. Rewrite using `[← hpw_nat, ← hpw_comp, add_comm]`.

Establish `shift : ∀ n : ℤ, (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n) = (l : Acris l) * c (n + 1)`. Introduce `n`. Apply `acris_cancel (n.toNat + (n+1).toNat)` to reduce the goal to its premises. Establish `e1` using `congrArg ((⇑(GlobalTheory.MemLoc.phiA l))^[h]) (hc n)`. Rewrite `e1` using `[hφl, hφl, iter_tm, hpwj]`.

Establish `e2` using `hc (n + 1)`. Establish `hh : (n + 1) * (h : ℤ) = n * h + h` using `by ring`. Rewrite `e2` using `[hh]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers. Use `_ = _ := by rw [← e2]; ring`. Take `⟨w, hw, hsum⟩` from `GlobalTheory.T.twoSided_shift_series_hasSum l (Acris l) (GlobalTheory.MemLoc.phiA l) h c hdvd shift`. Use `⟨w, hw, fun Θ hΘ hΘt j => ?_⟩` and prove the remaining obligations.

Establish `hs` using `hsum (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (fun a => hΘ _)`. Establish `hl : (l : ℂ_[l]) ≠ 0` using `GlobalTheory.RingBasics.p_ne_zero`. Establish `hterm : ∀ n : ℤ, (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (c n) = (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)`. Introduce `n`. Establish `e` using `congrArg (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (hc n)`.

Rewrite `e` using `[RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_pow, hφl, hφl, iter_tm, hpwj, map_mul, map_mul, map_pow, map_pow, map_natCast, hΘt]`. Rewrite using `[RingHom.comp_apply, RingHom.coe_pow]`. Establish `hn : -n = ((-n).toNat : ℤ) - (n.toNat : ℤ)` using `by omega`. Establish `ha : (l : ℂ_[l]) ^ n.toNat ≠ 0` using `pow_ne_zero _ hl`. Rewrite using `[hn, zpow_sub₀ hl, zpow_natCast, zpow_natCast]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel_left₀ ha]`. Use `_ = _ := by rw [e]; ring`. Establish `hs' : HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) ((Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) w)`. Simplify `hs` using `only [hterm]`.

Rewrite using `[lam, hs'.tsum_eq, RingHom.comp_apply, RingHom.coe_pow]`.
-/
theorem series_acris : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = lam h j x := by
  intro l _ h x h2 hx
  obtain ⟨-, -, -, hpw_comp, hpw_nat, -, -⟩ := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  obtain ⟨c, hdvd, hc⟩ := GlobalTheory.T.acris_series_terms_mem_prime_pow l h x h2 hx
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  have hφl : ∀ (j : ℕ) (k : ℕ) (a : Acris l), (⇑(GlobalTheory.MemLoc.phiA l))^[j] ((l : Acris l) ^ k * a) =
      (l : Acris l) ^ k * (⇑(GlobalTheory.MemLoc.phiA l))^[j] a := by
    intro j k a
    rw [← RingHom.coe_pow, map_mul, map_pow, map_natCast]
  have hpwj : ∀ (n : ℤ) (j : ℕ), pw (n * h) x ^ l ^ j = pw (n * h + j) x := by
    intro n j
    rw [← hpw_nat, ← hpw_comp, add_comm]
  have shift : ∀ n : ℤ, (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n) = (l : Acris l) * c (n + 1) := by
    intro n
    apply acris_cancel (n.toNat + (n+1).toNat)
    have e1 := congrArg ((⇑(GlobalTheory.MemLoc.phiA l))^[h]) (hc n)
    rw [hφl, hφl, iter_tm, hpwj] at e1
    have e2 := hc (n + 1)
    have hh : (n + 1) * (h : ℤ) = n * h + h := by ring
    rw [hh] at e2
    calc (l : Acris l) ^ (n.toNat + (n+1).toNat) * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)
        = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ n.toNat * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)) := by ring
      _ = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ (-n).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by rw [e1]
      _ = (l : Acris l) ^ (n.toNat + 1) * ((l : Acris l) ^ (-(n+1)).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          congr 2
          omega
      _ = _ := by rw [← e2]; ring
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.T.twoSided_shift_series_hasSum l (Acris l) (GlobalTheory.MemLoc.phiA l) h c hdvd shift
  refine ⟨w, hw, fun Θ hΘ hΘt j => ?_⟩
  have hs := hsum (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (fun a => hΘ _)
  have hl : (l : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  have hterm : ∀ n : ℤ, (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (c n) =
      (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
    intro n
    have e := congrArg (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (hc n)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_pow, hφl, hφl, iter_tm, hpwj, map_mul,
      map_mul, map_pow, map_pow, map_natCast, hΘt] at e
    rw [RingHom.comp_apply, RingHom.coe_pow]
    have hn : -n = ((-n).toNat : ℤ) - (n.toNat : ℤ) := by omega
    have ha : (l : ℂ_[l]) ^ n.toNat ≠ 0 := pow_ne_zero _ hl
    rw [hn, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
    calc Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))
        = ((l : ℂ_[l]) ^ n.toNat)⁻¹ * ((l : ℂ_[l]) ^ n.toNat * Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))) := by
          rw [inv_mul_cancel_left₀ ha]
      _ = _ := by rw [e]; ring
  have hs' : HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x))
      ((Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) w) := by
    simpa only [hterm] using hs
  rw [lam, hs'.tsum_eq, RingHom.comp_apply, RingHom.coe_pow]

end GlobalTheory.PSer

end
