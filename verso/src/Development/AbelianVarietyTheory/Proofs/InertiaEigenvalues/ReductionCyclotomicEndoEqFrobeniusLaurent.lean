import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
namespace GlobalTheory.RedPhiProof

/- English proof (translation)
Establish `hpoly : ∀ p : Polynomial O, f (p : O⟦X⟧) = g (p : O⟦X⟧)`. Introduce `p`. Establish `hfg : f.comp (Polynomial.coeToPowerSeries.ringHom) = g.comp (Polynomial.coeToPowerSeries.ringHom)` using `Polynomial.ringHom_ext (fun c => by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hC c) (by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hX)`. Simplify `RingHom.congr_fun hfg p` using `[Polynomial.coeToPowerSeries.ringHom_apply]`. Use `PowerSeries.ext fun n => ?_` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero, ← map_sub]`. Establish `htail : PowerSeries.X ^ (n + 1) ∣ a - (PowerSeries.trunc (n + 1) a : O⟦X⟧)`. Use `PowerSeries.X_pow_dvd_iff.mpr fun m hm => ?_` and prove the remaining obligations. Rewrite using `[map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]`. Take `⟨b, hb⟩` from `htail`.

Establish `ha : a = (PowerSeries.trunc (n + 1) a : O⟦X⟧) + PowerSeries.X ^ (n + 1) * b`. Rewrite using `[← hb]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdiv : PowerSeries.X ^ (n + 1) ∣ f a - g a`. Establish `e : f a - g a = f PowerSeries.X ^ (n + 1) * (f b - g b)` using `by conv_lhs => rw [ha]`.

Rewrite using `[map_add, map_add, hpoly, map_mul, map_mul, map_pow, map_pow, ← hX]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd _) _`. Conclude with `PowerSeries.X_pow_dvd_iff.mp hdiv n (Nat.lt_succ_self n)`.
-/
theorem ringHom_eq_of_agree {O k : Type} [CommRing O] [CommRing k] (f g : O⟦X⟧ →+* k⟦X⟧)
    (hC : ∀ c : O, f (PowerSeries.C c) = g (PowerSeries.C c))
    (hX : f PowerSeries.X = g PowerSeries.X) (hd : PowerSeries.X ∣ f PowerSeries.X) (a : O⟦X⟧) :
    f a = g a := by

  have hpoly : ∀ p : Polynomial O, f (p : O⟦X⟧) = g (p : O⟦X⟧) := by
    intro p
    have hfg : f.comp (Polynomial.coeToPowerSeries.ringHom) = g.comp (Polynomial.coeToPowerSeries.ringHom) :=
      Polynomial.ringHom_ext (fun c => by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hC c)
        (by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hX)
    simpa [Polynomial.coeToPowerSeries.ringHom_apply] using RingHom.congr_fun hfg p
  refine PowerSeries.ext fun n => ?_
  rw [← sub_eq_zero, ← map_sub]

  have htail : PowerSeries.X ^ (n + 1) ∣ a - (PowerSeries.trunc (n + 1) a : O⟦X⟧) := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun m hm => ?_
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨b, hb⟩ := htail
  have ha : a = (PowerSeries.trunc (n + 1) a : O⟦X⟧) + PowerSeries.X ^ (n + 1) * b := by
    rw [← hb]; ring

  have hdiv : PowerSeries.X ^ (n + 1) ∣ f a - g a := by
    have e : f a - g a = f PowerSeries.X ^ (n + 1) * (f b - g b) := by
      conv_lhs => rw [ha]
      rw [map_add, map_add, hpoly, map_mul, map_mul, map_pow, map_pow, ← hX]
      ring
    rw [e]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd _) _
  exact PowerSeries.X_pow_dvd_iff.mp hdiv n (Nat.lt_succ_self n)

/- English proof (translation)
Establish `hc : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) = 0` using `by simp`. Establish `hs : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1)` using `PowerSeries.HasSubst.of_constantCoeff_zero' hc`. Establish `key : PowerSeries.map (algebraMap O k) (φ₀ a) = (PowerSeries.map (algebraMap O k) a).subst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1)`. Establish `e` using `ringHom_eq_of_agree ((PowerSeries.map (algebraMap O k)).comp φ₀.toRingHom) ((PowerSeries.substAlgHom hs).toRingHom.comp (PowerSeries.map (algebraMap O k))) (fun c => by`. Establish `h1 : φ₀ (PowerSeries.C c) = PowerSeries.C c` using `by simpa using φ₀.commutes c`.

Establish `h2` using `(PowerSeries.substAlgHom hs).commutes (algebraMap O k c)`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, PowerSeries.map_C]`. Simplify using `using h2.symm)`. Use the proof step `(by`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h, PowerSeries.map_X, PowerSeries.substAlgHom_X]`.

Use the proof step `simp)`. Use the proof step `(by`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]`. Conclude with `PowerSeries.X_dvd_iff.mpr (by simp))`. Use `a`.

Simplify `e` using `[PowerSeries.coe_substAlgHom]`. Rewrite using `[key, GlobalTheory.PsiShiftProof.phi_eq_subst, GlobalTheory.PsiLemmaCompare.substHom_coe]`.
-/
theorem red_phi (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [Field k] [Algebra O k] [CharP k l]
    (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (h : φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1) (a : O⟦X⟧) :
    ((PowerSeries.map (algebraMap O k) (φ₀ a) : k⟦X⟧) : k⸨X⸩) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩) := by
  have hc : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) = 0 := by simp
  have hs : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hc

  have key : PowerSeries.map (algebraMap O k) (φ₀ a) =
      (PowerSeries.map (algebraMap O k) a).subst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) := by
    have e := ringHom_eq_of_agree ((PowerSeries.map (algebraMap O k)).comp φ₀.toRingHom)
      ((PowerSeries.substAlgHom hs).toRingHom.comp (PowerSeries.map (algebraMap O k)))
      (fun c => by
        have h1 : φ₀ (PowerSeries.C c) = PowerSeries.C c := by simpa using φ₀.commutes c
        have h2 := (PowerSeries.substAlgHom hs).commutes (algebraMap O k c)
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, PowerSeries.map_C]
        simpa using h2.symm)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h, PowerSeries.map_X,
          PowerSeries.substAlgHom_X]
        simp)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]
        exact PowerSeries.X_dvd_iff.mpr (by simp))
      a
    simpa [PowerSeries.coe_substAlgHom] using e
  rw [key, GlobalTheory.PsiShiftProof.phi_eq_subst, GlobalTheory.PsiLemmaCompare.substHom_coe]

end GlobalTheory.RedPhiProof
