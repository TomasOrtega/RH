import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Establish `hv` using `WittVector.eq_iterate_verschiebung (n := 1) (x := a) (fun i hi => by`. Rewrite using `[Nat.lt_one_iff.1 hi]`. Conclude with `h)`. Establish `hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l)`. Rewrite using `[WittVector.frobenius_eq_map_frobenius]`.

Conclude with `WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective`. Take `⟨c, hc⟩` from `hsurj (a.shift 1)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, Function.iterate_one, ← hc, WittVector.verschiebung_frobenius, mul_comm]`.
-/
theorem ainf_exists_l_mul_of_coeff_zero (a : Ainf l) (h : a.coeff 0 = 0) :
    ∃ b : Ainf l, a = (l : Ainf l) * b := by
  have hv := WittVector.eq_iterate_verschiebung (n := 1) (x := a) (fun i hi => by
    rw [Nat.lt_one_iff.1 hi]; exact h)
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    rw [WittVector.frobenius_eq_map_frobenius]
    exact WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective
  obtain ⟨c, hc⟩ := hsurj (a.shift 1)
  refine ⟨c, ?_⟩
  rw [hv, Function.iterate_one, ← hc, WittVector.verschiebung_frobenius, mul_comm]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `WittVector.constantCoeff ((l : WittVector l R) * x) = 0`. Rewrite using `[map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]`.
-/
theorem coeff_zero_l_mul {R : Type} [CommRing R] [CharP R l] (x : WittVector l R) :
    ((l : WittVector l R) * x).coeff 0 = 0 := by
  change WittVector.constantCoeff ((l : WittVector l R) * x) = 0
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

/- English proof (translation)
Introduce `l _ K bk τ hτ`. Take `⟨-, ε, η, hε, hφ⟩` from `hτ`. Establish `hε1 : ε ≠ 1`. Introduce and unpack `rfl`. Take `⟨-, hu⟩` from `hε`.

Conclude with `hu (by rw [map_one]; simp)`. Establish `hc0 : τ.coeff 0 ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg (fun x => WittVector.constantCoeff x) hφ`. Express the relevant statement in the definitionally equal form `(WittVector.frobenius τ).coeff 0 = _ at h1`.

Rewrite `h1` using `[WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one]`. Express the relevant statement in the definitionally equal form `0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1`. Rewrite `h1` using `[WittVector.teichmuller_coeff_zero]`. Establish `hη : IsUnit (WittVector.constantCoeff (η : Ainf l))` using `η.isUnit.map _`. Break down `mul_eq_zero.1 h1.symm with h | h` into its components or cases.

Conclude with `hη.ne_zero h`. Conclude with `hε1 (sub_eq_zero.1 h)`. Establish `hU : IsUnit (inclW l τ)`. Apply `WittVector.isUnit_of_coeff_zero_ne_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (OCb l) (Cb l) (τ.coeff 0) ≠ 0`.

Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hc0`. Use `⟨hU, fun g => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← galW_inclW]`. Conclude with `hU.map (galW l g)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro a _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `a ⟨c, hc⟩`.

Establish `h0 : a.coeff 0 = 0`. Establish `h1 : (inclW l a).coeff 0 = 0`. Rewrite using `[hc, pow_succ', mul_assoc]`. Conclude with `coeff_zero_l_mul _`. Express the relevant statement in the definitionally equal form `algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1`.

Conclude with `(map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1`. Take `⟨b, rfl⟩` from `ainf_exists_l_mul_of_coeff_zero a h0`. Establish `hl0 : ((l : ℕ) : WCb l) ≠ 0` using `fun h => by`. Establish `h1` using `congrArg (fun x : WCb l => x.coeff 1) h`. Simplify using `[WittVector.coeff_p] at h1`.

Establish `hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b`. Use `⟨c, mul_left_cancel₀ hl0 ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]`. Conclude with `pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)`.
-/
theorem isUnit_inclW_per_and_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧
      ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  intro l _ K bk τ hτ
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hε1 : ε ≠ 1 := by
    rintro rfl
    obtain ⟨-, hu⟩ := hε
    exact hu (by rw [map_one]; simp)
  have hc0 : τ.coeff 0 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => WittVector.constantCoeff x) hφ
    change (WittVector.frobenius τ).coeff 0 = _ at h1
    rw [WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one] at h1
    change 0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1
    rw [WittVector.teichmuller_coeff_zero] at h1
    have hη : IsUnit (WittVector.constantCoeff (η : Ainf l)) := η.isUnit.map _
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact hη.ne_zero h
    · exact hε1 (sub_eq_zero.1 h)
  have hU : IsUnit (inclW l τ) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change algebraMap (OCb l) (Cb l) (τ.coeff 0) ≠ 0
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hc0
  refine ⟨hU, fun g => ?_, ?_⟩
  · rw [← galW_inclW]
    exact hU.map (galW l g)
  · intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ⟨c, hc⟩
      have h0 : a.coeff 0 = 0 := by
        have h1 : (inclW l a).coeff 0 = 0 := by
          rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
        change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
        exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
      obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
      have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
        have h1 := congrArg (fun x : WCb l => x.coeff 1) h
        simp [WittVector.coeff_p] at h1
      have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
        refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
        rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
      exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

end GlobalTheory.BSP
