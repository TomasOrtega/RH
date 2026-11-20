import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPf
import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosureProperties

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.H2CurveOrder.LeafKumMuInjPfGlue
open LateralTheory.E.H2CurveOrder.LeafKumMuInjPf

/- English proof (translation)
Introduce `q A _ ζ`. Take `⟨hq, hz⟩` from `ζ.2`. Break down `Nat.eq_zero_or_pos q with rfl | hq0` into its components or cases. Establish `: Subsingleton A`. Simplify using `at hz`.

Conclude with `subsingleton_of_zero_eq_one hz.symm`. Conclude with `⟨1, Subsingleton.elim _ _, fun _ _ => Or.inr this⟩`. Establish `hqz : ζ.1 ^ q = 1`. Take `⟨G, hG⟩` from `cyclotomic.dvd_X_pow_sub_one q ℤ`. Use `congrArg (aeval ζ.1) hG` as an intermediate fact.

Simplify using `[hz] at this`. Conclude with `sub_eq_zero.1 this`. Establish `h1 : ζ.1 * ζ.1 ^ (q - 1) = 1` using `by rw [← pow_succ', Nat.sub_add_cancel hq0]; exact hqz`. Establish `hu : IsUnit ζ.1` using `⟨⟨ζ.1, ζ.1 ^ (q - 1), h1, by rw [mul_comm]; exact h1⟩, rfl⟩`. Use `⟨hu.unit, rfl, fun c hc => ?_⟩` and prove the remaining obligations.

Establish `hc' : ζ.1 ^ c = 1` using `by simpa using congrArg Units.val hc`. Use `set d := Nat.gcd c q with hd`. Establish `hdz : ζ.1 ^ d = 1` using `pow_gcd_eq_one.2 ⟨hc', hqz⟩`. Distinguish the cases in `hdq : d = q`. Use `left`.

Rewrite using `[← hdq]`. Conclude with `Nat.gcd_dvd_left c q`. Use `right`. Take `⟨G, hG⟩` from `X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ (Nat.mem_properDivisors.2 ⟨Nat.gcd_dvd_right c q, lt_of_le_of_ne (Nat.le_of_dvd hq0 (Nat.gcd_dvd_right c q)) hdq⟩)`. Establish `hG'` using `congrArg (Polynomial.map (Int.castRingHom A)) hG`.

Simplify using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, map_cyclotomic] at hG'`. Establish `r1 : (X - C ζ.1) ∣ (X ^ d - 1 : A[X])` using `dvd_iff_isRoot.2 (by simp [hdz])`. Establish `r2 : (X - C ζ.1) ∣ cyclotomic q A` using `dvd_iff_isRoot.2 (by`. Use `hz` as an intermediate fact. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic] at this)` and apply the resulting hypothesis.

Take `⟨a, ha⟩` from `r1`. Take `⟨b, hb⟩` from `r2`. Establish `hE : (X ^ q - 1 : A[X]) = (X - C ζ.1) ^ 2 * (a * b * G.map (Int.castRingHom A))`. Rewrite using `[hG', ha, hb]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hD` using `congrArg (fun p => eval ζ.1 (derivative p)) hE`. Simplify using `[derivative_mul, derivative_pow] at hD`. Establish `hu' : IsUnit ((q : A) * ζ.1 ^ (q - 1))` using `hq.mul (hu.pow _)`. Establish `h0 : (q : A) * ζ.1 ^ (q - 1) = 0` using `by simpa using hD`. Rewrite `hu'` using `[h0]`.

Conclude with `subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu')`.
-/
theorem cycPow : CycPow := by
  intro q A _ ζ
  obtain ⟨hq, hz⟩ := ζ.2
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · have : Subsingleton A := by
      simp at hz
      exact subsingleton_of_zero_eq_one hz.symm
    exact ⟨1, Subsingleton.elim _ _, fun _ _ => Or.inr this⟩
  have hqz : ζ.1 ^ q = 1 := by
    obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
    have := congrArg (aeval ζ.1) hG
    simp [hz] at this
    exact sub_eq_zero.1 this
  have h1 : ζ.1 * ζ.1 ^ (q - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hq0]; exact hqz
  have hu : IsUnit ζ.1 := ⟨⟨ζ.1, ζ.1 ^ (q - 1), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, rfl, fun c hc => ?_⟩
  have hc' : ζ.1 ^ c = 1 := by simpa using congrArg Units.val hc
  set d := Nat.gcd c q with hd
  have hdz : ζ.1 ^ d = 1 := pow_gcd_eq_one.2 ⟨hc', hqz⟩
  by_cases hdq : d = q
  · left; rw [← hdq]; exact Nat.gcd_dvd_left c q
  right
  obtain ⟨G, hG⟩ := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ (Nat.mem_properDivisors.2 ⟨Nat.gcd_dvd_right c q, lt_of_le_of_ne (Nat.le_of_dvd hq0 (Nat.gcd_dvd_right c q)) hdq⟩)
  have hG' := congrArg (Polynomial.map (Int.castRingHom A)) hG
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_cyclotomic] at hG'
  have r1 : (X - C ζ.1) ∣ (X ^ d - 1 : A[X]) := dvd_iff_isRoot.2 (by simp [hdz])
  have r2 : (X - C ζ.1) ∣ cyclotomic q A := dvd_iff_isRoot.2 (by
    have := hz
    rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at this)
  obtain ⟨a, ha⟩ := r1
  obtain ⟨b, hb⟩ := r2
  have hE : (X ^ q - 1 : A[X]) = (X - C ζ.1) ^ 2 * (a * b * G.map (Int.castRingHom A)) := by
    rw [hG', ha, hb]; ring
  have hD := congrArg (fun p => eval ζ.1 (derivative p)) hE
  simp [derivative_mul, derivative_pow] at hD
  have hu' : IsUnit ((q : A) * ζ.1 ^ (q - 1)) := hq.mul (hu.pow _)
  have h0 : (q : A) * ζ.1 ^ (q - 1) = 0 := by simpa using hD
  rw [h0] at hu'
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu')

/- English proof (translation)
Introduce `R _ F V hs y`. Establish `: IsEmpty V`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : V.presheaf.stalk x) = 0`. Rewrite using `[← map_one (V.presheaf.germ ⊤ x trivial).hom, Subsingleton.elim (1 : Γ(V, ⊤)) 0, map_zero]`.

Conclude with `one_ne_zero h1`. Conclude with `LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.shfSep R F V y (LateralTheory.EtaleFoundations.LocBasicPf.loc_empty V _)`.
-/
theorem emptySec : EmptySec := by
  intro R _ F V hs y
  have : IsEmpty V := by
    refine ⟨fun x => ?_⟩
    have h1 : (1 : V.presheaf.stalk x) = 0 := by
      rw [← map_one (V.presheaf.germ ⊤ x trivial).hom, Subsingleton.elim (1 : Γ(V, ⊤)) 0, map_zero]
    exact one_ne_zero h1
  exact LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.shfSep R F V y (LateralTheory.EtaleFoundations.LocBasicPf.loc_empty V _)

/- English proof (translation)
The claim follows from `LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.LeafKumMuInj_of hL hG cycPow emptySec`.
-/
theorem LeafKumMuInj_of (hL : TwLocGen) (hG : GmSep) : LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.LeafKumMuInj :=
  LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.LeafKumMuInj_of hL hG cycPow emptySec

end LateralTheory.E.H2CurveOrder.LeafKumMuInjPfGlue
