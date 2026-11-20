import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenThetaTorsion

variable {Λ : AddSubgroup ℂ}

def phase (Λ : AddSubgroup ℂ) (x y : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (y * (starRingEnd ℂ) x - x * (starRingEnd ℂ) y) / (2 * (area Λ : ℂ)))

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
theorem phase_ne_zero (x y : ℂ) : phase Λ x y ≠ 0 := Complex.exp_ne_zero _

/- English proof (translation)
Simplify using `only [U1, phase]`. Rewrite using `[mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc]`. Use `congr 2`. Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaTranslate_comp_eq_phase_mul_add (x y : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ x (U1 Λ y G) z = phase Λ x y * U1 Λ (x + y) G z := by
  simp only [U1, phase]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc]
  congr 2
  simp only [map_add]
  ring

/- English proof (translation)
Take `⟨m, hm, hx⟩` from `hx`. Take `⟨n, hn, hy⟩` from `hy`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Use `Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rationalLatticePoint_add {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have := Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)
  convert this using 1
  simp only [nsmul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, by simpa using hx⟩`.
-/
theorem rationalLatticePoint_of_mem_lattice {x : ℂ} (hx : x ∈ Λ) : InRationalLattice Λ x := ⟨1, one_pos, by simpa using hx⟩

/- English proof (translation)
Take `⟨m, hm, hx⟩` from `hx`. Take `⟨n, hn, hy⟩` from `hy`. Take `⟨L, hL⟩` from `GlobalTheory.OddTheta.exists_periodPair Λ h`. Take `⟨k, hk⟩` from `GlobalTheory.exists_int_im_latticeForm L ((hL _).1 hy) ((hL _).1 hx)`. Establish `hA` using `GlobalTheory.latticeArea_pos L`.

Rewrite `hk` using `[GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff hA.ne', ← GlobalTheory.OddTheta.area_eq L Λ hL]`. Rewrite `hA` using `[← GlobalTheory.OddTheta.area_eq L Λ hL]`. Establish `hA' : (area Λ : ℂ) ≠ 0` using `by exact_mod_cast hA.ne'`. Establish `e` using `Complex.sub_conj ((n : ℂ) * y * (starRingEnd ℂ) ((m : ℂ) * x))`. Rewrite `e` using `[hk]`.

Simplify using `only [map_mul, map_natCast, Complex.conj_conj] at e`. Move the coercions through the operations in `at e`. Establish `hp : phase Λ x y ^ (2 * m * n) = 1`. Rewrite using `[phase, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`. Rewrite using `[mem_algebraicClosure_iff]`. Use `IsAlgebraic.of_pow (n := 2 * m * n) (by positivity) ?_` and prove the remaining obligations.

Rewrite using `[hp]`. Conclude with `isAlgebraic_one`.
-/
theorem phase_mem (h : IsLat Λ) {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) :
    phase Λ x y ∈ Qbar := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ((hL _).1 hy) ((hL _).1 hx)
  have hA := GlobalTheory.latticeArea_pos L
  rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff hA.ne', ← GlobalTheory.OddTheta.area_eq L Λ hL] at hk
  rw [← GlobalTheory.OddTheta.area_eq L Λ hL] at hA
  have hA' : (area Λ : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have e := Complex.sub_conj ((n : ℂ) * y * (starRingEnd ℂ) ((m : ℂ) * x))
  rw [hk] at e
  simp only [map_mul, map_natCast, Complex.conj_conj] at e
  push_cast at e
  have hp : phase Λ x y ^ (2 * m * n) = 1 := by
    rw [phase, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    field_simp
    linear_combination e
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * m * n) (by positivity) ?_
  rw [hp]
  exact isAlgebraic_one

/- English proof (translation)
Use `⟨hF.1.const_mul κ, fun n => ?_⟩` and prove the remaining obligations. Establish `: coef1 (fun z => κ * F z) n = κ * coef1 F n`. Rewrite using `[coef1, coef1, iteratedDeriv_const_mul_field, mul_div_assoc]`. Rewrite using `[this]`. Conclude with `Qbar.mul_mem hκ (hF.2 n)`.
-/
theorem algEnt_const_mul {F : ℂ → ℂ} (hF : AlgEnt F) {κ : ℂ} (hκ : κ ∈ Qbar) :
    AlgEnt fun z => κ * F z := by
  refine ⟨hF.1.const_mul κ, fun n => ?_⟩
  have : coef1 (fun z => κ * F z) n = κ * coef1 F n := by
    rw [coef1, coef1, iteratedDeriv_const_mul_field, mul_div_assoc]
  rw [this]
  exact Qbar.mul_mem hκ (hF.2 n)

/- English proof (translation)
Rewrite using `[div_mul_eq_mul_div, ← thetaTranslate_comp_eq_phase_mul_add]`. Simplify using `only [U1, GL3Theta.th0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaTranslate_evenTheta_eq_sigmaStar_translate (t x z : ℂ) : U1 Λ x (GL3Theta.th0 Λ t) z =
    (phase Λ x t / U1 Λ t (sgStar Λ) 0) * U1 Λ (x + t) (sgStar Λ) z := by
  rw [div_mul_eq_mul_div, ← thetaTranslate_comp_eq_phase_mul_add]
  simp only [U1, GL3Theta.th0]
  ring

/- English proof (translation)
Establish `e` using `thetaTranslate_comp_eq_phase_mul_add (Λ := Λ) y ω (sgStar Λ) z`. Rewrite `e` using `[funext (h.sg_law hω)]`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff (phase_ne_zero _ _), mul_comm, ← e]`. Simplify using `only [U1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigmaStarTranslate_add_lattice_sign_phase (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (y z : ℂ) :
    U1 Λ (y + ω) (sgStar Λ) z =
      ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ y ω) * U1 Λ y (sgStar Λ) z := by
  have e := thetaTranslate_comp_eq_phase_mul_add (Λ := Λ) y ω (sgStar Λ) z
  rw [funext (h.sg_law hω)] at e
  rw [div_mul_eq_mul_div, eq_div_iff (phase_ne_zero _ _), mul_comm, ← e]
  simp only [U1]
  ring

/- English proof (translation)
Introduce `Λ h halg t _ h2 x hx`. Establish `ht : InRationalLattice Λ t` using `⟨2, two_pos, by simpa using h2⟩`. Establish `hc : U1 Λ t (sgStar Λ) 0 ∈ Qbar`. Simplify `(halg t ht).2 0` using `[coef1]`. Use `⟨?_, fun ω hω => ?_⟩` and prove the remaining obligations.

Rewrite using `[funext (thetaTranslate_evenTheta_eq_sigmaStar_translate t x)]`. Conclude with `algEnt_const_mul (halg _ (rationalLatticePoint_add hx ht)) (Qbar.div_mem (phase_mem h hx ht) hc)`. Establish `hω'` using `rationalLatticePoint_of_mem_lattice hω`. Establish `hs : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ∈ Qbar` using `by split_ifs`. Conclude with `Qbar.one_mem`.

Conclude with `Qbar.neg_mem Qbar.one_mem`. Apply the tactic sequence `have hs0 : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ≠ 0 := by split_ifs <;> norm_num`. Use `⟨phase Λ (x + ω) t / phase Λ x t * ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ (x + t) ω), Qbar.mul_mem (Qbar.div_mem (phase_mem h (rationalLatticePoint_add hx hω') ht) (phase_mem h hx ht)) (Qbar.div_mem hs (phase_mem h (rationalLatticePoint_add hx ht) hω')), mul_ne_zero (div_ne_zer …` and prove the remaining obligations. Rewrite using `[thetaTranslate_evenTheta_eq_sigmaStar_translate, thetaTranslate_evenTheta_eq_sigmaStar_translate, add_right_comm, sigmaStarTranslate_add_lattice_sign_phase h hω]`. Use `phase_ne_zero (Λ := Λ) x t` as an intermediate fact.

Generalize the expression as in `(if ω / 2 ∈ Λ then 1 else -1 : ℂ) / phase Λ (x + t) ω = s`. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]`. Generalize the expression as in `(U1 Λ t (sgStar Λ) 0)⁻¹ = c`. Clear the denominators using the available nonvanishing facts.
-/
theorem algebraicTaylor_torsionTranslate_evenTheta_alt : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  intro Λ h halg t _ h2 x hx
  have ht : InRationalLattice Λ t := ⟨2, two_pos, by simpa using h2⟩
  have hc : U1 Λ t (sgStar Λ) 0 ∈ Qbar := by
    simpa [coef1] using (halg t ht).2 0
  refine ⟨?_, fun ω hω => ?_⟩
  · rw [funext (thetaTranslate_evenTheta_eq_sigmaStar_translate t x)]
    exact algEnt_const_mul (halg _ (rationalLatticePoint_add hx ht)) (Qbar.div_mem (phase_mem h hx ht) hc)
  · have hω' := rationalLatticePoint_of_mem_lattice hω
    have hs : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ∈ Qbar := by
      split_ifs
      · exact Qbar.one_mem
      · exact Qbar.neg_mem Qbar.one_mem
    have hs0 : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ≠ 0 := by
      split_ifs <;> norm_num
    refine ⟨phase Λ (x + ω) t / phase Λ x t * ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ (x + t) ω),
      Qbar.mul_mem (Qbar.div_mem (phase_mem h (rationalLatticePoint_add hx hω') ht) (phase_mem h hx ht))
        (Qbar.div_mem hs (phase_mem h (rationalLatticePoint_add hx ht) hω')),
      mul_ne_zero (div_ne_zero (phase_ne_zero _ _) (phase_ne_zero _ _))
        (div_ne_zero hs0 (phase_ne_zero _ _)), fun z => ?_⟩
    rw [thetaTranslate_evenTheta_eq_sigmaStar_translate, thetaTranslate_evenTheta_eq_sigmaStar_translate, add_right_comm, sigmaStarTranslate_add_lattice_sign_phase h hω]
    have := phase_ne_zero (Λ := Λ) x t
    generalize (if ω / 2 ∈ Λ then 1 else -1 : ℂ) / phase Λ (x + t) ω = s
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    generalize (U1 Λ t (sgStar Λ) 0)⁻¹ = c
    field_simp

end GlobalTheory.EvenThetaTorsion
