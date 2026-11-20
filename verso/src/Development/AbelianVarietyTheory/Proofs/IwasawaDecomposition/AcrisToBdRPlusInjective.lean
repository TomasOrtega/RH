import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisDivisibleOfKernelPowersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFiltrationApproxByEnvelopeKernelPowerStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

/- English proof (translation)
Take `⟨-, -, hd, hdv⟩` from `acris_basic l`. Take `⟨s, z, hs⟩` from `hd x 1`. Establish `h1 : (l : Per.Acris0 l) ∣ s`. Use `GlobalTheory.T.acris_divisible_of_kernel_powers l s fun n => ?_` and prove the remaining obligations. Take `⟨u, z', hu, e⟩` from `GlobalTheory.T.acris_filtration_approx_by_envelope_kernel_power l j hj n x (by rw [hx]; exact zero_mem _)`.

Take `⟨w, hw⟩` from `(hdv (s - u) 1).1 ⟨z' - z, by rw [map_sub]; linear_combination e - hs⟩`. Conclude with `⟨u, w, by linear_combination hw, hu⟩`. Take `⟨w, hw⟩` from `h1`. Establish `e : x = (l : Per.Acris l) * (algebraMap (Per.Acris0 l) (Per.Acris l) w + z)`. Rewrite using `[hs, hw, map_mul, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨_, ?_, e⟩` and prove the remaining obligations. Establish `hu : IsUnit (l : Per.BdRp l)`. Use `(GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Rewrite `hx` using `[e, map_mul, map_natCast]`. Conclude with `hu.mul_right_eq_zero.1 hx`.
-/
theorem crisP_ker_dvd (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (x : Per.Acris l) (hx : j x = 0) : ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) * y := by
  obtain ⟨-, -, hd, hdv⟩ := acris_basic l
  obtain ⟨s, z, hs⟩ := hd x 1
  have h1 : (l : Per.Acris0 l) ∣ s := by
    refine GlobalTheory.T.acris_divisible_of_kernel_powers l s fun n => ?_
    obtain ⟨u, z', hu, e⟩ := GlobalTheory.T.acris_filtration_approx_by_envelope_kernel_power l j hj n x (by rw [hx]; exact zero_mem _)
    obtain ⟨w, hw⟩ := (hdv (s - u) 1).1 ⟨z' - z, by rw [map_sub]; linear_combination e - hs⟩
    exact ⟨u, w, by linear_combination hw, hu⟩
  obtain ⟨w, hw⟩ := h1
  have e : x = (l : Per.Acris l) * (algebraMap (Per.Acris0 l) (Per.Acris l) w + z) := by
    rw [hs, hw, map_mul, map_natCast]
    ring
  refine ⟨_, ?_, e⟩
  have hu : IsUnit (l : Per.BdRp l) := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
    rwa [map_natCast] at this
  rw [e, map_mul, map_natCast] at hx
  exact hu.mul_right_eq_zero.1 hx

/- English proof (translation)
Introduce `l _ j hj`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h : ∀ n : ℕ, ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) ^ n * y`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => exact ⟨x, hx, by rw [pow_zero, one_mul]⟩`. Consider the case `succ n ih`. Take `⟨y, hy, e⟩` from `ih`. Take `⟨y', hy', e'⟩` from `crisP_ker_dvd l j hj y hy`.

Conclude with `⟨y', hy', by rw [e, e', pow_succ, mul_assoc]⟩`. Establish `hc` using `(acris_basic l).1`. Use `hc.toIsHausdorff.haus x fun n => ?_` and prove the remaining obligations. Take `⟨y, -, e⟩` from `h n`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Conclude with `⟨y, e⟩`.
-/
theorem crisP_injective : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Function.Injective j := by
  intro l _ j hj
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h : ∀ n : ℕ, ∃ y : Per.Acris l, j y = 0 ∧ x = (l : Per.Acris l) ^ n * y := by
    intro n
    induction n with
    | zero => exact ⟨x, hx, by rw [pow_zero, one_mul]⟩
    | succ n ih =>
      obtain ⟨y, hy, e⟩ := ih
      obtain ⟨y', hy', e'⟩ := crisP_ker_dvd l j hj y hy
      exact ⟨y', hy', by rw [e, e', pow_succ, mul_assoc]⟩
  have hc := (acris_basic l).1
  refine hc.toIsHausdorff.haus x fun n => ?_
  obtain ⟨y, -, e⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨y, e⟩

end GlobalTheory.MemLoc
