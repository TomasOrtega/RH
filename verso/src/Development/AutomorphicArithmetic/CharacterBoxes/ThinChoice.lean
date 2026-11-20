import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AutomorphicArithmetic.MeanSquareBounds.Thin
import Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros
import Development.AutomorphicArithmetic.ConductorsKronecker.realClass
import Development.AutomorphicArithmetic.ConductorsKronecker.OddQSLe

section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (authored)
For every term in the range from one to the integer part of y, one has y/n ≥ 1. Thus the maximum weight equals y/n − 1. Substitute this equality in the finite sums and expand the matching principal and nonprincipal definitions, including the logarithmic derivative term in the latter case.
-/
private theorem gauss_sum_function_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HC.An.gChi χ y = G0 χ y := by
  have hmax : ∀ n ∈ Icc 1 ⌊y⌋₊, max (y / n - 1) 0 = y / n - 1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hy : 0 ≤ y := by
      by_contra hc
      rw [Nat.floor_of_nonpos (le_of_lt (not_le.1 hc))] at h2
      omega
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff hy).1 h2
    have : 1 ≤ y / n := (one_le_div hn0).2 hny
    exact max_eq_left (by linarith)
  unfold Formalism.HC.An.gChi G0
  by_cases h : χ = 1
  · rw [if_pos h, if_pos h]
    unfold Formalism.HC.An.G G1
    rw [Finset.sum_congr rfl fun n hn => by rw [hmax n hn]]
  · rw [if_neg h, if_neg h]
    unfold Formalism.HC.An.sumLamChi Gchi Formalism.HC.An.logDerivativeAtOne logDerivLAtOne
    rw [Finset.sum_congr rfl fun n hn => by rw [hmax n hn]]

/- English proof (authored)
A character whose square is trivial takes only the values zero, one, and minus one. Each has imaginary part zero.
-/
private theorem isReal_of_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h2 : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.2 h2 a with h | h | h <;> simp [h]

end QH

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (authored)
Choose the fixed exponent factor one half, and take the uniform thin-scale estimate with zero-free width the smaller of 1/400 and the small-conductor width. Each primitive character under consideration has conductor dividing the host conductor, so the assumed logarithmic bound controls its modulus. For a real character the conductor classification gives two possibilities. It is either bounded in terms of the odd part of the host modulus, where the small-zero estimate applies uniformly, or it is divisible by one of the two host primes, where the assumed zero box applies. The resulting real-zero condition permits the thin-scale estimate, and the two weighted character sums agree term by term.
-/
theorem thinChoice_host : ThinChoice := by
  intro eps he _
  refine ⟨1 / 2, by norm_num, fun Co => ?_⟩
  obtain ⟨c₁, hc₁, hsm⟩ := QH.small_zeros ⌈8 * Co ^ 2⌉₊
  obtain ⟨x₀, hx₀⟩ := QH.thin eps 3 (1 / 2) (min (1 / 400) c₁) he (by norm_num) (by norm_num) (lt_min (by norm_num) hc₁)
  refine ⟨x₀, ?_⟩
  intro s R H hs hx _ ho hQ hlog hbox
  subst hs
  rw [thinScales_iff_hostBound]
  intro N _ χ hχ y hy
  have hB := UpperTheory.GL.oddQS_le H.toHostRaw Co ho hQ
  obtain ⟨hdvd, hcl⟩ := UpperTheory.GL.realClass H.toHostRaw N χ hχ
  have hp : χ.IsPrimitive := hχ.choose_spec.1
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [QH.gauss_sum_function_eq]
  refine hx₀ s.x hx N χ hp ?_ ?_ y hy
  · refine le_trans ?_ hlog
    refine Real.log_le_log (by exact_mod_cast hN0) ?_
    exact_mod_cast (Nat.le_of_dvd H.condN_pos hdvd : N ≤ H.QS * H.q * H.d)
  · intro h2 h1 β hb1 hb2
    have hr := QH.isReal_of_sq χ h2
    rcases hcl hr with hN | hqd
    · have hle : N ≤ 8 * ordCompl[2] H.QS :=
        Nat.le_of_dvd (Nat.mul_pos (by norm_num) (Nat.ordCompl_pos 2 H.QS_pos.ne')) hN
      have hle' : N ≤ ⌈8 * Co ^ 2⌉₊ := by
        have a1 : (N : ℝ) ≤ 8 * ((ordCompl[2] H.QS : ℕ) : ℝ) := by exact_mod_cast hle
        have a2 : (N : ℝ) ≤ (⌈8 * Co ^ 2⌉₊ : ℝ) := le_trans (by linarith) (Nat.le_ceil (8 * Co ^ 2))
        exact_mod_cast a2
      refine hsm N χ hle' h1 β ?_ hb2
      have := min_le_right (1 / 400 : ℝ) c₁
      linarith
    · refine hbox N χ hχ hr hqd β ?_ hb2
      have := min_le_left (1 / 400 : ℝ) c₁
      linarith

end GlobalTheory.EX
