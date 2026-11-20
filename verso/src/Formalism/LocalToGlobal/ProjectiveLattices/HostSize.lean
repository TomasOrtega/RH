import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtExC
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.I2

variable {D : D7}

/- English proof (translation)
Rewrite using `[D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]`. Use `first`. Consider the case `ring`. Consider the case `rfl`. Consider the case `omega`.

Consider the case `(simp only [Formalism.BasicNotions.Ranks.ord]; ring)`.
-/
theorem hostSize_finrank (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
  first
  | ring
  | rfl
  | omega
  | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.G.I2.PT.f, hostSize_finrank D]`. Use linear arithmetic over natural numbers and integers.
-/
theorem hostSize_f (D : D7) : PT.f D.host.E = D.R.f := by
  simp only [ReciprocityTheory.ChartRestriction.G.I2.PT.f, hostSize_finrank D]
  omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hostSize_rd (D : D7) : PT.rd D.host.E = D.host.rdE := rfl

/- English proof (translation)
The claim follows from `(UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1`.
-/
theorem hostSize_n_sqrt_le (D : D7) :
    Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

/- English proof (translation)
Take `⟨hq, hd⟩` from `D.host.qd_big`. Establish `hf : D.R.f = 2 * D.R.ord` using `Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)`. Establish `hfk` using `D.R.f_le_k`. Establish `hm` using `D.R.two_le_m`. Establish `hmf` using `D.R.m_le_f`.

Establish `ht` using `D.R.rank_add_five_le`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `h1 : D.R.f + 6 ≤ D.R.t` using `by omega`. Establish `h2 : D.R.f + 6 ≤ 4 * D.R.r` using `by omega`. Establish `key : (D.R.f + 6) ^ 2 < 4 * D.R.t * D.R.r + 1`.

Use `Nat.mul_le_mul h1 h2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `keyR : ((D.R.f : ℝ) + 6) ^ 2 < ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ)` using `by exact_mod_cast key`. Establish `hA : (0 : ℝ) ≤ ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hqR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.q : ℝ)` using `by exact_mod_cast hq`.

Establish `hdR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.d : ℝ)` using `by exact_mod_cast hd`. Establish `hsq : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < Real.sqrt ((D.host.q : ℝ) * D.host.d)`. Rewrite using `[Real.lt_sqrt hA]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hostSize_sqrt_gt {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) :
    ((D.R.f : ℝ) + 6) ^ 2 < Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hf : D.R.f = 2 * D.R.ord := Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)
  have hfk := D.R.f_le_k
  have hm := D.R.two_le_m
  have hmf := D.R.m_le_f
  have ht := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h1 : D.R.f + 6 ≤ D.R.t := by omega
  have h2 : D.R.f + 6 ≤ 4 * D.R.r := by omega
  have key : (D.R.f + 6) ^ 2 < 4 * D.R.t * D.R.r + 1 := by
    have := Nat.mul_le_mul h1 h2
    nlinarith
  have keyR : ((D.R.f : ℝ) + 6) ^ 2 < ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) := by exact_mod_cast key
  have hA : (0 : ℝ) ≤ ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.q : ℝ) := by exact_mod_cast hq
  have hdR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.d : ℝ) := by exact_mod_cast hd
  have hsq : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.lt_sqrt hA]
    nlinarith
  linarith

/- English proof (translation)
Establish `h1` using `hostSize_sqrt_gt P`. Establish `h2` using `hostSize_n_sqrt_le D`. Rewrite using `[hostSize_f D, hostSize_rd D]`. Establish `h0 : (0 : ℝ) ≤ (D.R.f : ℝ)` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem host_f_sq_le_rd {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : (PT.f D.host.E : ℝ) ^ 2 ≤ PT.rd D.host.E := by
  have h1 := hostSize_sqrt_gt P
  have h2 := hostSize_n_sqrt_le D
  rw [hostSize_f D, hostSize_rd D]
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  nlinarith

/- English proof (translation)
Establish `h1` using `hostSize_sqrt_gt P`. Establish `h2` using `hostSize_n_sqrt_le D`. Rewrite using `[hostSize_rd D]`. Establish `h0 : (0 : ℝ) ≤ (D.R.f : ℝ)` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem host_rd_ge_sixteen {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : 16 ≤ PT.rd D.host.E := by
  have h1 := hostSize_sqrt_gt P
  have h2 := hostSize_n_sqrt_le D
  rw [hostSize_rd D]
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  nlinarith

/- English proof (translation)
Establish `hx : 1 < large₂.sc.x` using `large₂.sc.one_lt_alt`. Establish `hx0 : 0 < large₂.sc.x` using `by linarith`. Establish `he : 0 < large₂.sc.eps` using `large₂.sc.eps_pos`. Take `⟨⟨hN1, -⟩, ⟨-, hM2⟩, -⟩` from `hS`. Simplify using `only [Formalism.MainNotions.szTh, Formalism.BasicNotions.Scale.delta1] at hN1 hM2`.

Establish `hA : Real.sqrt (large₂.sc.x * large₂.sc.x ^ (-(large₂.sc.eps / 8))) = large₂.sc.x ^ ((1 + -(large₂.sc.eps / 8)) * (1 / 2))`. Rewrite using `[Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]`. Rewrite `hM2` using `[hA, ← Real.rpow_add hx0]`. Establish `hm0 : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `h4 : (D.R.m : ℝ) ^ 4 ≤ (large₂.sc.x ^ (large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2))) ^ 4` using `pow_le_pow_left₀ hm0 hM2 4`.

Establish `h5 : (large₂.sc.x ^ (large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2))) ^ 4 = large₂.sc.x ^ ((large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2)) * 4)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Evaluate the numerical expressions. Establish `h6 : large₂.sc.x ^ ((large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2)) * 4) ≤ large₂.sc.x ^ (2 + 8 * large₂.sc.eps - large₂.sc.eps / 100)` using `Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)`. Establish `key : ((D.R.m ^ 4 : ℕ) : ℝ) ≤ (D.R.n : ℝ)`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmn : D.R.m ^ 4 ≤ D.R.n` using `by exact_mod_cast key`. Establish `hn : D.R.n = D.R.ord` using `rfl`. Rewrite using `[hostSize_f D, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem host_m_pow_four_le_f {large₂ : SizeData₂ D} (hS : SizesAt large₂) : D.R.m ^ 4 ≤ PT.f D.host.E := by
  have hx : 1 < large₂.sc.x := large₂.sc.one_lt_alt
  have hx0 : 0 < large₂.sc.x := by linarith
  have he : 0 < large₂.sc.eps := large₂.sc.eps_pos
  obtain ⟨⟨hN1, -⟩, ⟨-, hM2⟩, -⟩ := hS
  simp only [Formalism.MainNotions.szTh, Formalism.BasicNotions.Scale.delta1] at hN1 hM2
  have hA : Real.sqrt (large₂.sc.x * large₂.sc.x ^ (-(large₂.sc.eps / 8))) =
      large₂.sc.x ^ ((1 + -(large₂.sc.eps / 8)) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]
  rw [hA, ← Real.rpow_add hx0] at hM2
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have h4 : (D.R.m : ℝ) ^ 4 ≤ (large₂.sc.x ^ (large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2))) ^ 4 :=
    pow_le_pow_left₀ hm0 hM2 4
  have h5 : (large₂.sc.x ^ (large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2))) ^ 4 =
      large₂.sc.x ^ ((large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2)) * 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h6 : large₂.sc.x ^ ((large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2)) * 4) ≤
      large₂.sc.x ^ (2 + 8 * large₂.sc.eps - large₂.sc.eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have key : ((D.R.m ^ 4 : ℕ) : ℝ) ≤ (D.R.n : ℝ) := by
    push_cast
    linarith
  have hmn : D.R.m ^ 4 ≤ D.R.n := by exact_mod_cast key
  have hn : D.R.n = D.R.ord := rfl
  rw [hostSize_f D, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
  omega

end Formalism.L2.Pj
