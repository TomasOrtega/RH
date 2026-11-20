import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LocBasisPlace
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.KernelEntryData
import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormOnePowerPrincipal.PowPrincipal
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemilocalBasis.IsPID
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalBasisAtPrime.Imports

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

/- English proof (translation)
Unfold `lamC`. Rewrite using `[dif_pos h]`.
-/
theorem lamC_mem' {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) :
    lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC; rw [dif_pos h]

/- English proof (translation)
Establish `hx : IsAlgebraic ℚ x` using `Algebra.IsAlgebraic.isAlgebraic x`. Establish `: IsAlgebraic ℚ ((embT D τ).toRatAlgHom x)` using `hx.algHom _`. Conclude with `(mem_algebraicClosure_iff).2 this`.
-/
theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

instance instUltraCp (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℂ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)

section Nu

variable {E : Type} [Field E] [NumberField E] {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : E →+* K)

end Nu

noncomputable def psiT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E →+* ℂ_[p] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

/- English proof (translation)
The claim follows from `lamC_mem' lam (embT_mem D τ x)`.
-/
theorem lamC_embT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = psiT D lam τ x := lamC_mem' lam (embT_mem D τ x)

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Classical

end Formalism.MainNotions.GL3Columns

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Columns

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions

/- English proof (translation)
Introduce `de hde`. Establish `he : 0 < eps`. Take `⟨i⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_eps 0 i]`. Conclude with `(Fm.L 0 i).sc.eps_pos`.

Establish `hq0 : 0 ≤ |Fm.CGam| / de` using `div_nonneg (abs_nonneg _) hde.le`. Use `⟨max (Fm.x1 + 1) (|Fm.CGam| / de + 2), ?_, ?_⟩` and prove the remaining obligations. Conclude with `lt_of_lt_of_le (by linarith [Fm.one_lt_family_threshold]) (le_max_left _ _)`. Introduce `x hx i u`. Establish `hx1 : Fm.x1 < x`.

Use `(le_max_left (Fm.x1 + 1) (|Fm.CGam| / de + 2)).trans hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxc : |Fm.CGam| / de + 2 ≤ x` using `(le_max_right _ _).trans hx`. Establish `h1x : 1 ≤ x` using `by linarith`. Establish `h0x : 0 < x` using `by linarith`.

Take `⟨-, ⟨-, hm⟩, ⟨hk, -⟩⟩` from `fam_sizes Fm x hx1 i`. Establish `hL : (Fm.L x i).sc.L = x ^ eps`. Unfold `Scale.L`. Rewrite using `[Fm.L_x x i hx1, Fm.L_eps x i]`. Rewrite using `[(Fm.L x i).Gam_eq u, Fm.CGam_eq x i, hL]`.

Use `set m : ℝ := ((Fm.D x i).R.m : ℝ) with hmdef`. Use `set k : ℝ := ((Fm.D x i).R.k : ℝ) with hkdef`. Use `set f : ℝ := ((Fm.D x i).R.f : ℝ) with hfdef`. Establish `hm0 : 0 ≤ m` using `Nat.cast_nonneg _`. Establish `hf0 : 0 ≤ f` using `Nat.cast_nonneg _`.

Establish `hk0 : 0 ≤ k` using `Nat.cast_nonneg _`. Establish `hs : Real.sqrt (x * x ^ (-(eps / 8))) ≤ x ^ ((1 : ℝ) / 2)`. Rewrite using `[← Real.sqrt_eq_rpow]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Establish `: x ^ (-(eps / 8)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos h1x (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hm' : m ≤ x ^ (eps / 100 + 1 / 2)`. Rewrite using `[Real.rpow_add h0x]`. Conclude with `hm.trans (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg h0x.le _))`. Establish `hm5 : m ^ 5 ≤ x ^ ((eps / 100 + 1 / 2) * 5)`.

Rewrite using `[Real.rpow_mul h0x.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Conclude with `pow_le_pow_left₀ hm0 hm' 5`. Establish `hmL : m ^ 5 * x ^ eps * x ^ (2 : ℝ) ≤ k`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add h0x, Real.rpow_add h0x]`.

Use `_ ≤ x ^ (9 / 2 + 10 * eps - eps / 100) := Real.rpow_le_rpow_of_exponent_le h1x (by nlinarith)`. Use `_ ≤ k := hk`. Establish `hx2 : |Fm.CGam| ≤ de * x ^ (2 : ℝ)`. Establish `h1 : |Fm.CGam| ≤ de * x`. Establish `: |Fm.CGam| / de ≤ x` using `by linarith`.

Rewrite `this` using `[div_le_iff₀ hde, mul_comm]`. Then use the resulting hypothesis. Establish `h2 : x ≤ x ^ (2 : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h1.trans (mul_le_mul_of_nonneg_left h2 hde.le)`. Establish `hA : 0 ≤ m ^ 5 * x ^ eps` using `mul_nonneg (pow_nonneg hm0 5) (Real.rpow_nonneg h0x.le _)`.

Establish `key : Fm.CGam * (m ^ 5 * x ^ eps) ≤ de * k`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem family_log_gamma_small_holds {eps : ℝ} (Fm : FamP eps) : compactDualInputFamily Fm := by
  intro de hde
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  have hq0 : 0 ≤ |Fm.CGam| / de := div_nonneg (abs_nonneg _) hde.le
  refine ⟨max (Fm.x1 + 1) (|Fm.CGam| / de + 2), ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith [Fm.one_lt_family_threshold]) (le_max_left _ _)
  intro x hx i u
  have hx1 : Fm.x1 < x := by
    have := (le_max_left (Fm.x1 + 1) (|Fm.CGam| / de + 2)).trans hx
    linarith
  have hxc : |Fm.CGam| / de + 2 ≤ x := (le_max_right _ _).trans hx
  have h1x : 1 ≤ x := by linarith
  have h0x : 0 < x := by linarith
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩⟩ := fam_sizes Fm x hx1 i
  have hL : (Fm.L x i).sc.L = x ^ eps := by
    unfold Scale.L
    rw [Fm.L_x x i hx1, Fm.L_eps x i]
  rw [(Fm.L x i).Gam_eq u, Fm.CGam_eq x i, hL]
  set m : ℝ := ((Fm.D x i).R.m : ℝ) with hmdef
  set k : ℝ := ((Fm.D x i).R.k : ℝ) with hkdef
  set f : ℝ := ((Fm.D x i).R.f : ℝ) with hfdef
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  have hk0 : 0 ≤ k := Nat.cast_nonneg _

  have hs : Real.sqrt (x * x ^ (-(eps / 8))) ≤ x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_sqrt
    have : x ^ (-(eps / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1x (by linarith)
    nlinarith
  have hm' : m ≤ x ^ (eps / 100 + 1 / 2) := by
    rw [Real.rpow_add h0x]
    exact hm.trans (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg h0x.le _))
  have hm5 : m ^ 5 ≤ x ^ ((eps / 100 + 1 / 2) * 5) := by
    rw [Real.rpow_mul h0x.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ hm0 hm' 5
  have hmL : m ^ 5 * x ^ eps * x ^ (2 : ℝ) ≤ k := by
    calc m ^ 5 * x ^ eps * x ^ (2 : ℝ)
        ≤ x ^ ((eps / 100 + 1 / 2) * 5) * x ^ eps * x ^ (2 : ℝ) := by
          gcongr
      _ = x ^ ((eps / 100 + 1 / 2) * 5 + eps + 2) := by
          rw [Real.rpow_add h0x, Real.rpow_add h0x]
      _ ≤ x ^ (9 / 2 + 10 * eps - eps / 100) :=
          Real.rpow_le_rpow_of_exponent_le h1x (by nlinarith)
      _ ≤ k := hk
  have hx2 : |Fm.CGam| ≤ de * x ^ (2 : ℝ) := by
    have h1 : |Fm.CGam| ≤ de * x := by
      have : |Fm.CGam| / de ≤ x := by linarith
      rwa [div_le_iff₀ hde, mul_comm] at this
    have h2 : x ≤ x ^ (2 : ℝ) := by
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by norm_num)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hde.le)
  have hA : 0 ≤ m ^ 5 * x ^ eps := mul_nonneg (pow_nonneg hm0 5) (Real.rpow_nonneg h0x.le _)
  have key : Fm.CGam * (m ^ 5 * x ^ eps) ≤ de * k := by
    calc Fm.CGam * (m ^ 5 * x ^ eps) ≤ |Fm.CGam| * (m ^ 5 * x ^ eps) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hA
      _ ≤ de * x ^ (2 : ℝ) * (m ^ 5 * x ^ eps) := mul_le_mul_of_nonneg_right hx2 hA
      _ = de * (m ^ 5 * x ^ eps * x ^ (2 : ℝ)) := by ring
      _ ≤ de * k := mul_le_mul_of_nonneg_left hmL hde.le
  calc Fm.CGam * m ^ 5 * f * x ^ eps = Fm.CGam * (m ^ 5 * x ^ eps) * f := by ring
    _ ≤ de * k * f := mul_le_mul_of_nonneg_right key hf0
    _ = de * f * k := by ring

end Formalism.MainNotions.ShortIntervalPrimes
