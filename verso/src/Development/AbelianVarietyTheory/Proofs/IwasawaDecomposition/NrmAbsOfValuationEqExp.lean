import Mathlib

noncomputable section

namespace GlobalTheory.Mem.NrmCompl

open NumberField IsDedekindDomain

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

def nrmAbs : AbsoluteValue (P.adicCompletion L) ℝ := NormedField.toAbsoluteValue (P.adicCompletion L)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nrmAbs_apply (x : P.adicCompletion L) : nrmAbs P x = ‖x‖ := rfl

/- English proof (translation)
The claim follows from `FinitePlace.norm_def (v := P) x`.
-/
theorem nrmAbs_eq_toNNReal (x : P.adicCompletion L) :
    nrmAbs P x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P) (Valued.v x) :=
  FinitePlace.norm_def (v := P) x

/- English proof (translation)
Establish `hv : Valued.v x ≠ 0` using `by simpa using hx`. Rewrite using `[nrmAbs_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]`. Take `⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n` from `⟨_, (WithZero.exp_log hv).symm⟩`. Simplify using `only [hn, WithZero.log_exp]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem nrmAbs_eq_zpow {x : P.adicCompletion L} (hx : x ≠ 0) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ (WithZero.log (Valued.v x)) := by
  have hv : Valued.v x ≠ 0 := by simpa using hx
  rw [nrmAbs_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨_, (WithZero.exp_log hv).symm⟩
  simp only [hn, WithZero.log_exp]
  push_cast
  rfl

/- English proof (translation)
Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero h.symm`. Rewrite using `[nrmAbs_eq_zpow P hx, h, WithZero.log_exp]`.
-/
theorem nrmAbs_of_valuation_eq_exp {x : P.adicCompletion L} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  rw [nrmAbs_eq_zpow P hx, h, WithZero.log_exp]

/- English proof (translation)
Rewrite using `[nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_le_coe]`. Conclude with `WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)`.
-/
theorem nrmAbs_le_one_iff (x : P.adicCompletion L) : nrmAbs P x ≤ 1 ↔ Valued.v x ≤ 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)

/- English proof (translation)
Rewrite using `[nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_inj]`. Conclude with `WithZeroMulInt.toNNReal_eq_one_iff _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P).ne'`.
-/
theorem nrmAbs_eq_one_iff (x : P.adicCompletion L) : nrmAbs P x = 1 ↔ Valued.v x = 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P).ne'

/- English proof (translation)
The claim follows from `continuous_norm`.
-/
theorem continuous_nrmAbs : Continuous (nrmAbs P) := continuous_norm

end GlobalTheory.Mem.NrmCompl
