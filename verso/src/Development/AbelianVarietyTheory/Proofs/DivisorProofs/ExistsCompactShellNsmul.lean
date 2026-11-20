import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.NonarchShell

/- English proof (translation)
Introduce `F _ _ v N V hV`. Use `haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v`. Take `⟨r, hr, hrV⟩` from `Metric.mem_nhds_iff.1 hV`. Use `set q : ℕ := Ideal.absNorm v.asIdeal with hqdef`. Establish `hq0 : q ≠ 0`.

Rewrite using `[hqdef, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `hq1 : ‖(q : v.adicCompletion F)‖ < 1`. Use `(NumberField.FinitePlace.norm_lt_one_iff_mem F v ((q : 𝓞 F))).2 (Ideal.absNorm_mem _)` as an intermediate fact. Rewrite `this` using `[map_natCast, map_natCast]`. Then use the resulting hypothesis.

Establish `hqne : (q : v.adicCompletion F) ≠ 0`. Rewrite using `[← map_natCast (algebraMap F (v.adicCompletion F)) q]`. Conclude with `(map_ne_zero _).2 (Nat.cast_ne_zero.2 hq0)`. Establish `hqpos : 0 < ‖(q : v.adicCompletion F)‖` using `norm_pos_iff.2 hqne`. Establish `hsm : ∀ (m : ℕ) (t : Fin N → v.adicCompletion F), ‖m • t‖ = ‖(m : v.adicCompletion F)‖ * ‖t‖`.

Introduce `m t`. Rewrite using `[← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]`. Use `⟨{t | r * ‖(q : v.adicCompletion F)‖ ≤ ‖t‖ ∧ ‖t‖ ≤ r}, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(isCompact_closedBall (0 : Fin N → v.adicCompletion F) r).of_isClosed_subset ?_ ?_` and prove the remaining obligations. Conclude with `(isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)`.

Introduce `t ht`. Simplify `ht.2` using `[mem_closedBall_zero_iff]`. Introduce `h`. Establish `h1` using `h.1`. Rewrite `h1` using `[norm_zero]`.

Conclude with `absurd h1 (not_le.2 (mul_pos hr hqpos))`. Introduce `t ht`. Establish `htr : r ≤ ‖t‖`. Assume the negation of the conclusion as `hlt`. Conclude with `ht (hrV (mem_ball_zero_iff.2 (not_le.1 hlt)))`.

Establish `htpos : 0 < ‖t‖` using `lt_of_lt_of_le hr htr`. Establish `hex : ∃ k : ℕ, ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (div_pos hr htpos) hq1`. Conclude with `⟨k, (lt_div_iff₀ htpos).1 hk⟩`. Use `set k := Nat.find hex with hkdef`.

Establish `hk : ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r` using `Nat.find_spec hex`. Establish `hk0 : k ≠ 0`. Introduce `h0`. Rewrite `hk` using `[h0, pow_zero, one_mul]`. Conclude with `absurd htr (not_le.2 hk)`.

Take `⟨j, hj⟩` from `Nat.exists_eq_succ_of_ne_zero hk0`. Establish `hjmin : ¬ ‖(q : v.adicCompletion F)‖ ^ j * ‖t‖ < r` using `Nat.find_min hex (by omega)`. Establish `hnorm : ‖(q ^ k) • t‖ = ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖`. Rewrite using `[hsm, Nat.cast_pow, norm_pow]`. Use `⟨q ^ k, ?_, ?_⟩` and prove the remaining obligations.

Use `show r * ‖(q : v.adicCompletion F)‖ ≤ ‖(q ^ k) • t‖`. Rewrite using `[hnorm, hj, pow_succ]`. Use `not_lt.1 hjmin` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `show ‖(q ^ k) • t‖ ≤ r`.

Rewrite using `[hnorm]`. Conclude with `hk.le`.
-/
theorem exists_compact_shell_nsmul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (V : Set (Fin N → v.adicCompletion F)), V ∈ nhds 0 →
      ∃ K : Set (Fin N → v.adicCompletion F), IsCompact K ∧ (0 : Fin N → v.adicCompletion F) ∉ K ∧
        ∀ t, t ∉ V → ∃ n : ℕ, n • t ∈ K := by
  intro F _ _ v N V hV
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq1 : ‖(q : v.adicCompletion F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v ((q : 𝓞 F))).2 (Ideal.absNorm_mem _)
    rwa [map_natCast, map_natCast] at this
  have hqne : (q : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F)) q]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hq0)
  have hqpos : 0 < ‖(q : v.adicCompletion F)‖ := norm_pos_iff.2 hqne
  have hsm : ∀ (m : ℕ) (t : Fin N → v.adicCompletion F), ‖m • t‖ = ‖(m : v.adicCompletion F)‖ * ‖t‖ := by
    intro m t
    rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]
  refine ⟨{t | r * ‖(q : v.adicCompletion F)‖ ≤ ‖t‖ ∧ ‖t‖ ≤ r}, ?_, ?_, ?_⟩
  · refine (isCompact_closedBall (0 : Fin N → v.adicCompletion F) r).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro t ht
      simpa [mem_closedBall_zero_iff] using ht.2
  · intro h
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.2 (mul_pos hr hqpos))
  · intro t ht
    have htr : r ≤ ‖t‖ := by
      by_contra hlt
      exact ht (hrV (mem_ball_zero_iff.2 (not_le.1 hlt)))
    have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr htr
    have hex : ∃ k : ℕ, ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr htpos) hq1
      exact ⟨k, (lt_div_iff₀ htpos).1 hk⟩
    classical
    set k := Nat.find hex with hkdef
    have hk : ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hk
      exact absurd htr (not_le.2 hk)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjmin : ¬ ‖(q : v.adicCompletion F)‖ ^ j * ‖t‖ < r :=
      Nat.find_min hex (by omega)
    have hnorm : ‖(q ^ k) • t‖ = ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ := by
      rw [hsm, Nat.cast_pow, norm_pow]
    refine ⟨q ^ k, ?_, ?_⟩
    · show r * ‖(q : v.adicCompletion F)‖ ≤ ‖(q ^ k) • t‖
      rw [hnorm, hj, pow_succ]
      have := not_lt.1 hjmin
      nlinarith
    · show ‖(q ^ k) • t‖ ≤ r
      rw [hnorm]; exact hk.le

end GlobalTheory.NonarchShell
