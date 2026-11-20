import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Introduce `l hl x m hm hlm hx`. Take `⟨h1, h2, h3⟩` from `tilt_facts l`. Establish `hxC : (x : ℂ_[l]) ^ m = 1`. Use `congrArg (algebraMap (Om l) ℂ_[l]) hx` as an intermediate fact. Rewrite `this` using `[map_pow, map_one]`.

Conclude with `this`. Establish `hn : ‖(x : ℂ_[l])‖ ≤ 1`. Establish `h` using `congrArg norm hxC`. Rewrite `h` using `[norm_pow, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h).le`.

Take `⟨y, hyx⟩ : ∃ y : Per.OC l, (y : ℂ_[l]) = (x : ℂ_[l])` from `⟨⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩, rfl⟩`. Establish `hy : y ^ m = 1` using `Subtype.ext (by push_cast; rw [hyx, hxC])`. Establish `hc : Nat.Coprime l m` using `(Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by`. Use `⟨l ^ (m.totient - 1), ?_⟩` and prove the remaining obligations.

Rewrite using `[← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]`. Conclude with `Nat.ModEq.pow_totient hc`. Establish `hstep : ∀ z : Per.OC l, z ^ m = 1 → (z ^ a) ^ l = z` using `fun z hz => by`. Rewrite using `[← pow_mul]`. Simplify using `using pow_eq_pow_of_modEq ha hz`.

Establish `hpm : ∀ n : ℕ, (y ^ a ^ n) ^ m = 1` using `fun n => by`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hy, one_pow]`. Take `⟨e, he⟩` from `h1 (fun n => y ^ a ^ n) (fun n => by show (y ^ a ^ (n + 1)) ^ l = y ^ a ^ n`. Rewrite using `[pow_succ, pow_mul]`. Conclude with `hstep _ (hpm n))`.

Use `⟨e, h2 _ fun n => by rw [h3, he, hpm], ?_⟩` and prove the remaining obligations. Establish `h0` using `he 0`. Rewrite `h0` using `[pow_zero, pow_one]`. Rewrite using `[← hyx, ← h0]`. Both sides reduce to the same expression.
-/
theorem exists_tilt_root_of_unity : ∀ (l : ℕ) [Fact l.Prime] (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → ∃ e : Per.Fl l, e ^ m = 1 ∧ (e.untilt : ℂ_[l]) = (x : ℂ_[l]) := by
  intro l hl x m hm hlm hx
  obtain ⟨h1, h2, h3⟩ := tilt_facts l
  have hxC : (x : ℂ_[l]) ^ m = 1 := by
    have := congrArg (algebraMap (Om l) ℂ_[l]) hx
    rw [map_pow, map_one] at this
    exact this
  have hn : ‖(x : ℂ_[l])‖ ≤ 1 := by
    have h := congrArg norm hxC
    rw [norm_pow, norm_one] at h
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h).le
  obtain ⟨y, hyx⟩ : ∃ y : Per.OC l, (y : ℂ_[l]) = (x : ℂ_[l]) := ⟨⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩, rfl⟩
  have hy : y ^ m = 1 := Subtype.ext (by push_cast; rw [hyx, hxC])
  have hc : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by
    refine ⟨l ^ (m.totient - 1), ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient hc
  have hstep : ∀ z : Per.OC l, z ^ m = 1 → (z ^ a) ^ l = z := fun z hz => by
    rw [← pow_mul]
    simpa using pow_eq_pow_of_modEq ha hz
  have hpm : ∀ n : ℕ, (y ^ a ^ n) ^ m = 1 := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  obtain ⟨e, he⟩ := h1 (fun n => y ^ a ^ n) (fun n => by
    show (y ^ a ^ (n + 1)) ^ l = y ^ a ^ n
    rw [pow_succ, pow_mul]
    exact hstep _ (hpm n))
  refine ⟨e, h2 _ fun n => by rw [h3, he, hpm], ?_⟩
  have h0 := he 0
  rw [pow_zero, pow_one] at h0
  rw [← hyx, ← h0]
  rfl

end GlobalTheory.MemLoc
