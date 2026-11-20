import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete

namespace GlobalTheory.AwayNorm

variable {R N : Type} [CommRing R] [CommRing N] [Algebra R N]

def Dv (R : Type) [CommRing R] [Algebra R N] (u : Nˣ) (x : N) (r : ℤ) : Prop :=
  ∃ y : R, x = ((u ^ r : Nˣ) : N) * algebraMap R N y

variable {R N : Type} [CommRing R] [CommRing N] [Algebra R N] in

/- English proof (translation)
Introduce `p R _ hp hR`. Take `⟨htf, hsep, hcomp⟩` from `hR`. Set `L` to `Localization.Away (p : R)`. Establish `hunit : IsUnit (algebraMap R L (p : R))` using `IsLocalization.Away.algebraMap_isUnit (p : R)`. Use `set u : Lˣ := hunit.unit with hu`.

Establish `hu' : (u : L) = (p : L)` using `by rw [hu, IsUnit.unit_spec, map_natCast]`. Establish `hp0 : (0 : ℝ) < (p : ℝ)⁻¹`. Establish `: (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Check the signs of the components of the expression. Establish `hp1 : (p : ℝ)⁻¹ < 1`.

Establish `: (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Conclude with `inv_lt_one_of_one_lt₀ (by linarith)`. Establish `hpne : (p : ℝ)⁻¹ ≠ 0` using `hp0.ne'`. Establish `hpn : ∀ n : ℕ, ∀ x : R, (p : R) ^ n * x = 0 → x = 0`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro x hx`. Simplify using `using hx`. Consider the case `succ n ih`. Introduce `x hx`.

Apply `ih` to reduce the goal to its premises. Apply `htf` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← pow_succ']`. Conclude with `hx`. Establish `hinj : Function.Injective (algebraMap R L)`.

Use `IsLocalization.injective L (M := Submonoid.powers (p : R)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`. Rewrite using `[mem_nonZeroDivisors_iff]`. Conclude with `⟨fun x hx => hpn n x hx, fun x hx => hpn n x (by rw [mul_comm]; exact hx)⟩`. Take `⟨D, hD⟩ : ∃ D : L → ℤ → Prop, ∀ x r, D x r ↔ ∃ y : R, x = ((u ^ r : Lˣ) : L) * algebraMap R L y` from `⟨_, fun _ _ => Iff.rfl⟩`.

Establish `hDnat : ∀ (x : L) (n : ℕ), D x n ↔ ∃ y : R, x = (p : L) ^ n * algebraMap R L y`. Introduce `x n`. Rewrite using `[hD, zpow_natCast, Units.val_pow_eq_pow_val, hu']`. Establish `hmono : ∀ x r s, s ≤ r → D x r → D x s`. Introduce `x r s hsr hx`.

Take `⟨n, rfl⟩ : ∃ n : ℕ, r = s + n` from `⟨(r - s).toNat, by omega⟩`. Rewrite `hx`, the goal using `[hD]`. Take `⟨y, rfl⟩` from `hx`. Use `⟨(p : R) ^ n * y, ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, hu', map_mul, map_pow, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hadd : ∀ x y r, D x r → D y r → D (x + y) r`. Introduce `x y r hx hy`. Rewrite `hx`, `hy`, the goal using `[hD]`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, by rw [map_add, mul_add]⟩`. Establish `hneg : ∀ x r, D x r → D (-x) r`. Introduce `x r hx`. Rewrite `hx`, the goal using `[hD]`.

Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨-a, by rw [map_neg, mul_neg]⟩`. Establish `hmul : ∀ x y r s, D x r → D y s → D (x * y) (r + s)`. Introduce `x y r s hx hy`. Rewrite `hx`, `hy`, the goal using `[hD]`.

Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a * b, by rw [zpow_add, Units.val_mul, map_mul]; ring⟩`. Establish `hup : ∀ x r, D x r → D ((p : L) * x) (r + 1)`. Introduce `x r hx`.

Rewrite `hx`, the goal using `[hD]`. Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨a, by rw [zpow_add_one, Units.val_mul, hu']; ring⟩`. Establish `hdown : ∀ x r, D ((p : L) * x) r → D x (r - 1)`. Introduce `x r hx`.

Take `⟨s, rfl⟩ : ∃ s, r = s + 1` from `⟨r - 1, by ring⟩`. Rewrite using `[add_sub_cancel_right]`. Rewrite `hx`, the goal using `[hD]`. Take `⟨a, ha⟩` from `hx`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `hpu : IsUnit (p : L)` using `hu' ▸ u.isUnit`. Apply `hpu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[ha, zpow_add_one, Units.val_mul, hu']`. Expand and normalize the polynomial expressions, which then agree. Establish `hex : ∀ x : L, ∃ r, D x r`.

Introduce `x`. Take `⟨z, hz⟩` from `IsLocalization.surj (Submonoid.powers (p : R)) x`. Take `⟨n, hn⟩` from `z.2.2`. Use `⟨-(n : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[hD]`.

Use `⟨z.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← hn, map_pow, map_natCast, ← hu', zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, mul_comm x, Units.inv_mul_cancel_left]`. Establish `hzero : ∀ r, D 0 r` using `fun r => (hD 0 r).2 ⟨0, by simp⟩`. Establish `hsepL : ∀ x : L, (∀ n : ℕ, D x n) → x = 0`. Introduce `x hx`.

Take `⟨y0, hy0⟩` from `(hDnat x 0).1 (hx 0)`. Rewrite `hy0` using `[pow_zero, one_mul]`. Establish `hy : y0 = 0`. Apply `hsep` to reduce the goal to its premises. Introduce `k`.

Take `⟨yk, hyk⟩` from `(hDnat x k).1 (hx k)`. Use `⟨yk, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← hy0, hyk, map_mul, map_pow, map_natCast]`. Rewrite using `[hy0, hy, map_zero]`. Set `nrm : L → ℝ` to `fun x => ⨅ r : {r : ℤ // D x r}, (p : ℝ)⁻¹ ^ (r : ℤ)`.

Establish `hne : ∀ x, Nonempty {r : ℤ // D x r}` using `fun x =>`. Set `⟨r, hr⟩` to `hex x`. Use the proof step `⟨⟨r, hr⟩⟩`. Establish `hbdd : ∀ x, BddBelow (Set.range fun r : {r : ℤ // D x r} => (p : ℝ)⁻¹ ^ (r : ℤ))` using `fun x => ⟨0, by rintro _ ⟨r, rfl⟩; positivity⟩`. Establish `hle1 : ∀ x r, D x r → nrm x ≤ (p : ℝ)⁻¹ ^ r` using `fun x r h => ciInf_le (hbdd x) ⟨r, h⟩`.

Establish `hge1 : ∀ x (c : ℝ), (∀ r, D x r → c ≤ (p : ℝ)⁻¹ ^ r) → c ≤ nrm x`. Introduce `x c h`. Use `haveI := hne x`. Conclude with `le_ciInf fun r => h r.1 r.2`. Establish `hnn : ∀ x, 0 ≤ nrm x` using `fun x => hge1 x 0 fun r _ => by positivity`.

Establish `hlow : ∀ x r, ¬ D x r → (p : ℝ)⁻¹ ^ (r - 1) ≤ nrm x`. Introduce `x r hr`. Use `hge1 x _ fun s hs => ?_` and prove the remaining obligations. Establish `hsr : s ≤ r - 1`. Assume the negation of the conclusion as `h`.

Conclude with `hr (hmono x s r (by omega) hs)`. Conclude with `zpow_le_zpow_right_of_le_one₀ hp0 hp1.le hsr`. Establish `hchar : ∀ x r, nrm x ≤ (p : ℝ)⁻¹ ^ r ↔ D x r`. Introduce `x r`. Use `⟨fun h => ?_, hle1 x r⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hr`. Establish `h1` using `hlow x r hr`. Establish `h2 : (p : ℝ)⁻¹ ^ r < (p : ℝ)⁻¹ ^ (r - 1)` using `zpow_lt_zpow_right_of_lt_one₀ hp0 hp1 (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnz : nrm 0 = 0`.

Use `le_antisymm ?_ (hnn 0)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one h hp1`. Use `hle1 0 n (hzero n)` as an intermediate fact.

Rewrite `this` using `[zpow_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnorm_mono : ∀ x y, (∀ r, D x r → D y r) → nrm y ≤ nrm x` using `fun x y h => hge1 x _ fun r hr => hle1 y r (h r hr)`. Establish `hnneg : ∀ x, nrm (-x) = nrm x` using `fun x => le_antisymm (hnorm_mono _ _ fun r hr => hneg x r hr) (hnorm_mono _ _ fun r hr => by have := hneg (-x) r hr; rwa [neg_neg] at this)`. Establish `hnadd : ∀ x y, nrm (x + y) ≤ nrm x + nrm y`.

Introduce `x y`. Establish `key : ∀ r s, D x r → D y s → nrm (x + y) ≤ (p : ℝ)⁻¹ ^ r + (p : ℝ)⁻¹ ^ s`. Introduce `r s hr hs`. Establish `hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ r` using `by positivity`. Establish `hs0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ s` using `by positivity`.

Break down `le_total r s with h | h` into its components or cases. Use `hle1 _ _ (hadd x y r hr (hmono y s r h hs))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `hle1 _ _ (hadd x y s (hmono x r s h hr) hs)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : ∀ s, D y s → nrm (x + y) - (p : ℝ)⁻¹ ^ s ≤ nrm x` using `fun s hs => hge1 x _ fun r hr => by have := key r s hr hs; linarith`. Establish `h2 : nrm (x + y) - nrm x ≤ nrm y` using `hge1 y _ fun s hs => by have := h1 s hs; linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnmul : ∀ x y, nrm (x * y) ≤ nrm x * nrm y`. Introduce `x y`.

Establish `key : ∀ r s, D x r → D y s → nrm (x * y) ≤ (p : ℝ)⁻¹ ^ r * (p : ℝ)⁻¹ ^ s`. Introduce `r s hr hs`. Rewrite using `[← zpow_add₀ hpne]`. Conclude with `hle1 _ _ (hmul x y r s hr hs)`. Establish `h1 : ∀ s, D y s → nrm (x * y) ≤ nrm x * (p : ℝ)⁻¹ ^ s`.

Introduce `s hs`. Establish `hq : (0 : ℝ) < (p : ℝ)⁻¹ ^ s` using `by positivity`. Rewrite using `[← div_le_iff₀ hq]`. Conclude with `hge1 x _ fun r hr => by rw [div_le_iff₀ hq]; exact key r s hr hs`. Break down `(hnn x).eq_or_lt with h0 | h0` into its components or cases.

Take `⟨s, hs⟩` from `hex y`. Use `h1 s hs` as an intermediate fact. Rewrite `this` using `[← h0, zero_mul]`. Rewrite using `[← h0, zero_mul]`. Conclude with `this`.

Rewrite using `[← div_le_iff₀' h0]`. Conclude with `hge1 y _ fun s hs => by rw [div_le_iff₀' h0]; exact h1 s hs`. Establish `hnpos : ∀ x, nrm x = 0 → x = 0` using `fun x h => hsepL x fun n => (hchar x n).1 (by rw [h]; positivity)`. Set `f : RingNorm L` to `{ toFun := nrm map_zero' := hnz add_le' := hnadd neg' := hnneg mul_le' := hnmul eq_zero_of_map_eq_zero' := hnpos }`. Use `letI inst : NormedCommRing L := { f.toNormedRing with mul_comm := mul_comm }`.

Establish `hnorm : ∀ x : L, ‖x‖ = nrm x` using `fun _ => rfl`. Establish `hcharN : ∀ (x : L) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : R, x = (p : L) ^ r * algebraMap R L y`. Introduce `x r`. Rewrite using `[hnorm, ← zpow_natCast, hchar, hDnat]`. Establish `hcomplete : CompleteSpace L`.

Use `Metric.complete_of_convergent_controlled_sequences (fun n => (p : ℝ)⁻¹ ^ n) (fun n => pow_pos hp0 n) fun v hv => ?_` and prove the remaining obligations. Establish `hstep : ∀ k : ℕ, ∃ z : R, v (k + 1) - v k = (p : L) ^ (k + 1) * algebraMap R L z`. Introduce `k`. Rewrite using `[← hDnat]`. Assume the negation of the conclusion as `h`.

Establish `h1` using `hlow _ _ h`. Rewrite `h1` using `[Nat.cast_succ, add_sub_cancel_right, zpow_natCast]`. Establish `h2` using `hv k (k + 1) k (Nat.le_succ k) le_rfl`. Rewrite `h2` using `[dist_eq_norm, hnorm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `choose z hz using hstep`. Take `⟨s, hs⟩` from `hcomp z`. Use `choose r hr using hs`. Establish `htel : ∀ n, v n = v 0 + (p : L) * algebraMap R L (∑ i ∈ Finset.range n, (p : R) ^ i * z i)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ, map_add, mul_add, ← add_assoc, ← ih, map_mul, map_pow, map_natCast]`. Take the linear combination `hz n`.

Use `⟨v 0 + (p : L) * algebraMap R L s, Metric.tendsto_atTop.2 fun ε hε => ?_⟩` and prove the remaining obligations. Take `⟨M, hM⟩` from `exists_pow_lt_of_lt_one hε hp1`. Use `⟨M, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hdiff : v n - (v 0 + (p : L) * algebraMap R L s) = (p : L) ^ (n + 1) * algebraMap R L (-r n)`. Rewrite using `[htel n, map_neg]`.

Use `congrArg (algebraMap R L) (hr n)` as an intermediate fact. Rewrite `this` using `[map_sub, map_mul, map_pow, map_natCast]`. Take the linear combination `(-(p : L)) * this`. Establish `hb : ‖v n - (v 0 + (p : L) * algebraMap R L s)‖ ≤ (p : ℝ)⁻¹ ^ (n + 1)` using `(hcharN _ _).2 ⟨_, hdiff⟩`. Establish `hc : (p : ℝ)⁻¹ ^ (n + 1) ≤ (p : ℝ)⁻¹ ^ M` using `pow_le_pow_of_le_one hp0.le hp1.le (by omega)`.

Rewrite using `[dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨L, inst, hcomplete, inferInstance, inferInstance, hcharN, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hnorm, hnorm]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations.

Establish `h : nrm ((p : L) * x) / (p : ℝ)⁻¹ ≤ nrm x` using `hge1 x _ fun r hr => by`. Rewrite using `[div_le_iff₀ hp0, ← zpow_add_one₀ hpne]`. Conclude with `hle1 _ _ (hup x r hr)`. Rewrite `h` using `[div_le_iff₀ hp0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `hge1 _ _ fun r hr => ?_` and prove the remaining obligations. Establish `h` using `hle1 _ _ (hdown x r hr)`. Establish `e : (p : ℝ)⁻¹ ^ r = (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ (r - 1)`. Rewrite using `[mul_comm, ← zpow_add_one₀ hpne, sub_add_cancel]`. Rewrite using `[e]`.

Conclude with `mul_le_mul_of_nonneg_left h hp0.le`.
-/
theorem _root_.GlobalTheory.AwayNorm.exists_normed_away : ∀ (p : ℕ) (R : Type) [CommRing R],
    2 ≤ p →
    _root_.GlobalTheory.Decompl.LAdic.Good p R →
    ∃ (N : Type) (_ : NormedCommRing N) (_ : CompleteSpace N) (_ : Algebra R N),
      IsLocalization.Away (p : R) N ∧
      (∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : R, x = (p : N) ^ r * algebraMap R N y) ∧
      ∀ x : N, ‖(p : N) * x‖ = (p : ℝ)⁻¹ * ‖x‖ := by
  intro p R _ hp hR
  obtain ⟨htf, hsep, hcomp⟩ := hR
  let L := Localization.Away (p : R)
  have hunit : IsUnit (algebraMap R L (p : R)) := IsLocalization.Away.algebraMap_isUnit (p : R)
  set u : Lˣ := hunit.unit with hu
  have hu' : (u : L) = (p : L) := by rw [hu, IsUnit.unit_spec, map_natCast]
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hpne : (p : ℝ)⁻¹ ≠ 0 := hp0.ne'
  have hpn : ∀ n : ℕ, ∀ x : R, (p : R) ^ n * x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply ih
      apply htf
      rw [← mul_assoc, ← pow_succ']
      exact hx
  have hinj : Function.Injective (algebraMap R L) := by
    refine IsLocalization.injective L (M := Submonoid.powers (p : R)) ?_
    rintro _ ⟨n, rfl⟩
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x hx => hpn n x hx, fun x hx => hpn n x (by rw [mul_comm]; exact hx)⟩
  obtain ⟨D, hD⟩ : ∃ D : L → ℤ → Prop,
      ∀ x r, D x r ↔ ∃ y : R, x = ((u ^ r : Lˣ) : L) * algebraMap R L y :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hDnat : ∀ (x : L) (n : ℕ), D x n ↔ ∃ y : R, x = (p : L) ^ n * algebraMap R L y := by
    intro x n
    rw [hD, zpow_natCast, Units.val_pow_eq_pow_val, hu']
  have hmono : ∀ x r s, s ≤ r → D x r → D x s := by
    intro x r s hsr hx
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = s + n := ⟨(r - s).toNat, by omega⟩
    rw [hD] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(p : R) ^ n * y, ?_⟩
    rw [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, hu', map_mul, map_pow,
      map_natCast]
    ring
  have hadd : ∀ x y r, D x r → D y r → D (x + y) r := by
    intro x y r hx hy
    rw [hD] at hx hy ⊢
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by rw [map_add, mul_add]⟩
  have hneg : ∀ x r, D x r → D (-x) r := by
    intro x r hx
    rw [hD] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨-a, by rw [map_neg, mul_neg]⟩
  have hmul : ∀ x y r s, D x r → D y s → D (x * y) (r + s) := by
    intro x y r s hx hy
    rw [hD] at hx hy ⊢
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, by rw [zpow_add, Units.val_mul, map_mul]; ring⟩
  have hup : ∀ x r, D x r → D ((p : L) * x) (r + 1) := by
    intro x r hx
    rw [hD] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rw [zpow_add_one, Units.val_mul, hu']; ring⟩
  have hdown : ∀ x r, D ((p : L) * x) r → D x (r - 1) := by
    intro x r hx
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
    rw [add_sub_cancel_right]
    rw [hD] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    have hpu : IsUnit (p : L) := hu' ▸ u.isUnit
    apply hpu.mul_left_cancel
    rw [ha, zpow_add_one, Units.val_mul, hu']
    ring
  have hex : ∀ x : L, ∃ r, D x r := by
    intro x
    obtain ⟨z, hz⟩ := IsLocalization.surj (Submonoid.powers (p : R)) x
    obtain ⟨n, hn⟩ := z.2.2
    refine ⟨-(n : ℤ), ?_⟩
    rw [hD]
    refine ⟨z.1, ?_⟩
    rw [← hz, ← hn, map_pow, map_natCast, ← hu', zpow_neg, zpow_natCast,
      ← Units.val_pow_eq_pow_val, mul_comm x, Units.inv_mul_cancel_left]
  have hzero : ∀ r, D 0 r := fun r => (hD 0 r).2 ⟨0, by simp⟩
  have hsepL : ∀ x : L, (∀ n : ℕ, D x n) → x = 0 := by
    intro x hx
    obtain ⟨y0, hy0⟩ := (hDnat x 0).1 (hx 0)
    rw [pow_zero, one_mul] at hy0
    have hy : y0 = 0 := by
      apply hsep
      intro k
      obtain ⟨yk, hyk⟩ := (hDnat x k).1 (hx k)
      refine ⟨yk, hinj ?_⟩
      rw [← hy0, hyk, map_mul, map_pow, map_natCast]
    rw [hy0, hy, map_zero]

  let nrm : L → ℝ := fun x => ⨅ r : {r : ℤ // D x r}, (p : ℝ)⁻¹ ^ (r : ℤ)
  have hne : ∀ x, Nonempty {r : ℤ // D x r} := fun x =>
    let ⟨r, hr⟩ := hex x
    ⟨⟨r, hr⟩⟩
  have hbdd : ∀ x, BddBelow (Set.range fun r : {r : ℤ // D x r} => (p : ℝ)⁻¹ ^ (r : ℤ)) :=
    fun x => ⟨0, by rintro _ ⟨r, rfl⟩; positivity⟩
  have hle1 : ∀ x r, D x r → nrm x ≤ (p : ℝ)⁻¹ ^ r := fun x r h =>
    ciInf_le (hbdd x) ⟨r, h⟩
  have hge1 : ∀ x (c : ℝ), (∀ r, D x r → c ≤ (p : ℝ)⁻¹ ^ r) → c ≤ nrm x := by
    intro x c h
    haveI := hne x
    exact le_ciInf fun r => h r.1 r.2
  have hnn : ∀ x, 0 ≤ nrm x := fun x => hge1 x 0 fun r _ => by positivity
  have hlow : ∀ x r, ¬ D x r → (p : ℝ)⁻¹ ^ (r - 1) ≤ nrm x := by
    intro x r hr
    refine hge1 x _ fun s hs => ?_
    have hsr : s ≤ r - 1 := by
      by_contra h
      exact hr (hmono x s r (by omega) hs)
    exact zpow_le_zpow_right_of_le_one₀ hp0 hp1.le hsr
  have hchar : ∀ x r, nrm x ≤ (p : ℝ)⁻¹ ^ r ↔ D x r := by
    intro x r
    refine ⟨fun h => ?_, hle1 x r⟩
    by_contra hr
    have h1 := hlow x r hr
    have h2 : (p : ℝ)⁻¹ ^ r < (p : ℝ)⁻¹ ^ (r - 1) :=
      zpow_lt_zpow_right_of_lt_one₀ hp0 hp1 (by omega)
    linarith
  have hnz : nrm 0 = 0 := by
    refine le_antisymm ?_ (hnn 0)
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h hp1
    have := hle1 0 n (hzero n)
    rw [zpow_natCast] at this
    linarith
  have hnorm_mono : ∀ x y, (∀ r, D x r → D y r) → nrm y ≤ nrm x := fun x y h =>
    hge1 x _ fun r hr => hle1 y r (h r hr)
  have hnneg : ∀ x, nrm (-x) = nrm x := fun x =>
    le_antisymm (hnorm_mono _ _ fun r hr => hneg x r hr)
      (hnorm_mono _ _ fun r hr => by have := hneg (-x) r hr; rwa [neg_neg] at this)
  have hnadd : ∀ x y, nrm (x + y) ≤ nrm x + nrm y := by
    intro x y
    have key : ∀ r s, D x r → D y s →
        nrm (x + y) ≤ (p : ℝ)⁻¹ ^ r + (p : ℝ)⁻¹ ^ s := by
      intro r s hr hs
      have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ r := by positivity
      have hs0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ s := by positivity
      rcases le_total r s with h | h
      · have := hle1 _ _ (hadd x y r hr (hmono y s r h hs))
        linarith
      · have := hle1 _ _ (hadd x y s (hmono x r s h hr) hs)
        linarith
    have h1 : ∀ s, D y s → nrm (x + y) - (p : ℝ)⁻¹ ^ s ≤ nrm x := fun s hs =>
      hge1 x _ fun r hr => by have := key r s hr hs; linarith
    have h2 : nrm (x + y) - nrm x ≤ nrm y :=
      hge1 y _ fun s hs => by have := h1 s hs; linarith
    linarith
  have hnmul : ∀ x y, nrm (x * y) ≤ nrm x * nrm y := by
    intro x y
    have key : ∀ r s, D x r → D y s → nrm (x * y) ≤ (p : ℝ)⁻¹ ^ r * (p : ℝ)⁻¹ ^ s := by
      intro r s hr hs
      rw [← zpow_add₀ hpne]
      exact hle1 _ _ (hmul x y r s hr hs)
    have h1 : ∀ s, D y s → nrm (x * y) ≤ nrm x * (p : ℝ)⁻¹ ^ s := by
      intro s hs
      have hq : (0 : ℝ) < (p : ℝ)⁻¹ ^ s := by positivity
      rw [← div_le_iff₀ hq]
      exact hge1 x _ fun r hr => by rw [div_le_iff₀ hq]; exact key r s hr hs
    rcases (hnn x).eq_or_lt with h0 | h0
    · obtain ⟨s, hs⟩ := hex y
      have := h1 s hs
      rw [← h0, zero_mul] at this
      rw [← h0, zero_mul]
      exact this
    · rw [← div_le_iff₀' h0]
      exact hge1 y _ fun s hs => by rw [div_le_iff₀' h0]; exact h1 s hs
  have hnpos : ∀ x, nrm x = 0 → x = 0 := fun x h =>
    hsepL x fun n => (hchar x n).1 (by rw [h]; positivity)
  let f : RingNorm L :=
    { toFun := nrm
      map_zero' := hnz
      add_le' := hnadd
      neg' := hnneg
      mul_le' := hnmul
      eq_zero_of_map_eq_zero' := hnpos }
  letI inst : NormedCommRing L := { f.toNormedRing with mul_comm := mul_comm }
  have hnorm : ∀ x : L, ‖x‖ = nrm x := fun _ => rfl
  have hcharN : ∀ (x : L) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔
      ∃ y : R, x = (p : L) ^ r * algebraMap R L y := by
    intro x r
    rw [hnorm, ← zpow_natCast, hchar, hDnat]
  have hcomplete : CompleteSpace L := by
    refine Metric.complete_of_convergent_controlled_sequences (fun n => (p : ℝ)⁻¹ ^ n)
      (fun n => pow_pos hp0 n) fun v hv => ?_
    have hstep : ∀ k : ℕ, ∃ z : R, v (k + 1) - v k = (p : L) ^ (k + 1) * algebraMap R L z := by
      intro k
      rw [← hDnat]
      by_contra h
      have h1 := hlow _ _ h
      rw [Nat.cast_succ, add_sub_cancel_right, zpow_natCast] at h1
      have h2 := hv k (k + 1) k (Nat.le_succ k) le_rfl
      rw [dist_eq_norm, hnorm] at h2
      linarith
    choose z hz using hstep
    obtain ⟨s, hs⟩ := hcomp z
    choose r hr using hs
    have htel : ∀ n, v n = v 0 + (p : L) *
        algebraMap R L (∑ i ∈ Finset.range n, (p : R) ^ i * z i) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, map_add, mul_add, ← add_assoc, ← ih, map_mul, map_pow,
          map_natCast]
        linear_combination hz n
    refine ⟨v 0 + (p : L) * algebraMap R L s, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hp1
    refine ⟨M, fun n hn => ?_⟩
    have hdiff : v n - (v 0 + (p : L) * algebraMap R L s) =
        (p : L) ^ (n + 1) * algebraMap R L (-r n) := by
      rw [htel n, map_neg]
      have := congrArg (algebraMap R L) (hr n)
      rw [map_sub, map_mul, map_pow, map_natCast] at this
      linear_combination (-(p : L)) * this
    have hb : ‖v n - (v 0 + (p : L) * algebraMap R L s)‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) :=
      (hcharN _ _).2 ⟨_, hdiff⟩
    have hc : (p : ℝ)⁻¹ ^ (n + 1) ≤ (p : ℝ)⁻¹ ^ M :=
      pow_le_pow_of_le_one hp0.le hp1.le (by omega)
    rw [dist_eq_norm]
    linarith
  refine ⟨L, inst, hcomplete, inferInstance, inferInstance, hcharN, fun x => ?_⟩
  rw [hnorm, hnorm]
  refine le_antisymm ?_ ?_
  · have h : nrm ((p : L) * x) / (p : ℝ)⁻¹ ≤ nrm x :=
      hge1 x _ fun r hr => by
        rw [div_le_iff₀ hp0, ← zpow_add_one₀ hpne]
        exact hle1 _ _ (hup x r hr)
    rw [div_le_iff₀ hp0] at h
    linarith
  · refine hge1 _ _ fun r hr => ?_
    have h := hle1 _ _ (hdown x r hr)
    have e : (p : ℝ)⁻¹ ^ r = (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ (r - 1) := by
      rw [mul_comm, ← zpow_add_one₀ hpne, sub_add_cancel]
    rw [e]
    exact mul_le_mul_of_nonneg_left h hp0.le

end GlobalTheory.AwayNorm
