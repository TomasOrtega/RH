import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

/- English proof (translation)
Establish `h0 : (n : S) * (a - b) = 0` using `by rw [mul_sub, e, sub_self]`. Use `(mem_nonZeroDivisors_iff.mp (hS n hn)).1 _ h0` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.
-/
theorem natCast_mul_cancel {S : Type} [CommRing S] (hS : TF S) {n : ℕ} (hn : n ≠ 0) {a b : S}
    (e : (n : S) * a = (n : S) * b) : a = b := by
  have h0 : (n : S) * (a - b) = 0 := by rw [mul_sub, e, sub_self]
  have := (mem_nonZeroDivisors_iff.mp (hS n hn)).1 _ h0
  exact sub_eq_zero.mp this

/- English proof (translation)
Establish `ex : ∀ (k : ℕ) (x : S), ∃ y : S, (x ∈ I → (k.factorial : S) * y = x ^ k ∧ (k ≠ 0 → y ∈ I)) ∧ (x ∉ I → y = 0)`. Introduce `k x`. Distinguish the cases in `hx : x ∈ I`. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality.

Conclude with `⟨1, fun _ => ⟨by simp, fun h => absurd rfl h⟩, fun h => absurd hx h⟩`. Take `⟨y, hy, e⟩` from `hI x hx k hk`. Conclude with `⟨y, fun _ => ⟨e, fun _ => hy⟩, fun h => absurd hx h⟩`. Conclude with `⟨0, fun h => absurd h hx, fun _ => rfl⟩`. Use `choose d hd using ex`.

Establish `spec : ∀ (k : ℕ) {x : S}, x ∈ I → (k.factorial : S) * d k x = x ^ k` using `fun k x hx => ((hd k x).1 hx).1`. Establish `hmem : ∀ {k : ℕ} {x : S}, k ≠ 0 → x ∈ I → d k x ∈ I` using `fun {k x} hk hx => ((hd k x).1 hx).2 hk`. Establish `fne : ∀ k : ℕ, k.factorial ≠ 0` using `Nat.factorial_ne_zero`. Use `⟨{ dpow := d dpow_null := fun {n x} hx => (hd n x).2 hx dpow_zero := fun {x} hx => ?_ dpow_one := fun {x} hx => ?_ dpow_mem := fun {n x} hn hx => hmem hn hx dpow_add := fun {n x y} hx hy => ?_ dpow_mul := fun {n a x} hx => ?_ mul_dpow := fun {m n x} hx => ?_ dpow_comp := fun {m n …` and prove the remaining obligations. Use `spec 0 hx` as an intermediate fact.

Simplify using `using this`. Use `spec 1 hx` as an intermediate fact. Simplify using `using this`. Apply `natCast_mul_cancel hS (fne n)` to reduce the goal to its premises. Rewrite using `[spec n (I.add_mem hx hy), (Commute.all x y).add_pow', Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Take `⟨i, j⟩` from `p`. Establish `hij : i + j = n` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hp`. Substitute `hij` using the available equality. Establish `hf : (((i + j).factorial : ℕ) : S) = ((i + j).choose i : S) * (i.factorial : S) * (j.factorial : S)`.

Rewrite using `[← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only`. Rewrite using `[hf, nsmul_eq_mul, ← spec i hx, ← spec j hy]`.

Expand and normalize the polynomial expressions, which then agree. Apply `natCast_mul_cancel hS (fne n)` to reduce the goal to its premises. Rewrite using `[spec n (I.mul_mem_left a hx), mul_pow, ← spec n hx]`. Expand and normalize the polynomial expressions, which then agree. Apply `natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (fne n))` to reduce the goal to its premises.

Establish `hf : (((m + n).factorial : ℕ) : S) = ((m + n).choose m : S) * (m.factorial : S) * (n.factorial : S)`. Rewrite using `[← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ((m.factorial * n.factorial : ℕ) : S) * (d m x * d n x) = x ^ (m + n)`.

Use `push_cast`. Rewrite using `[pow_add, ← spec m hx, ← spec n hx]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ((m.factorial * n.factorial : ℕ) : S) * (((m + n).choose m : S) * d (m + n) x) = x ^ (m + n)`. Rewrite using `[← spec (m + n) hx, hf]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality.

Establish `h0` using `spec 0 (hmem hn hx)`. Establish `h1` using `spec 0 hx`. Simplify using `only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero] at h0 h1`. Simplify using `[h0, h1, Nat.uniformBell_zero_left]`. Apply `natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (pow_ne_zero m (fne n)))` to reduce the goal to its premises.

Establish `hdx : d n x ∈ I` using `hmem hn hx`. Establish `hb : ((Nat.uniformBell m n : ℕ) : S) * ((n.factorial : S) ^ m) * (m.factorial : S) = ((m * n).factorial : S)`. Rewrite using `[← Nat.uniformBell_mul_eq _ hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : ((m.factorial * n.factorial ^ m : ℕ) : S) * d m (d n x) = x ^ (m * n)`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ((m.factorial * n.factorial ^ m : ℕ) : S) * (((Nat.uniformBell m n : ℕ) : S) * d (m * n) x) = x ^ (m * n)`. Rewrite using `[← spec (m * n) hx, ← hb]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`. Introduce `k x y hx e`. Apply `natCast_mul_cancel hS (fne k)` to reduce the goal to its premises.

Simplify using `only [RingHom.id_apply]`. Rewrite using `[spec k hx, e]`.
-/
theorem exists_dividedPowers {S : Type} [CommRing S] (hS : TF S) (I : Ideal S) (hI : PdI I) :
    ∃ δ : DividedPowers I, IsPd (RingHom.id S) I δ := by
  classical
  have ex : ∀ (k : ℕ) (x : S), ∃ y : S,
      (x ∈ I → (k.factorial : S) * y = x ^ k ∧ (k ≠ 0 → y ∈ I)) ∧ (x ∉ I → y = 0) := by
    intro k x
    by_cases hx : x ∈ I
    · by_cases hk : k = 0
      · subst hk
        exact ⟨1, fun _ => ⟨by simp, fun h => absurd rfl h⟩, fun h => absurd hx h⟩
      · obtain ⟨y, hy, e⟩ := hI x hx k hk
        exact ⟨y, fun _ => ⟨e, fun _ => hy⟩, fun h => absurd hx h⟩
    · exact ⟨0, fun h => absurd h hx, fun _ => rfl⟩
  choose d hd using ex
  have spec : ∀ (k : ℕ) {x : S}, x ∈ I → (k.factorial : S) * d k x = x ^ k :=
    fun k x hx => ((hd k x).1 hx).1
  have hmem : ∀ {k : ℕ} {x : S}, k ≠ 0 → x ∈ I → d k x ∈ I :=
    fun {k x} hk hx => ((hd k x).1 hx).2 hk
  have fne : ∀ k : ℕ, k.factorial ≠ 0 := Nat.factorial_ne_zero
  refine ⟨{ dpow := d
            dpow_null := fun {n x} hx => (hd n x).2 hx
            dpow_zero := fun {x} hx => ?_
            dpow_one := fun {x} hx => ?_
            dpow_mem := fun {n x} hn hx => hmem hn hx
            dpow_add := fun {n x y} hx hy => ?_
            dpow_mul := fun {n a x} hx => ?_
            mul_dpow := fun {m n x} hx => ?_
            dpow_comp := fun {m n x} hn hx => ?_ }, (Ideal.map_id I).symm, ?_⟩
  · have := spec 0 hx
    simpa using this
  · have := spec 1 hx
    simpa using this
  · apply natCast_mul_cancel hS (fne n)
    rw [spec n (I.add_mem hx hy), (Commute.all x y).add_pow', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨i, j⟩ := p
    have hij : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst hij
    have hf : (((i + j).factorial : ℕ) : S)
        = ((i + j).choose i : S) * (i.factorial : S) * (j.factorial : S) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
      push_cast
      ring
    simp only
    rw [hf, nsmul_eq_mul, ← spec i hx, ← spec j hy]
    ring
  · apply natCast_mul_cancel hS (fne n)
    rw [spec n (I.mul_mem_left a hx), mul_pow, ← spec n hx]
    ring
  · apply natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (fne n))
    have hf : (((m + n).factorial : ℕ) : S)
        = ((m + n).choose m : S) * (m.factorial : S) * (n.factorial : S) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
      push_cast
      ring
    have h1 : ((m.factorial * n.factorial : ℕ) : S) * (d m x * d n x) = x ^ (m + n) := by
      push_cast
      rw [pow_add, ← spec m hx, ← spec n hx]
      ring
    have h2 : ((m.factorial * n.factorial : ℕ) : S) * (((m + n).choose m : S) * d (m + n) x)
        = x ^ (m + n) := by
      rw [← spec (m + n) hx, hf]
      push_cast
      ring
    rw [h1, h2]
  · by_cases hm : m = 0
    · subst hm
      have h0 := spec 0 (hmem hn hx)
      have h1 := spec 0 hx
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero] at h0 h1
      simp [h0, h1, Nat.uniformBell_zero_left]
    · apply natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (pow_ne_zero m (fne n)))
      have hdx : d n x ∈ I := hmem hn hx
      have hb : ((Nat.uniformBell m n : ℕ) : S) * ((n.factorial : S) ^ m) * (m.factorial : S)
          = ((m * n).factorial : S) := by
        rw [← Nat.uniformBell_mul_eq _ hn]
        push_cast
        ring
      have h1 : ((m.factorial * n.factorial ^ m : ℕ) : S) * d m (d n x) = x ^ (m * n) := by
        push_cast
        calc (m.factorial : S) * (n.factorial : S) ^ m * d m (d n x)
            = (n.factorial : S) ^ m * ((m.factorial : S) * d m (d n x)) := by ring
          _ = ((n.factorial : S) * d n x) ^ m := by rw [spec m hdx, mul_pow]
          _ = x ^ (m * n) := by rw [spec n hx, ← pow_mul, mul_comm]
      have h2 : ((m.factorial * n.factorial ^ m : ℕ) : S)
          * (((Nat.uniformBell m n : ℕ) : S) * d (m * n) x) = x ^ (m * n) := by
        rw [← spec (m * n) hx, ← hb]
        push_cast
        ring
      rw [h1, h2]
  · intro k x y hx e
    apply natCast_mul_cancel hS (fne k)
    simp only [RingHom.id_apply]
    rw [spec k hx, e]

end GlobalTheory.CompanionTheory.PdTF
