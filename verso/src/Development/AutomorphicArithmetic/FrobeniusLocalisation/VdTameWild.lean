import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.VdFormula
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LayerBot
import Development.AutomorphicArithmetic.FrobeniusLocalisation.CardImgOneDvd
import Development.AutomorphicArithmetic.FrobeniusLocalisation.MemRam

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Establish `h2 : (2 : ℝ) ≤ c` using `by exact_mod_cast h`. Use `one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem half_le {c : ℕ} (h : 2 ≤ c) : (1 : ℝ) / 2 ≤ 1 - 1 / (c : ℝ) := by
  have h2 : (2 : ℝ) ≤ c := by exact_mod_cast h
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2
  linarith

/- English proof (translation)
Establish `hc : (1 : ℝ) ≤ c` using `by exact_mod_cast h`. Establish `h1 : 1 / (c : ℝ) ≤ 1`. Rewrite using `[div_le_one (by linarith)]`. Conclude with `hc`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem term_nonneg {c : ℕ} (h : 0 < c) : (0 : ℝ) ≤ 1 - 1 / (c : ℝ) := by
  have hc : (1 : ℝ) ≤ c := by exact_mod_cast h
  have h1 : 1 / (c : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hc
  linarith

/- English proof (translation)
Introduce `φ H l hl`. Use `set v := H.condN.factorization l with hv`. Use `set e := (HostRaw.condE H.toHostRaw).factorization l with he`. Set `G : ℕ → Subgroup φ.GG` to `fun j => HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ j)`. Establish `hev : e ≤ v` using `(layer_bot H.toHostRaw (j := 0) hl (Nat.zero_le _)).2.2`.

Establish `hbot : ∀ j, j ≤ v → (G j = ⊥ ↔ e ≤ j)` using `fun j hj => (layer_bot H.toHostRaw hl hj).1`. Establish `hdvd : ∀ j, j ≤ e → Nat.card (G j) ∣ (l ^ e).totient / (l ^ j).totient` using `fun j hj => (layer_bot H.toHostRaw hl (hj.trans hev)).2.1 hj`. Establish `hcard_one : ∀ j, j ≤ v → (Nat.card (G j) = 1 ↔ e ≤ j)` using `fun j hj => Subgroup.card_eq_one.trans (hbot j hj)`. Establish `hpos : ∀ j, j ≤ v → 0 < Nat.card (G j)`. Introduce `j hjv`.

Distinguish the cases in `hje : j ≤ e`. Establish `h1 : (l ^ j).totient ∣ (l ^ e).totient` using `Nat.totient_dvd_of_dvd (pow_dvd_pow l hje)`. Establish `h2 : 0 < (l ^ j).totient` using `Nat.totient_pos.2 (pow_pos hl.pos _)`. Establish `h3 : 0 < (l ^ e).totient` using `Nat.totient_pos.2 (pow_pos hl.pos _)`. Conclude with `Nat.pos_of_dvd_of_pos (hdvd j hje) (Nat.div_pos (Nat.le_of_dvd h3 h1) h2)`.

Use `push_neg at hje`. Rewrite using `[(hcard_one j hjv).2 hje.le]`. Conclude with `Nat.one_pos`. Establish `hge : ∀ j, j < e → 2 ≤ Nat.card (G j)`. Introduce `j hj`.

Establish `hjv : j ≤ v` using `by omega`. Establish `h1` using `hpos j hjv`. Establish `h2 : Nat.card (G j) ≠ 1` using `fun h => by`. Use `(hcard_one j hjv).1 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hanti : 1 ≤ v → Nat.card (G 1) ∣ Nat.card (G 0)`. Introduce `h1v`. Apply `Subgroup.card_dvd_of_le` to reduce the goal to its premises. Apply `HostRaw.imgOne_anti _ (mul_dvd_mul_left _ (pow_dvd_pow l (by norm_num)))` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `hel : H.el l = Nat.card (G 0)` using `by show Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v)) = Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ 0))`. Rewrite using `[pow_zero, mul_one]`. Establish `hsum : H.vdH l = ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ))` using `vd_formula H hl`. Establish `hsl : H.sl l = max 1 e` using `rfl`.

Establish `key1 : ¬ l ∣ H.el l → e ≤ 1`. Introduce `hnd`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h1v : 1 ≤ v` using `by omega`.

Establish `hd` using `hdvd 1 hlt.le`. Rewrite `hd` using `[Nat.totient_prime_pow hl (by omega), pow_one, Nat.totient_prime hl, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hl.one_lt)]`. Take `⟨k, hk, hk'⟩` from `(Nat.dvd_prime_pow hl).1 hd`. Establish `hne : Nat.card (G 1) ≠ 1` using `fun h => by`. Use `(hcard_one 1 h1v).1 h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hne (by simpa using hk')`. Establish `hl1 : l ∣ Nat.card (G 1)` using `hk' ▸ dvd_pow_self l hk0`.

Conclude with `hnd (hel ▸ hl1.trans (hanti h1v))`. Establish `key2 : l ∣ H.el l → 2 ≤ e`. Introduce `hd`. Rewrite `hd` using `[hel]`. Assume the negation of the conclusion as `hlt`.

Establish `hcases : e = 0 ∨ e = 1` using `by omega`. Break down `hcases with h0 | h1` into its components or cases. Rewrite `hd` using `[(hcard_one 0 (Nat.zero_le _)).2 (by omega)]`. Conclude with `hl.not_dvd_one hd`. Establish `hd0` using `hdvd 0 (by omega)`.

Rewrite `hd0` using `[h1]`. Simplify using `[Nat.totient_prime hl] at hd0`. Use `Nat.le_of_dvd (Nat.sub_pos_of_lt hl.one_lt) (hd.trans hd0)` as an intermediate fact. Use `hl.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `⟨fun hnd => ?_, fun hd => ?_, fun hnd => ?_⟩` and prove the remaining obligations. Establish `he1` using `key1 hnd`. Rewrite using `[hsum, hel]`. Use `Finset.sum_eq_single 0 ?_ ?_` and prove the remaining obligations. Introduce `j hj hj0`.

Establish `hjv : j ≤ v` using `(Finset.mem_range.1 hj).le`. Rewrite using `[(hcard_one j hjv).2 (by omega)]`. Evaluate the numerical expressions. Introduce `h0`. Establish `hv0 : v = 0` using `by simpa using h0`.

Rewrite using `[(hcard_one 0 (Nat.zero_le _)).2 (by omega)]`. Evaluate the numerical expressions. Rewrite using `[hsum]`. Establish `h2e` using `key2 hd`. Establish `h2v : 2 ≤ v` using `h2e.trans hev`.

Establish `hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range v`. Introduce `x hx`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Simplify using `only [Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.

Establish `h01 : (0 : ℕ) ≠ 1` using `by norm_num`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsl]`. Conclude with `max_eq_left (key1 hnd)`.
-/
theorem UpperTheory.HF.vd_tame_wild :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → (¬ l ∣ H.el l → H.vdH l = 1 - 1 / (H.el l : ℝ)) ∧ (l ∣ H.el l → 1 ≤ H.vdH l) ∧ (¬ l ∣ H.el l → H.sl l = 1) := by
  intro φ H l hl
  set v := H.condN.factorization l with hv
  set e := (HostRaw.condE H.toHostRaw).factorization l with he
  let G : ℕ → Subgroup φ.GG := fun j => HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ j)
  have hev : e ≤ v := (layer_bot H.toHostRaw (j := 0) hl (Nat.zero_le _)).2.2
  have hbot : ∀ j, j ≤ v → (G j = ⊥ ↔ e ≤ j) := fun j hj => (layer_bot H.toHostRaw hl hj).1
  have hdvd : ∀ j, j ≤ e → Nat.card (G j) ∣ (l ^ e).totient / (l ^ j).totient :=
    fun j hj => (layer_bot H.toHostRaw hl (hj.trans hev)).2.1 hj
  have hcard_one : ∀ j, j ≤ v → (Nat.card (G j) = 1 ↔ e ≤ j) :=
    fun j hj => Subgroup.card_eq_one.trans (hbot j hj)
  have hpos : ∀ j, j ≤ v → 0 < Nat.card (G j) := by
    intro j hjv
    by_cases hje : j ≤ e
    · have h1 : (l ^ j).totient ∣ (l ^ e).totient := Nat.totient_dvd_of_dvd (pow_dvd_pow l hje)
      have h2 : 0 < (l ^ j).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
      have h3 : 0 < (l ^ e).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
      exact Nat.pos_of_dvd_of_pos (hdvd j hje) (Nat.div_pos (Nat.le_of_dvd h3 h1) h2)
    · push_neg at hje
      rw [(hcard_one j hjv).2 hje.le]
      exact Nat.one_pos
  have hge : ∀ j, j < e → 2 ≤ Nat.card (G j) := by
    intro j hj
    have hjv : j ≤ v := by omega
    have h1 := hpos j hjv
    have h2 : Nat.card (G j) ≠ 1 := fun h => by
      have := (hcard_one j hjv).1 h
      omega
    omega
  have hanti : 1 ≤ v → Nat.card (G 1) ∣ Nat.card (G 0) := by
    intro h1v
    apply Subgroup.card_dvd_of_le
    apply HostRaw.imgOne_anti _ (mul_dvd_mul_left _ (pow_dvd_pow l (by norm_num)))
    calc H.condN / l ^ v * l ^ 1 ∣ H.condN / l ^ v * l ^ v := mul_dvd_mul_left _ (pow_dvd_pow l h1v)
      _ = H.condN := Nat.div_mul_cancel (Nat.ordProj_dvd _ _)
  have hel : H.el l = Nat.card (G 0) := by
    show Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v)) =
      Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ 0))
    rw [pow_zero, mul_one]
  have hsum : H.vdH l = ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ)) := vd_formula H hl
  have hsl : H.sl l = max 1 e := rfl
  have key1 : ¬ l ∣ H.el l → e ≤ 1 := by
    intro hnd
    by_contra hlt
    push_neg at hlt
    have h1v : 1 ≤ v := by omega
    have hd := hdvd 1 hlt.le
    rw [Nat.totient_prime_pow hl (by omega), pow_one, Nat.totient_prime hl,
      Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hl.one_lt)] at hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hl).1 hd
    have hne : Nat.card (G 1) ≠ 1 := fun h => by
      have := (hcard_one 1 h1v).1 h
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hk')
    have hl1 : l ∣ Nat.card (G 1) := hk' ▸ dvd_pow_self l hk0
    exact hnd (hel ▸ hl1.trans (hanti h1v))
  have key2 : l ∣ H.el l → 2 ≤ e := by
    intro hd
    rw [hel] at hd
    by_contra hlt
    have hcases : e = 0 ∨ e = 1 := by omega
    rcases hcases with h0 | h1
    · rw [(hcard_one 0 (Nat.zero_le _)).2 (by omega)] at hd
      exact hl.not_dvd_one hd
    · have hd0 := hdvd 0 (by omega)
      rw [h1] at hd0
      simp [Nat.totient_prime hl] at hd0
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hl.one_lt) (hd.trans hd0)
      have := hl.two_le
      omega
  refine ⟨fun hnd => ?_, fun hd => ?_, fun hnd => ?_⟩
  · have he1 := key1 hnd
    rw [hsum, hel]
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro j hj hj0
      have hjv : j ≤ v := (Finset.mem_range.1 hj).le
      rw [(hcard_one j hjv).2 (by omega)]
      norm_num
    · intro h0
      have hv0 : v = 0 := by simpa using h0
      rw [(hcard_one 0 (Nat.zero_le _)).2 (by omega)]
      norm_num
  · rw [hsum]
    have h2e := key2 hd
    have h2v : 2 ≤ v := h2e.trans hev
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have h01 : (0 : ℕ) ≠ 1 := by norm_num
    calc (1 : ℝ) = 1 / 2 + 1 / 2 := by norm_num
      _ ≤ (1 - 1 / (Nat.card (G 0) : ℝ)) + (1 - 1 / (Nat.card (G 1) : ℝ)) :=
          add_le_add (half_le (hge 0 (by omega))) (half_le (hge 1 (by omega)))
      _ = ∑ j ∈ ({0, 1} : Finset ℕ), (1 - 1 / (Nat.card (G j) : ℝ)) :=
          (Finset.sum_pair (f := fun j => (1 - 1 / (Nat.card (G j) : ℝ))) h01).symm
      _ ≤ ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j hj _ => term_nonneg (hpos j (Finset.mem_range.1 hj).le))
  · rw [hsl]
    exact max_eq_left (key1 hnd)
