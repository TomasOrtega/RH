import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

/- English proof (translation)
Assemble the required witnesses or components as `⟨x.log, (WithZero.exp_log h).symm⟩`.
-/
theorem exists_eq_exp_of_ne {x : WithZero (Multiplicative ℤ)} (h : x ≠ 0) : ∃ m : ℤ, x = WithZero.exp m :=
  ⟨x.log, (WithZero.exp_log h).symm⟩

/- English proof (translation)
Distinguish the cases in `h : x = 0`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Take `⟨m, rfl⟩` from `exists_eq_exp_of_ne h`. Rewrite using `[← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exp_mul_le_exp_iff {x : WithZero (Multiplicative ℤ)} {s k : ℤ} :
    WithZero.exp s * x ≤ WithZero.exp k ↔ x ≤ WithZero.exp (k - s) := by
  by_cases h : x = 0
  · subst h; simp
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Substitute `h0` using the available equality. Conclude with `absurd zero_le h`. Take `⟨m, rfl⟩` from `exists_eq_exp_of_ne h0`. Rewrite `h`, the goal using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exp_succ_le_of_not_le {x : WithZero (Multiplicative ℤ)} {k : ℤ} (h : ¬ x ≤ WithZero.exp k) :
    WithZero.exp (k + 1) ≤ x := by
  by_cases h0 : x = 0
  · subst h0; exact absurd zero_le h
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h0
    rw [WithZero.exp_le_exp] at h ⊢
    omega

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Conclude with `⟨0, by simp [h0]⟩`. Take `⟨m, rfl⟩` from `exists_eq_exp_of_ne h0`. Conclude with `⟨(m - k₀).toNat, WithZero.exp_le_exp.2 (by omega)⟩`.
-/
theorem exists_le_exp_add (x : WithZero (Multiplicative ℤ)) (k₀ : ℤ) : ∃ e : ℕ, x ≤ WithZero.exp (k₀ + e) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h0
    exact ⟨(m - k₀).toNat, WithZero.exp_le_exp.2 (by omega)⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Rewrite using `[map_pow, hϖ, ← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem v_pow_unif {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, hϖ, ← WithZero.exp_nsmul]; congr 1; simp

/- English proof (translation)
Rewrite using `[map_zpow₀, hϖ, ← WithZero.exp_zsmul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem v_zpow_unif {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; congr 1; simp

/- English proof (translation)
Use `show Valued.v (ϖ ^ k * x) ≤ 1 ↔ _`. Rewrite using `[map_mul, v_pow_unif hϖ, ← WithZero.exp_zero, exp_mul_le_exp_iff]`. Simplify using the standard rewrite rules.
-/
theorem pow_mul_mem_intL_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) (x : L) :
    ϖ ^ k * x ∈ intL L ↔ Valued.v x ≤ WithZero.exp (k : ℤ) := by
  show Valued.v (ϖ ^ k * x) ≤ 1 ↔ _
  rw [map_mul, v_pow_unif hϖ, ← WithZero.exp_zero, exp_mul_le_exp_iff]
  simp

section Entries

variable {σ : L →+* L} {N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in

/- English proof (translation)
Take `⟨hmz, h00, hll, hmm⟩` from `hm`. Establish `hmz' : ∀ i j, blk N i ≠ blk N j → mat m i j = 0` using `hmz`. Establish `hu' : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j` using `hu`. Establish `m0m : ∀ j, mat m 0 (mid j) = 0` using `fun j => hmz' _ _ (by simp)`. Establish `m0l : mat m 0 (Fin.last (N + 1)) = 0` using `hmz' _ _ (by simp)`.

Establish `mm0 : ∀ i, mat m (mid i) 0 = 0` using `fun i => hmz' _ _ (by simp)`. Establish `mml : ∀ i, mat m (mid i) (Fin.last (N + 1)) = 0` using `fun i => hmz' _ _ (by simp)`. Establish `ml0 : mat m (Fin.last (N + 1)) 0 = 0` using `hmz' _ _ (by simp)`. Establish `mlm : ∀ j, mat m (Fin.last (N + 1)) (mid j) = 0` using `fun j => hmz' _ _ (by simp)`. Establish `u00 : mat u 0 0 = 1` using `by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]`.

Establish `um0 : ∀ i, mat u (mid i) 0 = 0` using `fun i => by`. Rewrite using `[hu' _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]`. Establish `ul0 : mat u (Fin.last (N + 1)) 0 = 0`. Rewrite using `[hu' _ _ (by simp), Matrix.one_apply_ne last_ne_zero]`. Establish `hu_mm : ∀ i j, mat u (mid i) (mid j) = if i = j then 1 else 0` using `fun i j => by`.

Rewrite using `[hu' _ _ (by simp), Matrix.one_apply]; simp [mid_injective.eq_iff]`. Establish `ulm : ∀ j, mat u (Fin.last (N + 1)) (mid j) = 0` using `fun j => by`. Rewrite using `[hu' _ _ (by simp), Matrix.one_apply_ne (fun h => mid_ne_last j h.symm)]`. Establish `ull : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1` using `by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]`. Simplify using `only [mat_mul, Matrix.mul_apply, sum_idx]`.

Apply the tactic sequence `refine ⟨?_, fun j => ?_, ?_, fun i => ?_, fun i j => ?_, fun i => ?_, ?_, fun j => ?_, ?_⟩ <;>`. Simplify using `[m0m, m0l, mm0, mml, ml0, mlm, u00, um0, ul0, hu_mm, ulm, ull, h00, hll, hmm, rowOf, colOf, cornerOf, Matrix.mulVec, dotProduct]`.
-/
theorem leviElt_mul_rad_entries {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m u : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m)
    (hu : u ∈ radQ σ N) :
    mat (m * u) 0 0 = ϖ ^ a ∧ (∀ j, mat (m * u) 0 (mid j) = ϖ ^ a * rowOf u j) ∧
    mat (m * u) 0 (Fin.last (N + 1)) = ϖ ^ a * cornerOf u ∧
    (∀ i, mat (m * u) (mid i) 0 = 0) ∧ (∀ i j, mat (m * u) (mid i) (mid j) = mat g₀ i j) ∧
    (∀ i, mat (m * u) (mid i) (Fin.last (N + 1)) = (mat g₀ *ᵥ colOf u) i) ∧
    mat (m * u) (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, mat (m * u) (Fin.last (N + 1)) (mid j) = 0) ∧
    mat (m * u) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) := by
  obtain ⟨hmz, h00, hll, hmm⟩ := hm
  have hmz' : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hmz
  have hu' : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  have m0m : ∀ j, mat m 0 (mid j) = 0 := fun j => hmz' _ _ (by simp)
  have m0l : mat m 0 (Fin.last (N + 1)) = 0 := hmz' _ _ (by simp)
  have mm0 : ∀ i, mat m (mid i) 0 = 0 := fun i => hmz' _ _ (by simp)
  have mml : ∀ i, mat m (mid i) (Fin.last (N + 1)) = 0 := fun i => hmz' _ _ (by simp)
  have ml0 : mat m (Fin.last (N + 1)) 0 = 0 := hmz' _ _ (by simp)
  have mlm : ∀ j, mat m (Fin.last (N + 1)) (mid j) = 0 := fun j => hmz' _ _ (by simp)
  have u00 : mat u 0 0 = 1 := by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]
  have um0 : ∀ i, mat u (mid i) 0 = 0 := fun i => by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  have ul0 : mat u (Fin.last (N + 1)) 0 = 0 := by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  have hu_mm : ∀ i j, mat u (mid i) (mid j) = if i = j then 1 else 0 := fun i j => by
    rw [hu' _ _ (by simp), Matrix.one_apply]; simp [mid_injective.eq_iff]
  have ulm : ∀ j, mat u (Fin.last (N + 1)) (mid j) = 0 := fun j => by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne (fun h => mid_ne_last j h.symm)]
  have ull : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]
  simp only [mat_mul, Matrix.mul_apply, sum_idx]
  refine ⟨?_, fun j => ?_, ?_, fun i => ?_, fun i j => ?_, fun i => ?_, ?_, fun j => ?_, ?_⟩ <;>
    simp [m0m, m0l, mm0, mml, ml0, mlm, u00, um0, ul0, hu_mm, ulm, ull, h00, hll, hmm, rowOf, colOf, cornerOf,
      Matrix.mulVec, dotProduct]

end Entries

/- English proof (translation)
Introduce `L _ _ ϖ σ q N hU a g₀ m hm U V C l hf hl u hu`. Establish `hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hU.2.2.2.1`. Take `⟨e00, e0m, e0l, em0, emm, eml, el0, elm, ell⟩` from `leviElt_mul_rad_entries hm hu`. Establish `hrb : ∀ j, rowOf u j = -σ (colOf u j.rev)` using `((hH L ϖ σ q N hU).1 u hu).1`. Set `Q : ℕ → Prop` to `fun e => ∀ j, Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)`.

Establish `hQD : ∀ e, Q e ↔ (∀ i, Valued.v (((C * V * mat g₀) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)) ∧ ∀ i, Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)` using `fun e => by`. Use `hD L ϖ σ q N hU g₀ U V C hf (rowOf u) (colOf u) (ϖ ^ (a.toNat + e)) hrb` as an intermediate fact. Simplify using `only [pow_mul_mem_intL_iff hϖ] at this`. Conclude with `this`. Establish `hQex : ∃ e, Q e` using `by choose f hf' using fun j => exists_le_exp_add (Valued.v ((rowOf u ᵥ* C) j)) (a.toNat : ℤ)`.

Take `⟨M, hM⟩` from `Finite.exists_le f`. Conclude with `⟨M, fun j => (hf' j).trans (WithZero.exp_le_exp.2 (by have := hM j; push_cast; omega))⟩`. Set `e` to `Nat.find hQex`. Establish `hQe : Q e` using `Nat.find_spec hQex`. Establish `hQmono : ∀ e', Q e' ↔ e ≤ e'` using `fun e' => ⟨fun h => Nat.find_min' hQex h, fun h j => (hQe j).trans (WithZero.exp_le_exp.2 (by push_cast; omega))⟩`.

Establish `hnQ : 0 < e → ¬ Q (e - 1)` using `fun he h => by have := (hQmono _).1 h; omega`. Establish `hsucc : 0 < e → ((a.toNat + (e - 1) : ℕ) : ℤ) + 1 = ((a.toNat + e : ℕ) : ℤ)` using `fun he => by omega`. Establish `hQsharp : 0 < e → ∃ j, Valued.v ((rowOf u ᵥ* C) j) = WithZero.exp ((a.toNat + e : ℕ) : ℤ)` using `fun he => by`. Take `⟨j, hj⟩` from `not_forall.1 (hnQ he)`. Use `⟨j, le_antisymm (hQe j) ?_⟩` and prove the remaining obligations.

Use `exp_succ_le_of_not_le hj` as an intermediate fact. Rewrite `this` using `[hsucc he]`. Then use the resulting hypothesis. Set `y : L` to `ϖ ^ (-((a.toNat + e : ℕ) : ℤ))`. Establish `hy : Valued.v y = WithZero.exp ((a.toNat + e : ℕ) : ℤ)` using `by rw [v_zpow_unif hϖ, neg_neg]`. Take `⟨h2, h3⟩` from `(hQD e).1 hQe`.

Establish `h4 : Valued.v y = WithZero.exp (a.toNat : ℤ) ∨ (∃ i, Valued.v y = Valued.v (((C * V * mat g₀) *ᵥ colOf u) i)) ∨ ∃ i, Valued.v y = Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i)`. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Use `left`. Rewrite using `[hy, he]`. Both sides reduce to the same expression.

Use `right`. Establish `hn` using `hnQ he`. Rewrite `hn` using `[hQD]`. Break down `not_and_or.1 hn with hn | hn` into its components or cases. Take `⟨i, hi⟩` from `not_forall.1 hn`.

Use `exp_succ_le_of_not_le hi` as an intermediate fact. Rewrite `this` using `[hsucc he]`. Conclude with `Or.inl ⟨i, by rw [hy]; exact le_antisymm this (h2 i)⟩`. Take `⟨i, hi⟩` from `not_forall.1 hn`. Use `exp_succ_le_of_not_le hi` as an intermediate fact.

Rewrite `this` using `[hsucc he]`. Conclude with `Or.inr ⟨i, by rw [hy]; exact le_antisymm this (h3 i)⟩`. Take `⟨P, ρ, hPdet, hρ0, hρm, hρl, hlat⟩` from `hS L ϖ N a (mat (m * u)) (mat g₀) U V C (rowOf u) (colOf u) (cornerOf u) y hϖ hf e00 e0m e0l em0 emm eml el0 elm ell (by rw [hy, WithZero.exp_le_exp]; push_cast; omega) (fun i => by rw [hy]; exact h2 i) (fun i => by rw [hy]; exact h3 i) h4`. Take `⟨c', hc'⟩ : ∃ c', c' = cornerOf u - rowOf u ⬝ᵥ ((C * V * mat g₀) *ᵥ colOf u)` from `⟨_, rfl⟩`. Rewrite `hρl` using `[← hc']`.

Establish `hPdet' : Valued.v P.det = WithZero.exp ((a.natAbs + l + e : ℕ) : ℤ)`. Rewrite using `[hPdet, hl, hy, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_add]`. Use `congr 1`. Simplify using `only [Nat.cast_add]`. Use linear arithmetic over natural numbers and integers.

Establish `hvm : ∀ j (k : ℤ), Valued.v (ρ (mid j)) ≤ WithZero.exp k ↔ Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp (k + a.toNat)` using `fun j k => by`. Rewrite using `[hρm, map_mul, v_pow_unif hϖ, exp_mul_le_exp_iff, sub_neg_eq_add]`. Establish `hvl : Valued.v (ρ (Fin.last (N + 1))) = WithZero.exp (-((2 * a.toNat + e : ℕ) : ℤ)) * Valued.v c'`. Rewrite using `[hρl, map_div₀, map_mul, v_pow_unif hϖ, hy, div_eq_mul_inv, ← WithZero.exp_neg, mul_comm, ← mul_assoc, ← WithZero.exp_add]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hvl' : ∀ k : ℤ, Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp k ↔ Valued.v c' ≤ WithZero.exp (k + ((2 * a.toNat + e : ℕ) : ℤ))` using `fun k => by`. Rewrite using `[hvl, exp_mul_le_exp_iff, sub_neg_eq_add]`. Set `R : ℕ → Prop` to `fun e₂ => e ≤ e₂ ∧ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp (e₂ : ℤ)`.

Establish `hRex : ∃ e₂, R e₂`. Take `⟨k, hk⟩` from `exists_le_exp_add (Valued.v (ρ (Fin.last (N + 1)))) (e : ℤ)`. Conclude with `⟨e + k, by omega, by rwa [Nat.cast_add]⟩`. Set `e₂` to `Nat.find hRex`. Establish `hRe₂ : R e₂` using `Nat.find_spec hRex`.

Establish `hbound : ∀ i, Valued.v (ρ i) ≤ WithZero.exp (e₂ : ℤ)` using `fun i => by`. Break down `idx_cases i with rfl | ⟨j, rfl⟩ | rfl` into its components or cases. Rewrite using `[hρ0, map_zero]`. Conclude with `zero_le`. Rewrite using `[hvm]`.

Conclude with `(hQe j).trans (WithZero.exp_le_exp.2 (by have := hRe₂.1; push_cast; omega))`. Conclude with `hRe₂.2`. Establish `hsharp : e₂ = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e₂ : ℤ)`. Distinguish the cases in `h : e₂ = e`. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases.

Use `left`. Use linear arithmetic over natural numbers and integers. Use `right`. Take `⟨j, hj⟩` from `hQsharp he`. Use `⟨mid j, ?_⟩` and prove the remaining obligations.

Rewrite using `[hρm, map_mul, v_pow_unif hϖ, hj, ← WithZero.exp_add, h]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `right`.

Establish `hlt : e < e₂` using `lt_of_le_of_ne hRe₂.1 (Ne.symm h)`. Establish `hn : ¬ R (e₂ - 1)` using `Nat.find_min hRex (by omega)`. Establish `hn' : ¬ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp ((e₂ - 1 : ℕ) : ℤ)` using `fun h' => hn ⟨by omega, h'⟩`. Use `⟨Fin.last (N + 1), le_antisymm hRe₂.2 ?_⟩` and prove the remaining obligations. Use `exp_succ_le_of_not_le hn'` as an intermediate fact.

Rewrite `this` using `[show ((e₂ - 1 : ℕ) : ℤ) + 1 = (e₂ : ℤ) by omega]`. Then use the resulting hypothesis. Establish `hLat` using `hA L (N + 2) P ((a.natAbs + l + e : ℕ) : ℤ) ρ e₂ hPdet' hbound hsharp`. Rewrite `hLat` using `[← hlat]`. Establish `hlen : len (mat (m * u)) = a.natAbs + l + e + e₂` using `(hasLen_of_latLen (k := a.natAbs + l + e + e₂) (by convert hLat using 1; push_cast; ring)).len_eq`. Rewrite using `[hlen]`.

Use `⟨by omega, fun j => ?_⟩` and prove the remaining obligations. Establish `hsm : Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u ↔ e ≤ j / 2 ∧ Valued.v c' ≤ WithZero.exp ((2 * a.toNat + j : ℕ) : ℤ)`. Unfold `Small`. Rewrite using `[← hc']`. Simplify using `only [pow_mul_mem_intL_iff hϖ]`.

Conclude with `and_congr (hQmono (j / 2)) Iff.rfl`. Rewrite using `[hsm]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `hRe₂.1`.

Use `⟨by omega, ?_⟩` and prove the remaining obligations. Use `((hvl' _).1 hRe₂.2).trans (WithZero.exp_le_exp.2 ?_)` and prove the remaining obligations. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨h1, h2⟩`.

Establish `hR : R (j - e)` using `⟨by omega, (hvl' _).2 (h2.trans_eq (by congr 1; push_cast; omega))⟩`. Use `Nat.find_min' hRex hR` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem pointwise_of_steps (hA : AddVec) (hD : Dual) (hS : SpanEq) (hH : Heis) : Pointwise := by
  intro L _ _ ϖ σ q N hU a g₀ m hm U V C l hf hl u hu
  classical
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨e00, e0m, e0l, em0, emm, eml, el0, elm, ell⟩ := leviElt_mul_rad_entries hm hu
  have hrb : ∀ j, rowOf u j = -σ (colOf u j.rev) := ((hH L ϖ σ q N hU).1 u hu).1

  let Q : ℕ → Prop := fun e => ∀ j, Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)
  have hQD : ∀ e, Q e ↔
      (∀ i, Valued.v (((C * V * mat g₀) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)) ∧
      ∀ i, Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun e => by
    have := hD L ϖ σ q N hU g₀ U V C hf (rowOf u) (colOf u) (ϖ ^ (a.toNat + e)) hrb
    simp only [pow_mul_mem_intL_iff hϖ] at this
    exact this
  have hQex : ∃ e, Q e := by
    choose f hf' using fun j => exists_le_exp_add (Valued.v ((rowOf u ᵥ* C) j)) (a.toNat : ℤ)
    obtain ⟨M, hM⟩ := Finite.exists_le f
    exact ⟨M, fun j => (hf' j).trans (WithZero.exp_le_exp.2 (by have := hM j; push_cast; omega))⟩
  let e := Nat.find hQex
  have hQe : Q e := Nat.find_spec hQex
  have hQmono : ∀ e', Q e' ↔ e ≤ e' := fun e' =>
    ⟨fun h => Nat.find_min' hQex h, fun h j => (hQe j).trans (WithZero.exp_le_exp.2 (by push_cast; omega))⟩
  have hnQ : 0 < e → ¬ Q (e - 1) := fun he h => by have := (hQmono _).1 h; omega
  have hsucc : 0 < e → ((a.toNat + (e - 1) : ℕ) : ℤ) + 1 = ((a.toNat + e : ℕ) : ℤ) := fun he => by omega
  have hQsharp : 0 < e → ∃ j, Valued.v ((rowOf u ᵥ* C) j) = WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun he => by
    obtain ⟨j, hj⟩ := not_forall.1 (hnQ he)
    refine ⟨j, le_antisymm (hQe j) ?_⟩
    have := exp_succ_le_of_not_le hj
    rwa [hsucc he] at this

  let y : L := ϖ ^ (-((a.toNat + e : ℕ) : ℤ))
  have hy : Valued.v y = WithZero.exp ((a.toNat + e : ℕ) : ℤ) := by rw [v_zpow_unif hϖ, neg_neg]
  obtain ⟨h2, h3⟩ := (hQD e).1 hQe
  have h4 : Valued.v y = WithZero.exp (a.toNat : ℤ) ∨
      (∃ i, Valued.v y = Valued.v (((C * V * mat g₀) *ᵥ colOf u) i)) ∨
      ∃ i, Valued.v y = Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) := by
    rcases Nat.eq_zero_or_pos e with he | he
    · left; rw [hy, he]; rfl
    · right
      have hn := hnQ he
      rw [hQD] at hn
      rcases not_and_or.1 hn with hn | hn
      · obtain ⟨i, hi⟩ := not_forall.1 hn
        have := exp_succ_le_of_not_le hi
        rw [hsucc he] at this
        exact Or.inl ⟨i, by rw [hy]; exact le_antisymm this (h2 i)⟩
      · obtain ⟨i, hi⟩ := not_forall.1 hn
        have := exp_succ_le_of_not_le hi
        rw [hsucc he] at this
        exact Or.inr ⟨i, by rw [hy]; exact le_antisymm this (h3 i)⟩
  obtain ⟨P, ρ, hPdet, hρ0, hρm, hρl, hlat⟩ :=
    hS L ϖ N a (mat (m * u)) (mat g₀) U V C (rowOf u) (colOf u) (cornerOf u) y hϖ hf e00 e0m e0l em0 emm eml el0 elm
      ell (by rw [hy, WithZero.exp_le_exp]; push_cast; omega) (fun i => by rw [hy]; exact h2 i)
      (fun i => by rw [hy]; exact h3 i) h4
  obtain ⟨c', hc'⟩ : ∃ c', c' = cornerOf u - rowOf u ⬝ᵥ ((C * V * mat g₀) *ᵥ colOf u) := ⟨_, rfl⟩
  rw [← hc'] at hρl
  have hPdet' : Valued.v P.det = WithZero.exp ((a.natAbs + l + e : ℕ) : ℤ) := by
    rw [hPdet, hl, hy, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1; simp only [Nat.cast_add]; omega
  have hvm : ∀ j (k : ℤ), Valued.v (ρ (mid j)) ≤ WithZero.exp k ↔
      Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp (k + a.toNat) := fun j k => by
    rw [hρm, map_mul, v_pow_unif hϖ, exp_mul_le_exp_iff, sub_neg_eq_add]
  have hvl : Valued.v (ρ (Fin.last (N + 1))) = WithZero.exp (-((2 * a.toNat + e : ℕ) : ℤ)) * Valued.v c' := by
    rw [hρl, map_div₀, map_mul, v_pow_unif hϖ, hy, div_eq_mul_inv, ← WithZero.exp_neg, mul_comm, ← mul_assoc,
      ← WithZero.exp_add]
    congr 2; push_cast; ring
  have hvl' : ∀ k : ℤ, Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp k ↔
      Valued.v c' ≤ WithZero.exp (k + ((2 * a.toNat + e : ℕ) : ℤ)) := fun k => by
    rw [hvl, exp_mul_le_exp_iff, sub_neg_eq_add]

  let R : ℕ → Prop := fun e₂ => e ≤ e₂ ∧ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp (e₂ : ℤ)
  have hRex : ∃ e₂, R e₂ := by
    obtain ⟨k, hk⟩ := exists_le_exp_add (Valued.v (ρ (Fin.last (N + 1)))) (e : ℤ)
    exact ⟨e + k, by omega, by rwa [Nat.cast_add]⟩
  let e₂ := Nat.find hRex
  have hRe₂ : R e₂ := Nat.find_spec hRex
  have hbound : ∀ i, Valued.v (ρ i) ≤ WithZero.exp (e₂ : ℤ) := fun i => by
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · rw [hρ0, map_zero]; exact zero_le
    · rw [hvm]
      exact (hQe j).trans (WithZero.exp_le_exp.2 (by have := hRe₂.1; push_cast; omega))
    · exact hRe₂.2
  have hsharp : e₂ = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e₂ : ℤ) := by
    by_cases h : e₂ = e
    · rcases Nat.eq_zero_or_pos e with he | he
      · left; omega
      · right
        obtain ⟨j, hj⟩ := hQsharp he
        refine ⟨mid j, ?_⟩
        rw [hρm, map_mul, v_pow_unif hϖ, hj, ← WithZero.exp_add, h]
        congr 1; push_cast; ring
    · right
      have hlt : e < e₂ := lt_of_le_of_ne hRe₂.1 (Ne.symm h)
      have hn : ¬ R (e₂ - 1) := Nat.find_min hRex (by omega)
      have hn' : ¬ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp ((e₂ - 1 : ℕ) : ℤ) := fun h' =>
        hn ⟨by omega, h'⟩
      refine ⟨Fin.last (N + 1), le_antisymm hRe₂.2 ?_⟩
      have := exp_succ_le_of_not_le hn'
      rwa [show ((e₂ - 1 : ℕ) : ℤ) + 1 = (e₂ : ℤ) by omega] at this
  have hLat := hA L (N + 2) P ((a.natAbs + l + e : ℕ) : ℤ) ρ e₂ hPdet' hbound hsharp
  rw [← hlat] at hLat
  have hlen : len (mat (m * u)) = a.natAbs + l + e + e₂ :=
    (hasLen_of_latLen (k := a.natAbs + l + e + e₂) (by convert hLat using 1; push_cast; ring)).len_eq
  rw [hlen]
  refine ⟨by omega, fun j => ?_⟩
  have hsm : Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u ↔
      e ≤ j / 2 ∧ Valued.v c' ≤ WithZero.exp ((2 * a.toNat + j : ℕ) : ℤ) := by
    unfold Small
    rw [← hc']
    simp only [pow_mul_mem_intL_iff hϖ]
    exact and_congr (hQmono (j / 2)) Iff.rfl
  rw [hsm]
  constructor
  · intro h
    have h1 := hRe₂.1
    refine ⟨by omega, ?_⟩
    refine ((hvl' _).1 hRe₂.2).trans (WithZero.exp_le_exp.2 ?_)
    push_cast; omega
  · rintro ⟨h1, h2⟩
    have hR : R (j - e) := ⟨by omega, (hvl' _).2 (h2.trans_eq (by congr 1; push_cast; omega))⟩
    have := Nat.find_min' hRex hR
    omega

/- English proof (translation)
The claim follows from `pointwise_of_steps`.
-/
example : AddVec → Dual → SpanEq → Heis → Pointwise := pointwise_of_steps

end GlobalTheory.InertZeta
