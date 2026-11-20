import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubProdLeSumOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpread

open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

/- English proof (translation)
Rewrite using `[show ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = _ from GlobalTheory.CompHt.map_vdm (Int.castRingHom ℝ) la]`. Unfold `GlobalTheory.CompHt.vdm`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `lhs : ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ((Int.castRingHom ℝ) (la τ i) - (Int.castRingHom ℝ) (la τ l)) = ∏ i ∈ Finset.range N, ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1)`. Rewrite using `[← Fin.prod_univ_eq_prod_range (fun i => ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1)) N]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Fin.prod_univ_eq_prod_range (fun l => if (i : ℕ) < l then v τ i - v τ l else 1) N, ← Finset.prod_filter]`. Use `Finset.prod_congr (by ext l; simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]) fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hv, hv]`. Both sides reduce to the same expression.

Establish `rhs : ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l) = ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range N, (if i < l then v τ i - v τ l else 1)`. Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `Finset.prod_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use `Finset.mem_range.1 hl` as an intermediate fact.

Use extensionality with `i`. Simplify using `only [Finset.mem_range, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce `h; exact ⟨by omega, h⟩`. Introduce `h`.

Conclude with `h.2`. Rewrite using `[lhs, rhs, Finset.prod_comm]`.
-/
theorem vdm_cast_eq_range {ι : Type} [Fintype ι] {N : ℕ} (la : ι → Fin N → ℤ) (v : ι → ℕ → ℝ)
    (hv : ∀ τ (i : Fin N), v τ i = la τ i) :
    ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l) := by
  rw [show ((GlobalTheory.CompHt.vdm la : ℤ) : ℝ) = _ from GlobalTheory.CompHt.map_vdm (Int.castRingHom ℝ) la]
  unfold GlobalTheory.CompHt.vdm
  refine Finset.prod_congr rfl fun τ _ => ?_
  have lhs : ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ((Int.castRingHom ℝ) (la τ i) - (Int.castRingHom ℝ) (la τ l))
      = ∏ i ∈ Finset.range N, ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ l ∈ Finset.range N, (if i < l then v τ i - v τ l else 1)) N]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun l => if (i : ℕ) < l then v τ i - v τ l else 1) N, ← Finset.prod_filter]
    refine Finset.prod_congr (by ext l; simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]) fun l _ => ?_
    rw [hv, hv]
    rfl
  have rhs : ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l)
      = ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range N, (if i < l then v τ i - v τ l else 1) := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    have := Finset.mem_range.1 hl
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  rw [lhs, rhs, Finset.prod_comm]

/- English proof (translation)
Introduce `ι _ N W H hW hd hanti hw hH1 hH2 hbar`. Establish `hk` using `hW.kc_pos`. Establish `hkp` using `hW.kc_lt`. Establish `hpN` using `hW.p_lt`. Establish `hc0 : (0 : ℝ) ≤ W.c0` using `by exact_mod_cast hW.weightConst_nonneg`.

Establish `hT1 : 4 * (W.Dd : ℝ) + 4 ≤ W.T` using `by exact_mod_cast hW.h1`. Establish `hD : (0 : ℝ) ≤ W.Dd` using `Nat.cast_nonneg _`. Establish `hT0 : (0 : ℝ) < W.T` using `by linarith`. Establish `hN0 : (0 : ℝ) < N`. Establish `: 0 < N` using `by omega`.

Conclude with `this` after adjusting the coercions. Take `⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1` from `⟨_, rfl⟩`. Rewrite using `[← hM]`. Establish `hM0 : 0 < M` using `by linarith`. Establish `hMT : M ≤ 5 / 4 * W.T` using `by linarith`.

Establish `hNT : 0 < (N : ℝ) * W.T` using `mul_pos hN0 hT0`. Establish `hHpos : 0 < H` using `by linarith`. Take `⟨g1, hg1⟩ : ∃ g1 : ℝ, g1 = H / (2 * M)` from `⟨_, rfl⟩`. Establish `hg : 3 * (N : ℝ) < g1`. Rewrite using `[hg1, lt_div_iff₀ (by positivity)]`.

Establish `: (N : ℝ) * M ≤ N * (5 / 4 * W.T)` using `mul_le_mul_of_nonneg_left hMT hN0.le`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨U, hU⟩ : ∃ U : ι → ℕ → ℝ, ∀ τ (i : Fin N), U τ i = W.u1 τ i` from `⟨fun τ n => if h : n < N then (W.u1 τ ⟨n, h⟩ : ℝ) else 0, fun τ i => by simp [i.2]⟩`. Establish `hU' : ∀ τ (i : Fin N), (if (i : ℕ) < W.p then U τ i else U τ i + 3 * N) = ((W.u' τ i : ℤ) : ℝ)`. Introduce `τ i`.

Rewrite using `[hU]`. Unfold `Wts.u'`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`. Take `⟨a, ha⟩ : ∃ a : Fin N, (a : ℕ) = W.p - 1` from `⟨⟨W.p - 1, by omega⟩, rfl⟩`. Take `⟨b, hb⟩ : ∃ b : Fin N, (b : ℕ) = W.p` from `⟨⟨W.p, hpN⟩, rfl⟩`.

Establish `hab : (b : ℕ) = a + 1` using `by omega`. Establish `hbarGap : ∀ τ, g1 ≤ (W.u1 τ a : ℝ) - W.u1 τ b`. Introduce `τ`. Establish `e` using `(hd τ).2 a b hab`. Rewrite `e` using `[if_pos hb]`.

Establish `hG` using `hbar τ a b hab hb`. Establish `hMi : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1` using `by positivity`. Establish `h3` using `Int.emod_lt_of_pos (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) hMi`. Establish `h4` using `Int.mul_ediv_add_emod (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) ((W.T : ℤ) + W.Dd + 1)`. Rewrite `h4` using `[← e]`.

Establish `h5 : W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2)) - ((W.T : ℤ) + W.Dd + 1) < ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b)` using `by linarith`. Establish `h6 : ((W.u τ a - W.u τ b : ℤ) : ℝ) - W.c0 - 2 * N + 2 - M < M * ((W.u1 τ a : ℝ) - W.u1 τ b)`. Rewrite using `[hM]`. Use `(Int.cast_lt (R := ℝ)).2 h5` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hg1, div_le_iff₀ (by positivity)]`. Establish `h7 : H ≤ 2 * (M * ((W.u1 τ a : ℝ) - W.u1 τ b))` using `by linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdec : ∀ τ i l, i < l → l < N → U τ l < U τ i`.

Introduce `τ i l h1 h2`. Use `hU τ ⟨i, by omega⟩` as an intermediate fact. Use `hU τ ⟨l, h2⟩` as an intermediate fact. Simplify using `only at *`. Establish `h` using `hanti τ (show (⟨i, by omega⟩ : Fin N) < ⟨l, h2⟩ from h1)`.

Establish `h' : (W.u1 τ ⟨l, h2⟩ : ℝ) < W.u1 τ ⟨i, by omega⟩` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgap : ∀ τ i l, i < W.p → W.p ≤ l → l < N → g1 ≤ U τ i - U τ l`. Introduce `τ i l h1 h2 h3`. Establish `e1` using `hU τ ⟨i, by omega⟩`.

Establish `e2` using `hU τ ⟨l, h3⟩`. Simplify using `only at e1 e2`. Rewrite using `[e1, e2]`. Establish `m1 : W.u1 τ a ≤ W.u1 τ ⟨i, by omega⟩` using `(hanti τ).antitone (show (⟨i, by omega⟩ : Fin N) ≤ a by`. Rewrite using `[Fin.le_def]`.

Simplify using `only`. Use the proof step `omega)`. Establish `m2 : W.u1 τ ⟨l, h3⟩ ≤ W.u1 τ b` using `(hanti τ).antitone (show b ≤ (⟨l, h3⟩ : Fin N) by`. Rewrite using `[Fin.le_def]`. Simplify using `only`.

Use the proof step `omega)`. Establish `m1' : (W.u1 τ a : ℝ) ≤ W.u1 τ ⟨i, by omega⟩` using `by exact_mod_cast m1`. Establish `m2' : (W.u1 τ ⟨l, h3⟩ : ℝ) ≤ W.u1 τ b` using `by exact_mod_cast m2`. Combine the linear relations using `[hbarGap τ]`. Establish `hcl : ∀ τ i l, i < W.kc → W.p ≤ l → l < N → W.w τ / (2 * W.T) ≤ U τ i - U τ l`.

Introduce `τ i l h1 h2 h3`. Establish `e1` using `hU τ ⟨i, by omega⟩`. Establish `e2` using `hU τ ⟨l, h3⟩`. Simplify using `only at e1 e2`. Rewrite using `[e1, e2]`.

Establish `c1` using `(GlobalTheory.MeanTop.divided_entries ι N W hW hd τ ⟨i, by omega⟩).2.2 h1`. Establish `c1' : (0 : ℝ) ≤ W.u1 τ ⟨i, by omega⟩` using `by exact_mod_cast c1`. Establish `c2` using `((GlobalTheory.MeanTop.nodes_far_and_spread ι N W hW hd τ).1 ⟨l, h3⟩ (by simp only; omega)).1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `L` using `GlobalTheory.degree_ratio_shift_bound ι N W.p W.kc U (fun _ => g1) W.w (W.T : ℝ) hkp.le hpN.le hT0 hw (fun _ => hg) hdec hgap hcl`.

Simplify using `only at L`. Take `⟨-, -, L3⟩` from `L`. Unfold `GlobalTheory.CompHt.rhoOf`. Rewrite using `[vdm_cast_eq_range W.u' (fun τ i => if i < W.p then U τ i else U τ i + 3 * N) (fun τ i => hU' τ i), vdm_cast_eq_range W.u1 U hU]`. Use `L3.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity))` and prove the remaining obligations.

Establish `hwt` using `hw τ`. Establish `e : ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) / g1 = ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) * (2 * M) / H`. Rewrite using `[hg1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Establish `i1 : ((W.p - W.kc : ℕ) : ℝ) ≤ N` using `by exact_mod_cast (show W.p - W.kc ≤ N by omega)`. Establish `i2 : ((N - W.p : ℕ) : ℝ) ≤ N` using `by exact_mod_cast (show N - W.p ≤ N by omega)`. Establish `i3 : (W.kc : ℝ) ≤ N` using `by exact_mod_cast (show W.kc ≤ N by omega)`. Use `gcongr`.
-/
theorem rho_div_le : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : GlobalTheory.MeanTop.Wts ι N) (H : ℝ), W.Hyp → W.IsDiv →
    (∀ τ, StrictAnti (W.u1 τ)) → (∀ τ, 0 < W.w τ) → 4 * ((W.c0 : ℝ) + 2 * N + W.T + W.Dd + 1) ≤ H →
    24 * (N : ℝ) * W.T ≤ H →
    (∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) = W.p → H ≤ ((W.u τ a - W.u τ b : ℤ) : ℝ)) →
    GlobalTheory.CompHt.rhoOf W.u' W.u1 ≤
      3 * N * ∑ τ, ((N : ℝ) * N * (2 * ((W.T : ℝ) + W.Dd + 1)) / H + 2 * N * N * W.T / W.w τ) := by
  intro ι _ N W H hW hd hanti hw hH1 hH2 hbar
  have hk := hW.kc_pos
  have hkp := hW.kc_lt
  have hpN := hW.p_lt
  have hc0 : (0 : ℝ) ≤ W.c0 := by exact_mod_cast hW.weightConst_nonneg
  have hT1 : 4 * (W.Dd : ℝ) + 4 ≤ W.T := by exact_mod_cast hW.h1
  have hD : (0 : ℝ) ≤ W.Dd := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < W.T := by linarith
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1 := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 < M := by linarith
  have hMT : M ≤ 5 / 4 * W.T := by linarith
  have hNT : 0 < (N : ℝ) * W.T := mul_pos hN0 hT0
  have hHpos : 0 < H := by linarith
  obtain ⟨g1, hg1⟩ : ∃ g1 : ℝ, g1 = H / (2 * M) := ⟨_, rfl⟩
  have hg : 3 * (N : ℝ) < g1 := by
    rw [hg1, lt_div_iff₀ (by positivity)]
    have : (N : ℝ) * M ≤ N * (5 / 4 * W.T) := mul_le_mul_of_nonneg_left hMT hN0.le
    nlinarith
  obtain ⟨U, hU⟩ : ∃ U : ι → ℕ → ℝ, ∀ τ (i : Fin N), U τ i = W.u1 τ i :=
    ⟨fun τ n => if h : n < N then (W.u1 τ ⟨n, h⟩ : ℝ) else 0, fun τ i => by simp [i.2]⟩
  have hU' : ∀ τ (i : Fin N), (if (i : ℕ) < W.p then U τ i else U τ i + 3 * N) = ((W.u' τ i : ℤ) : ℝ) := by
    intro τ i
    rw [hU]
    unfold Wts.u'
    split_ifs <;> push_cast <;> ring

  obtain ⟨a, ha⟩ : ∃ a : Fin N, (a : ℕ) = W.p - 1 := ⟨⟨W.p - 1, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin N, (b : ℕ) = W.p := ⟨⟨W.p, hpN⟩, rfl⟩
  have hab : (b : ℕ) = a + 1 := by omega
  have hbarGap : ∀ τ, g1 ≤ (W.u1 τ a : ℝ) - W.u1 τ b := by
    intro τ
    have e := (hd τ).2 a b hab
    rw [if_pos hb] at e
    have hG := hbar τ a b hab hb
    have hMi : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
    have h3 := Int.emod_lt_of_pos (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) hMi
    have h4 := Int.mul_ediv_add_emod (W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2))) ((W.T : ℤ) + W.Dd + 1)
    rw [← e] at h4
    have h5 : W.u τ a - W.u τ b + (-W.c0 - (2 * (N : ℤ) - 2)) - ((W.T : ℤ) + W.Dd + 1) <
        ((W.T : ℤ) + W.Dd + 1) * (W.u1 τ a - W.u1 τ b) := by linarith
    have h6 : ((W.u τ a - W.u τ b : ℤ) : ℝ) - W.c0 - 2 * N + 2 - M < M * ((W.u1 τ a : ℝ) - W.u1 τ b) := by
      rw [hM]
      have := (Int.cast_lt (R := ℝ)).2 h5
      push_cast at this ⊢
      linarith
    rw [hg1, div_le_iff₀ (by positivity)]
    have h7 : H ≤ 2 * (M * ((W.u1 τ a : ℝ) - W.u1 τ b)) := by linarith
    linarith
  have hdec : ∀ τ i l, i < l → l < N → U τ l < U τ i := by
    intro τ i l h1 h2
    have := hU τ ⟨i, by omega⟩
    have := hU τ ⟨l, h2⟩
    simp only at *
    have h := hanti τ (show (⟨i, by omega⟩ : Fin N) < ⟨l, h2⟩ from h1)
    have h' : (W.u1 τ ⟨l, h2⟩ : ℝ) < W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast h
    linarith
  have hgap : ∀ τ i l, i < W.p → W.p ≤ l → l < N → g1 ≤ U τ i - U τ l := by
    intro τ i l h1 h2 h3
    have e1 := hU τ ⟨i, by omega⟩
    have e2 := hU τ ⟨l, h3⟩
    simp only at e1 e2
    rw [e1, e2]
    have m1 : W.u1 τ a ≤ W.u1 τ ⟨i, by omega⟩ := (hanti τ).antitone (show (⟨i, by omega⟩ : Fin N) ≤ a by
      rw [Fin.le_def]; simp only; omega)
    have m2 : W.u1 τ ⟨l, h3⟩ ≤ W.u1 τ b := (hanti τ).antitone (show b ≤ (⟨l, h3⟩ : Fin N) by
      rw [Fin.le_def]; simp only; omega)
    have m1' : (W.u1 τ a : ℝ) ≤ W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast m1
    have m2' : (W.u1 τ ⟨l, h3⟩ : ℝ) ≤ W.u1 τ b := by exact_mod_cast m2
    linarith [hbarGap τ]
  have hcl : ∀ τ i l, i < W.kc → W.p ≤ l → l < N → W.w τ / (2 * W.T) ≤ U τ i - U τ l := by
    intro τ i l h1 h2 h3
    have e1 := hU τ ⟨i, by omega⟩
    have e2 := hU τ ⟨l, h3⟩
    simp only at e1 e2
    rw [e1, e2]
    have c1 := (GlobalTheory.MeanTop.divided_entries ι N W hW hd τ ⟨i, by omega⟩).2.2 h1
    have c1' : (0 : ℝ) ≤ W.u1 τ ⟨i, by omega⟩ := by exact_mod_cast c1
    have c2 := ((GlobalTheory.MeanTop.nodes_far_and_spread ι N W hW hd τ).1 ⟨l, h3⟩ (by simp only; omega)).1
    linarith
  have L := GlobalTheory.degree_ratio_shift_bound ι N W.p W.kc U (fun _ => g1) W.w (W.T : ℝ) hkp.le hpN.le hT0 hw
    (fun _ => hg) hdec hgap hcl
  dsimp only at L
  obtain ⟨-, -, L3⟩ := L
  unfold GlobalTheory.CompHt.rhoOf
  rw [vdm_cast_eq_range W.u' (fun τ i => if i < W.p then U τ i else U τ i + 3 * N) (fun τ i => hU' τ i),
    vdm_cast_eq_range W.u1 U hU]
  refine L3.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity))
  have hwt := hw τ
  have e : ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) / g1 = ((W.p - W.kc : ℕ) : ℝ) * ((N - W.p : ℕ) : ℝ) * (2 * M) / H := by
    rw [hg1]; field_simp
  rw [e]
  have i1 : ((W.p - W.kc : ℕ) : ℝ) ≤ N := by exact_mod_cast (show W.p - W.kc ≤ N by omega)
  have i2 : ((N - W.p : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N - W.p ≤ N by omega)
  have i3 : (W.kc : ℝ) ≤ N := by exact_mod_cast (show W.kc ≤ N by omega)
  gcongr

end GlobalTheory.MeanTop
