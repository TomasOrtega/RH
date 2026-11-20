import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.WtComb

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `a b hb`. Establish `: a = b` using `Fin.ext (by omega)`.

Substitute `this` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `a b hb`. Establish `hk : (a : ℕ) + k < n` using `by have := b.2; omega`.

Establish `h1` using `ih a ⟨(a : ℕ) + k, hk⟩ rfl`. Establish `h2 : e ⟨(a : ℕ) + k, hk⟩ < e b` using `e.lt_iff_lt.2 (by rw [Fin.lt_def]; simp; omega)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem orderEmb_add_le {n : ℕ} (e : Fin n ↪o ℤ) :
    ∀ (k : ℕ) (a b : Fin n), (b : ℕ) = (a : ℕ) + k → e a + (k : ℤ) ≤ e b := by
  intro k
  induction k with
  | zero =>
    intro a b hb
    have : a = b := Fin.ext (by omega)
    subst this; simp
  | succ k ih =>
    intro a b hb
    have hk : (a : ℕ) + k < n := by have := b.2; omega
    have h1 := ih a ⟨(a : ℕ) + k, hk⟩ rfl
    have h2 : e ⟨(a : ℕ) + k, hk⟩ < e b := e.lt_iff_lt.2 (by rw [Fin.lt_def]; simp; omega)
    push_cast; linarith

/- English proof (translation)
Use `set c : ℂ := ((n : ℂ) - 1) / 2 with hcdef`. Set `g : ℂ → ℤ` to `fun x => if h : ∃ z : ℤ, x = (z : ℂ) + c then h.choose else 0`. Establish `hg : ∀ x ∈ S, x = (g x : ℂ) + c` using `fun x hx => by`. Simplify using `only [g, dif_pos (hm x hx)]`. Conclude with `(hm x hx).choose_spec`.

Set `M : Multiset ℤ` to `S.map (fun x => -g x)`. Establish `hMd : M.Nodup` using `hd.map_on (fun x hx y hy hxy => by`. Rewrite using `[hg x hx, hg y hy]`. Simplify using `only [neg_inj] at hxy`. Rewrite using `[hxy])`.

Set `T : Finset ℤ` to `⟨M, hMd⟩`. Establish `hT : T.card = n` using `by simp [T, M, hc]`. Set `e` to `T.orderEmbOfFin hT`. Use `⟨⟨fun a => -e a + (a : ℕ), ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Use `orderEmb_add_le e ((b : ℕ) - (a : ℕ)) a b (by rw [Fin.le_def] at hab; omega)` as an intermediate fact. Use `show -e b + ((b : ℕ) : ℤ) ≤ -e a + ((a : ℕ) : ℤ)`. Rewrite `hab` using `[Fin.le_def]`. Move the coercions through the operations in `[Nat.cast_sub hab] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `NG.infOf`. Establish `h1 : (Finset.univ.map e.toEmbedding) = T` using `Finset.map_orderEmbOfFin_univ T hT`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Multiset.map_map]`. Use `Multiset.map_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp, hcdef]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ = T.val.map (fun y : ℤ => -(y : ℂ) + c) := by rw [← h1]; rfl`. Use `_ = S := by show M.map _ = S`.

Rewrite using `[Multiset.map_map]`. Use `conv_rhs => rw [← Multiset.map_id S]`. Use `Multiset.map_congr rfl fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, id]`. Establish `h` using `hg x hx`.

Use `push_cast`. Take the linear combination `-1 * h`.
-/
theorem exists_domWeight_infOf (n : ℕ) (S : Multiset ℂ) (hc : Multiset.card S = n) (hd : S.Nodup)
    (hm : ∀ x ∈ S, ∃ z : ℤ, x = (z : ℂ) + ((n : ℂ) - 1) / 2) :
    ∃ lam : DomWeight n, NG.infOf lam.w = S := by
  classical
  set c : ℂ := ((n : ℂ) - 1) / 2 with hcdef
  let g : ℂ → ℤ := fun x => if h : ∃ z : ℤ, x = (z : ℂ) + c then h.choose else 0
  have hg : ∀ x ∈ S, x = (g x : ℂ) + c := fun x hx => by
    simp only [g, dif_pos (hm x hx)]; exact (hm x hx).choose_spec
  let M : Multiset ℤ := S.map (fun x => -g x)
  have hMd : M.Nodup := hd.map_on (fun x hx y hy hxy => by
    rw [hg x hx, hg y hy]; simp only [neg_inj] at hxy; rw [hxy])
  let T : Finset ℤ := ⟨M, hMd⟩
  have hT : T.card = n := by simp [T, M, hc]
  let e := T.orderEmbOfFin hT
  refine ⟨⟨fun a => -e a + (a : ℕ), ?_⟩, ?_⟩
  · intro a b hab
    have := orderEmb_add_le e ((b : ℕ) - (a : ℕ)) a b (by rw [Fin.le_def] at hab; omega)
    show -e b + ((b : ℕ) : ℤ) ≤ -e a + ((a : ℕ) : ℤ)
    rw [Fin.le_def] at hab
    push_cast [Nat.cast_sub hab] at this
    linarith
  · unfold NG.infOf
    have h1 : (Finset.univ.map e.toEmbedding) = T := Finset.map_orderEmbOfFin_univ T hT
    calc (Finset.univ.val.map fun a : Fin n => ((-e a + ((a : ℕ) : ℤ) : ℤ) : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ))
        = (Finset.univ.val.map fun a : Fin n => e a).map (fun y : ℤ => -(y : ℂ) + c) := by
          rw [Multiset.map_map]
          refine Multiset.map_congr rfl fun a _ => ?_
          simp only [Function.comp, hcdef]; push_cast; ring
      _ = T.val.map (fun y : ℤ => -(y : ℂ) + c) := by rw [← h1]; rfl
      _ = S := by
          show M.map _ = S
          rw [Multiset.map_map]
          conv_rhs => rw [← Multiset.map_id S]
          refine Multiset.map_congr rfl fun x hx => ?_
          simp only [Function.comp, id]
          have h := hg x hx
          push_cast
          linear_combination -1 * h

end GlobalTheory.WtComb

namespace GlobalTheory.WtComb

/- English proof (translation)
Introduce `i i' h`. Proceed by induction on `i' with`. Consider the case `zero => omega`. Consider the case `succ i' ih`. Introduce `hN`.

Break down `Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'` into its components or cases. Conclude with `lt_trans (hs i' hN) (ih h' (by omega))`. Substitute `h'` using the available equality. Conclude with `hs i hN`.
-/
theorem chain_lt (f : ℕ → ℚ) (N : ℕ) (hs : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i i', i < i' → i' < N → f i' < f i := by
  intro i i' h
  induction i' with
  | zero => omega
  | succ i' ih =>
    intro hN
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact lt_trans (hs i' hN) (ih h' (by omega))
    · subst h'; exact hs i hN

/- English proof (translation)
Introduce `i i' h hN`. Break down `Nat.lt_or_eq_of_le h with h' | h'` into its components or cases. Conclude with `(chain_lt f N hs i i' h' hN).le`. Rewrite using `[h']`.
-/
theorem chain_le (f : ℕ → ℚ) (N : ℕ) (hs : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i i', i ≤ i' → i' < N → f i' ≤ f i := by
  intro i i' h hN
  rcases Nat.lt_or_eq_of_le h with h' | h'
  · exact (chain_lt f N hs i i' h' hN).le
  · rw [h']

def qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Finset.univ.val.map fun i : Fin (R.k - 1) => h.v i) + (Finset.univ.val.map fun i : Fin R.m => -h.b i) +
  ((Multiset.range R.t).map fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2)

/- English proof (translation)
Unfold `NG.paramV qv`. Simplify using `only [Multiset.map_add, Multiset.map_map]`. Use `congr 1`. Apply the tactic sequence `congr 1 all_goals refine Multiset.map_congr rfl fun i _ => ?_ all_goals simp only [Function.comp]`. Use `push_cast`.

Apply the tactic sequence `try ring`. Use `Multiset.map_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp]`. Use `push_cast`. Apply the tactic sequence `try ring`.
-/
theorem paramV_eq (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ) :
    NG.paramV R h j sh = (qv R h j).map (fun q : ℚ => (q : ℂ) - sh) := by
  unfold NG.paramV qv
  simp only [Multiset.map_add, Multiset.map_map]
  congr 1
  · congr 1
    all_goals refine Multiset.map_congr rfl fun i _ => ?_
    all_goals simp only [Function.comp]; push_cast; try ring
  · refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp]; push_cast; try ring

/- English proof (translation)
Use `R.m_add_three_le_k` as an intermediate fact. Simplify using `[qv, Ranks.nV, Ranks.r]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : Multiset.card (qv R h j) = R.nV := by
  have := R.m_add_three_le_k
  simp [qv, Ranks.nV, Ranks.r]
  omega

end GlobalTheory.WtComb

namespace GlobalTheory.WtComb

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hm2` using `R.two_le_m`. Establish `ht0 : (0 : ℚ) ≤ R.t` using `by positivity`. Set `U : ℕ → ℚ` to `fun i => if hi : i < R.k then h.u ⟨i, hi⟩ else 0`. Set `V : ℕ → ℚ` to `fun i => if hi : i < R.k - 1 then h.v ⟨i, hi⟩ else 0`.

Set `B : ℕ → ℚ` to `fun i => if hi : i < R.m then -h.b ⟨i, hi⟩ else 0`. Establish `hU : ∀ i, i + 1 < R.k → U (i + 1) < U i`. Introduce `i hi`. Establish `h1` using `h.u_gt_v ⟨i, by omega⟩`. Establish `h2` using `h.v_gt_u ⟨i, by omega⟩`.

Simplify using `only [U, dif_pos hi, dif_pos (show i < R.k by omega)]`. Conclude with `lt_trans h2 h1`. Establish `hV : ∀ i, i + 1 < R.k - 1 → V (i + 1) < V i`. Introduce `i hi`. Establish `h1` using `h.u_gt_v ⟨i + 1, hi⟩`.

Establish `h2` using `h.v_gt_u ⟨i, by omega⟩`. Simplify using `only [V, dif_pos hi, dif_pos (show i < R.k - 1 by omega)]`. Conclude with `lt_trans h1 h2`. Establish `hB : ∀ i, i + 1 < R.m → B (i + 1) < B i`. Introduce `i hi`.

Establish `h1` using `h.gap_be ⟨i, by omega⟩`. Establish `h2` using `h.gap_eb ⟨i, by omega⟩ hi`. Simplify using `only [B, dif_pos hi, dif_pos (show i < R.m by omega)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `bmono : ∀ i i' : Fin R.m, i.1 ≤ i'.1 → -h.b i' ≤ -h.b i`.

Introduce `i i' hii`. Use `chain_le B R.m hB i.1 i'.1 hii i'.2` as an intermediate fact. Simplify `this` using `only [B, dif_pos i.2, dif_pos i'.2]`. Establish `vgt : ∀ (i : Fin (R.k - 1)) (i' : Fin R.m), -h.b i' < h.v i`. Introduce `i i'`.

Establish `a1` using `h.v_gt_u i`. Establish `a2` using `chain_le U R.k hU (i.1 + 1) (R.k - 1) (by omega) (by omega)`. Establish `a3` using `h.u_last_gt (by omega) (by omega)`. Establish `a4` using `bmono ⟨0, by omega⟩ i' (Nat.zero_le _)`. Simplify using `only [U, dif_pos (show R.k - 1 < R.k by omega), dif_pos (show i.1 + 1 < R.k by omega)] at a2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `top : ∀ c : ℕ, -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 < -h.b j`. Introduce `c`. Use `h.gap_be j` as an intermediate fact. Establish `hc : (0 : ℚ) ≤ c` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `bne : ∀ (i : Fin R.m) (c : ℕ), c < R.t → -h.b i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2`. Introduce `i c hc`. Distinguish the cases in `hij : i.1 ≤ j.1`. Use `bmono i j hij` as an intermediate fact.

Use `top c` as an intermediate fact. Introduce `heq`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj1 : j.1 + 1 < R.m` using `by have := i.2; omega`. Establish `a1` using `h.gap_eb j hj1`.

Establish `a2` using `bmono ⟨j.1 + 1, hj1⟩ i (show j.1 + 1 ≤ i.1 by omega)`. Establish `hc' : (c : ℚ) + 1 ≤ R.t` using `by exact_mod_cast hc`. Introduce `heq`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `vne : ∀ (i : Fin (R.k - 1)) (c : ℕ), h.v i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2`.

Introduce `i c heq`. Use `vgt i j` as an intermediate fact. Use `top c` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `vinj : Function.Injective h.v`.

Use `StrictAnti.injective fun a b hab => ?_` and prove the remaining obligations. Use `chain_lt V (R.k - 1) hV a.1 b.1 hab b.2` as an intermediate fact. Simplify `this` using `only [V, dif_pos a.2, dif_pos b.2]`. Establish `binj : Function.Injective fun i : Fin R.m => -h.b i`. Use `StrictAnti.injective fun a b hab => ?_` and prove the remaining obligations.

Use `chain_lt B R.m hB a.1 b.1 hab b.2` as an intermediate fact. Simplify `this` using `only [B, dif_pos a.2, dif_pos b.2]`. Establish `rinj : Function.Injective fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2`. Introduce `c c' hcc`. Establish `: (c : ℚ) = c'` using `by simp only at hcc; linarith`.

Conclude with `this` after adjusting the coercions. Unfold `qv`. Use `Multiset.nodup_add.2 ⟨Multiset.nodup_add.2 ⟨Finset.univ.nodup.map vinj, Finset.univ.nodup.map binj, ?_⟩, (Multiset.nodup_range _).map rinj, ?_⟩` and prove the remaining obligations. Use `Multiset.disjoint_left.2 fun ha hb => ?_` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 ha`.

Take `⟨i', -, hi'⟩` from `Multiset.mem_map.1 hb`. Use `vgt i i'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Multiset.disjoint_left.2 fun ha hb => ?_` and prove the remaining obligations. Take `⟨c, hc, rfl⟩` from `Multiset.mem_map.1 hb`.

Rewrite `hc` using `[Multiset.mem_range]`. Break down `Multiset.mem_add.1 ha with ha | ha` into its components or cases. Take `⟨i, -, hi⟩` from `Multiset.mem_map.1 ha`. Conclude with `vne i c hi`. Take `⟨i, -, hi⟩` from `Multiset.mem_map.1 ha`.

Conclude with `bne i c hc hi`.
-/
theorem nodup_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : (qv R h j).Nodup := by
  classical
  have hk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have ht0 : (0 : ℚ) ≤ R.t := by positivity
  let U : ℕ → ℚ := fun i => if hi : i < R.k then h.u ⟨i, hi⟩ else 0
  let V : ℕ → ℚ := fun i => if hi : i < R.k - 1 then h.v ⟨i, hi⟩ else 0
  let B : ℕ → ℚ := fun i => if hi : i < R.m then -h.b ⟨i, hi⟩ else 0
  have hU : ∀ i, i + 1 < R.k → U (i + 1) < U i := by
    intro i hi
    have h1 := h.u_gt_v ⟨i, by omega⟩
    have h2 := h.v_gt_u ⟨i, by omega⟩
    simp only [U, dif_pos hi, dif_pos (show i < R.k by omega)]
    exact lt_trans h2 h1
  have hV : ∀ i, i + 1 < R.k - 1 → V (i + 1) < V i := by
    intro i hi
    have h1 := h.u_gt_v ⟨i + 1, hi⟩
    have h2 := h.v_gt_u ⟨i, by omega⟩
    simp only [V, dif_pos hi, dif_pos (show i < R.k - 1 by omega)]
    exact lt_trans h1 h2
  have hB : ∀ i, i + 1 < R.m → B (i + 1) < B i := by
    intro i hi
    have h1 := h.gap_be ⟨i, by omega⟩
    have h2 := h.gap_eb ⟨i, by omega⟩ hi
    simp only [B, dif_pos hi, dif_pos (show i < R.m by omega)]
    linarith
  have bmono : ∀ i i' : Fin R.m, i.1 ≤ i'.1 → -h.b i' ≤ -h.b i := by
    intro i i' hii
    have := chain_le B R.m hB i.1 i'.1 hii i'.2
    simpa only [B, dif_pos i.2, dif_pos i'.2] using this
  have vgt : ∀ (i : Fin (R.k - 1)) (i' : Fin R.m), -h.b i' < h.v i := by
    intro i i'
    have a1 := h.v_gt_u i
    have a2 := chain_le U R.k hU (i.1 + 1) (R.k - 1) (by omega) (by omega)
    have a3 := h.u_last_gt (by omega) (by omega)
    have a4 := bmono ⟨0, by omega⟩ i' (Nat.zero_le _)
    simp only [U, dif_pos (show R.k - 1 < R.k by omega), dif_pos (show i.1 + 1 < R.k by omega)] at a2
    linarith
  have top : ∀ c : ℕ, -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 < -h.b j := by
    intro c
    have := h.gap_be j
    have hc : (0 : ℚ) ≤ c := by positivity
    linarith
  have bne : ∀ (i : Fin R.m) (c : ℕ), c < R.t → -h.b i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro i c hc
    by_cases hij : i.1 ≤ j.1
    · have := bmono i j hij
      have := top c
      intro heq; linarith
    · have hj1 : j.1 + 1 < R.m := by have := i.2; omega
      have a1 := h.gap_eb j hj1
      have a2 := bmono ⟨j.1 + 1, hj1⟩ i (show j.1 + 1 ≤ i.1 by omega)
      have hc' : (c : ℚ) + 1 ≤ R.t := by exact_mod_cast hc
      intro heq; linarith
  have vne : ∀ (i : Fin (R.k - 1)) (c : ℕ), h.v i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro i c heq
    have := vgt i j
    have := top c
    linarith
  have vinj : Function.Injective h.v := by
    refine StrictAnti.injective fun a b hab => ?_
    have := chain_lt V (R.k - 1) hV a.1 b.1 hab b.2
    simpa only [V, dif_pos a.2, dif_pos b.2] using this
  have binj : Function.Injective fun i : Fin R.m => -h.b i := by
    refine StrictAnti.injective fun a b hab => ?_
    have := chain_lt B R.m hB a.1 b.1 hab b.2
    simpa only [B, dif_pos a.2, dif_pos b.2] using this
  have rinj : Function.Injective fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro c c' hcc
    have : (c : ℚ) = c' := by simp only at hcc; linarith
    exact_mod_cast this
  unfold qv
  refine Multiset.nodup_add.2 ⟨Multiset.nodup_add.2 ⟨Finset.univ.nodup.map vinj, Finset.univ.nodup.map binj, ?_⟩,
    (Multiset.nodup_range _).map rinj, ?_⟩
  · refine Multiset.disjoint_left.2 fun ha hb => ?_
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨i', -, hi'⟩ := Multiset.mem_map.1 hb
    have := vgt i i'
    linarith
  · refine Multiset.disjoint_left.2 fun ha hb => ?_
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [Multiset.mem_range] at hc
    rcases Multiset.mem_add.1 ha with ha | ha
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 ha
      exact vne i c hi
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 ha
      exact bne i c hc hi

/- English proof (translation)
Introduce `q hq`. Unfold `qv at hq`. Break down `Multiset.mem_add.1 hq with hq | hq` into its components or cases. Break down `Multiset.mem_add.1 hq with hq | hq` into its components or cases. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hq`.

Conclude with `h.v_int i`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hq`. Take `⟨z, hz⟩` from `h.b_int i`. Conclude with `⟨-z, by rw [hz]; push_cast; ring⟩`. Take `⟨c, -, rfl⟩` from `Multiset.mem_map.1 hq`.

Take `⟨z, hz⟩` from `h.e_int j`. Take `⟨s, hs⟩` from `R.t_odd`. Use `⟨-z + s - c, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hs]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem int_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : ∀ q ∈ qv R h j, ∃ z : ℤ, q = z := by
  intro q hq
  unfold qv at hq
  rcases Multiset.mem_add.1 hq with hq | hq
  · rcases Multiset.mem_add.1 hq with hq | hq
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hq
      exact h.v_int i
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hq
      obtain ⟨z, hz⟩ := h.b_int i
      exact ⟨-z, by rw [hz]; push_cast; ring⟩
  · obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨z, hz⟩ := h.e_int j
    obtain ⟨s, hs⟩ := R.t_odd
    refine ⟨-z + s - c, ?_⟩
    rw [hz, hs]; push_cast; ring

/- English proof (translation)
Introduce `R h j sh ⟨z', hz'⟩`. Rewrite using `[paramV_eq]`. Apply `exists_domWeight_infOf` to reduce the goal to its premises. Rewrite using `[Multiset.card_map, card_qv]`. Conclude with `(nodup_qv R h j).map (fun a b hab => by simpa using hab)`.

Introduce `x hx`. Take `⟨q, hq, rfl⟩` from `Multiset.mem_map.1 hx`. Take `⟨w, rfl⟩` from `int_qv R h j q hq`. Take `⟨a, ha⟩` from `R.k_even`. Take `⟨b, hb⟩` from `R.m_even`.

Take `⟨s, hs⟩` from `R.t_odd`. Establish `hk` using `R.m_add_three_le_k`. Establish `hp : R.nV = 2 * (a + b + s)` using `by simp only [Ranks.nV, Ranks.r]; omega`. Use `⟨w - z' - (a + b + s), ?_⟩` and prove the remaining obligations. Rewrite using `[hz', hp]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem paramV_eq_infOf : ∀ (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ), (∃ z : ℤ, sh = (z : ℂ) + 1 / 2) →
    ∃ lam : DomWeight R.nV, NG.infOf lam.w = NG.paramV R h j sh := by
  intro R h j sh ⟨z', hz'⟩
  rw [paramV_eq]
  apply exists_domWeight_infOf
  · rw [Multiset.card_map, card_qv]
  · exact (nodup_qv R h j).map (fun a b hab => by simpa using hab)
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨w, rfl⟩ := int_qv R h j q hq
    obtain ⟨a, ha⟩ := R.k_even
    obtain ⟨b, hb⟩ := R.m_even
    obtain ⟨s, hs⟩ := R.t_odd
    have hk := R.m_add_three_le_k
    have hp : R.nV = 2 * (a + b + s) := by simp only [Ranks.nV, Ranks.r]; omega
    refine ⟨w - z' - (a + b + s), ?_⟩
    rw [hz', hp]; push_cast; ring

end GlobalTheory.WtComb
