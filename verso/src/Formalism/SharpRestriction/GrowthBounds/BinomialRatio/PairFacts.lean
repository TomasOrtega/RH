import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Finset

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`. Rewrite using `[sum_range_succ]`. Establish `h1` using `ih fun t ht => h t (by omega)`.

Establish `h2` using `h q (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pf_tele (L K : ℕ → ℤ) (q : ℕ) (h : ∀ t, t < q → L (t + 1) ≤ K t) :
    ∑ t ∈ range (q + 1), (L t - K t) ≤ L 0 - K q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ]
    have h1 := ih fun t ht => h t (by omega)
    have h2 := h q (by omega)
    linarith

def pfMass {r : ℕ} (v : Fin r → ℤ) : ℤ := ∑ t, max 0 (-(v t))

/- English proof (translation)
The claim follows from `Finset.sum_le_sum fun t _ => max_le_max le_rfl (neg_le_neg (h.1 t))`.
-/
theorem pfMass_up {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : pfMass nu ≤ pfMass mu :=
  Finset.sum_le_sum fun t _ => max_le_max le_rfl (neg_le_neg (h.1 t))

/- English proof (translation)
Establish `e : ∀ t, max 0 (-(mu t)) ≤ max 0 (-(nu t)) + (nu t - mu t)` using `fun t => by`. Use `h.1 t` as an intermediate fact. Apply the tactic sequence `rcases le_total 0 (-(mu t)) with h1 | h1 <;> rcases le_total 0 (-(nu t)) with h2 | h2 <;>`. Apply the tactic sequence `simp only [max_eq_left, max_eq_right, h1, h2] <;> omega`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_sub_distrib, h.2.2]`. Both sides reduce to the same expression.
-/
theorem pfMass_down {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : pfMass mu ≤ pfMass nu + g := by
  have e : ∀ t, max 0 (-(mu t)) ≤ max 0 (-(nu t)) + (nu t - mu t) := fun t => by
    have := h.1 t
    rcases le_total 0 (-(mu t)) with h1 | h1 <;> rcases le_total 0 (-(nu t)) with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2] <;> omega
  calc pfMass mu ≤ ∑ t, (max 0 (-(nu t)) + (nu t - mu t)) := Finset.sum_le_sum fun t _ => e t
    _ = pfMass nu + g := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h.2.2]; rfl

variable {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `_`. Establish `e : (⟨2 * 0 + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = 1` using `rfl`.

Rewrite using `[e]`. Unfold `pfMass`. Simplify using `[chain_first_tail (N := 2 * s) h (by simp [kLetters])]`. Consider the case `succ n ih`. Introduce `hn`.

Establish `h0` using `ih (by omega)`. Take `⟨hW, hC, -, -, -, -, -, -⟩` from `pair_top h (⟨n, by omega⟩ : Fin s)`. Establish `h1` using `pfMass_up hW`. Establish `h2` using `pfMass_down hC`. Establish `h3` using `sum_lt_succ (fun x : Fin s => (Ci x : ℤ)) (⟨n, by omega⟩ : Fin s)`.

Simplify using `only at h3`. Rewrite using `[h3]`. Establish `e : (⟨2 * (n + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * n + 3, by omega⟩` using `Fin.ext (by show 2 * (n + 1) + 1 = 2 * n + 3; omega)`. Rewrite using `[e]`. Establish `h4 : ((Ci ⟨n, by omega⟩ - (pairSg mu Ai ⟨n, by omega⟩).toNat : ℕ) : ℤ) ≤ (Ci ⟨n, by omega⟩ : ℤ)`.

Conclude with `Nat.sub_le _ _` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pf_mass (h : IsChain (kLetters A Ai Ci) mu) : ∀ (n : ℕ) (hn : n ≤ s),
    pfMass (fun t : Fin r => mu ⟨2 * n + 1, by omega⟩ t.succ) ≤ ∑ x : Fin s, if x.val < n then (Ci x : ℤ) else 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : (⟨2 * 0 + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = 1 := rfl
    rw [e]
    unfold pfMass
    simp [chain_first_tail (N := 2 * s) h (by simp [kLetters])]
  | succ n ih =>
    intro hn
    have h0 := ih (by omega)
    obtain ⟨hW, hC, -, -, -, -, -, -⟩ := pair_top h (⟨n, by omega⟩ : Fin s)
    have h1 := pfMass_up hW
    have h2 := pfMass_down hC
    have h3 := sum_lt_succ (fun x : Fin s => (Ci x : ℤ)) (⟨n, by omega⟩ : Fin s)
    simp only at h3
    rw [h3]
    have e : (⟨2 * (n + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * n + 3, by omega⟩ := Fin.ext (by show 2 * (n + 1) + 1 = 2 * n + 3; omega)
    rw [e]
    have h4 : ((Ci ⟨n, by omega⟩ - (pairSg mu Ai ⟨n, by omega⟩).toNat : ℕ) : ℤ) ≤ (Ci ⟨n, by omega⟩ : ℤ) := by
      exact_mod_cast Nat.sub_le _ _
    linarith

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `_`. Establish `e : (⟨2 * 0 + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = 1` using `rfl`.

Rewrite using `[e, chain_first_tail (N := 2 * s) h (by simp [kLetters])]`. Conclude with `(Finset.sum_eq_zero fun x _ => if_neg (Nat.not_lt_zero _)).symm.le`. Consider the case `succ n ih`. Introduce `hn`. Establish `h0` using `ih (by omega)`.

Take `⟨hW, hC, hw, -, -, -, -, -⟩` from `pair_top h (⟨n, by omega⟩ : Fin s)`. Establish `h1` using `strip_first hW`. Establish `h2` using `hC.1 (0 : Fin r)`. Establish `h3` using `sum_lt_succ (fun x : Fin s => pairW mu x.val) (⟨n, by omega⟩ : Fin s)`. Simplify using `only at h3 h1 h2 hw`.

Rewrite using `[h3]`. Establish `e : (⟨2 * (n + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * n + 3, by omega⟩` using `Fin.ext (by show 2 * (n + 1) + 1 = 2 * n + 3; omega)`. Rewrite using `[e]`. Rewrite `h1` using `[Int.toNat_of_nonneg hw]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pf_prev_le [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) : ∀ (n : ℕ) (hn : n ≤ s),
    mu ⟨2 * n + 1, by omega⟩ (0 : Fin r).succ ≤ ∑ x : Fin s, if x.val < n then pairW mu x.val else 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : (⟨2 * 0 + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = 1 := rfl
    rw [e, chain_first_tail (N := 2 * s) h (by simp [kLetters])]
    exact (Finset.sum_eq_zero fun x _ => if_neg (Nat.not_lt_zero _)).symm.le
  | succ n ih =>
    intro hn
    have h0 := ih (by omega)
    obtain ⟨hW, hC, hw, -, -, -, -, -⟩ := pair_top h (⟨n, by omega⟩ : Fin s)
    have h1 := strip_first hW
    have h2 := hC.1 (0 : Fin r)
    have h3 := sum_lt_succ (fun x : Fin s => pairW mu x.val) (⟨n, by omega⟩ : Fin s)
    simp only at h3 h1 h2 hw
    rw [h3]
    have e : (⟨2 * (n + 1) + 1, by omega⟩ : Fin (2 * s + 1 + 1)) = ⟨2 * n + 3, by omega⟩ := Fin.ext (by show 2 * (n + 1) + 1 = 2 * n + 3; omega)
    rw [e]
    rw [Int.toNat_of_nonneg hw] at h1
    linarith

/- English proof (translation)
Take `⟨hW, -, hw, -, -, -, -, -⟩` from `pair_top h i`. Establish `h1` using `strip_first hW`. Rewrite `h1` using `[Int.toNat_of_nonneg hw]`. Unfold `pairRho`. Rewrite using `[finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega)]`.

Conclude with `h1`.
-/
theorem pf_rho_le [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairRho mu i.val ≤ mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin r).succ + pairW mu i.val := by
  obtain ⟨hW, -, hw, -, -, -, -, -⟩ := pair_top h i
  have h1 := strip_first hW
  rw [Int.toNat_of_nonneg hw] at h1
  unfold pairRho
  rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega)]
  exact h1

/- English proof (translation)
Establish `h1` using `pf_rho_le h i`. Establish `hs : pairSg mu Ai i = pairO mu Ai i - pairW mu i.val` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pf_u_ge [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairSg mu Ai i - mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin r).succ ≤ pairO mu Ai i - pairRho mu i.val := by
  have h1 := pf_rho_le h i
  have hs : pairSg mu Ai i = pairO mu Ai i - pairW mu i.val := rfl
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, -, h1, h2⟩` from `pair_top h i`. Unfold `pairRho`. Rewrite using `[finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega)]`. Conclude with `⟨h1 0 (by simp), h2 0 (by simp)⟩`.
-/
theorem pf_rho_le_c [NeZero r] (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    pairRho mu i.val ≤ pairC mu i.val ∧ pairRho mu i.val ≤ pairC mu (i.val + 1) := by
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := pair_top h i
  unfold pairRho
  rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega)]
  exact ⟨h1 0 (by simp), h2 0 (by simp)⟩

/- English proof (translation)
Take `⟨hch, hint⟩` from `h`. Take `⟨q, rfl⟩ : ∃ q, r = q + 1 + s` from `⟨r - 1 - s, by omega⟩`. Use `set ka : Fin (q + 1 + s) → ℤ := fun t => mu (Fin.last _) t.succ with hka`. Set `L : ℕ → ℤ` to `fun t => if h : t < q + 1 + s then lam ⟨t, h⟩ else 0`. Set `K : ℕ → ℤ` to `fun t => if h : t < q + 1 + s then ka ⟨t, h⟩ else 0`.

Establish `hlast : (Fin.last (2 * s + 1) : Fin (2 * s + 1 + 1)) = ⟨2 * s + 1, by omega⟩` using `rfl`. Establish `hD : pairD mu lam = ∑ t ∈ range (q + 1 + s), (L t - K t)`. Unfold `pairD pairTail`. Rewrite using `[finPos_eq (2 * s + 1) (2 * s + 1) (by omega), ← Finset.sum_sub_distrib]`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun t => L t - K t)]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [L, K, dif_pos t.2, hka, hlast]`. Establish `hmass` using `pf_mass hch s le_rfl`. Establish `hmass' : pfMass ka ≤ ∑ i, (Ci i : ℤ)`. Establish `e : ∀ x : Fin s, (if x.val < s then (Ci x : ℤ) else 0) = Ci x` using `fun x => if_pos x.2`.

Rewrite `hmass` using `[Finset.sum_congr rfl fun x _ => e x]`. Conclude with `hmass`. Rewrite using `[hD, Finset.sum_range_add]`. Establish `hup : ∑ t ∈ range (q + 1), (L t - K t) ≤ L 0 - K q` using `pf_tele L K q fun t ht => by`. Simplify using `only [L, K, dif_pos (show t + 1 < q + 1 + s by omega), dif_pos (show t < q + 1 + s by omega), hka]`.

Use `(hint ⟨t + 1, by omega⟩).2` as an intermediate fact. Establish `e : (⟨t + 1, by omega⟩ : Fin (q + 1 + s)).castSucc = (⟨t, by omega⟩ : Fin (q + 1 + s)).succ` using `Fin.ext rfl`. Rewrite `this` using `[e]`. Conclude with `this`. Establish `hL0 : L 0 ≤ pairC mu s`.

Simplify using `only [L, dif_pos (show 0 < q + 1 + s by omega)]`. Use `(hint ⟨0, by omega⟩).2` as an intermediate fact. Unfold `pairC`. Rewrite using `[finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]`. Conclude with `this`.

Establish `hKq : 0 ≤ K q`. Simplify using `only [K, dif_pos (show q < q + 1 + s by omega), hka]`. Establish `hM : ∀ i, Ai i ≤ ∑ i, Ai i + ∑ i, Ci i` using `fun i => le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)`. Establish `hM' : ∀ i, Ci i ≤ ∑ i, Ai i + ∑ i, Ci i` using `fun i => le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)`. Use `(pc_shape hM hM' hch (Fin.last _) (⟨q, by omega⟩ : Fin (q + 1 + s)).succ).2.1` as an intermediate fact.

Apply `this` to reduce the goal to its premises. Simplify using `only [Fin.val_succ, Fin.val_last, pcL]`. Use linear arithmetic over natural numbers and integers. Establish `hlowL : ∑ x ∈ range s, L (q + 1 + x) = -∑ i : Fin s, pairN (s` using `s) lam i := by`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun x => L (q + 1 + x)), ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `pairN`. Establish `e : q + 1 + s - s + i.val = q + 1 + i.val` using `by omega`. Simplify using `only [L, e, neg_neg]`. Establish `hlowK : -∑ x ∈ range s, K (q + 1 + x) ≤ pfMass ka`.

Establish `h1 : -∑ x ∈ range s, K (q + 1 + x) ≤ ∑ x ∈ range s, max 0 (-(K (q + 1 + x)))`. Rewrite using `[← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_le_sum fun x _ => le_max_right _ _`. Establish `h2 : ∑ t ∈ range (q + 1 + s), max 0 (-(K t)) = pfMass ka`. Unfold `pfMass`.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun t => max 0 (-(K t)))]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [K, dif_pos t.2]`. Establish `h3 : ∑ x ∈ range s, max 0 (-(K (q + 1 + x))) ≤ ∑ t ∈ range (q + 1 + s), max 0 (-(K t))`. Rewrite using `[Finset.sum_range_add]`.

Establish `: 0 ≤ ∑ t ∈ range (q + 1), max 0 (-(K t))` using `Finset.sum_nonneg fun _ _ => le_max_left _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsplit : ∑ x ∈ range s, (L (q + 1 + x) - K (q + 1 + x)) = ∑ x ∈ range s, L (q + 1 + x) - ∑ x ∈ range s, K (q + 1 + x)` using `Finset.sum_sub_distrib _ _`. Rewrite using `[hsplit, hlowL]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pf_d_le (h : IsPair A Ai Ci mu lam) (hr : s + 1 ≤ r) :
    pairD mu lam ≤ pairC mu s + ∑ i, (Ci i : ℤ) - ∑ i : Fin s, pairN (s := s) lam i := by
  obtain ⟨hch, hint⟩ := h
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 + s := ⟨r - 1 - s, by omega⟩
  set ka : Fin (q + 1 + s) → ℤ := fun t => mu (Fin.last _) t.succ with hka
  let L : ℕ → ℤ := fun t => if h : t < q + 1 + s then lam ⟨t, h⟩ else 0
  let K : ℕ → ℤ := fun t => if h : t < q + 1 + s then ka ⟨t, h⟩ else 0
  have hlast : (Fin.last (2 * s + 1) : Fin (2 * s + 1 + 1)) = ⟨2 * s + 1, by omega⟩ := rfl
  have hD : pairD mu lam = ∑ t ∈ range (q + 1 + s), (L t - K t) := by
    unfold pairD pairTail
    rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega), ← Finset.sum_sub_distrib]
    rw [← Fin.sum_univ_eq_sum_range (fun t => L t - K t)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [L, K, dif_pos t.2, hka, hlast]
  have hmass := pf_mass hch s le_rfl
  have hmass' : pfMass ka ≤ ∑ i, (Ci i : ℤ) := by
    have e : ∀ x : Fin s, (if x.val < s then (Ci x : ℤ) else 0) = Ci x := fun x => if_pos x.2
    rw [Finset.sum_congr rfl fun x _ => e x] at hmass
    exact hmass
  rw [hD, Finset.sum_range_add]

  have hup : ∑ t ∈ range (q + 1), (L t - K t) ≤ L 0 - K q := pf_tele L K q fun t ht => by
    simp only [L, K, dif_pos (show t + 1 < q + 1 + s by omega), dif_pos (show t < q + 1 + s by omega), hka]
    have := (hint ⟨t + 1, by omega⟩).2
    have e : (⟨t + 1, by omega⟩ : Fin (q + 1 + s)).castSucc = (⟨t, by omega⟩ : Fin (q + 1 + s)).succ := Fin.ext rfl
    rw [e] at this
    exact this
  have hL0 : L 0 ≤ pairC mu s := by
    simp only [L, dif_pos (show 0 < q + 1 + s by omega)]
    have := (hint ⟨0, by omega⟩).2
    unfold pairC
    rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]
    exact this
  have hKq : 0 ≤ K q := by
    simp only [K, dif_pos (show q < q + 1 + s by omega), hka]
    have hM : ∀ i, Ai i ≤ ∑ i, Ai i + ∑ i, Ci i := fun i =>
      le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)
    have hM' : ∀ i, Ci i ≤ ∑ i, Ai i + ∑ i, Ci i := fun i =>
      le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
    have := (pc_shape hM hM' hch (Fin.last _) (⟨q, by omega⟩ : Fin (q + 1 + s)).succ).2.1
    apply this
    simp only [Fin.val_succ, Fin.val_last, pcL]
    omega

  have hlowL : ∑ x ∈ range s, L (q + 1 + x) = -∑ i : Fin s, pairN (s := s) lam i := by
    rw [← Fin.sum_univ_eq_sum_range (fun x => L (q + 1 + x)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold pairN
    have e : q + 1 + s - s + i.val = q + 1 + i.val := by omega
    simp only [L, e, neg_neg]
  have hlowK : -∑ x ∈ range s, K (q + 1 + x) ≤ pfMass ka := by
    have h1 : -∑ x ∈ range s, K (q + 1 + x) ≤ ∑ x ∈ range s, max 0 (-(K (q + 1 + x))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun x _ => le_max_right _ _
    have h2 : ∑ t ∈ range (q + 1 + s), max 0 (-(K t)) = pfMass ka := by
      unfold pfMass
      rw [← Fin.sum_univ_eq_sum_range (fun t => max 0 (-(K t)))]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [K, dif_pos t.2]
    have h3 : ∑ x ∈ range s, max 0 (-(K (q + 1 + x))) ≤ ∑ t ∈ range (q + 1 + s), max 0 (-(K t)) := by
      rw [Finset.sum_range_add]
      have : 0 ≤ ∑ t ∈ range (q + 1), max 0 (-(K t)) := Finset.sum_nonneg fun _ _ => le_max_left _ _
      linarith
    linarith
  have hsplit : ∑ x ∈ range s, (L (q + 1 + x) - K (q + 1 + x)) =
      ∑ x ∈ range s, L (q + 1 + x) - ∑ x ∈ range s, K (q + 1 + x) := Finset.sum_sub_distrib _ _
  rw [hsplit, hlowL]
  linarith

/- English proof (translation)
Establish `h1` using `pf_d_le h hr`. Establish `h2 : ((pairD mu lam : ℤ) : ℝ) ≤ ((pairC mu s : ℤ) : ℝ) + ∑ i, (Ci i : ℝ) - ∑ i : Fin s, ((pairN (s` using `s) lam i : ℤ) : ℝ) := by`. Use `(Int.cast_le (R := ℝ)).2 h1` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Establish `h3 : ∑ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) ≤ ∑ i : Fin s, ((pairN (s` using `s) lam i : ℤ) : ℝ) := Finset.sum_le_sum fun i _ => hK i`. Establish `h4 : ∑ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) = ∑ i, (Ci i : ℝ) - La / ((r : ℝ) + 1) * ∑ i, (Ci i : ℝ)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pf_X (h : IsPair A Ai Ci mu lam) (hr : s + 1 ≤ r) (La : ℝ)
    (hK : ∀ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) ≤ ((pairN (s := s) lam i : ℤ) : ℝ)) :
    ((pairD mu lam : ℤ) : ℝ) ≤ ((pairC mu s : ℤ) : ℝ) + La / ((r : ℝ) + 1) * ∑ i, (Ci i : ℝ) := by
  have h1 := pf_d_le h hr
  have h2 : ((pairD mu lam : ℤ) : ℝ) ≤ ((pairC mu s : ℤ) : ℝ) + ∑ i, (Ci i : ℝ) - ∑ i : Fin s, ((pairN (s := s) lam i : ℤ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).2 h1
    push_cast at this
    exact this
  have h3 : ∑ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) ≤ ∑ i : Fin s, ((pairN (s := s) lam i : ℤ) : ℝ) :=
    Finset.sum_le_sum fun i _ => hK i
  have h4 : ∑ i : Fin s, (Ci i : ℝ) * (1 - La / ((r : ℝ) + 1)) =
      ∑ i, (Ci i : ℝ) - La / ((r : ℝ) + 1) * ∑ i, (Ci i : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

end Formalism.MainNotions.ColumnSystems.Pf
