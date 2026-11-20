import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Swap

def ex (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0

/- English proof (translation)
Unfold `tMat ex`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem tMat_eq {L : Type} [Field L] (ϖ : L) (n m : ℕ) (a : Fin m → ℤ) :
    tMat ϖ n m a = Matrix.diagonal fun i => ϖ ^ ex n m a i := by
  unfold tMat ex
  congr 1
  funext i
  split_ifs <;> simp

/- English proof (translation)
Unfold `ex`. Rewrite using `[dif_pos (h ▸ k.2)]`. Conclude with `congrArg a (Fin.ext h)`.
-/
theorem ex_low {n m : ℕ} (a : Fin m → ℤ) (c : Fin n) (k : Fin m) (h : c.val = k.val) : ex n m a c = a k := by
  unfold ex
  rw [dif_pos (h ▸ k.2)]
  exact congrArg a (Fin.ext h)

/- English proof (translation)
Use `k.2` as an intermediate fact. Unfold `ex`. Rewrite using `[dif_neg (by omega), dif_pos (by omega)]`. Conclude with `congrArg (fun x => -a x) (Fin.ext (by simp only; omega))`.
-/
theorem ex_high {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (c : Fin n) (k : Fin m) (h : c.val + k.val + 1 = n) :
    ex n m a c = -a k := by
  have := k.2
  unfold ex
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg (fun x => -a x) (Fin.ext (by simp only; omega))

/- English proof (translation)
Unfold `ex`. Rewrite using `[dif_neg (by omega), dif_neg (by omega)]`.
-/
theorem ex_mid {n m : ℕ} (a : Fin m → ℤ) (c : Fin n) (h : m ≤ c.val) (h' : c.val + m < n) :
    ex n m a c = 0 := by
  unfold ex
  rw [dif_neg (by omega), dif_neg (by omega)]

/- English proof (translation)
Establish `h1` using `c.2`. Establish `h2` using `Fin.val_rev c`. Distinguish the cases in `h : c.val < m`. Rewrite using `[ex_low a c ⟨c.val, h⟩ rfl, ex_high hm a c.rev ⟨c.val, h⟩ (by simp only; omega)]`. Distinguish the cases in `h' : c.val + m < n`.

Rewrite using `[ex_mid a c (by omega) h', ex_mid a c.rev (by omega) (by omega), neg_zero]`. Rewrite using `[ex_high hm a c ⟨c.rev.val, by omega⟩ (by simp only; omega), ex_low a c.rev ⟨c.rev.val, by omega⟩ rfl, neg_neg]`.
-/
theorem ex_rev {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (c : Fin n) : ex n m a c.rev = -ex n m a c := by
  have h1 := c.2
  have h2 := Fin.val_rev c
  by_cases h : c.val < m
  · rw [ex_low a c ⟨c.val, h⟩ rfl, ex_high hm a c.rev ⟨c.val, h⟩ (by simp only; omega)]
  · by_cases h' : c.val + m < n
    · rw [ex_mid a c (by omega) h', ex_mid a c.rev (by omega) (by omega), neg_zero]
    · rw [ex_high hm a c ⟨c.rev.val, by omega⟩ (by simp only; omega), ex_low a c.rev ⟨c.rev.val, by omega⟩ rfl,
        neg_neg]

def emb (n i : ℕ) (h : 2 * i + 4 ≤ n) : Fin 4 → Fin n :=
  ![⟨i, by omega⟩, ⟨i + 1, by omega⟩, ⟨n - 2 - i, by omega⟩, ⟨n - 1 - i, by omega⟩]

def blk (n i : ℕ) (a : Fin n) : ℕ :=
  if a.val = i + 1 then i else if a.val = n - 1 - i then n - 2 - i else a.val

/- English proof (translation)
Unfold `blk`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem blk_eq_iff {n i : ℕ} (h : 2 * i + 4 ≤ n) (a b : Fin n) :
    blk n i a = blk n i b ↔ a.val = b.val ∨ (a.val = i ∧ b.val = i + 1) ∨ (a.val = i + 1 ∧ b.val = i) ∨
      (a.val + i + 2 = n ∧ b.val + i + 1 = n) ∨ (a.val + i + 1 = n ∧ b.val + i + 2 = n) := by
  unfold blk
  split_ifs <;> omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro ⟨k, rfl⟩ fin_cases k <;> simp [emb]`. Introduce and unpack `(h1 | h1 | h1 | h1) exacts [⟨0, Fin.ext h1.symm⟩, ⟨1, Fin.ext h1.symm⟩, ⟨2, Fin.ext h1.symm⟩, ⟨3, Fin.ext h1.symm⟩]`.
-/
theorem mem_range_emb {n i : ℕ} (h : 2 * i + 4 ≤ n) (a : Fin n) :
    a ∈ Set.range (emb n i h) ↔ a.val = i ∨ a.val = i + 1 ∨ a.val = n - 2 - i ∨ a.val = n - 1 - i := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [emb]
  · rintro (h1 | h1 | h1 | h1)
    exacts [⟨0, Fin.ext h1.symm⟩, ⟨1, Fin.ext h1.symm⟩, ⟨2, Fin.ext h1.symm⟩, ⟨3, Fin.ext h1.symm⟩]

/- English proof (translation)
Establish `v0 : (emb n i h 0).val = i` using `rfl`. Establish `v1 : (emb n i h 1).val = i + 1` using `rfl`. Establish `v2 : (emb n i h 2).val = n - 2 - i` using `rfl`. Establish `v3 : (emb n i h 3).val = n - 1 - i` using `rfl`. Apply the tactic sequence `have b0 : blk n i (emb n i h 0) = i := by unfold blk; rw [v0]; split_ifs <;> omega`.

Apply the tactic sequence `have b1 : blk n i (emb n i h 1) = i := by unfold blk; rw [v1]; split_ifs <;> omega`. Apply the tactic sequence `have b2 : blk n i (emb n i h 2) = n - 2 - i := by unfold blk; rw [v2]; split_ifs <;> omega`. Apply the tactic sequence `have b3 : blk n i (emb n i h 3) = n - 2 - i := by unfold blk; rw [v3]; split_ifs <;> omega`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.strictMono_iff_lt_succ]`.

Introduce `k`. Use `fin_cases k`. Use `show i < i + 1`. Use linear arithmetic over natural numbers and integers. Use `show i + 1 < n - 2 - i`.

Use linear arithmetic over natural numbers and integers. Use `show n - 2 - i < n - 1 - i`. Use linear arithmetic over natural numbers and integers. Introduce `k`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[Fin.val_rev]`. Use `fin_cases k`. Use `show n - 1 - i = n - (i + 1)`. Use linear arithmetic over natural numbers and integers. Use `show n - 2 - i = n - (i + 1 + 1)`.

Use linear arithmetic over natural numbers and integers. Use `show i + 1 = n - (n - 2 - i + 1)`. Use linear arithmetic over natural numbers and integers. Use `show i = n - (n - 1 - i + 1)`. Use linear arithmetic over natural numbers and integers.

Introduce `a b hab`. Establish `: a.val ≤ b.val` using `hab`. Unfold `blk`. Apply the tactic sequence `split_ifs <;> omega`. Introduce `a b`.

Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Rewrite using `[blk_eq_iff h, blk_eq_iff h, Fin.val_rev, Fin.val_rev]`. Use `clear v0 v1 v2 v3 b0 b1 b2 b3`. Apply the tactic sequence `rintro (h1 | h1 | h1 | h1 | h1) <;> omega`.

Introduce `a b`. Rewrite using `[mem_range_emb, mem_range_emb, Fin.ext_iff, blk_eq_iff h]`. Introduce and unpack `(h1 | h1 | h1 | h1 | h1)`. Conclude with `Or.inl h1`. Apply the tactic sequence `all_goals exact Or.inr ⟨by omega, by omega⟩`.

Establish `hne : i ≠ n - 2 - i` using `by omega`. Simplify using `only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]`. Simplify using `[b0, b1, b2, b3, hne, hne.symm, show (Fin.succ 2 : Fin 4) = 3 from rfl]`.
-/
theorem isBlockDatum_emb {n i : ℕ} (h : 2 * i + 4 ≤ n) : IsBlockDatum (emb n i h) (blk n i) ![0, 0, 1, 1] := by
  have v0 : (emb n i h 0).val = i := rfl
  have v1 : (emb n i h 1).val = i + 1 := rfl
  have v2 : (emb n i h 2).val = n - 2 - i := rfl
  have v3 : (emb n i h 3).val = n - 1 - i := rfl
  have b0 : blk n i (emb n i h 0) = i := by unfold blk; rw [v0]; split_ifs <;> omega
  have b1 : blk n i (emb n i h 1) = i := by unfold blk; rw [v1]; split_ifs <;> omega
  have b2 : blk n i (emb n i h 2) = n - 2 - i := by unfold blk; rw [v2]; split_ifs <;> omega
  have b3 : blk n i (emb n i h 3) = n - 2 - i := by unfold blk; rw [v3]; split_ifs <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro k
    fin_cases k
    · show i < i + 1
      omega
    · show i + 1 < n - 2 - i
      omega
    · show n - 2 - i < n - 1 - i
      omega
  · intro k
    apply Fin.ext
    rw [Fin.val_rev]
    fin_cases k
    · show n - 1 - i = n - (i + 1)
      omega
    · show n - 2 - i = n - (i + 1 + 1)
      omega
    · show i + 1 = n - (n - 2 - i + 1)
      omega
    · show i = n - (n - 1 - i + 1)
      omega
  · intro a b hab
    have : a.val ≤ b.val := hab
    unfold blk
    split_ifs <;> omega
  · intro a b
    have := a.2
    have := b.2
    rw [blk_eq_iff h, blk_eq_iff h, Fin.val_rev, Fin.val_rev]
    clear v0 v1 v2 v3 b0 b1 b2 b3
    rintro (h1 | h1 | h1 | h1 | h1) <;> omega
  · intro a b
    rw [mem_range_emb, mem_range_emb, Fin.ext_iff, blk_eq_iff h]
    rintro (h1 | h1 | h1 | h1 | h1)
    · exact Or.inl h1
    all_goals exact Or.inr ⟨by omega, by omega⟩
  · have hne : i ≠ n - 2 - i := by omega
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
    simp [b0, b1, b2, b3, hne, hne.symm, show (Fin.succ 2 : Fin 4) = 3 from rfl]

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n m hU hm hn h hh a i j hij t t' ht ht'`. Establish `hj` using `j.2`. Establish `h4 : 2 * i.val + 4 ≤ n` using `by omega`. Establish `hq : q ≠ 0`. Use `hU.2.2.2.2.2.1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `key : ∀ (c : Fin m → ℤ) (k : Fin 4), ex n m c (emb n i h4 k) = (![c i, c j, -c j, -c i] : Fin 4 → ℤ) k`. Introduce `c k`. Use `fin_cases k`. Conclude with `ex_low c _ i rfl`.

Conclude with `ex_low c _ j hij.symm`. Conclude with `ex_high hm c _ j (by show n - 2 - i.val + j.val + 1 = n; omega)`. Conclude with `ex_high hm c _ i (by show n - 1 - i.val + i.val + 1 = n; omega)`. Establish `key' : ∀ k : Fin 4, ex n m (a ∘ Equiv.swap i j) (emb n i h4 k) = (![a j, a i, -a i, -a j] : Fin 4 → ℤ) k`. Introduce `k`.

Rewrite using `[key]`. Simplify using `only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Establish `main` using `H L ϖ σ q n 4 (emb n i h4) (blk n i) ![0, 0, 1, 1] ![1, 0, 0, -1] (ex n m a) (ex n m (a ∘ Equiv.swap i j)) (q ^ 2) (a j - a i) t t' h hU (isBlockDatum_emb h4) (by decide) (by decide) (ex_rev hm _) (ex_rev hm _) ?_ ?_ (ht.trans (tMat_eq _ _ _ _)) (ht'.trans (tMat_eq _ _ _ _)) (pow …`. Rewrite using `[main, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `c hc`. Rewrite `hc` using `[mem_range_emb]`. Use `c.2` as an intermediate fact.

Unfold `ex`. Use `split_ifs with h1 h2`. Apply the tactic sequence `rw [Function.comp, Equiv.swap_apply_of_ne_of_ne] <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega`. Apply the tactic sequence `rw [Function.comp, Equiv.swap_apply_of_ne_of_ne] <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega`. Both sides reduce to the same expression.

Introduce `k l`. Rewrite using `[key', key']`. Apply the tactic sequence `fin_cases k <;> fin_cases l <;> simp <;> ring`. Introduce `s s' hs hs'`. Simplify using `only [key a] at hs`.

Simplify using `only [key'] at hs'`. Conclude with `HC L ϖ σ q hU (a i) (a j) s s' hs hs'`.
-/
theorem coeffSwap (H : LeviStep) (HI : IndexFour) (HC : CartanFour) : CoeffSwap := by
  intro L _ _ _ ϖ σ q n m hU hm hn h hh a i j hij t t' ht ht'
  have hj := j.2
  have h4 : 2 * i.val + 4 ≤ n := by omega
  have hq : q ≠ 0 := by
    have := hU.2.2.2.2.2.1
    omega
  have key : ∀ (c : Fin m → ℤ) (k : Fin 4),
      ex n m c (emb n i h4 k) = (![c i, c j, -c j, -c i] : Fin 4 → ℤ) k := by
    intro c k
    fin_cases k
    · exact ex_low c _ i rfl
    · exact ex_low c _ j hij.symm
    · exact ex_high hm c _ j (by show n - 2 - i.val + j.val + 1 = n; omega)
    · exact ex_high hm c _ i (by show n - 1 - i.val + i.val + 1 = n; omega)
  have key' : ∀ k : Fin 4, ex n m (a ∘ Equiv.swap i j) (emb n i h4 k) =
      (![a j, a i, -a i, -a j] : Fin 4 → ℤ) k := by
    intro k
    rw [key]
    simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have main := H L ϖ σ q n 4 (emb n i h4) (blk n i) ![0, 0, 1, 1] ![1, 0, 0, -1] (ex n m a)
    (ex n m (a ∘ Equiv.swap i j)) (q ^ 2) (a j - a i) t t' h hU (isBlockDatum_emb h4)
    (by decide) (by decide) (ex_rev hm _) (ex_rev hm _) ?_ ?_ (ht.trans (tMat_eq _ _ _ _))
    (ht'.trans (tMat_eq _ _ _ _)) (pow_ne_zero _ hq) (HI L ϖ σ q hU) ?_ hh
  · rw [main, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 2
    push_cast
    ring
  · intro c hc
    rw [mem_range_emb] at hc
    have := c.2
    unfold ex
    split_ifs with h1 h2
    · rw [Function.comp, Equiv.swap_apply_of_ne_of_ne] <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega
    · rw [Function.comp, Equiv.swap_apply_of_ne_of_ne] <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega
    · rfl
  · intro k l
    rw [key', key']
    fin_cases k <;> fin_cases l <;> simp <;> ring
  · intro s s' hs hs'
    simp only [key a] at hs
    simp only [key'] at hs'
    exact HC L ϖ σ q hU (a i) (a j) s s' hs hs'

end GlobalTheory.SatakeWeyl.Swap

end
