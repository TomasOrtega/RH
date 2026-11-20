import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Neg

def ext {m : ℕ} (a : Fin m → ℤ) (x : ℕ) : ℤ := if h : x < m then a ⟨x, h⟩ else 0

def expo (n m : ℕ) (A : ℕ → ℤ) (x : Fin n) : ℤ :=
  if x.val < m then A x else if n - m ≤ x.val then -A (n - 1 - x.val) else 0

/- English proof (translation)
Unfold `tMat`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `hx` using `x.2`. Unfold `expo ext`.

Distinguish the cases in `h1 : x.val < m`. Simplify using `[h1]`. Distinguish the cases in `h2 : n - m ≤ x.val`. Establish `h3 : n - 1 - x.val < m` using `by omega`. Simplify using `[h1, h2, h3]`.

Simplify using `[h1, h2]`.
-/
theorem tMat_eq {L : Type} [Field L] (ϖ : L) {n m : ℕ} (a : Fin m → ℤ) :
    tMat ϖ n m a = Matrix.diagonal fun x => ϖ ^ expo n m (ext a) x := by
  unfold tMat
  congr 1
  funext x
  have hx := x.2
  unfold expo ext
  by_cases h1 : x.val < m
  · simp [h1]
  · by_cases h2 : n - m ≤ x.val
    · have h3 : n - 1 - x.val < m := by omega
      simp [h1, h2, h3]
    · simp [h1, h2]

/- English proof (translation)
Unfold `ext`. Distinguish the cases in `h : x = i.val`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `h1 : x < m`.

Establish `: (⟨x, h1⟩ : Fin m) ≠ i` using `fun e => h (congrArg Fin.val e)`. Simplify using `[h, h1, Function.update_of_ne this]`. Simplify using `[h, h1]`.
-/
theorem ext_update {m : ℕ} (a : Fin m → ℤ) (i : Fin m) (c : ℤ) (x : ℕ) :
    ext (Function.update a i c) x = if x = i.val then c else ext a x := by
  unfold ext
  by_cases h : x = i.val
  · subst h
    simp
  · by_cases h1 : x < m
    · have : (⟨x, h1⟩ : Fin m) ≠ i := fun e => h (congrArg Fin.val e)
      simp [h, h1, Function.update_of_ne this]
    · simp [h, h1]

/- English proof (translation)
Establish `hx` using `x.2`. Establish `hr : (x.rev : ℕ) = n - 1 - x` using `by rw [Fin.val_rev]; omega`. Unfold `expo`. Rewrite using `[hr]`. Establish `e : n - 1 - (n - 1 - x.val) = x.val` using `by omega`.

Rewrite using `[e]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`.
-/
theorem expo_rev {n m : ℕ} (h : 2 * m ≤ n) (A : ℕ → ℤ) (x : Fin n) :
    expo n m A x.rev = -expo n m A x := by
  have hx := x.2
  have hr : (x.rev : ℕ) = n - 1 - x := by rw [Fin.val_rev]; omega
  unfold expo
  rw [hr]
  have e : n - 1 - (n - 1 - x.val) = x.val := by omega
  rw [e]
  split_ifs <;> first | omega | simp

def mid {n : ℕ} (k r : ℕ) (h : n = 2 * k + r) (j : Fin r) : Fin n := ⟨k + j.val, by have := j.2; omega⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, rfl⟩`. Use `j.2` as an intermediate fact. Simplify using `only [mid]`. Use linear arithmetic over natural numbers and integers.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨x.val - k, by omega⟩, Fin.ext (by simp only [mid]; omega)⟩`.
-/
theorem mem_range_mid {n k r : ℕ} (h : n = 2 * k + r) (x : Fin n) :
    x ∈ Set.range (mid k r h) ↔ k ≤ x.val ∧ x.val < k + r := by
  constructor
  · rintro ⟨j, rfl⟩
    have := j.2
    simp only [mid]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x.val - k, by omega⟩, Fin.ext (by simp only [mid]; omega)⟩

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun i => ?_, fun x y hxy => ?_, fun x y hxy => ?_, fun x y hxy => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `: i.val < j.val` using `hij show k + i.val < k + j.val`. Use linear arithmetic over natural numbers and integers. Use `i.2` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [mid, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Establish `: x.val ≤ y.val` using `hxy`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> omega`.

Use `x.2` as an intermediate fact. Use `y.2` as an intermediate fact. Simplify using `only [Fin.val_rev] at hxy ⊢`. Apply the tactic sequence `split_ifs at hxy ⊢ <;> omega`. Rewrite using `[mem_range_mid, mem_range_mid, Fin.ext_iff]`.

Simplify using `only at hxy`. Apply the tactic sequence `split_ifs at hxy <;> omega`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Simplify using `only [mid, hγ]`.

Apply the tactic sequence `split_ifs <;> first | omega | simp`.
-/
theorem blockDatum {n k r : ℕ} (h : n = 2 * k + r) (γ : Fin r → ℕ) (hγ : ∀ j, γ j = 0) :
    IsBlockDatum (mid k r h) (fun x => if k ≤ x.val ∧ x.val < k + r then k else x.val) γ := by
  refine ⟨fun i j hij => ?_, fun i => ?_, fun x y hxy => ?_, fun x y hxy => ?_, fun x y hxy => ?_, fun i j => ?_⟩
  · have : i.val < j.val := hij
    show k + i.val < k + j.val
    omega
  · have := i.2
    apply Fin.ext
    simp only [mid, Fin.val_rev]
    omega
  · have : x.val ≤ y.val := hxy
    simp only
    split_ifs <;> omega
  · have := x.2
    have := y.2
    simp only [Fin.val_rev] at hxy ⊢
    split_ifs at hxy ⊢ <;> omega
  · rw [mem_range_mid, mem_range_mid, Fin.ext_iff]
    simp only at hxy
    split_ifs at hxy <;> omega
  · have := i.2
    have := j.2
    simp only [mid, hγ]
    split_ifs <;> first | omega | simp

/- English proof (translation)
Establish `h0 : ϖ ≠ 0`. Introduce `h`. Use `hU.2.2.2.1` as an intermediate fact. Rewrite `this` using `[h, Valuation.map_zero]`. Conclude with `absurd this WithZero.zero_ne_coe`.

Establish `key : ∀ (c : Fin m → ℤ) (j : Fin r), expo n m (ext c) (mid i.val r hn j) = c i * b j`. Introduce `c j`. Establish `hj` using `j.2`. Establish `hci : ext c i.val = c i` using `by simp [ext]`. Rewrite using `[hb]`.

Unfold `expo`. Simplify using `only [mid]`. Distinguish the cases in `h1 : j.val = 0`. Simplify using `[h1, hci]`. Distinguish the cases in `h2 : j.val + 1 = r`.

Establish `e : n - 1 - (i.val + j.val) = i.val` using `by omega`. Establish `f1 : ¬ i.val + j.val < m` using `by omega`. Establish `f2 : n - m ≤ i.val + j.val` using `by omega`. Simplify using `[f1, f2, e, hci, h1, h2]`. Establish `f1 : ¬ i.val + j.val < m` using `by omega`.

Establish `f2 : ¬ n - m ≤ i.val + j.val` using `by omega`. Rewrite using `[if_neg h1, if_neg h2, mul_zero]`. Simplify using `only [f1, f2, if_false]`. Rewrite `ht`, `ht'` using `[tMat_eq]`. Use `H L ϖ σ q n r (mid i.val r hn) _ γ b _ _ Q (-a i) t t' h hU (blockDatum hn γ hγ) ?_ ?_ (expo_rev hm _) (expo_rev hm _) ?_ ?_ ht ht' hQ hI ?_ hh` as an intermediate fact.

Rewrite `this` using `[neg_neg]`. Then use the resulting hypothesis. Introduce `j`. Use `j.2` as an intermediate fact. Rewrite using `[hb, hb, Fin.val_rev]`. Apply the tactic sequence `split_ifs <;> omega`.

Introduce `j l hjl _`. Use `l.2` as an intermediate fact. Establish `: j.val < l.val` using `hjl`. Rewrite using `[hb, hb]`. Apply the tactic sequence `split_ifs <;> omega`.

Introduce `x hx`. Use `x.2` as an intermediate fact. Rewrite `hx` using `[mem_range_mid]`. Unfold `expo`. Rewrite using `[ext_update, ext_update]`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Introduce `j l _`. Rewrite using `[key, key, Function.update_self]`. Expand and normalize the polynomial expressions, which then agree. Introduce `s s' hs hs' g _`.

Establish `e : s' = s⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Apply `mat_injective` to reduce the goal to its premises. Rewrite using `[mat_mul, hs, hs', Matrix.diagonal_mul_diagonal, mat_one, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Rewrite using `[key, key, Function.update_self, ← zpow_add₀ h0]`. Simplify using the standard rewrite rules. Take `⟨k₁, hk₁, k₂, hk₂, e'⟩` from `inv_mem_dc hU (s * g)`. Use `⟨k₁, hk₁, k₂, ⟨hk₂, fun x y hxy => absurd ((hγ x).trans (hγ y).symm) hxy⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← e', e, mul_inv_rev]`.
-/
theorem step (H : LeviStep) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q n m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1)
    {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) (a : Fin m → ℤ) (i : Fin m) (hi : i.val + 1 = m)
    {t t' : GU σ n} (ht : mat t = tMat ϖ n m a) (ht' : mat t' = tMat ϖ n m (Function.update a i (-a i)))
    (r : ℕ) (hn : n = 2 * i.val + r) (γ : Fin r → ℕ) (hγ : ∀ j, γ j = 0) (b : Fin r → ℤ)
    (hb : ∀ j, b j = if j.val = 0 then 1 else if j.val + 1 = r then -1 else 0) (Q : ℕ) (hQ : Q ≠ 0)
    (hI : ∀ s₀ : GU σ r, mat s₀ = Matrix.diagonal (fun i => ϖ ^ b i) →
      ((KU σ r ⊓ rootU σ γ).map (MulAut.conj s₀).toMonoidHom).relIndex (KU σ r ⊓ rootU σ γ) = Q) :
    cellSum (KU σ n) (radU σ Fin.val) h t = (Q : ℂ) ^ (a i) * cellSum (KU σ n) (radU σ Fin.val) h t' := by
  have h0 : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact absurd this WithZero.zero_ne_coe
  have key : ∀ (c : Fin m → ℤ) (j : Fin r), expo n m (ext c) (mid i.val r hn j) = c i * b j := by
    intro c j
    have hj := j.2
    have hci : ext c i.val = c i := by simp [ext]
    rw [hb]
    unfold expo
    simp only [mid]
    by_cases h1 : j.val = 0
    · simp [h1, hci]
    · by_cases h2 : j.val + 1 = r
      · have e : n - 1 - (i.val + j.val) = i.val := by omega
        have f1 : ¬ i.val + j.val < m := by omega
        have f2 : n - m ≤ i.val + j.val := by omega
        simp [f1, f2, e, hci, h1, h2]
      · have f1 : ¬ i.val + j.val < m := by omega
        have f2 : ¬ n - m ≤ i.val + j.val := by omega
        rw [if_neg h1, if_neg h2, mul_zero]
        simp only [f1, f2, if_false]
  rw [tMat_eq] at ht ht'
  have := H L ϖ σ q n r (mid i.val r hn) _ γ b _ _ Q (-a i) t t' h hU (blockDatum hn γ hγ) ?_ ?_
    (expo_rev hm _) (expo_rev hm _) ?_ ?_ ht ht' hQ hI ?_ hh
  · rwa [neg_neg] at this
  · intro j
    have := j.2
    rw [hb, hb, Fin.val_rev]
    split_ifs <;> omega
  · intro j l hjl _
    have := l.2
    have : j.val < l.val := hjl
    rw [hb, hb]
    split_ifs <;> omega
  · intro x hx
    have := x.2
    rw [mem_range_mid] at hx
    unfold expo
    rw [ext_update, ext_update]
    split_ifs <;> first | rfl | omega
  · intro j l _
    rw [key, key, Function.update_self]
    ring
  · intro s s' hs hs' g _
    have e : s' = s⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      apply mat_injective
      rw [mat_mul, hs, hs', Matrix.diagonal_mul_diagonal, mat_one, ← Matrix.diagonal_one]
      congr 1
      funext j
      rw [key, key, Function.update_self, ← zpow_add₀ h0]
      simp
    obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := inv_mem_dc hU (s * g)
    refine ⟨k₁, hk₁, k₂, ⟨hk₂, fun x y hxy => absurd ((hγ x).trans (hγ y).symm) hxy⟩, ?_⟩
    rw [← e', e, mul_inv_rev]

end GlobalTheory.SatakeWeyl.Neg

/- English proof (translation)
Introduce `H H2 H3 L _ _ _ ϖ σ q n m hU hm hm' h hh a i hi t t' ht ht'`. Establish `hq : q ≠ 0` using `by have := hU.2.2.2.2.2.1; omega`. Break down `(by omega : n = 2 * i.val + 2 ∨ n = 2 * i.val + 3) with hn | hn` into its components or cases. Rewrite using `[Neg.step H hU hm hm' hh a i hi ht ht' 2 hn ![0, 0] (by decide) ![1, -1] (by decide) (q ^ 2) (pow_ne_zero _ hq) (H2 L ϖ σ q hU)]`. Use `congr 1`.

Rewrite using `[Nat.cast_pow, ← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Rewrite using `[hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Neg.step H hU hm hm' hh a i hi ht ht' 3 hn ![0, 0, 0] (by decide) ![1, 0, -1] (by decide) (q ^ 4) (pow_ne_zero _ hq) (H3 L ϖ σ q hU)]`. Use `congr 1`. Rewrite using `[Nat.cast_pow, ← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Rewrite using `[hn]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep : LeviStep → IndexTwo → IndexThree → CoeffNeg := by
  intro H H2 H3 L _ _ _ ϖ σ q n m hU hm hm' h hh a i hi t t' ht ht'
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  rcases (by omega : n = 2 * i.val + 2 ∨ n = 2 * i.val + 3) with hn | hn
  · rw [Neg.step H hU hm hm' hh a i hi ht ht' 2 hn ![0, 0] (by decide) ![1, -1] (by decide) (q ^ 2)
      (pow_ne_zero _ hq) (H2 L ϖ σ q hU)]
    congr 1
    rw [Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hn]
    push_cast
    ring
  · rw [Neg.step H hU hm hm' hh a i hi ht ht' 3 hn ![0, 0, 0] (by decide) ![1, 0, -1] (by decide) (q ^ 4)
      (pow_ne_zero _ hq) (H3 L ϖ σ q hU)]
    congr 1
    rw [Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hn]
    push_cast
    ring

end
