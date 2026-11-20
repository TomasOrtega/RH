import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset PositivityTheory.RgBcC.RealD
open CompanionTheory.D.LK (Pos key)

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

variable {n : ℕ}

/- English proof (translation)
Take `⟨⟨a, b⟩, hab⟩` from `i`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Use `show (a : ℕ) * n + b < n * n`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem key_lt (i : Pos n) : key i < n * n := by
  obtain ⟨⟨a, b⟩, hab⟩ := i
  have ha := a.isLt
  have hb := b.isLt
  show (a : ℕ) * n + b < n * n
  calc (a : ℕ) * n + b < a * n + n := by omega
    _ = (a + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right _ ha

/- English proof (translation)
Take `⟨b1, p1⟩` from `l`. Take `⟨b2, p2⟩` from `m`. Establish `k1` using `key_lt p1`. Establish `k2` using `key_lt p2`. Establish `hk : key p1 = key p2 ∧ b1 = b2`.

Simplify using `only [keyL] at h`. Apply the tactic sequence `cases b1 <;> cases b2 <;> simp at h ⊢ <;> omega`. Take `⟨hk, rfl⟩` from `hk`. Take `⟨⟨a1, c1⟩, h1⟩` from `p1`. Take `⟨⟨a2, c2⟩, h2⟩` from `p2`.

Establish `hc1` using `c1.isLt`. Establish `hc2` using `c2.isLt`. Establish `hn : 0 < n` using `by omega`. Establish `hk' : (c1 : ℕ) + a1 * n = c2 + a2 * n`. Establish `e : (a1 : ℕ) * n + c1 = a2 * n + c2` using `hk`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ea : (a1 : ℕ) = a2`. Use `congrArg (· / n) hk'` as an intermediate fact. Simplify `this` using `[Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc1, Nat.div_eq_of_lt hc2]`. Establish `ec : (c1 : ℕ) = c2`.

Use `congrArg (· % n) hk'` as an intermediate fact. Simplify `this` using `[Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2]`. Establish `e1 : a1 = a2` using `Fin.ext ea`. Establish `e2 : c1 = c2` using `Fin.ext ec`. Substitute `e1 e2` using the available equality.

Both sides reduce to the same expression.
-/
theorem keyL_inj {l m : Lt n} (h : keyL l = keyL m) : l = m := by
  obtain ⟨b1, p1⟩ := l
  obtain ⟨b2, p2⟩ := m
  have k1 := key_lt p1
  have k2 := key_lt p2
  have hk : key p1 = key p2 ∧ b1 = b2 := by
    simp only [keyL] at h
    cases b1 <;> cases b2 <;> simp at h ⊢ <;> omega
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨⟨a1, c1⟩, h1⟩ := p1
  obtain ⟨⟨a2, c2⟩, h2⟩ := p2
  have hc1 := c1.isLt
  have hc2 := c2.isLt
  have hn : 0 < n := by omega
  have hk' : (c1 : ℕ) + a1 * n = c2 + a2 * n := by
    have e : (a1 : ℕ) * n + c1 = a2 * n + c2 := hk
    linarith
  have ea : (a1 : ℕ) = a2 := by
    have := congrArg (· / n) hk'
    simpa [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc1, Nat.div_eq_of_lt hc2] using this
  have ec : (c1 : ℕ) = c2 := by
    have := congrArg (· % n) hk'
    simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] using this
  have e1 : a1 = a2 := Fin.ext ea
  have e2 : c1 = c2 := Fin.ext ec
  subst e1 e2
  rfl

def twL (l m : Lt n) : ℂ := if keyL m < keyL l then -1 else 1

/- English proof (translation)
Simplify using `[twL]`.
-/
theorem twL_self (l : Lt n) : twL l l = 1 := by simp [twL]

/- English proof (translation)
Unfold `twL`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem twL_mul_self (l m : Lt n) : twL l m * twL l m = 1 := by
  unfold twL
  split_ifs <;> norm_num

/- English proof (translation)
Establish `hk : keyL l ≠ keyL m` using `fun e => h (keyL_inj e)`. Unfold `twL`. Use `split_ifs with h1 h2 h2`. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.

Evaluate the numerical expressions. Evaluate the numerical expressions. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.
-/
theorem twL_swap {l m : Lt n} (h : l ≠ m) : twL m l = -twL l m := by
  have hk : keyL l ≠ keyL m := fun e => h (keyL_inj e)
  unfold twL
  split_ifs with h1 h2 h2
  · exfalso; omega
  · norm_num
  · norm_num
  · exfalso; omega

/- English proof (translation)
Unfold `sgL`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.
-/
theorem sgL_mul_self (l : Lt n) (A : Finset (Lt n)) : sgL l A * sgL l A = 1 := by
  unfold sgL
  rw [← mul_pow]
  norm_num

/- English proof (translation)
Unfold `sgL`. Conclude with `pow_ne_zero _ (by norm_num)`.
-/
theorem sgL_ne_zero (l : Lt n) (A : Finset (Lt n)) : sgL l A ≠ 0 := by
  unfold sgL
  exact pow_ne_zero _ (by norm_num)

/- English proof (translation)
Unfold `sgL twL`. Rewrite using `[Finset.filter_insert]`. Use `split_ifs with hk`. Rewrite using `[Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules.
-/
theorem sgL_insert (l : Lt n) {m : Lt n} {A : Finset (Lt n)} (h : m ∉ A) :
    sgL l (insert m A) = twL l m * sgL l A := by
  unfold sgL twL
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

/- English proof (translation)
Establish `h1` using `sgL_insert l (Finset.notMem_erase m A)`. Rewrite `h1` using `[Finset.insert_erase h]`. Rewrite using `[h1, ← mul_assoc, twL_mul_self, one_mul]`.
-/
theorem sgL_erase (l : Lt n) {m : Lt n} {A : Finset (Lt n)} (h : m ∈ A) :
    sgL l (A.erase m) = twL l m * sgL l A := by
  have h1 := sgL_insert l (Finset.notMem_erase m A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, twL_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem annL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    annL l x A = if l ∈ A then 0 else sgL l A • x (insert l A) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem creL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creL l x A = if l ∈ A then sgL l A • x (A.erase l) else 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftL_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cq n V) (A : Finset (Lt n)) :
    liftL n T x A = T (x A) := rfl

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply, annL_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Establish `hji : j ≠ i` using `fun e => hij e.symm`. Distinguish the cases in `hi : i ∈ A`. Simplify using `[hi]`. Distinguish the cases in `hj : j ∈ A`. Simplify using `[hj]`.

Simplify using `only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]`. Rewrite using `[sgL_insert j hi, sgL_insert i hj, twL_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]`. Establish `: sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0` using `by ring`. Rewrite using `[this, zero_smul]`.
-/
theorem annL_annL (i j : Lt n) : (annL i * annL j + annL j * annL i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    annL_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sgL_insert j hi, sgL_insert i hj, twL_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply, creL_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Establish `hji : j ≠ i` using `fun e => hij e.symm`. Distinguish the cases in `hi : i ∈ A`. Use `swap`. Simplify using `[hi]`. Distinguish the cases in `hj : j ∈ A`.

Use `swap`. Simplify using `[hj]`. Simplify using `only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]`. Rewrite using `[sgL_erase j hi, sgL_erase i hj, twL_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul, ← add_smul]`. Establish `: sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0` using `by ring`.

Rewrite using `[this, zero_smul]`.
-/
theorem creL_creL (i j : Lt n) : (creL i * creL j + creL j * creL i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    creL_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sgL_erase j hi, sgL_erase i hj, twL_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

/- English proof (translation)
Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[if_pos rfl]`. Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, annL_apply, creL_apply, Module.End.one_apply]`.

Distinguish the cases in `hi : i ∈ A`. Establish `h1 : i ∉ A.erase i` using `Finset.notMem_erase i A`. Rewrite using `[if_pos hi, if_pos hi, if_neg h1, sgL_erase i hi, twL_self, one_mul, Finset.insert_erase hi, smul_smul, sgL_mul_self, one_smul, zero_add]`. Establish `h1 : i ∈ insert i A` using `Finset.mem_insert_self i A`. Rewrite using `[if_neg hi, if_pos h1, if_neg hi, sgL_insert i hi, twL_self, one_mul, Finset.erase_insert hi, smul_smul, sgL_mul_self, one_smul, add_zero]`.

Rewrite using `[if_neg hij]`. Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply, Pi.add_apply, Pi.zero_apply, annL_apply, creL_apply]`. Distinguish the cases in `hi : i ∈ A`. Establish `hi' : i ∈ A.erase j` using `Finset.mem_erase.2 ⟨hij, hi⟩`.

Simplify using `[hi, hi']`. Distinguish the cases in `hj : j ∈ A`. Establish `hj' : j ∈ insert i A` using `Finset.mem_insert_of_mem hj`. Establish `hi' : i ∉ A.erase j` using `fun hm => hi (Finset.mem_of_mem_erase hm)`. Rewrite using `[if_neg hi, if_pos hj', if_pos hj, if_neg hi', sgL_insert j hi, sgL_erase i hj, twL_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]`.

Establish `e : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0` using `by ring`. Rewrite using `[e, zero_smul]`. Establish `hj' : j ∉ insert i A` using `by simp [hj, Ne.symm hij]`. Simplify using `[hi, hj, hj']`.
-/
theorem annL_creL (i j : Lt n) :
    (annL i * creL j + creL j * annL i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    refine LinearMap.ext fun x => funext fun A => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, annL_apply, creL_apply,
      Module.End.one_apply]
    by_cases hi : i ∈ A
    · have h1 : i ∉ A.erase i := Finset.notMem_erase i A
      rw [if_pos hi, if_pos hi, if_neg h1, sgL_erase i hi, twL_self, one_mul, Finset.insert_erase hi,
        smul_smul, sgL_mul_self, one_smul, zero_add]
    · have h1 : i ∈ insert i A := Finset.mem_insert_self i A
      rw [if_neg hi, if_pos h1, if_neg hi, sgL_insert i hi, twL_self, one_mul, Finset.erase_insert hi,
        smul_smul, sgL_mul_self, one_smul, add_zero]
  · rw [if_neg hij]
    refine LinearMap.ext fun x => funext fun A => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply, Pi.add_apply,
      Pi.zero_apply, annL_apply, creL_apply]
    by_cases hi : i ∈ A
    · have hi' : i ∈ A.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
      simp [hi, hi']
    · by_cases hj : j ∈ A
      · have hj' : j ∈ insert i A := Finset.mem_insert_of_mem hj
        have hi' : i ∉ A.erase j := fun hm => hi (Finset.mem_of_mem_erase hm)
        rw [if_neg hi, if_pos hj', if_pos hj, if_neg hi', sgL_insert j hi, sgL_erase i hj,
          twL_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]
        have e : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
        rw [e, zero_smul]
      · have hj' : j ∉ insert i A := by simp [hj, Ne.symm hij]
        simp [hi, hj, hj']

/- English proof (translation)
Rewrite `h` using `[annL_apply]`. Distinguish the cases in `hi : i ∈ A`. Simplify using `[hi] at h`. Use `⟨hi, fun hx => h ?_⟩` and prove the remaining obligations. Simplify using `[hi, hx]`.
-/
theorem annL_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : annL i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [annL_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · refine ⟨hi, fun hx => h ?_⟩
    simp [hi, hx]

/- English proof (translation)
Rewrite `h` using `[creL_apply]`. Distinguish the cases in `hi : i ∈ A`. Use `⟨hi, fun hx => h ?_⟩` and prove the remaining obligations. Simplify using `[hi, hx]`. Simplify using `[hi] at h`.
-/
theorem creL_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : creL i x A ≠ 0) : i ∈ A ∧ x (A.erase i) ≠ 0 := by
  rw [creL_apply] at h
  by_cases hi : i ∈ A
  · refine ⟨hi, fun hx => h ?_⟩
    simp [hi, hx]
  · simp [hi] at h

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, liftL_apply, annL_apply]`. Apply the tactic sequence `split_ifs <;> simp [liftL_apply]`.
-/
theorem liftL_annL (T : Module.End ℂ V) (l : Lt n) :
    ((liftL n T : Module.End ℂ (Cq n V)) * annL l : Module.End ℂ (Cq n V)) = annL l * (liftL n T : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, liftL_apply, annL_apply]
  split_ifs <;> simp [liftL_apply]

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, liftL_apply, creL_apply]`. Apply the tactic sequence `split_ifs <;> simp [liftL_apply]`.
-/
theorem liftL_creL (T : Module.End ℂ V) (l : Lt n) :
    ((liftL n T : Module.End ℂ (Cq n V)) * creL l : Module.End ℂ (Cq n V)) = creL l * (liftL n T : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, liftL_apply, creL_apply]
  split_ifs <;> simp [liftL_apply]

def adS (S : Lt n → Prop) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  open Classical in ∑ l : Lt n, ∑ k : Lt n, if S l then adCL s p q l k • (creL k * annL l) else 0

def Lv (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (liftL n (kA E1 E2 p q) : Module.End ℂ (Cq n V)) + adLL lev false p q

end GlobalTheory.CompanionTheory.LvChain
