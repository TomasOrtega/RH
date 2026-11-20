import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.GelfValSym

/- English proof (translation)
Simplify using `[dotProduct, mulVec]`.
-/
theorem tot_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, M a b = (fun _ => (1 : ℂ)) ⬝ᵥ (M *ᵥ fun _ => (1 : ℂ)) := by
  simp [dotProduct, mulVec]

/- English proof (translation)
Use extensionality with `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[Formalism.REAL.Amat]`. Simplify using `[Formalism.REAL.Amat, h, Matrix.one_apply_ne h]`.
-/
theorem amat_add_const {n : ℕ} (l : Fin n → ℂ) (t : ℂ) :
    Formalism.REAL.Amat (fun a => l a + t) = Formalism.REAL.Amat l + t • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext a b
  by_cases h : a = b
  · subst h; simp [Formalism.REAL.Amat]
  · simp [Formalism.REAL.Amat, h, Matrix.one_apply_ne h]

/- English proof (translation)
Simplify using `only [Formalism.REAL.Amat, Matrix.of_apply]`. Distinguish the cases in `hbp : b = p`. Substitute `hbp` using the available equality. Establish `h1 : q ≠ b` using `by intro h; rw [h] at hpq; omega`. Establish `h2 : ¬ q < b` using `by rw [Fin.lt_def]; omega`.

Simplify using `[h1, h2]`. Distinguish the cases in `hbq : b = q`. Substitute `hbq` using the available equality. Establish `h2 : p < b` using `by rw [Fin.lt_def]; omega`. Establish `h3 : p ≠ b` using `Ne.symm hbp`.

Simplify using `[hbp, h2, h3]`. Establish `e1 : p ≠ b` using `Ne.symm hbp`. Establish `e2 : q ≠ b` using `Ne.symm hbq`. Simplify using `only [e1, e2, hbp, hbq, if_false]`. Establish `: (p < b ↔ q < b)`.

Rewrite using `[Fin.lt_def, Fin.lt_def]`. Establish `: b.val ≠ p.val` using `fun h => hbp (Fin.ext h)`. Establish `: b.val ≠ q.val` using `fun h => hbq (Fin.ext h)`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : q < b`.

Simplify using `[h, this.mpr h]`. Simplify using `[h, mt this.mp h]`.
-/
theorem rowdiff {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (b : Fin n) :
    Formalism.REAL.Amat l p b - Formalism.REAL.Amat l q b =
      if b = p then l p else if b = q then -1 - l q else 0 := by
  simp only [Formalism.REAL.Amat, Matrix.of_apply]
  by_cases hbp : b = p
  · subst hbp
    have h1 : q ≠ b := by intro h; rw [h] at hpq; omega
    have h2 : ¬ q < b := by rw [Fin.lt_def]; omega
    simp [h1, h2]
  · by_cases hbq : b = q
    · subst hbq
      have h2 : p < b := by rw [Fin.lt_def]; omega
      have h3 : p ≠ b := Ne.symm hbp
      simp [hbp, h2, h3]
    · have e1 : p ≠ b := Ne.symm hbp
      have e2 : q ≠ b := Ne.symm hbq
      simp only [e1, e2, hbp, hbq, if_false]
      have : (p < b ↔ q < b) := by
        rw [Fin.lt_def, Fin.lt_def]
        have : b.val ≠ p.val := fun h => hbp (Fin.ext h)
        have : b.val ≠ q.val := fun h => hbq (Fin.ext h)
        omega
      by_cases h : q < b
      · simp [h, this.mpr h]
      · simp [h, mt this.mp h]

/- English proof (translation)
Establish `hne : p ≠ q` using `by intro h; rw [h] at hpq; omega`. Simplify using `only [Formalism.REAL.Amat, Matrix.of_apply, Function.comp_apply]`. Distinguish the cases in `hap : a = p`. Substitute `hap` using the available equality. Establish `h2 : a < q` using `by rw [Fin.lt_def]; omega`.

Simplify using `[hne, h2]`. Distinguish the cases in `haq : a = q`. Substitute `haq` using the available equality. Establish `h1 : ¬ a < p` using `by rw [Fin.lt_def]; omega`. Simplify using `[hap, h1, Equiv.swap_apply_right]`.

Simplify using `only [hap, haq, if_false]`. Establish `: (a < p ↔ a < q)`. Rewrite using `[Fin.lt_def, Fin.lt_def]`. Establish `: a.val ≠ p.val` using `fun h => hap (Fin.ext h)`. Establish `: a.val ≠ q.val` using `fun h => haq (Fin.ext h)`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : a < p`. Simplify using `[h, this.mp h]`. Simplify using `[h, mt this.mpr h]`.
-/
theorem coldiff {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (a : Fin n) :
    Formalism.REAL.Amat (l ∘ Equiv.swap p q) a p - Formalism.REAL.Amat (l ∘ Equiv.swap p q) a q =
      if a = p then l q + 1 else if a = q then - l p else 0 := by
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  simp only [Formalism.REAL.Amat, Matrix.of_apply, Function.comp_apply]
  by_cases hap : a = p
  · subst hap
    have h2 : a < q := by rw [Fin.lt_def]; omega
    simp [hne, h2]
  · by_cases haq : a = q
    · subst haq
      have h1 : ¬ a < p := by rw [Fin.lt_def]; omega
      simp [hap, h1, Equiv.swap_apply_right]
    · simp only [hap, haq, if_false]
      have : (a < p ↔ a < q) := by
        rw [Fin.lt_def, Fin.lt_def]
        have : a.val ≠ p.val := fun h => hap (Fin.ext h)
        have : a.val ≠ q.val := fun h => haq (Fin.ext h)
        omega
      by_cases h : a < p
      · simp [h, this.mp h]
      · simp [h, mt this.mpr h]

/- English proof (translation)
Simplify using `only [Formalism.REAL.Amat, Matrix.of_apply, Function.comp_apply]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem amat_sub_swap {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (a b : Fin n) :
    Formalism.REAL.Amat l a b - Formalism.REAL.Amat (l ∘ Equiv.swap p q) a b =
      if a = b then l a - l (Equiv.swap p q a) else 0 := by
  simp only [Formalism.REAL.Amat, Matrix.of_apply, Function.comp_apply]
  split_ifs <;> ring

/- English proof (translation)
Simplify using `[vecMul, dotProduct, Pi.single_apply, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem w_vecMul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (b : Fin n) :
    ((Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) ᵥ* M) b = M p b - M q b := by
  simp [vecMul, dotProduct, Pi.single_apply, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[mulVec, dotProduct, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem w_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (a : Fin n) :
    (M *ᵥ (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ)) a = M a p - M a q := by
  simp [mulVec, dotProduct, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Establish `hne : p ≠ q` using `by intro h; rw [h] at hpq; omega`. Rewrite using `[sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul, mul_vecMulVec]`. Use extensionality with `a b`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]`. Rewrite using `[w_vecMul, w_mulVec, rowdiff l p q hpq, coldiff l p q hpq]`.

Establish `hd` using `amat_sub_swap l p q a b`. Rewrite using `[← sub_eq_zero]`. Establish `key : (if a = b then l a - l (Equiv.swap p q a) else 0) - t * ((Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a * (if b = p then l p else if b = q then -1 - l q else 0)) + t * ((if a = p then l q + 1 else if a = q then - l p else 0) * (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) b) = …`. Simplify using `only [Pi.sub_apply, Pi.single_apply]`. Establish `hqp : q ≠ p` using `Ne.symm hne`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Distinguish the cases in `hap : a = p`. Substitute `hap` using the available equality. Simplify using `[hne]`.

Take the linear combination `-ht`. Distinguish the cases in `haq : a = q`. Substitute `haq` using the available equality. Simplify using `[hqp, Equiv.swap_apply_right]`. Take the linear combination `ht`.

Simplify using `[hap, haq, Equiv.swap_apply_of_ne_of_ne hap haq]`. Apply the tactic sequence `by_cases hap : a = p <;> by_cases haq : a = q <;> by_cases hbp : b = p <;> by_cases hbq : b = q <;> (try subst hap) <;> (try subst haq) <;> (try subst hbp) <;> (try subst hbq) <;>`. Apply the tactic sequence `simp_all <;> first | ring | linear_combination ht | linear_combination -ht | linear_combination (2 : ℂ) * ht | linear_combination (-2 : ℂ) * ht`. Take the linear combination `key + hd`.
-/
theorem amat_swap_semiconj {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1)
    (t : ℂ) (ht : t * (l p - l q - 1) = l p - l q) :
    (1 - t • vecMulVec (Pi.single p 1 - Pi.single q 1) (Pi.single p 1 - Pi.single q 1)) * Formalism.REAL.Amat l =
      Formalism.REAL.Amat (l ∘ Equiv.swap p q) *
        (1 - t • vecMulVec (Pi.single p 1 - Pi.single q 1) (Pi.single p 1 - Pi.single q 1)) := by
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  rw [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul, mul_vecMulVec]
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  rw [w_vecMul, w_mulVec, rowdiff l p q hpq, coldiff l p q hpq]
  have hd := amat_sub_swap l p q a b
  rw [← sub_eq_zero]
  have key : (if a = b then l a - l (Equiv.swap p q a) else 0) -
      t * ((Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a *
        (if b = p then l p else if b = q then -1 - l q else 0)) +
      t * ((if a = p then l q + 1 else if a = q then - l p else 0) *
        (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) b) = 0 := by
    simp only [Pi.sub_apply, Pi.single_apply]
    have hqp : q ≠ p := Ne.symm hne
    by_cases hab : a = b
    · subst hab
      by_cases hap : a = p
      · subst hap; simp [hne]; linear_combination -ht
      · by_cases haq : a = q
        · subst haq; simp [hqp, Equiv.swap_apply_right]; linear_combination ht
        · simp [hap, haq, Equiv.swap_apply_of_ne_of_ne hap haq]
    · by_cases hap : a = p <;> by_cases haq : a = q <;> by_cases hbp : b = p <;> by_cases hbq : b = q <;>
        (try subst hap) <;> (try subst haq) <;> (try subst hbp) <;> (try subst hbq) <;>
        simp_all <;> first | ring | linear_combination ht | linear_combination -ht | linear_combination (2 : ℂ) * ht | linear_combination (-2 : ℂ) * ht
  linear_combination key + hd

/- English proof (translation)
Use `set t : ℂ := (l p - l q) / (l p - l q - 1) with ht_def`. Establish `ht : t * (l p - l q - 1) = l p - l q` using `by rw [ht_def]; field_simp`. Use `set w : Fin n → ℂ := Pi.single p 1 - Pi.single q 1 with hw`. Establish `hne : p ≠ q` using `by intro h; rw [h] at hpq; omega`. Establish `hsum : ∑ c, w c = 0` using `by simp [hw, Finset.sum_sub_distrib]`.

Use `set Q : Matrix (Fin n) (Fin n) ℂ := 1 - t • vecMulVec w w with hQ_def`. Establish `hQ : SemiconjBy Q (Formalism.REAL.Amat l) (Formalism.REAL.Amat (l ∘ Equiv.swap p q))` using `amat_swap_semiconj l p q hpq t ht`. Establish `hk` using `hQ.pow_right k`. Establish `hl : (fun _ => (1 : ℂ)) ᵥ* Q = fun _ => 1`. Use function extensionality and compare the values at `b`.

Simplify using `only [hQ_def, vecMul_sub, vecMul_one, vecMul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Establish `: ((fun _ => (1 : ℂ)) ᵥ* vecMulVec w w) b = 0`. Simplify using `[vecMul, dotProduct, vecMulVec_apply, ← Finset.sum_mul, hsum]`. Rewrite using `[this, mul_zero, sub_zero]`. Establish `hr : Q *ᵥ (fun _ => (1 : ℂ)) = fun _ => 1`.

Use function extensionality and compare the values at `a`. Simplify using `only [hQ_def, sub_mulVec, one_mulVec, Pi.sub_apply]`. Establish `: ((t • vecMulVec w w) *ᵥ (fun _ => (1 : ℂ))) a = 0`. Simplify using `[mulVec, dotProduct, vecMulVec_apply, ← Finset.mul_sum, hsum]`. Rewrite using `[this, sub_zero]`.

Rewrite using `[tot_eq, tot_eq]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mulVec_mulVec]`. Use `_ = (fun _ => (1 : ℂ)) ⬝ᵥ ((Q * Formalism.REAL.Amat l ^ k) *ᵥ fun _ => 1) := by rw [hk.eq]`. Use `_ = (fun _ => (1 : ℂ)) ⬝ᵥ (Q *ᵥ (Formalism.REAL.Amat l ^ k *ᵥ fun _ => 1)) := by rw [mulVec_mulVec]`.

Use `_ = ((fun _ => (1 : ℂ)) ᵥ* Q) ⬝ᵥ (Formalism.REAL.Amat l ^ k *ᵥ fun _ => 1) := dotProduct_mulVec _ _ _`. Use `_ = _ := by rw [hl]`.
-/
theorem tot_swap_of {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1)
    (hd : l p - l q - 1 ≠ 0) (k : ℕ) :
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  set t : ℂ := (l p - l q) / (l p - l q - 1) with ht_def
  have ht : t * (l p - l q - 1) = l p - l q := by rw [ht_def]; field_simp
  set w : Fin n → ℂ := Pi.single p 1 - Pi.single q 1 with hw
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  have hsum : ∑ c, w c = 0 := by simp [hw, Finset.sum_sub_distrib]
  set Q : Matrix (Fin n) (Fin n) ℂ := 1 - t • vecMulVec w w with hQ_def
  have hQ : SemiconjBy Q (Formalism.REAL.Amat l) (Formalism.REAL.Amat (l ∘ Equiv.swap p q)) :=
    amat_swap_semiconj l p q hpq t ht
  have hk := hQ.pow_right k
  have hl : (fun _ => (1 : ℂ)) ᵥ* Q = fun _ => 1 := by
    funext b
    simp only [hQ_def, vecMul_sub, vecMul_one, vecMul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have : ((fun _ => (1 : ℂ)) ᵥ* vecMulVec w w) b = 0 := by
      simp [vecMul, dotProduct, vecMulVec_apply, ← Finset.sum_mul, hsum]
    rw [this, mul_zero, sub_zero]
  have hr : Q *ᵥ (fun _ => (1 : ℂ)) = fun _ => 1 := by
    funext a
    simp only [hQ_def, sub_mulVec, one_mulVec, Pi.sub_apply]
    have : ((t • vecMulVec w w) *ᵥ (fun _ => (1 : ℂ))) a = 0 := by
      simp [mulVec, dotProduct, vecMulVec_apply, ← Finset.mul_sum, hsum]
    rw [this, sub_zero]
  rw [tot_eq, tot_eq]
  calc (fun _ => (1 : ℂ)) ⬝ᵥ (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k *ᵥ fun _ => 1)
      = (fun _ => (1 : ℂ)) ⬝ᵥ (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k *ᵥ (Q *ᵥ fun _ => 1)) := by rw [hr]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ ((Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k * Q) *ᵥ fun _ => 1) := by
        rw [mulVec_mulVec]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ ((Q * Formalism.REAL.Amat l ^ k) *ᵥ fun _ => 1) := by rw [hk.eq]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ (Q *ᵥ (Formalism.REAL.Amat l ^ k *ᵥ fun _ => 1)) := by rw [mulVec_mulVec]
    _ = ((fun _ => (1 : ℂ)) ᵥ* Q) ⬝ᵥ (Formalism.REAL.Amat l ^ k *ᵥ fun _ => 1) := dotProduct_mulVec _ _ _
    _ = _ := by rw [hl]

/- English proof (translation)
Distinguish the cases in `hd : l p - l q - 1 = 0`. Establish `hne : p ≠ q` using `by intro h; rw [h] at hpq; omega`. Establish `hd' : (l ∘ Equiv.swap p q) p - (l ∘ Equiv.swap p q) q - 1 ≠ 0`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Introduce `h`.

Apply `two_ne_zero (α := ℂ)` to reduce the goal to its premises. Take the linear combination `-h - hd`. Use `tot_swap_of (l ∘ Equiv.swap p q) p q hpq hd' k` as an intermediate fact. Establish `hinv : (l ∘ Equiv.swap p q) ∘ Equiv.swap p q = l`. Use function extensionality and compare the values at `a`.

Simplify using `[Equiv.swap_apply_self]`. Rewrite `this` using `[hinv]`. Conclude with `this.symm`. Conclude with `tot_swap_of l p q hpq hd k`.
-/
theorem tot_swap {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (k : ℕ) :
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  by_cases hd : l p - l q - 1 = 0
  · have hne : p ≠ q := by intro h; rw [h] at hpq; omega
    have hd' : (l ∘ Equiv.swap p q) p - (l ∘ Equiv.swap p q) q - 1 ≠ 0 := by
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      intro h; apply two_ne_zero (α := ℂ); linear_combination -h - hd
    have := tot_swap_of (l ∘ Equiv.swap p q) p q hpq hd' k
    have hinv : (l ∘ Equiv.swap p q) ∘ Equiv.swap p q = l := by
      funext a; simp [Equiv.swap_apply_self]
    rw [hinv] at this
    exact this.symm
  · exact tot_swap_of l p q hpq hd k

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Establish `: s = 1` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Introduce `l k`.

Both sides reduce to the same expression. Consider the case `succ m`. Establish `hs : s ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)`. Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ m]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Introduce `l k`. Conclude with `tot_swap l i.castSucc i.succ (by simp) k`.

Consider the case `one => intro l k`. Both sides reduce to the same expression. Consider the case `mul x y _ _ hx hy`. Introduce `l k`. Establish `hc : l ∘ ⇑(x * y) = (l ∘ ⇑x) ∘ ⇑y` using `by ext c; simp`.

Rewrite using `[hc, hy (l ∘ ⇑x) k, hx l k]`.
-/
theorem tot_perm {n : ℕ} (s : Equiv.Perm (Fin n)) : ∀ (l : Fin n → ℂ) (k : ℕ),
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ s) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  cases n with
  | zero =>
    have : s = 1 := Subsingleton.elim _ _
    subst this; intro l k; rfl
  | succ m =>
    have hs : s ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ m]; trivial
    induction hs using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro l k
      exact tot_swap l i.castSucc i.succ (by simp) k
    | one => intro l k; rfl
    | mul x y _ _ hx hy =>
      intro l k
      have hc : l ∘ ⇑(x * y) = (l ∘ ⇑x) ∘ ⇑y := by ext c; simp
      rw [hc, hy (l ∘ ⇑x) k, hx l k]

/- English proof (translation)
Introduce `n χ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `t k`. Unfold `gelfVal`. Establish `e : (fun c => χ c + t + ((n : ℂ) - 1) / 2) = fun c => (χ c + ((n : ℂ) - 1) / 2) + t`.

Use function extensionality and compare the values at `c`. Expand and normalize the polynomial expressions, which then agree. Use `set A := Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2)`. Establish `hM : (A + t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ k = ∑ j ∈ range (k + 1), ((k.choose j : ℂ) * t ^ (k - j)) • A ^ j`. Rewrite using `[(Commute.smul_right (Commute.one_right A) t).add_pow]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_pow, one_pow, Matrix.mul_smul, mul_one, ← Nat.cast_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Rewrite using `[e, amat_add_const, hM]`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]`. Simplify using `only [Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm (s := range (k + 1))]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Conclude with `Finset.sum_comm`. Simplify using `[gelfVal, Matrix.one_apply]`. Introduce `s k`.

Unfold `gelfVal`. Establish `e : (fun c => (χ ∘ s) c + ((n : ℂ) - 1) / 2) = (fun c => χ c + ((n : ℂ) - 1) / 2) ∘ s` using `rfl`. Rewrite using `[e, tot_perm]`.
-/
theorem gelfVal_shift_symm : ∀ (n : ℕ) (χ : Fin n → ℂ), (∀ (t : ℂ) (k : ℕ), gelfVal (fun a => χ a + t) k = ∑ j ∈ range (k + 1), (k.choose j : ℂ) * t ^ (k - j) * gelfVal χ j) ∧ gelfVal χ 0 = n ∧ ∀ (s : Equiv.Perm (Fin n)) (k : ℕ), gelfVal (χ ∘ s) k = gelfVal χ k := by
  intro n χ
  refine ⟨?_, ?_, ?_⟩
  · intro t k
    unfold gelfVal
    have e : (fun c => χ c + t + ((n : ℂ) - 1) / 2) = fun c => (χ c + ((n : ℂ) - 1) / 2) + t := by
      funext c; ring
    set A := Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2)
    have hM : (A + t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ k =
        ∑ j ∈ range (k + 1), ((k.choose j : ℂ) * t ^ (k - j)) • A ^ j := by
      rw [(Commute.smul_right (Commute.one_right A) t).add_pow]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_pow, one_pow, Matrix.mul_smul, mul_one, ← Nat.cast_comm, ← nsmul_eq_mul,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [e, amat_add_const, hM]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := range (k + 1))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.sum_comm
  · simp [gelfVal, Matrix.one_apply]
  · intro s k
    unfold gelfVal
    have e : (fun c => (χ ∘ s) c + ((n : ℂ) - 1) / 2) = (fun c => χ c + ((n : ℂ) - 1) / 2) ∘ s := rfl
    rw [e, tot_perm]

end GlobalTheory.GelfValSym
