import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CoreFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable

noncomputable section

namespace GlobalTheory.QuantumMinorCharts

open Equiv Formalism.REAL

section Capelli

variable {A : Type} [Ring A]

/- English proof (translation)
The claim follows from `| 0, f => by simp | n + 1, f => by have ih := comm_prod x (fun i : Fin n => f i.succ) have h0 : ∀ (y : A) (i : Fin n), Function.update f 0 y i.succ = f i.succ := fun y i => Function.update_of_ne (Fin.succ_ne_zero i) _ _ have h1 : ∀ (y : A) (k : Fin n), (fun i : Fin n => Function. …`.
-/
theorem comm_prod (x : A) : ∀ {n : ℕ} (f : Fin n → A),
    x * (List.ofFn f).prod - (List.ofFn f).prod * x =
      ∑ k, (List.ofFn (Function.update f k (x * f k - f k * x))).prod
  | 0, f => by simp
  | n + 1, f => by
    have ih := comm_prod x (fun i : Fin n => f i.succ)
    have h0 : ∀ (y : A) (i : Fin n), Function.update f 0 y i.succ = f i.succ :=
      fun y i => Function.update_of_ne (Fin.succ_ne_zero i) _ _
    have h1 : ∀ (y : A) (k : Fin n), (fun i : Fin n => Function.update f k.succ y i.succ) =
        Function.update (fun i : Fin n => f i.succ) k y := by
      intro y k
      funext i
      by_cases h : i = k
      · subst h; simp
      · rw [Function.update_of_ne h, Function.update_of_ne (fun e => h (Fin.succ_injective _ e))]
    have h2 : ∀ (y : A) (k : Fin n), Function.update f k.succ y 0 = f 0 :=
      fun y k => Function.update_of_ne (Fin.succ_ne_zero k).symm _ _
    rw [Fin.sum_univ_succ]
    simp only [List.ofFn_succ, List.prod_cons, h0, h1, h2, Function.update_self]
    rw [← Finset.mul_sum, ← ih]
    noncomm_ring

/- English proof (translation)
The claim follows from `(MultilinearMap.mkPiAlgebraFin ℤ n A).map_update_sub f k y z`.
-/
theorem prod_update_sub {n : ℕ} (f : Fin n → A) (k : Fin n) (y z : A) :
    (List.ofFn (Function.update f k (y - z))).prod =
      (List.ofFn (Function.update f k y)).prod - (List.ofFn (Function.update f k z)).prod :=
  (MultilinearMap.mkPiAlgebraFin ℤ n A).map_update_sub f k y z

/- English proof (translation)
The claim follows from `(MultilinearMap.mkPiAlgebraFin ℤ n A).map_update_zero f k`.
-/
theorem prod_update_zero {n : ℕ} (f : Fin n → A) (k : Fin n) :
    (List.ofFn (Function.update f k 0)).prod = 0 :=
  (MultilinearMap.mkPiAlgebraFin ℤ n A).map_update_zero f k

/- English proof (translation)
The claim follows from `| 0, k, _, _, _, _, _, _ => k.elim0 | n + 1, k, f₁, f₂, f₃, f₄, h, hr => by induction k using Fin.cases with | zero => have hh : ∀ i : Fin n, f₂ i.succ.succ = f₁ i.succ.succ ∧ f₃ i.succ.succ = f₁ i.succ.succ ∧ f₄ i.succ.succ = f₁ i.succ.succ := fun i => h _ (Fin.succ_ne_zero _) ( …`.
-/
theorem prod_adj : ∀ {n : ℕ} (k : Fin n) (f₁ f₂ f₃ f₄ : Fin (n + 1) → A),
    (∀ i, i ≠ k.castSucc → i ≠ k.succ → f₂ i = f₁ i ∧ f₃ i = f₁ i ∧ f₄ i = f₁ i) →
    f₁ k.castSucc * f₁ k.succ + f₂ k.castSucc * f₂ k.succ
      - (f₃ k.castSucc * f₃ k.succ + f₄ k.castSucc * f₄ k.succ) = 0 →
    (List.ofFn f₁).prod + (List.ofFn f₂).prod - ((List.ofFn f₃).prod + (List.ofFn f₄).prod) = 0
  | 0, k, _, _, _, _, _, _ => k.elim0
  | n + 1, k, f₁, f₂, f₃, f₄, h, hr => by
    induction k using Fin.cases with
    | zero =>
      have hh : ∀ i : Fin n, f₂ i.succ.succ = f₁ i.succ.succ ∧ f₃ i.succ.succ = f₁ i.succ.succ ∧
          f₄ i.succ.succ = f₁ i.succ.succ := fun i =>
        h _ (Fin.succ_ne_zero _) (fun e => Fin.succ_ne_zero _ (Fin.succ_injective _ e))
      simp only [List.ofFn_succ, List.prod_cons, fun i => (hh i).1, fun i => (hh i).2.1, fun i => (hh i).2.2]
      have := congrArg (· * (List.ofFn fun i : Fin n => f₁ i.succ.succ).prod) hr
      simp only [Fin.castSucc_zero, zero_mul] at this
      rw [← this]
      noncomm_ring
    | succ k =>
      have ih := prod_adj k (fun i => f₁ i.succ) (fun i => f₂ i.succ) (fun i => f₃ i.succ) (fun i => f₄ i.succ)
        (fun i h1 h2 => h _ (by rw [← Fin.succ_castSucc]; exact fun e => h1 (Fin.succ_injective _ e))
          (fun e => h2 (Fin.succ_injective _ e))) (by simpa only [Fin.succ_castSucc] using hr)
      obtain ⟨e2, e3, e4⟩ := h 0 (by rw [← Fin.succ_castSucc]; exact (Fin.succ_ne_zero _).symm)
        (Fin.succ_ne_zero _).symm
      rw [List.ofFn_succ (f := f₁), List.ofFn_succ (f := f₂), List.ofFn_succ (f := f₃), List.ofFn_succ (f := f₄)]
      simp only [List.prod_cons, e2, e3, e4]
      have := congrArg (f₁ 0 * ·) ih
      simp only [mul_zero] at this
      rw [← this]
      noncomm_ring

variable [Algebra ℂ A] {n : ℕ}

def GlRel (e : Fin n → Fin n → A) : Prop :=
  ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0)

/- English proof (translation)
Establish `h` using `he p q i j`. Establish `hc` using `Algebra.commutes u (e p q)`. Unfold `Tm`. Establish `: e p q * ((if i = j then algebraMap ℂ A u else 0) + e i j) - ((if i = j then algebraMap ℂ A u else 0) + e i j) * e p q = e p q * e i j - e i j * e p q` using `by split_ifs`. Rewrite using `[mul_add, add_mul, hc]`.

Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules. Rewrite using `[this, h]`. Apply the tactic sequence `by_cases h1 : q = i <;> by_cases h2 : j = p`. Substitute `h1 h2` using the available equality.

Simplify using `[eq_comm]`. Substitute `h1` using the available equality. Simplify using `[h2, Ne.symm h2]`. Substitute `h2` using the available equality. Simplify using `[h1, Ne.symm h1]`.

Simplify using `[h1, h2]`.
-/
theorem comm_Tm {e : Fin n → Fin n → A} (he : GlRel e) (u : ℂ) (p q i j : Fin n) :
    e p q * Tm e u i j - Tm e u i j * e p q = (if q = i then Tm e u p j else 0) - (if j = p then Tm e u i q else 0) := by
  have h := he p q i j
  have hc := Algebra.commutes u (e p q)
  unfold Tm
  have : e p q * ((if i = j then algebraMap ℂ A u else 0) + e i j) - ((if i = j then algebraMap ℂ A u else 0) + e i j) * e p q
      = e p q * e i j - e i j * e p q := by
    split_ifs
    · rw [mul_add, add_mul, hc]; abel
    · simp
  rw [this, h]
  by_cases h1 : q = i <;> by_cases h2 : j = p
  · subst h1 h2; simp [eq_comm]
  · subst h1; simp [h2, Ne.symm h2]
  · subst h2; simp [h1, Ne.symm h1]
  · simp [h1, h2]

/- English proof (translation)
Unfold `Tm`. Use `split_ifs`. Rewrite using `[map_sub, map_one]`. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules.
-/
theorem Tm_sub_one (e : Fin n → Fin n → A) (u : ℂ) (i j : Fin n) :
    Tm e (u - 1) i j = Tm e u i j - if i = j then 1 else 0 := by
  unfold Tm
  split_ifs
  · rw [map_sub, map_one]; abel
  · simp

/- English proof (translation)
Establish `key : ∀ p q i j, Tm e v p q * Tm e v i j - Tm e v i j * Tm e v p q = (if q = i then Tm e v p j else 0) - (if j = p then Tm e v i q else 0)`. Introduce `p q i j`. Rewrite using `[← comm_Tm he v p q i j]`. Establish `hc` using `Algebra.commutes v (Tm e v i j)`. Use `conv_lhs => rw [show Tm e v p q = (if p = q then algebraMap ℂ A v else 0) + e p q from rfl]`.

Use `split_ifs`. Rewrite using `[mul_add, add_mul, hc]`. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules. Establish `h1` using `key a c b d`.

Establish `h2` using `key a d b c`. Simplify using `only [Tm_sub_one, mul_sub, mul_ite, mul_one, mul_zero]`. Rewrite using `[eq_add_of_sub_eq h1, eq_add_of_sub_eq h2]`. Simplify using `only [@eq_comm _ c b, @eq_comm _ d a, @eq_comm _ d b, @eq_comm _ c a]`. Normalize the expressions using the abelian group laws.
-/
theorem Tm_rel {e : Fin n → Fin n → A} (he : GlRel e) (v : ℂ) (a b c d : Fin n) :
    Tm e v a c * Tm e (v - 1) b d + Tm e v a d * Tm e (v - 1) b c
      - (Tm e v b c * Tm e (v - 1) a d + Tm e v b d * Tm e (v - 1) a c) = 0 := by
  have key : ∀ p q i j, Tm e v p q * Tm e v i j - Tm e v i j * Tm e v p q =
      (if q = i then Tm e v p j else 0) - (if j = p then Tm e v i q else 0) := by
    intro p q i j
    rw [← comm_Tm he v p q i j]
    have hc := Algebra.commutes v (Tm e v i j)
    conv_lhs => rw [show Tm e v p q = (if p = q then algebraMap ℂ A v else 0) + e p q from rfl]
    split_ifs
    · rw [mul_add, add_mul, hc]; abel
    · simp
  have h1 := key a c b d
  have h2 := key a d b c
  simp only [Tm_sub_one, mul_sub, mul_ite, mul_one, mul_zero]
  rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2]
  simp only [@eq_comm _ c b, @eq_comm _ d a, @eq_comm _ d b, @eq_comm _ c a]
  abel

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qminor_def (e : Fin n → Fin n → A) {t : ℕ} (I J : Fin t → Fin n) (u : ℂ) :
    qminor e I J u = ∑ σ : Perm (Fin t), ((Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin t => Tm e (u - (k : ℕ)) (I (σ k)) (J k)).prod := rfl

/- English proof (translation)
Rewrite using `[qminor_def]`. Use `Finset.sum_involution (fun σ _ => swap p q * σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_` and prove the remaining obligations. Introduce `σ _`. Establish `: ∀ k, I ((swap p q * σ) k) = I (σ k)` using `fun k => by`. Rewrite using `[Perm.mul_apply]`.

Conclude with `apply_swap_eq_self h _`. Simplify using `only [this]`. Simplify using `[Perm.sign_swap hpq]`. Introduce `σ _ _ hs`. Conclude with `hpq (swap_eq_one_iff.1 (mul_eq_right.1 hs))`.

Introduce `σ _`. Simplify using `[← mul_assoc]`.
-/
theorem qminor_rows (e : Fin n → Fin n → A) {t : ℕ} (I J : Fin t → Fin n) (u : ℂ) {p q : Fin t} (hpq : p ≠ q)
    (h : I p = I q) : qminor e I J u = 0 := by
  rw [qminor_def]
  refine Finset.sum_involution (fun σ _ => swap p q * σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro σ _
    have : ∀ k, I ((swap p q * σ) k) = I (σ k) := fun k => by
      rw [Perm.mul_apply]; exact apply_swap_eq_self h _
    simp only [this]
    simp [Perm.sign_swap hpq]
  · intro σ _ _ hs
    exact hpq (swap_eq_one_iff.1 (mul_eq_right.1 hs))
  · intro σ _
    simp [← mul_assoc]

/- English proof (translation)
Establish `hk : k.castSucc ≠ k.succ` using `(Fin.castSucc_lt_succ).ne`. Rewrite using `[eq_neg_iff_add_eq_zero, qminor_def, qminor_def, ← Finset.sum_add_distrib]`. Use `Finset.sum_involution (fun σ _ => σ * swap k.castSucc k.succ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_` and prove the remaining obligations. Introduce `σ _`. Use `prod_adj k (fun i : Fin (t + 1) => Tm e (u - (i : ℕ)) (I (σ i)) ((J ∘ swap k.castSucc k.succ) i)) (fun i : Fin (t + 1) => Tm e (u - (i : ℕ)) (I (σ i)) (J i)) (fun i : Fin (t + 1) => Tm e (u - (i : ℕ)) (I ((σ * swap k.castSucc k.succ) i)) ((J ∘ swap k.castSucc k.succ) i)) (fun i : …` as an intermediate fact.

Use `Tm_rel he (u - (k : ℕ)) (I (σ k.castSucc)) (I (σ k.succ)) (J k.succ) (J k.castSucc)` as an intermediate fact. Simplify using `only [Function.comp, Perm.mul_apply, swap_apply_left, swap_apply_right, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, ← sub_sub]`. Rewrite using `[← this]`. Use the proof step `abel)`. Establish `h2` using `congrArg (((Perm.sign σ : ℤ) : A) * ·) this`.

Simplify using `only [mul_zero] at h2`. Rewrite using `[← h2, Perm.sign_mul, Perm.sign_swap hk]`. Use `push_cast`. Use `noncomm_ring`. Introduce `σ _ _ hs`.

Conclude with `hk (swap_eq_one_iff.1 (mul_eq_left.1 hs))`. Introduce `σ _`. Simplify using `[mul_assoc]`.
-/
theorem qminor_adj {e : Fin n → Fin n → A} (he : GlRel e) {t : ℕ} (I J : Fin (t + 1) → Fin n) (u : ℂ) (k : Fin t) :
    qminor e I (J ∘ swap k.castSucc k.succ) u = - qminor e I J u := by
  have hk : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ).ne
  rw [eq_neg_iff_add_eq_zero, qminor_def, qminor_def, ← Finset.sum_add_distrib]
  refine Finset.sum_involution (fun σ _ => σ * swap k.castSucc k.succ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro σ _
    have := prod_adj k (fun i : Fin (t + 1) => Tm e (u - (i : ℕ)) (I (σ i)) ((J ∘ swap k.castSucc k.succ) i))
      (fun i : Fin (t + 1) => Tm e (u - (i : ℕ)) (I (σ i)) (J i))
      (fun i : Fin (t + 1) => Tm e (u - (i : ℕ)) (I ((σ * swap k.castSucc k.succ) i)) ((J ∘ swap k.castSucc k.succ) i))
      (fun i : Fin (t + 1) => Tm e (u - (i : ℕ)) (I ((σ * swap k.castSucc k.succ) i)) (J i))
      (fun i h1 h2 => by simp [swap_apply_of_ne_of_ne h1 h2])
      (by
        have := Tm_rel he (u - (k : ℕ)) (I (σ k.castSucc)) (I (σ k.succ)) (J k.succ) (J k.castSucc)
        simp only [Function.comp, Perm.mul_apply, swap_apply_left, swap_apply_right, Fin.val_castSucc, Fin.val_succ,
          Nat.cast_add, Nat.cast_one, ← sub_sub]
        rw [← this]; abel)
    have h2 := congrArg (((Perm.sign σ : ℤ) : A) * ·) this
    simp only [mul_zero] at h2
    rw [← h2, Perm.sign_mul, Perm.sign_swap hk]
    push_cast
    noncomm_ring
  · intro σ _ _ hs
    exact hk (swap_eq_one_iff.1 (mul_eq_left.1 hs))
  · intro σ _
    simp [mul_assoc]

/- English proof (translation)
Establish `hs : s ∈ Submonoid.closure (Set.range fun i : Fin t => swap i.castSucc i.succ)`. Rewrite using `[Perm.mclosure_swap_castSucc_succ]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx`.

Take `⟨k, rfl⟩` from `hx`. Introduce `J`. Rewrite using `[qminor_adj he, Perm.sign_swap (Fin.castSucc_lt_succ).ne]`. Simplify using the standard rewrite rules. Consider the case `one => intro J`.

Simplify using the standard rewrite rules. Consider the case `mul x y _ _ hx hy`. Introduce `J`. Rewrite using `[Perm.coe_mul, ← Function.comp_assoc, hy, hx, Perm.sign_mul, mul_comm (Perm.sign x)]`. Use `push_cast`.

Rewrite using `[mul_assoc]`.
-/
theorem qminor_perm {e : Fin n → Fin n → A} (he : GlRel e) {t : ℕ} (I : Fin (t + 1) → Fin n) (u : ℂ)
    (s : Perm (Fin (t + 1))) : ∀ J : Fin (t + 1) → Fin n,
    qminor e I (J ∘ s) u = ((Perm.sign s : ℤ) : A) * qminor e I J u := by
  have hs : s ∈ Submonoid.closure (Set.range fun i : Fin t => swap i.castSucc i.succ) := by
    rw [Perm.mclosure_swap_castSucc_succ]; trivial
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro J
    rw [qminor_adj he, Perm.sign_swap (Fin.castSucc_lt_succ).ne]
    simp
  | one => intro J; simp
  | mul x y _ _ hx hy =>
    intro J
    rw [Perm.coe_mul, ← Function.comp_assoc, hy, hx, Perm.sign_mul, mul_comm (Perm.sign x)]
    push_cast
    rw [mul_assoc]

/- English proof (translation)
Consider the cases of `t with`. Consider the case `zero => exact p.elim0`. Consider the case `succ t`. Establish `h1` using `qminor_perm he I u (swap p q) J`. Establish `h2 : J ∘ swap p q = J` using `funext fun k => apply_swap_eq_self h k`.

Rewrite `h1` using `[h2, Perm.sign_swap hpq]`. Establish `h3 : (2 : ℂ) • qminor e I J u = 0`. Rewrite using `[two_smul]`. Use `nth_rewrite 1 [h1]`. Simplify using the standard rewrite rules.

Use `congrArg ((2 : ℂ)⁻¹ • ·) h3` as an intermediate fact. Simplify `this` using `[smul_smul]`.
-/
theorem qminor_cols {e : Fin n → Fin n → A} (he : GlRel e) {t : ℕ} (I J : Fin t → Fin n) (u : ℂ) {p q : Fin t}
    (hpq : p ≠ q) (h : J p = J q) : qminor e I J u = 0 := by
  cases t with
  | zero => exact p.elim0
  | succ t =>
    have h1 := qminor_perm he I u (swap p q) J
    have h2 : J ∘ swap p q = J := funext fun k => apply_swap_eq_self h k
    rw [h2, Perm.sign_swap hpq] at h1
    have h3 : (2 : ℂ) • qminor e I J u = 0 := by
      rw [two_smul]; nth_rewrite 1 [h1]; simp
    have := congrArg ((2 : ℂ)⁻¹ • ·) h3
    simpa [smul_smul] using this

/- English proof (translation)
Rewrite using `[show qdet e u = qminor e id id u from rfl]`. Simplify using `only [qminor_def, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← Int.cast_comm, mul_assoc, mul_assoc, ← mul_sub, ← mul_sub, comm_prod]`. Use `congr 1`.

Simplify using `only [comm_Tm he, prod_update_sub, Finset.sum_sub_distrib, id]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single (σ.symm q)]`. Use `congr 2`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `h : k = σ.symm q`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : σ k ≠ q` using `fun e => h (by rw [← e]; simp)`. Simplify using `[Function.update_of_ne h, Function.update_of_ne h']`.

Introduce `k _ h`. Establish `h' : q ≠ σ k` using `fun e => h (by rw [e]; simp)`. Rewrite using `[if_neg h', prod_update_zero]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single p]`.

Use `congr 2`. Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = p`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Function.update_of_ne h]`. Introduce `k _ h`. Rewrite using `[if_neg h, prod_update_zero]`. Simplify using the standard rewrite rules.
-/
theorem comm_qdet_eq {e : Fin n → Fin n → A} (he : GlRel e) (u : ℂ) (p q : Fin n) :
    e p q * qdet e u - qdet e u * e p q =
      qminor e (Function.update id q p) id u - qminor e id (Function.update id p q) u := by
  rw [show qdet e u = qminor e id id u from rfl]
  simp only [qminor_def, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← Int.cast_comm, mul_assoc, mul_assoc, ← mul_sub, ← mul_sub, comm_prod]
  congr 1
  simp only [comm_Tm he, prod_update_sub, Finset.sum_sub_distrib, id]
  congr 1
  · rw [Finset.sum_eq_single (σ.symm q)]
    · congr 2
      funext k
      by_cases h : k = σ.symm q
      · subst h; simp
      · have h' : σ k ≠ q := fun e => h (by rw [← e]; simp)
        simp [Function.update_of_ne h, Function.update_of_ne h']
    · intro k _ h
      have h' : q ≠ σ k := fun e => h (by rw [e]; simp)
      rw [if_neg h', prod_update_zero]
    · simp
  · rw [Finset.sum_eq_single p]
    · congr 2
      funext k
      by_cases h : k = p
      · subst h; simp
      · simp [Function.update_of_ne h]
    · intro k _ h
      rw [if_neg h, prod_update_zero]
    · simp

/- English proof (translation)
Rewrite using `[Commute, SemiconjBy, ← sub_eq_zero, comm_qdet_eq he]`. Distinguish the cases in `h : p = q`. Substitute `h` using the available equality. Establish `: Function.update (id : Fin n → Fin n) p p = id` using `Function.update_eq_self p id`. Rewrite using `[this, sub_self]`.

Rewrite using `[qminor_rows e _ _ u h (by simp [Function.update_of_ne h]), qminor_cols he _ _ u h (by simp [Function.update_of_ne (Ne.symm h)]), sub_self]`.
-/
theorem commute_gen_qdet {e : Fin n → Fin n → A} (he : GlRel e) (u : ℂ) (p q : Fin n) :
    Commute (e p q) (qdet e u) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, comm_qdet_eq he]
  by_cases h : p = q
  · subst h
    have : Function.update (id : Fin n → Fin n) p p = id := Function.update_eq_self p id
    rw [this, sub_self]
  · rw [qminor_rows e _ _ u h (by simp [Function.update_of_ne h]),
      qminor_cols he _ _ u h (by simp [Function.update_of_ne (Ne.symm h)]), sub_self]

/- English proof (translation)
Rewrite using `[show qdet e u = qminor e id id u from rfl, qminor_def]`. Use `Commute.sum_left _ _ _ fun σ _ => Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ ?_)` and prove the remaining obligations. Introduce `y hy`. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hy`. Unfold `Tm`.

Use `Commute.add_left ?_ (hx _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `Algebra.commutes _ _`. Conclude with `Commute.zero_left _`.
-/
theorem commute_qdet_of_gen {e : Fin n → Fin n → A} {x : A} (hx : ∀ i j, Commute (e i j) x) (u : ℂ) :
    Commute (qdet e u) x := by
  rw [show qdet e u = qminor e id id u from rfl, qminor_def]
  refine Commute.sum_left _ _ _ fun σ _ => Commute.mul_left (Int.cast_commute _ _) (Commute.list_prod_left _ _ ?_)
  intro y hy
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Tm
  refine Commute.add_left ?_ (hx _ _)
  split_ifs
  · exact Algebra.commutes _ _
  · exact Commute.zero_left _

end Capelli

section Lie

open GlobalTheory.CuspRep NumberField

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def mulL (x y : Lie E a) : Lie E a := Matrix.of.symm (Matrix.of x * Matrix.of y)

def lmul (x : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => mulL x y
      map_add' := fun y z => Matrix.mul_add (Matrix.of x) (Matrix.of y) (Matrix.of z)
      map_smul' := fun c y => Matrix.mul_smul (Matrix.of x) c (Matrix.of y) }

def rmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => mulL x y
      map_add' := fun x z => Matrix.add_mul (Matrix.of x) (Matrix.of z) (Matrix.of y)
      map_smul' := fun c x => Matrix.smul_mul c (Matrix.of x) (Matrix.of y) }

omit [IsTotallyComplex E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lmul_apply (x y : Lie E a) : lmul x y = mulL x y := rfl

omit [IsTotallyComplex E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rmul_apply (x y : Lie E a) : rmul y x = mulL x y := rfl

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `Matrix.mul_one (Matrix.of x)`.
-/
theorem mulL_one (x : Lie E a) : mulL x (oneL E a) = x := Matrix.mul_one (Matrix.of x)

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `Matrix.one_mul (Matrix.of x)`.
-/
theorem one_mulL (x : Lie E a) : mulL (oneL E a) x = x := Matrix.one_mul (Matrix.of x)

omit [IsTotallyComplex E] in
/- English proof (translation)
Establish `hc : Continuous fun y : Lie E a => (Matrix.of y).det` using `Continuous.matrix_det (A := fun y : Lie E a => Matrix.of y) continuous_id`. Establish `: invSet E a = (fun y : Lie E a => (Matrix.of y).det) ⁻¹' {z | IsUnit z}`. Use extensionality with `y`. Conclude with `Matrix.isUnit_iff_isUnit_det _`. Establish `ho : IsOpen (invSet E a)`.

Rewrite using `[this]`. Conclude with `Units.isOpen.preimage hc`. Conclude with `ho.mem_nhds hx`.
-/
theorem inv_nhds {x : Lie E a} (hx : IsUnit (Matrix.of x)) : invSet E a ∈ nhds x := by
  have hc : Continuous fun y : Lie E a => (Matrix.of y).det :=
    Continuous.matrix_det (A := fun y : Lie E a => Matrix.of y) continuous_id
  have : invSet E a = (fun y : Lie E a => (Matrix.of y).det) ⁻¹' {z | IsUnit z} := by
    ext y
    exact Matrix.isUnit_iff_isUnit_det _
  have ho : IsOpen (invSet E a) := by
    rw [this]; exact Units.isOpen.preimage hc
  exact ho.mem_nhds hx

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `isUnit_one`.
-/
theorem isUnit_oneL : IsUnit (Matrix.of (oneL E a)) := isUnit_one

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `e : Matrix.of (lmul x y) = Matrix.of x * Matrix.of y` using `rfl`. Simplify using `only [Function.comp]`. Unfold `chart`. Distinguish the cases in `hy : IsUnit (Matrix.of y)`.

Establish `hxy : IsUnit (Matrix.of (lmul x y))` using `e ▸ hx.mul hy`. Rewrite using `[dif_pos hy, dif_pos hxy, mul_assoc, ← map_mul]`. Use `congr 3`. Conclude with `Units.ext e.symm`. Establish `hxy : ¬ IsUnit (Matrix.of (lmul x y))`.

Rewrite using `[e]`. Conclude with `fun h => hy ((hx.mul_left_iff).1 h)`. Rewrite using `[dif_neg hy, dif_neg hxy]`.
-/
theorem chart_mul (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : IsUnit (Matrix.of x)) :
    chart φ (g * infGL E a hx.unit) = chart φ g ∘ lmul x := by
  funext y
  have e : Matrix.of (lmul x y) = Matrix.of x * Matrix.of y := rfl
  simp only [Function.comp]
  unfold chart
  by_cases hy : IsUnit (Matrix.of y)
  · have hxy : IsUnit (Matrix.of (lmul x y)) := e ▸ hx.mul hy
    rw [dif_pos hy, dif_pos hxy, mul_assoc, ← map_mul]
    congr 3
    exact Units.ext e.symm
  · have hxy : ¬ IsUnit (Matrix.of (lmul x y)) := by
      rw [e]; exact fun h => hy ((hx.mul_left_iff).1 h)
    rw [dif_neg hy, dif_neg hxy]

/- English proof (translation)
The claim follows from `((φ.2 g).contDiffAt (inv_nhds hx)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))`.
-/
theorem contDiffAt_chart (φ : Sm E a) (g : GA E a) {x : Lie E a} (hx : IsUnit (Matrix.of x)) :
    ContDiffAt ℝ 2 (chart φ.1 g) x :=
  ((φ.2 g).contDiffAt (inv_nhds hx)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))

/- English proof (translation)
Establish `h1 : chart (lieD Y φ.1) g x = lieD Y φ.1 (g * infGL E a hx.unit)` using `dif_pos hx`. Rewrite using `[h1]`. Unfold `lieD`. Establish `hd : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) x) (lmul x (oneL E a))`. Rewrite using `[lmul_apply, mulL_one]`.

Conclude with `((contDiffAt_chart φ g hx).differentiableAt (by norm_num)).hasFDerivAt`. Rewrite using `[chart_mul, (hd.comp _ (lmul x).hasFDerivAt).fderiv]`. Both sides reduce to the same expression.
-/
theorem chart_lieD (φ : Sm E a) (g : GA E a) (Y : Lie E a) {x : Lie E a} (hx : IsUnit (Matrix.of x)) :
    chart (lieD Y φ.1) g x = fderiv ℝ (chart φ.1 g) x (rmul Y x) := by
  have h1 : chart (lieD Y φ.1) g x = lieD Y φ.1 (g * infGL E a hx.unit) := dif_pos hx
  rw [h1]
  unfold lieD
  have hd : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) x) (lmul x (oneL E a)) := by
    rw [lmul_apply, mulL_one]
    exact ((contDiffAt_chart φ g hx).differentiableAt (by norm_num)).hasFDerivAt
  rw [chart_mul, (hd.comp _ (lmul x).hasFDerivAt).fderiv]
  rfl

/- English proof (translation)
Establish `h1 : chart (lieD Y φ.1) g =ᶠ[nhds (oneL E a)] fun x => fderiv ℝ (chart φ.1 g) x (rmul Y x)` using `by filter_upwards [inv_nhds (isUnit_oneL (E := E) (a := a))] with x hx`. Conclude with `chart_lieD φ g Y hx`. Establish `hd : DifferentiableAt ℝ (fderiv ℝ (chart φ.1 g)) (oneL E a)` using `((contDiffAt_chart φ g isUnit_oneL).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `h2` using `(hd.hasFDerivAt.clm_apply (rmul Y).hasFDerivAt).fderiv`. Use `show fderiv ℝ (chart (lieD Y φ.1) g) (oneL E a) X = _ + fderiv ℝ (chart φ.1 g) (oneL E a) (mulL X Y)`.

Rewrite using `[h1.fderiv_eq, h2]`. Simplify using `[rmul_apply, one_mulL, add_comm]`.
-/
theorem lieD_lieD (φ : Sm E a) (g : GA E a) (X Y : Lie E a) :
    lieD X (lieD Y φ.1) g = fderiv ℝ (fderiv ℝ (chart φ.1 g)) (oneL E a) X Y + lieD (mulL X Y) φ.1 g := by
  have h1 : chart (lieD Y φ.1) g =ᶠ[nhds (oneL E a)] fun x => fderiv ℝ (chart φ.1 g) x (rmul Y x) := by
    filter_upwards [inv_nhds (isUnit_oneL (E := E) (a := a))] with x hx
    exact chart_lieD φ g Y hx
  have hd : DifferentiableAt ℝ (fderiv ℝ (chart φ.1 g)) (oneL E a) :=
    ((contDiffAt_chart φ g isUnit_oneL).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 := (hd.hasFDerivAt.clm_apply (rmul Y).hasFDerivAt).fderiv
  show fderiv ℝ (chart (lieD Y φ.1) g) (oneL E a) X = _ + fderiv ℝ (chart φ.1 g) (oneL E a) (mulL X Y)
  rw [h1.fderiv_eq, h2]
  simp [rmul_apply, one_mulL, add_comm]

/- English proof (translation)
Use extensionality with `φ g`. Use `show lieD X (lieD Y φ.1) g - lieD Y (lieD X φ.1) g = lieD (mulL X Y) φ.1 g - lieD (mulL Y X) φ.1 g`. Establish `hs : IsSymmSndFDerivAt ℝ (chart φ.1 g) (oneL E a)` using `(contDiffAt_chart φ g isUnit_oneL).isSymmSndFDerivAt (by simp)`. Rewrite using `[lieD_lieD, lieD_lieD, hs X Y]`. Normalize the expressions using the abelian group laws.
-/
theorem lie_bracket (X Y : Lie E a) :
    lie E a X * lie E a Y - lie E a Y * lie E a X = lie E a (mulL X Y) - lie E a (mulL Y X) := by
  ext φ g
  show lieD X (lieD Y φ.1) g - lieD Y (lieD X φ.1) g = lieD (mulL X Y) φ.1 g - lieD (mulL Y X) φ.1 g
  have hs : IsSymmSndFDerivAt ℝ (chart φ.1 g) (oneL E a) :=
    (contDiffAt_chart φ g isUnit_oneL).isSymmSndFDerivAt (by simp)
  rw [lieD_lieD, lieD_lieD, hs X Y]
  abel

/- English proof (translation)
Establish `key : ∀ (i j k l : Fin a) (c d : Cinf E), lie E a (mulL (Matrix.single i j c) (Matrix.single k l d)) = if j = k then lieS E a i l (c * d) else 0`. Introduce `i j k l c d`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `congrArg (lie E a) (Matrix.single_mul_single_same c i j l d)`.

Conclude with `(congrArg (lie E a) (Matrix.single_mul_single_of_ne c i j k h d)).trans (map_zero _)`. Use `lie_bracket (E := E) (a := a) (Matrix.single i j c) (Matrix.single k l d)` as an intermediate fact. Rewrite `this` using `[key, key, mul_comm d c]`. Conclude with `this`.
-/
theorem lieS_bracket (i j k l : Fin a) (c d : Cinf E) :
    lieS E a i j c * lieS E a k l d - lieS E a k l d * lieS E a i j c =
      (if j = k then lieS E a i l (c * d) else 0) - (if l = i then lieS E a k j (c * d) else 0) := by
  have key : ∀ (i j k l : Fin a) (c d : Cinf E), lie E a (mulL (Matrix.single i j c) (Matrix.single k l d)) =
      if j = k then lieS E a i l (c * d) else 0 := by
    intro i j k l c d
    split_ifs with h
    · subst h
      exact congrArg (lie E a) (Matrix.single_mul_single_same c i j l d)
    · exact (congrArg (lie E a) (Matrix.single_mul_single_of_ne c i j k h d)).trans (map_zero _)
  have := lie_bracket (E := E) (a := a) (Matrix.single i j c) (Matrix.single k l d)
  rw [key, key, mul_comm d c] at this
  exact this

/- English proof (translation)
Unfold `Eop`. Simplify using `only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul]`. Use `module`.
-/
theorem Eop_bracket (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    Eop τ i j * Eop τ' k l - Eop τ' k l * Eop τ i j =
      (1 / 4 : ℂ) • ((lieS E a i j (atEmb τ 1) * lieS E a k l (atEmb τ' 1) - lieS E a k l (atEmb τ' 1) * lieS E a i j (atEmb τ 1))
        - Complex.I • (lieS E a i j (atEmb τ 1) * lieS E a k l (atEmb τ' Complex.I)
            - lieS E a k l (atEmb τ' Complex.I) * lieS E a i j (atEmb τ 1))
        - Complex.I • (lieS E a i j (atEmb τ Complex.I) * lieS E a k l (atEmb τ' 1)
            - lieS E a k l (atEmb τ' 1) * lieS E a i j (atEmb τ Complex.I))
        + (Complex.I * Complex.I) • (lieS E a i j (atEmb τ Complex.I) * lieS E a k l (atEmb τ' Complex.I)
            - lieS E a k l (atEmb τ' Complex.I) * lieS E a i j (atEmb τ Complex.I))) := by
  unfold Eop
  simp only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul]
  module

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Unfold `atEmb`. Rewrite using `[← Pi.single_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem atEmb_mul (τ : E →+* ℂ) (z w : ℂ) : atEmb τ z * atEmb τ w = atEmb τ (z * w) := by
  classical
  unfold atEmb
  rw [← Pi.single_mul]
  split_ifs <;> simp

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Unfold `atEmb`. Rewrite using `[← Pi.single_neg]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem atEmb_neg (τ : E →+* ℂ) (z : ℂ) : atEmb τ (-z) = - atEmb τ z := by
  classical
  unfold atEmb
  rw [← Pi.single_neg]
  split_ifs <;> simp

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Unfold `atEmb`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v = InfinitePlace.mk τ`. Substitute `hv` using the available equality. Simplify using `[Pi.single_eq_of_ne h]`.

Simplify using `[Pi.single_eq_of_ne hv]`.
-/
theorem atEmb_mul_of_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ ≠ InfinitePlace.mk τ') (z w : ℂ) :
    atEmb τ z * atEmb τ' w = 0 := by
  classical
  unfold atEmb
  funext v
  by_cases hv : v = InfinitePlace.mk τ
  · subst hv
    simp [Pi.single_eq_of_ne h]
  · simp [Pi.single_eq_of_ne hv]

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Unfold `atEmb`. Rewrite using `[← h]`. Use `congr 1`. Distinguish the cases in `h1 : (InfinitePlace.mk τ).embedding = τ`. Rewrite using `[if_pos h1, if_neg (fun e => hne (h1.symm.trans e))]`.

Establish `h2 : (InfinitePlace.mk τ).embedding = τ'`. Break down `InfinitePlace.embedding_mk_eq τ with e | e` into its components or cases. Conclude with `absurd e h1`. Break down `InfinitePlace.mk_eq_iff.1 h with e' | e'` into its components or cases. Conclude with `absurd e' hne`.

Conclude with `e.trans e'`. Rewrite using `[if_pos h2, if_neg h1, Complex.conj_conj]`.
-/
theorem atEmb_conj {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ = InfinitePlace.mk τ') (hne : τ ≠ τ') (w : ℂ) :
    atEmb τ' w = atEmb τ (starRingEnd ℂ w) := by
  unfold atEmb
  rw [← h]
  congr 1
  by_cases h1 : (InfinitePlace.mk τ).embedding = τ
  · rw [if_pos h1, if_neg (fun e => hne (h1.symm.trans e))]
  · have h2 : (InfinitePlace.mk τ).embedding = τ' := by
      rcases InfinitePlace.embedding_mk_eq τ with e | e
      · exact absurd e h1
      · rcases InfinitePlace.mk_eq_iff.1 h with e' | e'
        · exact absurd e' hne
        · exact e.trans e'
    rw [if_pos h2, if_neg h1, Complex.conj_conj]

/- English proof (translation)
Introduce `i j k l`. Rewrite using `[Eop_bracket]`. Simplify using `only [lieS_bracket, atEmb_mul, Complex.I_mul_I, mul_one, one_mul, atEmb_neg, map_neg]`. Unfold `Eop`. Apply the tactic sequence `split_ifs <;> module`.
-/
theorem glRel_Eop (τ : E →+* ℂ) : GlRel (Eop (a := a) τ) := by
  intro i j k l
  rw [Eop_bracket]
  simp only [lieS_bracket, atEmb_mul, Complex.I_mul_I, mul_one, one_mul, atEmb_neg, map_neg]
  unfold Eop
  split_ifs <;> module

/- English proof (translation)
Rewrite using `[Commute, SemiconjBy, ← sub_eq_zero, Eop_bracket]`. Distinguish the cases in `h : InfinitePlace.mk τ = InfinitePlace.mk τ'`. Simplify using `only [lieS_bracket]`. Simplify using `only [atEmb_conj h hne, atEmb_mul, Complex.I_mul_I, mul_one, one_mul, atEmb_neg, map_neg, map_one, Complex.conj_I, mul_neg, neg_neg]`. Apply the tactic sequence `split_ifs <;> module`.

Simplify using `[lieS_bracket, atEmb_mul_of_ne h]`.
-/
theorem commute_Eop {τ τ' : E →+* ℂ} (hne : τ ≠ τ') (i j k l : Fin a) : Commute (Eop τ i j) (Eop τ' k l) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, Eop_bracket]
  by_cases h : InfinitePlace.mk τ = InfinitePlace.mk τ'
  · simp only [lieS_bracket]
    simp only [atEmb_conj h hne, atEmb_mul, Complex.I_mul_I, mul_one, one_mul, atEmb_neg, map_neg,
      map_one, Complex.conj_I, mul_neg, neg_neg]
    split_ifs <;> module
  · simp [lieS_bracket, atEmb_mul_of_ne h]

/- English proof (translation)
Unfold `cap`. Use `commute_qdet_of_gen (fun i j => ?_) _` and prove the remaining obligations. Distinguish the cases in `h : τ = τ'`. Substitute `h` using the available equality. Conclude with `commute_gen_qdet (glRel_Eop τ) _ i j`.

Conclude with `(commute_qdet_of_gen (fun k l => (commute_Eop h i j k l).symm) _).symm`.
-/
theorem commute_cap (τ τ' : E →+* ℂ) (u v : ℂ) : Commute (cap (a := a) τ u) (cap τ' v) := by
  unfold cap
  refine commute_qdet_of_gen (fun i j => ?_) _
  by_cases h : τ = τ'
  · subst h
    exact commute_gen_qdet (glRel_Eop τ) _ i j
  · exact (commute_qdet_of_gen (fun k l => (commute_Eop h i j k l).symm) _).symm

end Lie

/- English proof (translation)
Unfold `GlobalTheory.CuspRep.Zalg at hz hz'`. Use `Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz' ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ', v, rfl⟩`. Use `(Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz ?_).symm` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, u, rfl⟩`.

Conclude with `commute_cap τ' τ v u`.
-/
theorem commute_of_mem_Zalg {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ}
    {z z' : Module.End ℂ ↥(GlobalTheory.CuspRep.Sm E a)} (hz : z ∈ GlobalTheory.CuspRep.Zalg E a) (hz' : z' ∈ GlobalTheory.CuspRep.Zalg E a) :
    Commute z z' := by
  unfold GlobalTheory.CuspRep.Zalg at hz hz'
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz' ?_
  rintro _ ⟨τ', v, rfl⟩
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz ?_).symm
  rintro _ ⟨τ, u, rfl⟩
  exact commute_cap τ' τ v u

end GlobalTheory.QuantumMinorCharts

end
