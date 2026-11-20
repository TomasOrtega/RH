import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

open Finset Matrix

noncomputable section

namespace GlobalTheory.Dec.GelfSepProof

open PowerSeries Matrix in

/- English proof (translation)
Establish `hA : ∀ a b, _root_.Formalism.REAL.Amat l a b = if a = b then l a else if a < b then -1 else 0`. Introduce `a b`. Unfold `_root_.Formalism.REAL.Amat`. Both sides reduce to the same expression. Use `set A := _root_.Formalism.REAL.Amat l with hAdef`.

Set `Y : Matrix (Fin n) (Fin n) (PowerSeries ℂ)` to `A.map (PowerSeries.C : ℂ → PowerSeries ℂ)`. Set `B : Matrix (Fin n) (Fin n) (PowerSeries ℂ)` to `Matrix.of fun a b => PowerSeries.mk fun k => (A ^ k) a b`. Establish `hB : (1 - (X : PowerSeries ℂ) • Y) * B = 1`. Rewrite using `[sub_mul, one_mul, smul_mul_assoc]`. Use extensionality with `a b k`.

Break down `k with _ | k` into its components or cases. Simplify using `[B, Matrix.one_apply]`. Apply the tactic sequence `simp [B, Y, Matrix.mul_apply, Matrix.one_apply, pow_succ', PowerSeries.coeff_succ_X_mul, map_sum] split_ifs <;> simp`. Set `c : Matrix (Fin n) (Fin 1) (PowerSeries ℂ)` to `replicateCol (Fin 1) 1`. Set `R : Matrix (Fin 1) (Fin n) (PowerSeries ℂ)` to `replicateRow (Fin 1) 1`.

Set `J : Matrix (Fin n) (Fin n) (PowerSeries ℂ)` to `Matrix.of fun _ _ => 1`. Set `U : Matrix (Fin n) (Fin 1) (PowerSeries ℂ)` to `-((X : PowerSeries ℂ) • (B * c))`. Establish `hcR : c * R = J`. Use extensionality with `a b`. Simplify using `[c, R, J, Matrix.mul_apply]`.

Establish `hBc : (1 - (X : PowerSeries ℂ) • Y) * (B * c) = c`. Rewrite using `[← Matrix.mul_assoc, hB, Matrix.one_mul]`. Establish `hfactor : (1 - (X : PowerSeries ℂ) • Y) * (1 + U * R) = 1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J`. Establish `hU : (1 - (X : PowerSeries ℂ) • Y) * U = -((X : PowerSeries ℂ) • c)` using `by show (1 - (X : PowerSeries ℂ) • Y) * -((X : PowerSeries ℂ) • (B * c)) = _`. Rewrite using `[Matrix.mul_neg, Matrix.mul_smul, hBc]`.

Rewrite using `[mul_add, mul_one, ← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.smul_mul, hcR]`. Normalize the expressions using the abelian group laws. Establish `hdet1 : (1 - (X : PowerSeries ℂ) • Y).det = ∏ a : Fin n, (1 - C (l a) * X)`. Rewrite using `[Matrix.det_of_isUpperTriangular]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `[Y, hA, mul_comm]`. Introduce `a b hab`. Establish `hba : b < a` using `hab`. Simplify using `[Y, hA, hba.ne', not_lt_of_gt hba, Matrix.one_apply_ne hba.ne']`. Establish `hdet2 : (1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J).det = ∏ a : Fin n, (1 - (C (l a) + 1) * X)`.

Rewrite using `[Matrix.det_of_isLowerTriangular]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[Y, J, hA]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a b hab`.

Establish `hab' : a < b` using `hab`. Simplify using `[Y, J, hA, hab'.ne, hab', Matrix.one_apply_ne hab'.ne]`. Establish `hdet3 : (1 + U * R).det = 1 - X * PowerSeries.mk fun k => ∑ a : Fin n, ∑ b : Fin n, (A ^ k) a b`. Rewrite using `[Matrix.det_one_add_mul_comm, Matrix.det_unique]`. Simplify using `[U, R, B, c, Matrix.mul_apply, Finset.mul_sum, sub_eq_add_neg]`.

Simplify using `only [← Finset.mul_sum]`. Use `congr 1`. Use extensionality with `k`. Simplify using `[PowerSeries.coeff_mk, map_sum]`. Rewrite using `[← hdet2, ← hfactor, Matrix.det_mul, hdet1, hdet3, mul_comm]`.
-/
theorem _root_.GlobalTheory.Dec.GelfSepProof.gen {n : ℕ} (l : Fin n → ℂ) :
    ((1 : PowerSeries ℂ) -
        PowerSeries.X * PowerSeries.mk fun (k : ℕ) ↦ ∑ a : Fin n, ∑ b : Fin n, (_root_.Formalism.REAL.Amat l ^ k) a b) *
      ∏ a : Fin n, ((1 : PowerSeries ℂ) - (PowerSeries.C : ℂ → PowerSeries ℂ) (l a) * PowerSeries.X) =
    ∏ a : Fin n,
      ((1 : PowerSeries ℂ) -
        ((PowerSeries.C : ℂ → PowerSeries ℂ) (l a) + (1 : PowerSeries ℂ)) * PowerSeries.X) := by
  have hA : ∀ a b, _root_.Formalism.REAL.Amat l a b = if a = b then l a else if a < b then -1 else 0 := by
    intro a b
    unfold _root_.Formalism.REAL.Amat
    rfl
  set A := _root_.Formalism.REAL.Amat l with hAdef
  let Y : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := A.map (PowerSeries.C : ℂ → PowerSeries ℂ)
  let B : Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
    Matrix.of fun a b => PowerSeries.mk fun k => (A ^ k) a b
  have hB : (1 - (X : PowerSeries ℂ) • Y) * B = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc]
    ext a b k
    rcases k with _ | k
    · simp [B, Matrix.one_apply]
    · simp [B, Y, Matrix.mul_apply, Matrix.one_apply, pow_succ', PowerSeries.coeff_succ_X_mul,
        map_sum]
      split_ifs <;> simp
  let c : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := replicateCol (Fin 1) 1
  let R : Matrix (Fin 1) (Fin n) (PowerSeries ℂ) := replicateRow (Fin 1) 1
  let J : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := Matrix.of fun _ _ => 1
  let U : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := -((X : PowerSeries ℂ) • (B * c))
  have hcR : c * R = J := by
    ext a b
    simp [c, R, J, Matrix.mul_apply]
  have hBc : (1 - (X : PowerSeries ℂ) • Y) * (B * c) = c := by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hfactor : (1 - (X : PowerSeries ℂ) • Y) * (1 + U * R) =
      1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J := by
    have hU : (1 - (X : PowerSeries ℂ) • Y) * U = -((X : PowerSeries ℂ) • c) := by
      show (1 - (X : PowerSeries ℂ) • Y) * -((X : PowerSeries ℂ) • (B * c)) = _
      rw [Matrix.mul_neg, Matrix.mul_smul, hBc]
    rw [mul_add, mul_one, ← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.smul_mul, hcR]
    abel
  have hdet1 : (1 - (X : PowerSeries ℂ) • Y).det = ∏ a : Fin n, (1 - C (l a) * X) := by
    rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, hA, mul_comm]
    · intro a b hab
      have hba : b < a := hab
      simp [Y, hA, hba.ne', not_lt_of_gt hba, Matrix.one_apply_ne hba.ne']
  have hdet2 : (1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J).det =
      ∏ a : Fin n, (1 - (C (l a) + 1) * X) := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, J, hA]
      ring
    · intro a b hab
      have hab' : a < b := hab
      simp [Y, J, hA, hab'.ne, hab', Matrix.one_apply_ne hab'.ne]
  have hdet3 : (1 + U * R).det =
      1 - X * PowerSeries.mk fun k => ∑ a : Fin n, ∑ b : Fin n, (A ^ k) a b := by
    rw [Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [U, R, B, c, Matrix.mul_apply, Finset.mul_sum, sub_eq_add_neg]
    simp only [← Finset.mul_sum]
    congr 1
    ext k
    simp [PowerSeries.coeff_mk, map_sum]
  rw [← hdet2, ← hfactor, Matrix.det_mul, hdet1, hdet3, mul_comm]

/- English proof (translation)
Establish `hinj : Function.Injective (fun x : ℂ => x + 1)` using `add_left_injective 1`. Establish `hc : ∀ x : ℂ, s.count x + t.count (x + 1) = t.count x + s.count (x + 1)`. Introduce `x`. Use `congrArg (Multiset.count (x + 1)) h` as an intermediate fact. Rewrite `this` using `[Multiset.count_add, Multiset.count_add]`.

Establish `e1` using `Multiset.count_map_eq_count' (fun x : ℂ => x + 1) s hinj x`. Establish `e2` using `Multiset.count_map_eq_count' (fun x : ℂ => x + 1) t hinj x`. Use linear arithmetic over natural numbers and integers. Use extensionality with `x`. Establish `hk : ∀ k : ℕ, s.count x + t.count (x + k) = t.count x + s.count (x + k)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [add_comm]`. Consider the case `succ k ih`. Use `hc (x + k)` as an intermediate fact.

Rewrite using `[Nat.cast_succ, ← add_assoc]`. Use linear arithmetic over natural numbers and integers. Establish `hi : Function.Injective (fun k : ℕ => x + (k : ℂ))` using `fun a b hab => by`. Simplify using `using hab`. Take `⟨_, ⟨k, rfl⟩, hk'⟩` from `(Set.infinite_range_of_injective hi).exists_notMem_finset (s + t).toFinset`.

Simplify using `only [Multiset.mem_toFinset, Multiset.mem_add, not_or] at hk'`. Use `hk k` as an intermediate fact. Rewrite `this` using `[Multiset.count_eq_zero_of_notMem hk'.1, Multiset.count_eq_zero_of_notMem hk'.2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem shift_inj (s t : Multiset ℂ) (h : s.map (· + 1) + t = t.map (· + 1) + s) : s = t := by
  classical
  have hinj : Function.Injective (fun x : ℂ => x + 1) := add_left_injective 1
  have hc : ∀ x : ℂ, s.count x + t.count (x + 1) = t.count x + s.count (x + 1) := by
    intro x
    have := congrArg (Multiset.count (x + 1)) h
    rw [Multiset.count_add, Multiset.count_add] at this
    have e1 := Multiset.count_map_eq_count' (fun x : ℂ => x + 1) s hinj x
    have e2 := Multiset.count_map_eq_count' (fun x : ℂ => x + 1) t hinj x
    omega
  ext x
  have hk : ∀ k : ℕ, s.count x + t.count (x + k) = t.count x + s.count (x + k) := by
    intro k
    induction k with
    | zero => simp [add_comm]
    | succ k ih =>
      have := hc (x + k)
      rw [Nat.cast_succ, ← add_assoc]
      omega
  have hi : Function.Injective (fun k : ℕ => x + (k : ℂ)) := fun a b hab => by
    simpa using hab
  obtain ⟨_, ⟨k, rfl⟩, hk'⟩ := (Set.infinite_range_of_injective hi).exists_notMem_finset (s + t).toFinset
  simp only [Multiset.mem_toFinset, Multiset.mem_add, not_or] at hk'
  have := hk k
  rw [Multiset.count_eq_zero_of_notMem hk'.1, Multiset.count_eq_zero_of_notMem hk'.2] at this
  omega

/- English proof (translation)
Establish `hc : ∀ c, Fintype.card {a // g a = c} = Fintype.card {a // f a = c}`. Introduce `c`. Use `congrArg (Multiset.count c) h` as an intermediate fact. Rewrite `this` using `[Multiset.count_map, Multiset.count_map]`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`.

Simplify using `only [eq_comm (b := c)]`. Conclude with `this.symm`. Use `⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Conclude with `(Equiv.ofFiberEquiv_map _ a).symm`.
-/
theorem exists_perm {n : ℕ} (f g : Fin n → ℂ) (h : univ.val.map f = univ.val.map g) :
    ∃ s : Equiv.Perm (Fin n), g = f ∘ s := by
  classical
  have hc : ∀ c, Fintype.card {a // g a = c} = Fintype.card {a // f a = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [eq_comm (b := c)]
    exact this.symm
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map _ a).symm

open Polynomial in

/- English proof (translation)
Establish `key : ∀ (p : Fin n → ℂ) (u : ℂ), u ≠ 0 → ∏ a, (u - p a) = u ^ n * ∏ a, (1 - p a * u⁻¹)`. Introduce `p u hu`. Establish `: u ^ n = ∏ _a : Fin n, u` using `by simp`. Rewrite using `[this, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Establish `hP : (∏ a, (X - C (f a))) * ∏ a, (X - C (g a)) = (∏ a, (X - C (f' a))) * ∏ a, ((X : ℂ[X]) - C (g' a))`. Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises. Use `Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl` and prove the remaining obligations. Introduce `u hu`.

Establish `hu : u ≠ 0` using `hu`. Establish `h2` using `congrArg (Polynomial.eval u⁻¹) h`. Simplify using `only [eval_mul, eval_prod, eval_sub, eval_one, eval_C, eval_X] at h2`. Simplify using `only [Set.mem_setOf_eq, eval_mul, eval_prod, eval_sub, eval_C, eval_X]`. Rewrite using `[key f u hu, key g u hu, key f' u hu, key g' u hu]`.

Take the linear combination `(u ^ n * u ^ n) * h2`. Establish `hr : ∀ p q : Fin n → ℂ, ((∏ a, (X - C (p a))) * ∏ a, ((X : ℂ[X]) - C (q a))).roots = univ.val.map p + univ.val.map q`. Introduce `p q`. Rewrite using `[← Polynomial.roots_multiset_prod_X_sub_C (univ.val.map p + univ.val.map q), Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map]`. Both sides reduce to the same expression.

Rewrite using `[← hr, ← hr, hP]`.
-/
theorem multiset_eq {n : ℕ} (f g f' g' : Fin n → ℂ)
    (h : (∏ a, (1 - C (f a) * X)) * ∏ a, (1 - C (g a) * X) =
      (∏ a, (1 - C (f' a) * X)) * ∏ a, (1 - C (g' a) * (X : ℂ[X]))) :
    univ.val.map f + univ.val.map g = univ.val.map f' + univ.val.map g' := by
  have key : ∀ (p : Fin n → ℂ) (u : ℂ), u ≠ 0 →
      ∏ a, (u - p a) = u ^ n * ∏ a, (1 - p a * u⁻¹) := by
    intro p u hu
    have : u ^ n = ∏ _a : Fin n, u := by simp
    rw [this, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    field_simp
  have hP : (∏ a, (X - C (f a))) * ∏ a, (X - C (g a)) =
      (∏ a, (X - C (f' a))) * ∏ a, ((X : ℂ[X]) - C (g' a)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro u hu
    have hu : u ≠ 0 := hu
    have h2 := congrArg (Polynomial.eval u⁻¹) h
    simp only [eval_mul, eval_prod, eval_sub, eval_one, eval_C, eval_X] at h2
    simp only [Set.mem_setOf_eq, eval_mul, eval_prod, eval_sub, eval_C, eval_X]
    rw [key f u hu, key g u hu, key f' u hu, key g' u hu]
    linear_combination (u ^ n * u ^ n) * h2
  have hr : ∀ p q : Fin n → ℂ, ((∏ a, (X - C (p a))) * ∏ a, ((X : ℂ[X]) - C (q a))).roots =
      univ.val.map p + univ.val.map q := by
    intro p q
    rw [← Polynomial.roots_multiset_prod_X_sub_C (univ.val.map p + univ.val.map q), Multiset.map_add,
      Multiset.prod_add, Multiset.map_map, Multiset.map_map]
    rfl
  rw [← hr, ← hr, hP]

open PowerSeries in

/- English proof (translation)
Establish `g1` using `gen l`. Establish `g2` using `gen l'`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `g2` using `[← funext h]`.

Apply `exists_perm` to reduce the goal to its premises. Apply `shift_inj` to reduce the goal to its premises. Rewrite using `[Multiset.map_map, Multiset.map_map]`. Apply `multiset_eq` to reduce the goal to its premises. Apply `Polynomial.coe_injective` to reduce the goal to its premises.

Establish `hcoe : ∀ p : Fin n → ℂ, ((∏ a, (1 - Polynomial.C (p a) * Polynomial.X) : Polynomial ℂ) : ℂ⟦X⟧) = ∏ a, (1 - C (p a) * X)`. Introduce `p`. Rewrite using `[← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]`. Simplify using the standard rewrite rules. Simplify using `only [Polynomial.coe_mul, hcoe]`.

Simplify using `only [Function.comp, map_add, map_one]`. Rewrite using `[← g1, ← g2]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨s, rfl⟩`. Establish `e1 : ∏ a, (1 - C ((l ∘ s) a) * (X : ℂ⟦X⟧)) = ∏ a, (1 - C (l a) * X)` using `Equiv.prod_comp s (fun a => 1 - C (l a) * (X : ℂ⟦X⟧))`.

Establish `e2 : ∏ a, (1 - (C ((l ∘ s) a) + 1) * (X : ℂ⟦X⟧)) = ∏ a, (1 - (C (l a) + 1) * X)` using `Equiv.prod_comp s (fun a => 1 - (C (l a) + 1) * (X : ℂ⟦X⟧))`. Rewrite `g2` using `[e1, e2, ← g1]`. Establish `hne : ∏ a, (1 - C (l a) * (X : ℂ⟦X⟧)) ≠ 0`. Introduce `h0`. Use `congrArg (constantCoeff (R := ℂ)) h0` as an intermediate fact.

Simplify using `[map_prod] at this`. Establish `h3` using `mul_left_cancel₀ X_ne_zero (sub_right_injective (mul_right_cancel₀ hne g2))`. Introduce `k`. Use `congrArg (coeff k) h3` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem sep {n : ℕ} (l l' : Fin n → ℂ) :
    (∀ k, ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l' ^ k) a b) ↔
      ∃ s : Equiv.Perm (Fin n), l' = l ∘ s := by
  have g1 := gen l
  have g2 := gen l'
  constructor
  · intro h
    rw [← funext h] at g2
    apply exists_perm
    apply shift_inj
    rw [Multiset.map_map, Multiset.map_map]
    apply multiset_eq
    apply Polynomial.coe_injective
    have hcoe : ∀ p : Fin n → ℂ, ((∏ a, (1 - Polynomial.C (p a) * Polynomial.X) : Polynomial ℂ) : ℂ⟦X⟧) =
        ∏ a, (1 - C (p a) * X) := by
      intro p
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
      simp
    simp only [Polynomial.coe_mul, hcoe]
    simp only [Function.comp, map_add, map_one]
    rw [← g1, ← g2]
    ring
  · rintro ⟨s, rfl⟩
    have e1 : ∏ a, (1 - C ((l ∘ s) a) * (X : ℂ⟦X⟧)) = ∏ a, (1 - C (l a) * X) :=
      Equiv.prod_comp s (fun a => 1 - C (l a) * (X : ℂ⟦X⟧))
    have e2 : ∏ a, (1 - (C ((l ∘ s) a) + 1) * (X : ℂ⟦X⟧)) = ∏ a, (1 - (C (l a) + 1) * X) :=
      Equiv.prod_comp s (fun a => 1 - (C (l a) + 1) * (X : ℂ⟦X⟧))
    rw [e1, e2, ← g1] at g2
    have hne : ∏ a, (1 - C (l a) * (X : ℂ⟦X⟧)) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff (R := ℂ)) h0
      simp [map_prod] at this
    have h3 := mul_left_cancel₀ X_ne_zero (sub_right_injective (mul_right_cancel₀ hne g2))
    intro k
    have := congrArg (coeff k) h3
    simpa using this.symm

end GlobalTheory.Dec.GelfSepProof

namespace GlobalTheory.Dec

end GlobalTheory.Dec
