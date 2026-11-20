import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Capelli

variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}

def trAlg (M : Matrix (Fin n) (Fin n) A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ (Set.range fun k : ℕ => (M ^ (k + 1)).trace)

/- English proof (translation)
Consider the cases of `k with`. Consider the case `zero => simpa using natCast_mem (trAlg M) n`. Consider the case `succ k => exact Algebra.subset_adjoin ⟨k, rfl⟩`.
-/
theorem trace_pow_mem (M : Matrix (Fin n) (Fin n) A) (k : ℕ) : (M ^ k).trace ∈ trAlg M := by
  cases k with
  | zero => simpa using natCast_mem (trAlg M) n
  | succ k => exact Algebra.subset_adjoin ⟨k, rfl⟩

/- English proof (translation)
The claim follows from `Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact h k)`.
-/
theorem trAlg_le {M : Matrix (Fin n) (Fin n) A} {S : Subalgebra ℂ A} (h : ∀ k, (M ^ (k + 1)).trace ∈ S) :
    trAlg M ≤ S := Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact h k)

/- English proof (translation)
Establish `key : ∀ k j : ℕ, (M ^ j * (s • M + c • 1) ^ k).trace ∈ trAlg M`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro j`. Simplify using `using trace_pow_mem M j`.

Consider the case `succ k ih`. Introduce `j`. Rewrite using `[pow_succ', ← mul_assoc, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_one, ← pow_succ, trace_add, trace_smul, trace_smul]`. Conclude with `add_mem (Subalgebra.smul_mem _ (ih _) _) (Subalgebra.smul_mem _ (ih _) _)`. Conclude with `trAlg_le fun k => by simpa using key (k + 1) 0`.
-/
theorem trAlg_shift_le (M : Matrix (Fin n) (Fin n) A) (s c : ℂ) : trAlg (s • M + c • 1) ≤ trAlg M := by
  have key : ∀ k j : ℕ, (M ^ j * (s • M + c • 1) ^ k).trace ∈ trAlg M := by
    intro k
    induction k with
    | zero => intro j; simpa using trace_pow_mem M j
    | succ k ih =>
      intro j
      rw [pow_succ', ← mul_assoc, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
        mul_one, ← pow_succ, trace_add, trace_smul, trace_smul]
      exact add_mem (Subalgebra.smul_mem _ (ih _) _) (Subalgebra.smul_mem _ (ih _) _)
  exact trAlg_le fun k => by simpa using key (k + 1) 0

/- English proof (translation)
Use `le_antisymm (trAlg_shift_le M s c) ?_` and prove the remaining obligations. Establish `h` using `trAlg_shift_le (s • M + c • (1 : Matrix (Fin n) (Fin n) A)) s⁻¹ (-(s⁻¹ * c))`. Rewrite `h` using `[smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, neg_smul, add_neg_cancel_right]`. Then use the resulting hypothesis.
-/
theorem trAlg_shift (M : Matrix (Fin n) (Fin n) A) {s : ℂ} (hs : s ≠ 0) (c : ℂ) :
    trAlg (s • M + c • 1) = trAlg M := by
  refine le_antisymm (trAlg_shift_le M s c) ?_
  have h := trAlg_shift_le (s • M + c • (1 : Matrix (Fin n) (Fin n) A)) s⁻¹ (-(s⁻¹ * c))
  rwa [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, neg_smul, add_neg_cancel_right] at h

/- English proof (translation)
Rewrite using `[trAlg]`. Use `congr 2`. Use function extensionality and compare the values at `k`. Rewrite using `[GlobalTheory.SmoothForms.gelfA_eq_sum_pow]`. Both sides reduce to the same expression.
-/
theorem adjoin_gelfA (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA E)) = trAlg (Matrix.of E) := by
  rw [trAlg]
  congr 2
  funext k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  rfl

section CCR

variable (X : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A)
  (hdd : ∀ a l b j, D a l * D b j = D b j * D a l)
  (hdx : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0)

omit [Algebra ℂ A] in
include hdd hdx in
/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, hdx, add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [mul_assoc, mul_assoc, hdd]`. Apply the tactic sequence `by_cases h : i = l <;> simp [h]`.
-/
theorem comm_one (a : Fin m) (l i j : Fin n) :
    D a l * (X * D) i j = (X * D) i j * D a l + if i = l then D a j else 0 := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, hdx, add_mul, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => by rw [mul_assoc, mul_assoc, hdd]
  · by_cases h : i = l <;> simp [h]

omit [Algebra ℂ A] in
include hdd hdx in
/- English proof (translation)
Proceed by induction on `p generalizing i with`. Consider the case `zero => by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Consider the case `succ p ih`. Establish `h1 : ∀ k, D a l * ((X * D) i k * ((X * D) ^ p) k j) = (X * D) i k * ((X * D) ^ p) k j * D a l + (∑ r ∈ Finset.range p, (X * D) i k * ((X * D) ^ r) k l * (D * (X * D) ^ (p - (r + 1))) a j + if i = l then D a k * ((X * D) ^ p) k j else 0)` using `fun k => by`. Rewrite using `[← mul_assoc, comm_one X D hdd hdx, add_mul, mul_assoc, ih, mul_add, Finset.mul_sum, add_assoc]`.

Simplify using `only [mul_assoc, ite_mul, zero_mul]`. Rewrite using `[pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.sum_range_succ']`. Simplify using `only [h1, Finset.sum_add_distrib]`. Use `congr 2`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, ← Matrix.mul_apply, ← pow_succ', Nat.add_sub_add_right]`. Apply the tactic sequence `by_cases h : i = l <;> simp [h, Matrix.one_apply, Matrix.mul_apply]`.
-/
theorem comm_pow (p : ℕ) (a : Fin m) (l i j : Fin n) :
    D a l * ((X * D) ^ p) i j = ((X * D) ^ p) i j * D a l
      + ∑ r ∈ Finset.range p, ((X * D) ^ r) i l * (D * (X * D) ^ (p - (r + 1))) a j := by
  induction p generalizing i with
  | zero => by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ p ih =>
    have h1 : ∀ k, D a l * ((X * D) i k * ((X * D) ^ p) k j) =
        (X * D) i k * ((X * D) ^ p) k j * D a l
        + (∑ r ∈ Finset.range p, (X * D) i k * ((X * D) ^ r) k l * (D * (X * D) ^ (p - (r + 1))) a j
          + if i = l then D a k * ((X * D) ^ p) k j else 0) := fun k => by
      rw [← mul_assoc, comm_one X D hdd hdx, add_mul, mul_assoc, ih, mul_add, Finset.mul_sum, add_assoc]
      simp only [mul_assoc, ite_mul, zero_mul]
    rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.sum_range_succ']
    simp only [h1, Finset.sum_add_distrib]
    congr 2
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_mul, ← Matrix.mul_apply, ← pow_succ', Nat.add_sub_add_right]
    · by_cases h : i = l <;> simp [h, Matrix.one_apply, Matrix.mul_apply]

omit [Algebra ℂ A] in
include hdd hdx in
/- English proof (translation)
Establish `hN : ∀ q : ℕ, (D * X) ^ (q + 1) = D * (X * D) ^ q * X` using `fun q => by`. Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih => rw [pow_succ, ih, pow_succ]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hY : ∀ a j, (D * (X * D) ^ p) a j = ∑ u, ((X * D) ^ p) u j * D a u + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * (D * (X * D) ^ (p - (r + 1))) a j` using `fun a j => by`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [comm_pow X D hdd hdx, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [trace, diag_apply, Finset.sum_mul]`. Establish `hT : ∀ q : ℕ, ((D * X) ^ (q + 1)).trace = ∑ a, ∑ j, (D * (X * D) ^ q) a j * X j a` using `fun q => by`. Rewrite using `[hN]`. Both sides reduce to the same expression. Establish `hE : ∀ u j, ∑ a, D a u * X j a = (X * D) j u + if j = u then (m : A) else 0` using `fun u j => by`.

Simplify using `only [hdx, Finset.sum_add_distrib, Matrix.mul_apply]`. Apply the tactic sequence `by_cases h : j = u <;> simp [h]`. Simplify using `only [hT]`. Simplify using `only [hY, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Use `congr 1`.

Rewrite using `[Finset.sum_comm]`. Establish `: ∀ j, ∑ a, ∑ u, ((X * D) ^ p) u j * (D a u * X j a) = ∑ u, ((X * D) ^ p) u j * (X * D) j u + (m : A) * ((X * D) ^ p) j j` using `fun j => by`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.mul_sum, hE, mul_add, Finset.sum_add_distrib]`. Simplify using `[Nat.cast_comm]`.

Simplify using `only [this, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_comm, pow_succ]`. Both sides reduce to the same expression. Simplify using `only [trace, diag_apply, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm (s := Finset.range p)]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_comm`.
-/
theorem trace_rec (p : ℕ) :
    ((D * X) ^ (p + 1)).trace = ((X * D) ^ (p + 1)).trace + (m : A) * ((X * D) ^ p).trace
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * ((D * X) ^ (p - (r + 1) + 1)).trace := by
  have hN : ∀ q : ℕ, (D * X) ^ (q + 1) = D * (X * D) ^ q * X := fun q => by
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]
  have hY : ∀ a j, (D * (X * D) ^ p) a j = ∑ u, ((X * D) ^ p) u j * D a u
      + ∑ r ∈ Finset.range p, ((X * D) ^ r).trace * (D * (X * D) ^ (p - (r + 1))) a j := fun a j => by
    rw [Matrix.mul_apply]
    simp only [comm_pow X D hdd hdx, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [trace, diag_apply, Finset.sum_mul]
  have hT : ∀ q : ℕ, ((D * X) ^ (q + 1)).trace = ∑ a, ∑ j, (D * (X * D) ^ q) a j * X j a := fun q => by
    rw [hN]; rfl
  have hE : ∀ u j, ∑ a, D a u * X j a = (X * D) j u + if j = u then (m : A) else 0 := fun u j => by
    simp only [hdx, Finset.sum_add_distrib, Matrix.mul_apply]
    by_cases h : j = u <;> simp [h]
  simp only [hT]
  simp only [hY, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  congr 1
  · rw [Finset.sum_comm]
    have : ∀ j, ∑ a, ∑ u, ((X * D) ^ p) u j * (D a u * X j a)
        = ∑ u, ((X * D) ^ p) u j * (X * D) j u + (m : A) * ((X * D) ^ p) j j := fun j => by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hE, mul_add, Finset.sum_add_distrib]
      simp [Nat.cast_comm]
    simp only [this, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm, pow_succ]; rfl
    · simp only [trace, diag_apply, Finset.mul_sum]
  · rw [Finset.sum_comm (s := Finset.range p)]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

include hdd hdx in
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `key : ∀ p : ℕ, ((X * D) ^ p).trace ∈ trAlg (D * X)` using `fun p => by`. Proceed by induction on `p using Nat.strong_induction_on with`. Consider the case `_ p ih`. Consider the cases of `p with`.

Consider the case `zero => simpa using natCast_mem (trAlg (D * X)) n`. Consider the case `succ p`. Establish `h` using `trace_rec X D hdd hdx p`. Rewrite `h` using `[add_assoc, ← sub_eq_iff_eq_add]`. Rewrite using `[← h]`.

Use `sub_mem (trace_pow_mem _ _) (add_mem (mul_mem (natCast_mem _ _) (ih p (by omega))) (sum_mem fun r hr => mul_mem (ih r ?_) (trace_pow_mem _ _)))` and prove the remaining obligations. Use `Finset.mem_range.1 hr` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `trAlg_le fun k => key _`. Use `trAlg_le fun p => ?_` and prove the remaining obligations.

Proceed by induction on `p using Nat.strong_induction_on with`. Consider the case `_ p ih`. Rewrite using `[trace_rec X D hdd hdx p]`. Use `add_mem (add_mem (trace_pow_mem _ _) (mul_mem (natCast_mem _ _) (trace_pow_mem _ _))) (sum_mem fun r hr => mul_mem (trace_pow_mem _ _) (ih _ ?_))` and prove the remaining obligations. Use `Finset.mem_range.1 hr` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem trAlg_mul_comm : trAlg (X * D) = trAlg (D * X) := by
  apply le_antisymm
  · have key : ∀ p : ℕ, ((X * D) ^ p).trace ∈ trAlg (D * X) := fun p => by
      induction p using Nat.strong_induction_on with
      | _ p ih =>
        cases p with
        | zero => simpa using natCast_mem (trAlg (D * X)) n
        | succ p =>
          have h := trace_rec X D hdd hdx p
          rw [add_assoc, ← sub_eq_iff_eq_add] at h
          rw [← h]
          refine sub_mem (trace_pow_mem _ _) (add_mem (mul_mem (natCast_mem _ _) (ih p (by omega)))
            (sum_mem fun r hr => mul_mem (ih r ?_) (trace_pow_mem _ _)))
          have := Finset.mem_range.1 hr
          omega
    exact trAlg_le fun k => key _
  · refine trAlg_le fun p => ?_
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      rw [trace_rec X D hdd hdx p]
      refine add_mem (add_mem (trace_pow_mem _ _) (mul_mem (natCast_mem _ _) (trace_pow_mem _ _)))
        (sum_mem fun r hr => mul_mem (trace_pow_mem _ _) (ih _ ?_))
      have := Finset.mem_range.1 hr
      omega

end CCR

/- English proof (translation)
Introduce `A _ _ n m x d h c c'`. Take `⟨-, hdd, hdx⟩` from `h`. Set `X : Matrix (Fin n) (Fin m) A` to `Matrix.of fun i a => x (i, a)`. Set `D : Matrix (Fin m) (Fin n) A` to `Matrix.of fun a i => d (i, a)`. Establish `hdx' : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0` using `fun a l i b => by`.

Use `hdx (i, b) (l, a)` as an intermediate fact. Rewrite `this` using `[sub_eq_iff_eq_add']`. Simplify `this` using `[X, D]`. Establish `h1 : (Matrix.of fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0) = (1 : ℂ) • (X * D) + c • 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [X, D, Matrix.mul_apply, Matrix.one_apply, hij, Algebra.algebraMap_eq_smul_one]`. Establish `h2 : (Matrix.of fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0) = (-1 : ℂ) • (D * X) + (c' + n) • 1`. Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, hdx', Finset.sum_add_distrib]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `[X, D, Algebra.algebraMap_eq_smul_one, add_smul, Nat.cast_smul_eq_nsmul]`. Normalize the expressions using the abelian group laws. Simplify using `[X, D, hab, Ne.symm hab]`. Rewrite using `[adjoin_gelfA, adjoin_gelfA, h1, h2, trAlg_shift _ one_ne_zero, trAlg_shift _ (by norm_num)]`.

Conclude with `trAlg_mul_comm X D (fun a l b j => hdd _ _) hdx'`.
-/
theorem adjoin_gelfA_dual_pair : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → ∀ c c' : ℂ, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)) = Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)) := by
  intro A _ _ n m x d h c c'
  obtain ⟨-, hdd, hdx⟩ := h
  let X : Matrix (Fin n) (Fin m) A := Matrix.of fun i a => x (i, a)
  let D : Matrix (Fin m) (Fin n) A := Matrix.of fun a i => d (i, a)
  have hdx' : ∀ a l i b, D a l * X i b = X i b * D a l + if i = l ∧ b = a then 1 else 0 := fun a l i b => by
    have := hdx (i, b) (l, a)
    rw [sub_eq_iff_eq_add'] at this
    simpa [X, D] using this
  have h1 : (Matrix.of fun i j : Fin n => ∑ a, x (i, a) * d (j, a) + if i = j then algebraMap ℂ A c else 0)
      = (1 : ℂ) • (X * D) + c • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [X, D, Matrix.mul_apply, Matrix.one_apply, hij, Algebra.algebraMap_eq_smul_one]
  have h2 : (Matrix.of fun a b : Fin m => -∑ i, x (i, b) * d (i, a) + if a = b then algebraMap ℂ A c' else 0)
      = (-1 : ℂ) • (D * X) + (c' + n) • 1 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, hdx', Finset.sum_add_distrib]
    by_cases hab : a = b
    · subst hab
      simp [X, D, Algebra.algebraMap_eq_smul_one, add_smul, Nat.cast_smul_eq_nsmul]
      abel
    · simp [X, D, hab, Ne.symm hab]
  rw [adjoin_gelfA, adjoin_gelfA, h1, h2, trAlg_shift _ one_ne_zero, trAlg_shift _ (by norm_num)]
  exact trAlg_mul_comm X D (fun a l b j => hdd _ _) hdx'

end GlobalTheory.Mem.Capelli
