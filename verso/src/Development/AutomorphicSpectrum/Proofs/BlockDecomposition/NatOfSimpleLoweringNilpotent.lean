import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

/- English proof (translation)
Establish `hne : i ≠ j` using `fun h => by rw [h] at hij; omega`. Establish `hxy : e (i, j) * e (j, i) = e (j, i) * e (i, j) + (e (i, i) - e (j, j))`. Use `e_mul_sub_mul (i, j) (j, i)` as an intermediate fact. Simplify using `only [if_true] at this`. Rewrite using `[← this]`.

Normalize the expressions using the abelian group laws. Establish `hh : ∀ p : ℕ, (e (i, i) - e (j, j)) * e (j, i) ^ p = e (j, i) ^ p * (e (i, i) - e (j, j)) - (2 * (p : ℂ)) • e (j, i) ^ p`. Introduce `p`. Rewrite using `[sub_mul, e_diag_mul_e_pow, e_diag_mul_e_pow, rootAt_lower_self hne, rootAt_lower_other hne, mul_sub]`. Use `module`.

Proceed by induction on `m with`. Consider the case `zero`. Simplify using `only [pow_zero, pow_one, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero, zero_smul, sub_zero]`. Conclude with `hxy`. Consider the case `succ m ih`.

Establish `e1 : e (i, j) * e (j, i) ^ (m + 1 + 1) = e (j, i) * (e (i, j) * e (j, i) ^ (m + 1)) + (e (i, i) - e (j, j)) * e (j, i) ^ (m + 1)`. Rewrite using `[pow_succ' _ (m + 1), ← mul_assoc, hxy, add_mul, mul_assoc]`. Rewrite using `[e1, hh, ih]`. Simplify using `only [mul_sub, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ']`. Use `push_cast`.

Use `module`.
-/
theorem e_upper_mul_pow_succ_eq {i j : Fin n} (hij : (j : ℕ) = i + 1) (m : ℕ) :
    e (i, j) * e (j, i) ^ (m + 1) =
      e (j, i) ^ (m + 1) * e (i, j) + ((m : ℂ) + 1) • (e (j, i) ^ m * (e (i, i) - e (j, j))) -
        (((m : ℂ) + 1) * m) • e (j, i) ^ m := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hxy : e (i, j) * e (j, i) = e (j, i) * e (i, j) + (e (i, i) - e (j, j)) := by
    have := e_mul_sub_mul (i, j) (j, i)
    simp only [if_true] at this
    rw [← this]; abel
  have hh : ∀ p : ℕ, (e (i, i) - e (j, j)) * e (j, i) ^ p =
      e (j, i) ^ p * (e (i, i) - e (j, j)) - (2 * (p : ℂ)) • e (j, i) ^ p := by
    intro p
    rw [sub_mul, e_diag_mul_e_pow, e_diag_mul_e_pow, rootAt_lower_self hne, rootAt_lower_other hne,
      mul_sub]
    module
  induction m with
  | zero =>
    simp only [pow_zero, pow_one, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero, zero_smul,
      sub_zero]
    exact hxy
  | succ m ih =>
    have e1 : e (i, j) * e (j, i) ^ (m + 1 + 1) =
        e (j, i) * (e (i, j) * e (j, i) ^ (m + 1)) + (e (i, i) - e (j, j)) * e (j, i) ^ (m + 1) := by
      rw [pow_succ' _ (m + 1), ← mul_assoc, hxy, add_mul, mul_assoc]
    rw [e1, hh, ih]
    simp only [mul_sub, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ']
    push_cast
    module

/- English proof (translation)
Establish `hi` using `hx i`. Establish `hj` using `hx j`. Establish `hd` using `rhoVec_sub (n := n) hij`. Establish `key : (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x = x * (e (i, i) - algebraMap ℂ (U n) (rhoVec n i)) - x * (e (j, j) - algebraMap ℂ (U n) (rhoVec n j))`. Establish `h1 : e (i, i) * x = x * e (i, i) + (μ i : ℂ) • x` using `by rw [← hi]; abel`.

Establish `h2 : e (j, j) * x = x * e (j, j) + (μ j : ℂ) • x` using `by rw [← hj]; abel`. Establish `h3 : rhoVec n i = rhoVec n j + 1` using `by rw [← hd]; ring`. Rewrite using `[sub_mul, h1, h2]`. Simplify using `only [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, h3]`. Use `module`.

Rewrite using `[key]`. Conclude with `vermaIdeal_le_Jp (Submodule.sub_mem _ (mul_e_sub_mem_vermaIdeal _ _ i) (mul_e_sub_mem_vermaIdeal _ _ j))`.
-/
theorem h_mul_sub_mem_Jp {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) {i j : Fin n}
    (hij : (j : ℕ) = i + 1) :
    (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x ∈ Jp n := by
  have hi := hx i
  have hj := hx j
  have hd := rhoVec_sub (n := n) hij
  have key : (e (i, i) - e (j, j)) * x - ((1 : ℂ) + (μ i : ℂ) - (μ j : ℂ)) • x =
      x * (e (i, i) - algebraMap ℂ (U n) (rhoVec n i)) -
        x * (e (j, j) - algebraMap ℂ (U n) (rhoVec n j)) := by
    have h1 : e (i, i) * x = x * e (i, i) + (μ i : ℂ) • x := by rw [← hi]; abel
    have h2 : e (j, j) * x = x * e (j, j) + (μ j : ℂ) • x := by rw [← hj]; abel
    have h3 : rhoVec n i = rhoVec n j + 1 := by rw [← hd]; ring
    rw [sub_mul, h1, h2]
    simp only [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, h3]
    module
  rw [key]
  exact vermaIdeal_le_Jp (Submodule.sub_mem _ (mul_e_sub_mem_vermaIdeal _ _ i)
    (mul_e_sub_mem_vermaIdeal _ _ j))

/- English proof (translation)
Establish `hp` using `Nat.find_spec hN`. Establish `hmin` using `fun m => Nat.find_min hN (m := m)`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q, Nat.find hN = q + 1 := by`. Use `Nat.exists_eq_succ_of_ne_zero fun h0 => hxJ ?_` and prove the remaining obligations. Rewrite `hp` using `[h0]`.

Simplify using `using hp`. Rewrite `hp` using `[hq]`. Establish `hqn : e (j, i) ^ q * x ∉ Jp n` using `hmin q (by omega)`. Establish `hEx : e (i, j) * x ∈ Jp n` using `hup (i, j) (by`. Simplify using `only [IsUpper]`.

Rewrite using `[Fin.lt_def, hij]`. Use the proof step `omega)`. Use `set c : ℂ := (1 : ℂ) + (μ i : ℂ) - (μ j : ℂ) with hc`. Establish `h1` using `mul_mem_Jp (e (i, j)) hp`. Establish `h2` using `mul_mem_Jp (e (j, i) ^ (q + 1)) hEx`.

Establish `h3` using `mul_mem_Jp (e (j, i) ^ q) (h_mul_sub_mem_Jp hx hij)`. Establish `key : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) = e (i, j) * (e (j, i) ^ (q + 1) * x) - e (j, i) ^ (q + 1) * (e (i, j) * x) - ((q : ℂ) + 1) • (e (j, i) ^ q * ((e (i, i) - e (j, j)) * x - c • x))`. Rewrite using `[← mul_assoc (e (i, j)), e_upper_mul_pow_succ_eq hij q]`. Simplify using `only [mul_sub, sub_mul, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]`. Use `module`.

Establish `hmem : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) ∈ Jp n`. Rewrite using `[key]`. Conclude with `Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ h3)`. Establish `hzero : ((q : ℂ) + 1) * (c - q) = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hqn ((Submodule.smul_mem_iff _ hne).1 hmem)`. Establish `hq1 : (q : ℂ) + 1 ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero q`. Establish `hcq : c = q` using `sub_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left hq1)`. Use `⟨q, ?_⟩` and prove the remaining obligations. Establish `: ((1 + μ i - μ j : ℤ) : ℂ) = ((q : ℤ) : ℂ)`.

Use `push_cast`. Conclude with `hcq`. Conclude with `this` after adjusting the coercions.
-/
theorem natural_of_primitive {n : ℕ} (μ : Fin n → ℤ) (x : U n) (i j : Fin n) (hx : IsAdW μ x)
    (hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hxJ : x ∉ Jp n)
    (hij : (j : ℕ) = i + 1) (hN : ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n) :
    ∃ p : ℕ, 1 + μ i - μ j = (p : ℤ) := by
  classical
  have hp := Nat.find_spec hN
  have hmin := fun m => Nat.find_min hN (m := m)
  obtain ⟨q, hq⟩ : ∃ q, Nat.find hN = q + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => hxJ ?_
    rw [h0] at hp
    simpa using hp
  rw [hq] at hp
  have hqn : e (j, i) ^ q * x ∉ Jp n := hmin q (by omega)
  have hEx : e (i, j) * x ∈ Jp n := hup (i, j) (by
    simp only [IsUpper]; rw [Fin.lt_def, hij]; omega)
  set c : ℂ := (1 : ℂ) + (μ i : ℂ) - (μ j : ℂ) with hc
  have h1 := mul_mem_Jp (e (i, j)) hp
  have h2 := mul_mem_Jp (e (j, i) ^ (q + 1)) hEx
  have h3 := mul_mem_Jp (e (j, i) ^ q) (h_mul_sub_mem_Jp hx hij)
  have key : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) =
      e (i, j) * (e (j, i) ^ (q + 1) * x) - e (j, i) ^ (q + 1) * (e (i, j) * x) -
        ((q : ℂ) + 1) • (e (j, i) ^ q * ((e (i, i) - e (j, j)) * x - c • x)) := by
    rw [← mul_assoc (e (i, j)), e_upper_mul_pow_succ_eq hij q]
    simp only [mul_sub, sub_mul, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    module
  have hmem : (((q : ℂ) + 1) * (c - q)) • (e (j, i) ^ q * x) ∈ Jp n := by
    rw [key]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.smul_mem _ _ h3)
  have hzero : ((q : ℂ) + 1) * (c - q) = 0 := by
    by_contra hne
    exact hqn ((Submodule.smul_mem_iff _ hne).1 hmem)
  have hq1 : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hcq : c = q := sub_eq_zero.1 ((mul_eq_zero.1 hzero).resolve_left hq1)
  refine ⟨q, ?_⟩
  have : ((1 + μ i - μ j : ℤ) : ℂ) = ((q : ℤ) : ℂ) := by
    push_cast
    exact hcq
  exact_mod_cast this

end GlobalTheory.CompanionTheory.PresRho
