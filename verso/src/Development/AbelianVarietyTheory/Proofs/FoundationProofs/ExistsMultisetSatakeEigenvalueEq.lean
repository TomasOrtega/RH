import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun

open Polynomial in

/- English proof (translation)
Use `set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), monomial k ((-1) ^ (n - k) * e (n - k)) with hp`. Establish `hc : ∀ k, p.coeff k = if k ≤ n then (-1) ^ (n - k) * e (n - k) else 0` using `fun k => by`. Simplify using `[hp, coeff_monomial]`. Establish `hle : p.natDegree ≤ n` using `natDegree_le_iff_coeff_eq_zero.2 fun k hk => by rw [hc, if_neg (by omega)]`. Establish `hcn : p.coeff n = 1` using `by simp [hc, h0]`.

Establish `hd : p.natDegree = n` using `natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hcn])`. Establish `hl : p.leadingCoeff = 1` using `by rw [leadingCoeff, hd, hcn]`. Establish `hr : p.roots.card = p.natDegree` using `(IsAlgClosed.splits p).natDegree_eq_card_roots.symm`. Use `⟨p.roots, hr.trans hd, fun hz => ?_, fun j hj => ?_⟩` and prove the remaining obligations. Use `isRoot_of_mem_roots hz` as an intermediate fact.

Rewrite `this` using `[IsRoot, ← coeff_zero_eq_eval_zero, hc]`. Simplify using `[hn] at this`. Use `coeff_eq_esymm_roots_of_card hr (k := n - j) (by omega)` as an intermediate fact. Rewrite `this` using `[hc, if_pos (by omega), hl, hd, one_mul, Nat.sub_sub_self hj]`. Conclude with `(mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) this).symm`.
-/
theorem exists_multiset_esymm_eq (n : ℕ) (e : ℕ → ℂ) (h0 : e 0 = 1) (hn : e n ≠ 0) :
    ∃ A : Multiset ℂ, A.card = n ∧ (0 : ℂ) ∉ A ∧ ∀ j ≤ n, A.esymm j = e j := by
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), monomial k ((-1) ^ (n - k) * e (n - k)) with hp
  have hc : ∀ k, p.coeff k = if k ≤ n then (-1) ^ (n - k) * e (n - k) else 0 := fun k => by
    simp [hp, coeff_monomial]
  have hle : p.natDegree ≤ n := natDegree_le_iff_coeff_eq_zero.2 fun k hk => by rw [hc, if_neg (by omega)]
  have hcn : p.coeff n = 1 := by simp [hc, h0]
  have hd : p.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hcn])
  have hl : p.leadingCoeff = 1 := by rw [leadingCoeff, hd, hcn]
  have hr : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  refine ⟨p.roots, hr.trans hd, fun hz => ?_, fun j hj => ?_⟩
  · have := isRoot_of_mem_roots hz
    rw [IsRoot, ← coeff_zero_eq_eval_zero, hc] at this
    simp [hn] at this
  · have := coeff_eq_esymm_roots_of_card hr (k := n - j) (by omega)
    rw [hc, if_pos (by omega), hl, hd, one_mul, Nat.sub_sub_self hj] at this
    exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) this).symm

/- English proof (translation)
Introduce `q n hq c h0 hn`. Establish `hw : ∀ j : ℕ, (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) ≠ 0` using `fun j h => hq (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h).1)`. Take `⟨A, hA, hz, he⟩` from `exists_multiset_esymm_eq n (fun j => c j / (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) (by simp [h0]) (div_ne_zero hn (hw n))`. Use `⟨A.pmap (fun a (h : a ≠ 0) => Units.mk0 a h) (fun a ha h => hz (h ▸ ha)), by simp [hA], fun j hj => ?_⟩` and prove the remaining obligations. Rewrite using `[satEig, Multiset.map_pmap]`.

Simplify using `only [Units.val_mk0, Multiset.pmap_eq_map, Multiset.map_id']`. Rewrite using `[he j hj]`. Conclude with `mul_div_cancel₀ _ (hw j)`.
-/
theorem exists_satEig_eq : ∀ (q n : ℕ), q ≠ 0 → ∀ c : ℕ → ℂ, c 0 = 1 → c n ≠ 0 →
    ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, satEig q n B j = c j := by
  intro q n hq c h0 hn
  have hw : ∀ j : ℕ, (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) ≠ 0 := fun j h =>
    hq (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h).1)
  obtain ⟨A, hA, hz, he⟩ := exists_multiset_esymm_eq n
    (fun j => c j / (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) (by simp [h0]) (div_ne_zero hn (hw n))
  refine ⟨A.pmap (fun a (h : a ≠ 0) => Units.mk0 a h) (fun a ha h => hz (h ▸ ha)), by simp [hA], fun j hj => ?_⟩
  rw [satEig, Multiset.map_pmap]
  simp only [Units.val_mk0, Multiset.pmap_eq_map, Multiset.map_id']
  rw [he j hj]
  exact mul_div_cancel₀ _ (hw j)

end GlobalTheory.LFun
