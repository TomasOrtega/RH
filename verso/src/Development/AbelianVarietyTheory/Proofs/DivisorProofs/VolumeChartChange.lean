import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

section Alt

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin n), f (fun j => v j + if j ∈ s then c j • v k else 0) = f v`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`.

Distinguish the cases in `hak : a = k`. Substitute `hak` using the available equality. Establish `e : (fun j => v j + if j ∈ insert a s then c j • v a else 0) = (fun j => v j + if j ∈ s then c j • v a else 0)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = a`.

Substitute `hj` using the available equality. Simplify using `[hc]`. Simplify using `[Finset.mem_insert, hj]`. Rewrite using `[e, ih]`. Use `set g : Fin n → M := fun j => v j + if j ∈ s then c j • v k else 0 with hg`.

Establish `e1 : (fun j => v j + if j ∈ insert a s then c j • v k else 0) = Function.update g a (v a + c a • v k)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = a`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hg, Function.update_of_ne hj, Finset.mem_insert, hj]`. Establish `e2 : Function.update g a (v a) = g`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = a`. Substitute `hj` using the available equality.

Simplify using `[hg, ha]`. Simplify using `[Function.update_of_ne hj]`. Establish `e3 : f (Function.update g a (v k)) = 0`. Use `f.map_eq_zero_of_eq _ (i := a) (j := k) ?_ hak` and prove the remaining obligations. Simplify using `[Function.update_of_ne (Ne.symm hak), hg, hc]`.

Rewrite using `[e1, f.map_update_add, f.map_update_smul, e2, ih, e3, smul_zero, add_zero]`. Simplify using `using key Finset.univ`.
-/
theorem altMap_add_smul_self {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) (k : Fin n) (c : Fin n → R)
    (hc : c k = 0) : f (fun j => v j + c j • v k) = f v := by
  classical
  have key : ∀ s : Finset (Fin n), f (fun j => v j + if j ∈ s then c j • v k else 0) = f v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      by_cases hak : a = k
      · subst hak
        have e : (fun j => v j + if j ∈ insert a s then c j • v a else 0) =
            (fun j => v j + if j ∈ s then c j • v a else 0) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hc]
          · simp [Finset.mem_insert, hj]
        rw [e, ih]
      · set g : Fin n → M := fun j => v j + if j ∈ s then c j • v k else 0 with hg
        have e1 : (fun j => v j + if j ∈ insert a s then c j • v k else 0) = Function.update g a (v a + c a • v k) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp
          · simp [hg, Function.update_of_ne hj, Finset.mem_insert, hj]
        have e2 : Function.update g a (v a) = g := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hg, ha]
          · simp [Function.update_of_ne hj]
        have e3 : f (Function.update g a (v k)) = 0 := by
          refine f.map_eq_zero_of_eq _ (i := a) (j := k) ?_ hak
          simp [Function.update_of_ne (Ne.symm hak), hg, hc]
        rw [e1, f.map_update_add, f.map_update_smul, e2, ih, e3, smul_zero, add_zero]
  simpa using key Finset.univ

/- English proof (translation)
Set `p : Fin d → Fin d` to `fun j => (τ j).pred (hne j)`. Establish `hp : Function.Injective p`. Introduce `a b hab`. Apply `hinj` to reduce the goal to its premises. Simplify `congrArg Fin.succ hab` using `[p]`.

Use `⟨Equiv.ofBijective p (Finite.injective_iff_bijective.1 hp), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using `[p]`.
-/
theorem exists_perm_succ {d : ℕ} (τ : Fin d → Fin (d + 1)) (hinj : Function.Injective τ) (hne : ∀ j, τ j ≠ 0) :
    ∃ π : Equiv.Perm (Fin d), τ = Fin.succ ∘ π := by
  let p : Fin d → Fin d := fun j => (τ j).pred (hne j)
  have hp : Function.Injective p := by
    intro a b hab
    apply hinj
    simpa [p] using congrArg Fin.succ hab
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.1 hp), ?_⟩
  funext j
  simp [p]

/- English proof (translation)
Consider the cases of `i using Fin.cases with`. Consider the case `zero => exact ⟨1, by simp [h0]⟩`. Consider the case `succ i'`. Establish `hd : 0 < d` using `Nat.lt_of_le_of_lt (Nat.zero_le _) i'.isLt`. Use `set i : Fin (d + 1) := i'.succ with hi`.

Use `set j0 : Fin d := ⟨0, hd⟩ with hj0`. Establish `hσ0 : i.succAbove j0 = 0`. Rewrite using `[Fin.succAbove_of_castSucc_lt]`. Both sides reduce to the same expression. Rewrite using `[Fin.lt_def]`.

Simplify using `[hi, hj0]`. Use `set w : Fin d → M := fun j => θ (i.succAbove j) - θ i with hw`. Use `set c : Fin d → R := fun j => if j = j0 then 0 else -1 with hc`. Establish `k1` using `altMap_add_smul_self f w j0 c (by simp [hc])`. Establish `e1 : (fun j => w j + c j • w j0) = Function.update (θ ∘ i.succAbove) j0 ((-1 : R) • θ i)`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = j0`. Substitute `hj` using the available equality. Simplify using `[hw, hc, hσ0, h0]`. Simplify using `[hw, hc, hj, hσ0, h0, Function.update_of_ne hj]`.

Use `set τ : Fin d → Fin (d + 1) := Function.update i.succAbove j0 i with hτ`. Establish `e2 : Function.update (θ ∘ i.succAbove) j0 (θ i) = θ ∘ τ`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = j0`. Substitute `hj` using the available equality.

Simplify using `[hτ]`. Simplify using `[hτ, Function.update_of_ne hj]`. Establish `hτinj : Function.Injective τ`. Introduce `a b hab`. Apply the tactic sequence `by_cases ha : a = j0 <;> by_cases hb : b = j0`.

Rewrite using `[ha, hb]`. Simplify using `[hτ, ha, Function.update_of_ne hb] at hab`. Simplify using `[hτ, hb, Function.update_of_ne ha] at hab`. Simplify using `only [hτ, Function.update_of_ne ha, Function.update_of_ne hb] at hab`. Conclude with `Fin.succAbove_right_injective hab`.

Establish `hτne : ∀ j, τ j ≠ 0`. Introduce `j`. Distinguish the cases in `hj : j = j0`. Substitute `hj` using the available equality. Simplify using `[hτ, hi]`.

Rewrite using `[hτ, Function.update_of_ne hj, ← hσ0]`. Conclude with `fun h => hj (Fin.succAbove_right_injective h)`. Take `⟨π, hπ⟩` from `exists_perm_succ τ hτinj hτne`. Use `⟨-Equiv.Perm.sign π, ?_⟩` and prove the remaining obligations. Rewrite using `[← k1, e1, f.map_update_smul, e2, hπ]`.

Establish `e3 : θ ∘ (Fin.succ ∘ ⇑π) = (fun j => θ j.succ) ∘ ⇑π` using `rfl`. Rewrite using `[e3, f.map_perm, Units.neg_smul, neg_one_smul]`.
-/
theorem altMap_sub_succAbove {d : ℕ} (f : M [⋀^Fin d]→ₗ[R] N) (θ : Fin (d + 1) → M) (h0 : θ 0 = 0)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, f (fun j => θ (i.succAbove j) - θ i) = ε • f (fun j => θ j.succ) := by
  classical
  cases i using Fin.cases with
  | zero => exact ⟨1, by simp [h0]⟩
  | succ i' =>
    have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i'.isLt
    set i : Fin (d + 1) := i'.succ with hi
    set j0 : Fin d := ⟨0, hd⟩ with hj0
    have hσ0 : i.succAbove j0 = 0 := by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · rw [Fin.lt_def]; simp [hi, hj0]
    set w : Fin d → M := fun j => θ (i.succAbove j) - θ i with hw
    set c : Fin d → R := fun j => if j = j0 then 0 else -1 with hc
    have k1 := altMap_add_smul_self f w j0 c (by simp [hc])
    have e1 : (fun j => w j + c j • w j0) = Function.update (θ ∘ i.succAbove) j0 ((-1 : R) • θ i) := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hw, hc, hσ0, h0]
      · simp [hw, hc, hj, hσ0, h0, Function.update_of_ne hj]
    set τ : Fin d → Fin (d + 1) := Function.update i.succAbove j0 i with hτ
    have e2 : Function.update (θ ∘ i.succAbove) j0 (θ i) = θ ∘ τ := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hτ]
      · simp [hτ, Function.update_of_ne hj]
    have hτinj : Function.Injective τ := by
      intro a b hab
      by_cases ha : a = j0 <;> by_cases hb : b = j0
      · rw [ha, hb]
      · simp [hτ, ha, Function.update_of_ne hb] at hab
      · simp [hτ, hb, Function.update_of_ne ha] at hab
      · simp only [hτ, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact Fin.succAbove_right_injective hab
    have hτne : ∀ j, τ j ≠ 0 := by
      intro j
      by_cases hj : j = j0
      · subst hj; simp [hτ, hi]
      · rw [hτ, Function.update_of_ne hj, ← hσ0]
        exact fun h => hj (Fin.succAbove_right_injective h)
    obtain ⟨π, hπ⟩ := exists_perm_succ τ hτinj hτne
    refine ⟨-Equiv.Perm.sign π, ?_⟩
    rw [← k1, e1, f.map_update_smul, e2, hπ]
    have e3 : θ ∘ (Fin.succ ∘ ⇑π) = (fun j => θ j.succ) ∘ ⇑π := rfl
    rw [e3, f.map_perm, Units.neg_smul, neg_one_smul]

end Alt

/- English proof (translation)
Establish `hx` using `h.pd.ne`. Use `set y : Fin (d + 1) → K := fun a => algebraMap F K (x a / x 0) with hy`. Establish `hy0 : ∀ a, y a ≠ 0` using `fun a => (map_ne_zero _).2 (div_ne_zero (hx a) (hx 0))`. Use `set θ : Fin (d + 1) → Ω[K⁄k] := fun a => (y a)⁻¹ • D k K (y a) with hθ`. Establish `hθ0 : θ 0 = 0` using `by show (algebraMap F K (x 0 / x 0))⁻¹ • D k K (algebraMap F K (x 0 / x 0)) = 0`.

Rewrite using `[div_self (hx 0), map_one, Derivation.map_one_eq_zero, smul_zero]`. Establish `hD : ∀ a, D k K (algebraMap F K (x a / x i)) = algebraMap F K (x a / x i) • (θ a - θ i)`. Introduce `a`. Establish `e : algebraMap F K (x a / x i) = y a / y i`. Simplify using `only [hy, ← map_div₀]`.

Use `congr 1`. Clear denominators, using `[hx 0, hx i]` for the nonvanishing conditions. Establish `ha` using `hy0 a`. Establish `hi` using `hy0 i`. Rewrite using `[e, Derivation.leibniz_div, hθ]`.

Simplify using `only [smul_sub, smul_smul]`. Apply the tactic sequence `congr 2 <;> field_simp`. Take `⟨ε, hε⟩` from `altMap_sub_succAbove (ExteriorAlgebra.ιMulti K d) θ hθ0 i`. Use `⟨ε, ?_⟩` and prove the remaining obligations. Establish `hprod : algebraMap F K (∏ j, x j / x i) = ∏ j, algebraMap F K (x (i.succAbove j) / x i)`.

Rewrite using `[Fin.prod_univ_succAbove _ i, div_self (hx i), one_mul, map_prod]`. Simplify using `only [hD]`. Rewrite using `[AlternatingMap.map_smul_univ, hε, hprod]`. Rewrite using `[smul_comm]`. Both sides reduce to the same expression.
-/
theorem volume_chart_change (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (h : IsFinCover k K x)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) =
      ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  have hx := h.pd.ne
  set y : Fin (d + 1) → K := fun a => algebraMap F K (x a / x 0) with hy
  have hy0 : ∀ a, y a ≠ 0 := fun a => (map_ne_zero _).2 (div_ne_zero (hx a) (hx 0))
  set θ : Fin (d + 1) → Ω[K⁄k] := fun a => (y a)⁻¹ • D k K (y a) with hθ
  have hθ0 : θ 0 = 0 := by
    show (algebraMap F K (x 0 / x 0))⁻¹ • D k K (algebraMap F K (x 0 / x 0)) = 0
    rw [div_self (hx 0), map_one, Derivation.map_one_eq_zero, smul_zero]
  have hD : ∀ a, D k K (algebraMap F K (x a / x i)) = algebraMap F K (x a / x i) • (θ a - θ i) := by
    intro a
    have e : algebraMap F K (x a / x i) = y a / y i := by
      simp only [hy, ← map_div₀]
      congr 1
      field_simp [hx 0, hx i]
    have ha := hy0 a
    have hi := hy0 i
    rw [e, Derivation.leibniz_div, hθ]
    simp only [smul_sub, smul_smul]
    congr 2 <;> field_simp
  obtain ⟨ε, hε⟩ := altMap_sub_succAbove (ExteriorAlgebra.ιMulti K d) θ hθ0 i
  refine ⟨ε, ?_⟩
  have hprod : algebraMap F K (∏ j, x j / x i) = ∏ j, algebraMap F K (x (i.succAbove j) / x i) := by
    rw [Fin.prod_univ_succAbove _ i, div_self (hx i), one_mul, map_prod]
  simp only [hD]
  rw [AlternatingMap.map_smul_univ, hε, hprod]
  rw [smul_comm]
  rfl

end GlobalTheory.PD
