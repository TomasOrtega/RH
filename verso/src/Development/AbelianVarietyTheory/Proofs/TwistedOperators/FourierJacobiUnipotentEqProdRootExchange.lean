import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.FJUnipotent
open GlobalTheory.RootEx.Radical

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def midLev (ρ : ℕ) : n ⊕ Fin c → ℕ :=
  Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1))

def midGroup (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Uni (midLev ρ) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun hx hy => Uni.mul hx hy
  inv_mem' := fun hx => Uni.inv hx

/- English proof (translation)
Establish `key : ∀ p, p = ρ ∨ p = ρ + 1 → N k n c p ≤ midGroup k n c ρ`. Introduce and unpack `p hp g hg`. Establish `hg'` using `(mem_N_iff g).1 hg`. Use `show Uni (midLev ρ) g.val`. Introduce `r s hrs`.

Apply `hg' r s` to reduce the goal to its premises. Apply the tactic sequence `rcases r with r | i <;> rcases s with s | j <;>`. Apply the tactic sequence `simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega`. Conclude with `sup_le (key ρ (Or.inl rfl)) (key (ρ + 1) (Or.inr rfl))`.
-/
theorem NFJ_le_midGroup (ρ : ℕ) : NFJ k n c ρ ≤ midGroup k n c ρ := by
  have key : ∀ p, p = ρ ∨ p = ρ + 1 → N k n c p ≤ midGroup k n c ρ := by
    rintro p hp g hg
    have hg' := (mem_N_iff g).1 hg
    show Uni (midLev ρ) g.val
    intro r s hrs
    apply hg' r s
    rcases r with r | i <;> rcases s with s | j <;>
      simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  exact sup_le (key ρ (Or.inl rfl)) (key (ρ + 1) (Or.inr rfl))

/- English proof (translation)
Establish `hg' : ∀ r s, midLev (n` using `n) (c := c) P.val s ≤ midLev P.val r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := hg`. Use `⟨g * colE c (P.val + 1) (-fun r => g.val (Sum.inl r) (Sum.inr P)), ?_, fun r => g.val (Sum.inl r) (Sum.inr P), ?_⟩` and prove the remaining obligations. Rewrite using `[mem_N_iff]`. Introduce `r s hrs`. Rewrite using `[Units.val_mul]`.

Break down `s with s | j` into its components or cases. Rewrite using `[GlobalTheory.RootEx.Exchange.mul_colE_inl]`. Apply `hg'` to reduce the goal to its premises. Apply the tactic sequence `rcases r with r | i <;>`. Apply the tactic sequence `simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega`.

Rewrite using `[GlobalTheory.RootEx.Exchange.mul_colE_inr]`. Distinguish the cases in `hj : j = P`. Establish `hc : j.val + 1 = P.val + 1` using `by rw [hj]`. Rewrite using `[if_pos hc, hj]`. Break down `r with r | i` into its components or cases.

Establish `hX : ∀ t, g.val (Sum.inl r) (Sum.inl t) = if r = t then 1 else 0`. Introduce `t`. Rewrite using `[hg' _ _ (by simp only [midLev, Sum.elim_inl]; omega)]`. Simplify using `[Matrix.one_apply]`. Simplify using `[hX]`.

Establish `hi : P.val ≤ i.val`. Rewrite `hrs` using `[hj]`. Simplify using `only [lev, Sum.elim_inr] at hrs`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `hg' (Sum.inr i) (Sum.inr P) (by simp only [midLev, Sum.elim_inr]; omega)`.

Establish `h2 : ∀ t, g.val (Sum.inr i) (Sum.inl t) = 0` using `fun t => by`. Rewrite using `[hg' _ _ (by simp only [midLev, Sum.elim_inl, Sum.elim_inr]; omega)]`. Simplify using the standard rewrite rules. Simplify using `[h1, h2]`. Establish `hj' : j.val ≠ P.val` using `fun h => hj (Fin.ext h)`.

Establish `hc : ¬ (j.val + 1 = P.val + 1)` using `fun h => hj' (by omega)`. Rewrite using `[if_neg hc, add_zero]`. Apply `hg'` to reduce the goal to its premises. Apply the tactic sequence `rcases r with r | i <;>`. Apply the tactic sequence `simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega`.

Rewrite using `[mul_assoc, GlobalTheory.RootEx.Exchange.colE_neg_mul, mul_one]`.
-/
theorem exists_col (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ midGroup k n c P.val) :
    ∃ u ∈ N k n c (P.val + 1), ∃ β : n → k, g = u * colE c (P.val + 1) β := by
  have hg' : ∀ r s, midLev (n := n) (c := c) P.val s ≤ midLev P.val r →
      g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := hg
  refine ⟨g * colE c (P.val + 1) (-fun r => g.val (Sum.inl r) (Sum.inr P)), ?_,
    fun r => g.val (Sum.inl r) (Sum.inr P), ?_⟩
  · rw [mem_N_iff]
    intro r s hrs
    rw [Units.val_mul]
    rcases s with s | j
    · rw [GlobalTheory.RootEx.Exchange.mul_colE_inl]
      apply hg'
      rcases r with r | i <;>
        simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
    · rw [GlobalTheory.RootEx.Exchange.mul_colE_inr]
      by_cases hj : j = P
      · have hc : j.val + 1 = P.val + 1 := by rw [hj]
        rw [if_pos hc, hj]
        rcases r with r | i
        · have hX : ∀ t, g.val (Sum.inl r) (Sum.inl t) = if r = t then 1 else 0 := by
            intro t
            rw [hg' _ _ (by simp only [midLev, Sum.elim_inl]; omega)]
            simp [Matrix.one_apply]
          simp [hX]
        · have hi : P.val ≤ i.val := by
            rw [hj] at hrs
            simp only [lev, Sum.elim_inr] at hrs
            omega
          have h1 := hg' (Sum.inr i) (Sum.inr P) (by simp only [midLev, Sum.elim_inr]; omega)
          have h2 : ∀ t, g.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
            rw [hg' _ _ (by simp only [midLev, Sum.elim_inl, Sum.elim_inr]; omega)]
            simp
          simp [h1, h2]
      · have hj' : j.val ≠ P.val := fun h => hj (Fin.ext h)
        have hc : ¬ (j.val + 1 = P.val + 1) := fun h => hj' (by omega)
        rw [if_neg hc, add_zero]
        apply hg'
        rcases r with r | i <;>
          simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  · rw [mul_assoc, GlobalTheory.RootEx.Exchange.colE_neg_mul, mul_one]

end

/- English proof (translation)
Introduce `k _ n _ _ c ρ _ hρc`. Establish `hle` using `NFJ_le_midGroup (k := k) (n := n) (c := c) ρ`. Establish `hcol : ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k, g = u * colE c (ρ + 1) β` using `fun g hg => exists_col ⟨ρ, hρc⟩ (hle hg)`. Establish `hcolN : ∀ β : n → k, colE c (ρ + 1) β ∈ N k n c ρ` using `fun β => colE_mem β (Nat.lt_succ_self ρ)`. Establish `hmid : ∀ g : GL (n ⊕ Fin c) k, g ∈ midGroup k n c ρ → g ∈ NFJ k n c ρ`.

Introduce `g hg`. Take `⟨u, hu, β, rfl⟩` from `exists_col (k := k) ⟨ρ, hρc⟩ hg`. Conclude with `(NFJ k n c ρ).mul_mem (le_sup_right (a := N k n c ρ) hu) (le_sup_left (b := N k n c (ρ + 1)) (hcolN β))`. Use `⟨fun g => ⟨fun hg => ?_, ?_⟩, fun g => ⟨fun hg => hle hg, fun hg => hmid g hg⟩, hcol⟩` and prove the remaining obligations. Take `⟨u, hu, β, hg'⟩` from `hcol g⁻¹ ((NFJ k n c ρ).inv_mem hg)`.

Use `⟨(colE c (ρ + 1) β)⁻¹, (N k n c ρ).inv_mem (hcolN β), u⁻¹, (N k n c (ρ + 1)).inv_mem hu, ?_⟩` and prove the remaining obligations. Rewrite using `[← _root_.mul_inv_rev, ← hg', inv_inv]`. Introduce and unpack `⟨x, hx, y, hy, rfl⟩`. Conclude with `(NFJ k n c ρ).mul_mem (le_sup_left (b := N k n c (ρ + 1)) hx) (le_sup_right (a := N k n c ρ) hy)`.
-/
theorem fj_unipotent : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ NFJ k n c ρ ↔ ∃ x ∈ N k n c ρ, ∃ y ∈ N k n c (ρ + 1), g = x * y) ∧ (∀ g : GL (n ⊕ Fin c) k, g ∈ NFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k, g = u * colE c (ρ + 1) β := by
  intro k _ n _ _ c ρ _ hρc
  have hle := NFJ_le_midGroup (k := k) (n := n) (c := c) ρ
  have hcol : ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k,
      g = u * colE c (ρ + 1) β :=
    fun g hg => exists_col ⟨ρ, hρc⟩ (hle hg)
  have hcolN : ∀ β : n → k, colE c (ρ + 1) β ∈ N k n c ρ :=
    fun β => colE_mem β (Nat.lt_succ_self ρ)
  have hmid : ∀ g : GL (n ⊕ Fin c) k, g ∈ midGroup k n c ρ → g ∈ NFJ k n c ρ := by
    intro g hg
    obtain ⟨u, hu, β, rfl⟩ := exists_col (k := k) ⟨ρ, hρc⟩ hg
    exact (NFJ k n c ρ).mul_mem (le_sup_right (a := N k n c ρ) hu)
      (le_sup_left (b := N k n c (ρ + 1)) (hcolN β))
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun g => ⟨fun hg => hle hg, fun hg => hmid g hg⟩, hcol⟩
  · obtain ⟨u, hu, β, hg'⟩ := hcol g⁻¹ ((NFJ k n c ρ).inv_mem hg)
    refine ⟨(colE c (ρ + 1) β)⁻¹, (N k n c ρ).inv_mem (hcolN β), u⁻¹,
      (N k n c (ρ + 1)).inv_mem hu, ?_⟩
    rw [← _root_.mul_inv_rev, ← hg', inv_inv]
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact (NFJ k n c ρ).mul_mem (le_sup_left (b := N k n c (ρ + 1)) hx)
      (le_sup_right (a := N k n c ρ) hy)

end GlobalTheory.RootEx.FJUnipotent
