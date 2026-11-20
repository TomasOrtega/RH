import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical

namespace Formalism.L2.SG.Pf.UnipB

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]`.
-/
theorem mulVec_eq_sum_cols {m p : Type*} [Fintype p] [DecidableEq p] (M : Matrix m p ℂ) (c : p → ℂ) :
    M *ᵥ c = ∑ k, c k • (M *ᵥ Pi.single k 1) := by
  ext i
  rw [Finset.sum_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

/- English proof (translation)
Rewrite using `[mulVec_eq_sum_cols]`. Simplify using `only [Bv_col]`.
-/
theorem Bv_mulVec (c : Kap X → ℂ) : Bv X v *ᵥ c = ∑ k, c k • rv X.B.I v (bv X k) := by
  rw [mulVec_eq_sum_cols]
  simp only [Bv_col]

/- English proof (translation)
Rewrite using `[Bv_mulVec]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k ∈ Sum.inl '' S`. Take `⟨b, hb, rfl⟩` from `hk`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)`.

Rewrite using `[hc k hk, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem Bv_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → ℂ) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bv X v *ᵥ c ∈ Submodule.span ℂ ((fun b => rv X.B.I v (X.eR b)) '' S) := by
  rw [Bv_mulVec]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, rfl⟩` from `hx`. Introduce `k hk`. Use `show (Bv' X v *ᵥ rv X.B.I v (bv X (Sum.inl b))) k = 0`.

Rewrite using `[Bv'_rv, Pi.single_apply, if_neg]`. Introduce and unpack `rfl`. Conclude with `hk ⟨b, hb, rfl⟩`. Consider the case `zero => intro k _`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy => intro k hk`. Rewrite using `[Matrix.mulVec_add, Pi.add_apply, hx k hk, hy k hk, add_zero]`. Consider the case `smul c x _ hx => intro k hk`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, hx k hk, smul_zero]`.
-/
theorem Bv'_mulVec_supp (S : Set (Fin D.R.rS)) {y : Fin X.B.I.n → ℂ}
    (hy : y ∈ Submodule.span ℂ ((fun b => rv X.B.I v (X.eR b)) '' S)) :
    ∀ k, k ∉ Sum.inl '' S → (Bv' X v *ᵥ y) k = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro k hk
    show (Bv' X v *ᵥ rv X.B.I v (bv X (Sum.inl b))) k = 0
    rw [Bv'_rv, Pi.single_apply, if_neg]
    rintro rfl
    exact hk ⟨b, hb, rfl⟩
  | zero => intro k _; simp
  | add x y _ _ hx hy => intro k hk; rw [Matrix.mulVec_add, Pi.add_apply, hx k hk, hy k hk, add_zero]
  | smul c x _ hx => intro k hk; rw [Matrix.mulVec_smul, Pi.smul_apply, hx k hk, smul_zero]

/- English proof (translation)
Rewrite using `[Bv_mulVec, hJ_sum_right']`. Establish `e : ∀ k, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (bv X k)) = X.B.I.φ v (JB X (Sum.inl a) k)`. Introduce `k`. Rewrite using `[hJ_rv_sc]`. Both sides reduce to the same expression.

Simplify using `only [e, JB_e_row]`. Simplify using the standard rewrite rules.
-/
theorem hJ_e_Bv (a : Fin D.R.rS) (c : Kap X → ℂ) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (Bv X v *ᵥ c) = c (Sum.inr (Sum.inr a)) := by
  rw [Bv_mulVec, hJ_sum_right']
  have e : ∀ k, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (bv X k)) =
      X.B.I.φ v (JB X (Sum.inl a) k) := by
    intro k
    rw [hJ_rv_sc]
    rfl
  simp only [e, JB_e_row]
  simp

/- English proof (translation)
Rewrite using `[hJ_rv_sc]`. Use `hE_ez X u a` as an intermediate fact. Simplify using `only [hE] at this`. Rewrite using `[this, map_zero]`.
-/
theorem hermitian_basis_e_z_orthogonal (a : Fin D.R.rS) : hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 := by
  rw [hJ_rv_sc]
  have := hE_ez X u a
  simp only [hE] at this
  rw [this, map_zero]

/- English proof (translation)
Rewrite using `[hJ_rv_sc]`. Use `(wb_mem X i a).1` as an intermediate fact. Simplify using `only [hE] at this`. Simplify using `only [bv, Sum.elim_inr, Sum.elim_inl]`. Rewrite using `[this, map_zero]`.
-/
theorem hJ_rv_e_w (a : Fin D.R.rS) (i : Fin (mW X)) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (bv X (Sum.inr (Sum.inl i)))) = 0 := by
  rw [hJ_rv_sc]
  have := (wb_mem X i a).1
  simp only [hE] at this
  simp only [bv, Sum.elim_inr, Sum.elim_inl]
  rw [this, map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem lvk_inl (a : Fin D.R.rS) : lvk X (Sum.inl a) = a.1 + 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem lvk_w (i : Fin (mW X)) : lvk X (Sum.inr (Sum.inl i)) = D.R.rS + 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem lvk_f (a : Fin D.R.rS) : lvk X (Sum.inr (Sum.inr a)) = 2 * D.R.rS + 1 - a.1 := rfl

/- English proof (translation)
Break down `k with a | i | a` into its components or cases. Conclude with `(hk a rfl).elim`. Simplify using the standard rewrite rules. Rewrite using `[lvk_f]`. Use `a.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem lvk_notinl (k : Kap X) (hk : ∀ b, k ≠ Sum.inl b) : D.R.rS + 1 ≤ lvk X k := by
  rcases k with a | i | a
  · exact (hk a rfl).elim
  · simp
  · rw [lvk_f]
    have := a.2
    omega

/- English proof (translation)
Use `set M := Bv' X v * g * Bv X v with hM`. Establish `hg : g - 1 = Bv X v * (M - 1) * Bv' X v`. Rewrite using `[hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bv_mul_Bv']`. Simplify using `only [← Matrix.mul_assoc, Bv_mul_Bv', Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, Bv_mul_Bv', Matrix.mul_one]`.

Establish `hgv : ∀ y, (g - 1) *ᵥ y = Bv X v *ᵥ ((M - 1) *ᵥ (Bv' X v *ᵥ y))`. Introduce `y`. Rewrite using `[hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Establish `hperp : ∀ y, (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) y = 0) → (g - 1) *ᵥ y ∈ spanLt (fun a => rv X.B.I v (X.eR a)) D.R.rS`. Introduce `y hy`.

Use `set c := Bv' X v *ᵥ y with hc`. Establish `hyc : y = Bv X v *ᵥ c` using `by rw [hc, Matrix.mulVec_mulVec, Bv_mul_Bv', Matrix.one_mulVec]`. Establish `hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0`. Introduce `a`. Use `hJ_e_Bv X v a c` as an intermediate fact.

Rewrite `this` using `[← hyc, hy a]`. Conclude with `this.symm`. Rewrite using `[hgv, ← hc]`. Use `Bv_mulVec_mem X v _ _ fun k hk => ?_` and prove the remaining obligations. Establish `hk' : ∀ b, k ≠ Sum.inl b`.

Introduce and unpack `b rfl`. Conclude with `hk ⟨b, b.2, rfl⟩`. Rewrite using `[mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hlk` using `lvk_notinl X k hk'`.

Break down `j with b | i | b` into its components or cases. Rewrite using `[hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]`. Rewrite using `[hpat k _ (by rw [lvk_w]; omega), zero_mul]`. Rewrite using `[hcf b, mul_zero]`. Use `⟨⟨fun a => ?_, hperp _ fun a => hermitian_basis_e_z_orthogonal X u v a⟩, hperp⟩` and prove the remaining obligations.

Rewrite using `[hgv]`. Use `show Bv X v *ᵥ ((M - 1) *ᵥ (Bv' X v *ᵥ rv X.B.I v (bv X (Sum.inl a)))) ∈ _`. Rewrite using `[Bv'_rv]`. Use `Bv_mulVec_mem X v {b | b.1 < a.1} _ fun k hk => ?_` and prove the remaining obligations. Rewrite using `[mulVec_single_one]`.

Use `hpat k _ ?_` and prove the remaining obligations. Break down `k with b | i | b` into its components or cases. Establish `: ¬ b.1 < a.1` using `fun h => hk ⟨b, h, rfl⟩`. Simplify using `only [lvk, Sum.elim_inl]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [lvk, Sum.elim_inl, Sum.elim_inr]`. Use `a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [lvk, Sum.elim_inl, Sum.elim_inr]`. Use `a.2` as an intermediate fact.

Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem inN_of_pat (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hpat : InPat (lvk X) 1 (Bv' X v * g * Bv X v - 1)) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) g := by
  set M := Bv' X v * g * Bv X v with hM
  have hg : g - 1 = Bv X v * (M - 1) * Bv' X v := by
    rw [hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bv_mul_Bv']
    simp only [← Matrix.mul_assoc, Bv_mul_Bv', Matrix.one_mul]
    rw [Matrix.mul_assoc, Bv_mul_Bv', Matrix.mul_one]
  have hgv : ∀ y, (g - 1) *ᵥ y = Bv X v *ᵥ ((M - 1) *ᵥ (Bv' X v *ᵥ y)) := by
    intro y
    rw [hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

  have hperp : ∀ y, (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) y = 0) →
      (g - 1) *ᵥ y ∈ spanLt (fun a => rv X.B.I v (X.eR a)) D.R.rS := by
    intro y hy
    set c := Bv' X v *ᵥ y with hc
    have hyc : y = Bv X v *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, Bv_mul_Bv', Matrix.one_mulVec]
    have hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0 := by
      intro a
      have := hJ_e_Bv X v a c
      rw [← hyc, hy a] at this
      exact this.symm
    rw [hgv, ← hc]
    refine Bv_mulVec_mem X v _ _ fun k hk => ?_
    have hk' : ∀ b, k ≠ Sum.inl b := by
      rintro b rfl
      exact hk ⟨b, b.2, rfl⟩
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hlk := lvk_notinl X k hk'
    rcases j with b | i | b
    · rw [hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
    · rw [hpat k _ (by rw [lvk_w]; omega), zero_mul]
    · rw [hcf b, mul_zero]
  refine ⟨⟨fun a => ?_, hperp _ fun a => hermitian_basis_e_z_orthogonal X u v a⟩, hperp⟩
  rw [hgv]
  show Bv X v *ᵥ ((M - 1) *ᵥ (Bv' X v *ᵥ rv X.B.I v (bv X (Sum.inl a)))) ∈ _
  rw [Bv'_rv]
  refine Bv_mulVec_mem X v {b | b.1 < a.1} _ fun k hk => ?_
  rw [mulVec_single_one]
  refine hpat k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

/- English proof (translation)
Introduce `i j hj hij`. Establish `hM : Bv' X v * g * Bv X v - 1 = Bv' X v * (g - 1) * Bv X v`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bv'_mul_Bv]`. Establish `hcol : ((Bv' X v * g * Bv X v - 1 : Matrix (Kap X) (Kap X) ℂ)) i j = (Bv' X v *ᵥ ((g - 1) *ᵥ rv X.B.I v (bv X j))) i`. Rewrite using `[hM, ← Bv_col, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_single_one]`.

Both sides reduce to the same expression. Rewrite using `[hcol]`. Break down `j with a | w | a` into its components or cases. Use `Bv'_mulVec_supp X v {b | b.1 < a.1} (hg.1.1 a) i ?_` and prove the remaining obligations. Introduce and unpack `⟨b, hb, rfl⟩`.

Simplify using `only [lvk, Sum.elim_inl, Set.mem_setOf_eq] at hij hb`. Use linear arithmetic over natural numbers and integers. Establish `h` using `hg.2 _ fun a => hJ_rv_e_w X v a w`. Use `Bv'_mulVec_supp X v {b | b.1 < D.R.rS} h i ?_` and prove the remaining obligations. Introduce and unpack `⟨b, -, rfl⟩`.

Simplify using `only [lvk, Sum.elim_inl, Sum.elim_inr] at hij`. Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [lvk, Sum.elim_inr] at hj`. Use `a.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem half_of_inN {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ}
    (hg : InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) g) :
    ∀ i j, lvk X j ≤ D.R.rS + 1 → lvk X j < lvk X i + 1 →
      ((Bv' X v * g * Bv X v - 1 : Matrix (Kap X) (Kap X) ℂ)) i j = 0 := by
  intro i j hj hij
  have hM : Bv' X v * g * Bv X v - 1 = Bv' X v * (g - 1) * Bv X v := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bv'_mul_Bv]
  have hcol : ((Bv' X v * g * Bv X v - 1 : Matrix (Kap X) (Kap X) ℂ)) i j =
      (Bv' X v *ᵥ ((g - 1) *ᵥ rv X.B.I v (bv X j))) i := by
    rw [hM, ← Bv_col, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_single_one]
    rfl
  rw [hcol]
  rcases j with a | w | a
  · refine Bv'_mulVec_supp X v {b | b.1 < a.1} (hg.1.1 a) i ?_
    rintro ⟨b, hb, rfl⟩
    simp only [lvk, Sum.elim_inl, Set.mem_setOf_eq] at hij hb
    omega
  · have h := hg.2 _ fun a => hJ_rv_e_w X v a w
    refine Bv'_mulVec_supp X v {b | b.1 < D.R.rS} h i ?_
    rintro ⟨b, -, rfl⟩
    simp only [lvk, Sum.elim_inl, Sum.elim_inr] at hij
    have := b.2
    omega
  · simp only [lvk, Sum.elim_inr] at hj
    have := a.2
    omega

/- English proof (translation)
Establish `hs' : s⁻¹ ∈ X.NinfU u` using `(NinfSub X.eR (X.zR u)).inv_mem hs`. Establish `hMN : Mv X v s = sharp (JBv X v) (JBv' X v) (Mv X v s⁻¹)`. Use `Mv_inv X v s⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Conclude with `half_to_full (JBv_graded X v) (JBv'_graded X v) (JBv'_mul X v) (h₀ := D.R.rS + 1) (by omega) hMN (half_of_inN X u v (hs' v)) (half_of_inN X u v (hs v))`.
-/
theorem pat_of_mem {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) : InPat (lvk X) 1 (Mv X v s - 1) := by
  have hs' : s⁻¹ ∈ X.NinfU u := (NinfSub X.eR (X.zR u)).inv_mem hs
  have hMN : Mv X v s = sharp (JBv X v) (JBv' X v) (Mv X v s⁻¹) := by
    have := Mv_inv X v s⁻¹
    rwa [inv_inv] at this
  exact half_to_full (JBv_graded X v) (JBv'_graded X v) (JBv'_mul X v) (h₀ := D.R.rS + 1) (by omega) hMN
    (half_of_inN X u v (hs' v)) (half_of_inN X u v (hs v))

end Formalism.L2.SG.Pf.UnipB
