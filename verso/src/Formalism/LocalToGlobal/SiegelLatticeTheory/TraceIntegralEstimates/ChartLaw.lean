import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open scoped Matrix
open Finset Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.S.Pv.Chart

variable {n r : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Simplify using `only [hJ, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem hJ_add (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem hJ_smul (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [hJ, Matrix.mulVec_zero, dotProduct_zero]`.
-/
theorem hJ_zero (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp only [hJ, Matrix.mulVec_zero, dotProduct_zero]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_empty, Finset.sum_empty, hJ_zero]`. Introduce `i t hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, hJ_add, ih]`.
-/
theorem hJ_sum {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (g : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, g i) = ∑ i ∈ s, hJ ε x (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, hJ_zero]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hJ_add, ih]

variable (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
  (hdual : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
include hdual

/- English proof (translation)
Unfold `spanLt at hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨d, hd, rfl⟩` from `hx`. Rewrite `hd` using `[Set.mem_setOf_eq]`.

Use `⟨?_, fun c hc => ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hdual, ite_smul, one_smul, zero_smul]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ d (fun c => e c), if_pos (Finset.mem_univ d)]`. Rewrite using `[hdual, if_neg]`. Introduce `h`.

Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Consider the case `zero`. Use `⟨?_, fun c _ => hJ_zero ε _⟩` and prove the remaining obligations. Repeatedly rewrite using `[hJ_zero, zero_smul, Finset.sum_const_zero]`.

Consider the case `add x y _ _ hx hy`. Use `⟨?_, fun c hc => by rw [hJ_add, hx.2 c hc, hy.2 c hc, add_zero]⟩` and prove the remaining obligations. Repeatedly rewrite using `[hJ_add, add_smul]`. Rewrite using `[Finset.sum_add_distrib, ← hx.1, ← hy.1]`. Consider the case `smul a x _ hx`.

Use `⟨?_, fun c hc => by rw [hJ_smul, hx.2 c hc, mul_zero]⟩` and prove the remaining obligations. Repeatedly rewrite using `[hJ_smul, mul_smul]`. Rewrite using `[← Finset.smul_sum, ← hx.1]`.
-/
theorem span_expand (b : ℕ) (v : Fin n → ℂ) (hv : v ∈ spanLt e b) :
    v = ∑ c, hJ ε (f c) v • e c ∧ ∀ c : Fin r, b ≤ c.1 → hJ ε (f c) v = 0 := by
  unfold spanLt at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [Set.mem_setOf_eq] at hd
    refine ⟨?_, fun c hc => ?_⟩
    · simp_rw [hdual, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq' Finset.univ d (fun c => e c), if_pos (Finset.mem_univ d)]
    · rw [hdual, if_neg]
      intro h
      subst h
      omega
  | zero =>
    refine ⟨?_, fun c _ => hJ_zero ε _⟩
    simp_rw [hJ_zero, zero_smul, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    refine ⟨?_, fun c hc => by rw [hJ_add, hx.2 c hc, hy.2 c hc, add_zero]⟩
    simp_rw [hJ_add, add_smul]
    rw [Finset.sum_add_distrib, ← hx.1, ← hy.1]
  | smul a x _ hx =>
    refine ⟨?_, fun c hc => by rw [hJ_smul, hx.2 c hc, mul_zero]⟩
    simp_rw [hJ_smul, mul_smul]
    rw [← Finset.smul_sum, ← hx.1]

include hfz

/- English proof (translation)
Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simp only [fam, Fin.snoc_last]`. Conclude with `hfz c`. Consider the case `cast b'`. Simplify using `only [fam, Fin.snoc_castSucc]`.

Rewrite using `[hdual, if_neg]`. Introduce `h`. Substitute `h` using the available equality. Simplify using `at hcb`.
-/
theorem hJ_fam (c : Fin r) (b : Fin (r + 1)) (hcb : c.1 < b.1) : hJ ε (f c) (fam e z b) = 0 := by
  induction b using Fin.lastCases with
  | last => simp only [fam, Fin.snoc_last]; exact hfz c
  | cast b' =>
    simp only [fam, Fin.snoc_castSucc]
    rw [hdual, if_neg]
    intro h
    subst h
    simp at hcb

/- English proof (translation)
Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simpa only [fam, Fin.snoc_last, Fin.val_last] using hg.2`. Consider the case `cast b' => simpa only [fam, Fin.snoc_castSucc, Fin.coe_castSucc] using hg.1 b'`.
-/
theorem sub_mem_spanLt {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (b : Fin (r + 1)) :
    (g - 1) *ᵥ fam e z b ∈ spanLt e b.1 := by
  induction b using Fin.lastCases with
  | last => simpa only [fam, Fin.snoc_last, Fin.val_last] using hg.2
  | cast b' => simpa only [fam, Fin.snoc_castSucc, Fin.coe_castSucc] using hg.1 b'

/- English proof (translation)
Take `⟨hw, hw0⟩` from `span_expand ε e f hdual b.1 _ (sub_mem_spanLt ε e f z hdual hfz hg b)`. Establish `hgw : g *ᵥ fam e z b = fam e z b + (g - 1) *ᵥ fam e z b`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Establish `hc : ∀ c : Fin r, (if c.1 < b.1 then hJ ε (f c) (g *ᵥ fam e z b) else 0) = hJ ε (f c) ((g - 1) *ᵥ fam e z b)`.

Introduce `c`. Use `split_ifs with h`. Rewrite using `[hgw, hJ_add, hJ_fam ε e f z hdual hfz c b h, zero_add]`. Conclude with `(hw0 c (not_lt.mp h)).symm`. Repeatedly rewrite using `[hc]`.

Rewrite using `[← hw]`. Conclude with `hgw`.
-/
theorem expand {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (b : Fin (r + 1)) :
    g *ᵥ fam e z b = fam e z b + ∑ c : Fin r, (if c.1 < b.1 then hJ ε (f c) (g *ᵥ fam e z b) else 0) • e c := by
  obtain ⟨hw, hw0⟩ := span_expand ε e f hdual b.1 _ (sub_mem_spanLt ε e f z hdual hfz hg b)
  have hgw : g *ᵥ fam e z b = fam e z b + (g - 1) *ᵥ fam e z b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hc : ∀ c : Fin r, (if c.1 < b.1 then hJ ε (f c) (g *ᵥ fam e z b) else 0) =
      hJ ε (f c) ((g - 1) *ᵥ fam e z b) := by
    intro c
    split_ifs with h
    · rw [hgw, hJ_add, hJ_fam ε e f z hdual hfz c b h, zero_add]
    · exact (hw0 c (not_lt.mp h)).symm
  simp_rw [hc]
  rw [← hw]
  exact hgw

/- English proof (translation)
Establish `hw0` using `(span_expand ε e f hdual a.1 _ (hg.1 a)).2 a le_rfl`. Establish `hgw : g *ᵥ e a = e a + (g - 1) *ᵥ e a`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[hgw, hJ_add, hw0, hdual, if_pos rfl, add_zero]`.
-/
theorem coef_diag {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : Fin r) :
    hJ ε (f a) (g *ᵥ e a) = 1 := by
  have hw0 := (span_expand ε e f hdual a.1 _ (hg.1 a)).2 a le_rfl
  have hgw : g *ᵥ e a = e a + (g - 1) *ᵥ e a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hgw, hJ_add, hw0, hdual, if_pos rfl, add_zero]

/- English proof (translation)
Establish `hw0` using `(span_expand ε e f hdual c.1 _ (hg.1 c)).2 a h.le`. Establish `hgw : g *ᵥ e c = e c + (g - 1) *ᵥ e c`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[hgw, hJ_add, hw0, hdual, if_neg (fun h' => by subst h'; exact lt_irrefl _ h), add_zero]`.
-/
theorem coef_low {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a c : Fin r) (h : c.1 < a.1) :
    hJ ε (f a) (g *ᵥ e c) = 0 := by
  have hw0 := (span_expand ε e f hdual c.1 _ (hg.1 c)).2 a h.le
  have hgw : g *ᵥ e c = e c + (g - 1) *ᵥ e c := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hgw, hJ_add, hw0, hdual, if_neg (fun h' => by subst h'; exact lt_irrefl _ h), add_zero]

/- English proof (translation)
Establish `hx` using `expand ε e f z hdual hfz h₂ b`. Use `conv_lhs => rw [← Matrix.mulVec_mulVec, hx]`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_sum, hJ_add, hJ_sum]`. Repeatedly rewrite using `[Matrix.mulVec_smul, hJ_smul]`. Rewrite using `[add_assoc]`.

Use `congr 1`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos hab, coef_diag ε e f z hdual hfz h₁ a, mul_one, if_neg (by omega), zero_add]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Establish `hca : c ≠ a` using `Finset.ne_of_mem_erase hc`.

Break down `lt_or_gt_of_ne (fun h' : c.1 = a.1 => hca (Fin.ext h')) with h | h` into its components or cases. Rewrite using `[coef_low ε e f z hdual hfz h₁ a c h, mul_zero, if_neg (by omega)]`. Distinguish the cases in `hcb : c.1 < b.1`. Rewrite using `[if_pos hcb, if_pos ⟨h, hcb⟩, mul_comm]`. Rewrite using `[if_neg hcb, if_neg (by omega), zero_mul]`.
-/
theorem coef_mul {g₁ g₂ : Matrix (Fin n) (Fin n) ℂ} (h₁ : InS e z g₁) (h₂ : InS e z g₂) (a : Fin r)
    (b : Fin (r + 1)) (hab : a.1 < b.1) :
    hJ ε (f a) ((g₁ * g₂) *ᵥ fam e z b) = hJ ε (f a) (g₁ *ᵥ fam e z b) + hJ ε (f a) (g₂ *ᵥ fam e z b) +
      ∑ c : Fin r, if a.1 < c.1 ∧ c.1 < b.1 then hJ ε (f a) (g₁ *ᵥ e c) * hJ ε (f c) (g₂ *ᵥ fam e z b) else 0 := by
  have hx := expand ε e f z hdual hfz h₂ b
  conv_lhs => rw [← Matrix.mulVec_mulVec, hx]
  rw [Matrix.mulVec_add, Matrix.mulVec_sum, hJ_add, hJ_sum]
  simp_rw [Matrix.mulVec_smul, hJ_smul]
  rw [add_assoc]
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    if_pos hab, coef_diag ε e f z hdual hfz h₁ a, mul_one, if_neg (by omega), zero_add]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  have hca : c ≠ a := Finset.ne_of_mem_erase hc
  rcases lt_or_gt_of_ne (fun h' : c.1 = a.1 => hca (Fin.ext h')) with h | h
  · rw [coef_low ε e f z hdual hfz h₁ a c h, mul_zero, if_neg (by omega)]
  · by_cases hcb : c.1 < b.1
    · rw [if_pos hcb, if_pos ⟨h, hcb⟩, mul_comm]
    · rw [if_neg hcb, if_neg (by omega), zero_mul]

end Formalism.L2.S.Pv.Chart

end
