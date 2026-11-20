import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.VolN

section Alg
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

def lm (P : ι → ι → Prop) (h : Matrix ι ι k) :
    Matrix {rs : ι × ι // P rs.1 rs.2} {rs : ι × ι // P rs.1 rs.2} k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then h a.1.1 b.1.1 else 0

def rm (P : ι → ι → Prop) (h : Matrix ι ι k) :
    Matrix {rs : ι × ι // P rs.1 rs.2} {rs : ι × ι // P rs.1 rs.2} k :=
  Matrix.of fun a b => if a.1.1 = b.1.1 then h b.1.2 a.1.2 else 0

def ext0 (P : ι → ι → Prop) [DecidableRel P] (e : {rs : ι × ι // P rs.1 rs.2} → k) : Matrix ι ι k :=
  Matrix.of fun r s => if h : P r s then e ⟨(r, s), h⟩ else 0

omit [DecidableEq ι] in
/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type' (fun r s => w (r, s) * ext0 P e r s), ← Finset.sum_filter_of_ne (p := fun rs : ι × ι => P rs.1 rs.2), Finset.sum_subtype (p := fun rs : ι × ι => P rs.1 rs.2) (F := F) _ (by simp)]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[ext0, b.2]`. Introduce `x _ hx`. Assume the negation of the conclusion as `h`.

Simplify using `[ext0, h] at hx`.
-/
theorem sum_extendByZero_fin_eq_sum_of_eq (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (w : ι × ι → k) :
    ∑ b : {rs : ι × ι // P rs.1 rs.2}, w b.1 * e b = ∑ r, ∑ s, w (r, s) * ext0 P e r s := by
  rw [← Fintype.sum_prod_type' (fun r s => w (r, s) * ext0 P e r s),
    ← Finset.sum_filter_of_ne (p := fun rs : ι × ι => P rs.1 rs.2),
    Finset.sum_subtype (p := fun rs : ι × ι => P rs.1 rs.2) (F := F) _ (by simp)]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [ext0, b.2]
  · intro x _ hx
    by_contra h
    simp [ext0, h] at hx

/- English proof (translation)
Use `sum_extendByZero_fin_eq_sum_of_eq P e (fun b => if a.1.2 = b.2 then h a.1.1 b.1 else 0)` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct, lm, Matrix.of_apply]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem mul_matrixExtendSelectedEntriesByZero_apply (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k)
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (a : {rs : ι × ι // P rs.1 rs.2}) :
    (h * ext0 P e) a.1.1 a.1.2 = (lm P h).mulVec e a := by
  have := sum_extendByZero_fin_eq_sum_of_eq P e (fun b => if a.1.2 = b.2 then h a.1.1 b.1 else 0)
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, lm, Matrix.of_apply]
  rw [this]
  simp

/- English proof (translation)
Use `sum_extendByZero_fin_eq_sum_of_eq P e (fun b => if a.1.1 = b.1 then h b.2 a.1.2 else 0)` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct, rm, Matrix.of_apply]`. Rewrite using `[this, Finset.sum_comm]`. Simplify using `[mul_comm]`.
-/
theorem matrixExtendByZero_mul (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k)
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (a : {rs : ι × ι // P rs.1 rs.2}) :
    (ext0 P e * h) a.1.1 a.1.2 = (rm P h).mulVec e a := by
  have := sum_extendByZero_fin_eq_sum_of_eq P e (fun b => if a.1.1 = b.1 then h b.2 a.1.2 else 0)
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, rm, Matrix.of_apply]
  rw [this, Finset.sum_comm]
  simp [mul_comm]

/- English proof (translation)
Set `_ : LinearOrder ι` to `LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective`. Establish `ht : (lm P h).BlockTriangular (fun a => a.1.2)`. Introduce `a b hab`. Simplify using `only [lm, Matrix.of_apply]`. Rewrite using `[if_neg (ne_of_lt hab).symm]`.

Rewrite using `[ht.det_fintype]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Set `E : {r // P r s} ≃ {a : {rs : ι × ι // P rs.1 rs.2} // a.1.2 = s}` to `{ toFun := fun r => ⟨⟨(r.1, s), r.2⟩, rfl⟩ invFun := fun a => ⟨a.1.1.1, by have h1 := a.1.2; have h2 : a.1.1.2 = s := a.2; rwa [h2] at h1⟩ left_inv := fun _ => rfl right_inv := by rintro ⟨⟨⟨r, s'⟩, h⟩, rfl⟩; rfl }`. Rewrite using `[← Matrix.det_submatrix_equiv_self E]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[toSquareBlock_def, toSquareBlockProp_def, lm, E]`.
-/
theorem det_lm (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    [DecidableEq {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k) :
    (lm P h).det = ∏ s, (h.toSquareBlockProp fun r => P r s).det := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have ht : (lm P h).BlockTriangular (fun a => a.1.2) := by
    intro a b hab
    simp only [lm, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab).symm]
  rw [ht.det_fintype]
  refine Finset.prod_congr rfl fun s _ => ?_
  let E : {r // P r s} ≃ {a : {rs : ι × ι // P rs.1 rs.2} // a.1.2 = s} :=
    { toFun := fun r => ⟨⟨(r.1, s), r.2⟩, rfl⟩
      invFun := fun a => ⟨a.1.1.1, by have h1 := a.1.2; have h2 : a.1.1.2 = s := a.2; rwa [h2] at h1⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨⟨r, s'⟩, h⟩, rfl⟩; rfl }
  rw [← Matrix.det_submatrix_equiv_self E]
  congr 1
  ext i j
  simp [toSquareBlock_def, toSquareBlockProp_def, lm, E]

/- English proof (translation)
Set `_ : LinearOrder ι` to `LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective`. Establish `ht : (rm P h).BlockTriangular (fun a => a.1.1)`. Introduce `a b hab`. Simplify using `only [rm, Matrix.of_apply]`. Rewrite using `[if_neg (ne_of_lt hab).symm]`.

Rewrite using `[ht.det_fintype]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Set `E : {r // P s r} ≃ {a : {rs : ι × ι // P rs.1 rs.2} // a.1.1 = s}` to `{ toFun := fun r => ⟨⟨(s, r.1), r.2⟩, rfl⟩ invFun := fun a => ⟨a.1.1.2, by have h1 := a.1.2; have h2 : a.1.1.1 = s := a.2; rwa [h2] at h1⟩ left_inv := fun _ => rfl right_inv := by rintro ⟨⟨⟨r, s'⟩, h⟩, rfl⟩; rfl }`. Rewrite using `[← Matrix.det_submatrix_equiv_self E, ← Matrix.det_transpose]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[toSquareBlock_def, toSquareBlockProp_def, rm, E]`.
-/
theorem det_rm (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}]
    [DecidableEq {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k) :
    (rm P h).det = ∏ r, (h.toSquareBlockProp fun s => P r s).det := by
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have ht : (rm P h).BlockTriangular (fun a => a.1.1) := by
    intro a b hab
    simp only [rm, Matrix.of_apply]
    rw [if_neg (ne_of_lt hab).symm]
  rw [ht.det_fintype]
  refine Finset.prod_congr rfl fun s _ => ?_
  let E : {r // P s r} ≃ {a : {rs : ι × ι // P rs.1 rs.2} // a.1.1 = s} :=
    { toFun := fun r => ⟨⟨(s, r.1), r.2⟩, rfl⟩
      invFun := fun a => ⟨a.1.1.2, by have h1 := a.1.2; have h2 : a.1.1.1 = s := a.2; rwa [h2] at h1⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨⟨r, s'⟩, h⟩, rfl⟩; rfl }
  rw [← Matrix.det_submatrix_equiv_self E, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [toSquareBlock_def, toSquareBlockProp_def, rm, E]

/- English proof (translation)
Establish `ht : M.BlockTriangular b`. Introduce `r s h`. Rewrite using `[hM r s h.le, Matrix.one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ h`.

Rewrite using `[ht.det]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Establish `: M.toSquareBlock b a = 1`. Use extensionality with `⟨r, hr⟩ ⟨s, hs⟩`. Simplify using `[toSquareBlock_def, hM r s (by omega), Matrix.one_apply]`.

Rewrite using `[this, det_one]`.
-/
theorem det_unitri (b : ι → ℕ) (M : Matrix ι ι k)
    (hM : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have ht : M.BlockTriangular b := by
    intro r s h
    rw [hM r s h.le, Matrix.one_apply_ne]
    rintro rfl; exact lt_irrefl _ h
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp [toSquareBlock_def, hM r s (by omega), Matrix.one_apply]
  rw [this, det_one]

/- English proof (translation)
Use `det_unitri (fun r => b r.1) _ fun r s h => ?_` and prove the remaining obligations. Simplify using `[toSquareBlockProp_def, hM _ _ h, Matrix.one_apply, Subtype.ext_iff]`.
-/
theorem det_block_unitri (b : ι → ℕ) (M : Matrix ι ι k)
    (hM : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) (Q : ι → Prop) [DecidablePred Q] :
    (M.toSquareBlockProp Q).det = 1 := by
  refine det_unitri (fun r => b r.1) _ fun r s h => ?_
  simp [toSquareBlockProp_def, hM _ _ h, Matrix.one_apply, Subtype.ext_iff]

/- English proof (translation)
Establish `key : ∀ (Q : n ⊕ t → Prop) [DecidablePred Q], (∀ a, ¬ Q (Sum.inl a)) → ((fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q).det = 1`. Introduce `Q _ hQ`. Establish `: (fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q = 1`. Use extensionality with `⟨r | r, hr⟩ ⟨s | s, hs⟩`. Conclude with `absurd hr (hQ _)`.

Conclude with `absurd hr (hQ _)`. Conclude with `absurd hs (hQ _)`. Simplify using `[toSquareBlockProp_def, Matrix.one_apply]`. Rewrite using `[this, det_one]`. Use `split_ifs with hq`.

Use `Matrix.twoBlockTriangular_det (fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k) Q (by` as an intermediate fact. Introduce and unpack `(r | r) hr (s | s) hs`. Conclude with `absurd ((hQ r).2 hq) hr`. Conclude with `absurd ((hQ r).2 hq) hr`. Simplify using the standard rewrite rules.

Establish `: r ≠ s` using `by rintro rfl; exact hr hs`. Simplify using `[this])`. Rewrite `this` using `[key (fun i => ¬ Q i) (fun a ha => ha ((hQ a).2 hq)), mul_one]`. Rewrite using `[← this]`. Simplify using the standard rewrite rules.

Conclude with `key Q fun a ha => hq ((hQ a).1 ha)`.
-/
theorem det_block_fromBlocks {n t : Type} [Fintype n] [DecidableEq n] [Fintype t] [DecidableEq t]
    (x : Matrix n n k) (Q : n ⊕ t → Prop) [DecidablePred Q] (q : Prop) [Decidable q]
    (hQ : ∀ a, Q (Sum.inl a) ↔ q) :
    ((fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q).det = if q then x.det else 1 := by
  have key : ∀ (Q : n ⊕ t → Prop) [DecidablePred Q], (∀ a, ¬ Q (Sum.inl a)) →
      ((fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q).det = 1 := by
    intro Q _ hQ
    have : (fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q = 1 := by
      ext ⟨r | r, hr⟩ ⟨s | s, hs⟩
      · exact absurd hr (hQ _)
      · exact absurd hr (hQ _)
      · exact absurd hs (hQ _)
      · simp [toSquareBlockProp_def, Matrix.one_apply]
    rw [this, det_one]
  split_ifs with hq
  · have := Matrix.twoBlockTriangular_det (fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k) Q (by
      rintro (r | r) hr (s | s) hs
      · exact absurd ((hQ r).2 hq) hr
      · exact absurd ((hQ r).2 hq) hr
      · simp
      · have : r ≠ s := by rintro rfl; exact hr hs
        simp [this])
    rw [key (fun i => ¬ Q i) (fun a ha => ha ((hQ a).2 hq)), mul_one] at this
    rw [← this]; simp
  · exact key Q fun a ha => hq ((hQ a).1 ha)

end Alg

section Grp
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

abbrev Up (n : Type) (c p : ℕ) : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s => lev p r < lev p s

abbrev Ix (n : Type) (c p : ℕ) : Type := {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}

def co (p : ℕ) (g : N k n c p) : Ix n c p → k := fun rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2

/- English proof (translation)
Use extensionality with `r s`. Express the relevant statement in the definitionally equal form `mkN p e r s = _`. Distinguish the cases in `h : lev p r < lev p s`. Establish `: r ≠ s` using `by rintro rfl; exact lt_irrefl _ h`. Simplify using `[mkN, ext0, h, this]`.

Simplify using `[mkN, ext0, h]`.
-/
theorem val_mkNel (p : ℕ) (e : Ix n c p → k) :
    ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k).val = 1 + ext0 (Up n c p) e := by
  ext r s
  change mkN p e r s = _
  by_cases h : lev p r < lev p s
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [mkN, ext0, h, this]
  · simp [mkN, ext0, h]

/- English proof (translation)
Use function extensionality and compare the values at `rs`. Express the relevant statement in the definitionally equal form `mkN p e _ _ = _`. Simplify using `[mkN, rs.2]`.
-/
theorem co_mkNel (p : ℕ) (e : Ix n c p → k) : co p (mkNel p e) = e := by
  funext rs
  change mkN p e _ _ = _
  simp [mkN, rs.2]

/- English proof (translation)
Use extensionality with `r s`. Express the relevant statement in the definitionally equal form `mkN p (co p g) r s = _`. Distinguish the cases in `h : lev p r < lev p s`. Simplify using `[mkN, h, co]`. Simplify using `only [mkN, Matrix.of_apply, dif_neg h]`.

Conclude with `(mem_N_iff.1 g.2 r s (not_lt.1 h)).symm`.
-/
theorem mkNel_co (p : ℕ) (g : N k n c p) : mkNel p (co p g) = g := by
  ext r s
  change mkN p (co p g) r s = _
  by_cases h : lev p r < lev p s
  · simp [mkN, h, co]
  · simp only [mkN, Matrix.of_apply, dif_neg h]
    exact (mem_N_iff.1 g.2 r s (not_lt.1 h)).symm

/- English proof (translation)
Rewrite using `[← mkNel_co p (g * mkNel p e)]`. Use `congr 1`. Use function extensionality and compare the values at `rs`. Rewrite using `[Pi.add_apply, ← mul_matrixExtendSelectedEntriesByZero_apply]`. Simplify using `only [co, Subgroup.coe_mul, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]`.

Rewrite using `[add_comm]`.
-/
theorem mul_mkNel (p : ℕ) (g : N k n c p) (e : Ix n c p → k) :
    g * mkNel p e = mkNel p ((lm (Up n c p) (g : GL (n ⊕ Fin c) k).val).mulVec e + co p g) := by
  rw [← mkNel_co p (g * mkNel p e)]
  congr 1
  funext rs
  rw [Pi.add_apply, ← mul_matrixExtendSelectedEntriesByZero_apply]
  simp only [co, Subgroup.coe_mul, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  rw [add_comm]

/- English proof (translation)
Rewrite using `[← mkNel_co p (mkNel p e * g)]`. Use `congr 1`. Use function extensionality and compare the values at `rs`. Rewrite using `[Pi.add_apply, ← matrixExtendByZero_mul]`. Simplify using `only [co, Subgroup.coe_mul, Units.val_mul, val_mkNel, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]`.

Rewrite using `[add_comm]`.
-/
theorem mkNel_mul (p : ℕ) (g : N k n c p) (e : Ix n c p → k) :
    mkNel p e * g = mkNel p ((rm (Up n c p) (g : GL (n ⊕ Fin c) k).val).mulVec e + co p g) := by
  rw [← mkNel_co p (mkNel p e * g)]
  congr 1
  funext rs
  rw [Pi.add_apply, ← matrixExtendByZero_mul]
  simp only [co, Subgroup.coe_mul, Units.val_mul, val_mkNel, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  rw [add_comm]

/- English proof (translation)
Rewrite using `[det_lm]`. Conclude with `Finset.prod_eq_one fun s _ => det_block_unitri (lev p) _ (mem_N_iff.1 g.2) _`.
-/
theorem det_lm_N (p : ℕ) (g : N k n c p) : (lm (Up n c p) (g : GL (n ⊕ Fin c) k).val).det = 1 := by
  rw [det_lm]
  exact Finset.prod_eq_one fun s _ => det_block_unitri (lev p) _ (mem_N_iff.1 g.2) _

/- English proof (translation)
Rewrite using `[det_rm]`. Conclude with `Finset.prod_eq_one fun s _ => det_block_unitri (lev p) _ (mem_N_iff.1 g.2) _`.
-/
theorem det_rm_N (p : ℕ) (g : N k n c p) : (rm (Up n c p) (g : GL (n ⊕ Fin c) k).val).det = 1 := by
  rw [det_rm]
  exact Finset.prod_eq_one fun s _ => det_block_unitri (lev p) _ (mem_N_iff.1 g.2) _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_embX (x : GL n k) : (embX c x).val = fromBlocks x.val 0 0 1 := rfl

/- English proof (translation)
Use extensionality with `r s`. Distinguish the cases in `h : lev p r < lev p s`. Rewrite using `[mul_matrixExtendSelectedEntriesByZero_apply (Up n c p) _ e ⟨(r, s), h⟩]`. Simplify using `[ext0, h]`. Establish `h0 : ∀ t, lev p t = lev p r → ∀ e : Ix n c p → k, ext0 (Up n c p) e t s = 0`.

Introduce `t ht e`. Simplify using `only [ext0, Matrix.of_apply]`. Rewrite using `[dif_neg]`. Simplify `h` using `[ht]`. Rewrite using `[h0 r rfl, Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases r with r | r <;> rcases t with t | t`. Rewrite using `[h0 (Sum.inl t) rfl, mul_zero]`. Simplify using `[val_embX]`. Simplify using `[val_embX]`.

Distinguish the cases in `hrt : r = t`. Rewrite using `[h0 _ (by rw [hrt]), mul_zero]`. Simplify using `[val_embX, hrt]`.
-/
theorem rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks (p : ℕ) (x : GL n k) (e : Ix n c p → k) :
    (embX c x).val * ext0 (Up n c p) e = ext0 (Up n c p) ((lm (Up n c p) (embX c x).val).mulVec e) := by
  ext r s
  by_cases h : lev p r < lev p s
  · rw [mul_matrixExtendSelectedEntriesByZero_apply (Up n c p) _ e ⟨(r, s), h⟩]
    simp [ext0, h]
  · have h0 : ∀ t, lev p t = lev p r → ∀ e : Ix n c p → k, ext0 (Up n c p) e t s = 0 := by
      intro t ht e
      simp only [ext0, Matrix.of_apply]
      rw [dif_neg]
      simpa [ht] using h
    rw [h0 r rfl, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    rcases r with r | r <;> rcases t with t | t
    · rw [h0 (Sum.inl t) rfl, mul_zero]
    · simp [val_embX]
    · simp [val_embX]
    · by_cases hrt : r = t
      · rw [h0 _ (by rw [hrt]), mul_zero]
      · simp [val_embX, hrt]

/- English proof (translation)
Establish `hm : embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹ ∈ N k n c p`. Simplify using `using conj_mem (mkNel p e).2 x⁻¹`. Use `mkNel_co p ⟨_, hm⟩` as an intermediate fact. Use `(congrArg Subtype.val this).symm.trans ?_` and prove the remaining obligations. Use `congr 2`.

Use function extensionality and compare the values at `rs`. Rewrite using `[← Matrix.mulVec_mulVec, ← matrixExtendByZero_mul, ← rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks, map_inv]`. Establish `hne : rs.1.1 ≠ rs.1.2` using `fun h => by have := rs.2; rw [h] at this; exact lt_irrefl _ this`. Simplify using `only [co, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]`.
-/
theorem conj_mkNel (p : ℕ) (x : GL n k) (e : Ix n c p → k) :
    embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹ =
      (mkNel p ((rm (Up n c p) (embX c x⁻¹).val * lm (Up n c p) (embX c x).val).mulVec e) : N k n c p) := by
  have hm : embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹ ∈ N k n c p := by
    simpa using conj_mem (mkNel p e).2 x⁻¹
  have := mkNel_co p ⟨_, hm⟩
  refine (congrArg Subtype.val this).symm.trans ?_
  congr 2
  funext rs
  rw [← Matrix.mulVec_mulVec, ← matrixExtendByZero_mul, ← rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks, map_inv]
  have hne : rs.1.1 ≠ rs.1.2 := fun h => by have := rs.2; rw [h] at this; exact lt_irrefl _ this
  simp only [co, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv,
    Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]

/- English proof (translation)
Rewrite using `[det_lm, val_embX]`. Rewrite using `[Finset.prod_congr rfl fun s _ => det_block_fromBlocks x.val _ (p < lev p s) fun a => Iff.rfl]`. Rewrite using `[Fintype.prod_sum_type]`. Express the relevant statement in the definitionally equal form `(∏ _a : n, if p < p then x.val.det else 1) * (∏ i : Fin c, if p < i.val + 1 then x.val.det else 1) = _`. Simplify using `only [lt_irrefl, if_false, Finset.prod_const_one, one_mul]`.

Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => if p < i + 1 then x.val.det else 1), ← Finset.prod_filter, Finset.prod_const]`. Use `congr 1`. Establish `: (Finset.range c).filter (fun i => p < i + 1) = Finset.Ico p c`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Nat.card_Ico]`.
-/
theorem det_lm_embX {p : ℕ} (x : GL n k) :
    (lm (Up n c p) (embX c x).val).det = x.val.det ^ (c - p) := by
  rw [det_lm, val_embX]
  rw [Finset.prod_congr rfl fun s _ => det_block_fromBlocks x.val _ (p < lev p s) fun a => Iff.rfl]
  rw [Fintype.prod_sum_type]
  change (∏ _a : n, if p < p then x.val.det else 1) * (∏ i : Fin c, if p < i.val + 1 then x.val.det else 1) = _
  simp only [lt_irrefl, if_false, Finset.prod_const_one, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => if p < i + 1 then x.val.det else 1), ← Finset.prod_filter,
    Finset.prod_const]
  congr 1
  have : (Finset.range c).filter (fun i => p < i + 1) = Finset.Ico p c := by
    ext i; simp; omega
  rw [this, Nat.card_Ico]

/- English proof (translation)
Rewrite using `[det_rm, val_embX]`. Rewrite using `[Finset.prod_congr rfl fun s _ => det_block_fromBlocks x.val _ (lev p s < p) fun a => Iff.rfl]`. Rewrite using `[Fintype.prod_sum_type]`. Express the relevant statement in the definitionally equal form `(∏ _a : n, if p < p then x.val.det else 1) * (∏ i : Fin c, if i.val + 1 < p then x.val.det else 1) = _`. Simplify using `only [lt_irrefl, if_false, Finset.prod_const_one, one_mul]`.

Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => if i + 1 < p then x.val.det else 1), ← Finset.prod_filter, Finset.prod_const]`. Use `congr 1`. Establish `: (Finset.range c).filter (fun i => i + 1 < p) = Finset.range (p - 1)`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Finset.card_range]`.
-/
theorem det_rm_embX {p : ℕ} (hp : p ≤ c) (x : GL n k) :
    (rm (Up n c p) (embX c x).val).det = x.val.det ^ (p - 1) := by
  rw [det_rm, val_embX]
  rw [Finset.prod_congr rfl fun s _ => det_block_fromBlocks x.val _ (lev p s < p) fun a => Iff.rfl]
  rw [Fintype.prod_sum_type]
  change (∏ _a : n, if p < p then x.val.det else 1) * (∏ i : Fin c, if i.val + 1 < p then x.val.det else 1) = _
  simp only [lt_irrefl, if_false, Finset.prod_const_one, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => if i + 1 < p then x.val.det else 1), ← Finset.prod_filter,
    Finset.prod_const]
  congr 1
  have : (Finset.range c).filter (fun i => i + 1 < p) = Finset.range (p - 1) := by
    ext i; simp; omega
  rw [this, Finset.card_range]

def InR (p : ℕ) (g : GL (n ⊕ Fin c) k) : Prop :=
  ∀ r s, lev p s ≤ lev p r → (r.isRight ∨ s.isRight) → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s

/- English proof (translation)
Set `S : Subgroup (GL (n ⊕ Fin c) k)` to `{ carrier := {g | ∃ x : GL n k, ∃ u ∈ N k n c p, g = embX c x * u} one_mem' := ⟨1, 1, one_mem _, by simp⟩ mul_mem' := by`. Introduce and unpack `_ _ ⟨x, u, hu, rfl⟩ ⟨y, v, hv, rfl⟩`. Conclude with `⟨x * y, _, mul_mem (conj_mem hu y) hv, by simp [mul_assoc]⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `_ ⟨x, u, hu, rfl⟩`.

Conclude with `⟨x⁻¹, _, conj_mem (inv_mem hu) x⁻¹, by simp [mul_assoc]⟩ }`. Establish `: R k n c p ≤ S` using `sup_le (by rintro _ ⟨x, rfl⟩; exact ⟨x, 1, one_mem _, by simp⟩) fun u hu => ⟨1, u, hu, by simp⟩`. Conclude with `this hg`.
-/
theorem exists_of_mem_R {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) :
    ∃ x : GL n k, ∃ u ∈ N k n c p, g = embX c x * u := by
  let S : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {g | ∃ x : GL n k, ∃ u ∈ N k n c p, g = embX c x * u}
      one_mem' := ⟨1, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, u, hu, rfl⟩ ⟨y, v, hv, rfl⟩
        exact ⟨x * y, _, mul_mem (conj_mem hu y) hv, by simp [mul_assoc]⟩
      inv_mem' := by
        rintro _ ⟨x, u, hu, rfl⟩
        exact ⟨x⁻¹, _, conj_mem (inv_mem hu) x⁻¹, by simp [mul_assoc]⟩ }
  have : R k n c p ≤ S := sup_le (by rintro _ ⟨x, rfl⟩; exact ⟨x, 1, one_mem _, by simp⟩)
    fun u hu => ⟨1, u, hu, by simp⟩
  exact this hg

/- English proof (translation)
Take `⟨x, u, hu, rfl⟩` from `exists_of_mem_R hg`. Rewrite `hu` using `[mem_N_iff]`. Introduce and unpack `(r | r) (s | s) h h'`. Simplify using `at h'`. Establish `: ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0` using `fun t => by`.

Simplify using `using hu (Sum.inl t) (Sum.inr s) h`. Simplify using `[val_embX, Matrix.mul_apply, this]`. Rewrite using `[← hu _ _ h]`. Simplify using `[val_embX, Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← hu _ _ h]`.

Simplify using `[val_embX, Matrix.mul_apply, Matrix.one_apply]`.
-/
theorem inR_of_mem {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) : InR p g := by
  obtain ⟨x, u, hu, rfl⟩ := exists_of_mem_R hg
  rw [mem_N_iff] at hu
  rintro (r | r) (s | s) h h'
  · simp at h'
  · have : ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
      simpa using hu (Sum.inl t) (Sum.inr s) h
    simp [val_embX, Matrix.mul_apply, this]
  · rw [← hu _ _ h]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
  · rw [← hu _ _ h]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]

/- English proof (translation)
Use `⟨fun h => ⟨inR_of_mem h, inR_of_mem (inv_mem h)⟩, fun ⟨h1, h2⟩ => ?_⟩` and prove the remaining obligations. Establish `e : (g⁻¹).val.toBlocks₁₁ * g.val.toBlocks₁₁ = 1`. Use extensionality with `a b`. Establish `h3` using `congrFun (congrFun g.inv_mul (Sum.inl a)) (Sum.inl b)`. Rewrite `h3` using `[Matrix.mul_apply, Fintype.sum_sum_type]`.

Establish `h4 : ∑ i : Fin c, (g⁻¹).val (Sum.inl a) (Sum.inr i) * g.val (Sum.inr i) (Sum.inl b) = 0`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Break down `le_total (i.val + 1) p with hi | hi` into its components or cases. Rewrite using `[h2 (Sum.inl a) (Sum.inr i) hi (by simp)]; simp`. Rewrite using `[h1 (Sum.inr i) (Sum.inl b) hi (by simp)]; simp`.

Rewrite `h3` using `[h4, add_zero]`. Rewrite using `[Matrix.mul_apply]`. Simplify `h3` using `[Matrix.one_apply, toBlocks₁₁]`. Set `y : GL n k` to `⟨_, _, e, mul_eq_one_comm.1 e⟩`. Establish `hy : embX c y * g ∈ N k n c p`.

Rewrite using `[mem_N_iff]`. Introduce and unpack `(r | r) (s | s) h`. Use `congrFun (congrFun e r) s` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Simplify `this` using `[val_embX, Matrix.mul_apply, y, Matrix.one_apply, toBlocks₁₁]`.

Establish `: ∀ t, g.val (Sum.inl t) (Sum.inr s) = 0` using `fun t => by`. Simplify using `using h1 (Sum.inl t) (Sum.inr s) h (by simp)`. Simplify using `[val_embX, Matrix.mul_apply, this]`. Rewrite using `[← h1 _ _ h (by simp)]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← h1 _ _ h (by simp)]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]`.

Establish `: g = embX c y⁻¹ * (embX c y * g)` using `by simp`. Rewrite using `[this]`. Conclude with `mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right hy)`.
-/
theorem mem_R_iff {p : ℕ} {g : GL (n ⊕ Fin c) k} : g ∈ R k n c p ↔ InR p g ∧ InR p g⁻¹ := by
  refine ⟨fun h => ⟨inR_of_mem h, inR_of_mem (inv_mem h)⟩, fun ⟨h1, h2⟩ => ?_⟩
  have e : (g⁻¹).val.toBlocks₁₁ * g.val.toBlocks₁₁ = 1 := by
    ext a b
    have h3 := congrFun (congrFun g.inv_mul (Sum.inl a)) (Sum.inl b)
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h3
    have h4 : ∑ i : Fin c, (g⁻¹).val (Sum.inl a) (Sum.inr i) * g.val (Sum.inr i) (Sum.inl b) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases le_total (i.val + 1) p with hi | hi
      · rw [h2 (Sum.inl a) (Sum.inr i) hi (by simp)]; simp
      · rw [h1 (Sum.inr i) (Sum.inl b) hi (by simp)]; simp
    rw [h4, add_zero] at h3
    rw [Matrix.mul_apply]
    simpa [Matrix.one_apply, toBlocks₁₁] using h3
  let y : GL n k := ⟨_, _, e, mul_eq_one_comm.1 e⟩
  have hy : embX c y * g ∈ N k n c p := by
    rw [mem_N_iff]
    rintro (r | r) (s | s) h
    · have := congrFun (congrFun e r) s
      rw [Matrix.mul_apply] at this
      simpa [val_embX, Matrix.mul_apply, y, Matrix.one_apply, toBlocks₁₁] using this
    · have : ∀ t, g.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
        simpa using h1 (Sum.inl t) (Sum.inr s) h (by simp)
      simp [val_embX, Matrix.mul_apply, this]
    · rw [← h1 _ _ h (by simp)]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
    · rw [← h1 _ _ h (by simp)]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
  have : g = embX c y⁻¹ * (embX c y * g) := by simp
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right hy)

end Grp

section Meas
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

/- English proof (translation)
Use `Units.continuous_val (M := Matrix n n k)` as an intermediate fact. Use `fun_prop`.
-/
theorem continuous_entry (r s : n) : Continuous fun g : GL n k => g.val r s := by
  have := Units.continuous_val (M := Matrix n n k)
  fun_prop

/- English proof (translation)
Use `(SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2` as an intermediate fact. Establish `e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = {g | InN p g}` using `Set.ext fun g => mem_N_iff`. Rewrite using `[e]`. Simplify using `only [InN, Set.ofPred_forall]`. Apply the tactic sequence `exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_eq (continuous_entry r s) continuous_const`.
-/
theorem isClosed_N (p : ℕ) : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  have := (SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = {g | InN p g} := Set.ext fun g => mem_N_iff
  rw [e]
  simp only [InN, Set.ofPred_forall]
  exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq (continuous_entry r s) continuous_const

/- English proof (translation)
Use `(SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2` as an intermediate fact. Establish `h : IsClosed {g : GL (n ⊕ Fin c) k | InR p g}`. Simplify using `only [InR, Set.ofPred_forall]`. Apply the tactic sequence `exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (continuous_entry r s) continuous_const`. Establish `e : (R k n c p : Set (GL (n ⊕ Fin c) k)) = {g | InR p g} ∩ (fun g => g⁻¹) ⁻¹' {g | InR p g}` using `Set.ext fun g => mem_R_iff`.

Rewrite using `[e]`. Conclude with `h.inter (h.preimage continuous_inv)`.
-/
theorem isClosed_R (p : ℕ) : IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) := by
  have := (SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have h : IsClosed {g : GL (n ⊕ Fin c) k | InR p g} := by
    simp only [InR, Set.ofPred_forall]
    exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_entry r s) continuous_const
  have e : (R k n c p : Set (GL (n ⊕ Fin c) k)) = {g | InR p g} ∩ (fun g => g⁻¹) ⁻¹' {g | InR p g} :=
    Set.ext fun g => mem_R_iff
  rw [e]
  exact h.inter (h.preimage continuous_inv)

/- English proof (translation)
The claim follows from `continuous_pi fun rs => (continuous_entry rs.1.1 rs.1.2).comp continuous_subtype_val`.
-/
theorem continuous_co (p : ℕ) : Continuous (co (k := k) (n := n) (c := c) p) :=
  continuous_pi fun rs => (continuous_entry rs.1.1 rs.1.2).comp continuous_subtype_val

/- English proof (translation)
Establish `h1 : Continuous (mkN (k` using `k) (n := n) (c := c) p) := by`. Use `continuous_pi fun r => continuous_pi fun s => ?_` and prove the remaining obligations. Distinguish the cases in `h : lev p r < lev p s`. Simplify using `only [mkN, Matrix.of_apply, dif_pos h]`. Conclude with `continuous_apply _`.

Simplify using `only [mkN, Matrix.of_apply, dif_neg h]`. Conclude with `continuous_const`. Use `continuous_induced_rng.2 (Units.continuous_iff.2 ⟨h1.congr fun _ => rfl, ?_⟩)` and prove the remaining obligations. Use `h1.matrix_adjugate.congr fun e => ?_` and prove the remaining obligations. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def]`.

Express the relevant statement in the definitionally equal form `_ = Ring.inverse (mkN p e).det • (mkN p e).adjugate`. Rewrite using `[det_mkN]`. Simplify using the standard rewrite rules.
-/
theorem continuous_mkNel (p : ℕ) : Continuous (mkNel (k := k) (n := n) (c := c) p) := by
  have h1 : Continuous (mkN (k := k) (n := n) (c := c) p) := by
    refine continuous_pi fun r => continuous_pi fun s => ?_
    by_cases h : lev p r < lev p s
    · simp only [mkN, Matrix.of_apply, dif_pos h]; exact continuous_apply _
    · simp only [mkN, Matrix.of_apply, dif_neg h]; exact continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨h1.congr fun _ => rfl, ?_⟩)
  refine h1.matrix_adjugate.congr fun e => ?_
  rw [Matrix.coe_units_inv, Matrix.inv_def]
  change _ = Ring.inverse (mkN p e).det • (mkN p e).adjugate
  rw [det_mkN]; simp

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

/- English proof (translation)
Take `⟨_, _⟩` from `SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Set `g : GL a k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero L (hL ▸ one_ne_zero)`. Establish `hg : Matrix.GeneralLinearGroup.det g = 1` using `Units.ext hL`. Establish `hc : ∀ M : Matrix a a k, Continuous fun e => M.mulVec e` using `fun M => continuous_const.matrix_mulVec continuous_id`. Set `T : (a → k) ≃ₜ (a → k)` to `{ toFun := fun e => g.val.mulVec e invFun := fun e => (g⁻¹).val.mulVec e left_inv := fun e => by simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] right_inv := fun e => by simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] continuous_toFun := hc _ …`.

Establish `h1 : (Measure.pi fun _ : a => ν).map T = Measure.pi fun _ : a => ν`. Use `Measure.Regular.map (μ := Measure.pi fun _ : a => ν) T` as an intermediate fact. Use `Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_` and prove the remaining obligations. Establish `h2` using `integral_comp_mulVec_eq_smul ν g fun x => (f x : ℂ)`. Rewrite `h2` using `[hg, integral_complex_ofReal, integral_complex_ofReal]`.

Establish `h3` using `integral_map_equiv (μ := Measure.pi fun _ : a => ν) T.toMeasurableEquiv f`. Rewrite `h3` using `[Homeomorph.toMeasurableEquiv_coe]`. Rewrite using `[h3]`. Express the relevant statement in the definitionally equal form `∫ x, f (g.val.mulVec x) ∂_ = _`. Simplify `h2` using `[nabs]`.

Use `⟨((hc L).add continuous_const).measurable, ?_⟩` and prove the remaining obligations. Establish `: (fun e => L.mulVec e + b) = (fun e => e + b) ∘ T` using `rfl`. Rewrite using `[this, ← Measure.map_map (measurable_add_const b) T.continuous.measurable, h1, map_add_right_eq_self]`.
-/
theorem map_affine {a : Type} [Fintype a] [DecidableEq a] (L : Matrix a a k) (hL : L.det = 1) (b : a → k) :
    Measurable (fun e => L.mulVec e + b) ∧
      (Measure.pi fun _ : a => ν).map (fun e => L.mulVec e + b) = Measure.pi fun _ : a => ν := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let g : GL a k := Matrix.GeneralLinearGroup.mkOfDetNeZero L (hL ▸ one_ne_zero)
  have hg : Matrix.GeneralLinearGroup.det g = 1 := Units.ext hL
  have hc : ∀ M : Matrix a a k, Continuous fun e => M.mulVec e := fun M =>
    continuous_const.matrix_mulVec continuous_id
  let T : (a → k) ≃ₜ (a → k) :=
    { toFun := fun e => g.val.mulVec e
      invFun := fun e => (g⁻¹).val.mulVec e
      left_inv := fun e => by simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      right_inv := fun e => by simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have h1 : (Measure.pi fun _ : a => ν).map T = Measure.pi fun _ : a => ν := by
    have := Measure.Regular.map (μ := Measure.pi fun _ : a => ν) T
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
    have h2 := integral_comp_mulVec_eq_smul ν g fun x => (f x : ℂ)
    rw [hg, integral_complex_ofReal, integral_complex_ofReal] at h2
    have h3 := integral_map_equiv (μ := Measure.pi fun _ : a => ν) T.toMeasurableEquiv f
    rw [Homeomorph.toMeasurableEquiv_coe] at h3
    rw [h3]
    change ∫ x, f (g.val.mulVec x) ∂_ = _
    simpa [nabs] using h2
  refine ⟨((hc L).add continuous_const).measurable, ?_⟩
  have : (fun e => L.mulVec e + b) = (fun e => e + b) ∘ T := rfl
  rw [this, ← Measure.map_map (measurable_add_const b) T.continuous.measurable, h1, map_add_right_eq_self]

def coEquiv (p : ℕ) : (Ix n c p → k) ≃ᵐ N k n c p where
  toFun := mkNel p
  invFun := co p
  left_inv := co_mkNel p
  right_inv := mkNel_co p
  measurable_toFun := by
    have h := (coord_embedding (k := k) (n := n) (c := c) p).1
    refine (h.measurable_comp_iff).1 ?_
    have : (co (k := k) (n := n) (c := c) p) ∘ mkNel p = id := funext (co_mkNel p)
    exact this ▸ measurable_id
  measurable_invFun := (coord_embedding (k := k) (n := n) (c := c) p).1.measurable

/- English proof (translation)
Rewrite using `[← MeasurableEquiv.comap_symm]`. Unfold `volN`. Use `congr!`.
-/
theorem volN_eq (p : ℕ) : volN ν n c p = (Measure.pi fun _ : Ix n c p => ν).map (coEquiv p) := by
  rw [← MeasurableEquiv.comap_symm]
  unfold volN
  congr!

/- English proof (translation)
Take `⟨h1, h2⟩` from `map_affine ν L hL b`. Establish `e1 : T ∘ coEquiv p = coEquiv p ∘ fun e => L.mulVec e + b` using `funext hT`. Establish `e2 : T = coEquiv p ∘ (fun e => L.mulVec e + b) ∘ (coEquiv p).symm`. Rewrite using `[← Function.comp_assoc, ← e1]`. Use `ext1 g`.

Simplify using the standard rewrite rules. Establish `hm : Measurable T` using `e2 ▸ (coEquiv p).measurable.comp (h1.comp (coEquiv p).symm.measurable)`. Rewrite using `[volN_eq, Measure.map_map hm (coEquiv p).measurable, e1, ← Measure.map_map (coEquiv p).measurable h1, h2]`.
-/
theorem map_volN_of_affine (p : ℕ) (T : N k n c p → N k n c p) (L : Matrix (Ix n c p) (Ix n c p) k)
    (hL : L.det = 1) (b : Ix n c p → k) (hT : ∀ e, T (mkNel p e) = mkNel p (L.mulVec e + b)) :
    (volN ν n c p).map T = volN ν n c p := by
  obtain ⟨h1, h2⟩ := map_affine ν L hL b
  have e1 : T ∘ coEquiv p = coEquiv p ∘ fun e => L.mulVec e + b := funext hT
  have e2 : T = coEquiv p ∘ (fun e => L.mulVec e + b) ∘ (coEquiv p).symm := by
    rw [← Function.comp_assoc, ← e1]; ext1 g; simp
  have hm : Measurable T := e2 ▸ (coEquiv p).measurable.comp (h1.comp (coEquiv p).symm.measurable)
  rw [volN_eq, Measure.map_map hm (coEquiv p).measurable, e1, ← Measure.map_map (coEquiv p).measurable h1, h2]

/- English proof (translation)
Take `⟨_, _⟩` from `SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Use `{ lt_top_of_isCompact := fun K hK => ?_, map_mul_left_eq_self := fun g => ?_, open_pos := fun U hU hne => ?_ }` and prove the remaining obligations. Rewrite using `[volN_eq, MeasurableEquiv.map_apply, ← MeasurableEquiv.image_symm]`. Conclude with `(hK.image (continuous_co p)).measure_lt_top`. Conclude with `map_volN_of_affine ν p _ _ (det_lm_N p g) _ (mul_mkNel p g)`.

Rewrite using `[volN_eq, MeasurableEquiv.map_apply]`. Take `⟨g, hg⟩` from `hne`. Conclude with `(hU.preimage (continuous_mkNel p)).measure_ne_zero _ ⟨co p g, by simpa [mkNel_co] using hg⟩`.
-/
theorem isHaarMeasure_volN (p : ℕ) : (volN ν n c p).IsHaarMeasure := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine { lt_top_of_isCompact := fun K hK => ?_, map_mul_left_eq_self := fun g => ?_, open_pos := fun U hU hne => ?_ }
  · rw [volN_eq, MeasurableEquiv.map_apply, ← MeasurableEquiv.image_symm]
    exact (hK.image (continuous_co p)).measure_lt_top
  · exact map_volN_of_affine ν p _ _ (det_lm_N p g) _ (mul_mkNel p g)
  · rw [volN_eq, MeasurableEquiv.map_apply]
    obtain ⟨g, hg⟩ := hne
    exact (hU.preimage (continuous_mkNel p)).measure_ne_zero _ ⟨co p g, by simpa [mkNel_co] using hg⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun g => map_volN_of_affine ν p _ _ (det_rm_N p g) _ (mkNel_mul p g)⟩`.
-/
theorem isMulRightInvariant_volN (p : ℕ) : (volN ν n c p).IsMulRightInvariant :=
  ⟨fun g => map_volN_of_affine ν p _ _ (det_rm_N p g) _ (mkNel_mul p g)⟩

/- English proof (translation)
Set `d : kˣ` to `Matrix.GeneralLinearGroup.det x`. Set `u : kˣ` to `d⁻¹ ^ (p - 1) * d ^ (c - p)`. Establish `hu : (rm (Up n c p) (embX c x⁻¹).val * lm (Up n c p) (embX c x).val).det = (u : k)`. Rewrite using `[det_mul, det_lm_embX, det_rm_embX hp]`. Simplify using `[u, d]`.

Set `G : GL (Ix n c p) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hu ▸ u.ne_zero)`. Establish `hG : Matrix.GeneralLinearGroup.det G = u` using `Units.ext hu`. Establish `key` using `integral_comp_mulVec_eq_smul ν G (fun e => f (mkNel p e : N k n c p))`. Rewrite using `[volN_eq, integral_map_equiv, integral_map_equiv]`. Express the relevant statement in the definitionally equal form `∫ e, f (embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂_ = _`.

Repeatedly rewrite using `[conj_mkNel]`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[hG]`. Use `congr 1`. Establish `hd` using `nabs_pos' d`.

Establish `: nabs k u = (nabs k d)⁻¹ ^ (p - 1) * nabs k d ^ (c - p)` using `by simp [u, nabs]`. Rewrite using `[this, mul_inv, inv_pow, inv_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hd.le, ← Real.rpow_add hd, Nat.cast_sub h1, Nat.cast_sub hp]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_conj_volN {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) =
      (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) •
        ∫ u : N k n c p, f u ∂(volN ν n c p) := by
  let d : kˣ := Matrix.GeneralLinearGroup.det x
  let u : kˣ := d⁻¹ ^ (p - 1) * d ^ (c - p)
  have hu : (rm (Up n c p) (embX c x⁻¹).val * lm (Up n c p) (embX c x).val).det = (u : k) := by
    rw [det_mul, det_lm_embX, det_rm_embX hp]; simp [u, d]
  let G : GL (Ix n c p) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hu ▸ u.ne_zero)
  have hG : Matrix.GeneralLinearGroup.det G = u := Units.ext hu
  have key := integral_comp_mulVec_eq_smul ν G (fun e => f (mkNel p e : N k n c p))
  rw [volN_eq, integral_map_equiv, integral_map_equiv]
  change ∫ e, f (embX c x * ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂_ = _
  simp_rw [conj_mkNel]
  refine key.trans ?_
  rw [hG]
  congr 1
  have hd := nabs_pos' d
  have : nabs k u = (nabs k d)⁻¹ ^ (p - 1) * nabs k d ^ (c - p) := by simp [u, nabs]
  rw [this, mul_inv, inv_pow, inv_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hd.le,
    ← Real.rpow_add hd, Nat.cast_sub h1, Nat.cast_sub hp]
  congr 1
  push_cast; ring

end Meas

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ p h1 hp ν _` and use `⟨isClosed_N p, isClosed_R p, isHaarMeasure_volN ν p, isMulRightInvariant_volN ν p, integral_conj_volN ν h1 hp⟩`.
-/
theorem volN_haar_and_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure], IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) ∧ IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) ∧ (volN ν n c p).IsHaarMeasure ∧ (volN ν n c p).IsMulRightInvariant ∧ ∀ (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) = (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) • ∫ u : N k n c p, f u ∂(volN ν n c p) :=
  fun _ _ _ _ _ _ _ _ _ _ _ p h1 hp ν _ =>
    ⟨isClosed_N p, isClosed_R p, isHaarMeasure_volN ν p, isMulRightInvariant_volN ν p,
      integral_conj_volN ν h1 hp⟩

end GlobalTheory.RootEx.VolN
