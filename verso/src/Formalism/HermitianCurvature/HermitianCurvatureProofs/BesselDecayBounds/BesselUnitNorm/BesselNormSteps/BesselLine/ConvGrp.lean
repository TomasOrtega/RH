import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SfiniteMuN

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Grp

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Apply the tactic sequence `rw [Matrix.mul_apply, Finset.sum_eq_single (⟨if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))]`. Apply the tactic sequence `simp only [Hpk, Matrix.one_apply, Fin.ext_iff, Fin.val_mk] split_ifs <;> first | (exfalso; omega) | norm_num`.

Introduce `l _ hl`. Establish `hl' : (l : ℕ) ≠ if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i` using `fun h => hl (Fin.ext h)`. Establish `hl2` using `l.isLt`. Simplify using `only [Hpk, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs at hl' ⊢ <;> first | (exfalso; omega) | norm_num`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single
    (⟨if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i, by split_ifs <;> omega⟩ :
      Fin (2 * r + k + 1))]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · intro l _ hl
    have hl' : (l : ℕ) ≠ if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i :=
      fun h => hl (Fin.ext h)
    have hl2 := l.isLt
    simp only [Hpk, Fin.ext_iff, Fin.val_mk]
    split_ifs at hl' ⊢ <;> first | (exfalso; omega) | norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hb' : bᴴ * Hpk k r * b = Hpk k r` using `hb`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uh_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hl : (Hpk k r * aᴴ * Hpk k r) * a = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv : a⁻¹ = Hpk k r * aᴴ * Hpk k r` using `Matrix.inv_eq_left_inv hl`. Establish `h1 : a⁻¹ * a = 1` using `by rw [hinv]; exact hl`.

Establish `h2 : a * a⁻¹ = 1` using `Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse hl)`. Use `⟨h2, h1, ?_⟩` and prove the remaining obligations. Use `show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uh_inv {a : Mx k r} (ha : a ∈ UH (Hpk k r)) :
    a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hl : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc Hpk k r * aᴴ * Hpk k r * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', hpk_sq]
  have hinv : a⁻¹ = Hpk k r * aᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have h1 : a⁻¹ * a = 1 := by rw [hinv]; exact hl
  have h2 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse hl)
  refine ⟨h2, h1, ?_⟩
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2]; simp

/- English proof (translation)
Unfold `bvec`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem col_eq (g : Mx k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by
  unfold bvec
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

def lowS (k r a : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) where
  carrier := {y | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0}
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eI_val (a : Fin r) : (eI k r a).val = a.val := rfl

/- English proof (translation)
Introduce `y hy`. Establish `hy' : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0` using `hy`. Use `show ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (n *ᵥ y) i = 0`. Introduce `i hi`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Distinguish the cases in `hl : a ≤ l.val`. Rewrite using `[hy' l hl, mul_zero]`. Establish `hlr : l.val < r` using `by omega`.

Establish `h1` using `hn ⟨l.val, hlr⟩ i (by show (l : ℕ) ≤ i; omega)`. Establish `heq : eI k r ⟨l.val, hlr⟩ = l` using `Fin.ext (eI_val _)`. Rewrite `h1` using `[heq]`. Rewrite using `[h1, if_neg (fun h => by subst h; omega), zero_mul]`.
-/
theorem maps_low {n : Mx k r} (hn : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      n i (eI k r a) = if i = eI k r a then 1 else 0) {a : ℕ} (har : a ≤ r) :
    ∀ y ∈ lowS k r a, n *ᵥ y ∈ lowS k r a := by
  intro y hy
  have hy' : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0 := hy
  show ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (n *ᵥ y) i = 0
  intro i hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : a ≤ l.val
  · rw [hy' l hl, mul_zero]
  · have hlr : l.val < r := by omega
    have h1 := hn ⟨l.val, hlr⟩ i (by show (l : ℕ) ≤ i; omega)
    have heq : eI k r ⟨l.val, hlr⟩ = l := Fin.ext (eI_val _)
    rw [heq] at h1
    rw [h1, if_neg (fun h => by subst h; omega), zero_mul]

/- English proof (translation)
Set `f : lowS k r a →ₗ[ℂ] lowS k r a` to `(Matrix.mulVecLin g).restrict (fun y hy => hmaps y hy)`. Establish `hinj : Function.Injective f`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : g *ᵥ (x : Fin (2 * r + k + 1) → ℂ) = g *ᵥ (y : Fin (2 * r + k + 1) → ℂ)` using `congrArg Subtype.val hxy`.

Establish `h2` using `congrArg (fun v => g⁻¹ *ᵥ v) h1`. Simplify using `only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2`. Conclude with `h2`. Establish `hsurj` using `LinearMap.injective_iff_surjective.mp hinj`. Introduce `y hy`.

Take `⟨x, hx⟩` from `hsurj ⟨y, hy⟩`. Conclude with `⟨x, x.2, congrArg Subtype.val hx⟩`.
-/
theorem onto_low {g : Mx k r} (hg : g⁻¹ * g = 1) {a : ℕ} (hmaps : ∀ y ∈ lowS k r a, g *ᵥ y ∈ lowS k r a) :
    ∀ y ∈ lowS k r a, ∃ x ∈ lowS k r a, g *ᵥ x = y := by
  let f : lowS k r a →ₗ[ℂ] lowS k r a := (Matrix.mulVecLin g).restrict (fun y hy => hmaps y hy)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h1 : g *ᵥ (x : Fin (2 * r + k + 1) → ℂ) = g *ᵥ (y : Fin (2 * r + k + 1) → ℂ) :=
      congrArg Subtype.val hxy
    have h2 := congrArg (fun v => g⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2
    exact h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

/- English proof (translation)
Take `⟨x', hx', he⟩` from `onto_low hg hmaps _ hx`. Establish `h3 : x' = x`. Establish `h2` using `congrArg (fun v => g⁻¹ *ᵥ v) he`. Simplify using `only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2`. Conclude with `h2`.

Rewrite using `[← h3]`. Conclude with `hx'`.
-/
private lemma mem_lowS_of_apply_mem_lowS {g : Mx k r} (hg : g⁻¹ * g = 1) {a : ℕ}
    (hmaps : ∀ y ∈ lowS k r a, g *ᵥ y ∈ lowS k r a) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : g *ᵥ x ∈ lowS k r a) : x ∈ lowS k r a := by
  obtain ⟨x', hx', he⟩ := onto_low hg hmaps _ hx
  have h3 : x' = x := by
    have h2 := congrArg (fun v => g⁻¹ *ᵥ v) he
    simp only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2
    exact h2
  rw [← h3]
  exact hx'

/- English proof (translation)
Unfold `Nset at hn ⊢`. Simplify using `only [Set.mem_setOf_eq] at hn ⊢`. Take `⟨hU, hcol, hmid⟩` from `hn`. Take `⟨h1, h2, hUi⟩` from `uh_inv hU`. Establish `key : ∀ a ≤ r, ∀ c, n *ᵥ bvec c - bvec c ∈ lowS k r a → n⁻¹ *ᵥ bvec c - bvec c ∈ lowS k r a`.

Introduce `a har c hc`. Apply `mem_lowS_of_apply_mem_lowS h2 (maps_low hcol har)` to reduce the goal to its premises. Establish `e : n *ᵥ (n⁻¹ *ᵥ bvec c - bvec c) = -(n *ᵥ bvec c - bvec c)`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `(lowS k r a).neg_mem hc`. Use `⟨hUi, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩` and prove the remaining obligations. Establish `h3 : ∀ i' : Fin (2 * r + k + 1), a.val ≤ i'.val → (n⁻¹ *ᵥ bvec (eI k r a) - bvec (eI k r a)) i' = 0`. Apply `key a.val a.isLt.le` to reduce the goal to its premises.

Use `show ∀ i' : Fin (2 * r + k + 1), a.val ≤ i'.val → (n *ᵥ bvec (eI k r a) - bvec (eI k r a)) i' = 0`. Introduce `i' hi'`. Establish `h5 : (n *ᵥ bvec (eI k r a)) i' = n i' (eI k r a)` using `by rw [col_eq]`. Rewrite using `[Pi.sub_apply, h5, hcol a i' hi']`. Unfold `bvec`.

Rewrite using `[Pi.single_apply, sub_self]`. Establish `h4` using `h3 i hi`. Establish `h5 : (n⁻¹ *ᵥ bvec (eI k r a)) i = n⁻¹ i (eI k r a)` using `by rw [col_eq]`. Rewrite `h4` using `[Pi.sub_apply, h5, sub_eq_zero]`. Rewrite using `[h4]`.

Unfold `bvec`. Rewrite using `[Pi.single_apply]`. Establish `h3 : ∀ i' : Fin (2 * r + k + 1), r ≤ i'.val → (n⁻¹ *ᵥ bvec j - bvec j) i' = 0`. Apply `key r le_rfl` to reduce the goal to its premises. Use `show ∀ i' : Fin (2 * r + k + 1), r ≤ i'.val → (n *ᵥ bvec j - bvec j) i' = 0`.

Introduce `i' hi'`. Establish `h5 : (n *ᵥ bvec j) i' = n i' j` using `by rw [col_eq]`. Rewrite using `[Pi.sub_apply, h5, hmid i' j hj1 hj2 hi']`. Unfold `bvec`. Rewrite using `[Pi.single_apply, sub_self]`.

Establish `h4` using `h3 i hi`. Establish `h5 : (n⁻¹ *ᵥ bvec j) i = n⁻¹ i j` using `by rw [col_eq]`. Rewrite `h4` using `[Pi.sub_apply, h5, sub_eq_zero]`. Rewrite using `[h4]`. Unfold `bvec`.

Rewrite using `[Pi.single_apply]`.
-/
theorem n_inv {n : Mx k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Nset k r := by
  unfold Nset at hn ⊢
  simp only [Set.mem_setOf_eq] at hn ⊢
  obtain ⟨hU, hcol, hmid⟩ := hn
  obtain ⟨h1, h2, hUi⟩ := uh_inv hU
  have key : ∀ a ≤ r, ∀ c, n *ᵥ bvec c - bvec c ∈ lowS k r a →
      n⁻¹ *ᵥ bvec c - bvec c ∈ lowS k r a := by
    intro a har c hc
    apply mem_lowS_of_apply_mem_lowS h2 (maps_low hcol har)
    have e : n *ᵥ (n⁻¹ *ᵥ bvec c - bvec c) = -(n *ᵥ bvec c - bvec c) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      abel
    rw [e]
    exact (lowS k r a).neg_mem hc
  refine ⟨hUi, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · have h3 : ∀ i' : Fin (2 * r + k + 1), a.val ≤ i'.val →
        (n⁻¹ *ᵥ bvec (eI k r a) - bvec (eI k r a)) i' = 0 := by
      apply key a.val a.isLt.le
      show ∀ i' : Fin (2 * r + k + 1), a.val ≤ i'.val →
        (n *ᵥ bvec (eI k r a) - bvec (eI k r a)) i' = 0
      intro i' hi'
      have h5 : (n *ᵥ bvec (eI k r a)) i' = n i' (eI k r a) := by rw [col_eq]
      rw [Pi.sub_apply, h5, hcol a i' hi']
      unfold bvec
      rw [Pi.single_apply, sub_self]
    have h4 := h3 i hi
    have h5 : (n⁻¹ *ᵥ bvec (eI k r a)) i = n⁻¹ i (eI k r a) := by rw [col_eq]
    rw [Pi.sub_apply, h5, sub_eq_zero] at h4
    rw [h4]
    unfold bvec
    rw [Pi.single_apply]
  · have h3 : ∀ i' : Fin (2 * r + k + 1), r ≤ i'.val →
        (n⁻¹ *ᵥ bvec j - bvec j) i' = 0 := by
      apply key r le_rfl
      show ∀ i' : Fin (2 * r + k + 1), r ≤ i'.val → (n *ᵥ bvec j - bvec j) i' = 0
      intro i' hi'
      have h5 : (n *ᵥ bvec j) i' = n i' j := by rw [col_eq]
      rw [Pi.sub_apply, h5, hmid i' j hj1 hj2 hi']
      unfold bvec
      rw [Pi.single_apply, sub_self]
    have h4 := h3 i hi
    have h5 : (n⁻¹ *ᵥ bvec j) i = n⁻¹ i j := by rw [col_eq]
    rw [Pi.sub_apply, h5, sub_eq_zero] at h4
    rw [h4]
    unfold bvec
    rw [Pi.single_apply]

/- English proof (translation)
Introduce `y hy`. Establish `hy' : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0` using `hy`. Establish `hdecomp : y = ∑ l, y l • bvec l`. Unfold `bvec`. Use extensionality with `i`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hsum` using `map_sum (Matrix.mulVecLin g) (fun l => y l • bvec l) Finset.univ`. Simplify using `only [Matrix.mulVecLin_apply] at hsum`. Use `conv_lhs => rw [hdecomp]`. Rewrite using `[hsum]`.

Use `conv_rhs => rw [hdecomp]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[Matrix.mulVec_smul]`. Distinguish the cases in `hl : a ≤ l.val`.

Rewrite using `[hy' l hl, zero_smul, zero_smul]`. Establish `hlr : l.val < r` using `by omega`. Establish `h1` using `hfix ⟨l.val, hlr⟩`. Rewrite `h1` using `[show eI k r ⟨l.val, hlr⟩ = l from Fin.ext (eI_val _)]`. Rewrite using `[h1]`.
-/
theorem fix_low {g : Mx k r} (hfix : ∀ b : Fin r, g *ᵥ bvec (eI k r b) = bvec (eI k r b)) {a : ℕ}
    (har : a ≤ r) : ∀ y ∈ lowS k r a, g *ᵥ y = y := by
  intro y hy
  have hy' : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0 := hy
  have hdecomp : y = ∑ l, y l • bvec l := by
    unfold bvec
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum := map_sum (Matrix.mulVecLin g) (fun l => y l • bvec l) Finset.univ
  simp only [Matrix.mulVecLin_apply] at hsum
  conv_lhs => rw [hdecomp]
  rw [hsum]
  conv_rhs => rw [hdecomp]
  apply Finset.sum_congr rfl
  intro l _
  rw [Matrix.mulVec_smul]
  by_cases hl : a ≤ l.val
  · rw [hy' l hl, zero_smul, zero_smul]
  · have hlr : l.val < r := by omega
    have h1 := hfix ⟨l.val, hlr⟩
    rw [show eI k r ⟨l.val, hlr⟩ = l from Fin.ext (eI_val _)] at h1
    rw [h1]

/- English proof (translation)
Unfold `herm`. Establish `hh' : hᴴ * Hpk k r * h = Hpk k r` using `hh`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']`.
-/
theorem herm_inv {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ x) (h *ᵥ y) = herm (Hpk k r) x y := by
  unfold herm
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

/- English proof (translation)
Establish `hb` using `b.isLt`. Establish `hl` using `l.isLt`. Simplify using `only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | norm_num`.
-/
theorem hpk_row_esI (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) l = if l = eI k r b then 1 else 0 := by
  have hb := b.isLt
  have hl := l.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

/- English proof (translation)
Establish `hb` using `b.isLt`. Establish `hl` using `l.isLt`. Simplify using `only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | norm_num`.
-/
theorem hpk_row_eI (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) l = if l = esI k r b then 1 else 0 := by
  have hb := b.isLt
  have hl := l.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

/- English proof (translation)
Establish `hs : star (bvec (esI k r b) : Fin (2 * r + k + 1) → ℂ) = bvec (esI k r b)`. Unfold `bvec`. Use extensionality with `l`. Rewrite using `[Pi.star_apply]`. Apply the tactic sequence `by_cases h : l = esI k r b <;> simp [h]`.

Unfold `herm`. Rewrite using `[hs]`. Unfold `bvec`. Simplify using `[dotProduct, Matrix.mulVec, Pi.single_apply, hpk_row_esI]`.
-/
theorem herm_esI (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (esI k r b)) = y (eI k r b) := by
  have hs : star (bvec (esI k r b) : Fin (2 * r + k + 1) → ℂ) = bvec (esI k r b) := by
    unfold bvec
    ext l
    rw [Pi.star_apply]
    by_cases h : l = esI k r b <;> simp [h]
  unfold herm
  rw [hs]
  unfold bvec
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, hpk_row_esI]

/- English proof (translation)
Establish `hs : star (bvec (eI k r b) : Fin (2 * r + k + 1) → ℂ) = bvec (eI k r b)`. Unfold `bvec`. Use extensionality with `l`. Rewrite using `[Pi.star_apply]`. Apply the tactic sequence `by_cases h : l = eI k r b <;> simp [h]`.

Unfold `herm`. Rewrite using `[hs]`. Unfold `bvec`. Simplify using `[dotProduct, Matrix.mulVec, Pi.single_apply, hpk_row_eI]`.
-/
theorem herm_eI (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (eI k r b)) = y (esI k r b) := by
  have hs : star (bvec (eI k r b) : Fin (2 * r + k + 1) → ℂ) = bvec (eI k r b) := by
    unfold bvec
    ext l
    rw [Pi.star_apply]
    by_cases h : l = eI k r b <;> simp [h]
  unfold herm
  rw [hs]
  unfold bvec
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, hpk_row_eI]

/- English proof (translation)
Unfold `UWset at hh`. Simplify using `only [Set.mem_setOf_eq] at hh`. Take `⟨hU, hfix, -⟩` from `hh`. Establish `hv' : ∀ i : Fin (2 * r + k + 1), ↑i < r ∨ r + k < ↑i → v i = 0` using `hv`. Use `show ∀ i : Fin (2 * r + k + 1), ↑i < r ∨ r + k < ↑i → (h *ᵥ v) i = 0`.

Introduce `i hi`. Break down `hi with hi | hi` into its components or cases. Establish `e : i = eI k r ⟨i.val, hi⟩`. Use `ext`. Rewrite using `[eI_val]`.

Rewrite using `[e, ← herm_esI (h *ᵥ v) ⟨i.val, hi⟩, ← (hfix ⟨i.val, hi⟩).2, herm_inv hU, herm_esI, ← e]`. Conclude with `hv' i (Or.inl hi)`. Establish `hb : 2 * r + k - i.val < r`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `e : i = esI k r ⟨2 * r + k - i.val, hb⟩` using `Fin.ext (by`. Use `i.isLt` as an intermediate fact. Simplify using `only [esI, Fin.val_mk]`. Use the proof step `omega)`. Rewrite using `[e, ← herm_eI (h *ᵥ v) ⟨2 * r + k - i.val, hb⟩, ← (hfix ⟨2 * r + k - i.val, hb⟩).1, herm_inv hU, herm_eI, ← e]`.

Conclude with `hv' i (Or.inr hi)`.
-/
theorem uw_inWb {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : inWb k r (h *ᵥ v) := by
  unfold UWset at hh
  simp only [Set.mem_setOf_eq] at hh
  obtain ⟨hU, hfix, -⟩ := hh
  have hv' : ∀ i : Fin (2 * r + k + 1), ↑i < r ∨ r + k < ↑i → v i = 0 := hv
  show ∀ i : Fin (2 * r + k + 1), ↑i < r ∨ r + k < ↑i → (h *ᵥ v) i = 0
  intro i hi
  rcases hi with hi | hi
  · have e : i = eI k r ⟨i.val, hi⟩ := by
      ext
      rw [eI_val]
    rw [e, ← herm_esI (h *ᵥ v) ⟨i.val, hi⟩, ← (hfix ⟨i.val, hi⟩).2, herm_inv hU, herm_esI, ← e]
    exact hv' i (Or.inl hi)
  · have hb : 2 * r + k - i.val < r := by
      have := i.isLt
      omega
    have e : i = esI k r ⟨2 * r + k - i.val, hb⟩ := Fin.ext (by
      have := i.isLt
      simp only [esI, Fin.val_mk]
      omega)
    rw [e, ← herm_eI (h *ᵥ v) ⟨2 * r + k - i.val, hb⟩, ← (hfix ⟨2 * r + k - i.val, hb⟩).1,
      herm_inv hU, herm_eI, ← e]
    exact hv' i (Or.inr hi)

/- English proof (translation)
Unfold `UWset at *`. Simplify using `only [Set.mem_setOf_eq] at hh ⊢`. Take `⟨hU, hfix, hz⟩` from `hh`. Take `⟨-, h2, hinvU⟩` from `uh_inv hU`. Establish `key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v` using `fun v hv => by conv_lhs => rw [← hv]`.

Rewrite using `[Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]`. Conclude with `⟨hinvU, fun c => ⟨key _ (hfix c).1, key _ (hfix c).2⟩, key _ hz⟩`.
-/
theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  unfold UWset at *
  simp only [Set.mem_setOf_eq] at hh ⊢
  obtain ⟨hU, hfix, hz⟩ := hh
  obtain ⟨-, h2, hinvU⟩ := uh_inv hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  exact ⟨hinvU, fun c => ⟨key _ (hfix c).1, key _ (hfix c).2⟩, key _ hz⟩

/- English proof (translation)
Unfold `UWset at *`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Take `⟨haU, hafix, haz⟩` from `ha`. Take `⟨hbU, hbfix, hbz⟩` from `hb`. Use `⟨uh_mul haU hbU, fun c => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec, (hbfix c).1, (hafix c).1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hbfix c).2, (hafix c).2]`. Rewrite using `[← Matrix.mulVec_mulVec, hbz, haz]`.
-/
theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ} {a b : Mx k r} (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) :
    a * b ∈ UWset k r z := by
  unfold UWset at *
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨haU, hafix, haz⟩ := ha
  obtain ⟨hbU, hbfix, hbz⟩ := hb
  refine ⟨uh_mul haU hbU, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hbfix c).1, (hafix c).1]
  · rw [← Matrix.mulVec_mulVec, (hbfix c).2, (hafix c).2]
  · rw [← Matrix.mulVec_mulVec, hbz, haz]

/- English proof (translation)
Unfold `Nset at hn`. Simplify using `only [Set.mem_setOf_eq] at hn`. Take `⟨-, -, hmid⟩` from `hn`. Establish `hu' : ∀ i : Fin (2 * r + k + 1), ↑i < r ∨ r + k < ↑i → u i = 0` using `hu`. Use `show ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (n *ᵥ u - u) i = 0`.

Introduce `i hi`. Rewrite using `[Pi.sub_apply, sub_eq_zero]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i]`. Distinguish the cases in `hm : i.val ≤ r + k`.

Rewrite using `[hmid i i hi hm hi, if_pos rfl, one_mul]`. Rewrite using `[hu' i (Or.inr (by omega)), mul_zero]`. Introduce `l _ hl`. Distinguish the cases in `hlm : r ≤ l.val ∧ l.val ≤ r + k`. Rewrite using `[hmid i l hlm.1 hlm.2 hi, if_neg (fun h => hl h.symm), zero_mul]`.

Rewrite using `[hu' l (by omega), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem n_on_Wb {n : Mx k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ lowS k r r := by
  unfold Nset at hn
  simp only [Set.mem_setOf_eq] at hn
  obtain ⟨-, -, hmid⟩ := hn
  have hu' : ∀ i : Fin (2 * r + k + 1), ↑i < r ∨ r + k < ↑i → u i = 0 := hu
  show ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (n *ᵥ u - u) i = 0
  intro i hi
  rw [Pi.sub_apply, sub_eq_zero]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hm : i.val ≤ r + k
    · rw [hmid i i hi hm hi, if_pos rfl, one_mul]
    · rw [hu' i (Or.inr (by omega)), mul_zero]
  · intro l _ hl
    by_cases hlm : r ≤ l.val ∧ l.val ≤ r + k
    · rw [hmid i l hlm.1 hlm.2 hi, if_neg (fun h => hl h.symm), zero_mul]
    · rw [hu' l (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hh0` using `hh`. Establish `hn0` using `hn`. Unfold `UWset at hh`. Unfold `Nset at hn ⊢`. Simplify using `only [Set.mem_setOf_eq] at hh hn ⊢`.

Take `⟨hU, hfix, hz⟩` from `hh`. Take `⟨hnU, hcol, hmid⟩` from `hn`. Take `⟨h1, h2, hUi⟩` from `uh_inv hU`. Establish `hinvfix : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v` using `fun v hv => by conv_lhs => rw [← hv]`. Rewrite using `[Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]`.

Establish `hlow : ∀ a ≤ r, ∀ y ∈ lowS k r a, h⁻¹ *ᵥ y = y` using `fun a har => fix_low (fun b => hinvfix _ (hfix b).1) har`. Use `⟨uh_mul (uh_mul hUi hnU) hU, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩` and prove the remaining obligations. Establish `hc : (h⁻¹ * n * h) *ᵥ bvec (eI k r a) = h⁻¹ *ᵥ (n *ᵥ bvec (eI k r a))`. Rewrite using `[← Matrix.mulVec_mulVec, (hfix a).1, ← Matrix.mulVec_mulVec]`. Establish `hw : n *ᵥ bvec (eI k r a) - bvec (eI k r a) ∈ lowS k r a.val` using `by show ∀ i' : Fin (2 * r + k + 1), a.val ≤ i'.val → (n *ᵥ bvec (eI k r a) - bvec (eI k r a)) i' = 0`.

Introduce `i' hi'`. Establish `h5 : (n *ᵥ bvec (eI k r a)) i' = n i' (eI k r a)` using `by rw [col_eq]`. Rewrite using `[Pi.sub_apply, h5, hcol a i' hi']`. Unfold `bvec`. Rewrite using `[Pi.single_apply, sub_self]`.

Establish `hfixw` using `hlow a.val a.isLt.le _ hw`. Establish `hE : (h⁻¹ * n * h) *ᵥ bvec (eI k r a) = n *ᵥ bvec (eI k r a)`. Rewrite using `[hc]`. Establish `e : n *ᵥ bvec (eI k r a) = (n *ᵥ bvec (eI k r a) - bvec (eI k r a)) + bvec (eI k r a)` using `by abel`. Rewrite using `[e, Matrix.mulVec_add, hfixw, hinvfix _ (hfix a).1]`.

Establish `h5 : ((h⁻¹ * n * h) *ᵥ bvec (eI k r a)) i = (h⁻¹ * n * h) i (eI k r a)` using `by rw [col_eq]`. Establish `h6 : (n *ᵥ bvec (eI k r a)) i = n i (eI k r a)` using `by rw [col_eq]`. Rewrite using `[← h5, hE, h6, hcol a i hi]`. Establish `hej : inWb k r (bvec j)` using `by show ∀ i' : Fin (2 * r + k + 1), ↑i' < r ∨ r + k < ↑i' → bvec j i' = 0`. Introduce `i' hi'`.

Unfold `bvec`. Rewrite using `[Pi.single_apply, if_neg (fun h => by subst h; omega)]`. Establish `hv` using `uw_inWb hh0 hej`. Establish `hw` using `n_on_Wb hn0 hv`. Establish `hw' : ∀ i' : Fin (2 * r + k + 1), r ≤ i'.val → (n *ᵥ (h *ᵥ bvec j) - h *ᵥ bvec j) i' = 0` using `hw`.

Establish `hfixw` using `hlow r le_rfl _ hw`. Establish `hinvh : h⁻¹ *ᵥ (h *ᵥ bvec j) = bvec j`. Rewrite using `[Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]`. Establish `hE : (h⁻¹ * n * h) *ᵥ bvec j = bvec j + (n *ᵥ (h *ᵥ bvec j) - h *ᵥ bvec j)`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`.

Establish `e2 : n *ᵥ (h *ᵥ bvec j) = (n *ᵥ (h *ᵥ bvec j) - h *ᵥ bvec j) + h *ᵥ bvec j` using `by abel`. Rewrite using `[e2, Matrix.mulVec_add, hfixw, hinvh]`. Normalize the expressions using the abelian group laws. Establish `h5 : ((h⁻¹ * n * h) *ᵥ bvec j) i = (h⁻¹ * n * h) i j` using `by rw [col_eq]`. Rewrite using `[← h5, hE, Pi.add_apply, hw' i hi, add_zero]`.

Unfold `bvec`. Rewrite using `[Pi.single_apply]`.
-/
theorem conj_n {z : Fin (2 * r + k + 1) → ℂ} {h n : Mx k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) :
    h⁻¹ * n * h ∈ Nset k r := by
  have hh0 := hh
  have hn0 := hn
  unfold UWset at hh
  unfold Nset at hn ⊢
  simp only [Set.mem_setOf_eq] at hh hn ⊢
  obtain ⟨hU, hfix, hz⟩ := hh
  obtain ⟨hnU, hcol, hmid⟩ := hn
  obtain ⟨h1, h2, hUi⟩ := uh_inv hU
  have hinvfix : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have hlow : ∀ a ≤ r, ∀ y ∈ lowS k r a, h⁻¹ *ᵥ y = y := fun a har =>
    fix_low (fun b => hinvfix _ (hfix b).1) har
  refine ⟨uh_mul (uh_mul hUi hnU) hU, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · have hc : (h⁻¹ * n * h) *ᵥ bvec (eI k r a) = h⁻¹ *ᵥ (n *ᵥ bvec (eI k r a)) := by
      rw [← Matrix.mulVec_mulVec, (hfix a).1, ← Matrix.mulVec_mulVec]
    have hw : n *ᵥ bvec (eI k r a) - bvec (eI k r a) ∈ lowS k r a.val := by
      show ∀ i' : Fin (2 * r + k + 1), a.val ≤ i'.val →
        (n *ᵥ bvec (eI k r a) - bvec (eI k r a)) i' = 0
      intro i' hi'
      have h5 : (n *ᵥ bvec (eI k r a)) i' = n i' (eI k r a) := by rw [col_eq]
      rw [Pi.sub_apply, h5, hcol a i' hi']
      unfold bvec
      rw [Pi.single_apply, sub_self]
    have hfixw := hlow a.val a.isLt.le _ hw
    have hE : (h⁻¹ * n * h) *ᵥ bvec (eI k r a) = n *ᵥ bvec (eI k r a) := by
      rw [hc]
      have e : n *ᵥ bvec (eI k r a) =
          (n *ᵥ bvec (eI k r a) - bvec (eI k r a)) + bvec (eI k r a) := by abel
      rw [e, Matrix.mulVec_add, hfixw, hinvfix _ (hfix a).1]
    have h5 : ((h⁻¹ * n * h) *ᵥ bvec (eI k r a)) i = (h⁻¹ * n * h) i (eI k r a) := by rw [col_eq]
    have h6 : (n *ᵥ bvec (eI k r a)) i = n i (eI k r a) := by rw [col_eq]
    rw [← h5, hE, h6, hcol a i hi]
  · have hej : inWb k r (bvec j) := by
      show ∀ i' : Fin (2 * r + k + 1), ↑i' < r ∨ r + k < ↑i' → bvec j i' = 0
      intro i' hi'
      unfold bvec
      rw [Pi.single_apply, if_neg (fun h => by subst h; omega)]
    have hv := uw_inWb hh0 hej
    have hw := n_on_Wb hn0 hv
    have hw' : ∀ i' : Fin (2 * r + k + 1), r ≤ i'.val →
        (n *ᵥ (h *ᵥ bvec j) - h *ᵥ bvec j) i' = 0 := hw
    have hfixw := hlow r le_rfl _ hw
    have hinvh : h⁻¹ *ᵥ (h *ᵥ bvec j) = bvec j := by
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have hE : (h⁻¹ * n * h) *ᵥ bvec j = bvec j + (n *ᵥ (h *ᵥ bvec j) - h *ᵥ bvec j) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have e2 : n *ᵥ (h *ᵥ bvec j) = (n *ᵥ (h *ᵥ bvec j) - h *ᵥ bvec j) + h *ᵥ bvec j := by abel
      rw [e2, Matrix.mulVec_add, hfixw, hinvh]
      abel
    have h5 : ((h⁻¹ * n * h) *ᵥ bvec j) i = (h⁻¹ * n * h) i j := by rw [col_eq]
    rw [← h5, hE, Pi.add_apply, hw' i hi, add_zero]
    unfold bvec
    rw [Pi.single_apply]

/- English proof (translation)
Introduce `k r z`. Unfold `GrpF`. Use `⟨fun a ha b hb => uh_mul ha hb, fun a ha => uh_inv ha, fun a ha => uw_inv ha, fun a ha => n_inv ha, fun h hh n hn => conj_n hh hn, fun h hh n hn => ?_, fun a ha b hb => uw_mul ha hb⟩` and prove the remaining obligations. Establish `h1` using `conj_n (uw_inv hh) hn`. Establish `hU : h ∈ UH (Hpk k r)`.

Unfold `UWset at hh`. Conclude with `hh.1`. Take `⟨hinv1, -, -⟩` from `uh_inv hU`. Establish `hdet : IsUnit h.det` using `Matrix.isUnit_det_of_right_inverse hinv1`. Rewrite `h1` using `[Matrix.nonsing_inv_nonsing_inv h hdet]`. Then use the resulting hypothesis.
-/
theorem grpAll : GrpAll := by
  intro k r z
  unfold GrpF
  refine ⟨fun a ha b hb => uh_mul ha hb, fun a ha => uh_inv ha, fun a ha => uw_inv ha,
    fun a ha => n_inv ha, fun h hh n hn => conj_n hh hn, fun h hh n hn => ?_,
    fun a ha b hb => uw_mul ha hb⟩
  have h1 := conj_n (uw_inv hh) hn
  have hU : h ∈ UH (Hpk k r) := by
    unfold UWset at hh
    exact hh.1
  obtain ⟨hinv1, -, -⟩ := uh_inv hU
  have hdet : IsUnit h.det := Matrix.isUnit_det_of_right_inverse hinv1
  rwa [Matrix.nonsing_inv_nonsing_inv h hdet] at h1

end Grp

end PI.WBL.Cv
