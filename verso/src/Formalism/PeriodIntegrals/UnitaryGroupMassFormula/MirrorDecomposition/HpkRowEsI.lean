import Mathlib
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix

noncomputable section

namespace PI.MirrorSection₂

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

section Grp

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Apply the tactic sequence `let t : Fin (2 * r + k + 1) := ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩`. Rewrite using `[Finset.sum_eq_single t]`. Apply the tactic sequence `simp only [Hpk, t, Fin.ext_iff] split_ifs <;> first | omega | norm_num`.

Introduce `l _ hl`. Establish `hl' : l.val ≠ t.val` using `fun h => hl (Fin.ext h)`. Simplify using `only [t] at hl'`. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs at hl' ⊢ <;> first | omega | norm_num`.

Simplify using the standard rewrite rules.
-/
theorem hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  let t : Fin (2 * r + k + 1) :=
    ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩
  rw [Finset.sum_eq_single t]
  · simp only [Hpk, t, Fin.ext_iff]
    split_ifs <;> first | omega | norm_num
  · intro l _ hl
    have hl' : l.val ≠ t.val := fun h => hl (Fin.ext h)
    simp only [t] at hl'
    simp only [Hpk, Fin.ext_iff]
    split_ifs at hl' ⊢ <;> first | omega | norm_num
  · simp

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hb' : bᴴ * Hpk k r * b = Hpk k r` using `hb`. Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uh_mul {a b : B.Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hl : (Hpk k r * aᴴ * Hpk k r) * a = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv : a⁻¹ = Hpk k r * aᴴ * Hpk k r` using `Matrix.inv_eq_left_inv hl`. Establish `h1 : a⁻¹ * a = 1` using `by rw [hinv]; exact hl`.

Establish `h2 : a * a⁻¹ = 1` using `Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse hl)`. Use `⟨h2, h1, ?_⟩` and prove the remaining obligations. Use `show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uh_inv {a : B.Mat k r} (ha : a ∈ UH (Hpk k r)) :
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
Use function extensionality and compare the values at `i`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem col_eq (g : B.Mat k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

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
Introduce `y hy i hi`. Simplify using `only [Matrix.mulVec, dotProduct]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Distinguish the cases in `hl : a ≤ l.val`.

Rewrite using `[hy l hl, mul_zero]`. Establish `hlr : l.val < r` using `by omega`. Establish `hle : (eI k r ⟨l.val, hlr⟩) = l` using `Fin.ext rfl`. Use `hn ⟨l.val, hlr⟩ i (by simp; omega)` as an intermediate fact. Rewrite `this` using `[hle]`.

Rewrite using `[this, if_neg (by intro h; rw [h] at hi; omega), zero_mul]`.
-/
theorem maps_low {n : B.Mat k r} (hn : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      n i (eI k r a) = if i = eI k r a then 1 else 0) {a : ℕ} (har : a ≤ r) :
    ∀ y ∈ lowS k r a, n *ᵥ y ∈ lowS k r a := by
  intro y hy i hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : a ≤ l.val
  · rw [hy l hl, mul_zero]
  · have hlr : l.val < r := by omega
    have hle : (eI k r ⟨l.val, hlr⟩) = l := Fin.ext rfl
    have := hn ⟨l.val, hlr⟩ i (by simp; omega)
    rw [hle] at this
    rw [this, if_neg (by intro h; rw [h] at hi; omega), zero_mul]

/- English proof (translation)
Set `f : lowS k r a →ₗ[ℂ] lowS k r a` to `(Matrix.mulVecLin g).restrict hmaps`. Establish `hinj : Function.Injective f`. Introduce `x x' hxx`. Establish `h1 : g *ᵥ (x : Fin (2 * r + k + 1) → ℂ) = g *ᵥ x'` using `congrArg Subtype.val hxx`. Establish `h2` using `congrArg (fun v => g⁻¹ *ᵥ v) h1`.

Simplify using `only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2`. Conclude with `Subtype.ext h2`. Establish `hsurj` using `LinearMap.injective_iff_surjective.mp hinj`. Introduce `y hy`. Take `⟨x, hx⟩` from `hsurj ⟨y, hy⟩`.

Conclude with `⟨x.1, x.2, congrArg Subtype.val hx⟩`.
-/
theorem onto_low {g : B.Mat k r} (hg : g⁻¹ * g = 1) {a : ℕ} (hmaps : ∀ y ∈ lowS k r a, g *ᵥ y ∈ lowS k r a) :
    ∀ y ∈ lowS k r a, ∃ x ∈ lowS k r a, g *ᵥ x = y := by
  let f : lowS k r a →ₗ[ℂ] lowS k r a := (Matrix.mulVecLin g).restrict hmaps
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h1 : g *ᵥ (x : Fin (2 * r + k + 1) → ℂ) = g *ᵥ x' := congrArg Subtype.val hxx
    have h2 := congrArg (fun v => g⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

/- English proof (translation)
Establish `hu` using `uh_inv hn.1`. Establish `hC1` using `hn.2.1`. Use `⟨hu.2.2, ?_, ?_⟩` and prove the remaining obligations. Introduce `a i hai`. Establish `hmaps` using `maps_low hC1 (a := a.val) a.isLt.le`.

Establish `hy : bvec (eI k r a) - n *ᵥ bvec (eI k r a) ∈ lowS k r a.val`. Introduce `l hl`. Rewrite using `[col_eq]`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[hC1 a l hl]`.

Simplify using `[bvec, Pi.single_apply]`. Take `⟨x, hx, hgx⟩` from `onto_low hu.2.1 hmaps _ hy`. Establish `hx2 : n *ᵥ (x + bvec (eI k r a)) = bvec (eI k r a)`. Rewrite using `[Matrix.mulVec_add, hgx]`. Normalize the expressions using the abelian group laws.

Establish `hx3 : n⁻¹ *ᵥ bvec (eI k r a) = x + bvec (eI k r a)`. Rewrite using `[← hx2, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec, hx2]`. Establish `e` using `congrFun hx3 i`. Rewrite `e` using `[col_eq]`. Simplify using `only at e`.

Rewrite using `[e]`. Simplify using `only [Pi.add_apply]`. Rewrite using `[hx i hai, zero_add]`. Simplify using `[bvec, Pi.single_apply]`. Introduce `i j hj1 hj2 hi`.

Establish `hmaps` using `maps_low hC1 (a := r) le_rfl`. Establish `hy : bvec j - n *ᵥ bvec j ∈ lowS k r r`. Introduce `l hl`. Rewrite using `[col_eq]`. Simplify using `only [Pi.sub_apply]`.

Rewrite using `[hn.2.2 l j hj1 hj2 hl]`. Simplify using `[bvec, Pi.single_apply]`. Take `⟨x, hx, hgx⟩` from `onto_low hu.2.1 hmaps _ hy`. Establish `hx2 : n *ᵥ (x + bvec j) = bvec j`. Rewrite using `[Matrix.mulVec_add, hgx]`.

Normalize the expressions using the abelian group laws. Establish `hx3 : n⁻¹ *ᵥ bvec j = x + bvec j`. Rewrite using `[← hx2, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec, hx2]`. Establish `e` using `congrFun hx3 i`. Rewrite `e` using `[col_eq]`.

Simplify using `only at e`. Rewrite using `[e]`. Simplify using `only [Pi.add_apply]`. Rewrite using `[hx i hi, zero_add]`. Simplify using `[bvec, Pi.single_apply]`.
-/
theorem n_inv {n : B.Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Nset k r := by
  have hu := uh_inv hn.1
  have hC1 := hn.2.1
  refine ⟨hu.2.2, ?_, ?_⟩
  · intro a i hai
    have hmaps := maps_low hC1 (a := a.val) a.isLt.le
    have hy : bvec (eI k r a) - n *ᵥ bvec (eI k r a) ∈ lowS k r a.val := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hC1 a l hl]
      simp [bvec, Pi.single_apply]
    obtain ⟨x, hx, hgx⟩ := onto_low hu.2.1 hmaps _ hy
    have hx2 : n *ᵥ (x + bvec (eI k r a)) = bvec (eI k r a) := by
      rw [Matrix.mulVec_add, hgx]
      abel
    have hx3 : n⁻¹ *ᵥ bvec (eI k r a) = x + bvec (eI k r a) := by
      rw [← hx2, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec, hx2]
    have e := congrFun hx3 i
    rw [col_eq] at e
    simp only at e
    rw [e]
    simp only [Pi.add_apply]
    rw [hx i hai, zero_add]
    simp [bvec, Pi.single_apply]
  · intro i j hj1 hj2 hi
    have hmaps := maps_low hC1 (a := r) le_rfl
    have hy : bvec j - n *ᵥ bvec j ∈ lowS k r r := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hn.2.2 l j hj1 hj2 hl]
      simp [bvec, Pi.single_apply]
    obtain ⟨x, hx, hgx⟩ := onto_low hu.2.1 hmaps _ hy
    have hx2 : n *ᵥ (x + bvec j) = bvec j := by
      rw [Matrix.mulVec_add, hgx]
      abel
    have hx3 : n⁻¹ *ᵥ bvec j = x + bvec j := by
      rw [← hx2, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec, hx2]
    have e := congrFun hx3 i
    rw [col_eq] at e
    simp only at e
    rw [e]
    simp only [Pi.add_apply]
    rw [hx i hi, zero_add]
    simp [bvec, Pi.single_apply]

/- English proof (translation)
Introduce `y hy`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Establish `hterm : ∀ l : Fin (2 * r + k + 1), g i l * y l = if i = l then y l else 0`. Introduce `l`.

Distinguish the cases in `hl : a ≤ l.val`. Rewrite using `[hy l hl]`. Simplify using the standard rewrite rules. Establish `hlr : l.val < r` using `by omega`. Establish `hle : (eI k r ⟨l.val, hlr⟩) = l` using `Fin.ext rfl`.

Use `congrFun (hfix ⟨l.val, hlr⟩) i` as an intermediate fact. Rewrite `this` using `[col_eq, hle]`. Simplify using `only at this`. Rewrite using `[this]`. Distinguish the cases in `hil : i = l`.

Substitute `hil` using the available equality. Simplify using `[bvec]`. Simplify using `[bvec, Pi.single_apply, hil]`. Rewrite using `[Finset.sum_congr rfl (fun l _ => hterm l)]`. Simplify using the standard rewrite rules.
-/
theorem fix_low {g : B.Mat k r} (hfix : ∀ b : Fin r, g *ᵥ bvec (eI k r b) = bvec (eI k r b)) {a : ℕ}
    (har : a ≤ r) : ∀ y ∈ lowS k r a, g *ᵥ y = y := by
  intro y hy
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have hterm : ∀ l : Fin (2 * r + k + 1), g i l * y l = if i = l then y l else 0 := by
    intro l
    by_cases hl : a ≤ l.val
    · rw [hy l hl]
      simp
    · have hlr : l.val < r := by omega
      have hle : (eI k r ⟨l.val, hlr⟩) = l := Fin.ext rfl
      have := congrFun (hfix ⟨l.val, hlr⟩) i
      rw [col_eq, hle] at this
      simp only at this
      rw [this]
      by_cases hil : i = l
      · subst hil
        simp [bvec]
      · simp [bvec, Pi.single_apply, hil]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  simp

/- English proof (translation)
Establish `hh' : hᴴ * Hpk k r * h = Hpk k r` using `hh`. Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Rewrite using `[hh']`.
-/
theorem herm_inv {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ x) (h *ᵥ y) = herm (Hpk k r) x y := by
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hh']

/- English proof (translation)
Simplify using `only [Hpk, esI, eI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem hpk_row_esI (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) l = if l = eI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Simplify using `only [Hpk, esI, eI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem hpk_row_eI (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) l = if l = esI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Unfold `herm`. Simplify using `[bvec, dotProduct, Pi.single_apply, Matrix.mulVec, hpk_row_esI]`.
-/
theorem herm_esI (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (esI k r b)) = y (eI k r b) := by
  unfold herm
  simp [bvec, dotProduct, Pi.single_apply, Matrix.mulVec, hpk_row_esI]

/- English proof (translation)
Unfold `herm`. Simplify using `[bvec, dotProduct, Pi.single_apply, Matrix.mulVec, hpk_row_eI]`.
-/
theorem herm_eI (y : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) y (bvec (eI k r b)) = y (esI k r b) := by
  unfold herm
  simp [bvec, dotProduct, Pi.single_apply, Matrix.mulVec, hpk_row_eI]

/- English proof (translation)
Introduce `l hl`. Break down `hl with hl | hl` into its components or cases. Establish `hle : eI k r ⟨l.val, hl⟩ = l` using `Fin.ext rfl`. Establish `key : (h *ᵥ v) (eI k r ⟨l.val, hl⟩) = 0`. Rewrite using `[← herm_esI (h *ᵥ v) ⟨l.val, hl⟩, ← (hh.2.1 ⟨l.val, hl⟩).2, herm_inv hh.1, herm_esI]`.

Conclude with `hv _ (Or.inl hl)`. Rewrite `key` using `[hle]`. Then use the resulting hypothesis. Establish `hb : 2 * r + k - l.val < r` using `by omega`. Establish `hle : esI k r ⟨2 * r + k - l.val, hb⟩ = l`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [esI]`. Use linear arithmetic over natural numbers and integers. Establish `key : (h *ᵥ v) (esI k r ⟨2 * r + k - l.val, hb⟩) = 0`. Rewrite using `[← herm_eI (h *ᵥ v) ⟨2 * r + k - l.val, hb⟩, ← (hh.2.1 ⟨2 * r + k - l.val, hb⟩).1, herm_inv hh.1, herm_eI]`. Rewrite using `[hle]`.

Conclude with `hv l (Or.inr hl)`. Rewrite `key` using `[hle]`. Then use the resulting hypothesis.
-/
theorem uw_inWb {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : inWb k r (h *ᵥ v) := by
  intro l hl
  rcases hl with hl | hl
  · have hle : eI k r ⟨l.val, hl⟩ = l := Fin.ext rfl
    have key : (h *ᵥ v) (eI k r ⟨l.val, hl⟩) = 0 := by
      rw [← herm_esI (h *ᵥ v) ⟨l.val, hl⟩, ← (hh.2.1 ⟨l.val, hl⟩).2, herm_inv hh.1, herm_esI]
      exact hv _ (Or.inl hl)
    rwa [hle] at key
  · have hb : 2 * r + k - l.val < r := by omega
    have hle : esI k r ⟨2 * r + k - l.val, hb⟩ = l := by
      apply Fin.ext
      simp only [esI]
      omega
    have key : (h *ᵥ v) (esI k r ⟨2 * r + k - l.val, hb⟩) = 0 := by
      rw [← herm_eI (h *ᵥ v) ⟨2 * r + k - l.val, hb⟩, ← (hh.2.1 ⟨2 * r + k - l.val, hb⟩).1, herm_inv hh.1,
        herm_eI]
      rw [hle]
      exact hv l (Or.inr hl)
    rwa [hle] at key

/- English proof (translation)
Establish `hu` using `uh_inv hh.1`. Establish `back : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v`. Introduce `v hv`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨hu.2.2, fun a => ⟨back _ (hh.2.1 a).1, back _ (hh.2.1 a).2⟩, back _ hh.2.2⟩`.
-/
theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have hu := uh_inv hh.1
  have back : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec]
  exact ⟨hu.2.2, fun a => ⟨back _ (hh.2.1 a).1, back _ (hh.2.1 a).2⟩, back _ hh.2.2⟩

/- English proof (translation)
Use `⟨uh_mul ha.1 hb.1, fun c => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]`. Rewrite using `[← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]`.
-/
theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ} {a b : B.Mat k r} (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) :
    a * b ∈ UWset k r z := by
  refine ⟨uh_mul ha.1 hb.1, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]
  · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]
  · rw [← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]

/- English proof (translation)
Introduce `i hi`. Simplify using `only [Pi.sub_apply, Matrix.mulVec, dotProduct]`. Establish `hterm : ∀ l : Fin (2 * r + k + 1), n i l * u l = if i = l then u l else 0`. Introduce `l`. Distinguish the cases in `hl : l.val < r ∨ r + k < l.val`.

Rewrite using `[hu l hl]`. Simplify using the standard rewrite rules. Use `push Not at hl`. Rewrite using `[hn.2.2 i l hl.1 hl.2 hi]`. Apply the tactic sequence `by_cases hil : i = l <;> simp [hil]`.

Rewrite using `[Finset.sum_congr rfl (fun l _ => hterm l)]`. Simplify using the standard rewrite rules.
-/
theorem n_on_Wb {n : B.Mat k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ lowS k r r := by
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  have hterm : ∀ l : Fin (2 * r + k + 1), n i l * u l = if i = l then u l else 0 := by
    intro l
    by_cases hl : l.val < r ∨ r + k < l.val
    · rw [hu l hl]
      simp
    · push Not at hl
      rw [hn.2.2 i l hl.1 hl.2 hi]
      by_cases hil : i = l <;> simp [hil]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  simp

/- English proof (translation)
Establish `hu` using `uh_inv hh.1`. Establish `hhi` using `uw_inv hh`. Establish `hfixi : ∀ b : Fin r, h⁻¹ *ᵥ bvec (eI k r b) = bvec (eI k r b)` using `fun b => (hhi.2.1 b).1`. Use `⟨uh_mul (uh_mul hu.2.2 hn.1) hh.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `a i hai`.

Establish `hcol : (h⁻¹ * n * h) *ᵥ bvec (eI k r a) = n *ᵥ bvec (eI k r a)`. Rewrite using `[← Matrix.mulVec_mulVec, (hh.2.1 a).1, ← Matrix.mulVec_mulVec]`. Apply `fix_low hfixi le_rfl` to reduce the goal to its premises. Introduce `l hl`. Rewrite using `[col_eq]`.

Simplify using `only`. Rewrite using `[hn.2.1 a l (by have := a.isLt; omega), if_neg]`. Introduce `h'`. Establish `h2 : l.val = a.val` using `congrArg Fin.val h'`. Use `a.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `e` using `congrFun hcol i`. Rewrite `e` using `[col_eq, col_eq]`. Simplify using `only at e`. Rewrite using `[e]`.

Conclude with `hn.2.1 a i hai`. Introduce `i j hj1 hj2 hi`. Establish `hbj : inWb k r (bvec j)`. Introduce `l hl`. Simplify using `only [bvec, Pi.single_apply]`.

Rewrite using `[if_neg]`. Introduce `h'`. Rewrite `hl` using `[h']`. Use linear arithmetic over natural numbers and integers. Use `set u := h *ᵥ bvec j with hu_def`.

Establish `huW : inWb k r u` using `uw_inWb hh hbj`. Establish `hd` using `n_on_Wb hn huW`. Establish `hcol : (h⁻¹ * n * h) *ᵥ bvec j = bvec j + (n *ᵥ u - u)`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu_def]`. Establish `: n *ᵥ u = u + (n *ᵥ u - u)` using `by abel`.

Rewrite using `[this, Matrix.mulVec_add, fix_low hfixi le_rfl _ hd, hu_def, Matrix.mulVec_mulVec, hu.2.1, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Establish `e` using `congrFun hcol i`. Rewrite `e` using `[col_eq]`. Simplify using `only [Pi.add_apply] at e`.

Rewrite using `[e, hd i hi, add_zero]`. Simplify using `[bvec, Pi.single_apply]`.
-/
theorem conj_n {z : Fin (2 * r + k + 1) → ℂ} {h n : B.Mat k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) :
    h⁻¹ * n * h ∈ Nset k r := by
  have hu := uh_inv hh.1
  have hhi := uw_inv hh
  have hfixi : ∀ b : Fin r, h⁻¹ *ᵥ bvec (eI k r b) = bvec (eI k r b) := fun b => (hhi.2.1 b).1
  refine ⟨uh_mul (uh_mul hu.2.2 hn.1) hh.1, ?_, ?_⟩
  · intro a i hai
    have hcol : (h⁻¹ * n * h) *ᵥ bvec (eI k r a) = n *ᵥ bvec (eI k r a) := by
      rw [← Matrix.mulVec_mulVec, (hh.2.1 a).1, ← Matrix.mulVec_mulVec]
      apply fix_low hfixi le_rfl
      intro l hl
      rw [col_eq]
      simp only
      rw [hn.2.1 a l (by have := a.isLt; omega), if_neg]
      intro h'
      have h2 : l.val = a.val := congrArg Fin.val h'
      have := a.isLt
      omega
    have e := congrFun hcol i
    rw [col_eq, col_eq] at e
    simp only at e
    rw [e]
    exact hn.2.1 a i hai
  · intro i j hj1 hj2 hi
    have hbj : inWb k r (bvec j) := by
      intro l hl
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro h'
      rw [h'] at hl
      omega
    set u := h *ᵥ bvec j with hu_def
    have huW : inWb k r u := uw_inWb hh hbj
    have hd := n_on_Wb hn huW
    have hcol : (h⁻¹ * n * h) *ᵥ bvec j = bvec j + (n *ᵥ u - u) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu_def]
      have : n *ᵥ u = u + (n *ᵥ u - u) := by abel
      rw [this, Matrix.mulVec_add, fix_low hfixi le_rfl _ hd, hu_def, Matrix.mulVec_mulVec, hu.2.1,
        Matrix.one_mulVec]
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hd i hi, add_zero]
    simp [bvec, Pi.single_apply]

/- English proof (translation)
Use `⟨uh_mul hn.1 hm.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `a i hai`. Establish `hy : m *ᵥ bvec (eI k r a) - bvec (eI k r a) ∈ lowS k r a.val`. Introduce `l hl`. Rewrite using `[col_eq]`.

Simplify using `only [Pi.sub_apply]`. Rewrite using `[hm.2.1 a l hl]`. Simplify using `[bvec, Pi.single_apply]`. Establish `hmaps` using `maps_low hn.2.1 (a := a.val) a.isLt.le`. Establish `hcol : (n * m) *ᵥ bvec (eI k r a) = n *ᵥ bvec (eI k r a) + n *ᵥ (m *ᵥ bvec (eI k r a) - bvec (eI k r a))`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Establish `e` using `congrFun hcol i`. Rewrite `e` using `[col_eq]`.

Simplify using `only [Pi.add_apply] at e`. Rewrite using `[e, hmaps _ hy i hai, add_zero, col_eq]`. Conclude with `hn.2.1 a i hai`. Introduce `i j hj1 hj2 hi`. Establish `hy : m *ᵥ bvec j - bvec j ∈ lowS k r r`.

Introduce `l hl`. Rewrite using `[col_eq]`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[hm.2.2 l j hj1 hj2 hl]`. Simplify using `[bvec, Pi.single_apply]`.

Establish `hmaps` using `maps_low hn.2.1 (a := r) le_rfl`. Establish `hcol : (n * m) *ᵥ bvec j = n *ᵥ bvec j + n *ᵥ (m *ᵥ bvec j - bvec j)`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Establish `e` using `congrFun hcol i`. Rewrite `e` using `[col_eq]`. Simplify using `only [Pi.add_apply] at e`. Rewrite using `[e, hmaps _ hy i hi, add_zero, col_eq]`. Conclude with `hn.2.2 i j hj1 hj2 hi`.
-/
theorem n_mul {n m : B.Mat k r} (hn : n ∈ Nset k r) (hm : m ∈ Nset k r) : n * m ∈ Nset k r := by
  refine ⟨uh_mul hn.1 hm.1, ?_, ?_⟩
  · intro a i hai
    have hy : m *ᵥ bvec (eI k r a) - bvec (eI k r a) ∈ lowS k r a.val := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hm.2.1 a l hl]
      simp [bvec, Pi.single_apply]
    have hmaps := maps_low hn.2.1 (a := a.val) a.isLt.le
    have hcol : (n * m) *ᵥ bvec (eI k r a) =
        n *ᵥ bvec (eI k r a) + n *ᵥ (m *ᵥ bvec (eI k r a) - bvec (eI k r a)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
      congr 1
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hmaps _ hy i hai, add_zero, col_eq]
    exact hn.2.1 a i hai
  · intro i j hj1 hj2 hi
    have hy : m *ᵥ bvec j - bvec j ∈ lowS k r r := by
      intro l hl
      rw [col_eq]
      simp only [Pi.sub_apply]
      rw [hm.2.2 l j hj1 hj2 hl]
      simp [bvec, Pi.single_apply]
    have hmaps := maps_low hn.2.1 (a := r) le_rfl
    have hcol : (n * m) *ᵥ bvec j = n *ᵥ bvec j + n *ᵥ (m *ᵥ bvec j - bvec j) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
      congr 1
      abel
    have e := congrFun hcol i
    rw [col_eq] at e
    simp only [Pi.add_apply] at e
    rw [e, hmaps _ hy i hi, add_zero, col_eq]
    exact hn.2.2 i j hj1 hj2 hi

end Grp

end PI.MirrorSection₂
