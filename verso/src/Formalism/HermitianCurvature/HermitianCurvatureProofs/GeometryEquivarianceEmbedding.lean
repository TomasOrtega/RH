import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open PI.UnitaryGroupMassFormula.GsFr PI.UnitaryGroupMassFormula.DLm.Gram
open Matrix

noncomputable section

namespace S3

variable {k r : ℕ}

def Fsp (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range (fvec k r z))

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨b, rfl⟩`.
-/
lemma fv_mem (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) : fvec k r z b ∈ Fsp k r z :=
  Submodule.subset_span ⟨b, rfl⟩

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `h` using `fv_mem z (Fin.castSucc a)`. Unfold `fvec at h`. Rewrite `h` using `[dif_pos (show ((Fin.castSucc a : Fin (r + 1)) : ℕ) < r from a.isLt)]`.

Conclude with `h`.
-/
lemma X_le (z : Fin (2 * r + k + 1) → ℂ) : Xsp k r ≤ Fsp k r z := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  have h := fv_mem z (Fin.castSucc a)
  unfold fvec at h
  rw [dif_pos (show ((Fin.castSucc a : Fin (r + 1)) : ℕ) < r from a.isLt)] at h
  exact h

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hx`. Establish `hZc : Zhat k r z z' y *ᵥ c = 0`. Use function extensionality and compare the values at `a`. Use `horth a` as an intermediate fact. Rewrite `this` using `[mv_sum]`.

Simplify using `only [mulVec_smul] at this`. Rewrite `this` using `[hm_sum_l]`. Simplify using `only [mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun b _ => by simp only [Zhat]; ring`.

Establish `hc0 : c = 0` using `Matrix.eq_zero_of_mulVec_eq_zero hd hZc`. Rewrite using `[hc0]`. Simplify using the standard rewrite rules.
-/
lemma lift_unique' {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hd : (Zhat k r z z' y).det ≠ 0)
    {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Fsp k r z')
    (horth : ∀ a, herm (Hpk k r) (y *ᵥ x) (fvec k r z a) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
  have hZc : Zhat k r z z' y *ᵥ c = 0 := by
    funext a
    have := horth a
    rw [mv_sum] at this
    simp only [mulVec_smul] at this
    rw [hm_sum_l] at this
    simp only [mulVec, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by simp only [Zhat]; ring
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd hZc
  rw [hc0]
  simp

/- English proof (translation)
Establish `hw : w = ∑ a : Fin r, w (eI k r a) • bvec (eI k r a)`. Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply]`. Distinguish the cases in `hi : i.val < r`. Establish `hsum : ∀ a : Fin r, w (eI k r a) * (if i = eI k r a then 1 else 0) = if a = ⟨i.val, hi⟩ then w i else 0`.

Introduce `a`. Distinguish the cases in `ha : a = ⟨i.val, hi⟩`. Substitute `ha` using the available equality. Establish `: i = eI k r ⟨i.val, hi⟩` using `Fin.ext rfl`. Rewrite using `[if_pos this, if_pos rfl, mul_one, ← this]`.

Establish `hne : i ≠ eI k r a`. Introduce `h'`. Apply `ha` to reduce the goal to its premises. Use `ext`. Use `congrArg Fin.val h'` as an intermediate fact.

Simplify using `only [eI] at this`. Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hne, if_neg ha, mul_zero]`. Rewrite using `[Finset.sum_congr rfl (fun a _ => hsum a), Finset.sum_ite_eq']`.

Simplify using the standard rewrite rules. Rewrite using `[h i (by omega)]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`.

Establish `hne : i ≠ eI k r a`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Simplify using `only [eI] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg hne, mul_zero]`. Rewrite using `[hw]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
private lemma mem_xsp_of_apply_eq_zero_of_le {w : Fin (2 * r + k + 1) → ℂ} (h : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → w i = 0) :
    w ∈ Xsp k r := by
  have hw : w = ∑ a : Fin r, w (eI k r a) • bvec (eI k r a) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply]
    by_cases hi : i.val < r
    · have hsum : ∀ a : Fin r, w (eI k r a) * (if i = eI k r a then 1 else 0) =
          if a = ⟨i.val, hi⟩ then w i else 0 := by
        intro a
        by_cases ha : a = ⟨i.val, hi⟩
        · subst ha
          have : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
          rw [if_pos this, if_pos rfl, mul_one, ← this]
        · have hne : i ≠ eI k r a := by
            intro h'
            apply ha
            ext
            have := congrArg Fin.val h'
            simp only [eI] at this
            simp only [Fin.val_mk]
            omega
          rw [if_neg hne, if_neg ha, mul_zero]
      rw [Finset.sum_congr rfl (fun a _ => hsum a), Finset.sum_ite_eq']
      simp
    · rw [h i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro a _
      have hne : i ≠ eI k r a := by
        intro h'
        have := congrArg Fin.val h'
        simp only [eI] at this
        omega
      rw [if_neg hne, mul_zero]
  rw [hw]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Apply `mem_xsp_of_apply_eq_zero_of_le` to reduce the goal to its premises. Introduce `i hi`. Simplify using `only [Pi.sub_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[sub_eq_zero]`. Establish `key : ∀ j, n i j * v j = if j = i then v i else 0`.

Introduce `j`. Distinguish the cases in `hj : j.val < r ∨ r + k < j.val`. Rewrite using `[hv j hj, mul_zero] split_ifs with h`. Substitute `h` using the available equality. Conclude with `(hv _ hj).symm`.

Both sides reduce to the same expression. Rewrite using `[hn.2.2 i j (by omega) (by omega) hi]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => key j)]`. Simplify using the standard rewrite rules.
-/
lemma N_wb_X {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    n *ᵥ v - v ∈ Xsp k r := by
  apply mem_xsp_of_apply_eq_zero_of_le
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  rw [sub_eq_zero]
  have key : ∀ j, n i j * v j = if j = i then v i else 0 := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hv j hj, mul_zero]
      split_ifs with h
      · subst h
        exact (hv _ hj).symm
      · rfl
    · rw [hn.2.2 i j (by omega) (by omega) hi]
      by_cases h : j = i
      · subst h
        simp
      · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp

/- English proof (translation)
Use `⟨1, ?_, n, hn, (one_mul n).symm⟩` and prove the remaining obligations. Unfold `UWset`. Simplify using `[UH]`.
-/
lemma sset_N {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z := by
  refine ⟨1, ?_, n, hn, (one_mul n).symm⟩
  unfold UWset
  simp [UH]

/- English proof (translation)
Establish `hcol : ∀ b, n *ᵥ fvec k r z b ∈ Fsp k r z`. Introduce `b`. Establish `hsplit : n *ᵥ fvec k r z b = fvec k r z b + (n *ᵥ fvec k r z b - fvec k r z b)` using `by abel`. Rewrite using `[hsplit]`. Use `Submodule.add_mem _ (fv_mem z b) (X_le z ?_)` and prove the remaining obligations.

Unfold `fvec`. Use `split_ifs with hb`. Apply `mem_xsp_of_apply_eq_zero_of_le` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[Pi.sub_apply, bvec, Matrix.mulVec_single_one]`.

Use `show n i (eI k r ⟨b.val, hb⟩) - (Pi.single (eI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = 0`. Rewrite using `[hn.2.1 ⟨b.val, hb⟩ i (by simp only; omega), Pi.single_apply, sub_self]`. Conclude with `N_wb_X hn hz.1`. Use `Submodule.span_induction (p := fun x _ => n *ᵥ x ∈ Fsp k r z) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `hcol b`. Simplify using `[Submodule.zero_mem]`. Introduce `x y _ _ hx hy`. Rewrite using `[Matrix.mulVec_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Introduce `c x _ hx`. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
lemma N_Fsp {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ Nset k r)
    {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Fsp k r z) : n *ᵥ x ∈ Fsp k r z := by
  have hcol : ∀ b, n *ᵥ fvec k r z b ∈ Fsp k r z := by
    intro b
    have hsplit : n *ᵥ fvec k r z b = fvec k r z b + (n *ᵥ fvec k r z b - fvec k r z b) := by abel
    rw [hsplit]
    refine Submodule.add_mem _ (fv_mem z b) (X_le z ?_)
    unfold fvec
    split_ifs with hb
    · apply mem_xsp_of_apply_eq_zero_of_le
      intro i hi
      rw [Pi.sub_apply, bvec, Matrix.mulVec_single_one]
      show n i (eI k r ⟨b.val, hb⟩) - (Pi.single (eI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = 0
      rw [hn.2.1 ⟨b.val, hb⟩ i (by simp only; omega), Pi.single_apply, sub_self]
    · exact N_wb_X hn hz.1
  refine Submodule.span_induction (p := fun x _ => n *ᵥ x ∈ Fsp k r z) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩
    exact hcol b
  · simp [Submodule.zero_mem]
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hx

/- English proof (translation)
Establish `hfv : ∀ b, h *ᵥ fvec k r z b = fvec k r z b`. Introduce `b`. Unfold `fvec`. Use `split_ifs with hb`. Conclude with `(hh.2.1 ⟨b, hb⟩).1`.

Use `first`. Consider the case `exact hh.2.2`. Consider the case `exact hh.2.2.1`. Use `Submodule.span_induction (p := fun x _ => h *ᵥ x = x) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `hfv b`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[Matrix.mulVec_add, hx, hy]`. Introduce `c x _ hx`.

Rewrite using `[Matrix.mulVec_smul, hx]`.
-/
lemma UW_Fsp {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Fsp k r z) : h *ᵥ x = x := by
  have hfv : ∀ b, h *ᵥ fvec k r z b = fvec k r z b := by
    intro b
    unfold fvec
    split_ifs with hb
    · exact (hh.2.1 ⟨b, hb⟩).1
    · first
      | exact hh.2.2
      | exact hh.2.2.1
  refine Submodule.span_induction (p := fun x _ => h *ᵥ x = x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩
    exact hfv b
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add, hx, hy]
  · intro c x _ hx
    rw [Matrix.mulVec_smul, hx]

/- English proof (translation)
Establish `hdet : IsUnit n.det`. Assume the negation of the conclusion as `hnd`. Establish `h0 : n⁻¹ = 0` using `Matrix.nonsing_inv_apply_not_isUnit n hnd`. Establish `hm` using `(Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn).1`. Rewrite `hm` using `[h0]`.

Establish `hm' : (0 : B.Mat k r)ᴴ * Hpk k r * 0 = Hpk k r` using `hm`. Rewrite `hm'` using `[Matrix.mul_zero]`. Use `congrFun (congrFun hm' ⟨r + k, by omega⟩) ⟨r + k, by omega⟩` as an intermediate fact. Simplify using `[Hpk] at this`. Establish `hinv : n * n⁻¹ = 1` using `Matrix.mul_nonsing_inv n hdet`.

Establish `hU : ∀ x y, herm (Hpk k r) (n *ᵥ x) (n *ᵥ y) = herm (Hpk k r) x y`. Introduce `x y`. Establish `hh' : nᴴ * Hpk k r * n = Hpk k r` using `hn.1`. Use `show star (n *ᵥ y) ⬝ᵥ (Hpk k r *ᵥ (n *ᵥ x)) = star y ⬝ᵥ (Hpk k r *ᵥ x)`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']`.

Establish `horthF : ∀ g ∈ Fsp k r z, herm (Hpk k r) p g = 0`. Introduce `g hg`. Use `Submodule.span_induction (p := fun g _ => herm (Hpk k r) p g = 0) ?_ ?_ ?_ ?_ hg` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `hp b`.

Use `show star (0 : Fin (2 * r + k + 1) → ℂ) ⬝ᵥ (Hpk k r *ᵥ p) = 0`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Establish `hx' : star x ⬝ᵥ (Hpk k r *ᵥ p) = 0` using `hx`. Establish `hy' : star y ⬝ᵥ (Hpk k r *ᵥ p) = 0` using `hy`.

Use `show star (x + y) ⬝ᵥ (Hpk k r *ᵥ p) = 0`. Rewrite using `[star_add, add_dotProduct, hx', hy', add_zero]`. Introduce `c x _ hx`. Establish `hx' : star x ⬝ᵥ (Hpk k r *ᵥ p) = 0` using `hx`. Use `show star (c • x) ⬝ᵥ (Hpk k r *ᵥ p) = 0`.

Rewrite using `[star_smul, smul_dotProduct, hx', smul_zero]`. Establish `hf : n⁻¹ *ᵥ fvec k r z a ∈ Fsp k r z` using `N_Fsp hz (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn) (fv_mem z a)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Use `_ = herm (Hpk k r) p (n⁻¹ *ᵥ fvec k r z a) := hU _ _`.

Use `_ = 0 := horthF _ hf`.
-/
lemma N_orth {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ Nset k r)
    {p : Fin (2 * r + k + 1) → ℂ} (hp : ∀ b, herm (Hpk k r) p (fvec k r z b) = 0) (a : Fin (r + 1)) :
    herm (Hpk k r) (n *ᵥ p) (fvec k r z a) = 0 := by
  have hdet : IsUnit n.det := by
    by_contra hnd
    have h0 : n⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit n hnd
    have hm := (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn).1
    rw [h0] at hm
    have hm' : (0 : B.Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hm
    rw [Matrix.mul_zero] at hm'
    have := congrFun (congrFun hm' ⟨r + k, by omega⟩) ⟨r + k, by omega⟩
    simp [Hpk] at this
  have hinv : n * n⁻¹ = 1 := Matrix.mul_nonsing_inv n hdet
  have hU : ∀ x y, herm (Hpk k r) (n *ᵥ x) (n *ᵥ y) = herm (Hpk k r) x y := by
    intro x y
    have hh' : nᴴ * Hpk k r * n = Hpk k r := hn.1
    show star (n *ᵥ y) ⬝ᵥ (Hpk k r *ᵥ (n *ᵥ x)) = star y ⬝ᵥ (Hpk k r *ᵥ x)
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']
  have horthF : ∀ g ∈ Fsp k r z, herm (Hpk k r) p g = 0 := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ => herm (Hpk k r) p g = 0) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨b, rfl⟩
      exact hp b
    · show star (0 : Fin (2 * r + k + 1) → ℂ) ⬝ᵥ (Hpk k r *ᵥ p) = 0
      simp
    · intro x y _ _ hx hy
      have hx' : star x ⬝ᵥ (Hpk k r *ᵥ p) = 0 := hx
      have hy' : star y ⬝ᵥ (Hpk k r *ᵥ p) = 0 := hy
      show star (x + y) ⬝ᵥ (Hpk k r *ᵥ p) = 0
      rw [star_add, add_dotProduct, hx', hy', add_zero]
    · intro c x _ hx
      have hx' : star x ⬝ᵥ (Hpk k r *ᵥ p) = 0 := hx
      show star (c • x) ⬝ᵥ (Hpk k r *ᵥ p) = 0
      rw [star_smul, smul_dotProduct, hx', smul_zero]
  have hf : n⁻¹ *ᵥ fvec k r z a ∈ Fsp k r z := N_Fsp hz (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn) (fv_mem z a)
  calc herm (Hpk k r) (n *ᵥ p) (fvec k r z a)
      = herm (Hpk k r) (n *ᵥ p) (n *ᵥ (n⁻¹ *ᵥ fvec k r z a)) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = herm (Hpk k r) p (n⁻¹ *ᵥ fvec k r z a) := hU _ _
    _ = 0 := horthF _ hf

/- English proof (translation)
Establish `hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r` using `hh`. Use `show star (h *ᵥ w) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (h *ᵥ v)) = star w ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v)`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']`.
-/
private theorem herm_hpk_mulVec_of_mem_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v w := by
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show star (h *ᵥ w) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (h *ᵥ v)) = star w ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

/- English proof (translation)
Rewrite using `[← UW_Fsp hh (fv_mem z a), herm_hpk_mulVec_of_mem_uh hh.1]`. Conclude with `hp a`.
-/
lemma UW_orth {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    {p : Fin (2 * r + k + 1) → ℂ} (hp : ∀ b, herm (Hpk k r) p (fvec k r z b) = 0) (a : Fin (r + 1)) :
    herm (Hpk k r) (h *ᵥ p) (fvec k r z a) = 0 := by
  rw [← UW_Fsp hh (fv_mem z a), herm_hpk_mulVec_of_mem_uh hh.1]
  exact hp a

/- English proof (translation)
Establish `hX : ∀ a : Fin r, (h *ᵥ q) (esI k r a) = 0` using `fun a => by`. Rewrite using `[← herm_bvec_eI (h *ᵥ q) a, ← fvec_lt z a]`. Conclude with `UW_orth hh hq _`. Rewrite using `[prW_N hn hX, prW_UW hz hh]`.
-/
lemma prW_NUW {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n h : B.Mat k r} (hn : n ∈ Nset k r)
    (hh : h ∈ UWset k r z) {q : Fin (2 * r + k + 1) → ℂ} (hq : ∀ b, herm (Hpk k r) q (fvec k r z b) = 0) :
    PI.UnitaryGroupMassFormula.GsFr.prW k r z (n *ᵥ (h *ᵥ q)) = h *ᵥ PI.UnitaryGroupMassFormula.GsFr.prW k r z q := by
  have hX : ∀ a : Fin r, (h *ᵥ q) (esI k r a) = 0 := fun a => by
    rw [← herm_bvec_eI (h *ᵥ q) a, ← fvec_lt z a]; exact UW_orth hh hq _
  rw [prW_N hn hX, prW_UW hz hh]

/- English proof (translation)
Establish `Nc` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k r`. Unfold `omW'`. Rewrite using `[xcofL_N hz hz' hn hn' y, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec, show n⁻¹ *ᵥ (n *ᵥ xcofL k r z z' y) = xcofL k r z z' y by`. Rewrite using `[mulVec_mulVec, Matrix.nonsing_inv_mul _ (Nc.unit n hn), one_mulVec],`. Use `prW_N (Nc.inv_mem n' hn') (ginv_xcofL_esI z z' hy)]`.
-/
lemma omW'_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {y : B.Mat k r} (hy : y ∈ B.GV k r) :
    omW' k r z z' (n * y * n') = omW' k r z z' y := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  unfold omW'
  rw [xcofL_N hz hz' hn hn' y, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec,
    show n⁻¹ *ᵥ (n *ᵥ xcofL k r z z' y) = xcofL k r z z' y by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (Nc.unit n hn), one_mulVec],
    prW_N (Nc.inv_mem n' hn') (ginv_xcofL_esI z z' hy)]

/- English proof (translation)
Use `show ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ v)).re)⁻¹ : ℝ) : ℂ) • (h *ᵥ v)) = h *ᵥ ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v)`. Rewrite using `[herm_hpk_mulVec_of_mem_uh hh, Matrix.mulVec_smul]`.
-/
lemma unitH_UH {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    unitH k r (h *ᵥ v) = h *ᵥ unitH k r v := by
  show ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ v)).re)⁻¹ : ℝ) : ℂ) • (h *ᵥ v)) =
    h *ᵥ ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v)
  rw [herm_hpk_mulVec_of_mem_uh hh, Matrix.mulVec_smul]

/- English proof (translation)
Establish `e1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v q = (star q ᵥ* Formalism.QuantumDeterminants.Hpk k r) ⬝ᵥ v` using `by show star q ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) = _`. Conclude with `Matrix.dotProduct_mulVec _ _ _`. Rewrite using `[e1]`. Use extensionality with `i`. Simplify using `only [Rk, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
private theorem rk_mulVec_eq_herm_smul (p q v : Fin (2 * r + k + 1) → ℂ) :
    Rk k r p q *ᵥ v = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v q • p := by
  have e1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v q = (star q ᵥ* Formalism.QuantumDeterminants.Hpk k r) ⬝ᵥ v := by
    show star q ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) = _
    exact Matrix.dotProduct_mulVec _ _ _
  rw [e1]
  ext i
  simp only [Rk, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [Dw, Matrix.mulVec_diagonal, PI.UnitaryGroupMassFormula.GsFr.wbPart]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem dw_mulVec_eq_wbPart (v : Fin (2 * r + k + 1) → ℂ) : Dw k r *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.wbPart k r v := by
  ext i
  simp only [Dw, Matrix.mulVec_diagonal, PI.UnitaryGroupMassFormula.GsFr.wbPart]
  split_ifs <;> simp

/- English proof (translation)
Use `show (Pm k r z' - Rk k r (nuG' z z' g) (nuG' z z' g) * Pm k r z') *ᵥ v = _`. Establish `hPm : Pm k r z' *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v` using `by show (Dw k r + ((Tz k r z' : ℂ))⁻¹ • (Rk k r z' z' * Dw k r)) *ᵥ v = _`. Rewrite using `[Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, rk_mulVec_eq_herm_smul, dw_mulVec_eq_wbPart]`. Use `show _ = PI.UnitaryGroupMassFormula.GsFr.wbPart k r v + (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.wbPart k r v) z' / (Tz k r z' : ℂ)) • z'`. Rewrite using `[smul_smul, div_eq_inv_mul]`.

Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, rk_mulVec_eq_herm_smul, hPm]`.
-/
lemma PpG_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    PpG z z' g *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v -
      herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (nuG' z z' g) • nuG' z z' g := by
  show (Pm k r z' - Rk k r (nuG' z z' g) (nuG' z z' g) * Pm k r z') *ᵥ v = _
  have hPm : Pm k r z' *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v := by
    show (Dw k r + ((Tz k r z' : ℂ))⁻¹ • (Rk k r z' z' * Dw k r)) *ᵥ v = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, rk_mulVec_eq_herm_smul, dw_mulVec_eq_wbPart]
    show _ = PI.UnitaryGroupMassFormula.GsFr.wbPart k r v +
      (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.wbPart k r v) z' / (Tz k r z' : ℂ)) • z'
    rw [smul_smul, div_eq_inv_mul]
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, rk_mulVec_eq_herm_smul, hPm]

/- English proof (translation)
Use `show (PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g) *ᵥ v = _`. Rewrite using `[← Matrix.mulVec_mulVec]`.
-/
lemma ioG_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    ioG z z' g *ᵥ v = Phi k r z z' g *ᵥ (PpG z z' g *ᵥ v) := by
  show (PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]

/- English proof (translation)
Establish `hsum : ∀ (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ), Lm k r z z' M *ᵥ u - u ∈ Fsp k r z'`. Introduce `M u`. Rewrite using `[Lm_mulVec, add_sub_cancel_left]`. Conclude with `Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (fv_mem z' c)`. Establish `e1` using `hsum g (h' *ᵥ w)`.

Establish `e2 : n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w ∈ Fsp k r z'`. Establish `e3 : n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w = n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w - w)) + (n' *ᵥ (h' *ᵥ w) - h' *ᵥ w)`. Rewrite using `[mulVec_sub, mulVec_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e3]`.

Use `Submodule.add_mem _ ?_ (X_le z' (N_wb_X hn' (uw_inWb hz'.1 hh' hw)))` and prove the remaining obligations. Rewrite using `[UW_Fsp hh' (hsum y w)]`. Conclude with `N_Fsp hz' hn' (hsum y w)`. Establish `hD : Lm k r z z' g *ᵥ (h' *ᵥ w) - n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) ∈ Fsp k r z'`. Establish `: Lm k r z z' g *ᵥ (h' *ᵥ w) - n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) = (Lm k r z z' g *ᵥ (h' *ᵥ w) - h' *ᵥ w) - (n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w)` using `by abel`.

Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ e1 e2`. Establish `hg2 : ∀ x : Fin (2 * r + k + 1) → ℂ, g *ᵥ (n' *ᵥ (h' *ᵥ x)) = n *ᵥ (h *ᵥ (y *ᵥ x))`. Introduce `x`. Rewrite using `[mulVec_mulVec _ n' h', mulVec_mulVec, he, ← mulVec_mulVec, ← mulVec_mulVec]`.

Use `sub_eq_zero.1 (lift_unique' hd hD fun a => ?_)` and prove the remaining obligations. Rewrite using `[mulVec_sub, hm_sub_l, lift_orth hd, hg2, N_orth hz hn (UW_orth hh (lift_orth hdy w)) a, sub_zero]`.
-/
lemma lift_eq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    {n h n' h' g y : B.Mat k r} (hn : n ∈ Nset k r) (hh : h ∈ UWset k r z) (hn' : n' ∈ Nset k r)
    (hh' : h' ∈ UWset k r z') (hd : (Zhat k r z z' g).det ≠ 0) (hdy : (Zhat k r z z' y).det ≠ 0)
    (he : g * (n' * h') = n * h * y) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) :
    Lm k r z z' g *ᵥ (h' *ᵥ w) = n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) := by
  have hsum : ∀ (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ), Lm k r z z' M *ᵥ u - u ∈ Fsp k r z' := by
    intro M u
    rw [Lm_mulVec, add_sub_cancel_left]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (fv_mem z' c)
  have e1 := hsum g (h' *ᵥ w)
  have e2 : n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w ∈ Fsp k r z' := by
    have e3 : n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w =
        n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w - w)) + (n' *ᵥ (h' *ᵥ w) - h' *ᵥ w) := by
      rw [mulVec_sub, mulVec_sub]; abel
    rw [e3]
    refine Submodule.add_mem _ ?_ (X_le z' (N_wb_X hn' (uw_inWb hz'.1 hh' hw)))
    rw [UW_Fsp hh' (hsum y w)]
    exact N_Fsp hz' hn' (hsum y w)
  have hD : Lm k r z z' g *ᵥ (h' *ᵥ w) - n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) ∈ Fsp k r z' := by
    have : Lm k r z z' g *ᵥ (h' *ᵥ w) - n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) =
        (Lm k r z z' g *ᵥ (h' *ᵥ w) - h' *ᵥ w) - (n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w) := by abel
    rw [this]; exact Submodule.sub_mem _ e1 e2
  have hg2 : ∀ x : Fin (2 * r + k + 1) → ℂ, g *ᵥ (n' *ᵥ (h' *ᵥ x)) = n *ᵥ (h *ᵥ (y *ᵥ x)) := by
    intro x
    rw [mulVec_mulVec _ n' h', mulVec_mulVec, he, ← mulVec_mulVec, ← mulVec_mulVec]
  refine sub_eq_zero.1 (lift_unique' hd hD fun a => ?_)
  rw [mulVec_sub, hm_sub_l, lift_orth hd, hg2, N_orth hz hn (UW_orth hh (lift_orth hdy w)) a, sub_zero]

/- English proof (translation)
Establish `Nc` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k r`. Establish `Wz` using `Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z`. Establish `hF` using `Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz`. Establish `hF'` using `Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' hz'`. Rewrite using `[zhat_UW (Wz.inv_mem h hh) hh', zhat_N hz hz' (Nc.inv_mem n hn) hn' g, Matrix.nonsing_inv_nonsing_inv n (Nc.unit n hn), Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, unitri_det (hF.1 n (sset_N hn)).2.1, unitri_det (hF'.1 n' (sset_N hn')).2.1]`.

Simplify using `using hd`.
-/
lemma det_tilde {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    {n h n' h' g : B.Mat k r} (hn : n ∈ Nset k r) (hh : h ∈ UWset k r z) (hn' : n' ∈ Nset k r)
    (hh' : h' ∈ UWset k r z') (hd : (Zhat k r z z' g).det ≠ 0) :
    (Zhat k r z z' (h⁻¹ * (n⁻¹ * g * n') * h')).det ≠ 0 := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hF' := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' hz'
  rw [zhat_UW (Wz.inv_mem h hh) hh', zhat_N hz hz' (Nc.inv_mem n hn) hn' g,
    Matrix.nonsing_inv_nonsing_inv n (Nc.unit n hn), Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    unitri_det (hF.1 n (sset_N hn)).2.1, unitri_det (hF'.1 n' (sset_N hn')).2.1]
  simpa using hd

end S3

open S3 in
/- English proof (translation)
Introduce `k r z z' hk hz hz' h hh n hn h' hh' n' hn' g hg`. Establish `Nc` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k r`. Establish `Wz` using `Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z`. Establish `Wz'` using `Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'`. Use `set y := h⁻¹ * n⁻¹ * g * n' * h' with hy_def`.

Establish `hyA : y = h⁻¹ * (n⁻¹ * g * n') * h'` using `by simp only [hy_def, Matrix.mul_assoc]`. Establish `hgy : g * (n' * h') = n * h * y`. Rewrite using `[hy_def]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc h h⁻¹, Matrix.mul_nonsing_inv _ (Wz.unit h hh), Matrix.one_mul, ← Matrix.mul_assoc n n⁻¹, Matrix.mul_nonsing_inv _ (Nc.unit n hn), Matrix.one_mul]`.

Establish `hd : (Zhat k r z z' g).det ≠ 0` using `det_ne_of_G hz hz' hg.2`. Establish `hdy : (Zhat k r z z' y).det ≠ 0` using `by rw [hyA]; exact det_tilde hz hz' hn hh hn' hh' hd`. Establish `hom : omW' k r z z' g = h' *ᵥ omW' k r z z' y`. Rewrite using `[hyA, omW'_UW hz hz' (Wz.inv_mem h hh) hh', omW'_N hz hz' (Nc.inv_mem n hn) hn' hg.1, mulVec_mulVec, Matrix.mul_nonsing_inv _ (Wz'.unit h' hh'), one_mulVec]`. Establish `hν' : nuG' z z' g = h' *ᵥ nuG' z z' y`.

Unfold `nuG'`. Rewrite using `[hom, unitH_UH hh'.1]`. Establish `hP : ∀ v, PpG z z' g *ᵥ (h' *ᵥ v) = h' *ᵥ (PpG z z' y *ᵥ v)`. Introduce `v`. Rewrite using `[PpG_mulVec, PpG_mulVec, hν', prW_UW hz' hh', Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hh'.1, mulVec_sub, mulVec_smul]`.

Establish `hPw : ∀ v, inWb k r (PpG z z' y *ᵥ v)`. Introduce `v i hi`. Establish `h1` using `(prW_mem hz' v).1 i hi`. Establish `h2 : omW' k r z z' y i = 0` using `(prW_mem hz' _).1 i hi`. Simplify using `only [PpG_mulVec, nuG', unitH, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2, mul_zero, sub_zero]`.

Establish `hPhi : ∀ w, inWb k r w → Phi k r z z' g *ᵥ (h' *ᵥ w) = h *ᵥ (Phi k r z z' y *ᵥ w)`. Introduce `w hw`. Rewrite using `[Phi_mulVec, Phi_mulVec, lift_eq hz hz' hn hh hn' hh' hd hdy hgy hw, mulVec_mulVec _ n' h', mulVec_mulVec, hgy, ← mulVec_mulVec, ← mulVec_mulVec, prW_NUW hz hn hh (lift_orth hdy w)]`. Establish `key : ∀ v, ioG z z' g *ᵥ (h' *ᵥ v) = h *ᵥ (ioG z z' y *ᵥ v)`. Introduce `v`.

Rewrite using `[ioG_mulVec, ioG_mulVec, hP, hPhi _ (hPw v)]`. Establish `hm : ioG z z' g * h' = h * ioG z z' y`. Use extensionality with `i j`. Use `congrFun (key (Pi.single j 1)) i` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, mulVec_mulVec]`.

Simplify `this` using `[Matrix.mulVec_single_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Wz'.unit h' hh'), Matrix.mul_one]`. Use `_ = h * ioG z z' y * h'⁻¹ := by rw [hm]`.
-/
theorem geometry_equivariance_embedding : GeomEqvIo := by
  intro k r z z' hk hz hz' h hh n hn h' hh' n' hn' g hg
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  set y := h⁻¹ * n⁻¹ * g * n' * h' with hy_def
  have hyA : y = h⁻¹ * (n⁻¹ * g * n') * h' := by simp only [hy_def, Matrix.mul_assoc]
  have hgy : g * (n' * h') = n * h * y := by
    rw [hy_def]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h h⁻¹, Matrix.mul_nonsing_inv _ (Wz.unit h hh), Matrix.one_mul,
      ← Matrix.mul_assoc n n⁻¹, Matrix.mul_nonsing_inv _ (Nc.unit n hn), Matrix.one_mul]
  have hd : (Zhat k r z z' g).det ≠ 0 := det_ne_of_G hz hz' hg.2
  have hdy : (Zhat k r z z' y).det ≠ 0 := by rw [hyA]; exact det_tilde hz hz' hn hh hn' hh' hd
  have hom : omW' k r z z' g = h' *ᵥ omW' k r z z' y := by
    rw [hyA, omW'_UW hz hz' (Wz.inv_mem h hh) hh', omW'_N hz hz' (Nc.inv_mem n hn) hn' hg.1, mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Wz'.unit h' hh'), one_mulVec]
  have hν' : nuG' z z' g = h' *ᵥ nuG' z z' y := by
    unfold nuG'; rw [hom, unitH_UH hh'.1]
  have hP : ∀ v, PpG z z' g *ᵥ (h' *ᵥ v) = h' *ᵥ (PpG z z' y *ᵥ v) := by
    intro v
    rw [PpG_mulVec, PpG_mulVec, hν', prW_UW hz' hh', Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hh'.1, mulVec_sub, mulVec_smul]
  have hPw : ∀ v, inWb k r (PpG z z' y *ᵥ v) := by
    intro v i hi
    have h1 := (prW_mem hz' v).1 i hi
    have h2 : omW' k r z z' y i = 0 := (prW_mem hz' _).1 i hi
    simp only [PpG_mulVec, nuG', unitH, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2, mul_zero, sub_zero]
  have hPhi : ∀ w, inWb k r w → Phi k r z z' g *ᵥ (h' *ᵥ w) = h *ᵥ (Phi k r z z' y *ᵥ w) := by
    intro w hw
    rw [Phi_mulVec, Phi_mulVec, lift_eq hz hz' hn hh hn' hh' hd hdy hgy hw, mulVec_mulVec _ n' h', mulVec_mulVec,
      hgy, ← mulVec_mulVec, ← mulVec_mulVec, prW_NUW hz hn hh (lift_orth hdy w)]
  have key : ∀ v, ioG z z' g *ᵥ (h' *ᵥ v) = h *ᵥ (ioG z z' y *ᵥ v) := by
    intro v; rw [ioG_mulVec, ioG_mulVec, hP, hPhi _ (hPw v)]
  have hm : ioG z z' g * h' = h * ioG z z' y := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [mulVec_mulVec, mulVec_mulVec] at this
    simpa [Matrix.mulVec_single_one] using this
  calc ioG z z' g = ioG z z' g * h' * h'⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Wz'.unit h' hh'), Matrix.mul_one]
    _ = h * ioG z z' y * h'⁻¹ := by rw [hm]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
