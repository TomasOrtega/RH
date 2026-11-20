import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

namespace RvB

variable {k r : ℕ}

/- English proof (translation)
Simplify using `only [eI, esI, ne_eq, Fin.ext_iff]`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  simp only [eI, esI, ne_eq, Fin.ext_iff]; have := a.isLt; have := b.isLt; omega

/- English proof (translation)
Simplify using `only [eI, Fin.ext_iff] at h`. Conclude with `Fin.ext h`.
-/
theorem eI_inj {a b : Fin r} (h : eI k r a = eI k r b) : a = b := by
  simp only [eI, Fin.ext_iff] at h; exact Fin.ext h

/- English proof (translation)
Simplify using `only [esI, Fin.ext_iff] at h; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)`.
-/
theorem esI_inj {a b : Fin r} (h : esI k r a = esI k r b) : a = b := by
  simp only [esI, Fin.ext_iff] at h; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_e, Formalism.FourierDecayAlt.P.Qx3.dd_e]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem w1_mulVec_bvec_eI (a : Fin r) (c : ℂ) : Q.w1 k r a c *ᵥ bvec (eI k r a) = c • bvec (esI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_e, Formalism.FourierDecayAlt.P.Qx3.dd_e]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_es, Formalism.FourierDecayAlt.P.Qx3.dd_es]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem w1_mulVec_bvec_esI (a : Fin r) (c : ℂ) : Q.w1 k r a c *ᵥ bvec (esI k r a) = (star c)⁻¹ • bvec (eI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, Formalism.FourierDecayAlt.P.Qx3.sw_es, Formalism.FourierDecayAlt.P.Qx3.dd_es]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single (Formalism.FourierDecayAlt.P.Qx3.sw k b p)]`. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.w1_apply, if_pos (Formalism.FourierDecayAlt.P.Qx3.sw_sw b p).symm]`. Break down `Formalism.FourierDecayAlt.P.Qx3.tri b p with h | h | ⟨h1', h2'⟩` into its components or cases. Substitute `h` using the available equality.

Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.sw_e, h2, h1, mul_zero]`. Substitute `h` using the available equality. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.sw_es, h1, h2, mul_zero]`. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.sw_o b h1' h2', Formalism.FourierDecayAlt.P.Qx3.dd_o b c h1' h2', one_mul]`. Introduce `q _ hq`.

Establish `: p ≠ Formalism.FourierDecayAlt.P.Qx3.sw k b q` using `fun h => hq (by rw [h, Formalism.FourierDecayAlt.P.Qx3.sw_sw])`. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.w1_apply, if_neg this, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem w1_mulVec_eq_self_of_eI_esI_eq_zero (b : Fin r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) (h1 : v (eI k r b) = 0)
    (h2 : v (esI k r b) = 0) : Q.w1 k r b c *ᵥ v = v := by
  funext p
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Formalism.FourierDecayAlt.P.Qx3.sw k b p)]
  · rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, if_pos (Formalism.FourierDecayAlt.P.Qx3.sw_sw b p).symm]
    rcases Formalism.FourierDecayAlt.P.Qx3.tri b p with h | h | ⟨h1', h2'⟩
    · subst h; rw [Formalism.FourierDecayAlt.P.Qx3.sw_e, h2, h1, mul_zero]
    · subst h; rw [Formalism.FourierDecayAlt.P.Qx3.sw_es, h1, h2, mul_zero]
    · rw [Formalism.FourierDecayAlt.P.Qx3.sw_o b h1' h2', Formalism.FourierDecayAlt.P.Qx3.dd_o b c h1' h2', one_mul]
  · intro q _ hq
    have : p ≠ Formalism.FourierDecayAlt.P.Qx3.sw k b q := fun h => hq (by rw [h, Formalism.FourierDecayAlt.P.Qx3.sw_sw])
    rw [Formalism.FourierDecayAlt.P.Qx3.w1_apply, if_neg this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons b L ih`. Rewrite using `[List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, w1_mulVec_eq_self_of_eI_esI_eq_zero b _ v (hv b).1 (hv b).2]`.
-/
theorem wl_fixv (c : Fin r → ℂ) (L : List (Fin r)) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b, v (eI k r b) = 0 ∧ v (esI k r b) = 0) : (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ v = v := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, w1_mulVec_eq_self_of_eI_esI_eq_zero b _ v (hv b).1 (hv b).2]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons b L ih`. Rewrite `hL` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hL.2]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_neg hL.1, w1_mulVec_bvec_eI, if_pos List.mem_cons_self]`. Establish `hmem : (a ∈ b :: L) ↔ a ∈ L` using `by simp [hab]`. Distinguish the cases in `h1 : a ∈ L`.

Rewrite using `[if_pos h1, if_pos (hmem.2 h1), Matrix.mulVec_smul, Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _ (fun h => eI_ne_esI b a h.symm) (fun h => hab (esI_inj h))]`. Rewrite using `[if_neg h1, if_neg (fun h => h1 (hmem.1 h)), Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _ (fun h => hab (eI_inj h)) (fun h => eI_ne_esI a b h)]`.
-/
theorem wl_e (c : Fin r → ℂ) (L : List (Fin r)) (hL : L.Nodup) (a : Fin r) :
    (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ bvec (eI k r a) =
      if a ∈ L then c a • bvec (esI k r a) else bvec (eI k r a) := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hL.2]
    by_cases hab : a = b
    · subst hab
      rw [if_neg hL.1, w1_mulVec_bvec_eI, if_pos List.mem_cons_self]
    · have hmem : (a ∈ b :: L) ↔ a ∈ L := by simp [hab]
      by_cases h1 : a ∈ L
      · rw [if_pos h1, if_pos (hmem.2 h1), Matrix.mulVec_smul, Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => eI_ne_esI b a h.symm) (fun h => hab (esI_inj h))]
      · rw [if_neg h1, if_neg (fun h => h1 (hmem.1 h)), Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => hab (eI_inj h)) (fun h => eI_ne_esI a b h)]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons b L ih`. Rewrite `hL` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hL.2]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_neg hL.1, w1_mulVec_bvec_esI, if_pos List.mem_cons_self]`. Establish `hmem : (a ∈ b :: L) ↔ a ∈ L` using `by simp [hab]`. Distinguish the cases in `h1 : a ∈ L`.

Rewrite using `[if_pos h1, if_pos (hmem.2 h1), Matrix.mulVec_smul, Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _ (fun h => hab (eI_inj h)) (fun h => eI_ne_esI a b h)]`. Rewrite using `[if_neg h1, if_neg (fun h => h1 (hmem.1 h)), Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _ (fun h => eI_ne_esI b a h.symm) (fun h => hab (esI_inj h))]`.
-/
theorem wl_es (c : Fin r → ℂ) (L : List (Fin r)) (hL : L.Nodup) (a : Fin r) :
    (L.map fun b => Q.w1 k r b (c b)).prod *ᵥ bvec (esI k r a) =
      if a ∈ L then (star (c a))⁻¹ • bvec (eI k r a) else bvec (esI k r a) := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih hL.2]
    by_cases hab : a = b
    · subst hab
      rw [if_neg hL.1, w1_mulVec_bvec_esI, if_pos List.mem_cons_self]
    · have hmem : (a ∈ b :: L) ↔ a ∈ L := by simp [hab]
      by_cases h1 : a ∈ L
      · rw [if_pos h1, if_pos (hmem.2 h1), Matrix.mulVec_smul, Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => hab (eI_inj h)) (fun h => eI_ne_esI a b h)]
      · rw [if_neg h1, if_neg (fun h => h1 (hmem.1 h)), Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector b _
          (fun h => eI_ne_esI b a h.symm) (fun h => hab (esI_inj h))]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wc_list (c : Fin r → ℂ) : Q.wCell k r (Fin.last r) c =
    (((List.finRange r).filter fun a => a.val < (Fin.last r).val).map fun a => Q.w1 k r a (c a)).prod := rfl

/- English proof (translation)
The claim follows from `(List.nodup_finRange r).filter _`.
-/
theorem wc_nodup : ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val).Nodup :=
  (List.nodup_finRange r).filter _

/- English proof (translation)
Rewrite using `[List.mem_filter]; exact ⟨List.mem_finRange a, by simp [a.isLt]⟩`.
-/
theorem wc_mem (a : Fin r) : a ∈ ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val) := by
  rw [List.mem_filter]; exact ⟨List.mem_finRange a, by simp [a.isLt]⟩

/- English proof (translation)
Rewrite using `[wc_list, wl_e c _ wc_nodup, if_pos (wc_mem a)]`.
-/
theorem W_e (c : Fin r → ℂ) (a : Fin r) :
    Q.wCell k r (Fin.last r) c *ᵥ bvec (eI k r a) = c a • bvec (esI k r a) := by
  rw [wc_list, wl_e c _ wc_nodup, if_pos (wc_mem a)]

/- English proof (translation)
Rewrite using `[wc_list, wl_es c _ wc_nodup, if_pos (wc_mem a)]`.
-/
theorem W_es (c : Fin r → ℂ) (a : Fin r) :
    Q.wCell k r (Fin.last r) c *ᵥ bvec (esI k r a) = (star (c a))⁻¹ • bvec (eI k r a) := by
  rw [wc_list, wl_es c _ wc_nodup, if_pos (wc_mem a)]

/- English proof (translation)
Rewrite using `[wc_list, wl_fixv c _ v hv]`.
-/
theorem W_fix (c : Fin r → ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ b, v (eI k r b) = 0 ∧ v (esI k r b) = 0) :
    Q.wCell k r (Fin.last r) c *ᵥ v = v := by
  rw [wc_list, wl_fixv c _ v hv]

/- English proof (translation)
Establish `hW' : Wᴴ * Hpk k r * W = Hpk k r` using `hW`. Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW']`.
-/
theorem herm_uh {W : Q.Mx k r} (hW : W ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (W *ᵥ x) (W *ᵥ y) = herm (Hpk k r) x y := by
  have hW' : Wᴴ * Hpk k r * W = Hpk k r := hW
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW']

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`.
-/
theorem herm_smul_right (x w : Fin (2 * r + k + 1) → ℂ) (s : ℂ) :
    herm (Hpk k r) x (s • w) = star s * herm (Hpk k r) x w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `herm bvec`. Rewrite using `[Matrix.mulVec_single_one]`. Simplify using `[dotProduct, Pi.single_apply]`.
-/
theorem herm_bvec (p q : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec q) (bvec p) = Hpk k r p q := by
  unfold herm bvec
  rw [Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

section what₂

variable {c : Fin r → ℂ} {g : Q.Mx k r}

/- English proof (translation)
Establish `hW : Q.wCell k r (Fin.last r) c ∈ UH (Hpk k r)` using `(Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val)).1`. Establish `hca : star (c a) ≠ 0` using `star_ne_zero.2 (hc a)`. Establish `he : bvec (eI k r a) = Q.wCell k r (Fin.last r) c *ᵥ (star (c a) • bvec (esI k r a))`. Rewrite using `[Matrix.mulVec_smul, W_es, smul_smul, mul_inv_cancel₀ hca, one_smul]`. Establish `hges : g *ᵥ bvec (esI k r a) = bvec (esI k r a)` using `(hg.2 a (by simp [a.isLt])).2`.

Rewrite using `[← Matrix.mulVec_mulVec, he, herm_uh hW, herm_smul_right, star_star, ← hges, herm_uh hg.1, herm_bvec, Formalism.FourierDecayAlt.P.Qx3.hpk_row_es]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem row_e (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec q) (bvec (eI k r a)) =
      if q = eI k r a then c a else 0 := by
  have hW : Q.wCell k r (Fin.last r) c ∈ UH (Hpk k r) :=
    (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val)).1
  have hca : star (c a) ≠ 0 := star_ne_zero.2 (hc a)
  have he : bvec (eI k r a) = Q.wCell k r (Fin.last r) c *ᵥ (star (c a) • bvec (esI k r a)) := by
    rw [Matrix.mulVec_smul, W_es, smul_smul, mul_inv_cancel₀ hca, one_smul]
  have hges : g *ᵥ bvec (esI k r a) = bvec (esI k r a) := (hg.2 a (by simp [a.isLt])).2
  rw [← Matrix.mulVec_mulVec, he, herm_uh hW, herm_smul_right, star_star, ← hges, herm_uh hg.1, herm_bvec,
    Formalism.FourierDecayAlt.P.Qx3.hpk_row_es]
  split_ifs <;> simp

/- English proof (translation)
Establish `hW : Q.wCell k r (Fin.last r) c ∈ UH (Hpk k r)` using `(Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val)).1`. Establish `hzf : Q.wCell k r (Fin.last r) c *ᵥ z = z` using `W_fix c z fun b => ⟨hz _ (Or.inl (by simp [eI])), hz _ (Or.inr (by simp [esI]; have := b.isLt; omega))⟩`. Use `conv_lhs => rw [← hzf]`. Rewrite using `[← Matrix.mulVec_mulVec, herm_uh hW]`.
-/
theorem herm_wCell_last_mul_mulVec_eq_of_inWb (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ v) z = herm (Hpk k r) (g *ᵥ v) z := by
  have hW : Q.wCell k r (Fin.last r) c ∈ UH (Hpk k r) :=
    (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc ((List.finRange r).filter fun a : Fin r => a.val < (Fin.last r).val)).1
  have hzf : Q.wCell k r (Fin.last r) c *ᵥ z = z := W_fix c z fun b =>
    ⟨hz _ (Or.inl (by simp [eI])), hz _ (Or.inr (by simp [esI]; have := b.isLt; omega))⟩
  conv_lhs => rw [← hzf]
  rw [← Matrix.mulVec_mulVec, herm_uh hW]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hg.2 a (by simp [a.isLt])`. Establish `hz1 : z (esI k r a) = 0` using `hz _ (Or.inr (by simp [esI]; have := a.isLt; omega))`. Establish `hz2 : z (eI k r a) = 0` using `hz _ (Or.inl (by simp [eI]))`. Rewrite using `[h1, h2]`. Prove the components needed by the constructor for the conclusion.

Simplify using `only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Matrix.col_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.hpk_col_e]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Simplify using `[hz1]`. Simplify using the standard rewrite rules. Simplify using `only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Matrix.col_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.FourierDecayAlt.P.Qx3.hpk_col_es]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[hz2]`. Simplify using the standard rewrite rules.
-/
theorem row_z_e (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin r) :
    herm (Hpk k r) (g *ᵥ bvec (eI k r a)) z = 0 ∧ herm (Hpk k r) (g *ᵥ bvec (esI k r a)) z = 0 := by
  obtain ⟨h1, h2⟩ := hg.2 a (by simp [a.isLt])
  have hz1 : z (esI k r a) = 0 := hz _ (Or.inr (by simp [esI]; have := a.isLt; omega))
  have hz2 : z (eI k r a) = 0 := hz _ (Or.inl (by simp [eI]))
  rw [h1, h2]
  constructor
  · simp only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Matrix.col_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Formalism.FourierDecayAlt.P.Qx3.hpk_col_e]
    split_ifs with h
    · subst h; simp [hz1]
    · simp
  · simp only [herm, bvec, Matrix.mulVec_single_one, dotProduct, Matrix.col_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Formalism.FourierDecayAlt.P.Qx3.hpk_col_es]
    split_ifs with h
    · subst h; simp [hz2]
    · simp

end what₂

section dets

def Arow (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (t : Fin (k + 1)) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.of fun p q =>
    if h : p.val < r then (if q = eI k r ⟨p.val, h⟩ then c ⟨p.val, h⟩ else 0)
    else if h2 : p.val = r then (if q = wI k r t then 1 else 0)
    else if q = J ⟨p.val - r - 1, by have := p.isLt; omega⟩ then 1 else 0

/- English proof (translation)
Establish `e : A = A.updateRow p (l • A p')` using `by rw [← hA, Matrix.updateRow_eq_self]`. Rewrite using `[e, Matrix.det_updateRow_smul, Matrix.det_zero_of_row_eq h (by rw [Matrix.updateRow_self, Matrix.updateRow_ne h.symm]), mul_zero]`.
-/
theorem det_prop {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} {p p' : Fin m} (h : p ≠ p') (l : ℂ) (hA : A p = l • A p') :
    A.det = 0 := by
  have e : A = A.updateRow p (l • A p') := by rw [← hA, Matrix.updateRow_eq_self]
  rw [e, Matrix.det_updateRow_smul,
    Matrix.det_zero_of_row_eq h (by rw [Matrix.updateRow_self, Matrix.updateRow_ne h.symm]), mul_zero]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp)`. Consider the case `insert x s hx ih`.

Rewrite using `[Finset.sum_insert hx, Finset.sum_insert hx, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih]`.
-/
theorem det_updateRow_sum' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (v : ι → Fin m → ℂ) :
    (A.updateRow i (∑ t ∈ s, a t • v t)).det = ∑ t ∈ s, a t * (A.updateRow i (v t)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih]

/- English proof (translation)
Introduce `i j h`. Simplify using `only [colsV, Fin.lt_def] at h ⊢`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem colsV_strictMono (t : Fin (k + 1)) : StrictMono (colsV k r t) := by
  intro i j h
  simp only [colsV, Fin.lt_def] at h ⊢
  split_ifs <;> omega

/- English proof (translation)
Simplify using `only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]`. Use `colsV_strictMono (k := k) (r := r) t` and compare the differences between its conclusion and the goal.
-/
theorem colsV_mem_jSet (t : Fin (k + 1)) : colsV k r t ∈ jSetR k r := by
  classical
  simp only [jSetR, Finset.mem_filter, Finset.mem_univ, true_and]
  convert colsV_strictMono (k := k) (r := r) t

/- English proof (translation)
Set `f : ℕ → ℂ` to `fun i => if h : i < r then c ⟨i, h⟩ else 1`. Establish `h1 : ∏ p : Fin (2 * r + k + 1), (if h : p.val < r then c ⟨p.val, h⟩ else 1) = ∏ i ∈ Finset.range (2 * r + k + 1), f i` using `Fin.prod_univ_eq_prod_range f _`. Establish `h2 : ∏ a : Fin r, c a = ∏ i ∈ Finset.range r, f i`. Rewrite using `[← Fin.prod_univ_eq_prod_range f r]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `[f, a.isLt]`. Rewrite using `[h1, h2, ← Finset.prod_range_mul_prod_Ico f (show r ≤ 2 * r + k + 1 by omega)]`. Rewrite using `[Finset.prod_eq_one (s := Finset.Ico r (2 * r + k + 1)) (fun i hi => by`. Simplify using `only [Finset.mem_Ico] at hi; simp [f, show ¬ i < r by omega]), mul_one]`.
-/
theorem prod_d (c : Fin r → ℂ) :
    ∏ p : Fin (2 * r + k + 1), (if h : p.val < r then c ⟨p.val, h⟩ else 1) = ∏ a : Fin r, c a := by
  let f : ℕ → ℂ := fun i => if h : i < r then c ⟨i, h⟩ else 1
  have h1 : ∏ p : Fin (2 * r + k + 1), (if h : p.val < r then c ⟨p.val, h⟩ else 1) =
      ∏ i ∈ Finset.range (2 * r + k + 1), f i := Fin.prod_univ_eq_prod_range f _
  have h2 : ∏ a : Fin r, c a = ∏ i ∈ Finset.range r, f i := by
    rw [← Fin.prod_univ_eq_prod_range f r]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [f, a.isLt]
  rw [h1, h2, ← Finset.prod_range_mul_prod_Ico f (show r ≤ 2 * r + k + 1 by omega)]
  rw [Finset.prod_eq_one (s := Finset.Ico r (2 * r + k + 1)) (fun i hi => by
    simp only [Finset.mem_Ico] at hi; simp [f, show ¬ i < r by omega]), mul_one]

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [Arow, Matrix.of_apply, Matrix.diagonal_apply, colsV, eI, wI, Fin.ext_iff, Nat.not_lt_zero, if_false]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem arow_zero (c : Fin r → ℂ) (h0 : 0 < k + 1) :
    Arow c (colsV k r ⟨0, h0⟩) ⟨0, h0⟩ = Matrix.diagonal fun p => if h : p.val < r then c ⟨p.val, h⟩ else 1 := by
  ext p q
  simp only [Arow, Matrix.of_apply, Matrix.diagonal_apply, colsV, eI, wI, Fin.ext_iff, Nat.not_lt_zero,
    if_false]
  split_ifs <;> first | rfl | omega

end dets

section dets2

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [Matrix.submatrix_apply, id, Equiv.swap_apply_def]`. Distinguish the cases in `h1 : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))`. Substitute `h1` using the available equality. Simplify using `only [if_true]`.

Simplify using `only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Distinguish the cases in `h2 : p = (⟨r + 1 + t, by omega⟩ : Fin (2 * r + k + 1))`. Substitute `h2` using the available equality. Simplify using `only [if_neg h1, if_true]`.

Simplify using `only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Simplify using `only [if_neg h1, if_neg h2]`. Establish `h1' : p.val ≠ r` using `fun h => h1 (Fin.ext h)`. Establish `h2' : p.val ≠ r + 1 + t` using `fun h => h2 (Fin.ext h)`.

Simplify using `only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem arow_succ (c : Fin r → ℂ) (t : ℕ) (ht : t + 1 < k + 1) :
    Arow c (colsV k r ⟨t + 1, ht⟩) ⟨t + 1, ht⟩ =
      (Arow c (colsV k r ⟨t, by omega⟩) ⟨t, by omega⟩).submatrix
        (Equiv.swap (⟨r, by omega⟩ : Fin (2 * r + k + 1)) ⟨r + 1 + t, by omega⟩) id := by
  ext p q
  simp only [Matrix.submatrix_apply, id, Equiv.swap_apply_def]
  by_cases h1 : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
  · subst h1
    simp only [if_true]
    simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  · by_cases h2 : p = (⟨r + 1 + t, by omega⟩ : Fin (2 * r + k + 1))
    · subst h2
      simp only [if_neg h1, if_true]
      simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    · simp only [if_neg h1, if_neg h2]
      have h1' : p.val ≠ r := fun h => h1 (Fin.ext h)
      have h2' : p.val ≠ r + 1 + t := fun h => h2 (Fin.ext h)
      simp only [Arow, Matrix.of_apply, colsV, wI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

/- English proof (translation)
The claim follows from `| 0, ht => by rw [arow_zero c ht, Matrix.det_diagonal, prod_d, pow_zero, one_mul] | t + 1, ht => by rw [arow_succ c t ht, Matrix.det_permute, Equiv.Perm.sign_swap (by simp only [ne_eq, Fin.ext_iff]; omega), det_arow_colsV c t (by omega), pow_succ] push_cast ring`.
-/
theorem det_arow_colsV (c : Fin r → ℂ) :
    ∀ (t : ℕ) (ht : t < k + 1), (Arow c (colsV k r ⟨t, ht⟩) ⟨t, ht⟩).det = (-1) ^ t * ∏ a, c a
  | 0, ht => by rw [arow_zero c ht, Matrix.det_diagonal, prod_d, pow_zero, one_mul]
  | t + 1, ht => by
    rw [arow_succ c t ht, Matrix.det_permute, Equiv.Perm.sign_swap (by simp only [ne_eq, Fin.ext_iff]; omega),
      det_arow_colsV c t (by omega), pow_succ]
    push_cast
    ring

end dets2

section dets3

/- English proof (translation)
Distinguish the cases in `hA : ∃ j : Fin (r + k), (J j).val < r`. Take `⟨j, hj⟩` from `hA`. Establish `hJj : ∀ h, J ⟨r + 1 + j.val - r - 1, h⟩ = J j` using `fun h => congrArg J (Fin.ext (by show r + 1 + j.val - r - 1 = j.val; omega))`. Use `det_prop (p := ⟨(J j).val, by omega⟩) (p' := ⟨r + 1 + j.val, by omega⟩) (by simp only [ne_eq, Fin.ext_iff]; omega) (c ⟨(J j).val, hj⟩) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`.

Simplify using `only [Arow, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, dif_pos hj, dif_neg (show ¬ (r + 1 + j.val < r) by omega), dif_neg (show ¬ (r + 1 + j.val = r) by omega), hJj]`. Establish `: eI k r ⟨(J j).val, hj⟩ = J j` using `Fin.ext rfl`. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`. Use `push Not at hA`.

Distinguish the cases in `hB : ∃ j, J j = wI k r t`. Take `⟨j, hj⟩` from `hB`. Establish `hJj : ∀ h, J ⟨r + 1 + j.val - r - 1, h⟩ = J j` using `fun h => congrArg J (Fin.ext (by show r + 1 + j.val - r - 1 = j.val; omega))`. Use `Matrix.det_zero_of_row_eq (i := ⟨r, by omega⟩) (j := ⟨r + 1 + j.val, by omega⟩) (by simp only [ne_eq, Fin.ext_iff]; omega) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`.

Simplify using `only [Arow, Matrix.of_apply, dif_neg (show ¬ (r < r) by omega), dif_neg (show ¬ (r + 1 + j.val < r) by omega), dif_neg (show ¬ (r + 1 + j.val = r) by omega), hJj, hj]`. Conclude with `dif_pos trivial`. Use `push Not at hB`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises.

Establish `hsub : Finset.image J Finset.univ ⊆ Finset.image (colsV k r t) Finset.univ`. Introduce `q hq`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hq`. Establish `h1` using `hA j`. Establish `h2 : (J j).val ≠ r + t.val` using `fun h => hB j (Fin.ext (by simp [wI, h]))`.

Establish `hlt` using `(J j).isLt`. Use `Finset.mem_image.2 ⟨⟨if (J j).val < r + t.val then (J j).val - r else (J j).val - r - 1, by` and prove the remaining obligations. Apply the tactic sequence `have := t.isLt; split_ifs <;> omega⟩, Finset.mem_univ _, Fin.ext ?_⟩`. Simplify using `only [colsV]`. Apply the tactic sequence `split_ifs <;> omega`.

Establish `hcard : (Finset.image (colsV k r t) Finset.univ).card ≤ (Finset.image J Finset.univ).card`. Rewrite using `[Finset.card_image_of_injective _ hJ.injective, Finset.card_image_of_injective _ (colsV_strictMono t).injective]`. Establish `heq` using `Finset.eq_of_subset_of_card_le hsub hcard`. Establish `hrange : Set.range J = Set.range (colsV k r t)`. Use `congrArg (fun s : Finset (Fin (2 * r + k + 1)) => (s : Set (Fin (2 * r + k + 1)))) heq` as an intermediate fact.

Simplify `this` using `[Finset.coe_image]`. Conclude with `(hJ.range_inj (colsV_strictMono t)).1 hrange`.
-/
theorem det_arow_ne (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) (t : Fin (k + 1))
    (hne : J ≠ colsV k r t) : (Arow c J t).det = 0 := by
  by_cases hA : ∃ j : Fin (r + k), (J j).val < r
  · obtain ⟨j, hj⟩ := hA
    have hJj : ∀ h, J ⟨r + 1 + j.val - r - 1, h⟩ = J j := fun h => congrArg J (Fin.ext (by show r + 1 + j.val - r - 1 = j.val; omega))
    refine det_prop (p := ⟨(J j).val, by omega⟩) (p' := ⟨r + 1 + j.val, by omega⟩)
      (by simp only [ne_eq, Fin.ext_iff]; omega) (c ⟨(J j).val, hj⟩) ?_
    funext q
    simp only [Arow, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, dif_pos hj,
      dif_neg (show ¬ (r + 1 + j.val < r) by omega), dif_neg (show ¬ (r + 1 + j.val = r) by omega), hJj]
    have : eI k r ⟨(J j).val, hj⟩ = J j := Fin.ext rfl
    rw [this]
    split_ifs <;> simp
  · push Not at hA
    by_cases hB : ∃ j, J j = wI k r t
    · obtain ⟨j, hj⟩ := hB
      have hJj : ∀ h, J ⟨r + 1 + j.val - r - 1, h⟩ = J j := fun h => congrArg J (Fin.ext (by show r + 1 + j.val - r - 1 = j.val; omega))
      refine Matrix.det_zero_of_row_eq (i := ⟨r, by omega⟩) (j := ⟨r + 1 + j.val, by omega⟩)
        (by simp only [ne_eq, Fin.ext_iff]; omega) ?_
      funext q
      simp only [Arow, Matrix.of_apply, dif_neg (show ¬ (r < r) by omega),
        dif_neg (show ¬ (r + 1 + j.val < r) by omega), dif_neg (show ¬ (r + 1 + j.val = r) by omega), hJj, hj]
      exact dif_pos trivial
    · push Not at hB
      exfalso
      apply hne
      have hsub : Finset.image J Finset.univ ⊆ Finset.image (colsV k r t) Finset.univ := by
        intro q hq
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
        have h1 := hA j
        have h2 : (J j).val ≠ r + t.val := fun h => hB j (Fin.ext (by simp [wI, h]))
        have hlt := (J j).isLt
        refine Finset.mem_image.2 ⟨⟨if (J j).val < r + t.val then (J j).val - r else (J j).val - r - 1, by
          have := t.isLt; split_ifs <;> omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        simp only [colsV]
        split_ifs <;> omega
      have hcard : (Finset.image (colsV k r t) Finset.univ).card ≤ (Finset.image J Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hJ.injective,
          Finset.card_image_of_injective _ (colsV_strictMono t).injective]
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      have hrange : Set.range J = Set.range (colsV k r t) := by
        have := congrArg (fun s : Finset (Fin (2 * r + k + 1)) => (s : Set (Fin (2 * r + k + 1)))) heq
        simpa [Finset.coe_image] using this
      exact (hJ.range_inj (colsV_strictMono t)).1 hrange

end dets3

section cell

variable {c : Fin r → ℂ} {g : Q.Mx k r}

/- English proof (translation)
Use extensionality with `p q`. Rewrite using `[Matrix.updateRow_apply]`. Distinguish the cases in `hp : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))`. Rewrite using `[if_pos hp]`. Substitute `hp` using the available equality.

Simplify using `only [Arow, Matrix.of_apply, dif_neg (lt_irrefl r), bvec, Pi.single_apply]`. Rewrite using `[dif_pos trivial]`. Rewrite using `[if_neg hp]`. Establish `hp' : p.val ≠ r` using `fun h => hp (Fin.ext h)`. Simplify using `only [Arow, Matrix.of_apply, dif_neg hp']`.
-/
theorem arow_update (c : Fin r → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (t : Fin (k + 1)) :
    (Arow c J ⟨0, by omega⟩).updateRow ⟨r, by omega⟩ (bvec (wI k r t)) = Arow c J t := by
  ext p q
  rw [Matrix.updateRow_apply]
  by_cases hp : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
  · rw [if_pos hp]
    subst hp
    simp only [Arow, Matrix.of_apply, dif_neg (lt_irrefl r), bvec, Pi.single_apply]
    rw [dif_pos trivial]
  · rw [if_neg hp]
    have hp' : p.val ≠ r := fun h => hp (Fin.ext h)
    simp only [Arow, Matrix.of_apply, dif_neg hp']

/- English proof (translation)
Use function extensionality and compare the values at `q`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hq : r ≤ q.val ∧ q.val ≤ r + k`. Take `⟨t0, rfl⟩ : ∃ t0 : Fin (k + 1), q = wI k r t0` from `⟨⟨q.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩`.

Rewrite using `[Finset.sum_eq_single t0 (fun t _ ht => if_neg (fun h => ht (by`. Simplify using `only [wI, Fin.ext_iff] at h; exact Fin.ext (by omega)))) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]`. Rewrite using `[Finset.sum_eq_zero (fun t _ => if_neg (fun h => hq (by`. Rewrite using `[h]`. Simplify using `only [wI]`.

Use `t.isLt` as an intermediate fact. Use the proof step `omega)))]`. Distinguish the cases in `h1 : q.val < r`. Establish `: q = eI k r ⟨q.val, h1⟩` using `Fin.ext rfl`. Rewrite using `[this]`.

Conclude with `(row_z_e hg hz _).1`. Establish `hq2 : r + k < q.val` using `by omega`. Establish `: q = esI k r ⟨2 * r + k - q.val, by have` using `q.isLt; omega⟩ := Fin.ext (by simp only [esI]; have := q.isLt; omega)`. Rewrite using `[this]`. Conclude with `(row_z_e hg hz _).2`.
-/
theorem yrow_sum (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (fun q => herm (Hpk k r) (g *ᵥ bvec q) z) =
      ∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z • bvec (wI k r t) := by
  funext q
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hq : r ≤ q.val ∧ q.val ≤ r + k
  · obtain ⟨t0, rfl⟩ : ∃ t0 : Fin (k + 1), q = wI k r t0 :=
      ⟨⟨q.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩
    rw [Finset.sum_eq_single t0 (fun t _ ht => if_neg (fun h => ht (by
      simp only [wI, Fin.ext_iff] at h; exact Fin.ext (by omega)))) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  · rw [Finset.sum_eq_zero (fun t _ => if_neg (fun h => hq (by
      rw [h]; simp only [wI]; have := t.isLt; omega)))]
    by_cases h1 : q.val < r
    · have : q = eI k r ⟨q.val, h1⟩ := Fin.ext rfl
      rw [this]; exact (row_z_e hg hz _).1
    · have hq2 : r + k < q.val := by omega
      have : q = esI k r ⟨2 * r + k - q.val, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp only [esI]; have := q.isLt; omega)
      rw [this]; exact (row_z_e hg hz _).2

/- English proof (translation)
Establish `hM : (Matrix.of fun p q => rowV k r z (Q.wCell k r (Fin.last r) c * g) J p q) = (Arow c J ⟨0, by omega⟩).updateRow ⟨r, by omega⟩ (∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z • bvec (wI k r t))`. Rewrite using `[← yrow_sum hg hz]`. Use extensionality with `p q`. Rewrite using `[Matrix.updateRow_apply]`. Distinguish the cases in `hp : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))`.

Rewrite using `[if_pos hp]`. Substitute `hp` using the available equality. Simplify using `only [Matrix.of_apply, rowV, dif_neg (lt_irrefl r)]`. Rewrite using `[dif_pos trivial]`. Conclude with `herm_wCell_last_mul_mulVec_eq_of_inWb hc hz (bvec q)`.

Rewrite using `[if_neg hp]`. Establish `hp' : p.val ≠ r` using `fun h => hp (Fin.ext h)`. Simplify using `only [Matrix.of_apply, rowV, Arow]`. Distinguish the cases in `h1 : p.val < r`. Rewrite using `[dif_pos h1, dif_pos h1, row_e hc hg]`.

Rewrite using `[dif_neg h1, dif_neg h1, dif_neg hp', dif_neg hp']`. Unfold `alJ`. Rewrite using `[hM, det_updateRow_sum' _ _ Finset.univ]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[arow_update]`.
-/
theorem alJ_cell (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    alJ k r z (Q.wCell k r (Fin.last r) c * g) J =
      ∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z * (Arow c J t).det := by
  have hM : (Matrix.of fun p q => rowV k r z (Q.wCell k r (Fin.last r) c * g) J p q) =
      (Arow c J ⟨0, by omega⟩).updateRow ⟨r, by omega⟩
        (∑ t : Fin (k + 1), herm (Hpk k r) (g *ᵥ bvec (wI k r t)) z • bvec (wI k r t)) := by
    rw [← yrow_sum hg hz]
    ext p q
    rw [Matrix.updateRow_apply]
    by_cases hp : p = (⟨r, by omega⟩ : Fin (2 * r + k + 1))
    · rw [if_pos hp]
      subst hp
      simp only [Matrix.of_apply, rowV, dif_neg (lt_irrefl r)]
      rw [dif_pos trivial]
      exact herm_wCell_last_mul_mulVec_eq_of_inWb hc hz (bvec q)
    · rw [if_neg hp]
      have hp' : p.val ≠ r := fun h => hp (Fin.ext h)
      simp only [Matrix.of_apply, rowV, Arow]
      by_cases h1 : p.val < r
      · rw [dif_pos h1, dif_pos h1, row_e hc hg]
      · rw [dif_neg h1, dif_neg h1, dif_neg hp', dif_neg hp']
  unfold alJ
  rw [hM, det_updateRow_sum' _ _ Finset.univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [arow_update]

/- English proof (translation)
Rewrite using `[alJ_cell hc hg hz]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : J = colsV k r s`. Substitute `h` using the available equality. Establish `hd : (Arow c (colsV k r s) s).det = (-1) ^ (s : ℕ) * ∏ a, c a` using `det_arow_colsV c s.val s.isLt`.

Rewrite using `[hd, if_pos rfl, mul_one]`. Rewrite using `[det_arow_ne c J hJ s h, if_neg h, mul_zero, mul_zero]`.
-/
theorem alJ_val (hc : c ∈ OmX r) (hg : g ∈ Q.Glev k r (Fin.last r)) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (J : Fin (r + k) → Fin (2 * r + k + 1)) (hJ : StrictMono J) :
    alJ k r z (Q.wCell k r (Fin.last r) c * g) J =
      ∑ s : Fin (k + 1), (herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * ((-1) ^ (s : ℕ) * ∏ a, c a)) *
        (if J = colsV k r s then 1 else 0) := by
  rw [alJ_cell hc hg hz]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : J = colsV k r s
  · subst h
    have hd : (Arow c (colsV k r s) s).det = (-1) ^ (s : ℕ) * ∏ a, c a := det_arow_colsV c s.val s.isLt
    rw [hd, if_pos rfl, mul_one]
  · rw [det_arow_ne c J hJ s h, if_neg h, mul_zero, mul_zero]

end cell

end RvB

/- English proof (translation)
Introduce `k r`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `E _ _ z z' Y f hz c hc g hg`. Establish `hsm : ∀ J ∈ jSetR k r, StrictMono J` using `fun J hJ => by classical`. Simplify `hJ` using `[jSetR]`.

Establish `hL : rvhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) = ∑ t : Fin (k + 1), ∑ s : Fin (k + 1), (((-1 : ℂ) ^ (t : ℕ) * z' (wI k r t)) * (herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * ((-1) ^ (s : ℕ) * ∏ a, c a))) • qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.las …`. Unfold `rvhatOp`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl fun J hJ => by rw [RvB.alJ_val hc hg hz J (hsm J hJ)]]`. Repeatedly rewrite using `[Finset.mul_sum, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (colsV k r s)]`. Rewrite using `[if_pos rfl, mul_one]`. Introduce `J _ hJ`.

Rewrite using `[if_neg hJ, mul_zero, mul_zero, zero_smul]`. Introduce `h`. Conclude with `absurd (RvB.colsV_mem_jSet s) h`. Establish `hR : NLv k r z z' 0 (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c * g) = ∑ s : Fin (k + 1), ∑ t : Fin (k + 1), (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t)) • qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (F …` using `by show (∑ s : Fin (k + 1), ∑ t : Fin (k + 1), (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z * z' (wI k r t)) • qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c …`. Simplify using `only [RvB.herm_wCell_last_mul_mulVec_eq_of_inWb hc hz]`.

Rewrite using `[hL, hR, Finset.smul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Use `congr 1`. Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mirror_residue_beta_holds : JDRvBeta := by
  intro k r
  refine ⟨1, one_ne_zero, ?_⟩
  intro E _ _ z z' Y f hz c hc g hg
  have hsm : ∀ J ∈ jSetR k r, StrictMono J := fun J hJ => by
    classical
    simpa [jSetR] using hJ
  have hL : rvhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
      ∑ t : Fin (k + 1), ∑ s : Fin (k + 1),
        (((-1 : ℂ) ^ (t : ℕ) * z' (wI k r t)) *
            (herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * ((-1) ^ (s : ℕ) * ∏ a, c a))) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g) := by
    unfold rvhatOp
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl fun J hJ => by rw [RvB.alJ_val hc hg hz J (hsm J hJ)]]
    simp_rw [Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single (colsV k r s)]
    · rw [if_pos rfl, mul_one]
    · intro J _ hJ
      rw [if_neg hJ, mul_zero, mul_zero, zero_smul]
    · intro h
      exact absurd (RvB.colsV_mem_jSet s) h
  have hR : NLv k r z z' 0 (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c * g) =
      ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
        (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g) := by
    show (∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
        (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) *
            herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
          qminorOp (Q.EH k r) (colsV k r s) (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f
            (Q.wCell k r (Fin.last r) c * g)) = _
    simp only [RvB.herm_wCell_last_mul_mulVec_eq_of_inWb hc hz]
  rw [hL, hR, Finset.smul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_smul]
  congr 1
  rw [pow_add]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP
