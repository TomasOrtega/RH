import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseFin

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB PIW.AdelClassFin

attribute [local instance] starRA

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Use `conv_lhs => rw [← Finset.univ_sum_single c]`. Rewrite using `[Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[show (Pi.single k (c k) : p → RA X) = c k • Pi.single k 1 by ext j; simp [Pi.single_apply], Matrix.mulVec_smul]`.
-/
theorem mulVec_cols' {m p : Type*} [Fintype p] [DecidableEq p] (M : Matrix m p (RA X)) (c : p → RA X) :
    M *ᵥ c = ∑ k, c k • (M *ᵥ Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (c k) : p → RA X) = c k • Pi.single k 1 by ext j; simp [Pi.single_apply],
    Matrix.mulVec_smul]

/- English proof (translation)
Rewrite using `[mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem Bf_col (k : Kap X) : Bf X *ᵥ Pi.single k 1 = incl X.B.I (bv X k) := by
  rw [mulVec_single_one]
  rfl

/- English proof (translation)
Rewrite using `[← Bf_col, Matrix.mulVec_mulVec, Bf'_mul_Bf, Matrix.one_mulVec]`.
-/
theorem Bf'_incl (k : Kap X) : Bf' X *ᵥ incl X.B.I (bv X k) = Pi.single k 1 := by
  rw [← Bf_col, Matrix.mulVec_mulVec, Bf'_mul_Bf, Matrix.one_mulVec]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty, Finset.sum_empty]`. Conclude with `DictLat.hhat_zero_right X.B.I x`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ← ih]`. Rewrite using `[show hA X.B.I x (c a • v a + ∑ k ∈ s, c k • v k) = hA X.B.I x (c a • v a) + hA X.B.I x (∑ k ∈ s, c k • v k) from DictLat.hhat_add_right X.B.I _ _ _]`. Rewrite using `[show hA X.B.I x (c a • v a) = c a * hA X.B.I x (v a) from DictLat.hhat_smul_right X.B.I _ _ _]`.
-/
theorem hA_sum' (x : VA X.B.I) (s : Finset (Kap X)) (c : Kap X → RA X) (v : Kap X → VA X.B.I) :
    hA X.B.I x (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k * hA X.B.I x (v k) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact DictLat.hhat_zero_right X.B.I x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rw [show hA X.B.I x (c a • v a + ∑ k ∈ s, c k • v k) =
        hA X.B.I x (c a • v a) + hA X.B.I x (∑ k ∈ s, c k • v k) from DictLat.hhat_add_right X.B.I _ _ _]
    rw [show hA X.B.I x (c a • v a) = c a * hA X.B.I x (v a) from DictLat.hhat_smul_right X.B.I _ _ _]

/- English proof (translation)
The claim follows from `DictLat.hhat_iv X.B.I v w`.
-/
theorem hA_incl (v w : Fin X.B.I.n → X.B.I.E) :
    hA X.B.I (incl X.B.I v) (incl X.B.I w) = ic X (hE X v w) := DictLat.hhat_iv X.B.I v w

/- English proof (translation)
Rewrite using `[mulVec_cols', hA_sum']`. Establish `e : ∀ k, hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ Pi.single k 1) = ic X (JB X (Sum.inl a) k)`. Introduce `k`. Rewrite using `[Bf_col]`. Conclude with `hA_incl X (X.eR a) (bv X k)`.

Simplify using `only [e, JB_e_row]`. Simplify using the standard rewrite rules.
-/
theorem hA_e_Bf (a : Fin D.R.rS) (c : Kap X → RA X) :
    hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ c) = c (Sum.inr (Sum.inr a)) := by
  rw [mulVec_cols', hA_sum']
  have e : ∀ k, hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ Pi.single k 1) = ic X (JB X (Sum.inl a) k) := by
    intro k
    rw [Bf_col]
    exact hA_incl X (X.eR a) (bv X k)
  simp only [e, JB_e_row]
  simp

/- English proof (translation)
Rewrite using `[hA_incl]`. Use `(wb_mem X i a).1` as an intermediate fact. Simplify using `only [bv, Sum.elim_inr, Sum.elim_inl]`. Rewrite using `[this, map_zero]`.
-/
theorem hA_e_w (a : Fin D.R.rS) (i : Fin (mW X)) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (bv X (Sum.inr (Sum.inl i)))) = 0 := by
  rw [hA_incl]
  have := (wb_mem X i a).1
  simp only [bv, Sum.elim_inr, Sum.elim_inl]
  rw [this, map_zero]

/- English proof (translation)
Rewrite using `[hA_incl, hE_ez X u a, map_zero]`.
-/
theorem adelicHermitian_hyperbolicE_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [hA_incl, hE_ez X u a, map_zero]

/- English proof (translation)
Rewrite using `[mulVec_cols']`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k ∈ Sum.inl '' S`. Take `⟨b, hb, rfl⟩` from `hk`. Rewrite using `[Bf_col]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)`. Rewrite using `[hc k hk, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem Bf_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → RA X) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bf X *ᵥ c ∈ Submodule.span (RA X) ((fun b => incl X.B.I (X.eR b)) '' S) := by
  rw [mulVec_cols']
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    rw [Bf_col]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, rfl⟩` from `hx`. Introduce `k hk`. Use `show (Bf' X *ᵥ incl X.B.I (bv X (Sum.inl b))) k = 0`.

Rewrite using `[Bf'_incl, Pi.single_apply, if_neg]`. Introduce and unpack `rfl`. Conclude with `hk ⟨b, hb, rfl⟩`. Consider the case `zero => intro k _`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy => intro k hk`. Rewrite using `[Matrix.mulVec_add, Pi.add_apply, hx k hk, hy k hk, add_zero]`. Consider the case `smul c x _ hx => intro k hk`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, hx k hk, smul_zero]`.
-/
theorem Bf'_mulVec_supp (S : Set (Fin D.R.rS)) {y : VA X.B.I}
    (hy : y ∈ Submodule.span (RA X) ((fun b => incl X.B.I (X.eR b)) '' S)) :
    ∀ k, k ∉ Sum.inl '' S → (Bf' X *ᵥ y) k = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro k hk
    show (Bf' X *ᵥ incl X.B.I (bv X (Sum.inl b))) k = 0
    rw [Bf'_incl, Pi.single_apply, if_neg]
    rintro rfl
    exact hk ⟨b, hb, rfl⟩
  | zero => intro k _; simp
  | add x y _ _ hx hy => intro k hk; rw [Matrix.mulVec_add, Pi.add_apply, hx k hk, hy k hk, add_zero]
  | smul c x _ hx => intro k hk; rw [Matrix.mulVec_smul, Pi.smul_apply, hx k hk, smul_zero]

/- English proof (translation)
Use `set M := Mf X x with hM`. Establish `hg : X.B.I.fmat x - 1 = Bf X * (M - 1) * Bf' X`. Rewrite using `[hM, Mf, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf_mul_Bf']`. Simplify using `only [← Matrix.mul_assoc, Bf_mul_Bf', Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, Bf_mul_Bf', Matrix.mul_one]`.

Establish `hgv : ∀ y, (X.B.I.fmat x - 1) *ᵥ y = Bf X *ᵥ ((M - 1) *ᵥ (Bf' X *ᵥ y))`. Introduce `y`. Rewrite using `[hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Establish `hperp : ∀ y : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) y = 0) → (X.B.I.fmat x - 1) *ᵥ y ∈ Submodule.span (RA X) (Set.range fun b => incl X.B.I (X.eR b))`. Introduce `y hy`.

Use `set c := Bf' X *ᵥ y with hc`. Establish `hyc : y = Bf X *ᵥ c` using `by rw [hc, Matrix.mulVec_mulVec, Bf_mul_Bf', Matrix.one_mulVec]`. Establish `hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0`. Introduce `a`. Use `hA_e_Bf X a c` as an intermediate fact.

Rewrite `this` using `[← hyc, hy a]`. Conclude with `this.symm`. Rewrite using `[hgv, ← hc, ← Set.image_univ]`. Use `Bf_mulVec_mem X Set.univ _ fun k hk => ?_` and prove the remaining obligations. Establish `hk' : ∀ b, k ≠ Sum.inl b`.

Introduce and unpack `b rfl`. Conclude with `hk ⟨b, Set.mem_univ _, rfl⟩`. Rewrite using `[mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hlk` using `lvk_notinl X k hk'`.

Break down `j with b | i | b` into its components or cases. Rewrite using `[hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]`. Rewrite using `[hpat k _ (by rw [lvk_w]; omega), zero_mul]`. Rewrite using `[hcf b, mul_zero]`. Use `show _ ∧ _ ∧ _`.

Use `⟨fun a => ?_, hperp _ fun a => adelicHermitian_hyperbolicE_anisotropic_eq_zero X u a, hperp⟩` and prove the remaining obligations. Rewrite using `[hgv]`. Rewrite using `[show incl X.B.I (X.eR a) = incl X.B.I (bv X (Sum.inl a)) from rfl, Bf'_incl]`. Use `Bf_mulVec_mem X {b | b.1 < a.1} _ fun k hk => ?_` and prove the remaining obligations. Rewrite using `[mulVec_single_one]`.

Use `hpat k _ ?_` and prove the remaining obligations. Break down `k with b | i | b` into its components or cases. Establish `: ¬ b.1 < a.1` using `fun h => hk ⟨b, h, rfl⟩`. Simplify using `only [lvk, Sum.elim_inl]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [lvk, Sum.elim_inl, Sum.elim_inr]`. Use `a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [lvk, Sum.elim_inl, Sum.elim_inr]`. Use `a.2` as an intermediate fact.

Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem nf_of_pat (x : X.B.I.Gf) (hpat : InPat (lvk X) 1 (Mf X x - 1)) : x ∈ X.NfinU u := by
  set M := Mf X x with hM
  have hg : X.B.I.fmat x - 1 = Bf X * (M - 1) * Bf' X := by
    rw [hM, Mf, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf_mul_Bf']
    simp only [← Matrix.mul_assoc, Bf_mul_Bf', Matrix.one_mul]
    rw [Matrix.mul_assoc, Bf_mul_Bf', Matrix.mul_one]
  have hgv : ∀ y, (X.B.I.fmat x - 1) *ᵥ y = Bf X *ᵥ ((M - 1) *ᵥ (Bf' X *ᵥ y)) := by
    intro y
    rw [hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hperp : ∀ y : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) y = 0) →
      (X.B.I.fmat x - 1) *ᵥ y ∈ Submodule.span (RA X) (Set.range fun b => incl X.B.I (X.eR b)) := by
    intro y hy
    set c := Bf' X *ᵥ y with hc
    have hyc : y = Bf X *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, Bf_mul_Bf', Matrix.one_mulVec]
    have hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0 := by
      intro a
      have := hA_e_Bf X a c
      rw [← hyc, hy a] at this
      exact this.symm
    rw [hgv, ← hc, ← Set.image_univ]
    refine Bf_mulVec_mem X Set.univ _ fun k hk => ?_
    have hk' : ∀ b, k ≠ Sum.inl b := by
      rintro b rfl
      exact hk ⟨b, Set.mem_univ _, rfl⟩
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hlk := lvk_notinl X k hk'
    rcases j with b | i | b
    · rw [hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
    · rw [hpat k _ (by rw [lvk_w]; omega), zero_mul]
    · rw [hcf b, mul_zero]
  show _ ∧ _ ∧ _
  refine ⟨fun a => ?_, hperp _ fun a => adelicHermitian_hyperbolicE_anisotropic_eq_zero X u a, hperp⟩
  rw [hgv]
  rw [show incl X.B.I (X.eR a) = incl X.B.I (bv X (Sum.inl a)) from rfl, Bf'_incl]
  refine Bf_mulVec_mem X {b | b.1 < a.1} _ fun k hk => ?_
  rw [mulVec_single_one]
  refine hpat k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

/- English proof (translation)
Introduce `i j hj hij`. Establish `hM : Mf X y - 1 = Bf' X * (X.B.I.fmat y - 1) * Bf X`. Unfold `Mf`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf'_mul_Bf]`. Establish `hcol : (Mf X y - 1) i j = (Bf' X *ᵥ ((X.B.I.fmat y - 1) *ᵥ incl X.B.I (bv X j))) i`.

Rewrite using `[hM, ← Bf_col, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_single_one]`. Both sides reduce to the same expression. Rewrite using `[hcol]`. Break down `j with a | w | a` into its components or cases. Use `Bf'_mulVec_supp X {b | b.1 < a.1} (hy.1 a) i ?_` and prove the remaining obligations.

Introduce and unpack `⟨b, hb, rfl⟩`. Simplify using `only [lvk, Sum.elim_inl, Set.mem_setOf_eq] at hij hb`. Use linear arithmetic over natural numbers and integers. Establish `h` using `hy.2.2 _ fun a => hA_e_w X a w`. Rewrite `h` using `[← Set.image_univ]`.

Use `Bf'_mulVec_supp X Set.univ h i ?_` and prove the remaining obligations. Introduce and unpack `⟨b, -, rfl⟩`. Simplify using `only [lvk, Sum.elim_inl, Sum.elim_inr] at hij`. Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [lvk, Sum.elim_inr] at hj`. Use `a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem half_fin {y : X.B.I.Gf} (hy : y ∈ X.NfinU u) :
    ∀ i j, lvk X j ≤ D.R.rS + 1 → lvk X j < lvk X i + 1 → (Mf X y - 1) i j = 0 := by
  intro i j hj hij
  have hM : Mf X y - 1 = Bf' X * (X.B.I.fmat y - 1) * Bf X := by
    unfold Mf
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf'_mul_Bf]
  have hcol : (Mf X y - 1) i j = (Bf' X *ᵥ ((X.B.I.fmat y - 1) *ᵥ incl X.B.I (bv X j))) i := by
    rw [hM, ← Bf_col, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_single_one]
    rfl
  rw [hcol]
  rcases j with a | w | a
  · refine Bf'_mulVec_supp X {b | b.1 < a.1} (hy.1 a) i ?_
    rintro ⟨b, hb, rfl⟩
    simp only [lvk, Sum.elim_inl, Set.mem_setOf_eq] at hij hb
    omega
  · have h := hy.2.2 _ fun a => hA_e_w X a w
    rw [← Set.image_univ] at h
    refine Bf'_mulVec_supp X Set.univ h i ?_
    rintro ⟨b, -, rfl⟩
    simp only [lvk, Sum.elim_inl, Sum.elim_inr] at hij
    have := b.2
    omega
  · simp only [lvk, Sum.elim_inr] at hj
    have := a.2
    omega

/- English proof (translation)
Establish `hx' : x⁻¹ ∈ X.NfinU u` using `(Formalism.L2.SG.Pf.NfinSub X.eR (X.zR u)).inv_mem hx`. Establish `hMN : Mf X x = sharp (JBf X) (JBf' X) (Mf X x⁻¹)`. Use `Mf_inv X x⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Conclude with `half_to_full (JBf_graded X) (JBf'_graded X) (JBf'_mul X) (h₀ := D.R.rS + 1) (by omega) hMN (half_fin X u hx') (half_fin X u hx)`.
-/
theorem pat_of_nf {x : X.B.I.Gf} (hx : x ∈ X.NfinU u) : InPat (lvk X) 1 (Mf X x - 1) := by
  have hx' : x⁻¹ ∈ X.NfinU u := (Formalism.L2.SG.Pf.NfinSub X.eR (X.zR u)).inv_mem hx
  have hMN : Mf X x = sharp (JBf X) (JBf' X) (Mf X x⁻¹) := by
    have := Mf_inv X x⁻¹
    rwa [inv_inv] at this
  exact half_to_full (JBf_graded X) (JBf'_graded X) (JBf'_mul X) (h₀ := D.R.rS + 1) (by omega) hMN
    (half_fin X u hx') (half_fin X u hx)

/- English proof (translation)
Introduce `_ X u _ hx` and use `pat_of_nf X u hx`.
-/
theorem pattern_of_nilradical : NfPat := fun _ X u _ hx => pat_of_nf X u hx

/- English proof (translation)
Introduce `_ X u x h` and use `nf_of_pat X u x h`.
-/
theorem nilradical_of_pattern : NfOfPat := fun _ X u x h => nf_of_pat X u x h

/- English proof (translation)
Use `set N := 2 * D.R.rS + 2 with hN`. Establish `hZpat : InPat (lvk X) 1 (icay N (Mf X x))` using `inPat_mul hT (inPat_geo (inPat_neg (inPat_smul _ hT)) N)`. Establish `hP : sharp (JBf X) (JBf' X) (Mf X x) = Mf X x⁻¹` using `(Mf_inv X x).symm`. Establish `hPM : Mf X x⁻¹ * Mf X x = 1` using `by rw [← Mf_mul, inv_mul_cancel, Mf_one]`. Establish `hT' : InPat (lvk X) 1 (Mf X x⁻¹ - 1)`.

Establish `e : Mf X x⁻¹ - 1 = sharp (JBf X) (JBf' X) (Mf X x - 1)`. Rewrite using `[sharp_sub, hP, sharp_one (JBf'_mul X)]`. Rewrite using `[e]`. Conclude with `inPat_sharp (JBf_graded X) (JBf'_graded X) hT`. Establish `hs` using `icay_skew (JBf_mul X) (JBf'_mul X) hP hPM (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hT' _)`.

Use `⟨icay N (Mf X x), hZpat, ?_, cay_icay (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hZpat _)⟩` and prove the remaining obligations. Rewrite using `[cT_eqR]`. Combine the equalities or inequalities in the displayed calculation. Unfold `sharp`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, JBf_mul, Matrix.one_mul]`.

Use `_ = -(JBf X * icay N (Mf X x)) := by rw [hs, Matrix.mul_neg]`.
-/
theorem cay_inv_R (x : X.B.I.Gf) (hT : InPat (lvk X) 1 (Mf X x - 1)) :
    ∃ Z : Matrix (Kap X) (Kap X) (RA X), InPat (lvk X) 1 Z ∧
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) ∧
        cay (2 * D.R.rS + 2) Z = Mf X x := by
  set N := 2 * D.R.rS + 2 with hN
  have hZpat : InPat (lvk X) 1 (icay N (Mf X x)) :=
    inPat_mul hT (inPat_geo (inPat_neg (inPat_smul _ hT)) N)
  have hP : sharp (JBf X) (JBf' X) (Mf X x) = Mf X x⁻¹ := (Mf_inv X x).symm
  have hPM : Mf X x⁻¹ * Mf X x = 1 := by rw [← Mf_mul, inv_mul_cancel, Mf_one]
  have hT' : InPat (lvk X) 1 (Mf X x⁻¹ - 1) := by
    have e : Mf X x⁻¹ - 1 = sharp (JBf X) (JBf' X) (Mf X x - 1) := by
      rw [sharp_sub, hP, sharp_one (JBf'_mul X)]
    rw [e]
    exact inPat_sharp (JBf_graded X) (JBf'_graded X) hT
  have hs := icay_skew (JBf_mul X) (JBf'_mul X) hP hPM (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hT' _)
  refine ⟨icay N (Mf X x), hZpat, ?_, cay_icay (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hZpat _)⟩
  rw [cT_eqR]
  calc (icay N (Mf X x))ᴴ * JBf X = JBf X * sharp (JBf X) (JBf' X) (icay N (Mf X x)) := by
        unfold sharp
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, JBf_mul, Matrix.one_mul]
    _ = -(JBf X * icay N (Mf X x)) := by rw [hs, Matrix.mul_neg]

/- English proof (translation)
Introduce `_ X x h` and use `cay_inv_R X x h`.
-/
theorem cayley_inverse_right : CayInvR := fun _ X x h => cay_inv_R X x h

end Formalism.L2.SG.Pf.SlabNDensePf
