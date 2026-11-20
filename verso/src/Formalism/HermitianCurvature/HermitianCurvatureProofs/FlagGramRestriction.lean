import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace FlagGramRestriction

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts

variable {k r : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[gnB, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
lemma col_mul (M : B.Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (M * gnB k r z z' γ) a j) = M *ᵥ gramVec k r z z' γ j := by
  funext a; simp [gnB, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[gnB, Matrix.mul_apply, Finset.sum_apply, mul_comm]`.
-/
lemma col_V_mul (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (Φ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (gnB k r z z' γ * Φ) a j) = ∑ i, Φ i j • gramVec k r z z' γ i := by
  funext a; simp [gnB, Matrix.mul_apply, Finset.sum_apply, mul_comm]

/- English proof (translation)
Use extensionality with `a j`. Conclude with `congrFun (h j) a`.
-/
lemma mat_ext_col {n : ℕ} {ι : Type*} (A B : Matrix (Fin n) ι ℂ) (h : ∀ j, (fun a => A a j) = fun a => B a j) :
    A = B := by
  ext a j; exact congrFun (h j) a

def PhiH (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ h : B.Mat k r) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks (C2.uMap k r z h) 0 0 (C2.uMap k r z' (γ⁻¹ * h * γ))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hs, s', hs', rfl⟩`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Establish `: γ⁻¹ * (γ * s' * γ⁻¹) * γ = s'`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ hγ, Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one]`. Rewrite using `[this]`. Conclude with `hs'`. Introduce and unpack `⟨hs, hs'⟩`. Use `⟨hs, _, hs', ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv _ hγ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hγ]`.
-/
lemma Hst_iff {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : IsUnit γ.det) (h : B.Mat k r) :
    h ∈ C2.Hst k r z z' γ ↔ h ∈ Sset k r z ∧ γ⁻¹ * h * γ ∈ Sset k r z' := by
  constructor
  · rintro ⟨hs, s', hs', rfl⟩
    refine ⟨hs, ?_⟩
    have : γ⁻¹ * (γ * s' * γ⁻¹) * γ = s' := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hγ, Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one]
    rw [this]; exact hs'
  · rintro ⟨hs, hs'⟩
    refine ⟨hs, _, hs', ?_⟩
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hγ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hγ]

/- English proof (translation)
Establish `hU` using `(unipotent_map_frame k r z hstd.2.1).1 h hs`. Establish `hU'` using `(unipotent_map_frame k r z' hstd.2.2).1 _ hs'`. Apply `mat_ext_col` to reduce the goal to its premises. Introduce `j`. Rewrite using `[col_mul, col_V_mul, Fintype.sum_sum_type]`.

Consider the cases of `j with`. Consider the case `inl b`. Simplify using `only [PhiH, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]`. Conclude with `hU.1 b`. Consider the case `inr b`.

Simplify using `only [PhiH, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]`. Use `show h *ᵥ (γ *ᵥ fvec k r z' b) = ∑ c, C2.uMap k r z' (γ⁻¹ * h * γ) c b • (γ *ᵥ fvec k r z' c)`. Establish `e : h * γ = γ * (γ⁻¹ * h * γ)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hγ]`.

Rewrite using `[Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hU'.1 b, Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul]`.
-/
lemma mulV {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r} (hγ : IsUnit γ.det)
    {h : B.Mat k r} (hs : h ∈ Sset k r z) (hs' : γ⁻¹ * h * γ ∈ Sset k r z') :
    h * gnB k r z z' γ = gnB k r z z' γ * PhiH k r z z' γ h := by
  have hU := (unipotent_map_frame k r z hstd.2.1).1 h hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  apply mat_ext_col
  intro j
  rw [col_mul, col_V_mul, Fintype.sum_sum_type]
  cases j with
  | inl b =>
    simp only [PhiH, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    exact hU.1 b
  | inr b =>
    simp only [PhiH, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, zero_add]
    show h *ᵥ (γ *ᵥ fvec k r z' b) = ∑ c, C2.uMap k r z' (γ⁻¹ * h * γ) c b • (γ *ᵥ fvec k r z' c)
    have e : h * γ = γ * (γ⁻¹ * h * γ) := by
      simp only [Matrix.mul_assoc]; rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hU'.1 b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]

/- English proof (translation)
Establish `hU` using `(unipotent_map_frame k r z hstd.2.1).1 h hs`. Establish `hU'` using `(unipotent_map_frame k r z' hstd.2.2).1 _ hs'`. Unfold `PhiH`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁]`. Conclude with `(C2x2.ut_unit hU.2.1).mul (C2x2.ut_unit hU'.2.1)`.
-/
lemma Phi_unit {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ h : B.Mat k r}
    (hs : h ∈ Sset k r z) (hs' : γ⁻¹ * h * γ ∈ Sset k r z') : IsUnit (PhiH k r z z' γ h).det := by
  have hU := (unipotent_map_frame k r z hstd.2.1).1 h hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  unfold PhiH
  rw [Matrix.det_fromBlocks_zero₂₁]
  exact (C2x2.ut_unit hU.2.1).mul (C2x2.ut_unit hU'.2.1)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (g * V)ᴴ * H * (g * V) := by rw [hgV]`. Use `_ = Vᴴ * (gᴴ * H * g) * V := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]`.

Use `_ = Vᴴ * H * V := by rw [hg]`.
-/
lemma Phi_gram {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] (H : Matrix n n ℂ)
    (V : Matrix n ι ℂ) (g : Matrix n n ℂ) (Φ : Matrix ι ι ℂ) (hg : gᴴ * H * g = H) (hgV : g * V = V * Φ) :
    Φᴴ * (Vᴴ * H * V) * Φ = Vᴴ * H * V := by
  calc Φᴴ * (Vᴴ * H * V) * Φ = (V * Φ)ᴴ * H * (V * Φ) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (g * V)ᴴ * H * (g * V) := by rw [hgV]
    _ = Vᴴ * (gᴴ * H * g) * V := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * H * V := by rw [hg]

/- English proof (translation)
Apply `mat_ext_col` to reduce the goal to its premises. Introduce `j`. Rewrite using `[col_mul, hκ.2 j]`. Use function extensionality and compare the values at `a`. Simplify using `[gnB]`.
-/
lemma KU_V {z z' : Fin (2 * r + k + 1) → ℂ} {γ κ : B.Mat k r} (hκ : κ ∈ C2.KU k r z z' γ) :
    κ * gnB k r z z' γ = gnB k r z z' γ := by
  apply mat_ext_col; intro j
  rw [col_mul, hκ.2 j]
  funext a; simp [gnB]

/- English proof (translation)
Establish `e : (∑ c, u c b • fvec k r z c) - fvec k r z b = ∑ c, (u c b - if c = b then 1 else 0) • fvec k r z c`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[e]`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `c _`.

Distinguish the cases in `hcb : c < b`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨⟨c, hcb⟩, rfl⟩`. Establish `h0 : u c b - (if c = b then 1 else 0) = 0`.

Break down `lt_or_eq_of_le (not_lt.mp hcb) with h | h` into its components or cases. Rewrite using `[hu.1 c b h, if_neg (ne_of_gt h), sub_self]`. Substitute `h` using the available equality. Rewrite using `[hu.2, if_pos rfl, sub_self]`. Rewrite using `[h0, zero_smul]`.

Conclude with `Submodule.zero_mem _`.
-/
lemma flag_mem (z : Fin (2 * r + k + 1) → ℂ) (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hu : u ∈ C2.UTset (r + 1))
    (b : Fin (r + 1)) : (∑ c, u c b • fvec k r z c) - fvec k r z b ∈ C2.flagSpan k r z b := by
  have e : (∑ c, u c b • fvec k r z c) - fvec k r z b =
      ∑ c, (u c b - if c = b then 1 else 0) • fvec k r z c := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e]
  apply Submodule.sum_mem
  intro c _
  by_cases hcb : c < b
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨c, hcb⟩, rfl⟩
  · have h0 : u c b - (if c = b then 1 else 0) = 0 := by
      rcases lt_or_eq_of_le (not_lt.mp hcb) with h | h
      · rw [hu.1 c b h, if_neg (ne_of_gt h), sub_self]
      · subst h; rw [hu.2, if_pos rfl, sub_self]
    rw [h0, zero_smul]; exact Submodule.zero_mem _

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma cancel_left {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ) (hA : IsUnit A.det)
    (h : A * X = A * Y) : X = Y := by
  calc X = A⁻¹ * (A * X) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    _ = A⁻¹ * (A * Y) := by rw [h]
    _ = Y := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma cancel_right {m : Type*} [Fintype m] [DecidableEq m] (A X Y : Matrix m m ℂ) (hA : IsUnit A.det)
    (h : X * A = Y * A) : X = Y := by
  calc X = X * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
    _ = Y * A * A⁻¹ := by rw [h]
    _ = Y := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]

/- English proof (translation)
Establish `hγ : IsUnit γ.det` using `WeylGroupFacts.isUnit_of_uh hpos.1`. Take `⟨hs, hs'⟩` from `(Hst_iff hγ ρ).mp hρ.1`. Apply `eq_rhoOf _ _ _ (gram_det z z' γ hstd hpos) ρ (mulV hstd hγ hs hs')` to reduce the goal to its premises. Introduce `x hx`. Conclude with `hρ.2 x ((mem_Uperp z z' γ x).mpr hx)`.
-/
lemma Rst_rho {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r}
    (hpos : C2.PosPt k r z z' γ) {ρ : B.Mat k r} (hρ : ρ ∈ C2.Rst k r z z' γ) :
    ρ = rhoOf (Hpk k r) (gnB k r z z' γ) (PhiH k r z z' γ ρ) := by
  have hγ : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hpos.1
  obtain ⟨hs, hs'⟩ := (Hst_iff hγ ρ).mp hρ.1
  apply eq_rhoOf _ _ _ (gram_det z z' γ hstd hpos) ρ (mulV hstd hγ hs hs')
  intro x hx
  exact hρ.2 x ((mem_Uperp z z' γ x).mpr hx)

/- English proof (translation)
Establish `hγ : IsUnit γ.det` using `WeylGroupFacts.isUnit_of_uh hpos.1`. Take `⟨hs, hs'⟩` from `(Hst_iff hγ ρ).mp hρ.1`. Establish `hU` using `(unipotent_map_frame k r z hstd.2.1).1 ρ hs`. Establish `hU'` using `(unipotent_map_frame k r z' hstd.2.2).1 _ hs'`. Establish `e` using `Rst_rho hstd hpos hρ`.

Establish `hΦ : (PhiH k r z z' γ ρ - 1) ^ (r + 1) = 0`. Unfold `PhiH`. Establish `e1 : Matrix.fromBlocks (C2.uMap k r z ρ) 0 0 (C2.uMap k r z' (γ⁻¹ * ρ * γ)) - 1 = Matrix.fromBlocks (C2.uMap k r z ρ - 1) 0 0 (C2.uMap k r z' (γ⁻¹ * ρ * γ) - 1)`. Rewrite using `[← Matrix.fromBlocks_one]`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.one_apply]`.

Rewrite using `[e1, blk_pow, ut_sub_pow hU.2.1, ut_sub_pow hU'.2.1, Matrix.fromBlocks_zero]`. Rewrite using `[e, rhoOf_sub_one_pow _ _ _ (gram_det z z' γ hstd hpos), HermitianProjections.pow_eq_zero_of_le hΦ (by omega), Matrix.mul_zero, Matrix.zero_mul]`.
-/
lemma Rst_unip {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r}
    (hpos : C2.PosPt k r z z' γ) {ρ : B.Mat k r} (hρ : ρ ∈ C2.Rst k r z z' γ) :
    (ρ - 1) ^ (2 * r + k + 1) = 0 := by
  have hγ : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hpos.1
  obtain ⟨hs, hs'⟩ := (Hst_iff hγ ρ).mp hρ.1
  have hU := (unipotent_map_frame k r z hstd.2.1).1 ρ hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  have e := Rst_rho hstd hpos hρ
  have hΦ : (PhiH k r z z' γ ρ - 1) ^ (r + 1) = 0 := by
    unfold PhiH
    have e1 : Matrix.fromBlocks (C2.uMap k r z ρ) 0 0 (C2.uMap k r z' (γ⁻¹ * ρ * γ)) - 1 =
        Matrix.fromBlocks (C2.uMap k r z ρ - 1) 0 0 (C2.uMap k r z' (γ⁻¹ * ρ * γ) - 1) := by
      rw [← Matrix.fromBlocks_one]
      ext (i | i) (j | j) <;> simp [Matrix.one_apply]
    rw [e1, blk_pow, ut_sub_pow hU.2.1, ut_sub_pow hU'.2.1, Matrix.fromBlocks_zero]
  rw [e, rhoOf_sub_one_pow _ _ _ (gram_det z z' γ hstd hpos),
    HermitianProjections.pow_eq_zero_of_le hΦ (by omega), Matrix.mul_zero, Matrix.zero_mul]

end FlagGramRestriction

end Formalism.FourierDecayAlt.P
