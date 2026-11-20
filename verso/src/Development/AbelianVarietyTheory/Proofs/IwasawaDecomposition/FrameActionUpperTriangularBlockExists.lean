import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ProperlyDiscontinuousFlags
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteOfLocallyFinite
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PropDiscOfFlagDomainData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMulUpperTriangular

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.BlockTransporter

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular`. Consider the case `exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular`. Consider the case `(apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular ..)`.
-/
theorem exists_unitary_mul_upper {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ t : Matrix (Fin n) (Fin n) ℂ, t.BlockTriangular id ∧ y = u * t := by
  first
  | exact @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | (apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular ..)

/- English proof (translation)
Take `⟨u, hu, t, ht, e⟩` from `exists_unitary_mul_upper B`. Establish `hud : u.det ≠ 0`. Introduce `h`. Use `congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)` as an intermediate fact. Rewrite `this` using `[det_mul, h, mul_zero, det_one]`.

Conclude with `zero_ne_one this`. Establish `htd : t.det ≠ 0`. Introduce `h`. Rewrite `hB` using `[e, det_mul, h, mul_zero]`. Conclude with `hB rfl`.

Use `letI := invertibleOfIsUnitDet t htd.isUnit`. Establish `hti : (t⁻¹).BlockTriangular id` using `blockTriangular_inv_of_blockTriangular ht`. Establish `hu' : u = B * t⁻¹` using `by rw [e, Matrix.mul_nonsing_inv_cancel_right _ _ htd.isUnit]`. Use `⟨u, t, hu, fun a c hc ha => ?_, htd, fun a c h => ht h, e⟩` and prove the remaining obligations. Rewrite using `[hu', mul_apply]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k ≤ c`. Rewrite using `[h0 a k (lt_of_le_of_lt (Fin.le_def.1 hk) hc) ha, zero_mul]`. Rewrite using `[hti (not_le.1 hk), mul_zero]`.
-/
theorem exists_unitary_block {r p : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.det ≠ 0)
    (h0 : ∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → B a c = 0) :
    ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ B = u * t := by
  obtain ⟨u, hu, t, ht, e⟩ := exists_unitary_mul_upper B
  have hud : u.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have htd : t.det ≠ 0 := by
    intro h; rw [e, det_mul, h, mul_zero] at hB; exact hB rfl
  letI := invertibleOfIsUnitDet t htd.isUnit
  have hti : (t⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  have hu' : u = B * t⁻¹ := by rw [e, Matrix.mul_nonsing_inv_cancel_right _ _ htd.isUnit]
  refine ⟨u, t, hu, fun a c hc ha => ?_, htd, fun a c h => ht h, e⟩
  rw [hu', mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ≤ c
  · rw [h0 a k (lt_of_le_of_lt (Fin.le_def.1 hk) hc) ha, zero_mul]
  · rw [hti (not_le.1 hk), mul_zero]

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def unitBlock (X : Data E r) : Set (Frame X.Ψ r) :=
  {u | ∀ τ, mat u τ ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
    ∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}

/- English proof (translation)
Use `Metric.isCompact_of_isClosed_isBounded ?_ ?_` and prove the remaining obligations. Establish `: unitBlock X = ⋂ τ, ({u : Frame X.Ψ r | star (mat u τ) * mat u τ = 1} ∩ ⋂ a : Fin r, ⋂ c : Fin r, {u | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0})`. Use extensionality with `u`. Simplify using `only [unitBlock, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]`. Simplify using `only [Matrix.mem_unitaryGroup_iff']`.

Rewrite using `[this]`. Use `isClosed_iInter fun τ => IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun c => ?_)` and prove the remaining obligations. Establish `hc : Continuous fun u : Frame X.Ψ r => mat u τ` using `continuous_apply τ`. Conclude with `isClosed_eq (hc.star.matrix_mul hc) continuous_const`. Distinguish the cases in `h : (c : ℕ) < X.p0 ∧ ¬ (a : ℕ) < X.p0`.

Establish `: {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = {u | u τ a c = 0}`. Use extensionality with `u`. Simplify using `only [Set.mem_setOf_eq]`. Conclude with `⟨fun hu => hu h.1 h.2, fun hu _ _ => hu⟩`. Rewrite using `[this]`.

Conclude with `isClosed_eq ((continuous_apply c).comp ((continuous_apply a).comp (continuous_apply τ))) continuous_const`. Establish `: {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = Set.univ`. Use extensionality with `u`. Simplify using `only [Set.mem_setOf_eq, Set.mem_univ, iff_true]`. Introduce `h1 h2`.

Conclude with `absurd ⟨h1, h2⟩ h`. Rewrite using `[this]`. Conclude with `isClosed_univ`. Use `(Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`.

Use `pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun τ => ?_` and prove the remaining obligations. Use `pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun a => ?_` and prove the remaining obligations. Use `pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun c => ?_` and prove the remaining obligations. Conclude with `entry_norm_bound_of_unitary (hu τ).1 a c`.
-/
theorem isCompact_unitBlock (X : Data E r) : IsCompact (unitBlock X) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : unitBlock X = ⋂ τ, ({u : Frame X.Ψ r | star (mat u τ) * mat u τ = 1} ∩
        ⋂ a : Fin r, ⋂ c : Fin r, {u | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}) := by
      ext u
      simp only [unitBlock, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      simp only [Matrix.mem_unitaryGroup_iff']
    rw [this]
    refine isClosed_iInter fun τ => IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun c => ?_)
    · have hc : Continuous fun u : Frame X.Ψ r => mat u τ := continuous_apply τ
      exact isClosed_eq (hc.star.matrix_mul hc) continuous_const
    · by_cases h : (c : ℕ) < X.p0 ∧ ¬ (a : ℕ) < X.p0
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = {u | u τ a c = 0} := by
          ext u; simp only [Set.mem_setOf_eq]; exact ⟨fun hu => hu h.1 h.2, fun hu _ _ => hu⟩
        rw [this]
        exact isClosed_eq ((continuous_apply c).comp ((continuous_apply a).comp (continuous_apply τ)))
          continuous_const
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = Set.univ := by
          ext u; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro h1 h2; exact absurd ⟨h1, h2⟩ h
        rw [this]; exact isClosed_univ
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun τ => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun a => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun c => ?_
    exact entry_norm_bound_of_unitary (hu τ).1 a c

/- English proof (translation)
Use `continuous_pi fun τ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.1 τ` using `(continuous_apply τ).comp continuous_fst`. Establish `h2 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.2 τ` using `(continuous_apply τ).comp continuous_snd`. Conclude with `h1.matrix_mul h2`.
-/
theorem continuous_rmul (X : Data E r) : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have h1 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.1 τ := (continuous_apply τ).comp continuous_fst
  have h2 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.2 τ := (continuous_apply τ).comp continuous_snd
  exact h1.matrix_mul h2

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

/- English proof (translation)
Introduce `E _ _ _ r X K hK hKd`. Use `set K' := (fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2) '' (K ×ˢ unitBlock X) with hK'`. Establish `hK'c : IsCompact K'` using `(hK.prod (isCompact_unitBlock X)).image (continuous_rmul X)`. Establish `hK'd : K' ⊆ X.dom`. Introduce and unpack `_ ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩`.

Use `GlobalTheory.PointOfFrames.rmul_mem_dom X (hKd hy) u (fun τ h => ?_) (fun τ => (hu τ).2)` and prove the remaining obligations. Use `congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 (hu τ).1)` as an intermediate fact. Rewrite `this` using `[det_mul, h, mul_zero, det_one]`. Conclude with `zero_ne_one this`. Establish `hfin` using `GlobalTheory.PropDiscCompare.compact_of_local X (GlobalTheory.propDisc_of_flagDomainData E r X) (K ∪ K') (hK.union hK'c) (Set.union_subset hKd hK'd)`.

Use `hfin.subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨hγ, x, hx, y, hy, b, hb, h0, e⟩`. Establish `key : ∀ τ : X.Ψ, ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧ (∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u a c = 0) ∧ t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ mat b τ = u * t` using `fun τ => exists_unitary_block (mat b τ) (hb τ) (h0 τ)`. Use `choose u t hu hu0 htd ht hbut using key`. Use `⟨hγ, x, Or.inl hx, rmul y (fun τ => u τ), Or.inr ⟨(y, fun τ => u τ), ⟨hy, fun τ => ⟨hu τ, hu0 τ⟩⟩, rfl⟩, fun τ => t τ, fun τ => ⟨htd τ, ht τ⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[e]`. Use function extensionality and compare the values at `τ`. Use `show mat y τ * mat b τ = (mat y τ * u τ) * t τ`. Rewrite using `[Matrix.mul_assoc, ← hbut τ]`.
-/
theorem finite_blockTransporter : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (K : Set (ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), IsCompact K → K ⊆ X.dom →
    {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
      (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
      (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
      ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b}.Finite := by
  intro E _ _ _ r X K hK hKd
  set K' := (fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2) '' (K ×ˢ unitBlock X) with hK'
  have hK'c : IsCompact K' := (hK.prod (isCompact_unitBlock X)).image (continuous_rmul X)
  have hK'd : K' ⊆ X.dom := by
    rintro _ ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
    refine GlobalTheory.PointOfFrames.rmul_mem_dom X (hKd hy) u (fun τ h => ?_) (fun τ => (hu τ).2)
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 (hu τ).1)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hfin := GlobalTheory.PropDiscCompare.compact_of_local X (GlobalTheory.propDisc_of_flagDomainData E r X) (K ∪ K')
    (hK.union hK'c) (Set.union_subset hKd hK'd)
  refine hfin.subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, h0, e⟩
  have key : ∀ τ : X.Ψ, ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ mat b τ = u * t :=
    fun τ => exists_unitary_block (mat b τ) (hb τ) (h0 τ)
  choose u t hu hu0 htd ht hbut using key
  refine ⟨hγ, x, Or.inl hx, rmul y (fun τ => u τ), Or.inr ⟨(y, fun τ => u τ), ⟨hy, fun τ => ⟨hu τ, hu0 τ⟩⟩, rfl⟩,
    fun τ => t τ, fun τ => ⟨htd τ, ht τ⟩, ?_⟩
  rw [e]
  funext τ
  show mat y τ * mat b τ = (mat y τ * u τ) * t τ
  rw [Matrix.mul_assoc, ← hbut τ]

end GlobalTheory.BlockTransporter
