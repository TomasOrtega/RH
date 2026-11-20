import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section InvL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Use `⟨-(ContinuousLinearMap.mulLeftRight ℂ (Matrix (Fin n) (Fin n) ℂ) (↑hx.unit⁻¹) (↑hx.unit⁻¹)), ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hasFDerivAt_ringInverse (𝕜 := ℂ) hx.unit`. Rewrite `h` using `[hx.unit_spec]`. Establish `e : (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) = Ring.inverse`. Use function extensionality and compare the values at `Matrix.nonsing_inv_eq_ringInverse`.

Rewrite using `[e]`. Conclude with `h`. Introduce `h`. Simplify using `only [Matrix.coe_units_inv, hx.unit_spec]`. Conclude with `congrArg Neg.neg (ContinuousLinearMap.mulLeftRight_apply ℂ (Matrix (Fin n) (Fin n) ℂ) x⁻¹ x⁻¹ h)`.
-/
lemma tb_inv_hasFDerivAt {x : Matrix (Fin n) (Fin n) ℂ} (hx : IsUnit x) :
    ∃ L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ,
      HasFDerivAt (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) L x ∧ ∀ h, L h = -(x⁻¹ * h * x⁻¹) := by
  refine ⟨-(ContinuousLinearMap.mulLeftRight ℂ (Matrix (Fin n) (Fin n) ℂ) (↑hx.unit⁻¹) (↑hx.unit⁻¹)),
    ?_, ?_⟩
  · have h := hasFDerivAt_ringInverse (𝕜 := ℂ) hx.unit
    rw [hx.unit_spec] at h
    have e : (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) = Ring.inverse :=
      funext Matrix.nonsing_inv_eq_ringInverse
    rw [e]
    exact h
  · intro h
    simp only [Matrix.coe_units_inv, hx.unit_spec]
    exact congrArg Neg.neg (ContinuousLinearMap.mulLeftRight_apply ℂ (Matrix (Fin n) (Fin n) ℂ) x⁻¹ x⁻¹ h)

end InvL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ m`. Establish `h` using `hy (Fin.last m)`.

Simplify using `only [lead, Fin.val_last, le_refl, dif_pos] at h`. Establish `e : y.submatrix (Fin.castLE (le_refl (m + 1))) (Fin.castLE (le_refl (m + 1))) = y`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite `h` using `[e]`.

Conclude with `isUnit_iff_ne_zero.mpr h`.
-/
lemma tb_isUnit_of_omega {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ OmegaSet n) : IsUnit y := by
  rw [Matrix.isUnit_iff_isUnit_det]
  cases n with
  | zero => simp
  | succ m =>
    have h := hy (Fin.last m)
    simp only [lead, Fin.val_last, le_refl, dif_pos] at h
    have e : y.submatrix (Fin.castLE (le_refl (m + 1))) (Fin.castLE (le_refl (m + 1))) = y := by
      ext a b; rfl
    rw [e] at h
    exact isUnit_iff_ne_zero.mpr h

/- English proof (translation)
The claim follows from `Matrix.isUnit_nonsing_inv_iff.mp (tb_isUnit_of_omega hx)`.
-/
lemma tb_isUnit_of_omegaP {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ OmegaP n) : IsUnit x := Matrix.isUnit_nonsing_inv_iff.mp (tb_isUnit_of_omega hx)

/- English proof (translation)
The claim follows from `contDiff_apply_apply ℂ ℂ a b`.
-/
lemma tb_contDiff_entry (a b : Fin n) : ContDiff ℂ ω (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := contDiff_apply_apply ℂ ℂ a b

/- English proof (translation)
Unfold `lead`. Distinguish the cases in `h : i ≤ n`. Simplify using `only [dif_pos h]`. Repeatedly rewrite using `[det_apply']`. Use `ContDiff.sum fun σ _ => ?_` and prove the remaining obligations.

Use `contDiff_const.mul ?_` and prove the remaining obligations. Apply the tactic sequence `exact contDiff_prod fun j _ => tb_contDiff_entry _ _`. Simplify using `only [dif_neg h]`. Conclude with `contDiff_const`.
-/
lemma tb_contDiff_lead (i : ℕ) : ContDiff ℂ ω (lead (n := n) i) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [dif_pos h]
    simp_rw [det_apply']
    refine ContDiff.sum fun σ _ => ?_
    refine contDiff_const.mul ?_
    exact contDiff_prod fun j _ => tb_contDiff_entry _ _
  · simp only [dif_neg h]
    exact contDiff_const

/- English proof (translation)
Break down `m with k | k` into its components or cases. Simplify using `using hf.pow k`. Establish `h1` using `(hf.pow (k + 1)).inv (fun x hx => pow_ne_zero _ (h0 x hx))`. Use `h1.congr fun x _ => ?_` and prove the remaining obligations. Simplify using `[zpow_negSucc]`.
-/
lemma tb_contDiffOn_zpow {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {s : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiffOn ℂ ω f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) :
    ContDiffOn ℂ ω (fun x => f x ^ m) s := by
  rcases m with k | k
  · simpa using hf.pow k
  · have h1 := (hf.pow (k + 1)).inv (fun x hx => pow_ne_zero _ (h0 x hx))
    refine h1.congr fun x _ => ?_
    simp [zpow_negSucc]

/- English proof (translation)
Use `show ContDiffOn ℂ ω (fun z => ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))) (OmegaSet n)`. Conclude with `contDiffOn_prod fun i _ => tb_contDiffOn_zpow (tb_contDiff_lead _).contDiffOn (fun x (hx : x ∈ OmegaSet n) => hx i) _`.
-/
lemma tb_contDiffOn_phiM (μ : Fin n → ℤ) : ContDiffOn ℂ ω (PhiM μ) (OmegaSet n) := by
  show ContDiffOn ℂ ω (fun z => ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))) (OmegaSet n)
  exact contDiffOn_prod fun i _ =>
    tb_contDiffOn_zpow (tb_contDiff_lead _).contDiffOn (fun x (hx : x ∈ OmegaSet n) => hx i) _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hl : ContDiff ℂ ω (fun z : Matrix (Fin n) (Fin n) ℂ => Z * z)` using `(LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Z)).contDiff`. Conclude with `(hF.fderiv_of_isOpen hs le_top).clm_apply hl.contDiffOn`.
-/
lemma tb_contDiffOn_lhol {F : Matrix (Fin n) (Fin n) ℂ → E} {s : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hs : IsOpen s) (hF : ContDiffOn ℂ ω F s) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℂ ω (Lhol Z F) s := by
  have hl : ContDiff ℂ ω (fun z : Matrix (Fin n) (Fin n) ℂ => Z * z) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Z)).contDiff
  exact (hF.fderiv_of_isOpen hs le_top).clm_apply hl.contDiffOn

/- English proof (translation)
Proceed by induction on `D with`. Consider the case `nil => exact tb_contDiffOn_phiM μ`. Consider the case `cons Z D ih => exact tb_contDiffOn_lhol isOpen_omega ih Z`.
-/
lemma tb_contDiffOn_lWord (μ : Fin n → ℤ) (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    ContDiffOn ℂ ω (lWord D (PhiM μ)) (OmegaSet n) := by
  induction D with
  | nil => exact tb_contDiffOn_phiM μ
  | cons Z D ih => exact tb_contDiffOn_lhol isOpen_omega ih Z

/- English proof (translation)
Proceed by induction on `D with`. Consider the case `nil => intro x _`. Both sides reduce to the same expression. Consider the case `cons Z D ih`. Introduce `x hx`.

Establish `hxu` using `tb_isUnit_of_omegaP hx`. Take `⟨L, hL, hLv⟩` from `tb_inv_hasFDerivAt hxu`. Establish `hnhds : OmegaP n ∈ nhds x` using `hL.continuousAt.preimage_mem_nhds (isOpen_omega.mem_nhds (show x⁻¹ ∈ OmegaSet n from hx))`. Establish `hev : hWord D (PhiP μ) =ᶠ[nhds x] fun z => lWord (D.map Neg.neg) (PhiM μ) z⁻¹` using `Filter.eventually_of_mem hnhds ih`. Establish `hG : HasFDerivAt (lWord (D.map Neg.neg) (PhiM μ)) (fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹) x⁻¹` using `(((tb_contDiffOn_lWord μ _).differentiableOn (by simp)).differentiableAt (isOpen_omega.mem_nhds hx)).hasFDerivAt`.

Establish `hcomp : HasFDerivAt (fun z => lWord (D.map Neg.neg) (PhiM μ) z⁻¹) ((fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹).comp L) x` using `hG.comp x hL`. Use `show fderiv ℂ (hWord D (PhiP μ)) x (x * Z) = fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹ (-Z * x⁻¹)`. Rewrite using `[hev.fderiv_eq, hcomp.fderiv, ContinuousLinearMap.comp_apply, hLv]`. Use `congr 1`. Establish `hxd : IsUnit x.det` using `(Matrix.isUnit_iff_isUnit_det x).mp hxu`.

Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul x hxd, Matrix.one_mul, Matrix.neg_mul]`.
-/
theorem tb_hWord_phiP (μ : Fin n → ℤ) (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    ∀ x ∈ OmegaP n, hWord D (PhiP μ) x = lWord (D.map Neg.neg) (PhiM μ) x⁻¹ := by
  induction D with
  | nil => intro x _; rfl
  | cons Z D ih =>
    intro x hx
    have hxu := tb_isUnit_of_omegaP hx
    obtain ⟨L, hL, hLv⟩ := tb_inv_hasFDerivAt hxu
    have hnhds : OmegaP n ∈ nhds x :=
      hL.continuousAt.preimage_mem_nhds (isOpen_omega.mem_nhds (show x⁻¹ ∈ OmegaSet n from hx))
    have hev : hWord D (PhiP μ) =ᶠ[nhds x] fun z => lWord (D.map Neg.neg) (PhiM μ) z⁻¹ :=
      Filter.eventually_of_mem hnhds ih
    have hG : HasFDerivAt (lWord (D.map Neg.neg) (PhiM μ))
        (fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹) x⁻¹ :=
      (((tb_contDiffOn_lWord μ _).differentiableOn (by simp)).differentiableAt
        (isOpen_omega.mem_nhds hx)).hasFDerivAt
    have hcomp : HasFDerivAt (fun z => lWord (D.map Neg.neg) (PhiM μ) z⁻¹)
        ((fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹).comp L) x := hG.comp x hL
    show fderiv ℂ (hWord D (PhiP μ)) x (x * Z) = fderiv ℂ (lWord (D.map Neg.neg) (PhiM μ)) x⁻¹ (-Z * x⁻¹)
    rw [hev.fderiv_eq, hcomp.fderiv, ContinuousLinearMap.comp_apply, hLv]
    congr 1
    have hxd : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).mp hxu
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul x hxd, Matrix.one_mul, Matrix.neg_mul]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
