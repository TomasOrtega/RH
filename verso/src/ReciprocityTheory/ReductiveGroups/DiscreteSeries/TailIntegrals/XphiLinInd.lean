import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HpkMulVecMulVec

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section fs
variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `c`. Simplify using `only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and, Fin.le_def]`. Prove the components needed by the constructor for the conclusion. Introduce `hc; exact ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩`. Introduce and unpack `⟨a, rfl⟩`.

Use `a.isLt` as an intermediate fact. Simplify using `only [Fin.castLEEmb_apply, Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers.
-/
theorem iic_eq (l : Fin (r + 1)) :
    Finset.Iic l = Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)) := by
  ext c
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and, Fin.le_def]
  constructor
  · intro hc; exact ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩
  · rintro ⟨a, rfl⟩
    have := a.isLt
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    omega

/- English proof (translation)
Unfold `fsR`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hpos l).le _)]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `ht : Ga k r l (fun a => x *ᵥ phiV' k r a) = ((cl τ l : ℝ)) ^ 2`. Rewrite using `[← hGa l, iic_eq, Finset.prod_map, Finset.prod_pow, cl, NNReal.coe_prod]`.

Both sides reduce to the same expression. Establish `hc : 0 < (cl τ l : ℝ)`. Establish `h0` using `hpos l`. Rewrite `h0` using `[ht]`. Conclude with `lt_of_le_of_ne (NNReal.coe_nonneg _) (fun he => by rw [← he] at h0; simp at h0)`.

Rewrite using `[ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← ENNReal.ofReal_rpow_of_pos hc, ENNReal.ofReal_coe_nnreal]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ofReal_fsR (s : Fin (r + 1) → ℝ) (x : Mat k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hGa : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l (fun a => x *ᵥ phiV' k r a))
    (hpos : ∀ l, 0 < Ga k r l (fun a => x *ᵥ phiV' k r a)) :
    ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  unfold fsR
  rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hpos l).le _)]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ht : Ga k r l (fun a => x *ᵥ phiV' k r a) = ((cl τ l : ℝ)) ^ 2 := by
    rw [← hGa l, iic_eq, Finset.prod_map, Finset.prod_pow, cl, NNReal.coe_prod]
    rfl
  have hc : 0 < (cl τ l : ℝ) := by
    have h0 := hpos l
    rw [ht] at h0
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (fun he => by rw [← he] at h0; simp at h0)
  rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← ENNReal.ofReal_rpow_of_pos hc,
    ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `hinj : Function.Injective (Matrix.mulVecLin x)` using `fun u v huv => by`. Establish `h2` using `congrArg (fun w => x⁻¹ *ᵥ w) huv`. Simplify `h2` using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, uh_inv_mul hx]`. Conclude with `(phiV'_linInd k r hk).map' (Matrix.mulVecLin x) (LinearMap.ker_eq_bot.2 hinj)`.
-/
theorem xphi_linInd (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    LinearIndependent ℂ (fun a => x *ᵥ phiV' k r a) := by
  have hinj : Function.Injective (Matrix.mulVecLin x) := fun u v huv => by
    have h2 := congrArg (fun w => x⁻¹ *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, uh_inv_mul hx] using h2
  exact (phiV'_linInd k r hk).map' (Matrix.mulVecLin x) (LinearMap.ker_eq_bot.2 hinj)

/- English proof (translation)
Take `⟨κ, hκ, τ, hτ, hY, hGa⟩` from `hIW k r (fun a => x *ᵥ phiV' k r a) hk (xphi_linInd hk hx) (fun a b => by rw [herm_UH' _ hx]; exact phiV'_iso k r hk a b)`. Conclude with `⟨κ, hκ, τ, hτ, hY, fun s => ofReal_fsR s x τ hGa (fun l => GS.ga_pos k r _ (xphi_linInd hk hx) l)⟩`.
-/
theorem iw_at (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ s, ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hGa⟩ := hIW k r (fun a => x *ᵥ phiV' k r a) hk (xphi_linInd hk hx)
    (fun a b => by rw [herm_UH' _ hx]; exact phiV'_iso k r hk a b)
  exact ⟨κ, hκ, τ, hτ, hY, fun s => ofReal_fsR s x τ hGa (fun l => GS.ga_pos k r _ (xphi_linInd hk hx) l)⟩

/- English proof (translation)
Take `⟨κ, hκ, τ, hτ, hY, hf⟩` from `iw_at hIW hk hx`. Use `⟨κ, hκ, fun s g => ?_⟩` and prove the remaining obligations. Rewrite using `[hf s]`. Conclude with `fsE_fac s _ _ _ (dl_left hx hκ.1 τ hτ hY g)`.
-/
theorem fsE_left (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (x⁻¹ * g) = ENNReal.ofReal (fsR k r s x) * FsE k r s (κ⁻¹ * g) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hx
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_left hx hκ.1 τ hτ hY g)

/- English proof (translation)
Take `⟨κ, hκ, τ, hτ, hY, hf⟩` from `iw_at hIW hk hy`. Use `⟨κ, hκ, fun s g => ?_⟩` and prove the remaining obligations. Rewrite using `[hf s]`. Conclude with `fsE_fac s _ _ _ (dl_right τ hτ hY g)`.
-/
theorem fsE_right (hIW : IW) (hk : 1 ≤ k) {y : Mat k r} (hy : y ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (g * y) = ENNReal.ofReal (fsR k r s y) * FsE k r s (g * κ) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hy
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_right τ hτ hY g)

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun l _ => Real.rpow_nonneg (GS.ga_pos k r _ (xphi_linInd hk hx) l).le _`.
-/
theorem fsR_nonneg {k r : ℕ} (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) (s : Fin (r + 1) → ℝ) :
    0 ≤ fsR k r s x :=
  Finset.prod_nonneg fun l _ => Real.rpow_nonneg (GS.ga_pos k r _ (xphi_linInd hk hx) l).le _

end fs

section meas
variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Continuous.matrix_mul continuous_const continuous_id`.
-/
theorem cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) :=
  Continuous.matrix_mul continuous_const continuous_id

/- English proof (translation)
The claim follows from `Continuous.matrix_mul continuous_id continuous_const`.
-/
theorem cont_rmul (a : Mat k r) : Continuous (rmulF a : Mt k r → Mt k r) :=
  Continuous.matrix_mul continuous_id continuous_const

def lmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv g := by
    show a⁻¹ * (a * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_inv_mul ha, Matrix.one_mul]; rfl
  right_inv g := by
    show a * (a⁻¹ * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_mul_inv ha, Matrix.one_mul]; rfl
  measurable_toFun := (cont_lmul a).measurable
  measurable_invFun := (cont_lmul a⁻¹).measurable

def rmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulF a
  invFun := rmulF a⁻¹
  left_inv g := by
    show Matrix.of g * a * a⁻¹ = g
    rw [Matrix.mul_assoc, uh_mul_inv ha, Matrix.mul_one]; rfl
  right_inv g := by
    show Matrix.of g * a⁻¹ * a = g
    rw [Matrix.mul_assoc, uh_inv_mul ha, Matrix.mul_one]; rfl
  measurable_toFun := (cont_rmul a).measurable
  measurable_invFun := (cont_rmul a⁻¹).measurable

/- English proof (translation)
Establish `h` using `lintegral_map_equiv f (lmulE ha) (μ := μ)`. Rewrite `h` using `[show ⇑(lmulE ha) = lmulM a from rfl, hμ.left a ha]`. Conclude with `h.symm`.
-/
theorem lmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (lmulM a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (lmulE ha) (μ := μ)
  rw [show ⇑(lmulE ha) = lmulM a from rfl, hμ.left a ha] at h
  exact h.symm

/- English proof (translation)
Establish `h` using `lintegral_map_equiv f (rmulE ha) (μ := μ)`. Rewrite `h` using `[show ⇑(rmulE ha) = rmulF a from rfl, hμ.right a ha]`. Conclude with `h.symm`.
-/
theorem rmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (rmulF a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (rmulE ha) (μ := μ)
  rw [show ⇑(rmulE ha) = rmulF a from rfl, hμ.right a ha] at h
  exact h.symm

end meas

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
