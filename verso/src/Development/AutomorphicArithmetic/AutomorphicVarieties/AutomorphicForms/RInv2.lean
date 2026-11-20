import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory GlobalTheory.CuspRep

namespace UpperTheory.V.InvT

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem invT_val (g : GL (Fin a) R) : (invT a R g).val = (g⁻¹).valᵀ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem invT_inv_val (g : GL (Fin a) R) : ((invT a R g)⁻¹).val = g.valᵀ := rfl

/- English proof (translation)
The claim follows from `Units.ext (Matrix.transpose_transpose _)`.
-/
@[simp] theorem invT_invT (g : GL (Fin a) R) : invT a R (invT a R g) = g := Units.ext (Matrix.transpose_transpose _)

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem map_invT (f : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map f (invT a R g) = invT a S (GeneralLinearGroup.map f g) := Units.ext rfl

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g⁻¹).val j i) = (1 : Matrix (Fin a) (Fin a) S) j i - s ((1 : Matrix (Fin a) (Fin a) R) j i) + s ((g⁻¹).val j i)`. Simplify using `only [Matrix.one_apply, eq_comm (a := i)]`.
-/
theorem cornerGL_invT (s : R →ₙ+* S) (g : GL (Fin a) R) : cornerGL a s (invT a R g) = invT a S (cornerGL a s g) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g⁻¹).val j i) =
    (1 : Matrix (Fin a) (Fin a) S) j i - s ((1 : Matrix (Fin a) (Fin a) R) j i) + s ((g⁻¹).val j i)
  simp only [Matrix.one_apply, eq_comm (a := i)]

/- English proof (translation)
Rewrite using `[← map_inv]`. Conclude with `Units.ext (Matrix.det_transpose _)`.
-/
theorem det_invT (g : GL (Fin a) R) : GeneralLinearGroup.det (invT a R g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  exact Units.ext (Matrix.det_transpose _)

/- English proof (translation)
The claim follows from `Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩`.
-/
theorem continuous_invT [TopologicalSpace R] : Continuous (invT a R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

def revGL (a : ℕ) (R : Type) [CommRing R] : GL (Fin a) R :=
  ⟨(1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id, (1 : Matrix (Fin a) (Fin a) R).submatrix id Fin.revPerm,
    by rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]; simp,
    by rw [Matrix.submatrix_mul_equiv]; simp⟩

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `f ((1 : Matrix (Fin a) (Fin a) R) _ _) = (1 : Matrix (Fin a) (Fin a) S) _ _`. Simplify using `[Matrix.one_apply, apply_ite f]`.
-/
theorem map_revGL (f : R →+* S) : GeneralLinearGroup.map f (revGL a R) = revGL a S := by
  ext i j
  change f ((1 : Matrix (Fin a) (Fin a) R) _ _) = (1 : Matrix (Fin a) (Fin a) S) _ _
  simp [Matrix.one_apply, apply_ite f]

def blockRev {r : ℕ} : BlockIx a (a - r) ≃ BlockIx a r where
  toFun p := ⟨(p.1.2.rev, p.1.1.rev), by have := p.2; have := p.1.1.2; have := p.1.2.2; simp only [Fin.val_rev]; omega⟩
  invFun p := ⟨(p.1.2.rev, p.1.1.rev), by have := p.2; have := p.1.1.2; have := p.1.2.2; simp only [Fin.val_rev]; omega⟩
  left_inv p := by simp
  right_inv p := by simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id * (1 - nilM x)ᵀ = (1 + nilM fun p : BlockIx a (a - r) => -x (blockRev p)) * (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id`. Use extensionality with `i j`. Establish `h1 : ∀ M : Matrix (Fin a) (Fin a) R, ((1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id * M) i j = M i.rev j` using `fun M => by`. Simplify using `[Matrix.mul_apply, Matrix.one_apply]`.

Establish `h2 : ∀ M : Matrix (Fin a) (Fin a) R, (M * (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id) i j = M i j.rev` using `fun M => by`. Simplify using `[Matrix.mul_apply, Matrix.one_apply, Fin.rev_eq_iff]`. Rewrite using `[h1, h2]`. Establish `hi` using `i.2`. Establish `hj` using `j.2`.

Simplify using `only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, nilM, Matrix.of_apply]`. Rewrite using `[sub_eq_add_neg]`. Use `congr 1`. Conclude with `if_congr (by rw [eq_comm, Fin.rev_eq_iff]) rfl rfl`. Distinguish the cases in `h : (j : ℕ) < r ∧ r ≤ (i.rev : ℕ)`.

Rewrite using `[dif_pos h, dif_pos (by simp only [Fin.val_rev] at h ⊢; omega)]`. Simplify using `[blockRev]`. Rewrite using `[dif_neg h, dif_neg (by simp only [Fin.val_rev] at h ⊢; omega), neg_zero]`.
-/
theorem revGL_mul_invT_unip {r : ℕ} (x : BlockIx a r → R) :
    revGL a R * invT a R (unip x) = unip (fun p : BlockIx a (a - r) => -x (blockRev p)) * revGL a R := by
  apply Units.ext
  change (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id * (1 - nilM x)ᵀ =
    (1 + nilM fun p : BlockIx a (a - r) => -x (blockRev p)) * (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id
  ext i j
  have h1 : ∀ M : Matrix (Fin a) (Fin a) R,
      ((1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id * M) i j = M i.rev j := fun M => by
    simp [Matrix.mul_apply, Matrix.one_apply]
  have h2 : ∀ M : Matrix (Fin a) (Fin a) R,
      (M * (1 : Matrix (Fin a) (Fin a) R).submatrix Fin.revPerm id) i j = M i j.rev := fun M => by
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.rev_eq_iff]
  rw [h1, h2]
  have hi := i.2
  have hj := j.2
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, nilM, Matrix.of_apply]
  rw [sub_eq_add_neg]
  congr 1
  · exact if_congr (by rw [eq_comm, Fin.rev_eq_iff]) rfl rfl
  · by_cases h : (j : ℕ) < r ∧ r ≤ (i.rev : ℕ)
    · rw [dif_pos h, dif_pos (by simp only [Fin.val_rev] at h ⊢; omega)]
      simp [blockRev]
    · rw [dif_neg h, dif_neg (by simp only [Fin.val_rev] at h ⊢; omega), neg_zero]

def smIrrInvT [TopologicalSpace R] (σ : SmIrr (GL (Fin a) R)) : SmIrr (GL (Fin a) R) where
  V := σ.V
  ρ := σ.ρ.comp (invT a R)
  smooth v := (σ.smooth v).preimage continuous_invT
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    have h1 : σ.ρ (invT a R (invT a R g)) v ∈ W := hW (invT a R g) v hv
    rwa [invT_invT] at h1

end Ring

section Smooth

open scoped ContDiff

variable {A : Type} [NormedCommRing A] [NormedAlgebra ℝ A] {a : ℕ}

def invTL (x : Fin a → Fin a → A) : Fin a → Fin a → A := Matrix.of.symm ((Matrix.of x)⁻¹)ᵀ

omit [NormedAlgebra ℝ A] in
/- English proof (translation)
The claim follows from `congrArg (fun m : Matrix (Fin a) (Fin a) A => Matrix.of.symm mᵀ) (Matrix.coe_units_inv y).symm`.
-/
theorem invTL_val (y : GL (Fin a) A) : invTL (Matrix.of.symm y.val) = Matrix.of.symm (invT a A y).val :=
  congrArg (fun m : Matrix (Fin a) (Fin a) A => Matrix.of.symm mᵀ) (Matrix.coe_units_inv y).symm

omit [NormedAlgebra ℝ A] in
/- English proof (translation)
The claim follows from `(invTL_val 1).trans (by rw [map_one]; rfl)`.
-/
theorem invTL_one : invTL (Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A)) = Matrix.of.symm 1 :=
  (invTL_val 1).trans (by rw [map_one]; rfl)

omit [NormedAlgebra ℝ A] in
/- English proof (translation)
Take `⟨u, hu⟩` from `hx`. Establish `e : x = Matrix.of.symm u.val` using `hu.symm`. Rewrite using `[e, invTL_val]`. Conclude with `(invT a A u).isUnit`.
-/
theorem isUnit_invTL {x : Fin a → Fin a → A} (hx : IsUnit (Matrix.of x)) : IsUnit (Matrix.of (invTL x)) := by
  obtain ⟨u, hu⟩ := hx
  have e : x = Matrix.of.symm u.val := hu.symm
  rw [e, invTL_val]
  exact (invT a A u).isUnit

omit [NormedAlgebra ℝ A] in

/- English proof (translation)
Establish `h : ∀ x : Matrix (Fin a) (Fin a) A, ‖Matrix.of.symm xᵀ‖ ≤ ‖Matrix.of.symm x‖` using `fun x => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => (norm_le_pi_norm (Matrix.of.symm x j) i).trans (norm_le_pi_norm (Matrix.of.symm x) j)`. Conclude with `le_antisymm (h x) (h xᵀ)`.
-/
theorem norm_transpose (x : Matrix (Fin a) (Fin a) A) : ‖Matrix.of.symm xᵀ‖ = ‖Matrix.of.symm x‖ := by
  have h : ∀ x : Matrix (Fin a) (Fin a) A, ‖Matrix.of.symm xᵀ‖ ≤ ‖Matrix.of.symm x‖ := fun x =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
      (norm_le_pi_norm (Matrix.of.symm x j) i).trans (norm_le_pi_norm (Matrix.of.symm x) j)
  exact le_antisymm (h x) (h xᵀ)

/- English proof (translation)
Simplify using `only [Matrix.det_apply', Matrix.of_apply]`. Use `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)` and prove the remaining obligations. Conclude with `(contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))`.
-/
private theorem contDiff_det : ContDiff ℝ ∞ fun x : Fin a → Fin a → A => (Matrix.of x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))

variable [CompleteSpace A]

/- English proof (translation)
Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det _).1 hx`. Use `contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_` and prove the remaining obligations. Establish `e : (fun x : Fin a → Fin a → A => invTL x i j) = fun x => Ring.inverse (Matrix.of x).det * (Matrix.of (Function.update x i (Pi.single j 1))).det`. Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `(Matrix.of x)⁻¹ j i = _`.

Rewrite using `[Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `ContDiffAt.mul (ContDiffAt.comp (g := Ring.inverse) x (hu ▸ contDiffAt_ringInverse ℝ u) contDiff_det.contDiffAt) (contDiff_det.comp (contDiff_pi.2 fun k => ?_)).contDiffAt` and prove the remaining obligations. Distinguish the cases in `h : k = i`.

Substitute `h` using the available equality. Simplify using `using contDiff_const`. Simplify `contDiff_apply ℝ _ k` using `[h]`.
-/
theorem contDiffAt_invTL {x : Fin a → Fin a → A} (hx : IsUnit (Matrix.of x)) : ContDiffAt ℝ ∞ invTL x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have e : (fun x : Fin a → Fin a → A => invTL x i j) = fun x =>
      Ring.inverse (Matrix.of x).det * (Matrix.of (Function.update x i (Pi.single j 1))).det := by
    funext x
    change (Matrix.of x)⁻¹ j i = _
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply]
    rfl
  rw [e]
  refine ContDiffAt.mul (ContDiffAt.comp (g := Ring.inverse) x (hu ▸ contDiffAt_ringInverse ℝ u) contDiff_det.contDiffAt)
    (contDiff_det.comp (contDiff_pi.2 fun k => ?_)).contDiffAt
  by_cases h : k = i
  · subst h; simpa using contDiff_const
  · simpa [h] using contDiff_apply ℝ _ k

/- English proof (translation)
Use `set o : Fin a → Fin a → A := Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A) with ho`. Establish `hd : HasFDerivAt invTL (fderiv ℝ invTL o) o` using `((contDiffAt_invTL (x := o) isUnit_one).differentiableAt (by simp)).hasFDerivAt`. Use function extensionality and compare the values at `i j`. Establish `h1 : ∀ k, HasFDerivAt (fun x : Fin a → Fin a → A => x k i) _ o` using `fun k => hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 (hasFDerivAt_id (𝕜 := ℝ) o) k) i`. Establish `h2 : ∀ k, HasFDerivAt (fun x : Fin a → Fin a → A => invTL x k j) _ o` using `fun k => hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 hd k) j`.

Establish `h3` using `HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (h1 k).mul' (h2 k)`. Establish `hu : ∀ᶠ x : Fin a → Fin a → A in 𝓝 o, IsUnit (Matrix.of x).det` using `(Units.isOpen.preimage contDiff_det.continuous).mem_nhds ((Matrix.isUnit_iff_isUnit_det _).1 isUnit_one)`. Establish `h4 : HasFDerivAt (𝕜` using `ℝ) (fun x : Fin a → Fin a → A => ∑ k, x k i * invTL x k j) 0 o := by`. Use `(hasFDerivAt_const ((1 : Matrix (Fin a) (Fin a) A) i j) o).congr_of_eventuallyEq (hu.mono fun x hx => ?_)` and prove the remaining obligations. Use `congrFun (congrFun (congrArg Matrix.transpose (Matrix.nonsing_inv_mul _ hx)) i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_one]`. Then use the resulting hypothesis. Establish `h5` using `congrArg (fun L : (Fin a → Fin a → A) →L[ℝ] A => L X) (h3.unique h4)`. Establish `e : invTL o = o` using `invTL_one`. Establish `e' : ∀ k l, o k l = if k = l then 1 else 0` using `fun k l => Matrix.one_apply`. Simplify using `[e, e', Finset.sum_add_distrib] at h5`.

Conclude with `eq_neg_of_add_eq_zero_left h5`.
-/
theorem fderiv_invTL_one (X : Fin a → Fin a → A) :
    fderiv ℝ invTL (Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A)) X = Matrix.of.symm (-(Matrix.of X)ᵀ) := by
  set o : Fin a → Fin a → A := Matrix.of.symm (1 : Matrix (Fin a) (Fin a) A) with ho
  have hd : HasFDerivAt invTL (fderiv ℝ invTL o) o :=
    ((contDiffAt_invTL (x := o) isUnit_one).differentiableAt (by simp)).hasFDerivAt
  funext i j
  have h1 : ∀ k, HasFDerivAt (fun x : Fin a → Fin a → A => x k i) _ o := fun k =>
    hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 (hasFDerivAt_id (𝕜 := ℝ) o) k) i
  have h2 : ∀ k, HasFDerivAt (fun x : Fin a → Fin a → A => invTL x k j) _ o := fun k =>
    hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 hd k) j
  have h3 := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (h1 k).mul' (h2 k)
  have hu : ∀ᶠ x : Fin a → Fin a → A in 𝓝 o, IsUnit (Matrix.of x).det :=
    (Units.isOpen.preimage contDiff_det.continuous).mem_nhds ((Matrix.isUnit_iff_isUnit_det _).1 isUnit_one)
  have h4 : HasFDerivAt (𝕜 := ℝ) (fun x : Fin a → Fin a → A => ∑ k, x k i * invTL x k j) 0 o := by
    refine (hasFDerivAt_const ((1 : Matrix (Fin a) (Fin a) A) i j) o).congr_of_eventuallyEq (hu.mono fun x hx => ?_)
    have := congrFun (congrFun (congrArg Matrix.transpose (Matrix.nonsing_inv_mul _ hx)) i) j
    rwa [Matrix.transpose_mul, Matrix.transpose_one] at this
  have h5 := congrArg (fun L : (Fin a → Fin a → A) →L[ℝ] A => L X) (h3.unique h4)
  have e : invTL o = o := invTL_one
  have e' : ∀ k l, o k l = if k = l then 1 else 0 := fun k l => Matrix.one_apply
  simp [e, e', Finset.sum_add_distrib] at h5
  exact eq_neg_of_add_eq_zero_left h5

end Smooth

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
The claim follows from `map_invT _ γ`.
-/
theorem ratGL_invT (γ : GL (Fin a) E) : ratGL E a (invT a E γ) = invT a (Ad E) (ratGL E a γ) := map_invT _ γ

/- English proof (translation)
The claim follows from `cornerGL_invT _ k`.
-/
theorem finGL_invT (k : GL (Fin a) (Af E)) : finGL E a (invT a (Af E) k) = invT a (Ad E) (finGL E a k) :=
  cornerGL_invT _ k

/- English proof (translation)
The claim follows from `cornerGL_invT _ g`.
-/
theorem locGL_invT (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    locGL E a w (invT a _ g) = invT a (Af E) (locGL E a w g) := cornerGL_invT _ g

/- English proof (translation)
The claim follows from `(congrArg χ.1 (det_invT g)).trans (map_inv χ.1 _)`.
-/
theorem chiDet_invT (χ : Formalism.L2.Host.HChar E) (g : GA E a) : chiDet a χ (invT a (Ad E) g) = chiDet a χ⁻¹ g :=
  (congrArg χ.1 (det_invT g)).trans (map_inv χ.1 _)

/- English proof (translation)
Introduce `r h0 h1 _ _ μ 𝓕 hμ hF g`. Use `borelize (BlockIx a (a - r) → Ad E)`. Set `e : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a (a - r) → Ad E)` to `{ toFun := fun x p => -x (blockRev p) invFun := fun y p => -y (blockRev.symm p) left_inv := fun x => by funext p; simp right_inv := fun x => by funext p; simp map_add' := fun x y => by funext p; simp [add_comm] continuous_toFun := continuous_pi fun p => (continuous_apply _).neg c …`. Set `em : (BlockIx a r → Ad E) ≃ᵐ (BlockIx a (a - r) → Ad E)` to `e.toHomeomorph.toMeasurableEquiv`. Establish `hμ' : (μ.map em).IsAddHaarMeasure` using `e.isAddHaarMeasure_map μ`.

Set `er : ratN E a (a - r) ≃ ratN E a r` to `{ toFun := fun y => ⟨e.symm y.1, by`. Take `⟨_, y, rfl⟩` from `y`. Conclude with `⟨fun p => -y (blockRev.symm p), funext fun p => map_neg (algebraMap E (Ad E)) _⟩⟩`. Use `invFun := fun y => ⟨e y.1, by`. Take `⟨_, y, rfl⟩` from `y`.

Conclude with `⟨fun p => -y (blockRev p), funext fun p => map_neg (algebraMap E (Ad E)) _⟩⟩`. Use `left_inv := fun y => Subtype.ext (e.apply_symm_apply _)`. Use `right_inv := fun y => Subtype.ext (e.symm_apply_apply _) }`. Establish `hF' : IsAddFundamentalDomain (ratN E a (a - r)) (em '' 𝓕) (μ.map em)` using `hF.image_of_equiv em.toEquiv (MeasurePreserving.symm em ⟨em.measurable, rfl⟩).quasiMeasurePreserving er fun y x => by`. Express the relevant statement in the definitionally equal form `e (e.symm y.1 + x) = y.1 + e x`.

Rewrite using `[map_add, e.apply_symm_apply]`. Establish `key` using `h (a - r) (by omega) (by omega) _ _ hμ' hF' (revGL a (Ad E) * invT a (Ad E) g)`. Rewrite `key` using `[setIntegral_map_equiv, Set.preimage_image_eq _ em.injective]`. Rewrite using `[← key]`. Use `congrArg _ (funext fun x => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[map_mul, ← hl (revGL a E), ratGL, map_revGL, ← mul_assoc, revGL_mul_invT_unip, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem isCuspidal_invT {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g) (h : IsCuspidal φ) :
    IsCuspidal fun g => φ (invT a (Ad E) g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  borelize (BlockIx a (a - r) → Ad E)
  let e : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a (a - r) → Ad E) :=
    { toFun := fun x p => -x (blockRev p)
      invFun := fun y p => -y (blockRev.symm p)
      left_inv := fun x => by funext p; simp
      right_inv := fun x => by funext p; simp
      map_add' := fun x y => by funext p; simp [add_comm]
      continuous_toFun := continuous_pi fun p => (continuous_apply _).neg
      continuous_invFun := continuous_pi fun p => (continuous_apply _).neg }
  let em : (BlockIx a r → Ad E) ≃ᵐ (BlockIx a (a - r) → Ad E) := e.toHomeomorph.toMeasurableEquiv
  have hμ' : (μ.map em).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let er : ratN E a (a - r) ≃ ratN E a r :=
    { toFun := fun y => ⟨e.symm y.1, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => -y (blockRev.symm p), funext fun p => map_neg (algebraMap E (Ad E)) _⟩⟩
      invFun := fun y => ⟨e y.1, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => -y (blockRev p), funext fun p => map_neg (algebraMap E (Ad E)) _⟩⟩
      left_inv := fun y => Subtype.ext (e.apply_symm_apply _)
      right_inv := fun y => Subtype.ext (e.symm_apply_apply _) }
  have hF' : IsAddFundamentalDomain (ratN E a (a - r)) (em '' 𝓕) (μ.map em) :=
    hF.image_of_equiv em.toEquiv
      (MeasurePreserving.symm em ⟨em.measurable, rfl⟩).quasiMeasurePreserving er fun y x => by
        change e (e.symm y.1 + x) = y.1 + e x
        rw [map_add, e.apply_symm_apply]
  have key := h (a - r) (by omega) (by omega) _ _ hμ' hF' (revGL a (Ad E) * invT a (Ad E) g)
  rw [setIntegral_map_equiv, Set.preimage_image_eq _ em.injective] at key
  rw [← key]
  refine congrArg _ (funext fun x => ?_)
  beta_reduce
  rw [map_mul, ← hl (revGL a E), ratGL, map_revGL, ← mul_assoc, revGL_mul_invT_unip, mul_assoc]
  rfl

/- English proof (translation)
Set `c` to `GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl (w.adicCompletion E)) a`. Establish `hc : ∀ g, c g = invT a _ g` using `fun g => Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)`. Establish `hs : ∀ g, c.symm g = invT a _ g` using `fun g => (MulEquiv.symm_apply_eq _).2 (by rw [hc, invT_invT])`. Establish `hK` using `GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (RingEquiv.refl (w.adicCompletion E)) (O := Formalism.UG.Ov E w) (O' := Formalism.UG.Ov E w) fun _ => Iff.rfl`. Establish `hf : ∀ g y, T.toLinearMap ((ρ.comp c.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y)` using `fun g y => by`.

Express the relevant statement in the definitionally equal form `T (ρ (c.symm g) y) = ρ' g (T y)`. Rewrite using `[hs, hT]`. Establish `key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w ρ' (T x) (B.map (·⁻¹))` using `fun x hx => (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT (.refl _) (fun _ => rfl) rfl hx).map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)`. Prove the components needed by the constructor for the conclusion. Take `⟨x, hx⟩` from `h.exists_vec`.

Conclude with `(Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩`. Introduce `y hy h0`. Take `⟨x, rfl⟩` from `T.surjective y`. Use `key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))` and prove the remaining obligations. Use `GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)` as an intermediate fact.

Rewrite `this` using `[hT, show GlobalTheory.LFun.ConjPlace.invT _ a k = _ from hc k, invT_invT]`. Then use the resulting hypothesis.
-/
theorem hasSatGL_invT {w : HeightOneSpectrum (𝓞 E)} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' g (T x) = T (ρ (invT a _ g) x)) {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ B) :
    GlobalTheory.LFun.HasSatGL w ρ' (B.map (·⁻¹)) := by
  let c := GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl (w.adicCompletion E)) a
  have hc : ∀ g, c g = invT a _ g := fun g => Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
  have hs : ∀ g, c.symm g = invT a _ g := fun g => (MulEquiv.symm_apply_eq _).2 (by rw [hc, invT_invT])
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) (RingEquiv.refl (w.adicCompletion E)) (O := Formalism.UG.Ov E w)
    (O' := Formalism.UG.Ov E w) fun _ => Iff.rfl
  have hf : ∀ g y, T.toLinearMap ((ρ.comp c.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ (c.symm g) y) = ρ' g (T y)
    rw [hs, hT]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT (.refl _) (fun _ => rfl) rfl hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT, show GlobalTheory.LFun.ConjPlace.invT _ a k = _ from hc k, invT_invT] at this

/- English proof (translation)
Take `⟨k, h, rfl⟩` from `hk`. Use `⟨invT a _ k, ?_, map_invT _ k⟩` and prove the remaining obligations. Establish `h' : GeneralLinearGroup.map _ k = 1` using `h`. Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map _ (invT a _ k) = 1`. Rewrite using `[map_invT, h', map_one]`.
-/
theorem invT_mem_KLev {M : ℕ} {k : GL (Fin a) (Af E)} (hk : k ∈ Af.KLev E a M) : invT a (Af E) k ∈ Af.KLev E a M := by
  obtain ⟨k, h, rfl⟩ := hk
  refine ⟨invT a _ k, ?_, map_invT _ k⟩
  have h' : GeneralLinearGroup.map _ k = 1 := h
  change GeneralLinearGroup.map _ (invT a _ k) = 1
  rw [map_invT, h', map_one]

/- English proof (translation)
Take `⟨v, h0, hv⟩` from `h`. Conclude with `⟨T v, (map_ne_zero_iff T T.injective).2 h0, fun u hu => by rw [hT, hv _ (hU u hu)]⟩`.
-/
theorem hasFixed_invT {R V W : Type} [CommRing R] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) R) V} {ρ' : Representation ℂ (GL (Fin a) R) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' g (T x) = T (ρ (invT a _ g) x)) {U : Subgroup (GL (Fin a) R)}
    (hU : ∀ u ∈ U, invT a R u ∈ U) (h : Af.HasFixed ρ U) : Af.HasFixed ρ' U := by
  obtain ⟨v, h0, hv⟩ := h
  exact ⟨T v, (map_ne_zero_iff T T.injective).2 h0, fun u hu => by rw [hT, hv _ (hU u hu)]⟩

end UpperTheory.V.InvT
