import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.HeisMultLin

/- English proof (translation)
Introduce `r hr`. Establish `h : ∀ i j, r • x i j = 0` using `fun i j => by`. Use `congrFun (congrFun (hx r hr) i) j` as an intermediate fact. Simplify using `using this`. Rewrite using `[← mul_smul_comm]`.

Unfold `hTens`. Simplify using `only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]`.
-/
theorem at_neg_hTens {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl F} {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (x u : Matrix (Fin m) (Fin n) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) (incM F JA) (incM F JB) x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP c ι hι w`. Establish `hcm : IsCMExt F E σ` using `hP.base.cm`. Take `⟨w0⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdX : X.J.det ≠ 0`. Introduce `h0`.

Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w0)` to reduce the goal to its premises. Establish `e : (X.J.map (B.emb w0).1).det = (B.emb w0).1 X.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e, h0, map_zero]`. Establish `hdW : W.J.det ≠ 0`. Introduce `h0`.

Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w0)` to reduce the goal to its premises. Establish `e : (W.J.map (B.emb w0).1).det = (B.emb w0).1 W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_smul, e, h0, map_zero, mul_zero]`. Use `set A := X.J.map B.τ₁ with hAdef`. Use `set Bm := W.J.map B.τ₁ with hBdef`.

Establish `hA : IsUnit A.det`. Establish `e : A.det = (B.τ₁ : E →+* Fv F B.v₁) X.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e]`. Conclude with `isUnit_iff_ne_zero.2 fun h => hdX ((B.τ₁ : E →+* Fv F B.v₁).injective (by rw [map_zero]; exact h))`. Establish `hB : IsUnit Bmᵀ.det`.

Establish `e : Bm.det = (B.τ₁ : E →+* Fv F B.v₁) W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_transpose, e]`. Conclude with `isUnit_iff_ne_zero.2 fun h => hdW ((B.τ₁ : E →+* Fv F B.v₁).injective (by rw [map_zero]; exact h))`. Take `⟨Z, hZat, hZ0, hZ1⟩` from `GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm B.v₁ B.τ₁ (Matrix.of fun (l : Fin d) (_ : Unit) => -w l) (0 : Matrix (Fin d) Unit (Fv F B.v₁))`. Establish `hZa : ∀ a : AF F, evFin F B.v₁ a = 0 → ∀ l, a • Z l () = 0` using `fun a ha l => by`.

Use `congrFun (congrFun (hZat a ha) l) ()` as an intermediate fact. Simplify using `using this`. Establish `hZτ : ∀ l, piW B.τ₁ (Z l ()) = -w l` using `fun l => by`. Use `congrFun (congrFun hZ0 l) ()` as an intermediate fact. Simplify using `using this`.

Establish `hZσ : ∀ l, piW (B.τ₁.comp σ) (Z l ()) = 0` using `fun l => by`. Use `congrFun (congrFun hZ1 l) ()` as an intermediate fact. Simplify using `using this`. Use `⟨fun l => Z l (), ?_, hZσ, ?_⟩` and prove the remaining obligations. Introduce `a ha`.

Use function extensionality and compare the values at `l`. Simplify using `using hZa a ha l`. Introduce `φ hφ φ₁ hφ₁ hact Y`. Use `set u := Matrix.vecMulVec c (fun l => Z l ()) with hudef`. Establish `huat : At (evFin F B.v₁) u`.

Introduce `a ha`. Use function extensionality and compare the values at `k l`. Simplify using `only [hudef, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]`. Rewrite using `[← mul_smul_comm, hZa a ha l, mul_zero]`. Establish `hu1 : u.map (piW (B.τ₁.comp σ)) = 0`.

Use function extensionality and compare the values at `k l`. Simplify using `[hudef, Matrix.vecMulVec_apply, map_mul, hZσ]`. Establish `hu0 : ∀ k l, u.map (piW B.τ₁) k l = piW B.τ₁ (c k) * -w l` using `fun k l => by`. Simplify using `[hudef, Matrix.vecMulVec_apply, map_mul, hZτ]`. Establish `hL` using `hι`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL`. Simplify using `only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL`. Take `⟨x, hxat, hx0, hx1⟩` from `GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm B.v₁ B.τ₁ (0 : Matrix (Fin n) (Fin d) (Fv F B.v₁)) (-(A⁻¹ * Y * (Bmᵀ)⁻¹))`. Establish `hco : -(A * x.map (piW (B.τ₁.comp σ)) * Bmᵀ) = Y`. Rewrite using `[hx1]`.

Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]`. Establish `hm` using `hL.mult u huat hu1 φ hφ φ₁ hφ₁ hact x hxat hx0`. Rewrite `hm` using `[hco]`. Rewrite using `[hm]`.

Use `congr 1`. Establish `hsymp : B.ψ (symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = GlobalTheory.LatVac.psiAt B.ψ B.v₁ (-(∑ k, ∑ j, (-(A * x.map (piW (B.τ₁.comp σ)) * Bmᵀ)) k j * u.map (piW B.τ₁) k j)) := by`. Unfold `symp`. Rewrite using `[GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm B.v₁ B.τ₁ _ (at_neg_hTens _ _ x u hxat)]`. Rewrite using `[map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm B.τ₁ X.J W.J hP.herm.herm hP.skew.skew x u hx0 hu1]`.

Both sides reduce to the same expression. Rewrite using `[hsymp, hco, GlobalTheory.LatVac.psiAt_apply]`. Use `congr 1`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hu0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heis_mult_lin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (c : Fin n → AE F E)
    (ι : ((Fin n × Fin d → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F B.v₁) → ℂ)),
    M.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ w : Fin d → Fv F B.v₁, ∃ z : Fin d → AE F E, At (evFin F B.v₁) z ∧
      (∀ l, piW (B.τ₁.comp σ) (z l) = 0) ∧
      ∀ φ ∈ SB (Fin n × Fin d → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F B.v₁),
        Acts (evFin F B.v₁) (M.co.rho B.ψ (Matrix.vecMulVec c z)) φ φ₁ →
        ∀ Y : Matrix (Fin n) (Fin d) (Fv F B.v₁),
          ι φ₁ Y = psiLoc B.ψ B.v₁ (∑ k, ∑ l, Y k l * piW B.τ₁ (c k) * w l) * ι φ Y := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP c ι hι w
  have hcm : IsCMExt F E σ := hP.base.cm
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w0)
    have e : (X.J.map (B.emb w0).1).det = (B.emb w0).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w0)
    have e : (W.J.map (B.emb w0).1).det = (B.emb w0).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  set A := X.J.map B.τ₁ with hAdef
  set Bm := W.J.map B.τ₁ with hBdef
  have hA : IsUnit A.det := by
    have e : A.det = (B.τ₁ : E →+* Fv F B.v₁) X.J.det := (RingHom.map_det _ _).symm
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((B.τ₁ : E →+* Fv F B.v₁).injective (by rw [map_zero]; exact h))
  have hB : IsUnit Bmᵀ.det := by
    have e : Bm.det = (B.τ₁ : E →+* Fv F B.v₁) W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_transpose, e]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((B.τ₁ : E →+* Fv F B.v₁).injective (by rw [map_zero]; exact h))
  obtain ⟨Z, hZat, hZ0, hZ1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm B.v₁ B.τ₁
    (Matrix.of fun (l : Fin d) (_ : Unit) => -w l) (0 : Matrix (Fin d) Unit (Fv F B.v₁))
  have hZa : ∀ a : AF F, evFin F B.v₁ a = 0 → ∀ l, a • Z l () = 0 := fun a ha l => by
    have := congrFun (congrFun (hZat a ha) l) ()
    simpa using this
  have hZτ : ∀ l, piW B.τ₁ (Z l ()) = -w l := fun l => by
    have := congrFun (congrFun hZ0 l) ()
    simpa using this
  have hZσ : ∀ l, piW (B.τ₁.comp σ) (Z l ()) = 0 := fun l => by
    have := congrFun (congrFun hZ1 l) ()
    simpa using this
  refine ⟨fun l => Z l (), ?_, hZσ, ?_⟩
  · intro a ha
    funext l
    simpa using hZa a ha l
  intro φ hφ φ₁ hφ₁ hact Y
  set u := Matrix.vecMulVec c (fun l => Z l ()) with hudef
  have huat : At (evFin F B.v₁) u := by
    intro a ha
    funext k l
    simp only [hudef, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    rw [← mul_smul_comm, hZa a ha l, mul_zero]
  have hu1 : u.map (piW (B.τ₁.comp σ)) = 0 := by
    funext k l
    simp [hudef, Matrix.vecMulVec_apply, map_mul, hZσ]
  have hu0 : ∀ k l, u.map (piW B.τ₁) k l = piW B.τ₁ (c k) * -w l := fun k l => by
    simp [hudef, Matrix.vecMulVec_apply, map_mul, hZτ]
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm B.v₁ B.τ₁ (0 : Matrix (Fin n) (Fin d) (Fv F B.v₁))
    (-(A⁻¹ * Y * (Bmᵀ)⁻¹))
  have hco : -(A * x.map (piW (B.τ₁.comp σ)) * Bmᵀ) = Y := by
    rw [hx1]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hB, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  have hm := hL.mult u huat hu1 φ hφ φ₁ hφ₁ hact x hxat hx0
  rw [hco] at hm
  rw [hm]
  congr 1
  have hsymp : B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
      GlobalTheory.LatVac.psiAt B.ψ B.v₁
        (-(∑ k, ∑ j, (-(A * x.map (piW (B.τ₁.comp σ)) * Bmᵀ)) k j * u.map (piW B.τ₁) k j)) := by
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm B.v₁ B.τ₁ _ (at_neg_hTens _ _ x u hxat)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add,
      GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm B.τ₁ X.J W.J hP.herm.herm hP.skew.skew x u hx0 hu1]
    rfl
  rw [hsymp, hco, GlobalTheory.LatVac.psiAt_apply]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hu0]
  ring

end GlobalTheory.HeisMultLin
