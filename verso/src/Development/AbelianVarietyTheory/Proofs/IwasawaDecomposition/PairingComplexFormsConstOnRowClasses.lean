import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

variable {X : Fields} {n : ℕ}
open Matrix

/- English proof (translation)
Simplify using `[ufGL, toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]`.
-/
theorem ufGL_apply_single (γ : UF X.E n) (i j : Fin n) :
    ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) i j = (γ.1 (Pi.single j 1)) i := by
  simp [ufGL, toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

/- English proof (translation)
Use extensionality with `j k`. Establish `h` using `γ.2 (Pi.single j 1) (Pi.single k 1)`. Simplify using `only [hStd, LinearMap.mk₂'ₛₗ_apply] at h`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.conjTranspose_apply, ufGL_apply_single]`.

Rewrite using `[h]`. Simplify using `only [Pi.single_apply, Matrix.one_apply]`. Simplify using `[eq_comm]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ufGL_unitary (γ : UF X.E n) :
    ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)ᴴ * (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E) = 1 := by
  ext j k
  have h := γ.2 (Pi.single j 1) (Pi.single k 1)
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, ufGL_apply_single]
  rw [h]
  simp only [Pi.single_apply, Matrix.one_apply]
  simp [eq_comm]
  split_ifs <;> simp

/- English proof (translation)
Use `set A := Formalism.UG.bc φ (ufGL X.E n γ)`. Establish `hA : (A : Matrix (Fin n) (Fin n) ℂ) = (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E).map φ` using `rfl`. Establish `h1 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * (A : Matrix (Fin n) (Fin n) ℂ) = 1`. Use `congrArg (fun M => M.map φ) (ufGL_unitary γ)` as an intermediate fact. Simplify using `only [Matrix.map_mul, Matrix.map_one _ φ.map_zero φ.map_one] at this`.

Rewrite using `[← this, hA]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, hX.conjE]`. Apply `Units.ext` to reduce the goal to its premises.

Use `show (A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ`. Establish `h2 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Use `_ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Rewrite using `[← h2, Matrix.transpose_transpose]`.
-/
theorem bc_conj_unitary (hX : X.Ok) (φ : X.E →+* ℂ) (γ : UF X.E n) :
    Formalism.UG.bc (starRingEnd ℂ) (Formalism.UG.bc φ (ufGL X.E n γ)) = inside₂ ℂ n (Formalism.UG.bc φ (ufGL X.E n γ)) := by
  set A := Formalism.UG.bc φ (ufGL X.E n γ)
  have hA : (A : Matrix (Fin n) (Fin n) ℂ) = (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E).map φ := rfl
  have h1 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * (A : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have := congrArg (fun M => M.map φ) (ufGL_unitary γ)
    simp only [Matrix.map_mul, Matrix.map_one _ φ.map_zero φ.map_one] at this
    rw [← this, hA]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hX.conjE]
  apply Units.ext
  show (A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ
  have h2 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    calc _ = ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * ((A : Matrix (Fin n) (Fin n) ℂ) * ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [← h2, Matrix.transpose_transpose]

/- English proof (translation)
Rewrite using `[rhoC_apply]`. Use `(GlobalTheory.ValCmp.use₂ (starRingEnd ℂ) lam _ p).trans ?_` and prove the remaining obligations. Use `congr 2`. Use function extensionality and compare the values at `τ`. Conclude with `bc_conj_unitary hX (embAt σ X.emb τ) γ`.
-/
theorem map_conj_rhoC (hX : X.Ok) (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n) (γ : UF X.E n) (p : Pol ℂ X.Tau n) :
    MvPolynomial.map (starRingEnd ℂ) (rhoC σ lam γ p) =
      actP lam (invTrK (embGL (embAt σ X.emb) (ufGL X.E n γ))) (MvPolynomial.map (starRingEnd ℂ) p) := by
  rw [rhoC_apply]
  refine (GlobalTheory.ValCmp.use₂ (starRingEnd ℂ) lam _ p).trans ?_
  congr 2
  funext τ
  exact bc_conj_unitary hX (embAt σ X.emb τ) γ

/- English proof (translation)
Rewrite using `[map_conj_rhoC hX σ lam γ p, rhoC_apply]`. Conclude with `pairingBInvariantK_holds ℂ X.Tau n lam _ _ q`.
-/
theorem pairB_rhoC (hX : X.Ok) (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n) (γ : UF X.E n) (p q : Pol ℂ X.Tau n) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (rhoC σ lam γ p)) (rhoC σ lam γ q) =
      pairB lam (MvPolynomial.map (starRingEnd ℂ) p) q := by
  rw [map_conj_rhoC hX σ lam γ p, rhoC_apply]
  exact pairingBInvariantK_holds ℂ X.Tau n lam _ _ q

/- English proof (translation)
Take `⟨N, hN, hp⟩` from `(isOfFinOrder_of_finite h).exists_pow_eq_one`. Establish `h1 : (σ (Λ.chr h : X.Kˣ)) ^ N = 1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hp, map_one, Units.val_one, map_one]`. Establish `h2` using `Complex.norm_eq_one_of_pow_eq_one h1 hN.ne'`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]`.

Simplify using the standard rewrite rules.
-/
theorem conj_mul_self_chr {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (h : ↥Λ.grp) :
    starRingEnd ℂ (σ (Λ.chr h : X.Kˣ)) * σ (Λ.chr h : X.Kˣ) = 1 := by
  obtain ⟨N, hN, hp⟩ := (isOfFinOrder_of_finite h).exists_pow_eq_one
  have h1 : (σ (Λ.chr h : X.Kˣ)) ^ N = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hp, map_one, Units.val_one, map_one]
  have h2 := Complex.norm_eq_one_of_pow_eq_one h1 hN.ne'
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]
  simp

/- English proof (translation)
Introduce `B X I hX a F G d d' h`. Take `⟨g, rfl⟩` from `((rowS I a).cls_eq_iff _ _).1 h`. Establish `hF` using `(F.2 d').2 g`. Establish `hG` using `(G.2 d').2 g`. Use `letI := (rowS I a).actD`.

Use `erw [hF, hG]`. Rewrite using `[map_conj_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply]`. Rewrite using `[pairB_rhoC hX, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (B.embLL _)]`. Establish `hc` using `conj_mul_self_chr B.embLL (rowTy I.Ch I.sel (I.tup a) I.Ps).inv g.2`. Rewrite using `[hc, one_mul]`.
-/
theorem pairB_conj_cls_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a)
    (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' →
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) =
      pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := by
  intro B X I hX a F G d d' h
  obtain ⟨g, rfl⟩ := ((rowS I a).cls_eq_iff _ _).1 h
  have hF := (F.2 d').2 g
  have hG := (G.2 d').2 g
  letI := (rowS I a).actD
  erw [hF, hG]
  rw [map_conj_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [pairB_rhoC hX, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (B.embLL _)]
  have hc := conj_mul_self_chr B.embLL (rowTy I.Ch I.sel (I.tup a) I.Ps).inv g.2
  rw [hc, one_mul]

/- English proof (translation)
The claim follows from `pairB_conj_cls_eq`.
-/
example : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' → pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) = pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := pairB_conj_cls_eq

end GlobalTheory.Mem.Df
