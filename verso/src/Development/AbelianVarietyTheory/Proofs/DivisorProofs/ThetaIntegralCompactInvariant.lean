import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaKInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `A' : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA]`.

Use extensionality with `i j`. Simplify using `[A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]`. Establish `h2 : (A'ᵀ * M * A'.map star).det ≠ 0`. Rewrite using `[h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[Matrix.det_neg]`.

Introduce `h0`. Apply `h2` to reduce the goal to its premises. Rewrite using `[Matrix.det_mul, Matrix.det_mul, h0]`. Simplify using the standard rewrite rules.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

/- English proof (translation)
Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Use `det_ne_zero_of_hasSig (hX.sig w)` as an intermediate fact. Introduce `h0`. Apply `this` to reduce the goal to its premises. Establish `e` using `RingHom.map_det (B.emb w).1 X.J`.

Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← e, h0, map_zero]`.
-/
theorem det_ne_zero_of_isHerm {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) :
    X.J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_zero_of_hasSig (hX.sig w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 X.J
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, h0, map_zero]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_eq_sigR (σ : E →ₐ[F] E) (x : AE F E) : cA σ x = sigR (AF F) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Use extensionality with `g`. Establish `hc : (g : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = (g : Matrix (Fin n) (Fin n) (AE F E)).map (sigR (AF F) σ)`. Use extensionality with `i j`. Conclude with `cA_eq_sigR σ _`. Establish `hJ : JR (AF F) Jᵀ = (incM F J)ᵀ` using `rfl`.

Express the relevant statement in the definitionally equal form `(g : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J * (g : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J ↔ Formalism.UG.cT (sigR (AF F) σ) (g : Matrix (Fin n) (Fin n) (AE F E)) * JR (AF F) Jᵀ * (g : Matrix (Fin n) (Fin n) (AE F E)) = JR (AF F) Jᵀ`. Rewrite using `[hc, hJ, Formalism.UG.cT]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg Matrix.transpose h` as an intermediate fact.

Simplify `this` using `[Matrix.transpose_mul, Matrix.mul_assoc]`. Introduce `h`. Use `congrArg Matrix.transpose h` as an intermediate fact. Simplify `this` using `[Matrix.transpose_mul, Matrix.mul_assoc]`.
-/
theorem UG_eq_HR (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    UG (cA σ) (incM F J) = HR (AF F) σ Jᵀ := by
  ext g
  have hc : (g : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = (g : Matrix (Fin n) (Fin n) (AE F E)).map (sigR (AF F) σ) := by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  change (g : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J * (g : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J ↔
    Formalism.UG.cT (sigR (AF F) σ) (g : Matrix (Fin n) (Fin n) (AE F E)) * JR (AF F) Jᵀ * (g : Matrix (Fin n) (Fin n) (AE F E)) = JR (AF F) Jᵀ
  rw [hc, hJ, Formalism.UG.cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

end GlobalTheory.ThetaKInv

namespace GlobalTheory.ThetaKInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hJ : IsHermND σ Jᵀ` using `⟨fun i j => by simp [Matrix.transpose_apply, herm], by rwa [Matrix.det_transpose]⟩`. Take `⟨hU, -⟩` from `GlobalTheory.AdelicStabUnimod.unimodularOver_adele F E σ hcm n Jᵀ hJ`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`.

Use `haveI : IsTopologicalGroup (UA σ J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F J)))`. Use `haveI : BorelSpace (UA σ J) := ⟨rfl⟩`. Set `e : UA σ J ≃* HA (AF F) σ Jᵀ` to `MulEquiv.subgroupCongr (GlobalTheory.ThetaKInv.UG_eq_HR σ J)`. Establish `h1 : Continuous e` using `continuous_induced_rng.2 continuous_subtype_val`. Establish `h2 : Continuous e.symm` using `continuous_induced_rng.2 continuous_subtype_val`.

Conclude with `(GlobalTheory.AdelicStabUnimod.isUnimodularLC_of_equiv hU e h1 h2).2.2.2.2.2.2 μ inferInstance`.
-/
theorem isMulRightInvariant (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (herm : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  have hJ : IsHermND σ Jᵀ := ⟨fun i j => by simp [Matrix.transpose_apply, herm], by rwa [Matrix.det_transpose]⟩
  obtain ⟨hU, -⟩ := GlobalTheory.AdelicStabUnimod.unimodularOver_adele F E σ hcm n Jᵀ hJ
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F J)))
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  let e : UA σ J ≃* HA (AF F) σ Jᵀ := MulEquiv.subgroupCongr (GlobalTheory.ThetaKInv.UG_eq_HR σ J)
  have h1 : Continuous e := continuous_induced_rng.2 continuous_subtype_val
  have h2 : Continuous e.symm := continuous_induced_rng.2 continuous_subtype_val
  exact (GlobalTheory.AdelicStabUnimod.isUnimodularLC_of_equiv hU e h1 h2).2.2.2.2.2.2 μ inferInstance

end GlobalTheory.ThetaKInv

namespace GlobalTheory.ThetaKInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`. Use `haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))`. Use `haveI : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E)) (fun _ _ h => Units.ext h)`. Set `f` to `Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))`. Establish `hr : (Set.range f).Countable` using `Set.countable_range f`.

Use `haveI : Countable (Set.range f) := hr.to_subtype`. Use `Function.Injective.countable (f := fun γ : ratU σ J => (⟨γ.1.1, γ.2⟩ : Set.range f)) ?_` and prove the remaining obligations. Introduce `a b hab`. Use `congrArg Subtype.val hab` as an intermediate fact. Conclude with `Subtype.ext (Subtype.ext (by simpa using this))`.
-/
theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E)) (fun _ _ h => Units.ext h)
  let f := Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))
  have hr : (Set.range f).Countable := Set.countable_range f
  haveI : Countable (Set.range f) := hr.to_subtype
  refine Function.Injective.countable (f := fun γ : ratU σ J => (⟨γ.1.1, γ.2⟩ : Set.range f)) ?_
  intro a b hab
  have := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext (by simpa using this))

end GlobalTheory.ThetaKInv

namespace GlobalTheory.ThetaKInv

end GlobalTheory.ThetaKInv
