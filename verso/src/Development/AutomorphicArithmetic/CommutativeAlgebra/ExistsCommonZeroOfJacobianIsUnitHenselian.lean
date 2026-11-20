import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionLiftOfEtaleOfHenselian

noncomputable section
open IsLocalRing UpperTheory.Et

/- English proof (translation)
Set `I` to `Ideal.span (Set.range F)`. Set `d` to `Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det`. Set `P1` to `Algebra.PreSubmersivePresentation.naive (v := F) (id : Fin n → Fin n) Function.injective_id`. Set `P2` to `Algebra.PreSubmersivePresentation.localizationAway (Localization.Away d) d`. Establish `hJ : P1.jacobian = d`.

Rewrite using `[P1.jacobian_eq_jacobiMatrix_det]`. Establish `hM : P1.jacobiMatrix = Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)`. Use extensionality with `i j`. Simplify using `[P1]`. Rewrite using `[hM, Algebra.Generators.algebraMap_apply]`.

Establish `hE : MvPolynomial.aeval P1.val = Ideal.Quotient.mkₐ A I` using `MvPolynomial.algHom_ext fun i => by simp [P1, I, Algebra.Generators.naive]`. Conclude with `congrFun (congrArg DFunLike.coe hE) _`. Set `P : Algebra.SubmersivePresentation A (Localization.Away d) (Unit ⊕ Fin n) (Unit ⊕ Fin n)` to `{ P2.comp P1 with jacobian_isUnit := by`. Rewrite using `[Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian, hJ]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit d).mul (IsLocalization.Away.algebraMap_isUnit d) }`.

Establish `: Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away d)` using `P.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])`. Use `infer_instance`.
-/
private theorem etale_away_jacobian (A : Type) [CommRing A] (n : ℕ)
    (F : Fin n → MvPolynomial (Fin n) A) :
    Algebra.Etale A (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det)) := by
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  let P1 := Algebra.PreSubmersivePresentation.naive (v := F) (id : Fin n → Fin n)
    Function.injective_id
  let P2 := Algebra.PreSubmersivePresentation.localizationAway (Localization.Away d) d
  have hJ : P1.jacobian = d := by
    rw [P1.jacobian_eq_jacobiMatrix_det]
    have hM : P1.jacobiMatrix = Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t) := by
      ext i j
      simp [P1]
    rw [hM, Algebra.Generators.algebraMap_apply]
    have hE : MvPolynomial.aeval P1.val = Ideal.Quotient.mkₐ A I :=
      MvPolynomial.algHom_ext fun i => by simp [P1, I, Algebra.Generators.naive]
    exact congrFun (congrArg DFunLike.coe hE) _
  let P : Algebra.SubmersivePresentation A (Localization.Away d) (Unit ⊕ Fin n) (Unit ⊕ Fin n) :=
    { P2.comp P1 with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian, hJ]
        exact (IsLocalization.Away.algebraMap_isUnit d).mul
          (IsLocalization.Away.algebraMap_isUnit d) }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away d) :=
    P.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  infer_instance

/- English proof (translation)
Introduce `A _ _ n F hF hU`. Set `I` to `Ideal.span (Set.range F)`. Set `d` to `Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det`. Use `haveI := etale_away_jacobian A n F`. Set `ψ : MvPolynomial (Fin n) A →ₐ[A] ResidueField A` to `(Algebra.ofId A (ResidueField A)).comp (MvPolynomial.aeval (0 : Fin n → A))`.

Establish `hψ : ∀ p, ψ p = residue A (MvPolynomial.eval 0 p)` using `fun p => by`. Simplify using `[ψ, MvPolynomial.coe_aeval_eq_eval, IsLocalRing.ResidueField.algebraMap_eq]`. Establish `hI : ∀ a ∈ I, ψ a = 0`. Introduce `a ha`. Establish `hle : I ≤ RingHom.ker ψ`.

Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, hψ, residue_eq_zero_iff]`. Conclude with `hF i`. Conclude with `hle ha`.

Set `π0 : (MvPolynomial (Fin n) A ⧸ I) →ₐ[A] ResidueField A` to `Ideal.Quotient.liftₐ I ψ hI`. Establish `hπ0 : ∀ p, π0 (Ideal.Quotient.mk I p) = residue A (MvPolynomial.eval 0 p)` using `fun p => by`. Rewrite using `[← hψ]`. Both sides reduce to the same expression. Establish `hd : IsUnit (π0 d)`.

Rewrite using `[hπ0]`. Establish `hdet : MvPolynomial.eval 0 (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det = (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det`. Rewrite using `[RingHom.map_det, ← Matrix.det_transpose]`. Use `congr 1`. Rewrite using `[hdet]`.

Conclude with `hU.map (residue A)`. Set `π : Localization.Away d →ₐ[A] ResidueField A` to `IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := π0) (by`. Introduce and unpack `⟨y, k, rfl⟩`. Simplify using `using hd.pow k)`. Take `⟨σ, hσ⟩` from `UpperTheory.exists_section_lift_of_etale_of_henselian A (Localization.Away d) π`.

Set `φ : MvPolynomial (Fin n) A →ₐ[A] A` to `(σ.comp (IsScalarTower.toAlgHom A _ (Localization.Away d))).comp (Ideal.Quotient.mkₐ A I)`. Establish `hφ : ∀ p, φ p = MvPolynomial.eval (fun j => φ (MvPolynomial.X j)) p`. Introduce `p`. Rewrite using `[← MvPolynomial.coe_aeval_eq_eval]`. Conclude with `congrFun (congrArg DFunLike.coe (MvPolynomial.algHom_ext (fun j => by simp) : φ = MvPolynomial.aeval _)) p`.

Use `⟨fun j => φ (MvPolynomial.X j), fun i => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ]`. Establish `h0 : Ideal.Quotient.mk I (F i) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)`. Simplify using `[φ, h0]`. Rewrite using `[← residue_eq_zero_iff] show residue A (σ (algebraMap _ (Localization.Away d) (Ideal.Quotient.mk I (MvPolynomial.X j)))) = 0`.

Rewrite using `[hσ]`. Simplify using `[π, hπ0]`.
-/
theorem UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian :
    ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (n : ℕ) (F : Fin n → MvPolynomial (Fin n) A),
      (∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A) → IsUnit (Matrix.det (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)))) →
      ∃ x : Fin n → A, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ ∀ j, x j ∈ maximalIdeal A := by
  intro A _ _ n F hF hU
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  haveI := etale_away_jacobian A n F
  let ψ : MvPolynomial (Fin n) A →ₐ[A] ResidueField A :=
    (Algebra.ofId A (ResidueField A)).comp (MvPolynomial.aeval (0 : Fin n → A))
  have hψ : ∀ p, ψ p = residue A (MvPolynomial.eval 0 p) := fun p => by
    simp [ψ, MvPolynomial.coe_aeval_eq_eval, IsLocalRing.ResidueField.algebraMap_eq]
  have hI : ∀ a ∈ I, ψ a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker ψ := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hψ, residue_eq_zero_iff]
      exact hF i
    exact hle ha
  let π0 : (MvPolynomial (Fin n) A ⧸ I) →ₐ[A] ResidueField A := Ideal.Quotient.liftₐ I ψ hI
  have hπ0 : ∀ p, π0 (Ideal.Quotient.mk I p) = residue A (MvPolynomial.eval 0 p) := fun p => by
    rw [← hψ]
    rfl
  have hd : IsUnit (π0 d) := by
    rw [hπ0]
    have hdet : MvPolynomial.eval 0 (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det =
        (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
      rw [RingHom.map_det, ← Matrix.det_transpose]
      congr 1
    rw [hdet]
    exact hU.map (residue A)
  let π : Localization.Away d →ₐ[A] ResidueField A :=
    IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := π0) (by
      rintro ⟨y, k, rfl⟩
      simpa using hd.pow k)
  obtain ⟨σ, hσ⟩ := UpperTheory.exists_section_lift_of_etale_of_henselian A (Localization.Away d) π
  let φ : MvPolynomial (Fin n) A →ₐ[A] A :=
    (σ.comp (IsScalarTower.toAlgHom A _ (Localization.Away d))).comp (Ideal.Quotient.mkₐ A I)
  have hφ : ∀ p, φ p = MvPolynomial.eval (fun j => φ (MvPolynomial.X j)) p := by
    intro p
    rw [← MvPolynomial.coe_aeval_eq_eval]
    exact congrFun (congrArg DFunLike.coe
      (MvPolynomial.algHom_ext (fun j => by simp) : φ = MvPolynomial.aeval _)) p
  refine ⟨fun j => φ (MvPolynomial.X j), fun i => ?_, fun j => ?_⟩
  · rw [← hφ]
    have h0 : Ideal.Quotient.mk I (F i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    simp [φ, h0]
  · rw [← residue_eq_zero_iff]
    show residue A (σ (algebraMap _ (Localization.Away d)
      (Ideal.Quotient.mk I (MvPolynomial.X j)))) = 0
    rw [hσ]
    simp [π, hπ0]

end
