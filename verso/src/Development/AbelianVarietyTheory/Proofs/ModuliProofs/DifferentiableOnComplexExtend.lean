import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

noncomputable def complexExtend {O M : Type} [CommRing O] [Ring M] [Algebra ℂ M]
    (f : O →+* M) : ℂ ⊗[ℤ] O →ₐ[ℂ] M :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ M) f.toIntAlgHom
    (fun x y => Algebra.commute_algebraMap_left x (f y))

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Conclude with `Algebra.TensorProduct.lift_tmul _ _ _ c a`.
-/
theorem complexExtend_tmul {O M : Type} [CommRing O] [Ring M] [Algebra ℂ M]
    (f : O →+* M) (c : ℂ) (a : O) : complexExtend f (c ⊗ₜ a) = c • f a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ c a

/- English proof (translation)
Use `haveI : IsArtinianRing (ℂ ⊗[ℤ] O) := IsArtinianRing.of_finite ℂ _`. Use `haveI : IsSemisimpleRing (ℂ ⊗[ℤ] O) := IsArtinianRing.isSemisimpleRing_of_isReduced _`. Take `⟨f, hf, hI⟩` from `IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker (complexExtend τ))`. Establish `hf0 : complexExtend τ f = 0`. Establish `: f ∈ RingHom.ker (complexExtend τ)` using `hI ▸ Ideal.mem_span_singleton_self f`.

Conclude with `this`. Use `⟨1 - f, by simp [hf0], fun a => ?_⟩` and prove the remaining obligations. Establish `hk : ((1 : ℂ) ⊗ₜ[ℤ] a) - algebraMap ℂ (ℂ ⊗[ℤ] O) (τ a) ∈ RingHom.ker (complexExtend τ)`. Rewrite using `[RingHom.mem_ker, map_sub, complexExtend_tmul, AlgHom.commutes]`. Simplify using the standard rewrite rules.

Rewrite `hk` using `[hI, Ideal.mem_span_singleton']`. Take `⟨y, hy⟩` from `hk`. Rewrite using `[Algebra.smul_def, ← sub_eq_zero, ← sub_mul, ← hy, _root_.mul_assoc, mul_sub, _root_.mul_one, hf.eq, sub_self, mul_zero]`.
-/
theorem exists_eigen_element (O : Type) [CommRing O] [Module.Finite ℤ O]
    [IsReduced (ℂ ⊗[ℤ] O)] (τ : O →+* ℂ) :
    ∃ e : ℂ ⊗[ℤ] O, complexExtend τ e = 1 ∧ ∀ a : O, ((1 : ℂ) ⊗ₜ[ℤ] a) * e = τ a • e := by
  haveI : IsArtinianRing (ℂ ⊗[ℤ] O) := IsArtinianRing.of_finite ℂ _
  haveI : IsSemisimpleRing (ℂ ⊗[ℤ] O) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨f, hf, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (RingHom.ker (complexExtend τ))
  have hf0 : complexExtend τ f = 0 := by
    have : f ∈ RingHom.ker (complexExtend τ) := hI ▸ Ideal.mem_span_singleton_self f
    exact this
  refine ⟨1 - f, by simp [hf0], fun a => ?_⟩
  have hk : ((1 : ℂ) ⊗ₜ[ℤ] a) - algebraMap ℂ (ℂ ⊗[ℤ] O) (τ a) ∈
      RingHom.ker (complexExtend τ) := by
    rw [RingHom.mem_ker, map_sub, complexExtend_tmul, AlgHom.commutes]
    simp
  rw [hI, Ideal.mem_span_singleton'] at hk
  obtain ⟨y, hy⟩ := hk
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, ← hy, _root_.mul_assoc, mul_sub, _root_.mul_one, hf.eq,
    sub_self, mul_zero]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c a`. Simplify using `only [complexExtend_tmul, hf]`. Use extensionality with `i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, Matrix.diagonal_add]`.
-/
theorem complexExtend_diagonal {O : Type} [CommRing O] {g : ℕ}
    (f : O →+* Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (O →+* ℂ))
    (hf : ∀ a, f a = Matrix.diagonal (fun i => ty i a)) (x : ℂ ⊗[ℤ] O) :
    complexExtend f x = Matrix.diagonal (fun i => complexExtend (ty i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    simp only [complexExtend_tmul, hf]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.diagonal_add]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c a`. Simplify using `only [complexExtend_tmul, Matrix.smul_apply, smul_eq_mul]`. Conclude with `(hF a i j).const_mul c`.

Consider the case `add x y hx hy`. Simplify using `only [map_add, Matrix.add_apply]`. Conclude with `hx.add hy`.
-/
theorem differentiableOn_complexExtend {O : Type} [CommRing O] {g m : ℕ}
    {B : Set (Fin m → ℂ)} (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ))
    (hF : ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) (x : ℂ ⊗[ℤ] O) (i j : Fin g) :
    DifferentiableOn ℂ (fun b => complexExtend (F b) x i j) B := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    simp only [complexExtend_tmul, Matrix.smul_apply, smul_eq_mul]
    exact (hF a i j).const_mul c
  | add x y hx hy =>
    simp only [map_add, Matrix.add_apply]
    exact hx.add hy

/- English proof (translation)
Introduce `O _ g m B b₀ F ty hfin hred hB hb₀ hF hF₀`. Use `choose e he1 he using fun τ => exists_eigen_element O τ`. Set `h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ` to `fun b => Matrix.of fun i j => complexExtend (F b) (e (ty j)) i j`. Establish `hd : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B` using `fun i j => differentiableOn_complexExtend F hF _ i j`. Establish `h0 : h b₀ = 1`.

Use extensionality with `i j`. Simplify using `only [h, Matrix.of_apply, complexExtend_diagonal _ ty hF₀]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[he1]`.

Simplify using `[hij]`. Establish `hc : ContinuousOn h B` using `continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hd i j).continuousOn`. Establish `hdet : ContinuousOn (fun b => (h b).det) B` using `(Continuous.matrix_det continuous_id).comp_continuousOn hc`. Use `⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h, hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h0]⟩, Set.inter_subset_left, h0, fun i j => (hd i j).mono Set.inter_subset_left, ?_⟩` and prove the remaining obligations. Introduce and unpack `b ⟨-, hb⟩`.

Use `⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `key` using `congrArg (fun x => complexExtend (F b) x i j) (he (ty j) a)`. Simplify using `only [map_mul, map_smul, complexExtend_tmul, one_smul, Matrix.smul_apply, smul_eq_mul] at key`. Rewrite using `[Matrix.mul_diagonal, mul_comm]`.

Conclude with `key`.
-/
theorem holomorphic_diagonalisation :
    ∀ (O : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ] O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a) := by
  intro O _ g m B b₀ F ty hfin hred hB hb₀ hF hF₀
  choose e he1 he using fun τ => exists_eigen_element O τ
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => complexExtend (F b) (e (ty j)) i j
  have hd : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := fun i j =>
    differentiableOn_complexExtend F hF _ i j
  have h0 : h b₀ = 1 := by
    ext i j
    simp only [h, Matrix.of_apply, complexExtend_diagonal _ ty hF₀]
    by_cases hij : i = j
    · subst hij; simp [he1]
    · simp [hij]
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hd i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h0]⟩,
    Set.inter_subset_left, h0, fun i j => (hd i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  ext i j
  have key := congrArg (fun x => complexExtend (F b) x i j) (he (ty j) a)
  simp only [map_mul, map_smul, complexExtend_tmul, one_smul, Matrix.smul_apply,
    smul_eq_mul] at key
  rw [Matrix.mul_diagonal, mul_comm]
  exact key

end GlobalTheory
