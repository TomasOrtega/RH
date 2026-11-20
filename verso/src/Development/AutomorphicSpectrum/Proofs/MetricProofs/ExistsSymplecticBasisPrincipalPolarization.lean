import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice

open scoped Matrix

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun y w => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im)
    (fun a b w => by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct])
    (fun c a w => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul,
        Complex.smul_im])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im := rfl

/- English proof (translation)
Simplify using `[imForm_apply, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_neg, dotProduct_neg]`.
-/
theorem imForm_smul_I {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    imForm Hm z (Complex.I • z) = -(ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re := by
  simp [imForm_apply, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul,
    dotProduct_smul, Matrix.mulVec_neg, dotProduct_neg]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Assume the negation of the conclusion as `h0`. Establish `h1` using `imForm_smul_I Hm z`. Rewrite `h1` using `[hz]`.

Use `hpos z h0` as an intermediate fact. Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem imForm_injective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Injective (imForm Hm) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have h1 := imForm_smul_I Hm z
  rw [hz] at h1
  have := hpos z h0
  simp at h1
  linarith

/- English proof (translation)
The claim follows from `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 (imForm_injective Hm hpos)`.
-/
theorem imForm_surjective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Surjective (imForm Hm) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 (imForm_injective Hm hpos)

/- English proof (translation)
Introduce `g Λ Hm hdisc hspan hH hpos hint hdual`. Use `haveI : IsZLattice ℝ Λ := ⟨hspan⟩`. Use `choose k hk using hint`. Set `Ef : LinearMap.BilinForm ℤ Λ` to `LinearMap.mk₂ ℤ (fun x y => k x y) (fun x x' y => by`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises.

Use `push_cast`. Simplify using `only [← hk, ← imForm_apply]`. Use the proof step `simp)`. Use the proof step `(fun c x y => by`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises.

Simplify using `only [smul_eq_mul]`. Use `push_cast`. Simplify using `only [← hk, ← imForm_apply]`. Simplify using `[← Int.cast_smul_eq_zsmul ℝ c])`. Use the proof step `(fun x y y' => by`.

Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Use `push_cast`. Simplify using `only [← hk, ← imForm_apply]`. Use the proof step `simp)`. Use the proof step `(fun c x y => by`.

Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Simplify using `only [smul_eq_mul]`. Use `push_cast`. Simplify using `only [← hk, ← imForm_apply]`. Simplify using `[← Int.cast_smul_eq_zsmul ℝ c])`.

Establish `hE : ∀ l m : Λ, (Ef l m : ℝ) = imForm Hm (l : Fin g → ℂ) (m : Fin g → ℂ)` using `fun l m => (hk l m).symm`. Establish `hanti : ∀ l m : Λ, Ef m l = - Ef l m` using `fun l m => by`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Establish `h1` using `congrArg Complex.im (GlobalTheory.SiegelNormalForm.form_conj hH (l : Fin g → ℂ) m)`. Simplify using `only [Complex.star_def, Complex.conj_im] at h1`.

Use `push_cast`. Rewrite using `[hE, hE, imForm_apply, imForm_apply]`. Conclude with `h1.symm`. Establish `halt : Ef.IsAlt` using `fun l => by`. Use `hanti l l` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hinj : Function.Injective Ef`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `l hl`. Establish `hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤ LinearMap.ker (imForm Hm (l : Fin g → ℂ))`.

Rewrite using `[Submodule.span_le]`. Introduce `m hm`. Use `hE l ⟨m, hm⟩` as an intermediate fact. Rewrite `this` using `[hl]`. Simplify using `using this.symm`.

Rewrite `hle` using `[hspan]`. Establish `h0 : imForm Hm (l : Fin g → ℂ) = 0` using `LinearMap.ext fun y => hle (Submodule.mem_top)`. Conclude with `Subtype.ext ((injective_iff_map_eq_zero _).1 (imForm_injective Hm hpos) _ h0)`. Establish `hsurj : Function.Surjective Ef`. Introduce `φ`.

Set `b` to `Module.finBasis ℤ Λ`. Set `bR` to `b.ofZLatticeBasis ℝ Λ`. Set `ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ` to `bR.constr ℝ fun i => (φ (b i) : ℝ)`. Establish `hψ : ∀ y : Λ, ψ (y : Fin g → ℂ) = (φ y : ℝ)`. Introduce `y`.

Establish `hb : ∀ i, ψ (b i : Fin g → ℂ) = (φ (b i) : ℝ)` using `fun i => by`. Establish `h` using `bR.constr_basis ℝ (fun i => (φ (b i) : ℝ)) i`. Rewrite `h` using `[show bR i = (b i : Fin g → ℂ) by simp [bR]]`. Then use the resulting hypothesis. Use `conv_lhs => rw [← b.sum_repr y]`. Use `conv_rhs => rw [← b.sum_repr y]`.

Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, map_sum, map_zsmul, hb]`. Simplify using the standard rewrite rules. Take `⟨w, hw⟩` from `imForm_surjective Hm hpos ψ`. Establish `hwy : ∀ y : Λ, imForm Hm w (y : Fin g → ℂ) = (φ y : ℝ)` using `fun y => by rw [hw, hψ]`. Establish `hwΛ : w ∈ Λ` using `hdual w fun l => ⟨φ l, hwy l⟩`.

Use `⟨⟨w, hwΛ⟩, LinearMap.ext fun y => ?_⟩` and prove the remaining obligations. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Rewrite using `[hE, hwy]`. Establish `hrank : Module.finrank ℤ Λ = 2 * g`. Rewrite using `[ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]`.

Simplify using `[mul_comm]`. Take `⟨bs, hbs⟩` from `GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg (GlobalTheory.bijective_neg_bilinForm ⟨hinj, hsurj⟩) hrank`. Establish `hval : ∀ α β, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = (Ef (bs α) (bs β) : ℝ)` using `fun α β => (hE _ _).symm`. Use `⟨bs, ?_⟩` and prove the remaining obligations. Establish `hee : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inl j)) = 0` using `fun i j => by`.

Use `hbs.left_left i j` as an intermediate fact. Simplify using `using this`. Establish `hff : ∀ i j, Ef (bs (Sum.inr i)) (bs (Sum.inr j)) = 0` using `fun i j => by`. Use `hbs.right_right i j` as an intermediate fact. Simplify using `using this`.

Establish `hef : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inr j)) = if i = j then -1 else 0` using `fun i j => by`. Use `hbs.left_right i j` as an intermediate fact. Simplify using `only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this`. Apply the tactic sequence `rw [this]; split_ifs <;> simp`. Introduce and unpack `(i | i) (j | j)`.

Rewrite using `[hval, hee]`. Simplify using `[Matrix.J]`. Rewrite using `[hval, hef]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.J, h, Matrix.one_apply]`. Rewrite using `[hval, hanti, hef]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Matrix.J]`. Simplify using `[Matrix.J, h, Ne.symm h, Matrix.one_apply]`. Rewrite using `[hval, hff]`.

Simplify using `[Matrix.J]`.
-/
theorem exists_symplectic_basis : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k) →
    (∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) →
    ∃ bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, ∀ α β,
      (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β := by
  intro g Λ Hm hdisc hspan hH hpos hint hdual
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ (fun x y => k x y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
    (fun x y y' => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
  have hE : ∀ l m : Λ, (Ef l m : ℝ) = imForm Hm (l : Fin g → ℂ) (m : Fin g → ℂ) :=
    fun l m => (hk l m).symm
  have hanti : ∀ l m : Λ, Ef m l = - Ef l m := fun l m => by
    apply Int.cast_injective (α := ℝ)
    have h1 := congrArg Complex.im (GlobalTheory.SiegelNormalForm.form_conj hH (l : Fin g → ℂ) m)
    simp only [Complex.star_def, Complex.conj_im] at h1
    push_cast
    rw [hE, hE, imForm_apply, imForm_apply]
    exact h1.symm
  have halt : Ef.IsAlt := fun l => by
    have := hanti l l
    omega
  have hinj : Function.Injective Ef := by
    rw [injective_iff_map_eq_zero]
    intro l hl
    have hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤
        LinearMap.ker (imForm Hm (l : Fin g → ℂ)) := by
      rw [Submodule.span_le]
      intro m hm
      have := hE l ⟨m, hm⟩
      rw [hl] at this
      simpa using this.symm
    rw [hspan] at hle
    have h0 : imForm Hm (l : Fin g → ℂ) = 0 := LinearMap.ext fun y => hle (Submodule.mem_top)
    exact Subtype.ext ((injective_iff_map_eq_zero _).1 (imForm_injective Hm hpos) _ h0)
  have hsurj : Function.Surjective Ef := by
    intro φ
    let b := Module.finBasis ℤ Λ
    let bR := b.ofZLatticeBasis ℝ Λ
    let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ := bR.constr ℝ fun i => (φ (b i) : ℝ)
    have hψ : ∀ y : Λ, ψ (y : Fin g → ℂ) = (φ y : ℝ) := by
      intro y
      have hb : ∀ i, ψ (b i : Fin g → ℂ) = (φ (b i) : ℝ) := fun i => by
        have h := bR.constr_basis ℝ (fun i => (φ (b i) : ℝ)) i
        rwa [show bR i = (b i : Fin g → ℂ) by simp [bR]] at h
      conv_lhs => rw [← b.sum_repr y]
      conv_rhs => rw [← b.sum_repr y]
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, map_sum, map_zsmul, hb]
      simp
    obtain ⟨w, hw⟩ := imForm_surjective Hm hpos ψ
    have hwy : ∀ y : Λ, imForm Hm w (y : Fin g → ℂ) = (φ y : ℝ) := fun y => by rw [hw, hψ]
    have hwΛ : w ∈ Λ := hdual w fun l => ⟨φ l, hwy l⟩
    refine ⟨⟨w, hwΛ⟩, LinearMap.ext fun y => ?_⟩
    apply Int.cast_injective (α := ℝ)
    rw [hE, hwy]
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg
    (GlobalTheory.bijective_neg_bilinForm ⟨hinj, hsurj⟩) hrank
  have hval : ∀ α β, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (bs α : Fin g → ℂ)
      (bs β : Fin g → ℂ)).im = (Ef (bs α) (bs β) : ℝ) := fun α β => (hE _ _).symm
  refine ⟨bs, ?_⟩
  have hee : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inl j)) = 0 := fun i j => by
    have := hbs.left_left i j
    simpa using this
  have hff : ∀ i j, Ef (bs (Sum.inr i)) (bs (Sum.inr j)) = 0 := fun i j => by
    have := hbs.right_right i j
    simpa using this
  have hef : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inr j)) = if i = j then -1 else 0 := fun i j => by
    have := hbs.left_right i j
    simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
    rw [this]; split_ifs <;> simp
  rintro (i | i) (j | j)
  · rw [hval, hee]; simp [Matrix.J]
  · rw [hval, hef]
    by_cases h : i = j <;> simp [Matrix.J, h, Matrix.one_apply]
  · rw [hval, hanti, hef]
    by_cases h : i = j
    · subst h; simp [Matrix.J]
    · simp [Matrix.J, h, Ne.symm h, Matrix.one_apply]
  · rw [hval, hff]; simp [Matrix.J]

end GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice
