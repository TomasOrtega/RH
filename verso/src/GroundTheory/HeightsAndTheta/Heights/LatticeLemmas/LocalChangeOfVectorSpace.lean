import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.LatticeOfLocalisationsHyps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct IsDedekindDomain
  GroundTheory.Heights₂.Heights.ComplexAt

universe u v

noncomputable section

set_option linter.unusedSectionVars false

namespace LocalChangeEq

def AAt (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] : Prop :=
  ∀ (Nm : HermitianNorms K V) (M₁ M₂ : FullLattice K V)
    (g : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    {v | g v ≠ 1}.Finite →
    (∀ v, (Heights.localLattice v M₂.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      g v '' Heights.localLattice v M₁.carrier) →
      (Nm.bundle M₂).deg = (Nm.bundle M₁).deg +
        (∑ᶠ v, Real.log ‖LinearMap.det
          ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖) /
          Module.finrank ℚ K

def BAt (K : Type*) [Field K] [NumberField K] (r : ℕ) : Prop :=
  ∀ (H : HermitianSpace K r)
    (M₁ M₂ : Submodule (𝓞 K) (Fin r → K)) (h₁ : IsLattice M₁) (h₂ : IsLattice M₂)
    (g : ∀ v : HeightOneSpectrum (𝓞 K), Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)),
    {v | g v ≠ 1}.Finite →
    (∀ v, localLattice v M₂ = (localLattice v M₁).map (glMap v (g v))) →
    deg (H.lattice M₂ h₂.1) = deg (H.lattice M₁ h₁.1) +
      (∑ᶠ v, Real.log ‖(g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det‖) /
        Module.finrank ℚ K

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [coordInv, map_sum, Finset.sum_apply, coordMap_tmul, AlgEquiv.symm_apply_apply, Pi.single_apply]`. Simplify using the standard rewrite rules.
-/
theorem coordMap_coordInv (r : ℕ) (σ : K →+* ℂ) (w : Fin r → ℂ) :
    coordMap r σ (coordInv σ w) = w := by
  funext j
  simp only [coordInv, map_sum, Finset.sum_apply, coordMap_tmul, AlgEquiv.symm_apply_apply,
    Pi.single_apply]
  simp

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, star_zero]`. Consider the case `tmul z l`. Use extensionality with `i`. Rewrite using `[conjMap_tmul]`.

Express the relevant statement in the definitionally equal form `coordMap r (conjugate σ) (conj σ z ⊗ₜ l) i = starRingEnd ℂ (coordMap r σ (z ⊗ₜ l) i)`. Rewrite using `[coordMap_tmul, coordMap_tmul, map_mul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]`.
-/
theorem coordMap_conjMap (r : ℕ) (σ : K →+* ℂ) (t : Fibre σ (Fin r → K)) :
    coordMap r (conjugate σ) (conjMap σ (Fin r → K) t) = star (coordMap r σ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | tmul z l =>
    ext i
    rw [conjMap_tmul]
    change coordMap r (conjugate σ) (conj σ z ⊗ₜ l) i = starRingEnd ℂ (coordMap r σ (z ⊗ₜ l) i)
    rw [coordMap_tmul, coordMap_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {r : ℕ} (φ : V ≃ₗ[K] (Fin r → K))

def intEquiv : V ≃ₗ[𝓞 K] (Fin r → K) := φ.restrictScalars (𝓞 K)

def fibreCoord (σ : K →+* ℂ) : Fibre σ V →ₗ[ℂ] (Fin r → ℂ) :=
  coordMap r σ ∘ₗ fibreMap σ (intEquiv φ).toLinearMap

/- English proof (translation)
Use `⟨(coordMap_injective σ).comp (fibreMap_injective σ (intEquiv φ).injective), ?_⟩` and prove the remaining obligations. Introduce `w`. Take `⟨t, ht⟩` from `LinearMap.lTensor_surjective (ComplexAt σ) (intEquiv φ).surjective (coordInv σ w)`. Use `⟨t, ?_⟩` and prove the remaining obligations. Use `show coordMap r σ (((intEquiv φ).toLinearMap).lTensor (ComplexAt σ) t) = w`.

Rewrite using `[ht, coordMap_coordInv]`.
-/
theorem fibreCoord_bijective (σ : K →+* ℂ) : Function.Bijective (fibreCoord φ σ) := by
  refine ⟨(coordMap_injective σ).comp (fibreMap_injective σ (intEquiv φ).injective), ?_⟩
  intro w
  obtain ⟨t, ht⟩ := LinearMap.lTensor_surjective (ComplexAt σ) (intEquiv φ).surjective (coordInv σ w)
  refine ⟨t, ?_⟩
  show coordMap r σ (((intEquiv φ).toLinearMap).lTensor (ComplexAt σ) t) = w
  rw [ht, coordMap_coordInv]

/- English proof (translation)
Simplify using `only [fibreCoord, LinearMap.comp_apply]`. Rewrite using `[← conjMap_fibreMap, coordMap_conjMap]`.
-/
theorem fibreCoord_conjMap (σ : K →+* ℂ) (x : Fibre σ V) :
    fibreCoord φ (conjugate σ) (conjMap σ V x) = star (fibreCoord φ σ x) := by
  simp only [fibreCoord, LinearMap.comp_apply]
  rw [← conjMap_fibreMap, coordMap_conjMap]

def fibreCoordEquiv (σ : K →+* ℂ) : Fibre σ V ≃ₗ[ℂ] (Fin r → ℂ) :=
  LinearEquiv.ofBijective (fibreCoord φ σ) (fibreCoord_bijective φ σ)

/- English proof (translation)
Rewrite using `[LinearEquiv.symm_apply_eq]`. Express the relevant statement in the definitionally equal form `star w = fibreCoord φ (conjugate σ) (conjMap σ V _)`. Rewrite using `[fibreCoord_conjMap]`. Use `congr 1`. Conclude with `((fibreCoordEquiv φ σ).apply_symm_apply w).symm`.
-/
theorem fibreCoordEquiv_symm_star (σ : K →+* ℂ) (w : Fin r → ℂ) :
    (fibreCoordEquiv φ (conjugate σ)).symm (star w) = conjMap σ V ((fibreCoordEquiv φ σ).symm w) := by
  rw [LinearEquiv.symm_apply_eq]
  change star w = fibreCoord φ (conjugate σ) (conjMap σ V _)
  rw [fibreCoord_conjMap]
  congr 1
  exact ((fibreCoordEquiv φ σ).apply_symm_apply w).symm

def normsOf (H : HermitianSpace K r) : HermitianNorms K V where
  form σ := coreComap (H.form σ) (fibreCoord φ σ) (fibreCoord_bijective φ σ).1
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, fibreCoord_conjMap, fibreCoord_conjMap, H.form_conj]

def spaceOf (Nm : HermitianNorms K V) : HermitianSpace K r where
  form σ := coreComap (Nm.form σ) (fibreCoordEquiv φ σ).symm.toLinearMap
    (fibreCoordEquiv φ σ).symm.injective
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner]
    simp only [LinearEquiv.coe_coe]
    rw [fibreCoordEquiv_symm_star, fibreCoordEquiv_symm_star, Nm.form_conj]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normsOf_inner (H : HermitianSpace K r) (σ : K →+* ℂ) (x y : V) :
    ((normsOf φ H).form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (H.form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x)) (coordMap r σ (1 ⊗ₜ φ y)) := rfl

/- English proof (translation)
Establish `h : ∀ z : V, (fibreCoordEquiv φ σ).symm (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ z)) = (1 : ComplexAt σ) ⊗ₜ z` using `fun z ↦ by`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `_ = (Nm.form σ).inner ((fibreCoordEquiv φ σ).symm _) ((fibreCoordEquiv φ σ).symm _)`. Rewrite using `[h, h]`.
-/
theorem spaceOf_inner (Nm : HermitianNorms K V) (σ : K →+* ℂ) (x y : V) :
    (Nm.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      ((spaceOf φ Nm).form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x))
        (coordMap r σ (1 ⊗ₜ φ y)) := by
  have h : ∀ z : V, (fibreCoordEquiv φ σ).symm (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ z)) =
      (1 : ComplexAt σ) ⊗ₜ z := fun z ↦ by
    rw [LinearEquiv.symm_apply_eq]; rfl
  change _ = (Nm.form σ).inner ((fibreCoordEquiv φ σ).symm _) ((fibreCoordEquiv φ σ).symm _)
  rw [h, h]

/- English proof (translation)
Unfold `HermitianBundle.deg deg degOf HermitianBundle.arithDegree`. Use `congr 1`. Use `GroundTheory.Heights₂.Heights.LatticeLemmas.arithDegree_congr _ _ (Submodule.equivMapOfInjective _ (intEquiv φ).injective L.carrier) fun σ x y ↦ ?_` and prove the remaining obligations. Conclude with `hrel σ (Subtype.val (p := (· ∈ L.carrier)) x) (Subtype.val (p := (· ∈ L.carrier)) y)`.
-/
theorem deg_bundle_eq (Nm : HermitianNorms K V) (H : HermitianSpace K r)
    (hrel : ∀ (σ : K →+* ℂ) (x y : V), (Nm.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (H.form σ).inner (coordMap r σ ((1 : ComplexAt σ) ⊗ₜ φ x)) (coordMap r σ (1 ⊗ₜ φ y)))
    (L : FullLattice K V) (hL : (L.carrier.map (intEquiv φ).toLinearMap).FG) :
    (Nm.bundle L).deg = deg (H.lattice (L.carrier.map (intEquiv φ).toLinearMap) hL) := by
  unfold HermitianBundle.deg deg degOf HermitianBundle.arithDegree
  congr 1
  refine GroundTheory.Heights₂.Heights.LatticeLemmas.arithDegree_congr _ _
    (Submodule.equivMapOfInjective _ (intEquiv φ).injective L.carrier) fun σ x y ↦ ?_
  exact hrel σ (Subtype.val (p := (· ∈ L.carrier)) x) (Subtype.val (p := (· ∈ L.carrier)) y)

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem deg_lattice_congr (H : HermitianSpace K r) {M M' : Submodule (𝓞 K) (Fin r → K)} (e : M = M')
    (h : M.FG) (h' : M'.FG) : deg (H.lattice M h) = deg (H.lattice M' h') := by
  subst e; rfl

/- English proof (translation)
The claim follows from `hL.map _`.
-/
theorem fg_map (L : Submodule (𝓞 K) V) (hL : L.FG) : (L.map (intEquiv φ).toLinearMap).FG :=
  hL.map _

/- English proof (translation)
Rewrite using `[Submodule.map_coe]`. Express the relevant statement in the definitionally equal form `Submodule.span K (φ.toLinearMap '' (L : Set V)) = ⊤`. Rewrite using `[Submodule.span_image, hL, Submodule.map_top, LinearEquiv.range]`.
-/
theorem span_map (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) :
    Submodule.span K ((L.map (intEquiv φ).toLinearMap : Submodule (𝓞 K) (Fin r → K)) :
      Set (Fin r → K)) = ⊤ := by
  rw [Submodule.map_coe]
  change Submodule.span K (φ.toLinearMap '' (L : Set V)) = ⊤
  rw [Submodule.span_image, hL, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fg_map φ _ L.fg, span_map φ _ L.span_eq⟩`.
-/
theorem isLattice_map (L : FullLattice K V) : IsLattice (L.carrier.map (intEquiv φ).toLinearMap) :=
  ⟨fg_map φ _ L.fg, span_map φ _ L.span_eq⟩

def pullLattice (M : Submodule (𝓞 K) (Fin r → K)) (hM : IsLattice M) : FullLattice K V where
  carrier := M.map (intEquiv φ).symm.toLinearMap
  fg := hM.1.map _
  span_eq := by
    rw [Submodule.map_coe]
    change Submodule.span K (φ.symm.toLinearMap '' (M : Set (Fin r → K))) = ⊤
    rw [Submodule.span_image, hM.2, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Use `show Submodule.map (intEquiv φ).toLinearMap (Submodule.map (intEquiv φ).symm.toLinearMap M) = M`. Rewrite using `[← Submodule.map_comp]`. Establish `: (intEquiv φ).toLinearMap ∘ₗ (intEquiv φ).symm.toLinearMap = LinearMap.id` using `LinearMap.ext fun x ↦ (intEquiv φ).apply_symm_apply x`. Rewrite using `[this, Submodule.map_id]`.
-/
theorem map_pullLattice (M : Submodule (𝓞 K) (Fin r → K)) (hM : IsLattice M) :
    (pullLattice φ M hM).carrier.map (intEquiv φ).toLinearMap = M := by
  show Submodule.map (intEquiv φ).toLinearMap (Submodule.map (intEquiv φ).symm.toLinearMap M) = M
  rw [← Submodule.map_comp]
  have : (intEquiv φ).toLinearMap ∘ₗ (intEquiv φ).symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x ↦ (intEquiv φ).apply_symm_apply x
  rw [this, Submodule.map_id]

/- English proof (translation)
Take `⟨S, hS⟩` from `M.fg`. Use `⟨⟨S, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← M.span_eq, Submodule.span_le]`. Introduce `x hx`. Rewrite `hx` using `[SetLike.mem_coe, ← hS]`.

Conclude with `Submodule.span_le_restrictScalars (𝓞 K) K (S : Set V) hx`.
-/
theorem finiteDimensional (M : FullLattice K V) : FiniteDimensional K V := by
  obtain ⟨S, hS⟩ := M.fg
  refine ⟨⟨S, ?_⟩⟩
  rw [eq_top_iff, ← M.span_eq, Submodule.span_le]
  intro x hx
  rw [SetLike.mem_coe, ← hS] at hx
  exact Submodule.span_le_restrictScalars (𝓞 K) K (S : Set V) hx

variable (v : HeightOneSpectrum (𝓞 K))

def localEquiv : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K) :=
  (LinearEquiv.baseChange K (v.adicCompletion K) V (Fin r → K) φ).trans
    (TensorProduct.piScalarRight K (v.adicCompletion K) (v.adicCompletion K) (Fin r))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[localEquiv, Heights.toLocal, locVec, Algebra.algebraMap_eq_smul_one]`.
-/
theorem localEquiv_toLocal (x : V) : localEquiv φ v (Heights.toLocal v x) = locVec v (φ x) := by
  funext i
  simp [localEquiv, Heights.toLocal, locVec, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Set `f` to `(localEquiv φ v).toLinearMap.restrictScalars (v.adicCompletionIntegers K)`. Establish `hf : ⇑(localEquiv φ v) = ⇑f` using `rfl`. Rewrite using `[hf, Heights.localLattice, ← Submodule.map_coe, Submodule.map_span, localLattice, Submodule.map_coe, Set.image_image]`. Use `congr 2`. Use extensionality with `w`.

Simplify using `only [Set.mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨φ x, ⟨x, hx, rfl⟩, (localEquiv_toLocal φ v x).symm⟩`. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`.

Conclude with `⟨x, hx, localEquiv_toLocal φ v x⟩`.
-/
theorem image_localLattice (L : Submodule (𝓞 K) V) :
    localEquiv φ v '' (Heights.localLattice v L : Set (v.adicCompletion K ⊗[K] V)) =
      (localLattice v (L.map (intEquiv φ).toLinearMap) : Set (Fin r → v.adicCompletion K)) := by
  let f := (localEquiv φ v).toLinearMap.restrictScalars (v.adicCompletionIntegers K)
  have hf : ⇑(localEquiv φ v) = ⇑f := rfl
  rw [hf, Heights.localLattice, ← Submodule.map_coe, Submodule.map_span, localLattice,
    Submodule.map_coe, Set.image_image]
  congr 2
  ext w
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, ⟨x, hx, rfl⟩, (localEquiv_toLocal φ v x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, localEquiv_toLocal φ v x⟩

def glEquiv (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (g : Matrix (Fin r) (Fin r) (v.adicCompletion K)))
    (Matrix.toLin' ((g⁻¹ : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
      Matrix (Fin r) (Fin r) (v.adicCompletion K)))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glEquiv_apply (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K))
    (x : Fin r → v.adicCompletion K) : glEquiv v g x = glMap v g x := rfl

/- English proof (translation)
Use extensionality with `x i`. Simplify using `[glEquiv]`.
-/
theorem glEquiv_one : glEquiv v (1 : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) = 1 := by
  ext x i
  simp [glEquiv]

/- English proof (translation)
The claim follows from `LinearMap.det_toLin' _`.
-/
theorem det_glEquiv (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    LinearMap.det (glEquiv v g : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) =
      (g : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det :=
  LinearMap.det_toLin' _

def glOf (f : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) :
    Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) where
  val := LinearMap.toMatrix' (f : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _)
  inv := LinearMap.toMatrix' (f.symm : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _)
  val_inv := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
    congr 1
    exact LinearMap.ext fun x ↦ f.apply_symm_apply x
  inv_val := by
    rw [← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
    congr 1
    exact LinearMap.ext fun x ↦ f.symm_apply_apply x

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Matrix.toLin' (LinearMap.toMatrix' (f : _ →ₗ[v.adicCompletion K] _)) x = f x`. Rewrite using `[Matrix.toLin'_toMatrix']`. Both sides reduce to the same expression.
-/
theorem glMap_glOf (f : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K))
    (x : Fin r → v.adicCompletion K) : glMap v (glOf v f) x = f x := by
  change Matrix.toLin' (LinearMap.toMatrix' (f : _ →ₗ[v.adicCompletion K] _)) x = f x
  rw [Matrix.toLin'_toMatrix']
  rfl

/- English proof (translation)
Use extensionality with `: 1`. Express the relevant statement in the definitionally equal form `LinearMap.toMatrix' LinearMap.id = 1`. Conclude with `LinearMap.toMatrix'_id`.
-/
theorem glOf_one : glOf v (1 : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] _) = 1 := by
  ext : 1
  change LinearMap.toMatrix' LinearMap.id = 1
  exact LinearMap.toMatrix'_id

/- English proof (translation)
The claim follows from `LinearMap.det_toMatrix' _`.
-/
theorem det_glOf (f : (Fin r → v.adicCompletion K) ≃ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) :
    (glOf v f : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det =
      LinearMap.det (f : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) :=
  LinearMap.det_toMatrix' _

include φ in

/- English proof (translation)
Introduce `H M₁ M₂ h₁ h₂ g hg hloc`. Use `set gA : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V) := fun v ↦ (localEquiv φ v).trans ((glEquiv v (g v)).trans (localEquiv φ v).symm) with hgA`. Establish `hfin : {v | gA v ≠ 1}.Finite`. Use `hg.subset fun v hv h1 ↦ hv ?_` and prove the remaining obligations. Use `LinearEquiv.ext fun x ↦ ?_` and prove the remaining obligations.

Simplify using `[hgA, h1, glEquiv_one]`. Establish `hloc' : ∀ v, (Heights.localLattice v (pullLattice φ M₂ h₂).carrier : Set (v.adicCompletion K ⊗[K] V)) = gA v '' Heights.localLattice v (pullLattice φ M₁ h₁).carrier`. Introduce `v`. Apply `Set.image_injective.mpr (localEquiv φ v).injective` to reduce the goal to its premises. Rewrite using `[image_localLattice, map_pullLattice, hloc v, Set.image_image]`.

Establish `: (fun x ↦ localEquiv φ v (gA v x)) = glMap v (g v) ∘ localEquiv φ v`. Use function extensionality and compare the values at `x`. Simplify using `only [hgA, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Function.comp_apply, glEquiv_apply]`. Rewrite using `[this, Set.image_comp, image_localLattice, map_pullLattice, Submodule.map_coe]`. Establish `key` using `hA (normsOf φ H) (pullLattice φ M₁ h₁) (pullLattice φ M₂ h₂) gA hfin hloc'`.

Rewrite `key` using `[deg_bundle_eq φ _ H (normsOf_inner φ H) _ (isLattice_map φ _).1, deg_bundle_eq φ _ H (normsOf_inner φ H) _ (isLattice_map φ _).1, deg_lattice_congr H (map_pullLattice φ M₂ h₂) _ h₂.1, deg_lattice_congr H (map_pullLattice φ M₁ h₁) _ h₁.1]`. Establish `hdet : ∀ v, LinearMap.det (gA v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) = (g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det`. Introduce `v`. Establish `: (gA v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) = ((localEquiv φ v).symm : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) ∘ₗ (glEquiv v (g v) : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) ∘ₗ ((localEquiv φ v).symm.symm …` using `LinearMap.ext fun x ↦ rfl`. Rewrite using `[this, LinearMap.det_conj, det_glEquiv]`.

Simplify using `only [hdet] at key`. Conclude with `key`.
-/
theorem bAt_of_aAt (hA : AAt K V) : BAt K r := by
  intro H M₁ M₂ h₁ h₂ g hg hloc
  set gA : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V) :=
    fun v ↦ (localEquiv φ v).trans ((glEquiv v (g v)).trans (localEquiv φ v).symm) with hgA
  have hfin : {v | gA v ≠ 1}.Finite := by
    refine hg.subset fun v hv h1 ↦ hv ?_
    refine LinearEquiv.ext fun x ↦ ?_
    simp [hgA, h1, glEquiv_one]
  have hloc' : ∀ v, (Heights.localLattice v (pullLattice φ M₂ h₂).carrier :
      Set (v.adicCompletion K ⊗[K] V)) = gA v '' Heights.localLattice v (pullLattice φ M₁ h₁).carrier := by
    intro v
    apply Set.image_injective.mpr (localEquiv φ v).injective
    rw [image_localLattice, map_pullLattice, hloc v, Set.image_image]
    have : (fun x ↦ localEquiv φ v (gA v x)) = glMap v (g v) ∘ localEquiv φ v := by
      funext x
      simp only [hgA, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Function.comp_apply,
        glEquiv_apply]
    rw [this, Set.image_comp, image_localLattice, map_pullLattice, Submodule.map_coe]
  have key := hA (normsOf φ H) (pullLattice φ M₁ h₁) (pullLattice φ M₂ h₂) gA hfin hloc'
  rw [deg_bundle_eq φ _ H (normsOf_inner φ H) _ (isLattice_map φ _).1,
    deg_bundle_eq φ _ H (normsOf_inner φ H) _ (isLattice_map φ _).1,
    deg_lattice_congr H (map_pullLattice φ M₂ h₂) _ h₂.1,
    deg_lattice_congr H (map_pullLattice φ M₁ h₁) _ h₁.1] at key
  have hdet : ∀ v, LinearMap.det (gA v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] V)) = (g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det := by
    intro v
    have : (gA v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) =
        ((localEquiv φ v).symm : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) ∘ₗ
          (glEquiv v (g v) : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] _) ∘ₗ
          ((localEquiv φ v).symm.symm : _ →ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) :=
      LinearMap.ext fun x ↦ rfl
    rw [this, LinearMap.det_conj, det_glEquiv]
  simp only [hdet] at key
  exact key

include φ in

/- English proof (translation)
Introduce `Nm L₁ L₂ g hg hloc`. Use `set gB : ∀ v : HeightOneSpectrum (𝓞 K), Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) := fun v ↦ glOf v ((localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v))) with hgB`. Establish `hfin : {v | gB v ≠ 1}.Finite`. Use `hg.subset fun v hv h1 ↦ hv ?_` and prove the remaining obligations. Establish `: (localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v)) = 1` using `LinearEquiv.ext fun x ↦ by simp [h1]`.

Simplify using `only [hgB, this, glOf_one]`. Establish `hloc' : ∀ v, localLattice v (L₂.carrier.map (intEquiv φ).toLinearMap) = (localLattice v (L₁.carrier.map (intEquiv φ).toLinearMap)).map (glMap v (gB v))`. Introduce `v`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[Submodule.map_coe, ← image_localLattice, ← image_localLattice, hloc v, ← Set.image_comp, ← Set.image_comp]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [hgB, Function.comp_apply, glMap_glOf, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]`. Establish `hM₁` using `isLattice_map φ L₁`. Establish `hM₂` using `isLattice_map φ L₂`.

Establish `key` using `hB (spaceOf φ Nm) _ _ hM₁ hM₂ gB hfin hloc'`. Rewrite using `[deg_bundle_eq φ Nm (spaceOf φ Nm) (spaceOf_inner φ Nm) L₂ hM₂.1, deg_bundle_eq φ Nm (spaceOf φ Nm) (spaceOf_inner φ Nm) L₁ hM₁.1, key]`. Establish `hdet : ∀ v, (gB v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det = LinearMap.det (g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V))`. Introduce `v`. Simplify using `only [hgB]`.

Rewrite using `[det_glOf]`. Establish `: ((localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v)) : (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) = (localEquiv φ v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] _) ∘ₗ (g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] …` using `LinearMap.ext fun x ↦ rfl`. Rewrite using `[this, LinearMap.det_conj]`. Simplify using `only [hdet]`.
-/
theorem aAt_of_bAt (hB : BAt K r) : AAt K V := by
  intro Nm L₁ L₂ g hg hloc
  set gB : ∀ v : HeightOneSpectrum (𝓞 K), Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) :=
    fun v ↦ glOf v ((localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v))) with hgB
  have hfin : {v | gB v ≠ 1}.Finite := by
    refine hg.subset fun v hv h1 ↦ hv ?_
    have : (localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v)) = 1 :=
      LinearEquiv.ext fun x ↦ by simp [h1]
    simp only [hgB, this, glOf_one]
  have hloc' : ∀ v, localLattice v (L₂.carrier.map (intEquiv φ).toLinearMap) =
      (localLattice v (L₁.carrier.map (intEquiv φ).toLinearMap)).map (glMap v (gB v)) := by
    intro v
    apply SetLike.coe_injective
    rw [Submodule.map_coe, ← image_localLattice, ← image_localLattice, hloc v, ← Set.image_comp,
      ← Set.image_comp]
    congr 1
    funext x
    simp only [hgB, Function.comp_apply, glMap_glOf, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  have hM₁ := isLattice_map φ L₁
  have hM₂ := isLattice_map φ L₂
  have key := hB (spaceOf φ Nm) _ _ hM₁ hM₂ gB hfin hloc'
  rw [deg_bundle_eq φ Nm (spaceOf φ Nm) (spaceOf_inner φ Nm) L₂ hM₂.1,
    deg_bundle_eq φ Nm (spaceOf φ Nm) (spaceOf_inner φ Nm) L₁ hM₁.1, key]
  have hdet : ∀ v, (gB v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det =
      LinearMap.det (g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K]
        (v.adicCompletion K ⊗[K] V)) := by
    intro v
    simp only [hgB]
    rw [det_glOf]
    have : ((localEquiv φ v).symm.trans ((g v).trans (localEquiv φ v)) :
        (Fin r → v.adicCompletion K) →ₗ[v.adicCompletion K] (Fin r → v.adicCompletion K)) =
        (localEquiv φ v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] _) ∘ₗ
          (g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] _) ∘ₗ
          ((localEquiv φ v).symm : _ →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)) :=
      LinearMap.ext fun x ↦ rfl
    rw [this, LinearMap.det_conj]
  simp only [hdet]

end LocalChangeEq

open LocalChangeEq in

/- English proof (translation)
Introduce `K _ _ V _ _ _ _ Nm M₁ M₂ g hg hloc`. Establish `: FiniteDimensional K V` using `finiteDimensional M₁`. Conclude with `aAt_of_bAt (Module.finBasis K V).equivFun (hB K _) Nm M₁ M₂ g hg hloc`.
-/
theorem LocalChange.kleimanNef_field_of_alt (hB : LocalChange.Statement.{u}) :
    GroundTheory.Heights₂.Heights.LatticeLemmas.LocalChange.Statement.{u, v} := by
  intro K _ _ V _ _ _ _ Nm M₁ M₂ g hg hloc
  have : FiniteDimensional K V := finiteDimensional M₁
  exact aAt_of_bAt (Module.finBasis K V).equivFun (hB K _) Nm M₁ M₂ g hg hloc

open LocalChangeEq in

/- English proof (translation)
Introduce `K _ _ r`. Conclude with `bAt_of_aAt (V := ULift.{v} (Fin r → K)) ULift.moduleEquiv (hA K (ULift.{v} (Fin r → K)))`.
-/
theorem LocalChange.localChange_of_vectorSpace (hA : GroundTheory.Heights₂.Heights.LatticeLemmas.LocalChange.Statement.{u, max u v}) :
    LocalChange.Statement.{u} := by
  intro K _ _ r
  exact bAt_of_aAt (V := ULift.{v} (Fin r → K)) ULift.moduleEquiv (hA K (ULift.{v} (Fin r → K)))

/- English proof (translation)
Assemble the required witnesses or components as `⟨LocalChange.localChange_of_vectorSpace, LocalChange.kleimanNef_field_of_alt⟩`.
-/
theorem LocalChange.equiv :
    GroundTheory.Heights₂.Heights.LatticeLemmas.LocalChange.Statement.{u, max u v} ↔
      LocalChange.Statement.{u} :=
  ⟨LocalChange.localChange_of_vectorSpace, LocalChange.kleimanNef_field_of_alt⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
