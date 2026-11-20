import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance secondCountable_tens [SecondCountableTopology R] :
    SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isInducing.secondCountableTopology

instance borelSpace_tens : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

instance borelSpace_herm (σ : E →ₐ[F] E) (n : ℕ) : BorelSpace (HermR R σ n) := ⟨rfl⟩

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Set `b` to `Algebra.TensorProduct.basis R (Module.finBasis F E)`. Establish `hn : (fun x : R ⊗[F] E => Algebra.norm R x) = fun x => (Algebra.leftMulMatrix b x).det`. Use function extensionality and compare the values at `fun x => Algebra.norm_eq_matrix_det b x`. Rewrite using `[hn]`.

Use `Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)` and prove the remaining obligations. Simplify using `only [Algebra.leftMulMatrix_eq_repr_mul]`. Conclude with `IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight R (b j)))`.
-/
theorem continuous_norm_tens : Continuous (fun x : R ⊗[F] E => Algebra.norm R x) := by
  classical
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have hn : (fun x : R ⊗[F] E => Algebra.norm R x) = fun x => (Algebra.leftMulMatrix b x).det :=
    funext fun x => Algebra.norm_eq_matrix_det b x
  rw [hn]
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  exact IsModuleTopology.continuous_of_linearMap
    ((b.coord i).comp (LinearMap.mulRight R (b j)))

/- English proof (translation)
Use `haveI : Module.Free R (R ⊗[F] E) := Module.Free.of_basis (Algebra.TensorProduct.basis R (Module.finBasis F E))`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h.map (Algebra.norm R)`. Introduce `h`.

Rewrite `h` using `[Algebra.norm_apply]`. Take `⟨u, hu⟩` from `(LinearMap.isUnit_iff_isUnit_det _).2 h`. Establish `h1 : (u : Module.End R (R ⊗[F] E)) ((↑u⁻¹ : Module.End R (R ⊗[F] E)) 1) = 1`. Rewrite using `[← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]`. Rewrite `h1` using `[hu]`.

Conclude with `isUnit_iff_exists_inv.2 ⟨_, h1⟩`.
-/
theorem isUnit_iff_norm_tens (x : R ⊗[F] E) : IsUnit x ↔ IsUnit (Algebra.norm R x) := by
  haveI : Module.Free R (R ⊗[F] E) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis R (Module.finBasis F E))
  constructor
  · intro h
    exact h.map (Algebra.norm R)
  · intro h
    rw [Algebra.norm_apply] at h
    obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_isUnit_det _).2 h
    have h1 : (u : Module.End R (R ⊗[F] E)) ((↑u⁻¹ : Module.End R (R ⊗[F] E)) 1) = 1 := by
      rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    rw [hu] at h1
    exact isUnit_iff_exists_inv.2 ⟨_, h1⟩

/- English proof (translation)
Establish `hs : {x : R ⊗[F] E | IsUnit x} = (fun x => Algebra.norm R x) ⁻¹' {r : R | IsUnit r}` using `Set.ext fun x => isUnit_iff_norm_tens R x`. Rewrite using `[hs]`. Conclude with `h.preimage (continuous_norm_tens R)`.
-/
theorem isOpen_units_tens (h : IsOpen {r : R | IsUnit r}) :
    IsOpen {x : R ⊗[F] E | IsUnit x} := by
  have hs : {x : R ⊗[F] E | IsUnit x} = (fun x => Algebra.norm R x) ⁻¹' {r : R | IsUnit r} :=
    Set.ext fun x => isUnit_iff_norm_tens R x
  rw [hs]
  exact h.preimage (continuous_norm_tens R)

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _`. Conclude with `(isOpen_units_tens R h).preimage (continuous_id.matrix_det)`.
-/
theorem isOpen_isUnit_det (h : IsOpen {r : R | IsUnit r}) (n : ℕ) :
    IsOpen {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | IsUnit S.det} := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact (isOpen_units_tens R h).preimage (continuous_id.matrix_det)

def hLin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E) :
    (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun := hR R σ J x
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hM : (gramR R σ J X).mulVec g = 0`. Use function extensionality and compare the values at `b`. Establish `hb` using `congrArg (hLin R σ J (X b)) hg`.

Simplify using `only [map_sum, map_smul, map_zero, smul_eq_mul] at hb`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← hb]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [mul_comm]; rfl`. Establish `hg0 : g = 0`.

Rewrite using `[← Matrix.one_mulVec g, ← Matrix.nonsing_inv_mul _ h, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_zero]`. Introduce `i`. Rewrite using `[hg0]`. Both sides reduce to the same expression.
-/
theorem linIndep_of_isUnit_det (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (h : IsUnit (gramR R σ J X).det) :
    LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hM : (gramR R σ J X).mulVec g = 0 := by
    funext b
    have hb := congrArg (hLin R σ J (X b)) hg
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at hb
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← hb]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]; rfl
  have hg0 : g = 0 := by
    rw [← Matrix.one_mulVec g, ← Matrix.nonsing_inv_mul _ h, ← Matrix.mulVec_mulVec, hM,
      Matrix.mulVec_zero]
  intro i
  rw [hg0]
  rfl

variable [LocallyCompactSpace R] [T2Space R]

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _`. Set `sL : R ⊗[F] E →ₗ[R] R ⊗[F] E` to `{ toFun := sigR R σ map_add' := map_add _ map_smul' := fun r x => by`. Rewrite using `[RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `congr 1`.

Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply] }`. Establish `hs : Continuous (sigR R σ)` using `IsModuleTopology.continuous_of_linearMap sL`. Simplify using `only [hR, Formalism.UG.hform]`. Conclude with `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ((hs.comp ((continuous_apply i).comp continuous_fst)).mul continuous_const).mul ((continuous_apply j).comp continuous_snd)`.
-/
theorem continuous_hR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun p : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) => hR R σ J p.1 p.2) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let sL : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
    { toFun := sigR R σ
      map_add' := map_add _
      map_smul' := fun r x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        simp [sigR, Algebra.TensorProduct.algebraMap_apply] }
  have hs : Continuous (sigR R σ) := IsModuleTopology.continuous_of_linearMap sL
  simp only [hR, Formalism.UG.hform]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((hs.comp ((continuous_apply i).comp continuous_fst)).mul continuous_const).mul
      ((continuous_apply j).comp continuous_snd)

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _`. Set `sL : R ⊗[F] E →ₗ[R] R ⊗[F] E` to `{ toFun := sigR R σ map_add' := map_add _ map_smul' := fun r x => by`. Rewrite using `[RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `congr 1`.

Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply] }`. Establish `hs : Continuous (sigR R σ)` using `IsModuleTopology.continuous_of_linearMap sL`. Simplify using `only [gramR, hR, Formalism.UG.hform]`. Conclude with `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul ((continuous_apply j).comp (continuous_apply b))`.
-/
theorem continuous_gramR_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => gramR R σ J X a b) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let sL : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
    { toFun := sigR R σ
      map_add' := map_add _
      map_smul' := fun r x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        simp [sigR, Algebra.TensorProduct.algebraMap_apply] }
  have hs : Continuous (sigR R σ) := IsModuleTopology.continuous_of_linearMap sL
  simp only [gramR, hR, Formalism.UG.hform]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

/- English proof (translation)
The claim follows from `continuous_pi fun a => continuous_pi fun b => continuous_gramR_apply R σ J a b`.
-/
theorem continuous_gramR (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun X : Fin n → Fin M → R ⊗[F] E => gramR R σ J X) :=
  continuous_pi fun a => continuous_pi fun b => continuous_gramR_apply R σ J a b

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _`. Set `sL : R ⊗[F] E →ₗ[R] R ⊗[F] E` to `{ toFun := sigR R σ map_add' := map_add _ map_smul' := fun r x => by`. Rewrite using `[RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `congr 1`.

Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply] }`. Establish `hs : Continuous (sigR R σ)` using `IsModuleTopology.continuous_of_linearMap sL`. Establish `hset : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) = ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b}`. Use extensionality with `S`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`.

Both sides reduce to the same expression. Rewrite using `[hset]`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq (hs.comp ((continuous_apply a).comp (continuous_apply b))) ((continuous_apply b).comp (continuous_apply a))`.
-/
theorem isClosed_HermR (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let sL : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
    { toFun := sigR R σ
      map_add' := map_add _
      map_smul' := fun r x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        simp [sigR, Algebra.TensorProduct.algebraMap_apply] }
  have hs : Continuous (sigR R σ) := IsModuleTopology.continuous_of_linearMap sL
  have hset : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
    ext S
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [hset]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq (hs.comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))

instance locallyCompact_herm (σ : E →ₐ[F] E) (n : ℕ) : LocallyCompactSpace (HermR R σ n) :=
  (isClosed_HermR R σ n).isClosedEmbedding_subtypeVal.locallyCompactSpace

end Gen

section CM

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hσ τ (σ x), hσ τ x, star_star]`.
-/
theorem sigma_invol [NumberField E] (σ : E →ₐ[F] E)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [hσ τ (σ x), hσ τ x, star_star]

variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Introduce `a b`. Establish `hJR : ∀ i j, sigR R σ (JR R J j i) = JR R J i j` using `fun i j => by`. Simplify using `[JR, inclR, sigR, hJ]`. Simplify using `only [gramR, hR, Formalism.UG.hform, map_sum, map_mul, sigR_invol R σ hσ, hJR]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem gramR_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  intro a b
  have hJR : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := fun i j => by
    simp [JR, inclR, sigR, hJ]
  simp only [gramR, hR, Formalism.UG.hform, map_sum, map_mul, sigR_invol R σ hσ, hJR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end CM

section Arch

variable (F : Type) [Field F] [NumberField F]

instance secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (v := v)).isEmbedding.isInducing.secondCountableTopology

instance secondCountable_Ainf : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

/- English proof (translation)
Use `show IsOpen {x : (v : InfinitePlace F) → v.Completion | IsUnit x}`. Establish `hs : {x : (v : InfinitePlace F) → v.Completion | IsUnit x} = Set.univ.pi fun v : InfinitePlace F => {y : v.Completion | IsUnit y}`. Use extensionality with `x`. Simplify using `[Pi.isUnit_iff]`. Rewrite using `[hs]`.

Conclude with `isOpen_set_pi Set.finite_univ fun v _ => Units.isOpen`.
-/
theorem isOpen_units_Ainf : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by
  show IsOpen {x : (v : InfinitePlace F) → v.Completion | IsUnit x}
  have hs : {x : (v : InfinitePlace F) → v.Completion | IsUnit x} =
      Set.univ.pi fun v : InfinitePlace F => {y : v.Completion | IsUnit y} := by
    ext x
    simp [Pi.isUnit_iff]
  rw [hs]
  exact isOpen_set_pi Set.finite_univ fun v _ => Units.isOpen

end Arch

section Glue

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Use `show IsUnit (T.map (inclR R)).det`. Rewrite using `[show (T.map (inclR R)).det = inclR R T.det from (RingHom.map_det (inclR R) T).symm]`. Conclude with `(isUnit_iff_ne_zero.2 hdet).map _`.
-/
theorem isUnit_det_hermOf (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) :
    IsUnit ((hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) := by
  show IsUnit (T.map (inclR R)).det
  rw [show (T.map (inclR R)).det = inclR R T.det from (RingHom.map_det (inclR R) T).symm]
  exact (isUnit_iff_ne_zero.2 hdet).map _

def gramH (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) : HermR R σ n :=
  ⟨gramR R σ J X, gramR_mem R σ hσ J hJ X⟩

end Glue

section GlueTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

/- English proof (translation)
The claim follows from `(continuous_gramR R σ J).subtype_mk _`.
-/
theorem continuous_gramH (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j) :
    Continuous (gramH (n := n) R σ hσ J hJ) :=
  (continuous_gramR R σ J).subtype_mk _

/- English proof (translation)
The claim follows from `(isOpen_isUnit_det R h n).preimage continuous_subtype_val`.
-/
theorem isOpen_unitHerm (h : IsOpen {r : R | IsUnit r}) (σ : E →ₐ[F] E) (n : ℕ) :
    IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} :=
  (isOpen_isUnit_det R h n).preimage continuous_subtype_val

end GlueTop

end PI.VolStabS
