import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizerStatement

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TorCentTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}
  {k : Type} [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k]

omit [FiniteDimensional F E] [TopologicalSpace k] [IsTopologicalRing k] in

/- English proof (translation)
The claim follows from `IsScalarTower.of_algebraMap_eq fun c => by change c ⊗ₜ[F] (1 : Fld P) = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) (c ⊗ₜ[F] 1) rw [Algebra.TensorProduct.map_tmul, map_one]; rfl`.
-/
theorem isScalarTower_base : IsScalarTower k (k ⊗[F] E) (k ⊗[F] Fld P) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change c ⊗ₜ[F] (1 : Fld P) = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) (c ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

/- English proof (translation)
Use `haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩`. Use `haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _`. Use `haveI : ContinuousAdd (k ⊗[F] E) := IsModuleTopology.toContinuousAdd k _`. Use `haveI := isScalarTower_base (k := k) (P := P)`.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Establish `e : ∀ l, mulMat φ l i j = φ (l * φ.symm (Pi.single j 1)) i` using `fun l => by`. Rewrite using `[← mulMat_mulVec, φ.apply_symm_apply, Matrix.mulVec_single_one, Matrix.col_apply]`. Simplify using `only [e]`. Conclude with `IsModuleTopology.continuous_of_linearMap (((LinearMap.proj i).comp (φ.toLinearMap.comp (LinearMap.mulRight (k ⊗[F] E) (φ.symm (Pi.single j 1))))).restrictScalars k)`.
-/
theorem continuous_mulMat (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) : Continuous (mulMat φ) := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  haveI : ContinuousAdd (k ⊗[F] E) := IsModuleTopology.toContinuousAdd k _
  haveI := isScalarTower_base (k := k) (P := P)
  refine continuous_matrix fun i j => ?_
  have e : ∀ l, mulMat φ l i j = φ (l * φ.symm (Pi.single j 1)) i := fun l => by
    rw [← mulMat_mulVec, φ.apply_symm_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [e]
  exact IsModuleTopology.continuous_of_linearMap (((LinearMap.proj i).comp (φ.toLinearMap.comp
    (LinearMap.mulRight (k ⊗[F] E) (φ.symm (Pi.single j 1))))).restrictScalars k)

/- English proof (translation)
The claim follows from `Matrix.det_fin_one _`.
-/
theorem torUnit_val (t : Tor P k) : (torUnit t).1 = (matHom k (star' P) (one₁ P) t).1 0 0 :=
  Matrix.det_fin_one _

/- English proof (translation)
Simplify using `only [torUnit_val]`. Conclude with `(Units.continuous_val.comp (isEmbedding_matHom k (star' P) (one₁ P)).continuous).matrix_elem 0 0`.
-/
theorem continuous_torUnit : Continuous fun t : Tor P k => (torUnit t).1 := by
  simp only [torUnit_val]
  exact (Units.continuous_val.comp (isEmbedding_matHom k (star' P) (one₁ P)).continuous).matrix_elem 0 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matHom_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) : (matHom k σ J (torEmb h t)).1 = mulMat φ (torUnit t).1 := rfl

/- English proof (translation)
Rewrite using `[matHom_torEmb, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_one]`.
-/
theorem torUnit_eq {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) : (torUnit t).1 = φ.symm ((matHom k σ J (torEmb h t)).1 *ᵥ φ 1) := by
  rw [matHom_torEmb, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_one]

/- English proof (translation)
Use `haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _`. Use `(isEmbedding_matHom k σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun t => (matHom k σ J (torEmb h t)).1`. Simplify using `only [matHom_torEmb]`. Conclude with `(continuous_mulMat φ).comp continuous_torUnit`.

Express the relevant statement in the definitionally equal form `Continuous fun t => (matHom k σ J (torEmb h t))⁻¹.1`. Simplify using `only [← map_inv, matHom_torEmb]`. Conclude with `(continuous_mulMat φ).comp (continuous_torUnit.comp continuous_inv)`.
-/
theorem continuous_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) : Continuous (torEmb h) := by
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  refine (isEmbedding_matHom k σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · change Continuous fun t => (matHom k σ J (torEmb h t)).1
    simp only [matHom_torEmb]
    exact (continuous_mulMat φ).comp continuous_torUnit
  · change Continuous fun t => (matHom k σ J (torEmb h t))⁻¹.1
    simp only [← map_inv, matHom_torEmb]
    exact (continuous_mulMat φ).comp (continuous_torUnit.comp continuous_inv)

/- English proof (translation)
Use `haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩`. Use `haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _`. Use `haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _`. Use `haveI := isScalarTower_base (k := k) (P := P)`.

Use `haveI : ContinuousAdd (k ⊗[F] Fld P) := IsModuleTopology.toContinuousAdd k _`. Establish `h1 : Continuous (φ.symm.toLinearMap.restrictScalars k)` using `IsModuleTopology.continuous_of_linearMap _`. Use `h1.comp (Continuous.matrix_mulVec ?_ continuous_const)` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (isEmbedding_matHom k σ J).continuous`.
-/
theorem continuous_back (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) :
    Continuous fun g : HA k σ J => φ.symm ((matHom k σ J g).1 *ᵥ φ 1) := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  haveI := isScalarTower_base (k := k) (P := P)
  haveI : ContinuousAdd (k ⊗[F] Fld P) := IsModuleTopology.toContinuousAdd k _
  have h1 : Continuous (φ.symm.toLinearMap.restrictScalars k) := IsModuleTopology.continuous_of_linearMap _
  refine h1.comp (Continuous.matrix_mulVec ?_ continuous_const)
  exact Units.continuous_val.comp (isEmbedding_matHom k σ J).continuous

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM r n P J hJ k _ _ _ _ _ x φ h`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1`. Use `haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _`. Take `⟨-, -, hinj, hrange⟩` from `GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hCM r n P J hJ k x φ h`. Set `e0 : Tor P k ≃* cent (gam h)` to `(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)`.

Establish `he : ∀ t, (e0 t).1 = torEmb h t` using `fun t => rfl`. Establish `hs : ∀ s, torEmb h (e0.symm s) = s.1` using `fun s => by rw [← he, e0.apply_symm_apply]`. Establish `hback : ∀ s, (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0 = φ.symm ((matHom k σ J s.1).1 *ᵥ φ 1)` using `fun s => by rw [← torUnit_val, GlobalTheory.TorCentTop.torUnit_eq h, hs]`. Set `e : Tor P k ≃ₜ* cent (gam h)` to `{ e0 with continuous_toFun := continuous_induced_rng.2 (GlobalTheory.TorCentTop.continuous_torEmb h) continuous_invFun := by`. Use `(isEmbedding_matHom k (star' P) (one₁ P)).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Express the relevant statement in the definitionally equal form `Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0`. Simplify using `only [hback]`. Conclude with `(GlobalTheory.TorCentTop.continuous_back φ).comp continuous_subtype_val`.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim i 0, Subsingleton.elim j 0]`. Express the relevant statement in the definitionally equal form `Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s))⁻¹.1 0 0`. Simplify using `only [← map_inv, hback]`. Conclude with `(GlobalTheory.TorCentTop.continuous_back φ).comp (continuous_subtype_val.comp continuous_inv) }`.

Use `⟨e, fun t => rfl, fun dt => ?_⟩` and prove the remaining obligations. Use `haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _`. Establish `eh : (k ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → k)`. Set `b` to `(Algebra.TensorProduct.basis k (Module.finBasis F E)).equivFun`.

Use the proof step `{ b.toEquiv with continuous_toFun := IsModuleTopology.continuous_of_linearMap b.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap }`. Use `haveI : T2Space (k ⊗[F] E) := eh.isEmbedding.t2Space`. Use `haveI : T2Space (GL (Fin n) (k ⊗[F] E)) := Units.isEmbedding_embedProduct.t2Space`. Use `haveI : T2Space (HA k σ J) := (isEmbedding_matHom k σ J).t2Space`. Establish `hset : (cent (gam h) : Set (HA k σ J)) = {g | gam h * g = g * gam h}`.

Use extensionality with `g`. Simplify using `[cent, Subgroup.mem_centralizer_iff]`. Establish `hclosed : IsClosed (cent (gam h) : Set (HA k σ J))`. Rewrite using `[hset]`. Conclude with `isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)`.

Establish `hf : (torEmb h : Tor P k → HA k σ J) = Subtype.val ∘ e` using `funext fun t => rfl`. Unfold `centMeas`. Rewrite using `[hf, ← Measure.map_map measurable_subtype_coe (map_continuous e).measurable]`. Conclude with `(MeasurableEmbedding.subtype_coe hclosed.measurableSet).comap_map _`.
-/
theorem torEquiv_cent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ e : Tor P k ≃ₜ* cent (gam h), (∀ t, (e t).1 = torEmb h t) ∧ ∀ dt : Measure (Tor P k), centMeas h dt = dt.map e := by
  intro F E _ _ _ _ _ σ hCM r n P J hJ k _ _ _ _ _ x φ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  obtain ⟨-, -, hinj, hrange⟩ := GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hCM r n P J hJ k x φ h
  let e0 : Tor P k ≃* cent (gam h) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  have he : ∀ t, (e0 t).1 = torEmb h t := fun t => rfl
  have hs : ∀ s, torEmb h (e0.symm s) = s.1 := fun s => by rw [← he, e0.apply_symm_apply]
  have hback : ∀ s, (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0 = φ.symm ((matHom k σ J s.1).1 *ᵥ φ 1) :=
    fun s => by rw [← torUnit_val, GlobalTheory.TorCentTop.torUnit_eq h, hs]
  let e : Tor P k ≃ₜ* cent (gam h) :=
    { e0 with
      continuous_toFun := continuous_induced_rng.2 (GlobalTheory.TorCentTop.continuous_torEmb h)
      continuous_invFun := by
        refine (isEmbedding_matHom k (star' P) (one₁ P)).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
        · refine continuous_matrix fun i j => ?_
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
          change Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0
          simp only [hback]
          exact (GlobalTheory.TorCentTop.continuous_back φ).comp continuous_subtype_val
        · refine continuous_matrix fun i j => ?_
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
          change Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s))⁻¹.1 0 0
          simp only [← map_inv, hback]
          exact (GlobalTheory.TorCentTop.continuous_back φ).comp (continuous_subtype_val.comp continuous_inv) }
  refine ⟨e, fun t => rfl, fun dt => ?_⟩
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  have eh : (k ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → k) :=
    let b := (Algebra.TensorProduct.basis k (Module.finBasis F E)).equivFun
    { b.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap }
  haveI : T2Space (k ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : T2Space (GL (Fin n) (k ⊗[F] E)) := Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (HA k σ J) := (isEmbedding_matHom k σ J).t2Space
  have hset : (cent (gam h) : Set (HA k σ J)) = {g | gam h * g = g * gam h} := by
    ext g; simp [cent, Subgroup.mem_centralizer_iff]
  have hclosed : IsClosed (cent (gam h) : Set (HA k σ J)) := by
    rw [hset]; exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have hf : (torEmb h : Tor P k → HA k σ J) = Subtype.val ∘ e := funext fun t => rfl
  unfold centMeas
  rw [hf, ← Measure.map_map measurable_subtype_coe (map_continuous e).measurable]
  exact (MeasurableEmbedding.subtype_coe hclosed.measurableSet).comap_map _

end GlobalTheory.TorCentTop
