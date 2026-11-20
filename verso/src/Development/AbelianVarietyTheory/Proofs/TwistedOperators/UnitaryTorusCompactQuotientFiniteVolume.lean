import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiples
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLattice

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TorCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2 τ, h.2.2.2 τ, star_star]`.
-/
theorem sigma_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

/- English proof (translation)
Establish `hE : ∀ e : E, star' P (star' P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e`. Introduce `e`. Rewrite using `[star'_algebraMap, star'_algebraMap, sigma_invol h]`. Establish `hα : star' P (star' P (alpha P)) = alpha P`. Rewrite using `[star'_alpha, map_inv₀, star'_alpha, inv_inv]`.

Take `⟨p, rfl⟩ : ∃ p, AdjoinRoot.mk P.1 p = x` from `AdjoinRoot.mk_surjective x`. Set `g : Fld P →+* Fld P` to `((star' P).comp (star' P)).toRingHom`. Establish `hg : g.comp (algebraMap E (Fld P)) = algebraMap E (Fld P)` using `RingHom.ext hE`. Establish `hgα : g (alpha P) = alpha P` using `hα`. Establish `key : AdjoinRoot.mk P.1 p = Polynomial.eval₂ (algebraMap E (Fld P)) (alpha P) p`.

Rewrite using `[← AdjoinRoot.aeval_eq, Polynomial.aeval_def]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `g (AdjoinRoot.mk P.1 p) = AdjoinRoot.mk P.1 p`. Rewrite using `[key, Polynomial.hom_eval₂, hg, hgα]`.
-/
theorem star'_star' (h : IsCMExt F E σ) (P : PPol σ r) (x : Fld P) : star' P (star' P x) = x := by
  have hE : ∀ e : E, star' P (star' P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e := by
    intro e
    rw [star'_algebraMap, star'_algebraMap, sigma_invol h]
  have hα : star' P (star' P (alpha P)) = alpha P := by
    rw [star'_alpha, map_inv₀, star'_alpha, inv_inv]
  obtain ⟨p, rfl⟩ : ∃ p, AdjoinRoot.mk P.1 p = x := AdjoinRoot.mk_surjective x
  let g : Fld P →+* Fld P := ((star' P).comp (star' P)).toRingHom
  have hg : g.comp (algebraMap E (Fld P)) = algebraMap E (Fld P) := RingHom.ext hE
  have hgα : g (alpha P) = alpha P := hα
  have key : AdjoinRoot.mk P.1 p = Polynomial.eval₂ (algebraMap E (Fld P)) (alpha P) p := by
    rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
    rfl
  change g (AdjoinRoot.mk P.1 p) = AdjoinRoot.mk P.1 p
  rw [key, Polynomial.hom_eval₂, hg, hgα]

instance finiteFE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

instance finiteFL (P : PPol σ r) : Module.Finite F (Fld P) := Module.Finite.trans E (Fld P)

/- English proof (translation)
The claim follows from `GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice GlobalTheory.RegSSLattice.tensorLattice F (Fld P) (star' P) (GlobalTheory.RegSS.fieldUnitBounded_of_packing GlobalTheory.RegSS.normOnePacking GlobalTheory.RegSSLattice.tensorLattice F (Fld P) (star' P) (Field.toIsField _) (sta …`.
-/
theorem normBounded (h : IsCMExt F E σ) (P : PPol σ r) : GlobalTheory.RegSS.NormBounded F (Fld P) (star' P) :=
  GlobalTheory.RegSS.normOfUnitBounded_of_tensorLattice GlobalTheory.RegSSLattice.tensorLattice F (Fld P) (star' P)
    (GlobalTheory.RegSS.fieldUnitBounded_of_packing GlobalTheory.RegSS.normOnePacking GlobalTheory.RegSSLattice.tensorLattice
      F (Fld P) (star' P) (Field.toIsField _) (star'_star' h P))

end GlobalTheory.TorCompact

namespace GlobalTheory.TorCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

def swapE (P : PPol σ r) : Fld P ⊗[F] AF F ≃ₐ[F] AF F ⊗[F] Fld P := Algebra.TensorProduct.comm F _ _

/- English proof (translation)
Use `letI : Algebra (AF F) (Fld P ⊗[F] AF F) := Algebra.TensorProduct.rightAlgebra`. Use `letI : TopologicalSpace (Fld P ⊗[F] AF F) := Formalism.BasicNotions.tensTopL (F := F) (E := Fld P) (AF F)`. Use `haveI : IsModuleTopology (AF F) (Fld P ⊗[F] AF F) := ⟨rfl⟩`. Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] Fld P) := ⟨rfl⟩`. Use `haveI : ContinuousAdd (AF F ⊗[F] Fld P) := ModuleTopology.continuousAdd (AF F) (AF F ⊗[F] Fld P)`.

Use `haveI : ContinuousSMul (AF F) (AF F ⊗[F] Fld P) := ModuleTopology.continuousSMul (AF F) (AF F ⊗[F] Fld P)`. Set `f : (Fld P ⊗[F] AF F) →ₗ[AF F] (AF F ⊗[F] Fld P)` to `{ toFun := swapE P map_add' := map_add _ map_smul' := fun c u => by`. Rewrite using `[RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `congr 1 }`. Conclude with `IsModuleTopology.continuous_of_linearMap f`.
-/
theorem continuous_swapE (P : PPol σ r) :
    @Continuous _ _ (Formalism.BasicNotions.tensTopL (F := F) (E := Fld P) (AF F)) (topTens (F := F) (E := Fld P) (AF F))
      (swapE P) := by
  letI : Algebra (AF F) (Fld P ⊗[F] AF F) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (Fld P ⊗[F] AF F) := Formalism.BasicNotions.tensTopL (F := F) (E := Fld P) (AF F)
  haveI : IsModuleTopology (AF F) (Fld P ⊗[F] AF F) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] Fld P) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] Fld P) := ModuleTopology.continuousAdd (AF F) (AF F ⊗[F] Fld P)
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] Fld P) := ModuleTopology.continuousSMul (AF F) (AF F ⊗[F] Fld P)
  let f : (Fld P ⊗[F] AF F) →ₗ[AF F] (AF F ⊗[F] Fld P) :=
    { toFun := swapE P
      map_add' := map_add _
      map_smul' := fun c u => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1 }
  exact IsModuleTopology.continuous_of_linearMap f

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a => simp [swapE, Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem swapE_sigR (P : PPol σ r) (u : Fld P ⊗[F] AF F) :
    swapE P (Formalism.UG.sigR (star' P) (AF F) u) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (swapE P u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [swapE, Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Simplify using `[swapE, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`.
-/
theorem swapE_inclE (P : PPol σ r) (β : Fld P) :
    swapE P (Formalism.UG.inclE (F := F) (AF F) β) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) β := by
  simp [swapE, Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

/- English proof (translation)
Simplify using `only [Formalism.UG.UJ, Subgroup.mem_mk, Set.mem_setOf_eq, Submonoid.mem_mk, Subsemigroup.mem_mk]`. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using `[Formalism.UG.cT, Matrix.GeneralLinearGroup.scalar, hw]`.
-/
theorem scalar_mem_UJ {S : Type} [CommRing S] (s : S →+* S) (w : Sˣ) (hw : s w * w = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) w ∈ Formalism.UG.UJ s (1 : Matrix (Fin 1) (Fin 1) S) := by
  simp only [Formalism.UG.UJ, Subgroup.mem_mk, Set.mem_setOf_eq, Submonoid.mem_mk, Subsemigroup.mem_mk]
  ext i j
  fin_cases i
  fin_cases j
  simp [Formalism.UG.cT, Matrix.GeneralLinearGroup.scalar, hw]

/- English proof (translation)
Use `show (1 : Matrix (Fin 1) (Fin 1) (Fld P)).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) = 1`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem JR_one (P : PPol σ r) : JR (F := F) (AF F) (one₁ P) = 1 := by
  show (1 : Matrix (Fin 1) (Fin 1) (Fld P)).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) = 1
  exact Matrix.map_one _ (map_zero _) (map_one _)

def torOf (P : PPol σ r) (w : (AF F ⊗[F] Fld P)ˣ) (hw : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) w * w = 1) :
    Tor P (AF F) :=
  (⟨Matrix.GeneralLinearGroup.scalar (Fin 1) w, by
    change _ ∈ Formalism.UG.UJ _ (JR (AF F) (one₁ P))
    rw [JR_one]
    exact scalar_mem_UJ _ w hw⟩ : HR (AF F) (star' P) (one₁ P))

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show Matrix.det ((Matrix.GeneralLinearGroup.scalar (Fin 1) w).1) = (w : AF F ⊗[F] Fld P)`. Rewrite using `[Matrix.det_fin_one]`. Simplify using `[Matrix.GeneralLinearGroup.scalar]`.
-/
theorem torUnit_torOf (P : PPol σ r) (w : (AF F ⊗[F] Fld P)ˣ) (hw) : torUnit (torOf P w hw) = w := by
  apply Units.ext
  show Matrix.det ((Matrix.GeneralLinearGroup.scalar (Fin 1) w).1) = (w : AF F ⊗[F] Fld P)
  rw [Matrix.det_fin_one]
  simp [Matrix.GeneralLinearGroup.scalar]

/- English proof (translation)
Introduce `a b hab`. Establish `hv : Matrix.det (Subtype.val a).1 = Matrix.det (Subtype.val b).1` using `congrArg Units.val hab`. Rewrite `hv` using `[Matrix.det_fin_one, Matrix.det_fin_one]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Conclude with `hv`.
-/
theorem torUnit_injective (P : PPol σ r) : Function.Injective (torUnit (P := P) (k := AF F)) := by
  intro a b hab
  have hv : Matrix.det (Subtype.val a).1 = Matrix.det (Subtype.val b).1 := congrArg Units.val hab
  rw [Matrix.det_fin_one, Matrix.det_fin_one] at hv
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  exact hv

end GlobalTheory.TorCompact

namespace GlobalTheory.TorCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

/- English proof (translation)
Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`.
-/
theorem sigR_inclR (P : PPol σ r) (x : Fld P) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (star' P x) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

def ratOf (P : PPol σ r) (β : Fld P) (hβ : β * star' P β = 1) : Tor P (AF F) :=
  torOf P (Units.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) : Fld P →+* _).toMonoidHom
    (Units.mkOfMulEqOne β (star' P β) hβ)) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) β) *
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) β = 1
      rw [sigR_inclR, ← map_mul, mul_comm, hβ, map_one])

/- English proof (translation)
Establish `hu : Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.mkOfMulEqOne β (star' P β) hβ) ∈ Formalism.UG.UJ (star' P : Fld P →+* Fld P) (one₁ P)` using `scalar_mem_UJ _ _ (by simpa [mul_comm] using hβ)`. Express the relevant statement in the definitionally equal form `Subtype.val (ratOf P β hβ) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (AF F) (star' P) (one₁ P)`. Rewrite using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin, Subgroup.mem_map]`. Use `⟨_, hu, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using `[ratOf, torOf, Formalism.UG.bc, Matrix.GeneralLinearGroup.scalar, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`.
-/
theorem ratOf_mem (P : PPol σ r) (β : Fld P) (hβ : β * star' P β = 1) :
    ratOf P β hβ ∈ ratPts (star' P) (one₁ P) := by
  have hu : Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.mkOfMulEqOne β (star' P β) hβ) ∈
      Formalism.UG.UJ (star' P : Fld P →+* Fld P) (one₁ P) :=
    scalar_mem_UJ _ _ (by simpa [mul_comm] using hβ)
  change Subtype.val (ratOf P β hβ) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (AF F) (star' P) (one₁ P)
  rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin, Subgroup.mem_map]
  refine ⟨_, hu, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [ratOf, torOf, Formalism.UG.bc, Matrix.GeneralLinearGroup.scalar, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

/- English proof (translation)
Simplify using `[ratOf, torUnit_torOf]`.
-/
theorem torUnit_ratOf (P : PPol σ r) (β : Fld P) (hβ : β * star' P β = 1) :
    (torUnit (ratOf P β hβ)).1 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) β := by
  simp [ratOf, torUnit_torOf]

/- English proof (translation)
Take `⟨D, hD, hDu⟩` from `normBounded h P`. Use `letI tL : TopologicalSpace (Fld P ⊗[F] AF F) := Formalism.BasicNotions.tensTopL (F := F) (E := Fld P) (AF F)`. Take `⟨hTR, -, hT2, -, -, -, -⟩` from `GlobalTheory.RegSSLattice.tensorLattice F (Fld P)`. Use `haveI := hTR`. Use `haveI := hT2`.

Use `letI : Algebra (AF F) (Fld P ⊗[F] AF F) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsModuleTopology (AF F) (Fld P ⊗[F] AF F) := ⟨rfl⟩`. Use `haveI : ContinuousAdd (Fld P ⊗[F] AF F) := ModuleTopology.continuousAdd (AF F) (Fld P ⊗[F] AF F)`. Use `haveI : ContinuousSMul (AF F) (Fld P ⊗[F] AF F) := ModuleTopology.continuousSMul (AF F) (Fld P ⊗[F] AF F)`. Establish `hsig : Continuous (Formalism.UG.sigR (star' P) (AF F))`.

Set `f : (Fld P ⊗[F] AF F) →ₗ[AF F] (Fld P ⊗[F] AF F)` to `{ toFun := Formalism.UG.sigR (star' P) (AF F) map_add' := map_add _ map_smul' := fun c u => by`. Rewrite using `[RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `congr 1`. Use `show Formalism.UG.sigR (star' P) (AF F) ((1 : Fld P) ⊗ₜ[F] c) = (1 : Fld P) ⊗ₜ[F] c`. Simplify using `[Formalism.UG.sigR] }`.

Conclude with `IsModuleTopology.continuous_of_linearMap f`. Establish `hsw` using `continuous_swapE P`. Set `N : Set (Fld P ⊗[F] AF F)` to `{u | u * Formalism.UG.sigR (star' P) (AF F) u = 1}`. Establish `hN : IsClosed N` using `isClosed_eq (continuous_id.mul hsig) continuous_const`. Establish `hK : IsCompact (D ∩ N)` using `hD.inter_right hN`.

Establish `hmul : ∀ x : N, swapE P x.1 * swapE P (Formalism.UG.sigR (star' P) (AF F) x.1) = 1` using `fun x => by`. Rewrite using `[← map_mul, x.2, map_one]`. Establish `hmul' : ∀ x : N, swapE P (Formalism.UG.sigR (star' P) (AF F) x.1) * swapE P x.1 = 1` using `fun x => by`. Rewrite using `[mul_comm, hmul]`. Set `uN : N → (AF F ⊗[F] Fld P)ˣ` to `fun x => ⟨swapE P x.1, swapE P (Formalism.UG.sigR (star' P) (AF F) x.1), hmul x, hmul' x⟩`.

Establish `hwN : ∀ x : N, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (uN x) * uN x = 1` using `fun x => by show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (swapE P x.1) * swapE P x.1 = 1`. Rewrite using `[← swapE_sigR]`. Conclude with `hmul' x`. Set `Ψ : N → Tor P (AF F)` to `fun x => torOf P (uN x) (hwN x)`. Establish `hΨ : Continuous Ψ`.

Establish `hsc : Continuous fun x : N => Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x)`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `he : (Units.val ∘ fun x : N => Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x)) = fun x => Matrix.diagonal fun _ => swapE P x.1`. Use function extensionality and compare the values at `x`. Use extensionality with `i j`.

Use `fin_cases i`. Use `fin_cases j`. Simplify using `[uN, Matrix.GeneralLinearGroup.scalar]`. Rewrite using `[he]`. Conclude with `(continuous_pi fun _ => hsw.comp continuous_subtype_val).matrix_diagonal`.

Establish `he : (fun x : N => (((Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x))⁻¹ : GL (Fin 1) _) : Matrix (Fin 1) (Fin 1) _)) = fun x => Matrix.diagonal fun _ => swapE P (Formalism.UG.sigR (star' P) (AF F) x.1)`. Use function extensionality and compare the values at `x`. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`.

Simplify using `[uN, Matrix.GeneralLinearGroup.scalar]`. Rewrite using `[he]`. Conclude with `(continuous_pi fun _ => hsw.comp (hsig.comp continuous_subtype_val)).matrix_diagonal`. Conclude with `hsc.subtype_mk _`. Set `Ks : Set N` to `Subtype.val ⁻¹' (D ∩ N)`.

Establish `hKs : IsCompact Ks`. Rewrite using `[Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_comm, Set.inter_assoc, Set.inter_self]`. Conclude with `hK`. Use `⟨Ψ '' Ks, hKs.image hΨ, fun t => ?_⟩` and prove the remaining obligations. Establish `hwn` using `torUnit_norm t`.

Set `u` to `(swapE P).symm (torUnit t).1`. Establish `hsu : swapE P u = (torUnit t).1` using `(swapE P).apply_symm_apply _`. Establish `hu : u * Formalism.UG.sigR (star' P) (AF F) u = 1`. Apply `(swapE P).injective` to reduce the goal to its premises. Rewrite using `[map_mul, swapE_sigR, hsu, map_one]`.

Conclude with `hwn`. Take `⟨β, hβ, hβD⟩` from `hDu u hu`. Establish `hiβ : Formalism.UG.sigR (star' P) (AF F) (Formalism.UG.inclE (F` using `F) (AF F) β) = Formalism.UG.inclE (F := F) (AF F) (star' P β) := by`. Apply `(swapE P).injective` to reduce the goal to its premises. Rewrite using `[swapE_sigR, swapE_inclE, swapE_inclE, sigR_inclR]`.

Establish `hmem : u * Formalism.UG.inclE (F` using `F) (AF F) β ∈ N := by show _ * _ = _`. Rewrite using `[map_mul, hiβ, mul_mul_mul_comm, hu, one_mul, ← map_mul, hβ, map_one]`. Use `⟨ratOf P β hβ, ratOf_mem P β hβ, ⟨u * Formalism.UG.inclE (F := F) (AF F) β, hmem⟩, ⟨hβD, hmem⟩, ?_⟩` and prove the remaining obligations. Apply `torUnit_injective P` to reduce the goal to its premises. Rewrite using `[show Ψ ⟨u * Formalism.UG.inclE (F := F) (AF F) β, hmem⟩ = torOf P (uN ⟨_, hmem⟩) (hwN ⟨_, hmem⟩) from rfl, torUnit_torOf, map_mul]`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul]`. Use `show swapE P (u * Formalism.UG.inclE (F := F) (AF F) β) = _`. Rewrite using `[map_mul, swapE_inclE, hsu, torUnit_ratOf, mul_comm]`.
-/
theorem exists_compact (h : IsCMExt F E σ) (P : PPol σ r) :
    ∃ C : Set (Tor P (AF F)), IsCompact C ∧ ∀ t : Tor P (AF F), ∃ γ ∈ ratPts (star' P) (one₁ P), γ * t ∈ C := by
  obtain ⟨D, hD, hDu⟩ := normBounded h P
  letI tL : TopologicalSpace (Fld P ⊗[F] AF F) := Formalism.BasicNotions.tensTopL (F := F) (E := Fld P) (AF F)
  obtain ⟨hTR, -, hT2, -, -, -, -⟩ := GlobalTheory.RegSSLattice.tensorLattice F (Fld P)
  haveI := hTR
  haveI := hT2
  letI : Algebra (AF F) (Fld P ⊗[F] AF F) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (AF F) (Fld P ⊗[F] AF F) := ⟨rfl⟩
  haveI : ContinuousAdd (Fld P ⊗[F] AF F) := ModuleTopology.continuousAdd (AF F) (Fld P ⊗[F] AF F)
  haveI : ContinuousSMul (AF F) (Fld P ⊗[F] AF F) := ModuleTopology.continuousSMul (AF F) (Fld P ⊗[F] AF F)
  have hsig : Continuous (Formalism.UG.sigR (star' P) (AF F)) := by
    let f : (Fld P ⊗[F] AF F) →ₗ[AF F] (Fld P ⊗[F] AF F) :=
      { toFun := Formalism.UG.sigR (star' P) (AF F)
        map_add' := map_add _
        map_smul' := fun c u => by
          rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1
          show Formalism.UG.sigR (star' P) (AF F) ((1 : Fld P) ⊗ₜ[F] c) = (1 : Fld P) ⊗ₜ[F] c
          simp [Formalism.UG.sigR] }
    exact IsModuleTopology.continuous_of_linearMap f
  have hsw := continuous_swapE P
  let N : Set (Fld P ⊗[F] AF F) := {u | u * Formalism.UG.sigR (star' P) (AF F) u = 1}
  have hN : IsClosed N := isClosed_eq (continuous_id.mul hsig) continuous_const
  have hK : IsCompact (D ∩ N) := hD.inter_right hN
  have hmul : ∀ x : N, swapE P x.1 * swapE P (Formalism.UG.sigR (star' P) (AF F) x.1) = 1 := fun x => by
    rw [← map_mul, x.2, map_one]
  have hmul' : ∀ x : N, swapE P (Formalism.UG.sigR (star' P) (AF F) x.1) * swapE P x.1 = 1 := fun x => by
    rw [mul_comm, hmul]
  let uN : N → (AF F ⊗[F] Fld P)ˣ := fun x =>
    ⟨swapE P x.1, swapE P (Formalism.UG.sigR (star' P) (AF F) x.1), hmul x, hmul' x⟩
  have hwN : ∀ x : N, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (uN x) * uN x = 1 := fun x => by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) (star' P) (swapE P x.1) * swapE P x.1 = 1
    rw [← swapE_sigR]
    exact hmul' x
  let Ψ : N → Tor P (AF F) := fun x => torOf P (uN x) (hwN x)
  have hΨ : Continuous Ψ := by
    have hsc : Continuous fun x : N => Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have he : (Units.val ∘ fun x : N => Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x)) =
            fun x => Matrix.diagonal fun _ => swapE P x.1 := by
          funext x
          ext i j
          fin_cases i
          fin_cases j
          simp [uN, Matrix.GeneralLinearGroup.scalar]
        rw [he]
        exact (continuous_pi fun _ => hsw.comp continuous_subtype_val).matrix_diagonal
      · have he : (fun x : N => (((Matrix.GeneralLinearGroup.scalar (Fin 1) (uN x))⁻¹ : GL (Fin 1) _) :
              Matrix (Fin 1) (Fin 1) _)) =
            fun x => Matrix.diagonal fun _ => swapE P (Formalism.UG.sigR (star' P) (AF F) x.1) := by
          funext x
          ext i j
          fin_cases i
          fin_cases j
          simp [uN, Matrix.GeneralLinearGroup.scalar]
        rw [he]
        exact (continuous_pi fun _ => hsw.comp (hsig.comp continuous_subtype_val)).matrix_diagonal
    exact hsc.subtype_mk _
  let Ks : Set N := Subtype.val ⁻¹' (D ∩ N)
  have hKs : IsCompact Ks := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_comm, Set.inter_assoc, Set.inter_self]
    exact hK
  refine ⟨Ψ '' Ks, hKs.image hΨ, fun t => ?_⟩
  have hwn := torUnit_norm t
  let u := (swapE P).symm (torUnit t).1
  have hsu : swapE P u = (torUnit t).1 := (swapE P).apply_symm_apply _
  have hu : u * Formalism.UG.sigR (star' P) (AF F) u = 1 := by
    apply (swapE P).injective
    rw [map_mul, swapE_sigR, hsu, map_one]
    exact hwn
  obtain ⟨β, hβ, hβD⟩ := hDu u hu
  have hiβ : Formalism.UG.sigR (star' P) (AF F) (Formalism.UG.inclE (F := F) (AF F) β) =
      Formalism.UG.inclE (F := F) (AF F) (star' P β) := by
    apply (swapE P).injective
    rw [swapE_sigR, swapE_inclE, swapE_inclE, sigR_inclR]
  have hmem : u * Formalism.UG.inclE (F := F) (AF F) β ∈ N := by
    show _ * _ = _
    rw [map_mul, hiβ, mul_mul_mul_comm, hu, one_mul, ← map_mul, hβ, map_one]
  refine ⟨ratOf P β hβ, ratOf_mem P β hβ, ⟨u * Formalism.UG.inclE (F := F) (AF F) β, hmem⟩, ⟨hβD, hmem⟩, ?_⟩
  apply torUnit_injective P
  rw [show Ψ ⟨u * Formalism.UG.inclE (F := F) (AF F) β, hmem⟩ = torOf P (uN ⟨_, hmem⟩) (hwN ⟨_, hmem⟩) from rfl,
    torUnit_torOf, map_mul]
  apply Units.ext
  rw [Units.val_mul]
  show swapE P (u * Formalism.UG.inclE (F := F) (AF F) β) = _
  rw [map_mul, swapE_inclE, hsu, torUnit_ratOf, mul_comm]

end GlobalTheory.TorCompact

namespace GlobalTheory.TorCompact

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h r P`. Use `⟨exists_compact h P, fun dt hdt => ?_⟩` and prove the remaining obligations. Take `⟨C, hC, hCt⟩` from `exists_compact h P`. Establish `hs` using `GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (ratPts (star' P) (one₁ P)) dt`. Use `haveI : Countable (ratPts (star' P) (one₁ P)) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`.

Rewrite using `[torVol, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hs]`. Use `ne_top_of_le_ne_top (hC.measure_lt_top (μ := dt)).ne ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `measure_mono` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨γ, hγ, hγx⟩` from `hCt x`. Use `Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ⟨γ * x, hγx, ?_⟩, hx⟩` and prove the remaining obligations. Apply the tactic sequence `all_goals simp [Subgroup.smul_def]`. Use `_ ≤ ∑' g : ratPts (star' P) (one₁ P), dt ((fun y => g • y) '' C ∩ GlobalTheory.AutomorphicL2Unitary.stdDom (ratPts (star' P) (one₁ P))) := measure_iUnion_le _`. Use `_ = dt C := (hs.measure_eq_tsum C).symm`.
-/
theorem torus_compact_finiteVol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∃ C : Set (Tor P (AF F)), IsCompact C ∧ ∀ t : Tor P (AF F), ∃ γ ∈ ratPts (star' P) (one₁ P), γ * t ∈ C) ∧ ∀ dt : Measure (Tor P (AF F)), dt.IsHaarMeasure → torVol P dt ≠ ⊤ := by
  intro F E _ _ _ _ _ σ h r P
  refine ⟨exists_compact h P, fun dt hdt => ?_⟩
  obtain ⟨C, hC, hCt⟩ := exists_compact h P
  have hs := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (ratPts (star' P) (one₁ P)) dt
  haveI : Countable (ratPts (star' P) (one₁ P)) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  rw [torVol, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hs]
  refine ne_top_of_le_ne_top (hC.measure_lt_top (μ := dt)).ne ?_
  calc dt (GlobalTheory.AutomorphicL2Unitary.stdDom (ratPts (star' P) (one₁ P)))
      ≤ dt (⋃ g : ratPts (star' P) (one₁ P),
          (fun y => g • y) '' C ∩ GlobalTheory.AutomorphicL2Unitary.stdDom (ratPts (star' P) (one₁ P))) := by
        apply measure_mono
        intro x hx
        obtain ⟨γ, hγ, hγx⟩ := hCt x
        refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ⟨γ * x, hγx, ?_⟩, hx⟩
        all_goals simp [Subgroup.smul_def]
    _ ≤ ∑' g : ratPts (star' P) (one₁ P),
          dt ((fun y => g • y) '' C ∩ GlobalTheory.AutomorphicL2Unitary.stdDom (ratPts (star' P) (one₁ P))) :=
        measure_iUnion_le _
    _ = dt C := (hs.measure_eq_tsum C).symm

end GlobalTheory.TorCompact
