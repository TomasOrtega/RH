import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import GroundTheory.AutomorphicForms.Anisotropic

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.Compact

section General

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open scoped NumberField.AdeleRing

attribute [local instance] adeleTensorTopology isModuleTopology_adeleTensor
  isTopologicalRing_adeleTensor t2Space_adeleTensor

set_option maxSynthPendingDepth 1 in

/- English proof (translation)
Take `⟨Ω, hΩ, hdec⟩` from `exists_isCompact_normOneUnits (K := K) (D := D) (Module.finBasis K D)`. Set `f : (𝔸[K] ⊗[K] D)ˣ →* Bˣ` to `Units.map (Φ : 𝔸[K] ⊗[K] D →* B)`. Establish `hΦ : Continuous (Φ : 𝔸[K] ⊗[K] D →* B)` using `IsModuleTopology.continuous_of_linearMap Φ.toLinearEquiv.toLinearMap`. Establish `hf : Continuous f` using `Continuous.units_map _ hΦ`. Use `⟨(fun w => (f w)⁻¹) '' Ω, hΩ.image hf.inv, fun y => ?_⟩` and prove the remaining obligations.

Set `g : Bˣ →* (𝔸[K] ⊗[K] D)ˣ` to `Units.map (Φ.symm : B →* 𝔸[K] ⊗[K] D)`. Establish `hfg : f (g y) = y` using `Units.ext (by simp [f, g])`. Take `⟨a, ha⟩` from `exists_scalar_mem_normOneUnits (Module.finBasis K D) (g y)⁻¹`. Take `⟨δ, hδ⟩` from `hdec _ ha`. Use `⟨_, ⟨_, hδ, rfl⟩, δ⁻¹, a, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `y = (f _)⁻¹ * f (rationalUnits K D δ⁻¹) * f (scalarUnits K D a)`. Simplify using `only [map_mul, map_inv, hfg]`. Use `group`.
-/
theorem exists_compact_transport {K D B : Type*} [Field K] [NumberField K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Ring B] [Algebra 𝔸[K] B] [TopologicalSpace B] [IsTopologicalRing B]
    [ContinuousSMul 𝔸[K] B] (Φ : 𝔸[K] ⊗[K] D ≃ₐ[𝔸[K]] B) :
    ∃ C : Set Bˣ, IsCompact C ∧ ∀ y : Bˣ, ∃ c ∈ C, ∃ δ : Dˣ, ∃ z : (𝔸[K])ˣ,
      y = c * Units.map (Φ : 𝔸[K] ⊗[K] D →* B) (rationalUnits K D δ) *
        Units.map (Φ : 𝔸[K] ⊗[K] D →* B) (scalarUnits K D z) := by
  obtain ⟨Ω, hΩ, hdec⟩ := exists_isCompact_normOneUnits (K := K) (D := D) (Module.finBasis K D)
  let f : (𝔸[K] ⊗[K] D)ˣ →* Bˣ := Units.map (Φ : 𝔸[K] ⊗[K] D →* B)
  have hΦ : Continuous (Φ : 𝔸[K] ⊗[K] D →* B) :=
    IsModuleTopology.continuous_of_linearMap Φ.toLinearEquiv.toLinearMap
  have hf : Continuous f := Continuous.units_map _ hΦ
  refine ⟨(fun w => (f w)⁻¹) '' Ω, hΩ.image hf.inv, fun y => ?_⟩
  let g : Bˣ →* (𝔸[K] ⊗[K] D)ˣ := Units.map (Φ.symm : B →* 𝔸[K] ⊗[K] D)
  have hfg : f (g y) = y := Units.ext (by simp [f, g])
  obtain ⟨a, ha⟩ := exists_scalar_mem_normOneUnits (Module.finBasis K D) (g y)⁻¹
  obtain ⟨δ, hδ⟩ := hdec _ ha
  refine ⟨_, ⟨_, hδ, rfl⟩, δ⁻¹, a, ?_⟩
  change y = (f _)⁻¹ * f (rationalUnits K D δ⁻¹) * f (scalarUnits K D a)
  simp only [map_mul, map_inv, hfg]
  group

end General

section Quat

variable {F : Type} [Field F] {d β : F} {R : Type} [CommRing R] [Algebra F R]

@[reducible] def divRing (h : ∀ x : Q d β F, qn x = 0 → x = 0) : DivisionRing (Q d β F) :=
  { (inferInstance : Ring (Q d β F)) with
    inv := fun x => (qn x)⁻¹ • star x
    exists_pair_ne := ⟨0, 1, fun e => zero_ne_one (congrArg QuaternionAlgebra.re e)⟩
    mul_inv_cancel := fun x hx => by
      have hq : qn x ≠ 0 := fun e => hx (h x e)
      change x * ((qn x)⁻¹ • star x) = 1
      rw [mul_smul_comm, mul_star_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hq, map_one]
    inv_zero := by
      change (qn (0 : Q d β F))⁻¹ • star (0 : Q d β F) = 0
      simp
    nnqsmul := _
    qsmul := _ }

def ratA : Q d β F →ₐ[F] Q d β R :=
  { (rat : Q d β F →+* Q d β R) with
    commutes' := fun r => by
      have e : algebraMap F (Q d β R) r = ⟨algebraMap F R r, 0, 0, 0⟩ := rfl
      ext <;> simp [rat, qmap, Algebra.ofId_apply, QuaternionAlgebra.algebraMap_eq, e] }

def phi : R ⊗[F] Q d β F →ₐ[R] Q d β R :=
  Algebra.TensorProduct.lift (Algebra.ofId R (Q d β R)) ratA (fun a _ => Algebra.commutes a _)

/- English proof (translation)
Conclude with `Algebra.TensorProduct.lift_tmul _ _ _ a x`.
-/
theorem phi_tmul (a : R) (x : Q d β F) :
    phi (d := d) (β := β) (R := R) (a ⊗ₜ[F] x) = algebraMap R (Q d β R) a * rat x := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ a x

def psi (x : Q d β R) : R ⊗[F] Q d β F :=
  x.re ⊗ₜ[F] (⟨1, 0, 0, 0⟩ : Q d β F) + x.imI ⊗ₜ[F] (⟨0, 1, 0, 0⟩ : Q d β F) +
    x.imJ ⊗ₜ[F] (⟨0, 0, 1, 0⟩ : Q d β F) + x.imK ⊗ₜ[F] (⟨0, 0, 0, 1⟩ : Q d β F)

/- English proof (translation)
Simplify using `only [psi, map_add, phi_tmul]`. Apply the tactic sequence `ext <;> simp [rat, qmap, QuaternionAlgebra.algebraMap_eq]`.
-/
theorem phi_psi (x : Q d β R) : phi (d := d) (β := β) (R := R) (psi x) = x := by
  simp only [psi, map_add, phi_tmul]
  ext <;> simp [rat, qmap, QuaternionAlgebra.algebraMap_eq]

/- English proof (translation)
Simplify using `only [psi, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add, TensorProduct.add_tmul]`. Normalize the expressions using the abelian group laws.
-/
theorem psi_add (x y : Q d β R) : psi (x + y) = psi x + psi y := by
  simp only [psi, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, TensorProduct.add_tmul]
  abel

/- English proof (translation)
Rewrite using `[mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]`.
-/
theorem mul_algebraMap_tmul (a : R) (c : F) (y : Q d β F) :
    (a * algebraMap F R c) ⊗ₜ[F] y = a ⊗ₜ[F] (c • y) := by
  rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp [psi]`. Consider the case `add x y hx hy => rw [map_add, psi_add, hx, hy]`. Consider the case `tmul a x`. Rewrite using `[phi_tmul]`.

Establish `e : x = x.re • (⟨1, 0, 0, 0⟩ : Q d β F) + x.imI • (⟨0, 1, 0, 0⟩ : Q d β F) + x.imJ • (⟨0, 0, 1, 0⟩ : Q d β F) + x.imK • (⟨0, 0, 0, 1⟩ : Q d β F)`. Apply the tactic sequence `ext <;> simp`. Establish `key : psi (algebraMap R (Q d β R) a * rat x) = (a * algebraMap F R x.re) ⊗ₜ[F] (⟨1, 0, 0, 0⟩ : Q d β F) + (a * algebraMap F R x.imI) ⊗ₜ[F] (⟨0, 1, 0, 0⟩ : Q d β F) + (a * algebraMap F R x.imJ) ⊗ₜ[F] (⟨0, 0, 1, 0⟩ : Q d β F) + (a * algebraMap F R x.imK) ⊗ₜ[F] (⟨0, 0, 0, 1⟩ : Q d β …`. Simplify using `[psi, rat, qmap, QuaternionAlgebra.algebraMap_eq, Algebra.ofId_apply]`. Rewrite using `[key]`.

Simplify using `only [mul_algebraMap_tmul]`. Rewrite using `[← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← e]`.
-/
theorem psi_phi (t : R ⊗[F] Q d β F) : psi (phi (d := d) (β := β) (R := R) t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [psi]
  | add x y hx hy => rw [map_add, psi_add, hx, hy]
  | tmul a x =>
    rw [phi_tmul]
    have e : x = x.re • (⟨1, 0, 0, 0⟩ : Q d β F) + x.imI • (⟨0, 1, 0, 0⟩ : Q d β F) +
        x.imJ • (⟨0, 0, 1, 0⟩ : Q d β F) + x.imK • (⟨0, 0, 0, 1⟩ : Q d β F) := by
      ext <;> simp
    have key : psi (algebraMap R (Q d β R) a * rat x) =
        (a * algebraMap F R x.re) ⊗ₜ[F] (⟨1, 0, 0, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imI) ⊗ₜ[F] (⟨0, 1, 0, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imJ) ⊗ₜ[F] (⟨0, 0, 1, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imK) ⊗ₜ[F] (⟨0, 0, 0, 1⟩ : Q d β F) := by
      simp [psi, rat, qmap, QuaternionAlgebra.algebraMap_eq, Algebra.ofId_apply]
    rw [key]
    simp only [mul_algebraMap_tmul]
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← e]

def phiEquiv : R ⊗[F] Q d β F ≃ₐ[R] Q d β R :=
  AlgEquiv.ofBijective (phi (d := d) (β := β) (R := R))
    ⟨Function.LeftInverse.injective psi_phi, Function.RightInverse.surjective phi_psi⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[continuous_q_iff]`. Simplify using `only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]`. Conclude with `⟨continuous_fst.mul (continuous_re.comp continuous_snd), continuous_fst.mul (continuous_imI.comp continuous_snd), continuous_fst.mul (continuous_imJ.comp continuous_snd), continuous_fst.mul (continuous_imK.comp continuous_snd)⟩`.
-/
theorem continuousSMul_q [TopologicalSpace R] [IsTopologicalRing R] : ContinuousSMul R (Q d β R) := by
  constructor
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  exact ⟨continuous_fst.mul (continuous_re.comp continuous_snd),
    continuous_fst.mul (continuous_imI.comp continuous_snd),
    continuous_fst.mul (continuous_imJ.comp continuous_snd),
    continuous_fst.mul (continuous_imK.comp continuous_snd)⟩

end Quat

/- English proof (translation)
Introduce `F _ _ d β h`. Use `letI : DivisionRing (Q d β F) := divRing h`. Use `haveI : ContinuousSMul (AF F) (Q d β (AF F)) := continuousSMul_q`. Take `⟨C, hC, hdec⟩` from `exists_compact_transport (K := F) (D := Q d β F) (B := Q d β (AF F)) phiEquiv`. Use `⟨C, hC, fun y => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc, δ, z, e⟩` from `hdec y`. Use `⟨c, hc, δ, z, ?_⟩` and prove the remaining obligations. Establish `h1 : Units.map (phiEquiv (d` using `d) (β := β) (R := AF F) : AF F ⊗[F] Q d β F →* Q d β (AF F)) (GroundTheory.Automorphic.Anisotropic.rationalUnits F (Q d β F) δ) = Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ := by`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `phi (d := d) (β := β) (R := AF F) ((1 : AF F) ⊗ₜ[F] (δ : Q d β F)) = rat (δ : Q d β F)`.

Rewrite using `[phi_tmul, map_one, one_mul]`. Establish `h2 : Units.map (phiEquiv (d` using `d) (β := β) (R := AF F) : AF F ⊗[F] Q d β F →* Q d β (AF F)) (GroundTheory.Automorphic.Anisotropic.scalarUnits F (Q d β F) z) = Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z := Units.ext ((phiEquiv (d := d) (β := β) (R := AF F)).commutes (z : AF F))`. Rewrite using `[e, h1, h2]`.
-/
theorem exists_isCompact_units :
    ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∃ C : Set (Q d β (AF F))ˣ, IsCompact C ∧ ∀ y : (Q d β (AF F))ˣ, ∃ c ∈ C, ∃ δ : (Q d β F)ˣ, ∃ z : (AF F)ˣ,
    y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z := by
  intro F _ _ d β h
  letI : DivisionRing (Q d β F) := divRing h
  haveI : ContinuousSMul (AF F) (Q d β (AF F)) := continuousSMul_q
  obtain ⟨C, hC, hdec⟩ := exists_compact_transport (K := F) (D := Q d β F) (B := Q d β (AF F)) phiEquiv
  refine ⟨C, hC, fun y => ?_⟩
  obtain ⟨c, hc, δ, z, e⟩ := hdec y
  refine ⟨c, hc, δ, z, ?_⟩
  have h1 : Units.map (phiEquiv (d := d) (β := β) (R := AF F) : AF F ⊗[F] Q d β F →* Q d β (AF F))
      (GroundTheory.Automorphic.Anisotropic.rationalUnits F (Q d β F) δ) =
      Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ := by
    refine Units.ext ?_
    change phi (d := d) (β := β) (R := AF F) ((1 : AF F) ⊗ₜ[F] (δ : Q d β F)) = rat (δ : Q d β F)
    rw [phi_tmul, map_one, one_mul]
  have h2 : Units.map (phiEquiv (d := d) (β := β) (R := AF F) : AF F ⊗[F] Q d β F →* Q d β (AF F))
      (GroundTheory.Automorphic.Anisotropic.scalarUnits F (Q d β F) z) =
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z :=
    Units.ext ((phiEquiv (d := d) (β := β) (R := AF F)).commutes (z : AF F))
  rw [e, h1, h2]

end GlobalTheory.CompanionTheory.PlaneSA.Compact
