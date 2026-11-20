import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

noncomputable section

namespace GlobalTheory.HeisOrbitSmooth

open scoped ContDiff

section General

variable {F : Type} [Field F] [NumberField F]

def incI (x : mixedEmbedding.mixedSpace F) : AF F := ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0⟩

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem evI_incI (x : mixedEmbedding.mixedSpace F) : evI F (incI x) = x := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) = x
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem incI_add (x y : mixedEmbedding.mixedSpace F) : incI (x + y) = incI x + incI y := by
  show (⟨_, 0⟩ : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ⟨_, 0 + 0⟩
  rw [map_add, add_zero]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem incI_smul (c : ℝ) (x : mixedEmbedding.mixedSpace F) : incI (c • x) = realAd F c * incI x := by
  show (⟨_, 0⟩ : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ⟨_ * _, 0 * 0⟩
  rw [Algebra.smul_def, map_mul, mul_zero]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem evI_realAd (c : ℝ) : evI F (realAd F c) = algebraMap ℝ _ c := evI_incI _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem evI_eq_zero {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 h

def finOne : AF F := ⟨0, 1⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem evI_finOne : evI F (finOne : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem incI_evI {a : AF F} (h : (finOne : AF F) * a = 0) : incI (evI F a) = a := by
  have h2 : a.2 = 0 := by
    have := congrArg Prod.snd h
    calc a.2 = 1 * a.2 := (one_mul _).symm
      _ = 0 := this
  show (⟨_, 0⟩ : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (a : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  refine Prod.ext ?_ h2.symm
  exact RingEquiv.symm_apply_apply _ _

local notation "Vs" κ => (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)

variable {κ : Type} [Fintype κ] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}

def lift (d : GlobalTheory.WeilM.Darboux B κ) (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) : W :=
  d.e.symm (fun i => incI (w.1 i), fun i => incI (w.2 i))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem archCo_lift (d : GlobalTheory.WeilM.Darboux B κ) (w : Vs κ) : GlobalTheory.HeisOrbit.archCo d (lift d w) = w := by
  simp [GlobalTheory.HeisOrbit.archCo, lift, evI_incI]

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem archCo_add (d : GlobalTheory.WeilM.Darboux B κ) (x y : W) :
    GlobalTheory.HeisOrbit.archCo d (x + y) = GlobalTheory.HeisOrbit.archCo d x + GlobalTheory.HeisOrbit.archCo d y := by
  simp only [GlobalTheory.HeisOrbit.archCo, map_add]
  ext i <;> simp [evI_add]

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem archCo_smul (d : GlobalTheory.WeilM.Darboux B κ) (c : ℝ) (x : W) :
    GlobalTheory.HeisOrbit.archCo d (realAd F c • x) = c • GlobalTheory.HeisOrbit.archCo d x := by
  simp only [GlobalTheory.HeisOrbit.archCo, map_smul]
  ext i <;> simp [evI_mul, evI_realAd, Algebra.smul_def]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lift_add (d : GlobalTheory.WeilM.Darboux B κ) (w w' : Vs κ) : lift d (w + w') = lift d w + lift d w' := by
  simp only [lift, ← map_add]
  congr 1
  ext i <;> simp [incI_add]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lift_smul (d : GlobalTheory.WeilM.Darboux B κ) (c : ℝ) (w : Vs κ) : lift d (c • w) = realAd F c • lift d w := by
  simp only [lift, ← map_smul]
  congr 1
  ext i <;> simp [incI_smul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem at_lift (d : GlobalTheory.WeilM.Darboux B κ) (w : Vs κ) : At (evI F) (lift d w) := by
  intro a ha
  have h1 := evI_eq_zero ha
  simp only [lift, ← map_smul]
  rw [LinearEquiv.map_eq_zero_iff]
  have key : ∀ y : mixedEmbedding.mixedSpace F, a * incI y = 0 := by
    intro y
    show ((a * incI y : AF F) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ⟨0, 0⟩
    refine Prod.ext ?_ ?_
    · show a.1 * _ = 0
      rw [h1, zero_mul]
    · show a.2 * 0 = 0
      rw [mul_zero]
  ext i <;> simp [smul_eq_mul, key]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

A detailed English derivation is pending.
-/
theorem lift_archCo (d : GlobalTheory.WeilM.Darboux B κ) {x : W} (hx : At (evI F) x) :
    lift d (GlobalTheory.HeisOrbit.archCo d x) = x := by
  have h0 : d.e ((finOne : AF F) • x) = 0 := by rw [hx _ evI_finOne, map_zero]
  rw [map_smul] at h0
  apply d.e.injective
  simp only [lift, GlobalTheory.HeisOrbit.archCo, LinearEquiv.apply_symm_apply]
  ext i
  · exact incI_evI (congrFun (congrArg Prod.fst h0) i)
  · exact incI_evI (congrFun (congrArg Prod.snd h0) i)

end General

end GlobalTheory.HeisOrbitSmooth

namespace GlobalTheory.HeisOrbitSmooth

open scoped ContDiff

section Orbit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

local notation "Vs" κ => (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_archCo (M : Model σ X W) : Continuous (GlobalTheory.HeisOrbit.archCo M.co) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous (M.co.e : Matrix (Fin n) (Fin d) (AE F E) → _) :=
    IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hmix : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  have hev : Continuous (evI F) := hmix.comp continuous_fst
  unfold GlobalTheory.HeisOrbit.archCo
  exact Continuous.prodMk (continuous_pi fun i => hev.comp ((continuous_apply i).comp (continuous_fst.comp he)))
    (continuous_pi fun i => hev.comp ((continuous_apply i).comp (continuous_snd.comp he)))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_mat_line (γ : Multiplicative ℝ →* UA σ W.J) (hγ : Continuous γ) :
    Continuous fun t : ℝ => mat (γ (Multiplicative.ofAdd t)) :=
  Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul (g h : UA σ W.J) : mat (g * h) = mat g * mat h := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one : mat (1 : UA σ W.J) = 1 := rfl

end Orbit

end GlobalTheory.HeisOrbitSmooth

namespace GlobalTheory.HeisOrbitSmooth

open scoped ContDiff

section Orbit2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

local notation "Vs" κ => (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem at_mul {x : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evI F) x) (A : Matrix (Fin d) (Fin d) (AE F E)) :
    At (evI F) (x * A) := by
  intro a ha
  rw [← Matrix.smul_mul, hx a ha, Matrix.zero_mul]

def opL (M : Model σ X W) (g : Matrix (Fin d) (Fin d) (AE F E)) : (Vs (Fin n × Fin d)) →ₗ[ℝ] Vs (Fin n × Fin d) where
  toFun w := GlobalTheory.HeisOrbit.archCo M.co (lift M.co w * gᵀ)
  map_add' w w' := by rw [lift_add, Matrix.add_mul, archCo_add]
  map_smul' c w := by rw [lift_smul, Matrix.smul_mul, archCo_smul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem opL_apply (M : Model σ X W) (g : Matrix (Fin d) (Fin d) (AE F E)) (w) :
    opL M g w = GlobalTheory.HeisOrbit.archCo M.co (lift M.co w * gᵀ) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem opL_archCo (M : Model σ X W) (g : Matrix (Fin d) (Fin d) (AE F E)) {x : Matrix (Fin n) (Fin d) (AE F E)}
    (hx : At (evI F) x) : opL M g (GlobalTheory.HeisOrbit.archCo M.co x) = GlobalTheory.HeisOrbit.archCo M.co (x * gᵀ) := by
  rw [opL_apply, lift_archCo M.co hx]

def opR (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ W.J) (t : ℝ) :
    (Vs (Fin n × Fin d)) →L[ℝ] Vs (Fin n × Fin d) :=
  LinearMap.toContinuousLinearMap (opL M (mat (γ (Multiplicative.ofAdd t))))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem opR_apply (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ W.J) (t : ℝ) (w) :
    opR M γ t w = opL M (mat (γ (Multiplicative.ofAdd t))) w := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem opR_zero (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ W.J) : opR M γ 0 = 1 := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [opR_apply, opL_apply, ofAdd_zero, map_one, mat_one, Matrix.transpose_one, Matrix.mul_one, archCo_lift]
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem opR_add (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ W.J) (s t : ℝ) :
    opR M γ (s + t) = opR M γ s * opR M γ t := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [ContinuousLinearMap.mul_apply, opR_apply, opR_apply, opR_apply, opL_apply M (mat (γ (Multiplicative.ofAdd t))) w, opL_archCo M _ (at_mul (at_lift M.co w) _),
    opL_apply, ofAdd_add, map_mul, mat_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_opR (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ W.J) (hγ : Continuous γ) :
    Continuous (opR M γ) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  refine continuous_clm_apply.2 fun w => ?_
  simp only [opR_apply, opL_apply]
  exact (continuous_archCo M).comp (continuous_const.matrix_mul (continuous_mat_line γ hγ).matrix_transpose)

end Orbit2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem archCo_orbit_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  intro F E _ _ _ _ _ σ n d X W M γ hγ u hu
  haveI : CompleteSpace ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    FiniteDimensional.complete ℝ _
  haveI : FiniteDimensional ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) :=
    ContinuousLinearMap.finiteDimensional
  have hcomp : CompleteSpace (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) :=
    FiniteDimensional.complete ℝ _
  have hs : ContDiff ℝ ∞ (opR M γ) :=
    @GlobalTheory.contDiff_of_continuous_oneParameter _ _ _ hcomp (opR M γ) (continuous_opR M γ hγ.1) (opR_zero M γ) (opR_add M γ)
  have hf : (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) =
      fun t => opR M γ t (GlobalTheory.HeisOrbit.archCo M.co u) := by
    funext t
    rw [opR_apply, opL_archCo M _ hu]
  rw [hf]
  refine ⟨hs.clm_apply contDiff_const, lift M.co (deriv (opR M γ) 0 (GlobalTheory.HeisOrbit.archCo M.co u)), at_lift _ _, ?_⟩
  rw [archCo_lift]
  have hd : HasDerivAt (opR M γ) (deriv (opR M γ) 0) 0 :=
    ((hs.differentiable (by simp)) 0).hasDerivAt
  simpa using hd.clm_apply (hasDerivAt_const (0 : ℝ) (GlobalTheory.HeisOrbit.archCo M.co u))

end GlobalTheory.HeisOrbitSmooth

end
