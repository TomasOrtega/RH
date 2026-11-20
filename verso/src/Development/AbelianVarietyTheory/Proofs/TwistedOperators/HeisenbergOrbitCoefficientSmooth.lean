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
Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) = x`. Simplify using the standard rewrite rules.
-/
theorem evI_incI (x : mixedEmbedding.mixedSpace F) : evI F (incI x) = x := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) = x
  simp

/- English proof (translation)
The claim follows from `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
The claim follows from `map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
Use `show (⟨_, 0⟩ : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ⟨_, 0 + 0⟩`. Rewrite using `[map_add, add_zero]`. Both sides reduce to the same expression.
-/
theorem incI_add (x y : mixedEmbedding.mixedSpace F) : incI (x + y) = incI x + incI y := by
  show (⟨_, 0⟩ : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ⟨_, 0 + 0⟩
  rw [map_add, add_zero]
  rfl

/- English proof (translation)
Use `show (⟨_, 0⟩ : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ⟨_ * _, 0 * 0⟩`. Rewrite using `[Algebra.smul_def, map_mul, mul_zero]`. Both sides reduce to the same expression.
-/
theorem incI_smul (c : ℝ) (x : mixedEmbedding.mixedSpace F) : incI (c • x) = realAd F c * incI x := by
  show (⟨_, 0⟩ : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ⟨_ * _, 0 * 0⟩
  rw [Algebra.smul_def, map_mul, mul_zero]
  rfl

/- English proof (translation)
The claim follows from `evI_incI _`.
-/
theorem evI_realAd (c : ℝ) : evI F (realAd F c) = algebraMap ℝ _ c := evI_incI _

/- English proof (translation)
The claim follows from `(map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 h`.
-/
theorem evI_eq_zero {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 h

def finOne : AF F := ⟨0, 1⟩

/- English proof (translation)
The claim follows from `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.
-/
theorem evI_finOne : evI F (finOne : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

/- English proof (translation)
Establish `h2 : a.2 = 0`. Use `congrArg Prod.snd h` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Use `show (⟨_, 0⟩ : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (a : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)`. Use `Prod.ext ?_ h2.symm` and prove the remaining obligations.

Conclude with `RingEquiv.symm_apply_apply _ _`.
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
Simplify using `[GlobalTheory.HeisOrbit.archCo, lift, evI_incI]`.
-/
theorem archCo_lift (d : GlobalTheory.WeilM.Darboux B κ) (w : Vs κ) : GlobalTheory.HeisOrbit.archCo d (lift d w) = w := by
  simp [GlobalTheory.HeisOrbit.archCo, lift, evI_incI]

/- English proof (translation)
Simplify using `only [GlobalTheory.HeisOrbit.archCo, map_add]`. Apply the tactic sequence `ext i <;> simp [evI_add]`.
-/
theorem archCo_add (d : GlobalTheory.WeilM.Darboux B κ) (x y : W) :
    GlobalTheory.HeisOrbit.archCo d (x + y) = GlobalTheory.HeisOrbit.archCo d x + GlobalTheory.HeisOrbit.archCo d y := by
  simp only [GlobalTheory.HeisOrbit.archCo, map_add]
  ext i <;> simp [evI_add]

/- English proof (translation)
Simplify using `only [GlobalTheory.HeisOrbit.archCo, map_smul]`. Apply the tactic sequence `ext i <;> simp [evI_mul, evI_realAd, Algebra.smul_def]`.
-/
theorem archCo_smul (d : GlobalTheory.WeilM.Darboux B κ) (c : ℝ) (x : W) :
    GlobalTheory.HeisOrbit.archCo d (realAd F c • x) = c • GlobalTheory.HeisOrbit.archCo d x := by
  simp only [GlobalTheory.HeisOrbit.archCo, map_smul]
  ext i <;> simp [evI_mul, evI_realAd, Algebra.smul_def]

/- English proof (translation)
Simplify using `only [lift, ← map_add]`. Use `congr 1`. Apply the tactic sequence `ext i <;> simp [incI_add]`.
-/
theorem lift_add (d : GlobalTheory.WeilM.Darboux B κ) (w w' : Vs κ) : lift d (w + w') = lift d w + lift d w' := by
  simp only [lift, ← map_add]
  congr 1
  ext i <;> simp [incI_add]

/- English proof (translation)
Simplify using `only [lift, ← map_smul]`. Use `congr 1`. Apply the tactic sequence `ext i <;> simp [incI_smul]`.
-/
theorem lift_smul (d : GlobalTheory.WeilM.Darboux B κ) (c : ℝ) (w : Vs κ) : lift d (c • w) = realAd F c • lift d w := by
  simp only [lift, ← map_smul]
  congr 1
  ext i <;> simp [incI_smul]

/- English proof (translation)
Introduce `a ha`. Establish `h1` using `evI_eq_zero ha`. Simplify using `only [lift, ← map_smul]`. Rewrite using `[LinearEquiv.map_eq_zero_iff]`. Establish `key : ∀ y : mixedEmbedding.mixedSpace F, a * incI y = 0`.

Introduce `y`. Use `show ((a * incI y : AF F) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ⟨0, 0⟩`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show a.1 * _ = 0`. Rewrite using `[h1, zero_mul]`.

Use `show a.2 * 0 = 0`. Rewrite using `[mul_zero]`. Apply the tactic sequence `ext i <;> simp [smul_eq_mul, key]`.
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
Establish `h0 : d.e ((finOne : AF F) • x) = 0` using `by rw [hx _ evI_finOne, map_zero]`. Rewrite `h0` using `[map_smul]`. Apply `d.e.injective` to reduce the goal to its premises. Simplify using `only [lift, GlobalTheory.HeisOrbit.archCo, LinearEquiv.apply_symm_apply]`. Use extensionality with `i`.

Conclude with `incI_evI (congrFun (congrArg Prod.fst h0) i)`. Conclude with `incI_evI (congrFun (congrArg Prod.snd h0) i)`.
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
Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)`. Use `haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))`. Establish `he : Continuous (M.co.e : Matrix (Fin n) (Fin d) (AE F E) → _)` using `IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap`. Establish `hmix : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Express the relevant statement in the definitionally equal form `Continuous fun x : InfiniteAdeleRing F => ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)), (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))`.

Use `Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)`. Establish `hev : Continuous (evI F)` using `hmix.comp continuous_fst`. Unfold `GlobalTheory.HeisOrbit.archCo`.

Conclude with `Continuous.prodMk (continuous_pi fun i => hev.comp ((continuous_apply i).comp (continuous_fst.comp he))) (continuous_pi fun i => hev.comp ((continuous_apply i).comp (continuous_snd.comp he)))`.
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
The claim follows from `Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))`.
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
Introduce `a ha`. Rewrite using `[← Matrix.smul_mul, hx a ha, Matrix.zero_mul]`.
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
Rewrite using `[opL_apply, lift_archCo M.co hx]`.
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
Use `ContinuousLinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[opR_apply, opL_apply, ofAdd_zero, map_one, mat_one, Matrix.transpose_one, Matrix.mul_one, archCo_lift]`. Both sides reduce to the same expression.
-/
theorem opR_zero (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ W.J) : opR M γ 0 = 1 := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [opR_apply, opL_apply, ofAdd_zero, map_one, mat_one, Matrix.transpose_one, Matrix.mul_one, archCo_lift]
  rfl

/- English proof (translation)
Use `ContinuousLinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.mul_apply, opR_apply, opR_apply, opR_apply, opL_apply M (mat (γ (Multiplicative.ofAdd t))) w, opL_archCo M _ (at_mul (at_lift M.co w) _), opL_apply, ofAdd_add, map_mul, mat_mul, Matrix.transpose_mul, Matrix.mul_assoc]`.
-/
theorem opR_add (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ W.J) (s t : ℝ) :
    opR M γ (s + t) = opR M γ s * opR M γ t := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [ContinuousLinearMap.mul_apply, opR_apply, opR_apply, opR_apply, opL_apply M (mat (γ (Multiplicative.ofAdd t))) w, opL_archCo M _ (at_mul (at_lift M.co w) _),
    opL_apply, ofAdd_add, map_mul, mat_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/- English proof (translation)
Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)`. Use `continuous_clm_apply.2 fun w => ?_` and prove the remaining obligations. Simplify using `only [opR_apply, opL_apply]`. Conclude with `(continuous_archCo M).comp (continuous_const.matrix_mul (continuous_mat_line γ hγ).matrix_transpose)`.
-/
theorem continuous_opR (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ W.J) (hγ : Continuous γ) :
    Continuous (opR M γ) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  refine continuous_clm_apply.2 fun w => ?_
  simp only [opR_apply, opL_apply]
  exact (continuous_archCo M).comp (continuous_const.matrix_mul (continuous_mat_line γ hγ).matrix_transpose)

end Orbit2

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M γ hγ u hu`. Use `haveI : CompleteSpace ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := FiniteDimensional.complete ℝ _`. Use `haveI : FiniteDimensional ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) := ContinuousLinearMap.finiteDimensional`. Establish `hcomp : CompleteSpace (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)))` using `FiniteDimensional.complete ℝ _`. Establish `hs : ContDiff ℝ ∞ (opR M γ)` using `@GlobalTheory.contDiff_of_continuous_oneParameter _ _ _ hcomp (opR M γ) (continuous_opR M γ hγ.1) (opR_zero M γ) (opR_add M γ)`.

Establish `hf : (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) = fun t => opR M γ t (GlobalTheory.HeisOrbit.archCo M.co u)`. Use function extensionality and compare the values at `t`. Rewrite using `[opR_apply, opL_archCo M _ hu]`. Rewrite using `[hf]`. Use `⟨hs.clm_apply contDiff_const, lift M.co (deriv (opR M γ) 0 (GlobalTheory.HeisOrbit.archCo M.co u)), at_lift _ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[archCo_lift]`. Establish `hd : HasDerivAt (opR M γ) (deriv (opR M γ) 0) 0` using `((hs.differentiable (by simp)) 0).hasDerivAt`. Simplify using `using hd.clm_apply (hasDerivAt_const (0 : ℝ) (GlobalTheory.HeisOrbit.archCo M.co u))`.
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
