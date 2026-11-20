import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

noncomputable section
namespace GlobalTheory.StdFrameCounterexample
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def latC (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.map ((V.frame.equivFun.toLinearMap).restrictScalars (𝓞 D.host.E))

/- English proof (translation)
Use `show _ ↔ ∑ i, x i • V.frame i ∈ V.L0`. Rewrite using `[← V.frame.equivFun_symm_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`.

Introduce `h`. Conclude with `⟨_, h, V.frame.equivFun.apply_symm_apply x⟩`.
-/
theorem mem_latC (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ latC V ↔ x ∈ L0c D V := by
  show _ ↔ ∑ i, x i • V.frame i ∈ V.L0
  rw [← V.frame.equivFun_symm_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, V.frame.equivFun.apply_symm_apply x⟩

/- English proof (translation)
The claim follows from `Set.ext (mem_latC V)`.
-/
theorem latC_coe (V : HSp D) : (latC V : Set _) = L0c D V := Set.ext (mem_latC V)

/- English proof (translation)
Establish `hfg : (latC V).FG` using `Submodule.FG.map _ V.standardTuple_isLattice.fg`. Establish `hsp : Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤`. Establish `h` using `V.standardTuple_isLattice.span_eq_top`. Establish `: (latC V : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)` using `rfl`. Rewrite using `[this, ← Submodule.map_span, h, Submodule.map_top]`.

Conclude with `LinearMap.range_eq_top.2 V.frame.equivFun.surjective`. Establish `hc` using `(GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (latC V) hfg hsp).1`. Unfold `Bridge.hLat`. Rewrite using `[← Submodule.span_eq (latC V)]`. Use `congr 1`.

Use extensionality with `x`. Rewrite using `[SetLike.mem_coe, ← hc x, latC_coe]`. Establish `h1 : Units.val (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)) = 1`. Rewrite using `[Subgroup.coe_inv, Subgroup.coe_one, inv_one, Units.val_one]`. Use `show Matrix.mulVec (Units.val (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E))) _ ∈ latHat D.host.F D.host.E (L0c D V) ↔ _`.

Rewrite using `[h1, Matrix.one_mulVec]`. Both sides reduce to the same expression.
-/
theorem hLat_one (V : HSp D) : Bridge.hLat V 1 = latC V := by
  have hfg : (latC V).FG := Submodule.FG.map _ V.standardTuple_isLattice.fg
  have hsp : Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have h := V.standardTuple_isLattice.span_eq_top
    have : (latC V : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, ← Submodule.map_span, h, Submodule.map_top]
    exact LinearMap.range_eq_top.2 V.frame.equivFun.surjective
  have hc := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (latC V) hfg hsp).1
  unfold Bridge.hLat
  rw [← Submodule.span_eq (latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← hc x, latC_coe]
  have h1 : Units.val (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)) = 1 := by
    rw [Subgroup.coe_inv, Subgroup.coe_one, inv_one, Units.val_one]
  show Matrix.mulVec (Units.val (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E))) _ ∈
    latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [h1, Matrix.one_mulVec]
  rfl

/- English proof (translation)
Unfold `VStd`. Rewrite using `[hLat_one]`. Use `and_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.ext_iff]`. Use `forall_congr' fun x => ?_` and prove the remaining obligations.

Rewrite using `[mem_latC]`. Use `iff_congr Iff.rfl ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_pi]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_univ, true_imp_iff, Submodule.mem_one]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Rewrite using `[← hy]`. Conclude with `y.2`. Introduce `h`.

Conclude with `⟨⟨x a, h⟩, rfl⟩`.
-/
theorem vstd_iff (i : Fin D.R.m) : VStd D i ↔ (Vc D i).gram = 1 ∧
    ∀ x : Fin (Vc D i).rank → D.host.E, ∑ a, x a • (Vc D i).frame a ∈ (Vc D i).L0 ↔ ∀ a, IsIntegral ℤ (x a) := by
  unfold VStd
  rw [hLat_one]
  refine and_congr_right fun _ => ?_
  rw [Submodule.ext_iff]
  refine forall_congr' fun x => ?_
  rw [mem_latC]
  refine iff_congr Iff.rfl ?_
  rw [Submodule.mem_pi]
  refine forall_congr' fun a => ?_
  simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]; exact y.2
  · intro h
    exact ⟨⟨x a, h⟩, rfl⟩

def withV (D : D7) (S : HSp D) (b : Bool) (hs : S.SigOK) (hr : S.rank = D.R.nV)
    (ho : Formalism.HermitianLatticesTheory.IsOrthoLattice (if b then -S.hT else S.hT) S.L0 D.R.nV) : D7 :=
  { D with sp := { D.sp with
      V := fun _ => S, V_sig := fun _ => hs, V_rank := fun _ _ _ => hr, Vneg := fun _ => b, V_std := fun _ _ _ => ho } }

/- English proof (translation)
Use `⟨Pi.basisFun E (Fin N), (Pi.basisFun E (Fin N)).linearIndependent, (Pi.basisFun E (Fin N)).span_eq, rfl, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.basisFun_apply, Pi.basisFun_apply]`. Consider the cases of `b`. Simplify using `only [Bool.false_eq_true, if_false]`. Rewrite using `[diagForm_single]`.

Simplify using `[sgn]`. Simplify using `only [if_true, LinearMap.neg_apply]`. Rewrite using `[diagForm_single]`. Apply the tactic sequence `split_ifs <;> simp [sgn]`.
-/
theorem orthoSign {E : Type} [Field E] [NumberField E] [StarRing E] (N : ℕ) (b : Bool) : Formalism.HermitianLatticesTheory.IsOrthoLattice
    (if b then -(diagForm (E := E) N (fun _ => b)) else diagForm (E := E) N (fun _ => b)) (Examples₂.stdLat N) N := by
  refine ⟨Pi.basisFun E (Fin N), (Pi.basisFun E (Fin N)).linearIndependent,
    (Pi.basisFun E (Fin N)).span_eq, rfl, fun i j => ?_⟩
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [diagForm_single]
    simp [sgn]
  · simp only [if_true, LinearMap.neg_apply]
    rw [diagForm_single]
    split_ifs <;> simp [sgn]

def scaled {E : Type} [Field E] [NumberField E] [StarRing E] (N : ℕ) (u : Eˣ) : HSpace E :=
  { posSpace (star_isIntegral (E := E)) N with frame := (Pi.basisFun E (Fin N)).unitsSMul fun _ => u }

/- English proof (translation)
Use `Matrix.ext fun (i j : Fin N) => ?_` and prove the remaining obligations. Use `show diagForm N (fun _ => false) (((Pi.basisFun E (Fin N)).unitsSMul fun _ => u) i) (((Pi.basisFun E (Fin N)).unitsSMul fun _ => u) j) = (1 : Matrix (Fin N) (Fin N) E) i j`. Rewrite using `[Module.Basis.unitsSMul_apply, Module.Basis.unitsSMul_apply, Units.smul_def, Units.smul_def, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Pi.basisFun_apply, Pi.basisFun_apply, diagForm_single, Matrix.one_apply]`. Use `split_ifs`. Simplify using `only [sgn, starRingEnd_apply, smul_eq_mul]`.

Simplify `hu` using `[mul_comm]`. Simplify using the standard rewrite rules.
-/
theorem scaled_gram {E : Type} [Field E] [NumberField E] [StarRing E] (N : ℕ) (u : Eˣ) (hu : star (u : E) * u = 1) :
    (scaled N u).gram = 1 := by
  refine Matrix.ext fun (i j : Fin N) => ?_
  show diagForm N (fun _ => false) (((Pi.basisFun E (Fin N)).unitsSMul fun _ => u) i)
    (((Pi.basisFun E (Fin N)).unitsSMul fun _ => u) j) = (1 : Matrix (Fin N) (Fin N) E) i j
  rw [Module.Basis.unitsSMul_apply, Module.Basis.unitsSMul_apply, Units.smul_def, Units.smul_def, map_smul,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, Pi.basisFun_apply, Pi.basisFun_apply, diagForm_single, Matrix.one_apply]
  split_ifs
  · simp only [sgn, starRingEnd_apply, smul_eq_mul]
    simpa [mul_comm] using hu
  · simp

/- English proof (translation)
Introduce `τ`. Rewrite using `[scaled_gram N u hu, Matrix.map_one _ (map_zero τ) (map_one τ)]`. Establish `h` using `Formalism.UG.P.stdform_sig_one (n := Fin N)`. Rewrite `h` using `[Fintype.card_fin]`. Conclude with `h`.
-/
theorem scaled_sig {E : Type} [Field E] [NumberField E] [StarRing E] (N : ℕ) (u : Eˣ) (hu : star (u : E) * u = 1) :
    (scaled N u).SigOK := by
  intro τ
  rw [scaled_gram N u hu, Matrix.map_one _ (map_zero τ) (map_one τ)]
  have h := Formalism.UG.P.stdform_sig_one (n := Fin N)
  rw [Fintype.card_fin] at h
  exact h

def withScaled (D : D7) (u : D.host.Eˣ) (hu : star (u : D.host.E) * u = 1) : D7 :=
  withV D (scaled D.R.nV u) false (scaled_sig _ u hu) rfl (orthoSign _ false)

end GlobalTheory.StdFrameCounterexample
