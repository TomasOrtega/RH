import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FinEmbLat

open Matrix
open scoped nonZeroDivisors TensorProduct

variable {D : D7}

/- English proof (translation)
Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, hx, rfl⟩` from `hz`. Establish `e : N.map (eToEAf D) *ᵥ (fun i => Formalism.UG.inclE (F` using `D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) = fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((N *ᵥ x) i) := by`.

Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (eToEAf D) N x i).symm`. Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨_, hN x hx, rfl⟩`. Consider the case `zero => rw [mulVec_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [mulVec_add]`. Conclude with `add_mem ha hb`. Consider the case `smul r a _ ha => rw [Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ r ha`.
-/
theorem mulVec_mem_hatL_of_mapsTo {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E))
    (hN : ∀ x ∈ Λ, N *ᵥ x ∈ Λ') :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, N.map (eToEAf D) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have e : N.map (eToEAf D) *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) =
        fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((N *ᵥ x) i) := by
      funext i
      exact (RingHom.map_mulVec (eToEAf D) N x i).symm
    rw [e]
    exact Submodule.subset_span ⟨_, hN x hx, rfl⟩
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r ha

variable {A B : HSp D} {c : ℕ} {ε : D.host.E}

/- English proof (translation)
Establish `hP : ∀ z ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) Λ, (frameMat B A d.ι).map (eToEAf D) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) := mulVec_mem_hatL_of_mapsTo _ Λ _ fun x hx => ⟨x, hx, 0, fun _ => (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).zero_mem, by rw [mulVec_zero, add_zero]⟩`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨x, ⟨y0, hy0, u, hu, rfl⟩, rfl⟩` from `hv`.

Establish `e : (fun i => Formalism.UG.inclE (F` using `D.host.F) (Formalism.L2.Herm.Af D.host.F) (((frameMat B A d.ι) *ᵥ y0 + d.a *ᵥ u) i)) = (frameMat B A d.ι).map (eToEAf D) *ᵥ (fun i => eToEAf D (y0 i)) + d.a.map (eToEAf D) *ᵥ (fun p => eToEAf D (u p)) := by`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, Pi.add_apply, map_add]`. Conclude with `congrArg₂ (· + ·) (RingHom.map_mulVec (eToEAf D) _ y0 i) (RingHom.map_mulVec (eToEAf D) d.a u i)`. Use `show M *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (((frameMat B A d.ι) *ᵥ y0 + d.a *ᵥ u) i)) ∈ _`.

Rewrite using `[e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, ← mulVec_mulVec]`. Use `add_mem (hP _ (hK _ (Submodule.subset_span ⟨y0, hy0, rfl⟩))) ?_` and prove the remaining obligations. Establish `e2 : d.a.map (eToEAf D) *ᵥ (fun p => eToEAf D (u p)) = fun i => Formalism.UG.inclE (F` using `D.host.F) (Formalism.L2.Herm.Af D.host.F) ((d.a *ᵥ u) i) := by`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (eToEAf D) d.a u i).symm`.

Rewrite using `[e2]`. Conclude with `Submodule.subset_span ⟨_, ⟨0, zero_mem _, u, hu, by rw [mulVec_zero, zero_add]⟩, rfl⟩`. Consider the case `zero => rw [mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [mulVec_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul r a _ ha => rw [Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ r ha`.
-/
theorem mapsTo_hatL_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (M : Matrix (Fin B.rank) (Fin B.rank) (Lev.EAf D)) (K : Matrix (Fin A.rank) (Fin A.rank) (Lev.EAf D))
    (h1 : M * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * K)
    (h2 : M * d.a.map (eToEAf D) = d.a.map (eToEAf D))
    (hK : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, K *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1),
      M *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) := by
  have hP : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      (frameMat B A d.ι).map (eToEAf D) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) :=
    mulVec_mem_hatL_of_mapsTo _ Λ _ fun x hx =>
      ⟨x, hx, 0, fun _ => (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E).zero_mem, by rw [mulVec_zero, add_zero]⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, ⟨y0, hy0, u, hu, rfl⟩, rfl⟩ := hv
    have e : (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)
        (((frameMat B A d.ι) *ᵥ y0 + d.a *ᵥ u) i)) =
        (frameMat B A d.ι).map (eToEAf D) *ᵥ (fun i => eToEAf D (y0 i)) + d.a.map (eToEAf D) *ᵥ (fun p => eToEAf D (u p)) := by
      funext i
      rw [Pi.add_apply, Pi.add_apply, map_add]
      exact congrArg₂ (· + ·) (RingHom.map_mulVec (eToEAf D) _ y0 i) (RingHom.map_mulVec (eToEAf D) d.a u i)
    show M *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)
        (((frameMat B A d.ι) *ᵥ y0 + d.a *ᵥ u) i)) ∈ _
    rw [e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, ← mulVec_mulVec]
    refine add_mem (hP _ (hK _ (Submodule.subset_span ⟨y0, hy0, rfl⟩))) ?_
    have e2 : d.a.map (eToEAf D) *ᵥ (fun p => eToEAf D (u p)) =
        fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((d.a *ᵥ u) i) := by
      funext i
      exact (RingHom.map_mulVec (eToEAf D) d.a u i).symm
    rw [e2]
    exact Submodule.subset_span ⟨_, ⟨0, zero_mem _, u, hu, by rw [mulVec_zero, zero_add]⟩, rfl⟩
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r ha

end GlobalTheory.FinEmbLat

namespace GlobalTheory.FinEmbLat

open Matrix

/- English proof (translation)
Introduce `D A B c ε d Λ y hy`. Establish `hrel` using `finEmb_rel d y`. Use `set G' := Lev.finE B (finEmb d y).1 with hG'`. Use `set Y := Lev.finE A y.1 with hY`. Establish `h1 : G'.1 * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * Y.1`.

Use `congrArg (fun X => X.map (toEAf D)) hrel.1` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`. Conclude with `this`. Establish `h2 : G'.1 * d.a.map (eToEAf D) = d.a.map (eToEAf D)`. Use extensionality with `i p`.

Establish `hx` using `hrel.2 (fun k => d.a k p) (by`. Use function extensionality and compare the values at `k`. Conclude with `congrFun (congrFun d.perp k) p)`. Use `congrArg (toEAf D) (congrFun hx i)` as an intermediate fact. Rewrite `this` using `[RingHom.map_mulVec]`.

Conclude with `this`. Establish `hK : ∀ z ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) Λ, Y.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := fun z hz => (hy z).1 hz`. Establish `hKi : ∀ z ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) Λ, (Y⁻¹).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := fun z hz => ((Subgroup.inv_mem _ hy) z).1 hz`. Establish `h1i : (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * (Y⁻¹).1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Units.mul_inv, Matrix.mul_one]`. Use `_ = (G'⁻¹).1 * ((frameMat B A d.ι).map (eToEAf D) * Y.1) * (Y⁻¹).1 := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (G'⁻¹).1 * (G'.1 * (frameMat B A d.ι).map (eToEAf D)) * (Y⁻¹).1 := by rw [h1]`. Use `_ = (frameMat B A d.ι).map (eToEAf D) * (Y⁻¹).1 := by`.

Rewrite using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Establish `h2i : (G'⁻¹).1 * d.a.map (eToEAf D) = d.a.map (eToEAf D)` using `by conv_lhs => rw [← h2]`. Rewrite using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Introduce `v`. Prove the components needed by the constructor for the conclusion.

Conclude with `mapsTo_hatL_lat d Λ G'.1 Y.1 h1 h2 hK v`. Introduce `hv`. Use `mapsTo_hatL_lat d Λ (G'⁻¹).1 (Y⁻¹).1 h1i h2i hKi _ hv` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem finEmb_mem_stabGL : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (y : GfC A), Lev.finE A y.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) Λ) → Lev.finE B (finEmb d y).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) := by
  intro D A B c ε d Λ y hy
  have hrel := finEmb_rel d y
  set G' := Lev.finE B (finEmb d y).1 with hG'
  set Y := Lev.finE A y.1 with hY
  have h1 : G'.1 * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * Y.1 := by
    have := congrArg (fun X => X.map (toEAf D)) hrel.1
    simp only [Matrix.map_mul] at this
    exact this
  have h2 : G'.1 * d.a.map (eToEAf D) = d.a.map (eToEAf D) := by
    ext i p
    have hx := hrel.2 (fun k => d.a k p) (by
      funext k
      exact congrFun (congrFun d.perp k) p)
    have := congrArg (toEAf D) (congrFun hx i)
    rw [RingHom.map_mulVec] at this
    exact this
  have hK : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, Y.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    fun z hz => (hy z).1 hz
  have hKi : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Y⁻¹).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    fun z hz => ((Subgroup.inv_mem _ hy) z).1 hz
  have h1i : (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D) = (frameMat B A d.ι).map (eToEAf D) * (Y⁻¹).1 := by
    calc (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D)
        = (G'⁻¹).1 * (frameMat B A d.ι).map (eToEAf D) * (Y.1 * (Y⁻¹).1) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = (G'⁻¹).1 * ((frameMat B A d.ι).map (eToEAf D) * Y.1) * (Y⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = (G'⁻¹).1 * (G'.1 * (frameMat B A d.ι).map (eToEAf D)) * (Y⁻¹).1 := by rw [h1]
      _ = (frameMat B A d.ι).map (eToEAf D) * (Y⁻¹).1 := by
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have h2i : (G'⁻¹).1 * d.a.map (eToEAf D) = d.a.map (eToEAf D) := by
    conv_lhs => rw [← h2]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  intro v
  constructor
  · exact mapsTo_hatL_lat d Λ G'.1 Y.1 h1 h2 hK v
  · intro hv
    have := mapsTo_hatL_lat d Λ (G'⁻¹).1 (Y⁻¹).1 h1i h2i hKi _ hv
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end GlobalTheory.FinEmbLat
