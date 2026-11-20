import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ReVec

variable {D : D7}

def reWEquiv (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : WO S T ≃+ WO S T where
  toFun := reW S T b
  invFun := reWi S T b
  left_inv := reWi_reW S T b
  right_inv := reW_reWi S T b
  map_add' := reW_add S T b

/- English proof (translation)
Use `haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1`. Conclude with `continuous_id.matrix_mul continuous_const`.
-/
theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

/- English proof (translation)
Use `haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1`. Conclude with `continuous_id.matrix_mul continuous_const`.
-/
theorem continuous_reWi (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reWi S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

/- English proof (translation)
Establish `key : ∀ (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) D.host.E), x ∈ ratL T S → HMul.hMul (α` using `Matrix (Fin T.rank) (Fin S.rank) (AE D)) (β := Matrix (Fin S.rank) (Fin S.rank) (AE D)) (γ := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x (N.map (incA D)) ∈ ratL T S := by`. Introduce and unpack `x N ⟨γ, rfl⟩`. Use `⟨γ * N, ?_⟩` and prove the remaining obligations. Use `show (γ * N).map (incA D) = _`. Conclude with `Matrix.map_mul (f := incA D)`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `key _ (frP S b) h`. Establish `: HMul.hMul (α` using `Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x := reWi_reW S T b x`. Rewrite `h2` using `[this]`. Then use the resulting hypothesis.

Conclude with `key x _`.
-/
theorem reW_mem_ratL_iff (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO S T) :
    reW S T b x ∈ ratL T S ↔ x ∈ ratL T S := by
  have key : ∀ (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) D.host.E),
      x ∈ ratL T S → HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (β := Matrix (Fin S.rank) (Fin S.rank) (AE D))
        (γ := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x (N.map (incA D)) ∈ ratL T S := by
    rintro x N ⟨γ, rfl⟩
    refine ⟨γ * N, ?_⟩
    show (γ * N).map (incA D) = _
    exact Matrix.map_mul (f := incA D)
  constructor
  · intro h
    have h2 := key _ (frP S b) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · exact key x _

/- English proof (translation)
Introduce and unpack `⟨⟨p0, hp0⟩, hall⟩`. Establish `he : Continuous (reWEquiv S T b)` using `continuous_reW S T b`. Establish `he' : Continuous (reWEquiv S T b).symm` using `continuous_reWi S T b`. Establish `hr : ∀ x, reWEquiv S T b x ∈ ratL T S ↔ x ∈ ratL T S` using `reW_mem_ratL_iff S T b`. Establish `hr' : ∀ x, (reWEquiv S T b).symm x ∈ ratL T S ↔ x ∈ ratL T S` using `fun x => by`.

Rewrite using `[← hr, AddEquiv.apply_symm_apply]`. Use `⟨⟨(p0.1.map (reWEquiv S T b).symm, (reWEquiv S T b).symm '' p0.2), (GlobalTheory.Unf.ParCont.isCovolOne_map hp0 (reWEquiv S T b).symm he' he hr').1⟩, ?_⟩` and prove the remaining obligations. Establish `aux : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → nrm2 μ 𝓕 (fun x => f (reWEquiv S T b x)) = 1`. Introduce `μ 𝓕 hp`. Take `⟨h1, hemb⟩` from `GlobalTheory.Unf.ParCont.isCovolOne_map hp (reWEquiv S T b) he he' hr`.

Establish `h2` using `hall (μ.map (reWEquiv S T b), reWEquiv S T b '' 𝓕) h1`. Simplify using `only [nrm2] at h2 ⊢`. Rewrite `h2` using `[hemb.setIntegral_map, Set.preimage_image_eq _ (reWEquiv S T b).injective]`. Conclude with `h2`. Introduce and unpack `⟨μ', 𝓕'⟩ hp`.

Conclude with `aux μ' 𝓕' hp`.
-/
theorem reframeFunctionOnHoms_norm_one_covolumeOne (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) :
    AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := by
  rintro ⟨⟨p0, hp0⟩, hall⟩
  have he : Continuous (reWEquiv S T b) := continuous_reW S T b
  have he' : Continuous (reWEquiv S T b).symm := continuous_reWi S T b
  have hr : ∀ x, reWEquiv S T b x ∈ ratL T S ↔ x ∈ ratL T S := reW_mem_ratL_iff S T b
  have hr' : ∀ x, (reWEquiv S T b).symm x ∈ ratL T S ↔ x ∈ ratL T S := fun x => by
    rw [← hr, AddEquiv.apply_symm_apply]
  refine ⟨⟨(p0.1.map (reWEquiv S T b).symm, (reWEquiv S T b).symm '' p0.2),
    (GlobalTheory.Unf.ParCont.isCovolOne_map hp0 (reWEquiv S T b).symm he' he hr').1⟩, ?_⟩
  have aux : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      nrm2 μ 𝓕 (fun x => f (reWEquiv S T b x)) = 1 := by
    intro μ 𝓕 hp
    obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hp (reWEquiv S T b) he he' hr
    have h2 := hall (μ.map (reWEquiv S T b), reWEquiv S T b '' 𝓕) h1
    simp only [nrm2] at h2 ⊢
    rw [hemb.setIntegral_map, Set.preimage_image_eq _ (reWEquiv S T b).injective] at h2
    exact h2
  rintro ⟨μ', 𝓕'⟩ hp
  exact aux μ' 𝓕' hp

end GlobalTheory.AdSpan.ReVec
