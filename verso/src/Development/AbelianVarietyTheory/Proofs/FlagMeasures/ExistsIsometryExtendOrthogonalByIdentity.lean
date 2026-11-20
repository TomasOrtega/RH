import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrthExt

/- English proof (translation)
Use `hv` as an intermediate fact. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this`. Conclude with `this u hu`.
-/
theorem hT_orth_right {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT u v = 0 := by
  have := hv
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this u hu

/- English proof (translation)
Establish `h1` using `S.herm.eq u v`. Rewrite `h1` using `[hT_orth_right S U hu hv]`. Simplify using `using h1.symm`.
-/
theorem hT_orth_left {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT v u = 0 := by
  have h1 := S.herm.eq u v
  rw [hT_orth_right S U hu hv] at h1
  simpa using h1.symm

/- English proof (translation)
Introduce `E _ _ _ S U hc g hg`. Set `e` to `Submodule.prodEquivOfIsCompl U (orth S U) hc`. Set `γ : S.V ≃ₗ[E] S.V` to `(e.symm.trans ((LinearEquiv.refl E U).prodCongr g)).trans e`. Establish `hγ : ∀ x, γ x = ((e.symm x).1 : S.V) + (g (e.symm x).2 : S.V)` using `fun x => rfl`. Establish `hx : ∀ x, x = ((e.symm x).1 : S.V) + ((e.symm x).2 : S.V)` using `fun x => by conv_lhs => rw [← e.apply_symm_apply x]`.

Both sides reduce to the same expression. Establish `key : ∀ (a b : U) (c d : ↥(orth S U)), S.hT ((a : S.V) + (c : S.V)) ((b : S.V) + (d : S.V)) = S.hT a b + S.hT c d`. Introduce `a b c d`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[GlobalTheory.OrthExt.hT_orth_right S U a.2 d.2, GlobalTheory.OrthExt.hT_orth_left S U b.2 c.2]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨γ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Express the relevant statement in the definitionally equal form `S.hT (γ x) (γ y) = S.hT x y`. Rewrite using `[hγ, hγ, key, hg, ← key, ← hx, ← hx]`.

Introduce `u hu`. Rewrite using `[hγ]`. Establish `: e.symm u = (⟨u, hu⟩, 0)` using `Submodule.prodEquivOfIsCompl_symm_apply_left U (orth S U) hc ⟨u, hu⟩`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Introduce `w`. Rewrite using `[hγ]`. Establish `: e.symm w = (0, w)` using `Submodule.prodEquivOfIsCompl_symm_apply_right U (orth S U) hc w`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem extend_isom : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), IsCompl U (orth S U) → ∀ g : ↥(orth S U) ≃ₗ[E] ↥(orth S U), (∀ x y : ↥(orth S U), S.hT (g x : S.V) (g y : S.V) = S.hT (x : S.V) (y : S.V)) → ∃ γ : S.V ≃ₗ[E] S.V, γ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ u ∈ U, γ u = u) ∧ ∀ w : ↥(orth S U), γ (w : S.V) = (g w : S.V) := by
  intro E _ _ _ S U hc g hg
  let e := Submodule.prodEquivOfIsCompl U (orth S U) hc
  let γ : S.V ≃ₗ[E] S.V := (e.symm.trans ((LinearEquiv.refl E U).prodCongr g)).trans e
  have hγ : ∀ x, γ x = ((e.symm x).1 : S.V) + (g (e.symm x).2 : S.V) := fun x => rfl
  have hx : ∀ x, x = ((e.symm x).1 : S.V) + ((e.symm x).2 : S.V) := fun x => by
    conv_lhs => rw [← e.apply_symm_apply x]
    rfl
  have key : ∀ (a b : U) (c d : ↥(orth S U)),
      S.hT ((a : S.V) + (c : S.V)) ((b : S.V) + (d : S.V)) = S.hT a b + S.hT c d := by
    intro a b c d
    simp only [map_add, LinearMap.add_apply]
    rw [GlobalTheory.OrthExt.hT_orth_right S U a.2 d.2, GlobalTheory.OrthExt.hT_orth_left S U b.2 c.2]
    ring
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro x y
    change S.hT (γ x) (γ y) = S.hT x y
    rw [hγ, hγ, key, hg, ← key, ← hx, ← hx]
  · intro u hu
    rw [hγ]
    have : e.symm u = (⟨u, hu⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left U (orth S U) hc ⟨u, hu⟩
    rw [this]; simp
  · intro w
    rw [hγ]
    have : e.symm w = (0, w) := Submodule.prodEquivOfIsCompl_symm_apply_right U (orth S U) hc w
    rw [this]; simp

end GlobalTheory.OrthExt
