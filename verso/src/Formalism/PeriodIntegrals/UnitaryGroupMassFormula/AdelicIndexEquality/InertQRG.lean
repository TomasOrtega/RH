import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ChiEqOneOfClosure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertGen

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sig_apply (I : AutInst) (e : I.E) : I.cm.sig e = star e := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.map (AlgHom.id I.F _) I.cm.sig) (x ⊗ₜ e) = _`. Conclude with `Algebra.TensorProduct.map_tmul _ _ _ _`.
-/
theorem sigV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)
    (e : I.E) : sigV I v (x ⊗ₜ e) = x ⊗ₜ star e := by
  change (Algebra.TensorProduct.map (AlgHom.id I.F _) I.cm.sig) (x ⊗ₜ e) = _
  exact Algebra.TensorProduct.map_tmul _ _ _ _

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul x e => rw [sigV_tmul, sigV_tmul, star_star]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigV_invol (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : sigV I v (sigV I v a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x e => rw [sigV_tmul, sigV_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Conclude with `sigV_tmul I v 1 e`.
-/
theorem sigV_inclV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    sigV I v (inclV I v e) = inclV I v (star e) := by
  exact sigV_tmul I v 1 e

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Establish `h : starRingEnd I.E (I.J j i) = I.J i j` using `congrFun (congrFun I.J_herm i) j`. Use `show sigV I v (inclV I v (I.J j i)) = inclV I v (I.J i j)`. Rewrite using `[sigV_inclV]`. Conclude with `congrArg (inclV I v) h`.
-/
theorem herm_V (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by
  funext i j
  have h : starRingEnd I.E (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  show sigV I v (inclV I v (I.J j i)) = inclV I v (I.J i j)
  rw [sigV_inclV]
  exact congrArg (inclV I v) h

/- English proof (translation)
Introduce `I v hv g`. Set `_ : Field (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)` to `hv.toField`. Establish `hinj : Function.Injective (inclV I v)` using `(inclV I v).injective`. Establish `hdet : (I.J.map (inclV I v)).det ≠ 0`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Introduce `h`. Conclude with `I.J_det (hinj (by rw [h, map_zero]))`. Establish `h2 : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ≠ 0`. Introduce `h`. Establish `: inclV I v 2 = inclV I v 0` using `by rw [map_ofNat, map_zero]; exact h`.

Conclude with `two_ne_zero (hinj this)`. Conclude with `QRG.mem_S (sigV I v) (I.J.map (inclV I v)) (sigV_invol I v) (herm_V I v) hdet h2 g`.
-/
theorem q_reflection_generation : QReflGen := by
  intro I v hv g
  let _ : Field (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := hv.toField
  have hinj : Function.Injective (inclV I v) := (inclV I v).injective
  have hdet : (I.J.map (inclV I v)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h
    exact I.J_det (hinj (by rw [h, map_zero]))
  have h2 : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ≠ 0 := by
    intro h
    have : inclV I v 2 = inclV I v 0 := by rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero (hinj this)
  exact QRG.mem_S (sigV I v) (I.J.map (inclV I v)) (sigV_invol I v) (herm_V I v) hdet h2 g

/- English proof (translation)
Introduce `I v hv χ _ _ hK g`. Establish `hq : {s : Uv I v | IsQRefl I v s} ⊆ (χ.ker : Set (Uv I v))`. Introduce `s hs`. Take `⟨m, hm, hmK⟩` from `hP I v hv s hs`. Conclude with `MonoidHom.mem_ker.mpr (hK s ⟨m, hm, hmK⟩)`.

Conclude with `MonoidHom.mem_ker.mp ((Subgroup.closure_le _).mpr hq (q_reflection_generation I v hv g))`.
-/
theorem locInertChi_of_qReflPow (hP : QReflPow) : LocInertChi := by
  intro I v hv χ _ _ hK g
  have hq : {s : Uv I v | IsQRefl I v s} ⊆ (χ.ker : Set (Uv I v)) := by
    intro s hs
    obtain ⟨m, hm, hmK⟩ := hP I v hv s hs
    exact MonoidHom.mem_ker.mpr (hK s ⟨m, hm, hmK⟩)
  exact MonoidHom.mem_ker.mp ((Subgroup.closure_le _).mpr hq (q_reflection_generation I v hv g))

end PI.UnitaryGroupMassFormula.AdIndexEq

end
