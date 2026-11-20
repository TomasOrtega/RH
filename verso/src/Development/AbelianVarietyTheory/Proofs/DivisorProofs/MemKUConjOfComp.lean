import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSrcMemOrb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def thAt (u : Pl E) : GLw n (cPl E u) →* GLw n u :=
  (MulAut.conj (PhiU n (u.adicCompletion E))).toMonoidHom.comp
    ((invT n (u.adicCompletion E)).comp (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)))

/- English proof (translation)
The claim follows from `GlobalTheory.ThetaPull.phi_mul_apply _ i j`.
-/
theorem thAt_apply (u : Pl E) (h : GLw n (cPl E u)) (i j : Fin n) :
    (thAt u h).val i j =
      (-1) ^ ((i : ℕ) + j) * conjLoc (IsCMField.complexConj E).toRingEquiv u ((h⁻¹).val j.rev i.rev) :=
  GlobalTheory.ThetaPull.phi_mul_apply _ i j

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Establish `h` using `GlobalTheory.ThetaPull.thetaGL_apply (a := n) (conjFin (IsCMField.complexConj E).toRingEquiv) g i j`. Express the relevant statement in the definitionally equal form `pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j) = _`. Rewrite using `[h, thAt_apply, map_mul, map_pow, map_neg, map_one, pLoc_conjFin]`. Both sides reduce to the same expression.
-/
theorem map_thF (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n g) = thAt u (GeneralLinearGroup.map (pLoc E (cPl E u)) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (conjFin (IsCMField.complexConj E).toRingEquiv) g i j
  change pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j) = _
  rw [h, thAt_apply, map_mul, map_pow, map_neg, map_one, pLoc_conjFin]
  rfl

/- English proof (translation)
Establish `hv : ∀ (h : GLw n (cPl E u)) (i j : Fin n), Valued.v ((thAt u h).val i j) = Valued.v ((h⁻¹).val j.rev i.rev)`. Introduce `h i j`. Rewrite using `[thAt_apply, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow, one_mul]`. Conclude with `(conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 _`. Rewrite `hk`, the goal using `[GlobLev.mem_KGL_iff_val]`.

Take `⟨h1, h2⟩` from `hk`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Use `h2 j.rev i.rev` as an intermediate fact. Rewrite `this` using `[← map_inv, hv, inv_inv, Fin.rev_rev, Fin.rev_rev]`. Conclude with `this`.

Use `h1 j.rev i.rev` as an intermediate fact. Rewrite `this` using `[hv, Fin.rev_rev, Fin.rev_rev]`. Then use the resulting hypothesis.
-/
theorem mem_KGL_of_thAt (u : Pl E) (k : GLw n (cPl E u)) (hk : thAt u k ∈ GlobalTheory.LFun.KGL u n) :
    k ∈ GlobalTheory.LFun.KGL (cPl E u) n := by
  have hv : ∀ (h : GLw n (cPl E u)) (i j : Fin n),
      Valued.v ((thAt u h).val i j) = Valued.v ((h⁻¹).val j.rev i.rev) := by
    intro h i j
    rw [thAt_apply, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow, one_mul]
    exact (conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 _
  rw [GlobLev.mem_KGL_iff_val] at hk ⊢
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := h2 j.rev i.rev
    rw [← map_inv, hv, inv_inv, Fin.rev_rev, Fin.rev_rev] at this
    exact this
  · have := h1 j.rev i.rev
    rwa [hv, Fin.rev_rev, Fin.rev_rev] at this

end GlobalTheory.EulerTw.IntRead

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

end GlobalTheory.EulerTw.IntRead
