import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Complement

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsHyperbolicPair (h : HermitianForm F E W) (v w : W) : Prop :=
  h.toSesq v v = 0 ∧ h.toSesq w w = 0 ∧ h.toSesq v w = 1

def hypComplement (h : HermitianForm F E W) (v w : W) : Submodule E W :=
  LinearMap.ker (h.toSesq v) ⊓ LinearMap.ker (h.toSesq w)

/- English proof (translation)
Simplify using `[hypComplement]`.
-/
theorem mem_hypComplement {h : HermitianForm F E W} {v w x : W} :
    x ∈ hypComplement h v w ↔ h.toSesq v x = 0 ∧ h.toSesq w x = 0 := by
  simp [hypComplement]

def ComplementForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ v w : W, IsHyperbolicPair h v w →
    ∃ h' : HermitianForm F E (hypComplement h v w), ∀ x y, h'.toSesq x y = h.toSesq x y

end Complement

namespace GaussianPlane

def w0G : Fin 2 → Eg := ![1 / 2, -1 / 2]

/- English proof (translation)
The claim follows from `map_ofNat _ 2`.
-/
theorem conj_two_G : conj ℚ Eg (2 : Eg) = 2 := map_ofNat _ 2

/- English proof (translation)
Rewrite `hx` using `[mem_hypComplement, hG_apply, hG_apply]`. Take `⟨h1, h2⟩` from `hx`. Simplify using `[v0, w0G, conj_two_G] at h1 h2`. Establish `e0 : x 0 = 0` using `by linear_combination h2 + (1 / 2 : Eg) * h1`. Establish `e1 : x 1 = 0` using `by linear_combination h2 - (1 / 2 : Eg) * h1`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `e0`. Conclude with `e1`.
-/
theorem eq_zero_of_mem_hypComplementG {x : Fin 2 → Eg} (hx : x ∈ hypComplement hG v0 w0G) :
    x = 0 := by
  rw [mem_hypComplement, hG_apply, hG_apply] at hx
  obtain ⟨h1, h2⟩ := hx
  simp [v0, w0G, conj_two_G] at h1 h2
  have e0 : x 0 = 0 := by linear_combination h2 + (1 / 2 : Eg) * h1
  have e1 : x 1 = 0 := by linear_combination h2 - (1 / 2 : Eg) * h1
  funext i
  fin_cases i
  · exact e0
  · exact e1

instance : Subsingleton (hypComplement hG v0 w0G) :=
  ⟨fun a b => Subtype.ext ((eq_zero_of_mem_hypComplementG a.2).trans
    (eq_zero_of_mem_hypComplementG b.2).symm)⟩

def complementFormG : HermitianForm ℚ Eg (hypComplement hG v0 w0G) where
  toSesq := 0
  isSymm := ⟨fun x y => by
    change conjHom ℚ Eg (0 : Eg) = (0 : Eg)
    exact map_zero _⟩
  nonsingular := by
    refine ⟨fun a b _ => Subsingleton.elim a b, fun φ => ⟨0, ?_⟩⟩
    ext x
    rw [Subsingleton.elim x 0]
    simp

end GaussianPlane

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
