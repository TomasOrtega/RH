import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.LFun

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(g⁻¹).valᵀ = _`. Rewrite using `[Matrix.coe_units_inv, Matrix.transpose_nonsing_inv]`.
-/
theorem invT_val_eq (g : GA E a) : (invT a (Ad E) g).val = (g.valᵀ)⁻¹ := by
  change (g⁻¹).valᵀ = _
  rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((GeneralLinearGroup.scalar (Fin a) z)⁻¹).valᵀ = _`. Rewrite using `[← map_inv]`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[GeneralLinearGroup.scalar]`. Simplify using `[GeneralLinearGroup.scalar, h, Ne.symm h]`.
-/
theorem invT_scalar {R : Type} [CommRing R] (z : Rˣ) :
    invT a R (GeneralLinearGroup.scalar (Fin a) z) = GeneralLinearGroup.scalar (Fin a) z⁻¹ := by
  apply Units.ext
  change ((GeneralLinearGroup.scalar (Fin a) z)⁻¹).valᵀ = _
  rw [← map_inv]
  ext i j
  by_cases h : i = j
  · subst h; simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h, Ne.symm h]

namespace CuspSub

variable (π : CuspSub E a)

def contra : CuspSub E a := UpperTheory.V.TC.dual π

/- English proof (translation)
The claim follows from `UpperTheory.V.TC.dual_dual π`.
-/
@[simp] theorem contra_contra : π.contra.contra = π := UpperTheory.V.TC.dual_dual π

variable {π} {π' : CuspSub E a}

/- English proof (translation)
The claim follows from `UpperTheory.V.TC.iso_dual h`.
-/
theorem Iso.contra (h : Iso π π') : Iso π.contra π'.contra := UpperTheory.V.TC.iso_dual h

/- English proof (translation)
Introduce and unpack `z _ ⟨ψ, hψ, rfl⟩`. Express the relevant statement in the definitionally equal form `rt E a _ (UpperTheory.V.TC.dualFn E a ψ) = _ • UpperTheory.V.TC.dualFn E a ψ`. Rewrite using `[UpperTheory.V.TC.rt_dualFn, invT_scalar, h z⁻¹ ψ hψ, map_smul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem HasCentral.contra {ω : HChar E} (h : π.HasCentral ω) : π.contra.HasCentral ω⁻¹ := by
  rintro z _ ⟨ψ, hψ, rfl⟩
  change rt E a _ (UpperTheory.V.TC.dualFn E a ψ) = _ • UpperTheory.V.TC.dualFn E a ψ
  rw [UpperTheory.V.TC.rt_dualFn, invT_scalar, h z⁻¹ ψ hψ, map_smul]
  congr 1
  simp

/- English proof (translation)
Take `⟨ω, h1, h2⟩` from `h`. Conclude with `⟨ω⁻¹, h1.inv, h2.contra⟩`.
-/
theorem IsUnitary.contra (h : π.IsUnitary) : π.contra.IsUnitary := by
  obtain ⟨ω, h1, h2⟩ := h
  exact ⟨ω⁻¹, h1.inv, h2.contra⟩

/- English proof (translation)
The claim follows from `UpperTheory.V.TC.hasSatGL_dual h`.
-/
theorem HasSatGL.contra {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : HasSatGL w (π.locRep w) B) :
    HasSatGL w (π.contra.locRep w) (B.map (·⁻¹)) := UpperTheory.V.TC.hasSatGL_dual h

end CuspSub

namespace CG

def contra (π : CG E a) : CG E a :=
  Quotient.map (sa := CuspSub.setoid E a) (sb := CuspSub.setoid E a) CuspSub.contra (fun _ _ h => h.contra) π

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem contra_mk (π : CuspSub E a) : (mk π).contra = mk π.contra := rfl

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with`. Consider the case `_ π => exact (isUnitary_mk π.contra).2 ((isUnitary_mk π).1 h).contra`.
-/
theorem IsUnitary.contra {π : CG E a} (h : π.IsUnitary) : π.contra.IsUnitary := by
  induction π using Quotient.inductionOn with
  | _ π => exact (isUnitary_mk π.contra).2 ((isUnitary_mk π).1 h).contra

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with`. Consider the case `_ π => exact CuspSub.HasSatGL.contra h`.
-/
theorem HasSat.contra {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) :
    π.contra.HasSat w (B.map (·⁻¹)) := by
  induction π using Quotient.inductionOn with
  | _ π => exact CuspSub.HasSatGL.contra h

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with`. Consider the case `_ π => exact congrArg mk π.contra_contra`.
-/
@[simp] theorem contra_contra (π : CG E a) : π.contra.contra = π := by
  induction π using Quotient.inductionOn with
  | _ π => exact congrArg mk π.contra_contra

end CG

end GlobalTheory.CuspRep
