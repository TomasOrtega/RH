import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne

noncomputable section

namespace UpperTheory.GalN

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def OpenB (q : ℕ) (α : ℂ) : Prop := (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖α‖ ∧ ‖α‖ < (q : ℝ) ^ (1 / 2 : ℝ)

/- English proof (translation)
Establish `hq' : (1 : ℝ) < q` using `by exact_mod_cast hq`. Rewrite using `[OpenB, h]`. Conclude with `⟨Real.rpow_lt_one_of_one_lt_of_neg hq' (by norm_num), Real.one_lt_rpow hq' (by norm_num)⟩`.
-/
theorem OpenB.of_norm_one {q : ℕ} (hq : 1 < q) {α : ℂ} (h : ‖α‖ = 1) : OpenB q α := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  rw [OpenB, h]
  exact ⟨Real.rpow_lt_one_of_one_lt_of_neg hq' (by norm_num), Real.one_lt_rpow hq' (by norm_num)⟩

/- English proof (translation)
Rewrite `h` using `[OpenB, norm_mul, he, mul_one]`. Then use the resulting hypothesis.
-/
theorem OpenB.of_mul {q : ℕ} {α e : ℂ} (h : OpenB q (α * e)) (he : ‖e‖ = 1) : OpenB q α := by
  rwa [OpenB, norm_mul, he, mul_one] at h

def TempAt {a : ℕ} (π : A.CG a) (w : PlE H) : Prop :=
  (a = 1 → A.tempered (A.locG π w)) ∧ (A.unr (A.locG π w) → ∀ α ∈ A.frobEig (A.locG π w), OpenB (normV w) α)

def AllCuspidalOpenBound : Prop := ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.csd π → A.ralg π → ∀ w, TempAt N A π w

variable {N A}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => h, fun hu α hα => OpenB.of_norm_one (NumberField.HeightOneSpectrum.one_lt_absNorm w) ((A.tempered_unr _ hu).1 h α hα)⟩`.
-/
theorem TempAt.of_tempered {a : ℕ} {π : A.CG a} {w : PlE H} (h : A.tempered (A.locG π w)) : TempAt N A π w :=
  ⟨fun _ => h, fun hu α hα => OpenB.of_norm_one (NumberField.HeightOneSpectrum.one_lt_absNorm w)
    ((A.tempered_unr _ hu).1 h α hα)⟩

/- English proof (translation)
Introduce `a π ha hc hr w` and use `.of_tempered (h a π ha hc hr w)`.
-/
theorem tempoA (h : TemperedCuspidal N A) : AllCuspidalOpenBound N A := fun a π ha hc hr w => .of_tempered (h a π ha hc hr w)
/- English proof (translation)
The claim follows from `tempoA h`.
-/
theorem tempo {D : D7} (h : adm7 D) : AllCuspidalOpenBound D.nd D.naut := tempoA h
/- English proof (translation)
The claim follows from `h`.
-/
theorem tempo' {D : D7} (h : AllCuspidalOpenBound D.nd D.naut) : AllCuspidalOpenBound D.nd D.naut := h

end UpperTheory.GalN
