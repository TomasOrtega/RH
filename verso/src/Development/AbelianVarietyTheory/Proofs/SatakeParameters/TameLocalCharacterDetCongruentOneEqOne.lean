import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section

namespace GlobalTheory.TwV.AwayCpl.RhoOne

open GlobalTheory.TopStep

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[redGL_val, Units.val_one]`. Use extensionality with `a b`. Establish `hq` using `qOf_ne_zero (P := P)`. Establish `hint : IntAt P ((k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a) / ((qOf P : ℕ) : E))`.

Take `⟨d, hd⟩ : ∃ d, D = d + 1` from `⟨D - 1, by omega⟩`. Establish `e : (k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a) / ((qOf P : ℕ) : E) = ((qOf P : ℕ) : E) ^ d * ((((qOf P : ℕ) : E) ^ D)⁻¹ * (k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a))`. Rewrite using `[hd, pow_succ]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `(intAt_pow (intAt_nat _) _).mul (hk b a)`. Establish `h0` using `redP_eq_zero_of_div hint`. Establish `hs : IntAt P ((Pi.single b 1 : Sp E n) a)` using `mem_stdAt.1 (single_mem_stdAt b) a`. Apply the tactic sequence `rw [reduction_sub (glint_entry k a b) hs, sub_eq_zero] at h0`. Rewrite using `[redMat, Matrix.of_apply, h0]`.

Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[reduction_one₂]`. Simplify using `[Pi.single_apply, h, reduction_zero]`.
-/
theorem redGL_eq_one_of_cong {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (D : ℕ) (hD : 1 ≤ D) (k : GLint E n P)
    (hk : ∀ s l, IntAt P ((((qOf P : ℕ) : E) ^ D)⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l))) :
    redGL n P k = 1 := by
  apply Units.ext
  rw [redGL_val, Units.val_one]
  ext a b
  have hq := qOf_ne_zero (P := P)
  have hint : IntAt P ((k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a) / ((qOf P : ℕ) : E)) := by
    obtain ⟨d, hd⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
    have e : (k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a) / ((qOf P : ℕ) : E) =
        ((qOf P : ℕ) : E) ^ d * ((((qOf P : ℕ) : E) ^ D)⁻¹ * (k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a)) := by
      rw [hd, pow_succ]
      field_simp
    rw [e]
    exact (intAt_pow (intAt_nat _) _).mul (hk b a)
  have h0 := redP_eq_zero_of_div hint
  have hs : IntAt P ((Pi.single b 1 : Sp E n) a) := mem_stdAt.1 (single_mem_stdAt b) a
  rw [reduction_sub (glint_entry k a b) hs, sub_eq_zero] at h0
  rw [redMat, Matrix.of_apply, h0]
  by_cases h : a = b
  · subst h
    simp [reduction_one₂]
  · simp [Pi.single_apply, h, reduction_zero]

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst hc i n P k hk`. Establish `hred` using `redGL_eq_one_of_cong (cst.D P) (hc.D_pos P) k hk`. Establish `hdet : redP P.1 ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1`. Rewrite using `[(det_glint k).2, ← redGL_val, hred, Units.val_one, Matrix.det_one]`. Unfold `rhoS LocE.unitV`.

Rewrite using `[hdet]`. Simplify using the standard rewrite rules.
-/
theorem rhoS_det_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (i n : ℕ) (P : rowSG Pr sel mu) (k : GLint X.E n P.1),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E n) l))) →
    rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := by
  intro X Pr R Ch sel S mu cst hc i n P k hk
  have hred := redGL_eq_one_of_cong (cst.D P) (hc.D_pos P) k hk
  have hdet : redP P.1 ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := by
    rw [(det_glint k).2, ← redGL_val, hred, Units.val_one, Matrix.det_one]
  unfold rhoS LocE.unitV
  rw [hdet]
  simp

end GlobalTheory.TwV.AwayCpl.RhoOne
