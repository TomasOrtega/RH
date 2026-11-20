import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.XiSchur
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct ComplexOrder

/- English proof (translation)
Introduce `E _ _ _ a Ξ`. Take `⟨hL, hS⟩` from `xiSchur E a Ξ`. Take `⟨G, hG, hadj⟩` from `admEx E a Ξ`. Establish `h1 : oneL E a = toL (1 : Matrix (Fin a) (Fin a) (Cinf E))` using `rfl`. Take `⟨c, hc⟩` from `hS (Ξ.dmat (oneL E a)) fun X => by`.

Establish `h` using `hL 1 (Matrix.of X)`. Rewrite `h` using `[one_mul, mul_one, sub_self]`. Establish `h0 : toL (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 0` using `rfl`. Rewrite `h` using `[h0, map_zero, sub_eq_zero]`. Conclude with `h`.

Establish `h` using `hadj 1`. Rewrite `h` using `[star_one, ← h1, hc, conjTranspose_smul, conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]`. Use `⟨c.re, ?_⟩` and prove the remaining obligations. Unfold `HasOne`. Rewrite using `[hc]`.

Use extensionality with `i j`. Establish `hi` using `congrFun (congrFun h i) i`. Establish `hp : G i i ≠ 0` using `(hG.diag_pos (i := i)).ne'`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at hi`. Establish `hs : star c = c` using `mul_right_cancel₀ hp hi`.

Rewrite using `[← Complex.conj_eq_iff_re.1 hs]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Lit.Bor.oneReal :
    UpperTheory.V.Lit.Bor.OneReal := by
  intro E _ _ _ a Ξ
  obtain ⟨hL, hS⟩ := xiSchur E a Ξ
  obtain ⟨G, hG, hadj⟩ := admEx E a Ξ
  have h1 : oneL E a = toL (1 : Matrix (Fin a) (Fin a) (Cinf E)) := rfl
  obtain ⟨c, hc⟩ := hS (Ξ.dmat (oneL E a)) fun X => by
    have h := hL 1 (Matrix.of X)
    rw [one_mul, mul_one, sub_self] at h
    have h0 : toL (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 0 := rfl
    rw [h0, map_zero, sub_eq_zero] at h
    exact h
  have h := hadj 1
  rw [star_one, ← h1, hc, conjTranspose_smul, conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  refine ⟨c.re, ?_⟩
  unfold HasOne
  rw [hc]
  ext i j
  have hi := congrFun (congrFun h i) i
  have hp : G i i ≠ 0 := (hG.diag_pos (i := i)).ne'
  simp only [Matrix.smul_apply, smul_eq_mul] at hi
  have hs : star c = c := mul_right_cancel₀ hp hi
  rw [← Complex.conj_eq_iff_re.1 hs]
  simp
