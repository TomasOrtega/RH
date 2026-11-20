import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `F _ _ _ π χ hπ w σ hσ z c hc`. Take `⟨B, d, hl, -, -, hf, -, -⟩` from `hπ`. Take `⟨hnt, htop⟩` from `hσ`. Use `set k := locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) z) with hk`. Establish `hact : ∀ φ : π.V, π.finPart k φ = c • φ`.

Introduce `φ`. Establish `hφ : φ ∈ (⊤ : Submodule ℂ π.V)` using `Submodule.mem_top`. Rewrite `hφ` using `[← htop]`. Use `Submodule.iSup_induction _ (motive := fun φ => π.finPart k φ = c • φ) hφ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `f _ ⟨v, rfl⟩`.

Rewrite using `[hk, ← f.2, hc, map_smul]`. Simplify using the standard rewrite rules. Introduce `x y hx hy`. Rewrite using `[map_add, hx, hy, smul_add]`. Establish `hop : ∀ φ : π.V, π.op (.fin k) φ = c • φ` using `fun φ => hact φ`.

Take `⟨φ, hφ⟩` from `exists_ne (0 : π.V)`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hφ (hl φ h)`.

Establish `h1` using `hf k φ ψ`. Rewrite `h1` using `[hop, hop, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc]`. Establish `h2` using `mul_right_cancel₀ hψ h1`. Establish `hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2`. Use `ext`.

Simplify using `[Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, sq]`. Establish `h3 : chiDet 2 χ (finGL F 2 k) = χ.loc w (z ^ 2)`. Rewrite using `[← hdet]`. Conclude with `TR.CuspSub.chiDet_locGL χ w _`. Rewrite using `[sq, h2, h3, map_pow, Units.val_pow_eq_pow_val]`.
-/
theorem UpperTheory.central_char_sq_eq_of_isSelfDualBy :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (χ : HChar F), π.IsSelfDualBy χ → ∀ (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic π.finPart w σ → ∀ (z : (w.adicCompletion F)ˣ) (c : ℂ), (∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = c • v) → c ^ 2 = ((χ.loc w z : ℂˣ) : ℂ) ^ 2 := by
  intro F _ _ _ π χ hπ w σ hσ z c hc
  obtain ⟨B, d, hl, -, -, hf, -, -⟩ := hπ
  obtain ⟨hnt, htop⟩ := hσ
  set k := locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) z) with hk
  have hact : ∀ φ : π.V, π.finPart k φ = c • φ := by
    intro φ
    have hφ : φ ∈ (⊤ : Submodule ℂ π.V) := Submodule.mem_top
    rw [← htop] at hφ
    refine Submodule.iSup_induction _ (motive := fun φ => π.finPart k φ = c • φ) hφ ?_ ?_ ?_
    · rintro f _ ⟨v, rfl⟩
      rw [hk, ← f.2, hc, map_smul]
    · simp
    · intro x y hx hy
      rw [map_add, hx, hy, smul_add]
  have hop : ∀ φ : π.V, π.op (.fin k) φ = c • φ := fun φ => hact φ
  obtain ⟨φ, hφ⟩ := exists_ne (0 : π.V)
  obtain ⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (hl φ h)
  have h1 := hf k φ ψ
  rw [hop, hop, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
  have h2 := mul_right_cancel₀ hψ h1
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, sq]
  have h3 : chiDet 2 χ (finGL F 2 k) = χ.loc w (z ^ 2) := by
    rw [← hdet]
    exact TR.CuspSub.chiDet_locGL χ w _
  rw [sq, h2, h3, map_pow, Units.val_pow_eq_pow_val]
