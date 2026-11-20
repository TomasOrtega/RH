import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfU

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (finId locGL finGL)

/- English proof (translation)
Establish `h` using `GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)`. Rewrite `h`, the goal using `[locGL, GlobalTheory.CuspRep.cornerGL_scalar]`. Rewrite using `[finGL, GlobalTheory.CuspRep.cornerGL_scalar]`. Use `congr 1`. Conclude with `(congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))`.
-/
private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

/- English proof (translation)
Take `⟨d, hd⟩` from `IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4 * (p : ℂ)) (n := 2) two_pos`. Establish `h : (s + d) / 2 * ((s - d) / 2) = p` using `by linear_combination (-1 / 4 : ℂ) * hd`. Establish `h0` using `h ▸ p.ne_zero`. Use `⟨Units.mk0 _ (left_ne_zero_of_mul h0), Units.mk0 _ (right_ne_zero_of_mul h0), ?_, Units.ext h⟩` and prove the remaining obligations. Simplify using `only [Units.val_mk0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem roots (s : ℂ) (p : ℂˣ) : ∃ α β : ℂˣ, (α : ℂ) + β = s ∧ α * β = p := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4 * (p : ℂ)) (n := 2) two_pos
  have h : (s + d) / 2 * ((s - d) / 2) = p := by linear_combination (-1 / 4 : ℂ) * hd
  have h0 := h ▸ p.ne_zero
  refine ⟨Units.mk0 _ (left_ne_zero_of_mul h0), Units.mk0 _ (right_ne_zero_of_mul h0), ?_, Units.ext h⟩
  simp only [Units.val_mk0]
  ring

/- English proof (translation)
Introduce `F _ _ _ k c ω φ hφ h0 w lam hw hU`. Establish `hq : (0 : ℝ) < normV w` using `Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))`. Establish `hne : ∀ t : ℝ, (((normV w : ℝ) ^ t : ℝ) : ℂ) ≠ 0` using `fun t => Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq t).ne'`. Take `⟨α, β, h1, h2⟩` from `roots (lam / (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)) (ω.val w)`. Establish `h3 : (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = lam`.

Rewrite using `[h1, mul_div_cancel₀ _ (hne _)]`. Use `⟨α, β, UpperTheory.V.Af.Nf.satOfU F w _ _ φ α β h0 (hw ▸ hφ.level w) ?_ ?_, h3, h2⟩` and prove the remaining obligations. Use `smul_right_injective _ (hne ((k : ℝ) / 2 - 1)) (hU.trans ?_) dsimp only` and prove the remaining obligations. Rewrite using `[smul_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hq, ← h3]`. Use `congr 4`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (g * finGL F 2 (locGL F 2 w _)) = _`. Rewrite using `[fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Af.Nf.satHol :
    UpperTheory.V.Af.Nf.SatHol := by
  intro F _ _ _ k c ω φ hφ h0 w lam hw hU
  have hq : (0 : ℝ) < normV w :=
    Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
  have hne : ∀ t : ℝ, (((normV w : ℝ) ^ t : ℝ) : ℂ) ≠ 0 := fun t =>
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq t).ne'
  obtain ⟨α, β, h1, h2⟩ := roots (lam / (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)) (ω.val w)
  have h3 : (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = lam := by
    rw [h1, mul_div_cancel₀ _ (hne _)]
  refine ⟨α, β, UpperTheory.V.Af.Nf.satOfU F w _ _ φ α β h0 (hw ▸ hφ.level w) ?_ ?_, h3, h2⟩
  · refine smul_right_injective _ (hne ((k : ℝ) / 2 - 1)) (hU.trans ?_)
    dsimp only
    rw [smul_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hq, ← h3]
    congr 4
    ring
  · rw [h2]
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _
    rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]
    rfl
