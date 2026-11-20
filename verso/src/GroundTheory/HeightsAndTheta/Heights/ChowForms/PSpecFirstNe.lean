import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Choice

variable {F : Type} [Field F] {k n : ℕ}

def specFirstSplit (ij : Fin (k + 1) × Fin n) : (Fin k × Fin n) ⊕ Fin n :=
  Fin.cases (motive := fun _ => (Fin k × Fin n) ⊕ Fin n) (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1

/- English proof (translation)
Introduce and unpack `⟨i, m⟩ ⟨j, m'⟩ h`. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [specFirstSplit]`.
-/
theorem specFirstSplit_injective : Function.Injective (specFirstSplit (k := k) (n := n)) := by
  rintro ⟨i, m⟩ ⟨j, m'⟩ h
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [specFirstSplit]

/- English proof (translation)
Establish `h : (bind₁ (specFirstVar t) : MvPolynomial (Fin (k + 1) × Fin n) F →ₐ[F] _).toRingHom = (map (eval t)).comp ((sumAlgEquiv F (Fin k × Fin n) (Fin n)).toRingHom.comp (rename specFirstSplit).toRingHom)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Express the relevant statement in the definitionally equal form `bind₁ (specFirstVar t) (C a) = map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit (C a)))`. Rewrite using `[bind₁_C_right, rename_C, sumAlgEquiv_C_inl, map_C, eval_C]`.

Introduce and unpack `⟨i, m⟩`. Apply the tactic sequence `cases i using Fin.cases <;>`. Simplify using `[specFirstVar, specFirstSplit, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr]`. Conclude with `RingHom.congr_fun h g`.
-/
theorem specFirst_eq_map_eval (g : MvPolynomial (Fin (k + 1) × Fin n) F) (t : Fin n → F) :
    specFirst g t = map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit g)) := by
  have h : (bind₁ (specFirstVar t) : MvPolynomial (Fin (k + 1) × Fin n) F →ₐ[F] _).toRingHom =
      (map (eval t)).comp ((sumAlgEquiv F (Fin k × Fin n) (Fin n)).toRingHom.comp
        (rename specFirstSplit).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change bind₁ (specFirstVar t) (C a) =
        map (eval t) (sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit (C a)))
      rw [bind₁_C_right, rename_C, sumAlgEquiv_C_inl, map_C, eval_C]
    · rintro ⟨i, m⟩
      cases i using Fin.cases <;>
        simp [specFirstVar, specFirstSplit, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr]
  exact RingHom.congr_fun h g

/- English proof (translation)
Use `set g := sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit f) with hg_def`. Establish `hg : g ≠ 0` using `(map_ne_zero_iff _ (sumAlgEquiv F (Fin k × Fin n) (Fin n)).injective).mpr ((map_ne_zero_iff _ (rename_injective _ specFirstSplit_injective)).mpr hf)`. Take `⟨β, hβ⟩` from `ne_zero_iff.mp hg`. Establish `ht : ∃ t : Fin n → F, eval t (coeff β g) ≠ 0`. Assume the negation of the conclusion as `h`.

Simplify using `only [not_exists, not_not] at h`. Conclude with `hβ (MvPolynomial.funext fun x => by simp [h x])`. Take `⟨t, ht⟩` from `ht`. Use `⟨t, fun h0 => ht ?_⟩` and prove the remaining obligations. Use `congr_arg (coeff β) h0` as an intermediate fact.

Rewrite `this` using `[specFirst_eq_map_eval, ← hg_def, coeff_map, coeff_zero]`. Then use the resulting hypothesis.
-/
theorem exists_specFirst_ne_zero [Infinite F] {f : MvPolynomial (Fin (k + 1) × Fin n) F} (hf : f ≠ 0) :
    ∃ t : Fin n → F, specFirst f t ≠ 0 := by
  set g := sumAlgEquiv F (Fin k × Fin n) (Fin n) (rename specFirstSplit f) with hg_def
  have hg : g ≠ 0 :=
    (map_ne_zero_iff _ (sumAlgEquiv F (Fin k × Fin n) (Fin n)).injective).mpr
      ((map_ne_zero_iff _ (rename_injective _ specFirstSplit_injective)).mpr hf)
  obtain ⟨β, hβ⟩ := ne_zero_iff.mp hg
  have ht : ∃ t : Fin n → F, eval t (coeff β g) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hβ (MvPolynomial.funext fun x => by simp [h x])
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, fun h0 => ht ?_⟩
  have := congr_arg (coeff β) h0
  rwa [specFirst_eq_map_eval, ← hg_def, coeff_map, coeff_zero] at this

end Choice

/- English proof (translation)
Introduce `h`. Distinguish the cases in `H : ∃ s : Finset B, Nonempty (Module.Basis s O B)`. Take `⟨s, ⟨b⟩⟩` from `H`. Establish `: Module.Free O B` using `Module.Free.of_basis b`. Establish `hker` using `LinearMap.bot_lt_ker_of_det_eq_zero h`.

Rewrite `hker` using `[bot_lt_iff_ne_bot, Ne, LinearMap.ker_eq_bot]`. Conclude with `hker fun x y hxy => mul_left_cancel₀ hθ (by simpa using hxy)`. Simplify using `[LinearMap.coe_det, H] at h`.
-/
theorem det_mulLeft_ne_zero {O B : Type*} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [Algebra O B]
    {θ : B} (hθ : θ ≠ 0) : LinearMap.det (LinearMap.mulLeft O θ) ≠ 0 := by
  classical
  intro h
  by_cases H : ∃ s : Finset B, Nonempty (Module.Basis s O B)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : Module.Free O B := Module.Free.of_basis b
    have hker := LinearMap.bot_lt_ker_of_det_eq_zero h
    rw [bot_lt_iff_ne_bot, Ne, LinearMap.ker_eq_bot] at hker
    exact hker fun x y hxy => mul_left_cancel₀ hθ (by simpa using hxy)
  · simp [LinearMap.coe_det, H] at h

/- English proof (translation)
Introduce `F _ _ n e I f u hI hf hu`. Take `⟨t, ht⟩` from `exists_specFirst_ne_zero hf.1`. Establish `hlt : linForm t ∉ I` using `fun hmem => ht (by`. Establish `hmem'` using `h₂ F n e I I f t hf le_rfl hmem`. Rewrite using `[h₁ F n e I f hI hf, Ideal.mem_bot] at hmem')` and apply the resulting hypothesis.

Establish `htp : specFirst f t ∉ (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))`. Rewrite using `[Ideal.mem_bot]` and apply the resulting hypothesis. Take `⟨hdom, -, hθ⟩` from `h₄ F n e I f t ⊥ hI hf hlt`. Establish `hnorm` using `h₅ F n e I f t ⊥ hI hf (Or.inl rfl) htp u`. Establish `ha : algebraMap _ (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))) (specFirst f t) ≠ 0` using `fun h => ht (IsLocalization.injective (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))) (Ideal.primeCompl_le_nonZeroDivisors ⊥) (h.trans (map_zero _).symm))`.

Establish `hdet` using `det_mulLeft_ne_zero (O := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))) (hθ u hu)`. Introduce `h0`. Rewrite `hnorm` using `[h0, map_zero]`. Conclude with `mul_ne_zero ha hdet hnorm.symm`.
-/
theorem SpecFirstNe.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₄ : ChartLocDomain.Statement) (h₅ : ChartNorm.Statement) : SpecFirstNe.Statement := by
  intro F _ _ n e I f u hI hf hu
  obtain ⟨t, ht⟩ := exists_specFirst_ne_zero hf.1
  have hlt : linForm t ∉ I := fun hmem => ht (by
    have hmem' := h₂ F n e I I f t hf le_rfl hmem
    rwa [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem')
  have htp : specFirst f t ∉ (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)) := by
    rwa [Ideal.mem_bot]
  obtain ⟨hdom, -, hθ⟩ := h₄ F n e I f t ⊥ hI hf hlt
  have hnorm := h₅ F n e I f t ⊥ hI hf (Or.inl rfl) htp u
  have ha : algebraMap _ (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (specFirst f t) ≠ 0 := fun h => ht
    (IsLocalization.injective (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
      (Ideal.primeCompl_le_nonZeroDivisors ⊥) (h.trans (map_zero _).symm))
  have hdet := det_mulLeft_ne_zero (O := Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))
    (hθ u hu)
  intro h0
  rw [h0, map_zero] at hnorm
  exact mul_ne_zero ha hdet hnorm.symm

end

end GroundTheory.Heights₂.Heights
