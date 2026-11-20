import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.ConjForm

def refl (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma coe_refl (τ : ℍ) : ((refl τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
@[simp] lemma im_refl (τ : ℍ) : (refl τ).im = τ.im := by
  change (-conj (τ : ℂ)).im = τ.im
  simp [UpperHalfPlane.coe_im]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
lemma qs_conj (g : ℕ → ℂ) (τ : ℍ) : qs (fun n => conj (g n)) τ = conj (qs g (refl τ)) := by
  unfold qs
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp [coe_refl, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]

def twist (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linarith⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma twist_00 (γ : SL(2, ℤ)) : twist γ 0 0 = γ 0 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma twist_01 (γ : SL(2, ℤ)) : twist γ 0 1 = -γ 0 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma twist_10 (γ : SL(2, ℤ)) : twist γ 1 0 = -γ 1 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma twist_11 (γ : SL(2, ℤ)) : twist γ 1 1 = γ 1 1 := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma refl_smul (γ : SL(2, ℤ)) (τ : ℍ) : refl (γ • τ) = twist γ • refl τ := by
  apply UpperHalfPlane.ext
  have e := UpperHalfPlane.coe_specialLinearGroup_apply γ τ
  have e2 := UpperHalfPlane.coe_specialLinearGroup_apply (twist γ) (refl τ)
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at e e2
  have hd := UpperHalfPlane.denom_ne_zero γ τ
  rw [UpperHalfPlane.denom] at hd
  simp at hd
  rw [coe_refl, e, e2, coe_refl, map_div₀]
  have hd' : conj (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 := (map_ne_zero _).2 hd
  have hd'' : ((twist γ 1 0 : ℤ) : ℂ) * (-conj (τ : ℂ)) + ((twist γ 1 1 : ℤ) : ℂ) =
      conj (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    simp [map_add, map_mul, map_intCast]
  rw [hd'', neg_div', div_left_inj' hd']
  simp [map_add, map_mul, map_intCast]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
lemma conj_ch {N : ℕ} (χ : DirichletCharacter ℂ N) (d : ℤ) : conj (ch χ d) = ch χ⁻¹ d := by
  unfold ch
  exact MulChar.star_apply' χ _

end GlobalTheory.EisM.ConjForm

namespace GlobalTheory.EisM.ConjForm

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
lemma polyB_conj {g : ℕ → ℂ} (h : PolyB g) : PolyB (fun n => conj (g n)) := by
  obtain ⟨C, A, hC⟩ := h
  exact ⟨C, A, fun n => by simpa using hC n⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
lemma inv_conj {k L : ℕ} {χ : DirichletCharacter ℂ L} {g : ℕ → ℂ} (h : Inv k L (ch χ) (qs g)) :
    Inv k L (ch χ⁻¹) (qs (fun n => conj (g n))) := by
  intro γ hc τ
  have h1 := h (twist γ) (by simpa using hc) (refl τ)
  rw [qs_conj, qs_conj, refl_smul, h1, map_mul, map_mul, map_pow, conj_ch]
  congr 2
  simp [map_add, map_mul, map_intCast]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
lemma cf_conj {k N : ℕ} {χ : DirichletCharacter ℂ N} {g : ℕ → ℂ} (h : CF k N (ch χ) g) :
    CF k N (ch χ⁻¹) (fun n => conj (g n)) := by
  obtain ⟨⟨hp, hi⟩, C, hC⟩ := h
  refine ⟨⟨polyB_conj hp, inv_conj hi⟩, C, fun τ => ?_⟩
  have := hC (refl τ)
  rw [im_refl] at this
  rwa [qs_conj, Complex.norm_conj]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem conj_form : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ),
    (CF k N (ch χ) g → CF k N (ch χ⁻¹) (fun n => conj (g n))) ∧
    (Prim k N χ g → Prim k N χ⁻¹ (fun n => conj (g n))) := by
  intro k N χ g
  refine ⟨cf_conj, fun h => ⟨cf_conj h.cf, by simp [h.one], fun n hn => by simp [h.zero n hn], ?_⟩⟩
  intro q hq hqN
  funext n
  have e := congrFun (h.eig q hq hqN) n
  have e' := congrArg conj e
  simp only [To, Vo, map_add, map_mul, map_pow, map_natCast, conj_ch] at e'
  simp only [To, Vo]
  rw [← e']
  congr 2
  split_ifs <;> simp

end GlobalTheory.EisM.ConjForm

end
