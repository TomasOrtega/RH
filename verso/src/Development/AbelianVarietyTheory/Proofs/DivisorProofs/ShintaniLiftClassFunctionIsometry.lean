import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EveryElementIsNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIsGaloisTwistedNormGLMulCardGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLiftClassFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusionStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `F F' _ _ _ _ s hs n f f' hf hf'`. Use `haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective`. Use `letI : Fintype (GL (Fin n) F) := Fintype.ofFinite _`. Use `letI : Fintype (GL (Fin n) F') := Fintype.ofFinite _`. Establish `hex` using `GlobalTheory.T.every_element_is_norm F F' s hs n`.

Establish `hfib` using `GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n`. Establish `hlf` using `(GlobalTheory.T.base_change_lift_class_function F F' s hs n f hf).1`. Establish `hlf'` using `(GlobalTheory.T.base_change_lift_class_function F F' s hs n f' hf').1`. Establish `hnd` using `GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n`. Take `⟨c, hc⟩ : ∃ c : GL (Fin n) F → ℂ, ∀ γ, c γ = (Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} : ℂ)` from `⟨_, fun _ => rfl⟩`.

Take `⟨v, hv⟩ : ∃ v : GL (Fin n) F → ℂ, ∀ γ, v γ = f γ * star (f' γ)` from `⟨_, fun _ => rfl⟩`. Establish `hcne : ∀ γ, c γ ≠ 0`. Introduce `γ`. Rewrite using `[hc, Nat.cast_ne_zero]`. Use `haveI : Nonempty {γ' : GL (Fin n) F // IsConj γ γ'} := ⟨⟨γ, IsConj.refl γ⟩⟩`.

Conclude with `Nat.card_pos.ne'`. Establish `hclass : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → ∀ γ' : GL (Fin n) F, IsNorm s δ γ' ↔ IsConj γ γ'`. Introduce `δ γ h γ'`. Unfold `IsNorm at *`. Prove the components needed by the constructor for the conclusion.

Introduce `h'`. Conclude with `hnd γ γ' (IsConj.trans h (IsConj.symm h'))`. Introduce `h'`. Conclude with `IsConj.trans (IsConj.symm (MonoidHom.map_isConj (incl F F' n) h')) h`. Establish `hcard : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → c γ = ((Finset.univ.filter fun γ' => IsNorm s δ γ').card : ℂ)`.

Introduce `δ γ h`. Rewrite using `[hc, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 2`. Use extensionality with `γ'`. Simplify using `[hclass δ γ h γ']`.

Establish `key : ∀ δ : GL (Fin n) F', (∑ γ, if IsNorm s δ γ then v γ / c γ else 0) = shLift s f δ * star (shLift s f' δ)`. Introduce `δ`. Take `⟨γ0, h0⟩` from `hex δ`. Establish `e : ∀ γ, (if IsNorm s δ γ then v γ / c γ else 0) = if IsNorm s δ γ then (shLift s f δ * star (shLift s f' δ)) / c γ0 else 0`. Introduce `γ`.

Use `split_ifs with h`. Rewrite using `[hv, hcard δ γ h, ← hcard δ γ0 h0, hlf δ γ h, hlf' δ γ h]`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl (fun γ _ => e γ), Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcard δ γ0 h0]`. Clear denominators, using `[hcne γ0]` for the nonvanishing conditions.

Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`. Establish `lhs : (∑ δ, shLift s f δ * star (shLift s f' δ)) = ∑ γ, ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ)`. Rewrite using `[← Finset.sum_congr rfl (fun δ _ => key δ), Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun γ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`.

Rewrite using `[lhs, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun γ _ => ?_)` and prove the remaining obligations. Establish `h` using `hfib γ`. Rewrite `h` using `[Nat.card_eq_fintype_card (α := {δ : GL (Fin n) F' // IsNorm s δ γ}), Fintype.card_subtype]`. Establish `h' : (Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) = c γ * (Nat.card (GL (Fin n) F') : ℂ)`.

Rewrite using `[hc]`. Conclude with `(by rw [mul_comm]; exact h)` after adjusting the coercions. Rewrite using `[show (Nat.card (GL (Fin n) F) : ℂ) * (((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ)) = ((Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ)) * v γ / c γ by ring, h', hv]`. Clear denominators, using `[hcne γ]` for the nonvanishing conditions.
-/
theorem shLift_isometry : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f f' : GL (Fin n) F → ℂ), IsCl f → IsCl f' →
    (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ δ, shLift s f δ * star (shLift s f' δ) =
      (Nat.card (GL (Fin n) F') : ℂ) * ∑ᶠ γ, f γ * star (f' γ) := by
  intro F F' _ _ _ _ s hs n f f' hf hf'
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  letI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  letI : Fintype (GL (Fin n) F') := Fintype.ofFinite _
  have hex := GlobalTheory.T.every_element_is_norm F F' s hs n
  have hfib := GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n
  have hlf := (GlobalTheory.T.base_change_lift_class_function F F' s hs n f hf).1
  have hlf' := (GlobalTheory.T.base_change_lift_class_function F F' s hs n f' hf').1
  have hnd := GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n
  obtain ⟨c, hc⟩ : ∃ c : GL (Fin n) F → ℂ, ∀ γ, c γ = (Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} : ℂ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : GL (Fin n) F → ℂ, ∀ γ, v γ = f γ * star (f' γ) := ⟨_, fun _ => rfl⟩
  have hcne : ∀ γ, c γ ≠ 0 := by
    intro γ
    rw [hc, Nat.cast_ne_zero]
    haveI : Nonempty {γ' : GL (Fin n) F // IsConj γ γ'} := ⟨⟨γ, IsConj.refl γ⟩⟩
    exact Nat.card_pos.ne'

  have hclass : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → ∀ γ' : GL (Fin n) F, IsNorm s δ γ' ↔ IsConj γ γ' := by
    intro δ γ h γ'
    unfold IsNorm at *
    constructor
    · intro h'
      exact hnd γ γ' (IsConj.trans h (IsConj.symm h'))
    · intro h'
      exact IsConj.trans (IsConj.symm (MonoidHom.map_isConj (incl F F' n) h')) h
  have hcard : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → c γ = ((Finset.univ.filter fun γ' => IsNorm s δ γ').card : ℂ) := by
    intro δ γ h
    rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    ext γ'
    simp [hclass δ γ h γ']
  have key : ∀ δ : GL (Fin n) F',
      (∑ γ, if IsNorm s δ γ then v γ / c γ else 0) = shLift s f δ * star (shLift s f' δ) := by
    intro δ
    obtain ⟨γ0, h0⟩ := hex δ
    have e : ∀ γ, (if IsNorm s δ γ then v γ / c γ else 0) =
        if IsNorm s δ γ then (shLift s f δ * star (shLift s f' δ)) / c γ0 else 0 := by
      intro γ
      split_ifs with h
      · rw [hv, hcard δ γ h, ← hcard δ γ0 h0, hlf δ γ h, hlf' δ γ h]
      · rfl
    rw [Finset.sum_congr rfl (fun γ _ => e γ), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, ← hcard δ γ0 h0]
    field_simp [hcne γ0]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have lhs : (∑ δ, shLift s f δ * star (shLift s f' δ)) =
      ∑ γ, ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ) := by
    rw [← Finset.sum_congr rfl (fun δ _ => key δ), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [lhs, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  have h := hfib γ
  rw [Nat.card_eq_fintype_card (α := {δ : GL (Fin n) F' // IsNorm s δ γ}), Fintype.card_subtype] at h
  have h' : (Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) =
      c γ * (Nat.card (GL (Fin n) F') : ℂ) := by
    rw [hc]
    exact_mod_cast (by rw [mul_comm]; exact h)
  rw [show (Nat.card (GL (Fin n) F) : ℂ) * (((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ)) =
      ((Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ)) * v γ / c γ by ring,
    h', hv]
  field_simp [hcne γ]

end GlobalTheory.Shin

end
