import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityConjugateFormLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionModStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `g E N _ d w f hE hZ hf`. Establish `hN : 0 < N` using `Nat.pos_of_ne_zero (NeZero.ne N)`. Use `set F : ℍ → ℂ := fun τ => DD τ ^ w * f τ with hFdef`. Establish `hsl : ∀ (h : ℍ → ℂ) (γ : SL(2, ℤ)), ((fun τ => DD τ ^ w * h τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * h (γ • τ)` using `fun h γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w h γ`. Establish `hev : Even (12 * w)` using `⟨6 * w, by ring⟩`.

Establish `hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∣[((12 * w : ℕ) : ℤ)] γ = F`. Introduce `γ hγ`. Rewrite using `[hFdef, hsl]`. Use function extensionality and compare the values at `τ`. Rewrite using `[hf.1 γ hγ τ]`.

Establish `hq : ∀ γ : SL(2, ℤ), ∃ a, HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) a`. Introduce `γ`. Take `⟨a, ha, -⟩` from `hf.2 γ`. Conclude with `⟨a, by rw [hFdef, hsl]; exact ha⟩`. Take `⟨F', hF'inv, hF'c⟩` from `GlobalTheory.T.shimuraReciprocity_conjugate_form_level g N d (12 * w) F hZ hev hinv hq`.

Use `⟨fun τ => F' τ / DD τ ^ w, ?_, ?_⟩` and prove the remaining obligations. Establish `hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F'`. Use function extensionality and compare the values at `τ`. Use `pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Establish `key : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * (F' (γ • τ) / DD (γ • τ) ^ w)) = F' ∣[((12 * w : ℕ) : ℤ)] γ`. Introduce `γ`. Use `hsl (fun τ => F' τ / DD τ ^ w) γ` as an intermediate fact. Rewrite `this` using `[hF'eq]`. Conclude with `this.symm`.

Use `⟨fun γ hγ τ => ?_, fun γ' => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (key γ) τ`. Rewrite `h1` using `[hF'inv γ hγ]`. Establish `h2` using `congrFun hF'eq τ`. Establish `hne` using `pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)`.

Conclude with `mul_left_cancel₀ hne (h1.trans h2.symm)`. Take `⟨γ, hγ⟩` from `(GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N d).2 γ'`. Take `⟨a, ha, ha'⟩` from `hF'c γ γ' hγ`. Take `⟨b, hb, hbE⟩` from `hf.2 γ`. Establish `hb' : HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) b` using `by rw [hFdef, hsl]; exact hb`.

Establish `hab : a = b` using `GlobalTheory.QFam.hasQ_unique_both.1 N _ a b hN ha hb'`. Use `⟨fun n => g (a n), ?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[key γ']`. Conclude with `ha'`. Rewrite using `[hab]`.

Conclude with `hE _ (hbE n)`. Introduce `γ γ' hγ`. Establish `hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F'`. Use function extensionality and compare the values at `τ`. Use `pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish `key : (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w)) = F' ∣[((12 * w : ℕ) : ℤ)] γ'`. Use `hsl (fun τ => F' τ / DD τ ^ w) γ'` as an intermediate fact. Rewrite `this` using `[hF'eq]`. Conclude with `this.symm`.

Establish `kf : (fun τ => DD τ ^ w * f (γ • τ)) = F ∣[((12 * w : ℕ) : ℤ)] γ` using `by rw [hFdef, hsl]`. Use `show QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w))`. Rewrite using `[key, kf]`. Conclude with `hF'c γ γ' hγ`.
-/
theorem lv_galois_conj : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ),
    (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d →
        QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  intro g E N _ d w f hE hZ hf
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set F : ℍ → ℂ := fun τ => DD τ ^ w * f τ with hFdef
  have hsl : ∀ (h : ℍ → ℂ) (γ : SL(2, ℤ)),
      ((fun τ => DD τ ^ w * h τ) ∣[((12 * w : ℕ) : ℤ)] γ) = fun τ => DD τ ^ w * h (γ • τ) :=
    fun h γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w h γ
  have hev : Even (12 * w) := ⟨6 * w, by ring⟩
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∣[((12 * w : ℕ) : ℤ)] γ = F := by
    intro γ hγ
    rw [hFdef, hsl]
    funext τ
    rw [hf.1 γ hγ τ]
  have hq : ∀ γ : SL(2, ℤ), ∃ a, HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) a := by
    intro γ
    obtain ⟨a, ha, -⟩ := hf.2 γ
    exact ⟨a, by rw [hFdef, hsl]; exact ha⟩
  obtain ⟨F', hF'inv, hF'c⟩ := GlobalTheory.T.shimuraReciprocity_conjugate_form_level g N d (12 * w) F hZ hev hinv hq
  refine ⟨fun τ => F' τ / DD τ ^ w, ?_, ?_⟩
  · have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * (F' (γ • τ) / DD (γ • τ) ^ w)) =
        F' ∣[((12 * w : ℕ) : ℤ)] γ := by
      intro γ
      have := hsl (fun τ => F' τ / DD τ ^ w) γ
      rw [hF'eq] at this
      exact this.symm
    refine ⟨fun γ hγ τ => ?_, fun γ' => ?_⟩
    · have h1 := congrFun (key γ) τ
      rw [hF'inv γ hγ] at h1
      have h2 := congrFun hF'eq τ
      have hne := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      exact mul_left_cancel₀ hne (h1.trans h2.symm)
    · obtain ⟨γ, hγ⟩ := (GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N d).2 γ'
      obtain ⟨a, ha, ha'⟩ := hF'c γ γ' hγ
      obtain ⟨b, hb, hbE⟩ := hf.2 γ
      have hb' : HasQ N (F ∣[((12 * w : ℕ) : ℤ)] γ) b := by rw [hFdef, hsl]; exact hb
      have hab : a = b := GlobalTheory.QFam.hasQ_unique_both.1 N _ a b hN ha hb'
      refine ⟨fun n => g (a n), ?_, fun n => ?_⟩
      · rw [key γ']; exact ha'
      · rw [hab]; exact hE _ (hbE n)
  · intro γ γ' hγ
    have hF'eq : (fun τ => DD τ ^ w * (F' τ / DD τ ^ w)) = F' := by
      funext τ
      have := pow_ne_zero w (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
      field_simp
    have key : (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w)) = F' ∣[((12 * w : ℕ) : ℤ)] γ' := by
      have := hsl (fun τ => F' τ / DD τ ^ w) γ'
      rw [hF'eq] at this
      exact this.symm
    have kf : (fun τ => DD τ ^ w * f (γ • τ)) = F ∣[((12 * w : ℕ) : ℤ)] γ := by rw [hFdef, hsl]
    show QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * (F' (γ' • τ) / DD (γ' • τ) ^ w))
    rw [key, kf]
    exact hF'c γ γ' hγ

end GlobalTheory.FN
