import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

/- English proof (translation)
Introduce `F _ _ θ r hr S T G g a hST hT δ hδ t`. Take `⟨h1, h2⟩` from `hr δ hδ`. Establish `c1 : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = (a : AF F).1 * (θ δ * algebraMap F (Ainf F) (t : F))`. Establish `: ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = algebraMap F (Ainf F) (t : F) * ((a : AF F).1 * (r δ : AF F).1)` using `rfl`. Rewrite using `[this, h1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `c2 : ∀ v, ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * algebraMap F (Fv F v) (t : F)`. Introduce `v`. Establish `: ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = algebraMap F (Fv F v) (t : F) * ((a : AF F).2 v * (r δ : AF F).2 v)` using `rfl`. Rewrite using `[this, h2]`.

Establish `h3 : ((1 : FiniteAdeleRing (𝓞 F) F)) v = 1` using `rfl`. Rewrite using `[h3, mul_one, mul_comm]`. Establish `inv : ∀ v, (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1`. Introduce `v`. Establish `: ((a * a⁻¹ : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v` using `rfl`.

Rewrite using `[← this]`. Simplify using the standard rewrite rules. Establish `key : ∀ v, v ∉ T → ((a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F ↔ algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F)`. Introduce `v hv`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h'` using `mul_mem (hT v hv).2 h`. Establish `e : ((a⁻¹ : (AF F)ˣ) : AF F).2 v * ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) = algebraMap F (Fv F v) (t : F)`. Rewrite using `[← mul_assoc, mul_comm (((a⁻¹ : (AF F)ˣ) : AF F).2 v), inv, one_mul]`. Rewrite `h'` using `[e]`. Then use the resulting hypothesis.

Conclude with `fun h => mul_mem (hT v hv).1 h`. Rewrite using `[GlobalTheory.T.pure_adelic_function_formula F S G g (pr t * (a * r δ))]`. Simplify using `only [c1, c2]`. Distinguish the cases in `ht : ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F`. Rewrite using `[if_pos ht]`.

Distinguish the cases in `h : ∀ v, v ∉ S → (a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F`. Rewrite using `[if_pos h]`. Establish `hp : ∏ v ∈ S, g v ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) = ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F))`. Rewrite using `[← Finset.prod_subset hST]`. Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations.

Simplify using `[psiA, hv]`. Introduce `v _ hv`. Simplify using `[psiA, hv, h v hv]`. Rewrite using `[hp]`. Both sides reduce to the same expression.

Rewrite `h` using `[if_neg h] push_neg`. Take `⟨v, hvS, hv⟩` from `h`. Establish `hvT : v ∈ T`. Assume the negation of the conclusion as `hvT`. Conclude with `hv ((key v hvT).2 (ht v hvT))`.

Establish `hz : ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) = 0` using `Finset.prod_eq_zero hvT (by simp [psiA, hvS, hv])`. Rewrite using `[hz]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg ht, if_neg]`. Introduce `h`.

Conclude with `ht fun v hv => (key v hv).1 (h v fun hs => hv (hST hs))`.
-/
theorem pure_term : ∀ (F : Type) [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ (δ : ℝ), 0 < δ → ∀ t : Fˣ,
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * (a * r δ)) =
      if ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (phiA G a (fun _ => θ δ * algebraMap F (Ainf F) (t : F)) *
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F))) else 0 := by
  intro F _ _ θ r hr S T G g a hST hT δ hδ t
  obtain ⟨h1, h2⟩ := hr δ hδ
  have c1 : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = (a : AF F).1 * (θ δ * algebraMap F (Ainf F) (t : F)) := by
    have : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = algebraMap F (Ainf F) (t : F) * ((a : AF F).1 * (r δ : AF F).1) := rfl
    rw [this, h1]; ring
  have c2 : ∀ v, ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * algebraMap F (Fv F v) (t : F) := by
    intro v
    have : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = algebraMap F (Fv F v) (t : F) * ((a : AF F).2 v * (r δ : AF F).2 v) := rfl
    rw [this, h2]
    have h3 : ((1 : FiniteAdeleRing (𝓞 F) F)) v = 1 := rfl
    rw [h3, mul_one, mul_comm]
  have inv : ∀ v, (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    intro v
    have : ((a * a⁻¹ : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := rfl
    rw [← this]; simp
  have key : ∀ v, v ∉ T → ((a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F ↔
      algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F) := by
    intro v hv
    constructor
    · intro h
      have h' := mul_mem (hT v hv).2 h
      have e : ((a⁻¹ : (AF F)ˣ) : AF F).2 v * ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) =
          algebraMap F (Fv F v) (t : F) := by
        rw [← mul_assoc, mul_comm (((a⁻¹ : (AF F)ˣ) : AF F).2 v), inv, one_mul]
      rwa [e] at h'
    · exact fun h => mul_mem (hT v hv).1 h
  rw [GlobalTheory.T.pure_adelic_function_formula F S G g (pr t * (a * r δ))]
  simp only [c1, c2]
  by_cases ht : ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F
  · rw [if_pos ht]
    by_cases h : ∀ v, v ∉ S → (a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F
    · rw [if_pos h]
      have hp : ∏ v ∈ S, g v ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) =
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) := by
        rw [← Finset.prod_subset hST]
        · refine Finset.prod_congr rfl fun v hv => ?_
          simp [psiA, hv]
        · intro v _ hv
          simp [psiA, hv, h v hv]
      rw [hp]
      rfl
    · rw [if_neg h]
      push_neg at h
      obtain ⟨v, hvS, hv⟩ := h
      have hvT : v ∈ T := by
        by_contra hvT
        exact hv ((key v hvT).2 (ht v hvT))
      have hz : ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) = 0 :=
        Finset.prod_eq_zero hvT (by simp [psiA, hvS, hv])
      rw [hz]
      simp
  · rw [if_neg ht, if_neg]
    intro h
    exact ht fun v hv => (key v hv).1 (h v fun hs => hv (hST hs))

end GlobalTheory.CompanionTheory.BasePsi
