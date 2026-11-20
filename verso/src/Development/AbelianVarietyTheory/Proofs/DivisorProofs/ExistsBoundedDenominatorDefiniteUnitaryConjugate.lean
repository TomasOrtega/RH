import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdeles
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Use `choose N hN h using fun k => GlobalTheory.AdeleDenom.exists_nat_mul_integral E (a k)`. Use `⟨∏ k, N k, Finset.prod_pos fun k _ => hN k, fun k w => ?_⟩` and prove the remaining obligations. Establish `h' : (N k : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E`. Use `h k w` as an intermediate fact. Rewrite `this` using `[show ((N k : Af E) * a k) w = pLoc E w ((N k : Af E) * a k) from rfl, map_mul, map_natCast]`. Then use the resulting hypothesis.

Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Nat.cast_mul, mul_assoc]`. Conclude with `mul_mem (natCast_mem _ _) h'`.
-/
theorem exists_nat_denom {ι : Type} [Fintype ι] (a : ι → Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ (k : ι) (w : Pl E),
      (d : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
  choose N hN h using fun k => GlobalTheory.AdeleDenom.exists_nat_mul_integral E (a k)
  refine ⟨∏ k, N k, Finset.prod_pos fun k _ => hN k, fun k w => ?_⟩
  have h' : (N k : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
    have := h k w
    rwa [show ((N k : Af E) * a k) w = pLoc E w ((N k : Af E) * a k) from rfl, map_mul, map_natCast] at this
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) h'

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cLoc_val (k : finU E n) (w : Pl E) (i j : Fin n) :
    (cLoc w (k : UA E n)).val i j = pLoc E w ((FinPart.pU k).val i j) := rfl

/- English proof (translation)
Introduce `E _ _ _ n S hS x`. Take `⟨D₁, hD₁, h₁⟩` from `exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x).val k.1 k.2`. Take `⟨D₂, hD₂, h₂⟩` from `exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x⁻¹).val k.1 k.2`. Establish `key : ∀ (h : finU E n) (w : Pl E), cLoc w ((x⁻¹ * h * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL w n → ∀ i j, ((D₁ * D₂ : ℕ) : w.adicCompletion E) * (cLoc w (h : UA E n)).val i j ∈ w.adicCompletionIntegers E`. Introduce `h w hk i j`.

Establish `e : (h : UA E n) = (x : UA E n) * ((x⁻¹ * h * x : finU E n) : UA E n) * ((x⁻¹ : finU E n) : UA E n)`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`. Rewrite using `[e, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.mul_sum]`. Use `sum_mem fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Use `sum_mem fun a _ => ?_` and prove the remaining obligations. Establish `e1 : (D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a ∈ w.adicCompletionIntegers E`. Rewrite using `[cLoc_val]`. Conclude with `h₁ (i, a) w`.

Establish `e2 : (D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU E n) : UA E n)).val b j ∈ w.adicCompletionIntegers E`. Rewrite using `[cLoc_val]`. Conclude with `h₂ (b, j) w`. Establish `e3` using `GlobalTheory.BCT.LocCpt.entry_mem_of_mem_KGL hk a b`. Establish `e4 : ((D₁ * D₂ : ℕ) : w.adicCompletion E) * ((cLoc w (x : UA E n)).val i a * (cLoc w ((x⁻¹ * h * x : finU E n) : UA E n)).val a b * (cLoc w ((x⁻¹ : finU E n) : UA E n)).val b j) = ((D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a) * (cLoc w ((x⁻¹ * h * x : finU E n) : UA …` using `by push_cast; ring`.

Rewrite using `[e4]`. Conclude with `mul_mem (mul_mem e1 e3) e2`. Use `⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, fun g hg w i j => ?_⟩` and prove the remaining obligations. Break down `GlobalTheory.BCT.LocCpt.mem_or_conj_mem hS w with hw | hw` into its components or cases. Conclude with `key g w (hg w hw) i j`.

Establish `hinv : cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((x⁻¹ * g⁻¹ * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL (conjSrc (GlobalTheory.SplitPts.conjE E) w) n`. Establish `: (x⁻¹ * g⁻¹ * x : finU E n) = (x⁻¹ * g * x)⁻¹` using `by group`. Rewrite using `[this, Subgroup.coe_inv, map_inv]`. Conclude with `(GlobalTheory.LFun.KGL _ n).inv_mem (hg _ hw)`. Establish `h1` using `key g⁻¹ _ hinv j i`.

Establish `e2 : (cLoc w (g : UA E n)).val i j = conjLoc (GlobalTheory.SplitPts.conjE E) w ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((g⁻¹ : finU E n) : UA E n)).val j i)`. Rewrite using `[GlobalTheory.BCT.LocCpt.cLoc_eq_invT]`. Use `show ((GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) (g : UA E n)))⁻¹).val j i = _`. Rewrite using `[← map_inv, ← map_inv, Subgroup.coe_inv]`. Both sides reduce to the same expression.

Rewrite using `[e2, ← map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) (D₁ * D₂), ← map_mul, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1`.
-/
theorem exists_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ x : finU E n, ∃ d : ℕ, 0 < d ∧ ∀ g : finU E n, (∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL w n) → ∀ (w : Pl E) (i j : Fin n), (d : w.adicCompletion E) * (cLoc w (g : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ _ n S hS x
  obtain ⟨D₁, hD₁, h₁⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x).val k.1 k.2
  obtain ⟨D₂, hD₂, h₂⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x⁻¹).val k.1 k.2
  have key : ∀ (h : finU E n) (w : Pl E), cLoc w ((x⁻¹ * h * x : finU E n) : UA E n) ∈ GlobalTheory.LFun.KGL w n →
      ∀ i j, ((D₁ * D₂ : ℕ) : w.adicCompletion E) * (cLoc w (h : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
    intro h w hk i j
    have e : (h : UA E n) = (x : UA E n) * ((x⁻¹ * h * x : finU E n) : UA E n) * ((x⁻¹ : finU E n) : UA E n) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e1 : (D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₁ (i, a) w
    have e2 : (D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU E n) : UA E n)).val b j ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₂ (b, j) w
    have e3 := GlobalTheory.BCT.LocCpt.entry_mem_of_mem_KGL hk a b
    have e4 : ((D₁ * D₂ : ℕ) : w.adicCompletion E) * ((cLoc w (x : UA E n)).val i a *
        (cLoc w ((x⁻¹ * h * x : finU E n) : UA E n)).val a b * (cLoc w ((x⁻¹ : finU E n) : UA E n)).val b j) =
        ((D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a) * (cLoc w ((x⁻¹ * h * x : finU E n) : UA E n)).val a b *
        ((D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU E n) : UA E n)).val b j) := by
      push_cast; ring
    rw [e4]
    exact mul_mem (mul_mem e1 e3) e2
  refine ⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, fun g hg w i j => ?_⟩
  rcases GlobalTheory.BCT.LocCpt.mem_or_conj_mem hS w with hw | hw
  · exact key g w (hg w hw) i j
  · have hinv : cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((x⁻¹ * g⁻¹ * x : finU E n) : UA E n) ∈
        GlobalTheory.LFun.KGL (conjSrc (GlobalTheory.SplitPts.conjE E) w) n := by
      have : (x⁻¹ * g⁻¹ * x : finU E n) = (x⁻¹ * g * x)⁻¹ := by group
      rw [this, Subgroup.coe_inv, map_inv]
      exact (GlobalTheory.LFun.KGL _ n).inv_mem (hg _ hw)
    have h1 := key g⁻¹ _ hinv j i
    have e2 : (cLoc w (g : UA E n)).val i j = conjLoc (GlobalTheory.SplitPts.conjE E) w
        ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((g⁻¹ : finU E n) : UA E n)).val j i) := by
      rw [GlobalTheory.BCT.LocCpt.cLoc_eq_invT]
      show ((GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
        (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) (g : UA E n)))⁻¹).val j i = _
      rw [← map_inv, ← map_inv, Subgroup.coe_inv]
      rfl
    rw [e2, ← map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) (D₁ * D₂), ← map_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1

end GlobalTheory.BCT.StabDenom
