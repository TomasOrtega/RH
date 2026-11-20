import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDetVectorMultiplierShiftPlus
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelNegTAndQdet
open Formalism.REAL Finset

namespace GlobalTheory

open Finset in

/- English proof (translation)
Introduce `V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w`. Take `⟨hF, hqF⟩` from `_root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE`. Take `⟨hF', hqF'⟩` from `_root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ W) n E' hE'`. Establish `hιF : ∀ (a b : Fin n) (w : W), ι ((-E' b a) w) = (-E b a) (ι w)`. Introduce `a b w`.

Simplify using `only [LinearMap.neg_apply, map_neg, hι]`. Establish `hνF : Function.Injective (fun s : Fin n => (1 : ℂ) - n - ν s)`. Introduce `s t h`. Apply `hν` to reduce the goal to its premises. Establish `h' : (1 - n - ν s : ℂ) = 1 - n - ν t` using `h`.

Take the linear combination `-h'`. Establish `hqE' : ∀ (u : ℂ) (w : W), (_root_.Formalism.REAL.qdet (fun a b => -E' b a) u) w = (∏ s, (u + (1 - n - ν s))) • w`. Introduce `u w`. Rewrite using `[hqF', LinearMap.smul_apply, hq, smul_smul]`. Use `congr 1`.

Rewrite using `[← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hxF : ∀ (a b k : Fin n), (-E b a) * x k = x k * (-E b a) + if b = k then x a else 0`. Introduce `a b k`.

Rewrite using `[neg_mul, mul_neg, hx b a k]`. Normalize the expressions using the abelian group laws. Take `⟨v, hv1, hv2⟩` from `_root_.GlobalTheory.qdet_vector_multiplier_shift_plus V W n (fun a b => -E b a) (fun a b => -E' b a) ι x (fun s => 1 - n - ν s) hF hF' hιF hνF hqE' hxF j w`. Use `⟨v, hv1, fun s u => ?_⟩` and prove the remaining obligations. Establish `h` using `hv2 s ((n : ℂ) - 1 - u)`.

Rewrite `h` using `[hqF, show (n : ℂ) - 1 - ((n : ℂ) - 1 - u) = u by ring, LinearMap.smul_apply]`. Establish `h2` using `congrArg (((-1 : ℂ) ^ n) • ·) h`. Simplify using `only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul] at h2`. Rewrite using `[h2]`. Use `congr 1`.

Rewrite using `[← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem _root_.GlobalTheory.covector_multiplier_shift : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), _root_.Formalism.REAL.GlRel E → _root_.Formalism.REAL.GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), _root_.Formalism.REAL.qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b - if a = j then x b else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), _root_.Formalism.REAL.qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t - if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  obtain ⟨hF, hqF⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  obtain ⟨hF', hqF'⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ W) n E' hE'
  have hιF : ∀ (a b : Fin n) (w : W), ι ((-E' b a) w) = (-E b a) (ι w) := by
    intro a b w
    simp only [LinearMap.neg_apply, map_neg, hι]
  have hνF : Function.Injective (fun s : Fin n => (1 : ℂ) - n - ν s) := by
    intro s t h
    apply hν
    have h' : (1 - n - ν s : ℂ) = 1 - n - ν t := h
    linear_combination -h'
  have hqE' : ∀ (u : ℂ) (w : W), (_root_.Formalism.REAL.qdet (fun a b => -E' b a) u) w
      = (∏ s, (u + (1 - n - ν s))) • w := by
    intro u w
    rw [hqF', LinearMap.smul_apply, hq, smul_smul]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hxF : ∀ (a b k : Fin n), (-E b a) * x k = x k * (-E b a) + if b = k then x a else 0 := by
    intro a b k
    rw [neg_mul, mul_neg, hx b a k]
    abel
  obtain ⟨v, hv1, hv2⟩ := _root_.GlobalTheory.qdet_vector_multiplier_shift_plus V W n (fun a b => -E b a)
    (fun a b => -E' b a) ι x (fun s => 1 - n - ν s) hF hF' hιF hνF hqE' hxF j w
  · refine ⟨v, hv1, fun s u => ?_⟩
    have h := hv2 s ((n : ℂ) - 1 - u)
    rw [hqF, show (n : ℂ) - 1 - ((n : ℂ) - 1 - u) = u by ring, LinearMap.smul_apply] at h
    have h2 := congrArg (((-1 : ℂ) ^ n) • ·) h
    simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul] at h2
    rw [h2]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    split_ifs <;> ring

end GlobalTheory
