import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def wordMul (w z : List (ℝ → GAd σ J) →₀ ℂ) : List (ℝ → GAd σ J) →₀ ℂ :=
  w.sum fun l a => z.sum fun l' b => Finsupp.single (l ++ l') (a * b)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Conclude with `Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)`.
-/
theorem dop_add_comb (z z' : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) : dop (z + z') f = dop z f + dop z' f := by
  funext g
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [dop, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finsupp.sum_smul_index (fun _ => zero_mul _), Finsupp.mul_sum]`. Simplify using `only [smul_eq_mul, mul_assoc]`.
-/
theorem dop_smul_comb (c : ℂ) (z : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) : dop (c • z) f = c • dop z f := by
  funext g
  simp only [dop, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _), Finsupp.mul_sum]
  simp only [smul_eq_mul, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[dop]`.
-/
theorem dop_zero_comb (f : GAd σ J → ℂ) : dop (0 : List (ℝ → GAd σ J) →₀ ℂ) f = 0 := by
  funext g
  simp [dop]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[dop, Finsupp.sum_single_index]`.
-/
theorem dop_single (l : List (ℝ → GAd σ J)) (c : ℂ) (f : GAd σ J → ℂ) :
    dop (Finsupp.single l c) f = fun g => c * l.foldr lineDer f g := by
  funext g
  simp [dop, Finsupp.sum_single_index]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [dop_zero_comb]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dop_add_comb, ih]`.
-/
theorem dop_sum_comb {ι : Type} (s : Finset ι) (z : ι → List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) :
    dop (∑ i ∈ s, z i) f = ∑ i ∈ s, dop (z i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dop_zero_comb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dop_add_comb, ih]

/- English proof (translation)
Take `⟨l, hl, h1⟩` from `Finset.mem_biUnion.1 (Finsupp.support_sum hm)`. Take `⟨l', hl', h2⟩` from `Finset.mem_biUnion.1 (Finsupp.support_sum h1)`. Conclude with `⟨l, hl, l', hl', Finset.mem_singleton.1 (Finsupp.support_single_subset h2)⟩`.
-/
theorem mem_support_wordMul {w z : List (ℝ → GAd σ J) →₀ ℂ} {m : List (ℝ → GAd σ J)} (hm : m ∈ (wordMul w z).support) :
    ∃ l ∈ w.support, ∃ l' ∈ z.support, m = l ++ l' := by
  classical
  obtain ⟨l, hl, h1⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hm)
  obtain ⟨l', hl', h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum h1)
  exact ⟨l, hl, l', hl', Finset.mem_singleton.1 (Finsupp.support_single_subset h2)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp, fun f _ a _ g => by simp [dop_zero_comb]⟩`.
-/
theorem IsCentral.zero : IsCentral σ J (0 : List (ℝ → GAd σ J) →₀ ℂ) :=
  ⟨by simp, fun f _ a _ g => by simp [dop_zero_comb]⟩

/- English proof (translation)
Use `⟨fun l hl γ hγ => ?_, fun f hf a ha g => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl exacts [h.1 l hl γ hγ, h'.1 l hl γ hγ]` into its components or cases. Simplify using `only [dop_add_comb, Pi.add_apply, h.2 f hf a ha g, h'.2 f hf a ha g]`.
-/
theorem IsCentral.add {z z' : List (ℝ → GAd σ J) →₀ ℂ} (h : IsCentral σ J z) (h' : IsCentral σ J z') :
    IsCentral σ J (z + z') := by
  classical
  refine ⟨fun l hl γ hγ => ?_, fun f hf a ha g => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl
    exacts [h.1 l hl γ hγ, h'.1 l hl γ hγ]
  · simp only [dop_add_comb, Pi.add_apply, h.2 f hf a ha g, h'.2 f hf a ha g]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun l hl γ hγ => h.1 l (Finsupp.support_smul hl) γ hγ, fun f hf a ha g => by simp only [dop_smul_comb, Pi.smul_apply, h.2 f hf a ha g]⟩`.
-/
theorem IsCentral.smul {z : List (ℝ → GAd σ J) →₀ ℂ} (h : IsCentral σ J z) (c : ℂ) : IsCentral σ J (c • z) :=
  ⟨fun l hl γ hγ => h.1 l (Finsupp.support_smul hl) γ hγ, fun f hf a ha g => by
    simp only [dop_smul_comb, Pi.smul_apply, h.2 f hf a ha g]⟩

end GlobalTheory.UAut

end
