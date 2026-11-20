import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Establish `hN : ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ≠ 0`. Conclude with `(Ideal.absNorm_eq_zero_iff.not.mpr hp)` after adjusting the coercions. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hZ.1.sub (DifferentiableOn.mul (fun s _ => ?_) hZ'.1)` and prove the remaining obligations. Conclude with `((differentiableAt_id.neg).const_cpow (Or.inl hN)).differentiableWithinAt`.

Introduce `s hs`. Use `set S : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I} with hSdef`. Use `set A : Set (Ideal (𝓞 F)) := {I | CoprimeTo F (𝔪 * 𝔭) I} with hAdef`. Use `set B : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I ∧ ¬ CoprimeTo F (𝔪 * 𝔭) I} with hBdef`. Set `g : ClassGroup (𝓞 F) → Ideal (𝓞 F) → ℂ` to `fun D I => (wideInd D I : ℂ) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)`.

Establish `h1 : HasSum (S.indicator (g C)) (Z s)` using `(hasSum_subtype_iff_indicator (s := S)).mp (hZ.2 s hs)`. Establish `h2 : HasSum (S.indicator (g (C * (cls 𝔭)⁻¹))) (Z' s)` using `(hasSum_subtype_iff_indicator (s := S)).mp (hZ'.2 s hs)`. Establish `hAS : ∀ I, CoprimeTo F (𝔪 * 𝔭) I → CoprimeTo F 𝔪 I` using `fun I h => ⟨h.1, eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_left _))⟩`. Establish `hsplit : S.indicator (g C) = A.indicator (g C) + B.indicator (g C)`. Use function extensionality and compare the values at `I`.

Simplify using `only [Pi.add_apply, Set.indicator, hSdef, hAdef, hBdef, Set.mem_setOf_eq]`. Distinguish the cases in `hA : CoprimeTo F (𝔪 * 𝔭) I`. Simplify using `[hA, hAS I hA]`. Apply the tactic sequence `by_cases hS : CoprimeTo F 𝔪 I <;> simp [hA, hS]`. Establish `hmulS : ∀ J, CoprimeTo F 𝔪 J → 𝔭 * J ∈ B`.

Introduce `J hJ`. Use `⟨⟨mul_ne_zero hp hJ.1, ?_⟩, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rwa [sup_comm]), sup_comm]; exact hJ.2`. Establish `: 𝔭 * J ⊔ 𝔭 = 𝔭` using `sup_eq_right.mpr Ideal.mul_le_left`. Establish `htop : 𝔭 * J ⊔ 𝔭 = ⊤` using `eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_right _))`.

Conclude with `hmax.ne_top (this.symm.trans htop)`. Establish `hnot : ∀ J, ¬ CoprimeTo F 𝔪 J → 𝔭 * J ∉ B`. Introduce `J hJ hB`. Apply `hJ` to reduce the goal to its premises. Use `⟨fun h0 => hB.1.1 (by simp [h0]), eq_top_iff.mpr (hB.1.2.symm.le.trans (sup_le_sup_right Ideal.mul_le_right _))⟩` and prove the remaining obligations.

Establish `hB_range : ∀ I ∈ B, ∃ J, 𝔭 * J = I`. Introduce `I hI`. Establish `hItop : I ⊔ 𝔭 ≠ ⊤`. Introduce `h`. Apply `hI.2` to reduce the goal to its premises.

Use `⟨hI.1.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.sup_mul_eq_of_coprime_right h]`. Conclude with `hI.1.2`. Establish `hle : I ≤ 𝔭` using `le_sup_left.trans (hmax.eq_of_le hItop le_sup_right).ge`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.mpr hle`.

Conclude with `⟨J, hJ.symm⟩`. Establish `hinj : Function.Injective (fun J : Ideal (𝓞 F) => 𝔭 * J)` using `fun J J' h => mul_left_cancel₀ hp h`. Establish `hcomp : (B.indicator (g C)) ∘ (fun J => 𝔭 * J) = fun J => ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * S.indicator (g (C * (cls 𝔭)⁻¹)) J`. Use function extensionality and compare the values at `J`. Simplify using `only [Function.comp_apply]`.

Distinguish the cases in `hJ : CoprimeTo F 𝔪 J`. Rewrite using `[Set.indicator_of_mem (hmulS J hJ), Set.indicator_of_mem (show J ∈ S from hJ)]`. Simplify using `only [g, wideInd]`. Rewrite using `[cls_mul hp hJ.1, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]`. Establish `: (cls 𝔭 * cls J = C) ↔ (cls J = C * (cls 𝔭)⁻¹)`.

Rewrite using `[eq_mul_inv_iff_mul_eq, mul_comm]`. Distinguish the cases in `hc : cls J = C * (cls 𝔭)⁻¹`. Simplify using `[hc, this.mpr hc]`. Simplify using `[hc, mt this.mp hc]`. Rewrite using `[Set.indicator_of_notMem (hnot J hJ), Set.indicator_of_notMem (show J ∉ S from hJ), mul_zero]`.

Establish `h3 : HasSum (B.indicator (g C)) (((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s)`. Rewrite using `[← hinj.hasSum_iff (fun I hI => ?_), hcomp]`. Conclude with `h2.mul_left _`. Assume the negation of the conclusion as `hne`. Take `⟨J, rfl⟩` from `hB_range I (Set.mem_of_indicator_ne_zero hne)`.

Conclude with `hI ⟨J, rfl⟩`. Establish `h4 : HasSum (A.indicator (g C)) (Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s)`. Use `h1.sub h3` as an intermediate fact. Rewrite `this` using `[hsplit]`. Establish `e : (fun b => (A.indicator (g C) + B.indicator (g C)) b - B.indicator (g C) b) = A.indicator (g C)`.

Use function extensionality and compare the values at `I`. Simplify using the standard rewrite rules. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Conclude with `(hasSum_subtype_iff_indicator (s := A)).mpr h4`.
-/
theorem isRayL_mul_prime_wideInd {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)) (hmax : 𝔭.IsMaximal) (hp : 𝔭 ≠ ⊥)
    (hpm : 𝔭 ⊔ 𝔪 = ⊤) (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ) (hZ : IsRayL 𝔪 (wideInd C) Z)
    (hZ' : IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z') :
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
  have hN : ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hp)
  refine ⟨?_, ?_⟩
  · refine hZ.1.sub (DifferentiableOn.mul (fun s _ => ?_) hZ'.1)
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hN)).differentiableWithinAt
  intro s hs
  classical
  set S : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I} with hSdef
  set A : Set (Ideal (𝓞 F)) := {I | CoprimeTo F (𝔪 * 𝔭) I} with hAdef
  set B : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I ∧ ¬ CoprimeTo F (𝔪 * 𝔭) I} with hBdef
  let g : ClassGroup (𝓞 F) → Ideal (𝓞 F) → ℂ := fun D I => (wideInd D I : ℂ) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)
  have h1 : HasSum (S.indicator (g C)) (Z s) := (hasSum_subtype_iff_indicator (s := S)).mp (hZ.2 s hs)
  have h2 : HasSum (S.indicator (g (C * (cls 𝔭)⁻¹))) (Z' s) :=
    (hasSum_subtype_iff_indicator (s := S)).mp (hZ'.2 s hs)
  have hAS : ∀ I, CoprimeTo F (𝔪 * 𝔭) I → CoprimeTo F 𝔪 I := fun I h =>
    ⟨h.1, eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_left _))⟩
  have hsplit : S.indicator (g C) = A.indicator (g C) + B.indicator (g C) := by
    funext I
    simp only [Pi.add_apply, Set.indicator, hSdef, hAdef, hBdef, Set.mem_setOf_eq]
    by_cases hA : CoprimeTo F (𝔪 * 𝔭) I
    · simp [hA, hAS I hA]
    · by_cases hS : CoprimeTo F 𝔪 I <;> simp [hA, hS]

  have hmulS : ∀ J, CoprimeTo F 𝔪 J → 𝔭 * J ∈ B := by
    intro J hJ
    refine ⟨⟨mul_ne_zero hp hJ.1, ?_⟩, fun h => ?_⟩
    · rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rwa [sup_comm]), sup_comm]; exact hJ.2
    · have : 𝔭 * J ⊔ 𝔭 = 𝔭 := sup_eq_right.mpr Ideal.mul_le_left
      have htop : 𝔭 * J ⊔ 𝔭 = ⊤ := eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_right _))
      exact hmax.ne_top (this.symm.trans htop)
  have hnot : ∀ J, ¬ CoprimeTo F 𝔪 J → 𝔭 * J ∉ B := by
    intro J hJ hB
    apply hJ
    refine ⟨fun h0 => hB.1.1 (by simp [h0]), eq_top_iff.mpr (hB.1.2.symm.le.trans (sup_le_sup_right Ideal.mul_le_right _))⟩
  have hB_range : ∀ I ∈ B, ∃ J, 𝔭 * J = I := by
    intro I hI
    have hItop : I ⊔ 𝔭 ≠ ⊤ := by
      intro h
      apply hI.2
      refine ⟨hI.1.1, ?_⟩
      rw [Ideal.sup_mul_eq_of_coprime_right h]; exact hI.1.2
    have hle : I ≤ 𝔭 := le_sup_left.trans (hmax.eq_of_le hItop le_sup_right).ge
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    exact ⟨J, hJ.symm⟩
  have hinj : Function.Injective (fun J : Ideal (𝓞 F) => 𝔭 * J) := fun J J' h => mul_left_cancel₀ hp h
  have hcomp : (B.indicator (g C)) ∘ (fun J => 𝔭 * J) =
      fun J => ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * S.indicator (g (C * (cls 𝔭)⁻¹)) J := by
    funext J
    simp only [Function.comp_apply]
    by_cases hJ : CoprimeTo F 𝔪 J
    · rw [Set.indicator_of_mem (hmulS J hJ), Set.indicator_of_mem (show J ∈ S from hJ)]
      simp only [g, wideInd]
      rw [cls_mul hp hJ.1, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      have : (cls 𝔭 * cls J = C) ↔ (cls J = C * (cls 𝔭)⁻¹) := by
        rw [eq_mul_inv_iff_mul_eq, mul_comm]
      by_cases hc : cls J = C * (cls 𝔭)⁻¹
      · simp [hc, this.mpr hc]
      · simp [hc, mt this.mp hc]
    · rw [Set.indicator_of_notMem (hnot J hJ), Set.indicator_of_notMem (show J ∉ S from hJ), mul_zero]
  have h3 : HasSum (B.indicator (g C)) (((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
    rw [← hinj.hasSum_iff (fun I hI => ?_), hcomp]
    · exact h2.mul_left _
    · by_contra hne
      obtain ⟨J, rfl⟩ := hB_range I (Set.mem_of_indicator_ne_zero hne)
      exact hI ⟨J, rfl⟩
  have h4 : HasSum (A.indicator (g C)) (Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
    have := h1.sub h3
    rw [hsplit] at this
    have e : (fun b => (A.indicator (g C) + B.indicator (g C)) b - B.indicator (g C) b) = A.indicator (g C) := by
      funext I; simp
    rwa [e] at this
  exact (hasSum_subtype_iff_indicator (s := A)).mpr h4

end GlobalTheory
