import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.InertExchange

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Take `⟨a, ha, hA1, hA2⟩` from `Formalism.L2.DIV.lc_sandwich A hA`. Take `⟨b, hb, hB1, hB2⟩` from `Formalism.L2.DIV.lc_sandwich B hB`. Use `⟨a * b, mul_ne_zero ha hb, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `hB2 _ (hA1 x hx)`.

Rewrite using `[mul_smul]`. Conclude with `hA2 _ (hB1 x hx)`.
-/
theorem patchAt_commens (A B : Submodule (𝓞 E) (Sp E n)) (hA : Submodule.IsLattice E A)
    (hB : Submodule.IsLattice E B) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ (∀ x ∈ A, d • x ∈ B) ∧ (∀ x ∈ B, d • x ∈ A) := by
  obtain ⟨a, ha, hA1, hA2⟩ := Formalism.L2.DIV.lc_sandwich A hA
  obtain ⟨b, hb, hB1, hB2⟩ := Formalism.L2.DIV.lc_sandwich B hB
  refine ⟨a * b, mul_ne_zero ha hb, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_comm, mul_smul]
    exact hB2 _ (hA1 x hx)
  · rw [mul_smul]
    exact hA2 _ (hB1 x hx)

/- English proof (translation)
Introduce `hA hB`. Take `⟨d, hd, hAB, hBA⟩` from `patchAt_commens A B hA hB`. Set `Λ : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) (Sp E n)` to `fun Q => localization₂ Q.asIdeal (if Q = P then A else B)`. Establish `hcl : ∀ Q, localization₂ Q.asIdeal (Λ Q) = Λ Q` using `fun Q => Formalism.L2.DIV.localized_localized Q _`. Establish `h1 : ∀ Q, ∀ x ∈ Λ Q, d • x ∈ localization₂ Q.asIdeal B`.

Introduce `Q x hx`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Simplify using `only [Λ, if_true] at hx`. Take `⟨s, hs, hsx⟩` from `hx`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `hAB _ hsx`. Simplify using `only [Λ, hQ, if_false] at hx`. Conclude with `Submodule.smul_mem _ d hx`.

Establish `h2 : ∀ Q, ∀ x ∈ B, d • x ∈ Λ Q`. Introduce `Q x hx`. Distinguish the cases in `hQ : Q = P`. Simplify using `only [Λ, hQ, if_true]`. Conclude with `Formalism.L2.DIV.lc_le_locP _ _ (hBA x hx)`.

Simplify using `only [Λ, hQ, if_false]`. Conclude with `Formalism.L2.DIV.lc_le_locP _ _ (B.smul_mem d hx)`. Establish `hpat : patchAt P A B = ⨅ Q, Λ Q` using `rfl`. Use `⟨?_, fun Q => ?_⟩` and prove the remaining obligations. Establish `hdE : (algebraMap (𝓞 E) E d) ≠ 0`.

Introduce `h`. Conclude with `hd (FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [h, map_zero]))`. Establish `hmem : ∀ x ∈ B, d • x ∈ patchAt P A B`. Introduce `x hx`. Rewrite using `[hpat, Submodule.mem_iInf]`.

Conclude with `fun Q => h2 Q x hx`. Establish `hle : ∀ x ∈ patchAt P A B, d • x ∈ B`. Introduce `x hx`. Rewrite `hx` using `[hpat, Submodule.mem_iInf]`. Establish `: Submodule.span (𝓞 E) {d • x} ≤ B` using `Formalism.L2.DIV.lc_le_of_le_locP fun Q => by`.

Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `h1 Q x (hx Q)`. Conclude with `this (Submodule.subset_span rfl)`. Set `f : Sp E n →ₗ[𝓞 E] Sp E n` to `d • LinearMap.id`. Establish `hf : Function.Injective f`.

Introduce `x y hxy`. Establish `e : algebraMap (𝓞 E) E d • x = algebraMap (𝓞 E) E d • y`. Simplify `hxy` using `[f, algebraMap_smul]`. Conclude with `smul_right_injective _ hdE e`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hB.fg ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hle x hx`. Rewrite using `[eq_top_iff, ← hB.span_eq_top, Submodule.span_le]`. Introduce `y hy`.

Establish `hy' : y = (algebraMap (𝓞 E) E d)⁻¹ • (d • y)`. Rewrite using `[← algebraMap_smul E d y, smul_smul, inv_mul_cancel₀ hdE, one_smul]`. Rewrite using `[hy']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (hmem y hy))`. Rewrite using `[hpat]`.

Conclude with `Formalism.L2.DIV.localized_iInf Λ B d hd hcl h1 h2 Q`.
-/
theorem patchAt_isLattice_locP (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) :
    Submodule.IsLattice E A → Submodule.IsLattice E B → Submodule.IsLattice E (patchAt P A B) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (patchAt P A B) = localization₂ Q.asIdeal (if Q = P then A else B) := by
  intro hA hB
  obtain ⟨d, hd, hAB, hBA⟩ := patchAt_commens A B hA hB
  let Λ : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) (Sp E n) := fun Q => localization₂ Q.asIdeal (if Q = P then A else B)
  have hcl : ∀ Q, localization₂ Q.asIdeal (Λ Q) = Λ Q := fun Q => Formalism.L2.DIV.localized_localized Q _
  have h1 : ∀ Q, ∀ x ∈ Λ Q, d • x ∈ localization₂ Q.asIdeal B := by
    intro Q x hx
    by_cases hQ : Q = P
    · subst hQ
      simp only [Λ, if_true] at hx
      obtain ⟨s, hs, hsx⟩ := hx
      refine ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact hAB _ hsx
    · simp only [Λ, hQ, if_false] at hx
      exact Submodule.smul_mem _ d hx
  have h2 : ∀ Q, ∀ x ∈ B, d • x ∈ Λ Q := by
    intro Q x hx
    by_cases hQ : Q = P
    · simp only [Λ, hQ, if_true]
      exact Formalism.L2.DIV.lc_le_locP _ _ (hBA x hx)
    · simp only [Λ, hQ, if_false]
      exact Formalism.L2.DIV.lc_le_locP _ _ (B.smul_mem d hx)
  have hpat : patchAt P A B = ⨅ Q, Λ Q := rfl
  refine ⟨?_, fun Q => ?_⟩
  · have hdE : (algebraMap (𝓞 E) E d) ≠ 0 := by
      intro h
      exact hd (FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [h, map_zero]))
    have hmem : ∀ x ∈ B, d • x ∈ patchAt P A B := by
      intro x hx
      rw [hpat, Submodule.mem_iInf]
      exact fun Q => h2 Q x hx
    have hle : ∀ x ∈ patchAt P A B, d • x ∈ B := by
      intro x hx
      rw [hpat, Submodule.mem_iInf] at hx
      have : Submodule.span (𝓞 E) {d • x} ≤ B :=
        Formalism.L2.DIV.lc_le_of_le_locP fun Q => by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact h1 Q x (hx Q)
      exact this (Submodule.subset_span rfl)
    let f : Sp E n →ₗ[𝓞 E] Sp E n := d • LinearMap.id
    have hf : Function.Injective f := by
      intro x y hxy
      have e : algebraMap (𝓞 E) E d • x = algebraMap (𝓞 E) E d • y := by
        simpa [f, algebraMap_smul] using hxy
      exact smul_right_injective _ hdE e
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hB.fg ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hle x hx
    · rw [eq_top_iff, ← hB.span_eq_top, Submodule.span_le]
      intro y hy
      have hy' : y = (algebraMap (𝓞 E) E d)⁻¹ • (d • y) := by
        rw [← algebraMap_smul E d y, smul_smul, inv_mul_cancel₀ hdE, one_smul]
      rw [hy']
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem y hy))
  · rw [hpat]
    exact Formalism.L2.DIV.localized_iInf Λ B d hd hcl h1 h2 Q

end GlobalTheory.InertExchange
