import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace RenameMultiProjPrime

variable {S K' : Type} [DecidableEq S] [DecidableEq K'] {κ : S → Type} {ι' : K' → Type} (E : S ≃ K')
  (σ : (Σ s, κ s) ≃ (Σ k', ι' k'))

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => funext k`. Simplify using the standard rewrite rules. Consider the case `add f g hf hg`. Rewrite using `[Finsupp.mapDomain_add, map_add, map_add, hf, hg]`.

Both sides reduce to the same expression. Consider the case `single v n`. Rewrite using `[Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]`. Use function extensionality and compare the values at `k`. Simplify using `only [blockWeight, hσ, Function.comp_apply, Pi.smul_apply, Pi.single_apply, Equiv.symm_apply_eq, smul_eq_mul]`.
-/
theorem weight_mapDomain (hσ : ∀ v, (σ v).1 = E v.1) (d : (Σ s, κ s) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain σ d) =
      Finsupp.weight (blockWeight κ) d ∘ E.symm := by
  induction d using Finsupp.induction_linear with
  | zero => funext k; simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
    rfl
  | single v n =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    funext k
    simp only [blockWeight, hσ, Function.comp_apply, Pi.smul_apply, Pi.single_apply,
      Equiv.symm_apply_eq, smul_eq_mul]

/- English proof (translation)
Use extensionality with `m`. Establish `hm : m = Finsupp.mapDomain σ (Finsupp.mapDomain σ.symm m)`. Rewrite using `[← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]`. Rewrite using `[hm, coeff_weightedHomogeneousComponent, coeff_rename_mapDomain _ σ.injective, coeff_rename_mapDomain _ σ.injective, coeff_weightedHomogeneousComponent, weight_mapDomain E σ hσ]`. Establish `hiff : Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) ∘ E.symm = b ∘ E.symm ↔ Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) = b` using `E.symm.surjective.injective_comp_right.eq_iff`.

Simplify using `only [hiff]`.
-/
theorem rename_weightedHomogeneousComponent {R : Type u} [CommRing R]
    (hσ : ∀ v, (σ v).1 = E v.1) (b : S → ℕ) (f : MRing κ R) :
    rename σ (weightedHomogeneousComponent (blockWeight κ) b f) =
      weightedHomogeneousComponent (blockWeight ι') (b ∘ E.symm) (rename σ f) := by
  classical
  ext m
  have hm : m = Finsupp.mapDomain σ (Finsupp.mapDomain σ.symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  rw [hm, coeff_weightedHomogeneousComponent, coeff_rename_mapDomain _ σ.injective,
    coeff_rename_mapDomain _ σ.injective, coeff_weightedHomogeneousComponent,
    weight_mapDomain E σ hσ]
  have hiff : Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) ∘ E.symm = b ∘ E.symm ↔
      Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) = b :=
    E.symm.surjective.injective_comp_right.eq_iff
  simp only [hiff]

end RenameMultiProjPrime

/- English proof (translation)
Introduce `R _ S K' _ _ κ ι' E σ hσ P hP`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `hP.isPrime` as an intermediate fact. Conclude with `Ideal.comap_isPrime _ _`. Introduce `f hf b`.

Rewrite `hf`, the goal using `[Ideal.mem_comap]`. Rewrite using `[RenameMultiProjPrime.rename_weightedHomogeneousComponent (R := R) E σ hσ b f]`. Conclude with `hP.multiHomog _ hf _`. Introduce `s`. Take `⟨i', hi'⟩` from `hP.relevant (E s)`.

Take `⟨⟨s', i⟩, hv⟩ : ∃ v, σ v = ⟨E s, i'⟩` from `σ.surjective _`. Establish `hs : s' = s` using `E.injective (by simpa [hv] using (hσ ⟨s', i⟩).symm)`. Substitute `hs` using the available equality. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, rename_X, hv]`.

Conclude with `hi'`.
-/
theorem RenameMultiProjPrime.proof : RenameMultiProjPrime.Statement.{u} := by
  intro R _ S K' _ _ κ ι' E σ hσ P hP
  refine ⟨?_, ?_, ?_⟩
  · have := hP.isPrime
    exact Ideal.comap_isPrime _ _
  · intro f hf b
    rw [Ideal.mem_comap] at hf ⊢
    rw [RenameMultiProjPrime.rename_weightedHomogeneousComponent (R := R) E σ hσ b f]
    exact hP.multiHomog _ hf _
  · intro s
    obtain ⟨i', hi'⟩ := hP.relevant (E s)
    obtain ⟨⟨s', i⟩, hv⟩ : ∃ v, σ v = ⟨E s, i'⟩ := σ.surjective _
    have hs : s' = s := E.injective (by simpa [hv] using (hσ ⟨s', i⟩).symm)
    subst hs
    refine ⟨i, ?_⟩
    rw [Ideal.mem_comap, rename_X, hv]
    exact hi'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
