import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

/- English proof (translation)
Introduce `G _ Λ B hB r Q R v hR hv hvB`. Take `⟨hmono, -, hadd⟩` from `isBallFam_mono_neg_add G Λ B hB`. Set `f : (Fin r → Fin Q) → G` to `fun c => ∑ j, ((c j : ℕ) • v j)`. Establish `hterm : ∀ (n : ℕ) (j : Fin r), n • v j ∈ B (n * R)`. Introduce `n j`.

Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Simplify using `using hB.zero_mem 0 le_rfl`. Conclude with `(hB.nsmul_iff n R (v j) hn (hB.subset R (hvB j))).2 (hvB j)`. Establish `hsum : ∀ (c : Fin r → Fin Q) (s : Finset (Fin r)), ∑ j ∈ s, ((c j : ℕ) • v j) ∈ B (∑ j ∈ s, ((c j : ℕ) : ℝ) * R)`.

Introduce `c s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hB.zero_mem 0 le_rfl`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`.

Conclude with `hadd _ _ _ _ (hterm _ a) ih`. Establish `hmem : ∀ c, f c ∈ B (r * Q * R)`. Introduce `c`. Use `hmono _ _ ?_ (hsum c Finset.univ)` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`.

Apply `mul_le_mul_of_nonneg_right _ hR` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hinj : Function.Injective f`. Introduce `c c' h`. Establish `h0 : ∑ j, (((c j : ℕ) : ℤ) - ((c' j : ℕ) : ℤ)) • v j = 0`.

Simplify using `only [sub_smul, Finset.sum_sub_distrib, natCast_zsmul]`. Conclude with `sub_eq_zero.mpr h`. Use `Fintype.linearIndependent_iff.1 hv _ h0` as an intermediate fact. Use function extensionality and compare the values at `j`. Establish `hj` using `this j`.

Conclude with `Fin.ext (by omega)`. Establish `hsub : ((Finset.univ.image f : Finset G) : Set G) ⊆ B (r * Q * R)`. Introduce `x hx`. Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx`. Take `⟨c, rfl⟩` from `hx`.

Conclude with `hmem c`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_image_of_injective _ hinj]`. Simplify using the standard rewrite rules. Use `_ = ((Finset.univ.image f : Finset G) : Set G).encard := (Set.encard_coe_eq_coe_finsetCard _).symm`.

Use `_ ≤ (B (r * Q * R)).encard := Set.encard_le_encard hsub`.
-/
theorem isBallFam_pow_le_encard :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ)
      (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) →
      ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  classical
  intro G _ Λ B hB r Q R v hR hv hvB
  obtain ⟨hmono, -, hadd⟩ := isBallFam_mono_neg_add G Λ B hB
  let f : (Fin r → Fin Q) → G := fun c => ∑ j, ((c j : ℕ) • v j)

  have hterm : ∀ (n : ℕ) (j : Fin r), n • v j ∈ B (n * R) := by
    intro n j
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using hB.zero_mem 0 le_rfl
    · exact (hB.nsmul_iff n R (v j) hn (hB.subset R (hvB j))).2 (hvB j)
  have hsum : ∀ (c : Fin r → Fin Q) (s : Finset (Fin r)),
      ∑ j ∈ s, ((c j : ℕ) • v j) ∈ B (∑ j ∈ s, ((c j : ℕ) : ℝ) * R) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hB.zero_mem 0 le_rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact hadd _ _ _ _ (hterm _ a) ih
  have hmem : ∀ c, f c ∈ B (r * Q * R) := by
    intro c
    refine hmono _ _ ?_ (hsum c Finset.univ)
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hR
    calc (∑ j, ((c j : ℕ) : ℝ)) ≤ ∑ _j : Fin r, (Q : ℝ) :=
          Finset.sum_le_sum fun j _ => by exact_mod_cast (c j).isLt.le
      _ = r * Q := by simp
  have hinj : Function.Injective f := by
    intro c c' h
    have h0 : ∑ j, (((c j : ℕ) : ℤ) - ((c' j : ℕ) : ℤ)) • v j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, natCast_zsmul]
      exact sub_eq_zero.mpr h
    have := Fintype.linearIndependent_iff.1 hv _ h0
    funext j
    have hj := this j
    exact Fin.ext (by omega)
  have hsub : ((Finset.univ.image f : Finset G) : Set G) ⊆ B (r * Q * R) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨c, rfl⟩ := hx
    exact hmem c
  calc ((Q ^ r : ℕ) : ℕ∞) = ((Finset.univ.image f).card : ℕ∞) := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ = ((Finset.univ.image f : Finset G) : Set G).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (B (r * Q * R)).encard := Set.encard_le_encard hsub

end GlobalTheory.VolBr
