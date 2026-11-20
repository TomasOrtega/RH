import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

/- English proof (translation)
Establish `h` using `D.c_add 0 0`. Rewrite `h` using `[add_zero, padd, ← Hom.mul_def]`. Conclude with `mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)`.
-/
theorem degPre_c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = 1 := by
  have h := D.c_add 0 0
  rw [add_zero, padd, ← Hom.mul_def] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

/- English proof (translation)
Use `⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Fan.IsLimit.hom_ext T.lim` to reduce the goal to its premises. Introduce `i`. Establish `hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k` using `fun _ => rfl`. Simplify using `only [hp, Category.assoc, T.inc_pr']`.

Rewrite using `[(T.pr_hom i).one_hom]`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Apply `Fan.IsLimit.hom_ext T.lim` to reduce the goal to its premises.

Introduce `i`. Establish `hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k` using `fun _ => rfl`. Simplify using `only [hp, Category.assoc, T.inc_pr']`. Rewrite using `[(T.pr_hom i).mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, T.inc_pr']`. Use `split_ifs`.

Simplify using the standard rewrite rules. Rewrite using `[comp_one]`. Establish `: ((1 : D.P.A ⟶ D.P.A) ⊗ₘ (1 : D.P.A ⟶ D.P.A)) = lift (fst _ _ ≫ 1) (snd _ _ ≫ 1)`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[this, ← Hom.mul_def, comp_one, comp_one, _root_.mul_one]`.

Simplify using `using T.inc_pr' i₀ i₀`. Apply `Fan.IsLimit.hom_ext T.lim` to reduce the goal to its premises. Introduce `i`. Establish `hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k` using `fun _ => rfl`. Simplify using `only [hp, Category.assoc, T.inc_pr', Tens.act_pr]`.

Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, Category.comp_id, Finset.prod_eq_single i]`. Simplify using `[Matrix.single_apply]`. Introduce `j _ hj`.

Simplify using `[Matrix.single_apply, Ne.symm hj]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, comp_one]`. Use `symm`. Apply `Finset.prod_eq_one` to reduce the goal to its premises.

Introduce `j _`. Simplify using `[Matrix.single_apply, Ne.symm h]`. Introduce `y`. Apply `Fan.IsLimit.hom_ext T.lim` to reduce the goal to its premises. Introduce `i`.

Establish `hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k` using `fun _ => rfl`. Simplify using `only [hp, Category.assoc, T.inc_pr', T.c_pr]`. Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality. Simplify using `[Tens.xi]`.

Rewrite using `[if_neg h, comp_one]`. Simplify using `[Tens.xi, Pi.single_apply, h, degPre_c_zero]`.
-/
theorem tens_inc_pr_facts (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r) :
    IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧
      ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).one_hom]
    split_ifs
    · simp
    · rw [comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, T.inc_pr']
    split_ifs
    · simp
    · rw [comp_one]
      have : ((1 : D.P.A ⟶ D.P.A) ⊗ₘ (1 : D.P.A ⟶ D.P.A)) = lift (fst _ _ ≫ 1) (snd _ _ ≫ 1) := by
        ext <;> simp
      rw [this, ← Hom.mul_def, comp_one, comp_one, _root_.mul_one]
  · simpa using T.inc_pr' i₀ i₀
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', Tens.act_pr]
    by_cases h : i = i₀
    · subst h
      rw [if_pos rfl, Category.comp_id, Finset.prod_eq_single i]
      · simp [Matrix.single_apply]
      · intro j _ hj
        simp [Matrix.single_apply, Ne.symm hj]
      · simp
    · rw [if_neg h, comp_one]
      symm
      apply Finset.prod_eq_one
      intro j _
      simp [Matrix.single_apply, Ne.symm h]
  · intro y
    apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', T.c_pr]
    by_cases h : i = i₀
    · subst h
      simp [Tens.xi]
    · rw [if_neg h, comp_one]
      simp [Tens.xi, Pi.single_apply, h, degPre_c_zero]

end GlobalTheory.Mum
