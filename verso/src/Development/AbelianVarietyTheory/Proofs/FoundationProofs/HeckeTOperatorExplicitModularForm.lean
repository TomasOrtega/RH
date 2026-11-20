import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashRatIsBoundedAtGamma1InterGamma0LevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableHeckeOperatorsExplicitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTSlashInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitEqSumSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowSmulHeckeVOperatorExplicitEqSlashDiagStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `g _`. Simplify using `only [Finset.sum_empty]`. Rewrite using `[SlashAction.zero_slash]`.

Conclude with `zero_form_isBoundedAtImInfty`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
lemma isBoundedAt_finsetSum_heckeT {c : OnePoint ℝ} {k : ℤ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsBoundedAt (F i) k) : c.IsBoundedAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    simp only [Finset.sum_empty]
    rw [SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `N l q k σ hN hq hql hσ f`. Establish `hq0 : 0 < q` using `hq.pos`. Establish `hl : 0 < l`. Break down `Nat.eq_zero_or_pos l with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using `at hql`. Conclude with `h`. Establish `hinv : ∀ γ ∈ lev N l, (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f` using `fun γ hγ => f.slash_action_eq' _ ⟨γ, hγ, rfl⟩`. Use `⟨{ toFun := heckeT k q σ ⇑f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ }, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨A, (hA : A ∈ lev N l), rfl⟩`.

Conclude with `GlobalTheory.T.heckeT_slash_eq_of_slash_eq N l q k σ ⇑f hN hq hql hσ hinv A hA`. Conclude with `(GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k σ ⇑f hq0 f.holo').2.2`. Introduce `c hc`. Establish `hsum` using `GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0`. Establish `hv` using `GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag q k ((⇑f) ∣[k] σ) hq0`.

Use `show c.IsBoundedAt (heckeT k q σ ⇑f) k`. Unfold `heckeT`. Rewrite using `[hsum, hv]`. Use `OnePoint.IsBoundedAt.add (isBoundedAt_finsetSum_heckeT _ _ fun j _ => ?_) ?_` and prove the remaining obligations. Conclude with `GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc`.

Use `set D := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0.ne') with hD`. Establish `e : ((⇑f ∣[k] σ) ∣[k] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) D) = ⇑f ∣[k] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ σ * D)`. Rewrite using `[map_mul, SlashAction.slash_mul, SL_slash]`. Use `congr 2`. Use extensionality with `i j`.

Simplify using `[Matrix.SpecialLinearGroup.mapGL]`. Rewrite using `[e]`. Use `GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl ?_ f c hc` and prove the remaining obligations. Simplify using `[hD, Matrix.det_fin_two_of]`. Conclude with `hq0` after adjusting the coercions.
-/
theorem heckeT_modularForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  intro N l q k σ hN hq hql hσ f
  have hq0 : 0 < q := hq.pos
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hql
    · exact h
  have hinv : ∀ γ ∈ lev N l, (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := fun γ hγ =>
    f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  refine ⟨{ toFun := heckeT k q σ ⇑f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨A, (hA : A ∈ lev N l), rfl⟩
    exact GlobalTheory.T.heckeT_slash_eq_of_slash_eq N l q k σ ⇑f hN hq hql hσ hinv A hA
  · exact (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k σ ⇑f hq0 f.holo').2.2
  · intro c hc
    have hsum := GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0
    have hv := GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag q k ((⇑f) ∣[k] σ) hq0
    show c.IsBoundedAt (heckeT k q σ ⇑f) k
    unfold heckeT
    rw [hsum, hv]
    refine OnePoint.IsBoundedAt.add (isBoundedAt_finsetSum_heckeT _ _ fun j _ => ?_) ?_
    · exact GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
    · set D := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
          (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0.ne') with hD
      have e : ((⇑f ∣[k] σ) ∣[k] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) D)
          = ⇑f ∣[k] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)
              (Matrix.SpecialLinearGroup.mapGL ℚ σ * D) := by
        rw [map_mul, SlashAction.slash_mul, SL_slash]
        congr 2
        ext i j
        simp [Matrix.SpecialLinearGroup.mapGL]
      rw [e]
      refine GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl ?_ f c hc
      simp [hD, Matrix.det_fin_two_of]
      exact_mod_cast hq0
end GlobalTheory.Hk
