import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.FourierInv

open ValuativeRel

/- English proof (translation)
Rewrite using `[← Nat.card_eq_fintype_card]`. Establish `hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥` using `IsDiscreteValuationRing.not_a_field _`. Establish `hq` using `cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)`. Rewrite `hq` using `[Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `hq`.
-/
theorem card_res_pow (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (e : ℕ) : Fintype.card (Res k e) = resCard k ^ e := by
  rw [← Nat.card_eq_fintype_card]
  have hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

/- English proof (translation)
Introduce `k _ _ _ _ A _ _ C _ _ ψ ϖ n P hϖ hψ Ξ hΞ`. Use function extensionality and compare the values at `Y`. Rewrite using `[fourierSum_apply]`. Use `split_ifs with hY`. Set `r : A → P → 𝒪[k]` to `fun i j => ⟨((ϖ ^ n : kˣ) : k) * Y i j, hY i j j.2⟩`.

Set `S₀ : A → P → Res k n` to `fun i j => Ideal.Quotient.mk _ (r i j)`. Use `set M : Matrix A P k := (ϖ ^ n)⁻¹ • liftRes S₀ with hM`. Establish `h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k)` using `zero_lt_iff.2 (by simp)`. Establish `hdiff : ∀ i (j : P), Y i j - M i j ∈ 𝒪[k]` using `fun i j => by`. Establish `h1 : ((Quotient.out (S₀ i j) : 𝒪[k]) - r i j) ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n` using `Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)`.

Rewrite `h1` using `[GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ]`. Establish `e1 : Y i j - M i j = -((((ϖ ^ n)⁻¹ : kˣ) : k) * (((Quotient.out (S₀ i j) : 𝒪[k]) - r i j : 𝒪[k]) : k))`. Simplify using `only [hM, Matrix.smul_apply, Units.smul_def, smul_eq_mul, liftRes, Matrix.of_apply, r]`. Use `push_cast`. Rewrite using `[mul_sub, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, Valuation.mem_integer_iff, Valuation.map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `inv_mul_le_one_of_le₀ h1 h0.le`. Establish `triv : ∀ y : k, y ∈ 𝒪[k] → ψ y = 1` using `fun y hy => (hψ 1).2 le_rfl y (by simpa using (Valuation.mem_integer_iff _ _).1 hy)`. Establish `hpair : ∀ T : A → P → Res k n, ψ (pairCols P Y (liftRes T)) = ψ (pairCols P (setCols P Y M) (liftRes T))` using `fun T => by`.

Establish `e2 : pairCols P Y (liftRes T) = pairCols P (setCols P Y M) (liftRes T) + ∑ i, ∑ j : P, liftRes T i j * (Y i j - M i j)`. Simplify using `only [pairCols, setCols, Matrix.of_apply, Finset.coe_mem, dif_pos, Subtype.coe_eta, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, AddChar.map_add_eq_mul, triv _ (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (liftRes_mem T i j) (hdiff i j)), mul_one]`.

Establish `hinv : Ξ (setCols P Y M) = Ξ Y`. Establish `e3 : setCols P Y M = Y + Matrix.of fun i j => if h : j ∈ P then M i ⟨j, h⟩ - Y i j else 0`. Apply the tactic sequence `ext i j; by_cases h : j ∈ P <;> simp [setCols, h]`. Rewrite using `[e3]`. Use `hΞ.2 Y _ (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩)` and prove the remaining obligations.

Simplify using `only [Matrix.of_apply, dif_pos hj]`. Use `neg_mem (hdiff i ⟨j, hj⟩)` as an intermediate fact. Simplify using `using this`. Simplify using `[hj]`. Repeatedly rewrite using `[hpair]`.

Rewrite using `[GlobalTheory.SplitFlip.Model.sum_invFourierSum hϖ hψ n P Ξ Y S₀]`. Establish `hq : (resCard k : ℂ) ≠ 0` using `by show ((Nat.card 𝓀[k] : ℕ) : ℂ) ≠ 0`. Conclude with `(Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])).ne'` after adjusting the coercions. Establish `hc : ((resCard k : ℂ) ^ (n * Fintype.card A * P.card))⁻¹ * ((resCard k : ℂ) ^ n) ^ (Fintype.card A * P.card) = 1`. Rewrite using `[← pow_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq)]`.

Rewrite using `[← hM, hinv, card_res_pow, Nat.cast_pow, ← mul_assoc, hc, one_mul]`. Use `symm`. Use `hΞ.1 Y fun h => hY ?_` and prove the remaining obligations. Conclude with `(GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.1 h).1`.
-/
theorem fourierSum_invFourierSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (n : ℕ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Ξ : Matrix A C k → ℂ, HasDepth ϖ n (blockLat ϖ n P) Ξ → fourierSum ψ ϖ n P (invFourierSum ψ ϖ n P Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ n P hϖ hψ Ξ hΞ
  funext Y
  rw [fourierSum_apply]
  split_ifs with hY
  · let r : A → P → 𝒪[k] := fun i j => ⟨((ϖ ^ n : kˣ) : k) * Y i j, hY i j j.2⟩
    let S₀ : A → P → Res k n := fun i j => Ideal.Quotient.mk _ (r i j)
    set M : Matrix A P k := (ϖ ^ n)⁻¹ • liftRes S₀ with hM
    have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
    have hdiff : ∀ i (j : P), Y i j - M i j ∈ 𝒪[k] := fun i j => by
      have h1 : ((Quotient.out (S₀ i j) : 𝒪[k]) - r i j) ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n :=
        Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
      rw [GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ] at h1
      have e1 : Y i j - M i j = -((((ϖ ^ n)⁻¹ : kˣ) : k) * (((Quotient.out (S₀ i j) : 𝒪[k]) - r i j : 𝒪[k]) : k)) := by
        simp only [hM, Matrix.smul_apply, Units.smul_def, smul_eq_mul, liftRes, Matrix.of_apply, r]
        push_cast
        rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
        ring
      rw [e1, Valuation.mem_integer_iff, Valuation.map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_mul_le_one_of_le₀ h1 h0.le
    have triv : ∀ y : k, y ∈ 𝒪[k] → ψ y = 1 := fun y hy =>
      (hψ 1).2 le_rfl y (by simpa using (Valuation.mem_integer_iff _ _).1 hy)
    have hpair : ∀ T : A → P → Res k n,
        ψ (pairCols P Y (liftRes T)) = ψ (pairCols P (setCols P Y M) (liftRes T)) := fun T => by
      have e2 : pairCols P Y (liftRes T) = pairCols P (setCols P Y M) (liftRes T) +
          ∑ i, ∑ j : P, liftRes T i j * (Y i j - M i j) := by
        simp only [pairCols, setCols, Matrix.of_apply, Finset.coe_mem, dif_pos, Subtype.coe_eta,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e2, AddChar.map_add_eq_mul, triv _ (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (liftRes_mem T i j) (hdiff i j)), mul_one]
    have hinv : Ξ (setCols P Y M) = Ξ Y := by
      have e3 : setCols P Y M = Y + Matrix.of fun i j => if h : j ∈ P then M i ⟨j, h⟩ - Y i j else 0 := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      rw [e3]
      refine hΞ.2 Y _ (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩)
      · simp only [Matrix.of_apply, dif_pos hj]
        have := neg_mem (hdiff i ⟨j, hj⟩)
        simpa using this
      · simp [hj]
    simp_rw [hpair]
    rw [GlobalTheory.SplitFlip.Model.sum_invFourierSum hϖ hψ n P Ξ Y S₀]
    have hq : (resCard k : ℂ) ≠ 0 := by
      show ((Nat.card 𝓀[k] : ℕ) : ℂ) ≠ 0
      exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])).ne'
    have hc : ((resCard k : ℂ) ^ (n * Fintype.card A * P.card))⁻¹ *
        ((resCard k : ℂ) ^ n) ^ (Fintype.card A * P.card) = 1 := by
      rw [← pow_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq)]
    rw [← hM, hinv, card_res_pow, Nat.cast_pow, ← mul_assoc, hc, one_mul]
  · symm
    refine hΞ.1 Y fun h => hY ?_
    exact (GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat.1 h).1

end GlobalTheory.FlipMatch.FourierInv
