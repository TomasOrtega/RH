import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
import Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockRhoFull
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerSmulLe
import Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockChiOneTriv
import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKerChiOne

open Finset Classical

noncomputable section

namespace Formalism.NG

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace IdempotentColumnIndexImages

/- English proof (translation)
The claim follows from `Finset.sum_image fun _ _ _ _ h => hinj h`.
-/
lemma sum_image_colIdx {ι ι' : Type*} [Fintype ι] [DecidableEq ι'] (colIdx : ι → ι')
    (hinj : Function.Injective colIdx) (f : ι' → ℕ∞) :
    ∑ w ∈ (univ : Finset ι).image colIdx, f w = ∑ l : ι, f (colIdx l) :=
  Finset.sum_image fun _ _ _ _ h => hinj h

/- English proof (translation)
Rewrite using `[Finset.card_image_of_injective _ hinj, Finset.card_univ]`.
-/
lemma card_image_colIdx {ι ι' : Type*} [Fintype ι] [DecidableEq ι'] (colIdx : ι → ι')
    (hinj : Function.Injective colIdx) :
    (((univ : Finset ι).image colIdx).card : ℕ∞) = (Fintype.card ι : ℕ∞) := by
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]

end IdempotentColumnIndexImages

/- English proof (translation)
Introduce `O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j Kc k0 ℓ cB sE tE hd hE hEE he₁ hEM hk0 hδ hτ ρM Ψ lrows qs F deg vζ Q Sha H0 cols eO vδ hH0 hl hq hcols hQ hsel`. Set `lenRow : ι' → ℕ∞` to `fun w => (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)`. Establish `hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧ Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧ ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B`. Introduce `w hw`. Distinguish the cases in `hwl : w ∈ lrows`.

Take `⟨B, h1, h2, h3⟩` from `hl w hwl`. Use `⟨B, h1, h2.trans ?_, h3⟩` and prove the remaining obligations. Simplify using `only [lenRow, if_pos hwl]`. Conclude with `le_self_add`. Establish `hwq : w ∈ qs` using `(Finset.mem_union.mp hw).resolve_left hwl`.

Take `⟨B, h1, h2, h3⟩` from `hq w hwq`. Use `⟨B, h1, h2.trans ?_, h3⟩` and prove the remaining obligations. Simplify using `only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]`. Establish `hkerEq : LinearMap.ker Ψ = kerY (O` using `O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 := colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0`. Establish `hK1` using `hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 he₁ hEM hk0 (fun m => by rw [algebraMap_smul]; exact hδ m)`.

Establish `hsumH : ∑ l : ι, Module.length O (LinearMap.ker (colDO (O` using `O) (M := d → KO O) r χ (D (colIdx l)))) ≤ ∑ w ∈ cols, H0 := by`. Combine the equalities or inequalities in the displayed calculation. Establish `hker' : Module.length O (LinearMap.ker Ψ) ≤ ∑ w ∈ cols, ((((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) * (eO * (((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) + vδ) + (fun _ => H0 : ι' → ℕ∞) w) + (cols.card : ℕ∞) * (Fintype.card d : ℕ∞) * vδ`. Rewrite using `[hkerEq]`. Use `hK1.trans ?_` and prove the remaining obligations.

Simplify using `only [Nat.cast_zero, zero_mul, zero_add]`. Rewrite using `[show (cols.card : ℕ∞) = (Fintype.card ι : ℕ∞) from IdempotentColumnIndexImages.card_image_colIdx colIdx hinj]`. Conclude with `add_le_add hsumH le_rfl`. Establish `hcob : ∀ (h : ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A] (d → KO O)) (v : d → KO O), (Ψ h : G → (d → KO O)) = coD0 ρM v → (δO * δO) • v = 0` using `fun h v hv => cobColumn O A T' G (d → KO O) r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 sE tE hE hEE hEM hδ hτ h v hv`. Establish `h` using `blockRhoAbs O G d ρM _ Ψ δO hcob ι' (lrows ∪ qs) cols D F lenRow Q Sha ℓ (fun _ => 0) (fun _ => 0) (fun _ => H0) hrows hcols hQ hsel hker'`.

Establish `hsum : ∑ w ∈ lrows ∪ qs, lenRow w = eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w`. Simplify using `only [lenRow]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Nat.cast_zero, zero_mul, zero_add, Finset.sum_const, nsmul_eq_mul, hd, Nat.cast_one, mul_one]`.

Rewrite using `[hsum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem blockChiCFull_of (hK : StatColKerChiC.{u₁, u₂, u₃, u₄, u₅}) :
    StatBlockChiCFull.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j Kc k0 ℓ cB sE tE
    hd hE hEE he₁ hEM hk0 hδ hτ ρM Ψ lrows qs F deg vζ Q Sha H0 cols eO vδ hH0 hl hq hcols hQ hsel
  let lenRow : ι' → ℕ∞ := fun w =>
    (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)
  have hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B := by
    intro w hw
    by_cases hwl : w ∈ lrows
    · obtain ⟨B, h1, h2, h3⟩ := hl w hwl
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_pos hwl]
      exact le_self_add
    · have hwq : w ∈ qs := (Finset.mem_union.mp hw).resolve_left hwl
      obtain ⟨B, h1, h2, h3⟩ := hq w hwq
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]
  have hkerEq : LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 :=
    colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
      Kc k0
  have hK1 := hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    he₁ hEM hk0 (fun m => by rw [algebraMap_smul]; exact hδ m)
  have hsumH : ∑ l : ι, Module.length O
      (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D (colIdx l)))) ≤ ∑ w ∈ cols, H0 := by
    calc ∑ l : ι, Module.length O
          (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D (colIdx l))))
        ≤ ∑ l : ι, H0 :=
          Finset.sum_le_sum fun l _ => hH0 (colIdx l) (Finset.mem_image_of_mem _ (Finset.mem_univ l))
      _ = ∑ w ∈ cols, H0 := (IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun _ => H0)).symm
  have hker' : Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, ((((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) *
        (eO * (((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) + vδ) + (fun _ => H0 : ι' → ℕ∞) w) +
        (cols.card : ℕ∞) * (Fintype.card d : ℕ∞) * vδ := by
    rw [hkerEq]
    refine hK1.trans ?_
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [show (cols.card : ℕ∞) = (Fintype.card ι : ℕ∞) from IdempotentColumnIndexImages.card_image_colIdx colIdx hinj]
    exact add_le_add hsumH le_rfl
  have hcob : ∀ (h : ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
      (d → KO O)) (v : d → KO O), (Ψ h : G → (d → KO O)) = coD0 ρM v → (δO * δO) • v = 0 :=
    fun h v hv => cobColumn O A T' G (d → KO O) r χ E e₁ δ δO ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 sE tE hE hEE hEM hδ hτ h v hv
  have h := blockRhoAbs O G d ρM _ Ψ δO hcob ι' (lrows ∪ qs) cols D F lenRow Q Sha ℓ
    (fun _ => 0) (fun _ => 0) (fun _ => H0) hrows hcols hQ hsel hker'
  have hsum : ∑ w ∈ lrows ∪ qs, lenRow w =
      eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w := by
    simp only [lenRow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_zero, zero_mul, zero_add, Finset.sum_const, nsmul_eq_mul, hd, Nat.cast_one,
    mul_one]
  rw [hsum]
  ring

/- English proof (translation)
Introduce `O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0 ℓ cB hd hu he₁ hEM hδ hk0 ρM Ψ lrows qs F deg vζ Q vhE cols eO vδ hl hq hcols hQ hsel`. Set `lenRow : ι' → ℕ∞` to `fun w => (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)`. Establish `hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧ Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧ ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B`. Introduce `w hw`. Distinguish the cases in `hwl : w ∈ lrows`.

Take `⟨B, h1, h2, h3⟩` from `hl w hwl`. Use `⟨B, h1, h2.trans ?_, h3⟩` and prove the remaining obligations. Simplify using `only [lenRow, if_pos hwl]`. Conclude with `le_self_add`. Establish `hwq : w ∈ qs` using `(Finset.mem_union.mp hw).resolve_left hwl`.

Take `⟨B, h1, h2, h3⟩` from `hq w hwq`. Use `⟨B, h1, h2.trans ?_, h3⟩` and prove the remaining obligations. Simplify using `only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]`. Establish `hB : ∀ x ∈ coB1 ρM, x = 0`. Introduce and unpack `_ ⟨v, rfl⟩`.

Use function extensionality and compare the values at `g`. Conclude with `(show uElt r χ g • v - v = 0 by rw [hu, sub_self])`. Establish `h` using `TrivialCharacterBlockLength.blockTrivAbs ρM hB Ψ (lrows ∪ qs) cols D F lenRow Q vhE hrows hcols hQ hsel`. Establish `hkerEq : LinearMap.ker Ψ = kerY (O` using `O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 := colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0`. Establish `hK1` using `hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 ℓ (fun l => e' (colIdx l)) hu he₁ hEM (fun m => by rw [algebraMap_smul]; exact hδ m) hk0`.

Establish `hker : Module.length O (LinearMap.ker Ψ) ≤ ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) + (cols.card : ℕ∞) * vδ`. Rewrite using `[hkerEq]`. Use `hK1.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hd, Nat.cast_one, mul_one, IdempotentColumnIndexImages.card_image_colIdx colIdx hinj, IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun w => eO * (e' w : ℕ∞) + 2 * vδ)]`. Simplify using `only [one_mul]`.

Both sides reduce to the same expression. Establish `hsum : ∑ w ∈ lrows ∪ qs, lenRow w = eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w`. Simplify using `only [lenRow]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]`. Rewrite `h` using `[hsum]`.

Conclude with `h.trans (TrivialCharacterBlockLength.final_arith _ _ _ _ _ _ _ hker)`.
-/
theorem blockChiOneFull_of (hK : StatColKerChiOne.{u₁, u₂, u₃, u₄, u₅}) :
    StatBlockChiOneFull.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0 ℓ cB
    hd hu he₁ hEM hδ hk0 ρM Ψ lrows qs F deg vζ Q vhE cols eO vδ hl hq hcols hQ hsel
  let lenRow : ι' → ℕ∞ := fun w =>
    (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)
  have hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B := by
    intro w hw
    by_cases hwl : w ∈ lrows
    · obtain ⟨B, h1, h2, h3⟩ := hl w hwl
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_pos hwl]
      exact le_self_add
    · have hwq : w ∈ qs := (Finset.mem_union.mp hw).resolve_left hwl
      obtain ⟨B, h1, h2, h3⟩ := hq w hwq
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]
  have hB : ∀ x ∈ coB1 ρM, x = 0 := by
    rintro _ ⟨v, rfl⟩
    funext g
    exact (show uElt r χ g • v - v = 0 by rw [hu, sub_self])
  have h := TrivialCharacterBlockLength.blockTrivAbs ρM hB Ψ (lrows ∪ qs) cols D F lenRow Q vhE hrows hcols hQ hsel
  have hkerEq : LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 :=
    colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
      Kc k0
  have hK1 := hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    ℓ (fun l => e' (colIdx l)) hu he₁ hEM (fun m => by rw [algebraMap_smul]; exact hδ m) hk0
  have hker : Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) + (cols.card : ℕ∞) * vδ := by
    rw [hkerEq]
    refine hK1.trans (le_of_eq ?_)
    rw [hd, Nat.cast_one, mul_one, IdempotentColumnIndexImages.card_image_colIdx colIdx hinj,
      IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun w => eO * (e' w : ℕ∞) + 2 * vδ)]
    simp only [one_mul]
    rfl
  have hsum : ∑ w ∈ lrows ∪ qs, lenRow w =
      eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w := by
    simp only [lenRow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]
  rw [hsum] at h
  exact h.trans (TrivialCharacterBlockLength.final_arith _ _ _ _ _ _ _ hker)

/- English proof (translation)
The claim follows from `blockChiCFull_of colKerChiC`.
-/
theorem blockChiCFull : StatBlockChiCFull := blockChiCFull_of colKerChiC

/- English proof (translation)
The claim follows from `blockChiOneFull_of colKerChiOne`.
-/
theorem blockChiOneFull : StatBlockChiOneFull := blockChiOneFull_of colKerChiOne

end Formalism.NG
