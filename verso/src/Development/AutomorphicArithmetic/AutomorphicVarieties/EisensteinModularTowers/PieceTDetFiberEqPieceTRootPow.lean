import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinRootPow
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

/- English proof (translation)
Establish `hl : 0 < l ^ m` using `pow_pos (Fact.out : l.Prime).pos m`. Use `haveI : NeZero (l ^ m) := ⟨hl.ne'⟩`. Establish `hM : 0 < N * l ^ m` using `Nat.mul_pos hN hl`. Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hζ` using `[zero_pow hM.ne']`. Conclude with `zero_ne_one hζ`. Rewrite using `[UpperTheory.smoothedEisenstein_root_pow c j _ ζ a _ β hζ0]`. Use `UpperTheory.smoothedEisenstein_congr_of_modEq c j _ ζ hM hζ (Int.ModEq.refl _) ?_` and prove the remaining obligations. Establish `h1 : ((β : ℤ) * (y.val : ℤ)) ≡ (((y * (β : ZMod (l ^ m))).val : ℕ) : ℤ) [ZMOD ((l ^ m : ℕ) : ℤ)]`.

Rewrite using `[← ZMod.intCast_eq_intCast_iff]`. Use `push_cast`. Simplify using `[mul_comm]`. Establish `h2` using `Int.ModEq.mul_left' (c := (N : ℤ)) h1`. Simplify using `only [mul_zero, add_zero]`.

Rewrite using `[Nat.cast_mul N, mul_left_comm]`. Conclude with `h2`.
-/
private theorem siegel_function_root_power_eq {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N m j : ℕ) (c a : ℤ) (ζ : K) (β : ℕ)
    (hN : 0 < N) (hζ : ζ ^ (N * l ^ m) = 1) (y : ZMod (l ^ m)) :
    smF c j (N * l ^ m) (ζ ^ β) a ((N : ℤ) * (y.val : ℤ) + (l : ℤ) ^ m * 0) =
      smF c j (N * l ^ m) ζ a ((N : ℤ) * (((y * (β : ZMod (l ^ m))).val : ℕ) : ℤ) + (l : ℤ) ^ m * 0) := by
  have hl : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  haveI : NeZero (l ^ m) := ⟨hl.ne'⟩
  have hM : 0 < N * l ^ m := Nat.mul_pos hN hl
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  rw [UpperTheory.smoothedEisenstein_root_pow c j _ ζ a _ β hζ0]
  refine UpperTheory.smoothedEisenstein_congr_of_modEq c j _ ζ hM hζ (Int.ModEq.refl _) ?_
  have h1 : ((β : ℤ) * (y.val : ℤ)) ≡ (((y * (β : ZMod (l ^ m))).val : ℕ) : ℤ) [ZMOD ((l ^ m : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp [mul_comm]
  have h2 := Int.ModEq.mul_left' (c := (N : ℤ)) h1
  simp only [mul_zero, add_zero]
  rw [Nat.cast_mul N, mul_left_comm]
  exact h2

/- English proof (translation)
Introduce `K _ _ l _ N m k c d xt t ζ β z₀ hN hm hζ hz hβ r`. Establish `hl : 0 < l ^ m` using `pow_pos (Fact.out : l.Prime).pos m`. Use `haveI : NeZero (l ^ m) := ⟨hl.ne'⟩`. Establish `hdet : (!![1, 0; 0, z₀] : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = z₀`. Simplify using `[Matrix.det_fin_two]`.

Take `⟨D, hD⟩ : ∃ D : GL (Fin 2) (ZMod (l ^ m)), (D : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) = !![1, 0; 0, z₀]` from `⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hdet]; exact hz), rfl⟩`. Establish `e0 : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))) (i : Fin 2), ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 0 = (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 0`. Introduce `γ i`. Rewrite using `[Units.val_mul, hD]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `e1 : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))) (i : Fin 2), ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 1 = (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 1 * (β : ZMod (l ^ m))`. Introduce `γ i`. Rewrite using `[Units.val_mul, hD, hβ]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `ed : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))), ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det * z₀`.

Introduce `γ`. Rewrite using `[Units.val_mul, Matrix.det_mul, hD, hdet]`. Establish `eψ : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))), (1 : DirichletCharacter K (l ^ m)) (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) = 1`. Introduce `γ`. Rewrite using `[ZMod.natCast_zmod_val]`.

Conclude with `MulChar.one_apply (Matrix.isUnits_det_units γ)`. Unfold `pieceT`. Use `congr 1`. Use `symm`. Use `Finset.sum_equiv (Equiv.mulRight D) (fun γ => ?_) (fun γ _ => ?_)` and prove the remaining obligations.

Simplify using `only [Finset.mem_filter, unitSet, Finset.mem_univ, true_and, Equiv.coe_mulRight, e0, ed, ZMod.natCast_zmod_val]`. Use `and_congr_right fun _ => ⟨fun h => by rw [h, one_mul], fun h => ?_⟩` and prove the remaining obligations. Conclude with `hz.mul_right_cancel (by rw [h, one_mul])`. Simplify using `only [Equiv.coe_mulRight, eψ, rowT, e0, e1]`. Rewrite using `[siegel_function_root_power_eq l N m _ c _ ζ β hN hζ, siegel_function_root_power_eq l N m _ d _ ζ β hN hζ]`.
-/
theorem UpperTheory.pieceT_det_fiber_eq_pieceT_root_pow :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N m k : ℕ) (c d xt t : ℤ) (ζ : K) (β : ℕ) (z₀ : ZMod (l ^ m)), 0 < N → 1 ≤ m → ζ ^ (N * l ^ m) = 1 → IsUnit z₀ → (β : ZMod (l ^ m)) = z₀ → ∀ r : ℕ, pieceT N l m m k (1 : DirichletCharacter K (l ^ m)) c d (xt, 0) (t, 0) ζ ((unitSet l m).filter fun γ : GL (Fin 2) (ZMod (l ^ m)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = pieceT N l m m k (1 : DirichletCharacter K (l ^ m)) c d (xt, 0) (t, 0) (ζ ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1) r := by
  intro K _ _ l _ N m k c d xt t ζ β z₀ hN hm hζ hz hβ r
  have hl : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  haveI : NeZero (l ^ m) := ⟨hl.ne'⟩
  have hdet : (!![1, 0; 0, z₀] : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = z₀ := by
    simp [Matrix.det_fin_two]
  obtain ⟨D, hD⟩ : ∃ D : GL (Fin 2) (ZMod (l ^ m)), (D : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) = !![1, 0; 0, z₀] :=
    ⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hdet]; exact hz), rfl⟩
  have e0 : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))) (i : Fin 2),
      ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 0 =
        (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 0 := by
    intro γ i
    rw [Units.val_mul, hD]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))) (i : Fin 2),
      ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 1 =
        (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))) i 1 * (β : ZMod (l ^ m)) := by
    intro γ i
    rw [Units.val_mul, hD, hβ]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have ed : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))),
      ((γ * D : GL (Fin 2) (ZMod (l ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det =
        (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det * z₀ := by
    intro γ
    rw [Units.val_mul, Matrix.det_mul, hD, hdet]
  have eψ : ∀ (γ : GL (Fin 2) (ZMod (l ^ m))),
      (1 : DirichletCharacter K (l ^ m))
        (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) = 1 := by
    intro γ
    rw [ZMod.natCast_zmod_val]
    exact MulChar.one_apply (Matrix.isUnits_det_units γ)
  unfold pieceT
  congr 1
  symm
  refine Finset.sum_equiv (Equiv.mulRight D) (fun γ => ?_) (fun γ _ => ?_)
  · simp only [Finset.mem_filter, unitSet, Finset.mem_univ, true_and, Equiv.coe_mulRight, e0, ed, ZMod.natCast_zmod_val]
    refine and_congr_right fun _ => ⟨fun h => by rw [h, one_mul], fun h => ?_⟩
    exact hz.mul_right_cancel (by rw [h, one_mul])
  · simp only [Equiv.coe_mulRight, eψ, rowT, e0, e1]
    rw [siegel_function_root_power_eq l N m _ c _ ζ β hN hζ, siegel_function_root_power_eq l N m _ d _ ζ β hN hζ]
