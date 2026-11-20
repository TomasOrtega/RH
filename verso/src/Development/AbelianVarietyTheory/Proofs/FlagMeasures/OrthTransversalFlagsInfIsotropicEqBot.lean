import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PerpFlags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf]`.
-/
theorem mem_orth (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

/- English proof (translation)
Introduce `v hv` and use `(mem_orth _ _).2 fun x hx => (mem_orth _ _).1 hv x (h hx)`.
-/
theorem orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := fun v hv =>
  (mem_orth _ _).2 fun x hx => (mem_orth _ _).1 hv x (h hx)

/- English proof (translation)
Use `sup_le (fun v hv => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span h2))` and prove the remaining obligations. Take `⟨d, hd0, hd⟩` from `GlobalTheory.Mass.RowPerp.exists_smul_mem hΛ v`. Establish `h3 : d • v ∈ M` using `h1 ⟨hd, (toO S (Xsp F)).smul_mem d hv⟩`. Establish `h4` using `Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h3)`. Rewrite `h4` using `[← algebraMap_smul E d v, inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)]`. Then use the resulting hypothesis.
-/
theorem xplus_le {T : E} {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T)
    (M : Submodule (𝓞 E) S.V) (h1 : XLam Λ F ≤ M) (h2 : F.fl.z ∈ M) : Xplus F ≤ spanE S M := by
  refine sup_le (fun v hv => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span h2))
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hΛ v
  have h3 : d • v ∈ M := h1 ⟨hd, (toO S (Xsp F)).smul_mem d hv⟩
  have h4 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h3)
  rwa [← algebraMap_smul E d v,
    inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h4

/- English proof (translation)
Establish `hz : ∀ b, ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b = 0` using `fun b => by`. Use `h b` as an intermediate fact. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at this`. Simplify `this` using `[Zhat, brS, FlagG.fvec]`. Take `⟨a0, ha0⟩` from `Function.ne_iff.1 hc`.

Establish `d1 : Dl F F' r = 0`. Rewrite using `[Dl, leadMinorE, dif_pos (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]`. Use `⟨fun a => star (c a), fun e => ha0 (star_eq_zero.1 (congrFun e a0)), funext fun b => ?_⟩` and prove the remaining obligations. Conclude with `hz (Fin.castLE (Nat.le_succ r) b)`. Establish `d2 : Dl F F' (r + 1) = 0`.

Rewrite using `[Dl, leadMinorE, dif_pos le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]`. Use `⟨Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0, fun e => ha0 ?_, funext fun b => ?_⟩` and prove the remaining obligations. Simplify using `using congrFun e a0.castSucc`. Simplify `hz b` using `[Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc]`. Simplify using `[Gflag, d1, d2]`.
-/
theorem gflag_eq_zero {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c : Fin r → E) (hc : c ≠ 0)
    (h : ∀ b, S.hT (∑ a, c a • F.e a) (F'.fvec b) = 0) : Gflag F F' = 0 := by
  have hz : ∀ b, ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b = 0 := fun b => by
    have := h b
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply] at this
    simpa [Zhat, brS, FlagG.fvec] using this
  obtain ⟨a0, ha0⟩ := Function.ne_iff.1 hc
  have d1 : Dl F F' r = 0 := by
    rw [Dl, leadMinorE, dif_pos (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨fun a => star (c a), fun e => ha0 (star_eq_zero.1 (congrFun e a0)), funext fun b => ?_⟩
    exact hz (Fin.castLE (Nat.le_succ r) b)
  have d2 : Dl F F' (r + 1) = 0 := by
    rw [Dl, leadMinorE, dif_pos le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0, fun e => ha0 ?_, funext fun b => ?_⟩
    · simpa using congrFun e a0.castSucc
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc] using hz b
  simp [Gflag, d1, d2]

/- English proof (translation)
Introduce `E _ _ _ S r T T' Λ F F' hΛ hF hF' hG`. Establish `a1 : Hp Λ F F' ≤ orth S (Xplus F)` using `orth_anti (xplus_le hΛ F _ (le_sup_of_le_left (le_sup_of_le_left le_sup_left)) (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (hF.2 ▸ Submodule.mem_span_singleton_self _)))))`. Establish `a2 : Hp Λ F F' ≤ orth S (Xplus F')` using `orth_anti (xplus_le hΛ F' _ (le_sup_of_le_left le_sup_right) (Submodule.mem_sup_right (hF'.2 ▸ Submodule.mem_span_singleton_self _)))`. Use `⟨a1, a2, eq_bot_iff.2 fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hx.2`.

Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Use `absurd (gflag_eq_zero F.fl F'.fl c hc fun b => ?_) hG` and prove the remaining obligations. Use `GlobalTheory.Mass.RowPerp.swap_zero S.herm ((mem_orth _ _).1 (a2 hx.1) _ ?_)` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun i => ?_) b` and prove the remaining obligations.

Rewrite using `[FlagG.fvec, Fin.snoc_last]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Rewrite using `[FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → Hp Λ F F' ≤ orth S (Xplus F) ∧ Hp Λ F F' ≤ orth S (Xplus F') ∧ Hp Λ F F' ⊓ Xsp F = ⊥ := by
  intro E _ _ _ S r T T' Λ F F' hΛ hF hF' hG
  have a1 : Hp Λ F F' ≤ orth S (Xplus F) := orth_anti (xplus_le hΛ F _
    (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (hF.2 ▸ Submodule.mem_span_singleton_self _)))))
  have a2 : Hp Λ F F' ≤ orth S (Xplus F') := orth_anti (xplus_le hΛ F' _
    (le_sup_of_le_left le_sup_right)
    (Submodule.mem_sup_right (hF'.2 ▸ Submodule.mem_span_singleton_self _)))
  refine ⟨a1, a2, eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx.2
  by_cases hc : c = 0
  · simp [hc]
  refine absurd (gflag_eq_zero F.fl F'.fl c hc fun b => ?_) hG
  refine GlobalTheory.Mass.RowPerp.swap_zero S.herm ((mem_orth _ _).1 (a2 hx.1) _ ?_)
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · rw [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.LoopC.PerpFlags
