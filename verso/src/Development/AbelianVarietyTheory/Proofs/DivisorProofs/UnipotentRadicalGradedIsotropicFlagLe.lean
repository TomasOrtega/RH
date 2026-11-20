import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd`. Break down `S.eq_empty_or_nonempty with rfl | hne` into its components or cases. Establish `hs0 : s = 0`. Assume the negation of the conclusion as `h0`. Take `⟨k, hk, -⟩` from `(hS ⟨0, by omega⟩).1 (by simp only; omega)`.

Simplify using `at hk`. Substitute `hs0` using the available equality. Rewrite using `[GlobalTheory.StdPar.unip_empty]`. Use `(Subgroup.closure_le _).2 fun g hg => ?_` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Subgroup.mem_bot]`.

Use `Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations. Take `⟨a, ha⟩` from `hg.2 (Pi.single j 1) (Subsingleton.elim _ _)`. Establish `h0 : adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = 0` using `funext fun _ => by simp [Matrix.mulVec, dotProduct]`. Establish `hv : (fun i => inclR (F` using `F) (AF F) ((Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j 1 := by`. Use function extensionality and compare the values at `l`.

Distinguish the cases in `hl : l = j`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hl]`. Rewrite `ha` using `[h0, hv, sub_mulVec, one_mulVec, sub_eq_zero, mulVec_single_one]`.

Conclude with `(congrFun ha i).trans (Pi.single_apply _ _ _)`. Take `⟨m, hmS, hmax⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m` from `⟨S.max' hne, S.max'_mem hne, fun k hk => S.le_max' k hk⟩`. Establish `hsm : s = m.val + 1`. Apply `le_antisymm` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt push_neg at hlt`.

Take `⟨k, hk, hle⟩` from `(hS ⟨m.val + 1, by omega⟩).1 (by simp only; omega)`. Establish `h2` using `hmax k hk`. Rewrite `hle`, `h2` using `[Fin.le_def]`. Simplify using `only at hle`. Use linear arithmetic over natural numbers and integers.

Use `(hS m).2 ⟨m, hmS, le_rfl⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Substitute `hsm` using the available equality. Establish `hd' : d = fun i => (S.filter fun k => k.val < i.val).card`. Use function extensionality and compare the values at `i`.

Rewrite using `[hd i]`. Use `congr 1`. Substitute `hd'` using the available equality. Conclude with `GlobalTheory.FlagRad.unipFlag_le_unip F E σ h n J hJ r X Y hW S m hmS hmax`.
-/
theorem unipFlag_castLE_le_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hs0 : s = 0 := by
      by_contra h0
      obtain ⟨k, hk, -⟩ := (hS ⟨0, by omega⟩).1 (by simp only; omega)
      simp at hk
    subst hs0
    rw [GlobalTheory.StdPar.unip_empty]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    obtain ⟨a, ha⟩ := hg.2 (Pi.single j 1) (Subsingleton.elim _ _)
    have h0 : adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = 0 := funext fun _ => by simp [Matrix.mulVec, dotProduct]
    have hv : (fun i => inclR (F := F) (AF F) ((Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    rw [h0, hv, sub_mulVec, one_mulVec, sub_eq_zero, mulVec_single_one] at ha
    exact (congrFun ha i).trans (Pi.single_apply _ _ _)
  · obtain ⟨m, hmS, hmax⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' hne, S.max'_mem hne, fun k hk => S.le_max' k hk⟩
    have hsm : s = m.val + 1 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk, hle⟩ := (hS ⟨m.val + 1, by omega⟩).1 (by simp only; omega)
        have h2 := hmax k hk
        rw [Fin.le_def] at hle h2
        simp only at hle
        omega
      · have := (hS m).2 ⟨m, hmS, le_rfl⟩
        omega
    subst hsm
    have hd' : d = fun i => (S.filter fun k => k.val < i.val).card := by
      funext i
      rw [hd i]
      congr 1
    subst hd'
    exact GlobalTheory.FlagRad.unipFlag_le_unip F E σ h n J hJ r X Y hW S m hmS hmax

end GlobalTheory.TieStd
