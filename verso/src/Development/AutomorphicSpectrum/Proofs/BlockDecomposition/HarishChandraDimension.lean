import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraCharacterStatement

open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

/- English proof (translation)
Unfold `blkGL`. Rewrite using `[dif_pos (one_mem _)]`. Apply `Units.ext` to reduce the goal to its premises. Use `show Formalism.IrreducibleCountingLemmas.TYPES.blk K b c ((1 : GL ι K) : Matrix ι ι K) = 1`. Use extensionality with `i j`.

Simplify using `[Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.one_apply, Subtype.ext_iff]`.
-/
theorem blkGL_one_eq {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s) :
    blkGL b c (1 : GL ι K) = 1 := by
  unfold blkGL
  rw [dif_pos (one_mem _)]
  apply Units.ext
  show Formalism.IrreducibleCountingLemmas.TYPES.blk K b c ((1 : GL ι K) : Matrix ι ι K) = 1
  ext i j
  simp [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.one_apply, Subtype.ext_iff]

/- English proof (translation)
Unfold `indF`. Use `congr 1`. Establish `h : ∀ x : Γ, x * 1 * x⁻¹ = 1` using `fun x => by group`. Simplify using `only [h, one_mem, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`.
-/
theorem indF_one_eq {Γ : Type} [Group Γ] [Fintype Γ] (H : Subgroup Γ) (φ : Γ → ℂ) :
    indF H φ 1 = (Nat.card H : ℂ)⁻¹ * ((Nat.card Γ : ℂ) * φ 1) := by
  classical
  unfold indF
  congr 1
  have h : ∀ x : Γ, x * 1 * x⁻¹ = 1 := fun x => by group
  simp only [h, one_mem, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

/- English proof (translation)
Introduce `K _ _ _ ι _ _ s b lam`. Establish `h` using `congrFun (GlobalTheory.T.harish_chandra_character K ι s b lam).1 1`. Rewrite `h` using `[Representation.char_one, indF_one_eq]`. Establish `hf : hcFun b (fun c => (lam c).character) (1 : GL ι K) = ((∏ c, Module.finrank ℂ (lam c) : ℕ) : ℂ)`. Unfold `hcFun`.

Use `push_cast`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[blkGL_one_eq, FDRep.char_one]`. Rewrite `h` using `[hf]`. Establish `hP : (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`.

Establish `h2 : ((Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace K b lam) * Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℕ) : ℂ) = ((Nat.card (GL ι K) * ∏ c, Module.finrank ℂ (lam c) : ℕ) : ℂ)`. Rewrite using `[Nat.cast_mul, h, Nat.cast_mul]`. Clear the denominators using the available nonvanishing facts. Conclude with `h2` after adjusting the coercions.
-/
theorem hcDim : ReciprocityTheory.Ty.Fin.St.HCDim := by
  intro K _ _ _ ι _ _ s b lam
  have h := congrFun (GlobalTheory.T.harish_chandra_character K ι s b lam).1 1
  rw [Representation.char_one, indF_one_eq] at h
  have hf : hcFun b (fun c => (lam c).character) (1 : GL ι K)
      = ((∏ c, Module.finrank ℂ (lam c) : ℕ) : ℂ) := by
    unfold hcFun
    push_cast
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [blkGL_one_eq, FDRep.char_one]
  rw [hf] at h
  have hP : (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h2 : ((Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace K b lam) *
      Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℕ) : ℂ) =
      ((Nat.card (GL ι K) * ∏ c, Module.finrank ℂ (lam c) : ℕ) : ℂ) := by
    rw [Nat.cast_mul, h, Nat.cast_mul]
    field_simp
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.TyFin
