import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternSetCardColumnStepStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonalityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerColumnRecursionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalUnipotentRadicalSumZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishesOfRadicalSumsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GLTransitiveNonzeroVectorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockEmbeddingGLInverseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerBlockEmbeddingConjStatement

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

/- English proof (translation)
Use function extensionality and compare the values at `i l`. Distinguish the cases in `hl : (l : ℕ) = j`. Distinguish the cases in `hi : (l : ℕ) = i + 1`. Establish `hlt : (i : ℕ) < j` using `by omega`. Establish `hij : (⟨(i : ℕ), hlt⟩ : Fin j) = ⟨j - 1, by omega⟩` using `Fin.ext (by simp; omega)`.

Simplify using `only [colGeR, colGeE]`. Rewrite using `[dif_pos ⟨hl, hlt⟩, hij]`. Simplify using `[hl, hi]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [colGeR, colGeE]`.

Distinguish the cases in `hlt : (i : ℕ) < j`. Rewrite using `[dif_pos ⟨hl, hlt⟩]`. Establish `hne : (⟨(i : ℕ), hlt⟩ : Fin j) ≠ ⟨j - 1, by omega⟩`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `[hi, Pi.single_eq_of_ne hne]`. Rewrite using `[dif_neg (by tauto)]`. Simplify using `[hi]`.

Simplify using `only [colGeR, colGeE]`. Rewrite using `[dif_neg (by tauto)]`. Establish `: (j + 1 ≤ (l : ℕ)) ↔ j ≤ (l : ℕ)` using `by omega`. Simplify using `[this]`.
-/
theorem colGeR_single (K : Type) [Field K] (d j : ℕ) (hj : 1 ≤ j) :
    colGeR K d j (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) = colGeE K d j := by
  funext i l
  by_cases hl : (l : ℕ) = j
  · by_cases hi : (l : ℕ) = i + 1
    · have hlt : (i : ℕ) < j := by omega
      have hij : (⟨(i : ℕ), hlt⟩ : Fin j) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
      simp only [colGeR, colGeE]
      rw [dif_pos ⟨hl, hlt⟩, hij]
      simp [hl, hi]
      omega
    · simp only [colGeR, colGeE]
      by_cases hlt : (i : ℕ) < j
      · rw [dif_pos ⟨hl, hlt⟩]
        have hne : (⟨(i : ℕ), hlt⟩ : Fin j) ≠ ⟨j - 1, by omega⟩ := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp [hi, Pi.single_eq_of_ne hne]
      · rw [dif_neg (by tauto)]
        simp [hi]
  · simp only [colGeR, colGeE]
    rw [dif_neg (by tauto)]
    have : (j + 1 ≤ (l : ℕ)) ↔ j ≤ (l : ℕ) := by omega
    simp [this]

/- English proof (translation)
Establish `hs : (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) ≠ 0`. Introduce `h`. Use `congrFun h ⟨j - 1, by omega⟩` as an intermediate fact. Simplify using `at this`. Take `⟨g, hg⟩` from `GlobalTheory.T.GL_transitive_nonzero_vectors K j r _ hr hs`.

Take `⟨h, h1, h2⟩` from `GlobalTheory.T.block_embedding_GL_inverse K d j hd.le g`. Rewrite using `[GlobalTheory.T.whittaker_block_embedding_conj K d j ψ₀ χ g h r hd hχ h1 h2, hg, colGeR_single K d j hj]`.
-/
theorem wh_row_ne_zero (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ) (hj : 1 ≤ j) (hd : j < d) (hχ : ∀ x y, χ (x * y * x⁻¹) = χ y)
    (r : Fin j → K) (hr : r ≠ 0) :
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeE K d j) ψ₀ χ := by
  have hs : (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨j - 1, by omega⟩
    simp at this
  obtain ⟨g, hg⟩ := GlobalTheory.T.GL_transitive_nonzero_vectors K j r _ hr hs
  obtain ⟨h, h1, h2⟩ := GlobalTheory.T.block_embedding_GL_inverse K d j hd.le g
  rw [GlobalTheory.T.whittaker_block_embedding_conj K d j ψ₀ χ g h r hd hχ h1 h2, hg, colGeR_single K d j hj]

/- English proof (translation)
Rewrite using `[GlobalTheory.T.whittaker_column_recursion K d j ψ₀ τ.character hd (GlobalTheory.T.pattern_set_card_column_step K d j hd) (GlobalTheory.T.additive_character_sum_orthogonality K j ψ₀ hψ)]`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin j → K)), GlobalTheory.T.whittaker_vanishes_of_radical_sums K d j ψ₀ τ.character (GlobalTheory.T.cuspidal_unipotent_radical_sum_zero K d j τ hj hd hτ), zero_add, Finset.sum_congr rfl (fun r hr => wh_row_ne_zero K d j ψ₀ τ.chara …`. Rewrite using `[Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]`. Establish `h1 : 1 ≤ Fintype.card K ^ j` using `Nat.one_le_pow _ _ Fintype.card_pos`. Rewrite using `[Nat.cast_sub h1]`.

Simplify using the standard rewrite rules.
-/
theorem wh_step (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (hj : 1 ≤ j) (hd : j < d) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ τ.character =
      ((Fintype.card K : ℂ) ^ j - 1) * wh (colGe d j) (colGeE K d j) ψ₀ τ.character := by
  rw [GlobalTheory.T.whittaker_column_recursion K d j ψ₀ τ.character hd (GlobalTheory.T.pattern_set_card_column_step K d j hd) (GlobalTheory.T.additive_character_sum_orthogonality K j ψ₀ hψ)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin j → K)),
    GlobalTheory.T.whittaker_vanishes_of_radical_sums K d j ψ₀ τ.character (GlobalTheory.T.cuspidal_unipotent_radical_sum_zero K d j τ hj hd hτ), zero_add,
    Finset.sum_congr rfl (fun r hr => wh_row_ne_zero K d j ψ₀ τ.character hj hd
      (fun x y => FDRep.char_conj τ y x) r (Finset.ne_of_mem_erase hr))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  have h1 : 1 ≤ Fintype.card K ^ j := Nat.one_le_pow _ _ Fintype.card_pos
  rw [Nat.cast_sub h1]
  simp

/- English proof (translation)
Establish `hset : patSet K (colGe d d) = {1}`. Use extensionality with `u`. Simplify using `only [patSet, Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use extensionality with `i l`. Distinguish the cases in `hil : i = l`. Substitute `hil` using the available equality. Simplify using `using (h i i).1 rfl`. Use `(h i l).2 hil (fun hc => by have := hc.2; have := l.2; omega)` as an intermediate fact.

Simplify using `[this, Matrix.one_apply_ne hil]`. Introduce and unpack `rfl i l`. Conclude with `⟨fun h => by simp [h], fun h _ => by simp [Matrix.one_apply_ne h]⟩`. Establish `hE : patChar (colGeE K d d) ψ₀ (1 : GL (Fin d) K) = 1`. Establish `: ∀ i l : Fin d, colGeE K d d i l = 0`.

Introduce `i l`. Simplify using `only [colGeE]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨-, h⟩`. Use `l.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `[patChar, this]`. Simplify using `only [wh, hset, Set.ncard_singleton, Set.mem_singleton_iff]`. Simplify using `[hE, FDRep.char_one]`.
-/
theorem wh_top (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) :
    wh (colGe d d) (colGeE K d d) ψ₀ τ.character = (Module.finrank ℂ τ : ℂ) := by
  classical
  have hset : patSet K (colGe d d) = {1} := by
    ext u
    simp only [patSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      ext i l
      by_cases hil : i = l
      · subst hil; simpa using (h i i).1 rfl
      · have := (h i l).2 hil (fun hc => by have := hc.2; have := l.2; omega)
        simp [this, Matrix.one_apply_ne hil]
    · rintro rfl i l
      exact ⟨fun h => by simp [h], fun h _ => by simp [Matrix.one_apply_ne h]⟩
  have hE : patChar (colGeE K d d) ψ₀ (1 : GL (Fin d) K) = 1 := by
    have : ∀ i l : Fin d, colGeE K d d i l = 0 := by
      intro i l
      simp only [colGeE]
      rw [if_neg]
      rintro ⟨-, h⟩
      have := l.2
      omega
    simp [patChar, this]
  simp only [wh, hset, Set.ncard_singleton, Set.mem_singleton_iff]
  simp [hE, FDRep.char_one]

/- English proof (translation)
Establish `h1 : colGe d 1 = fun i j : Fin d => i < j`. Use function extensionality and compare the values at `i l`. Simplify using `only [colGe, eq_iff_iff, and_iff_left_iff_imp]`. Introduce `h`. Establish `: (i : ℕ) < l` using `h`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : colGeE K d 1 = cutE K d 0`. Use function extensionality and compare the values at `i l`. Simplify using `only [colGeE, cutE]`. Use `congr 1`.

Apply `propext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, h2]`.
-/
theorem wh_one_eq (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) :
    wh (colGe d 1) (colGeE K d 1) ψ₀ χ = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ χ := by
  have h1 : colGe d 1 = fun i j : Fin d => i < j := by
    funext i l
    simp only [colGe, eq_iff_iff, and_iff_left_iff_imp]
    intro h
    have : (i : ℕ) < l := h
    omega
  have h2 : colGeE K d 1 = cutE K d 0 := by
    funext i l
    simp only [colGeE, cutE]
    congr 1
    apply propext
    omega
  rw [h1, h2]

/- English proof (translation)
Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ k hk ih`. Rewrite using `[wh_step K d k ψ₀ τ hψ hτ hk (by omega), ih (by omega), Finset.prod_Ico_succ_top hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wh_prod (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    wh (colGe d k) (colGeE K d k) ψ₀ τ.character =
      wh (colGe d 1) (colGeE K d 1) ψ₀ τ.character * ∏ i ∈ Finset.Ico 1 k, ((Fintype.card K : ℂ) ^ i - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [wh_step K d k ψ₀ τ hψ hτ hk (by omega), ih (by omega), Finset.prod_Ico_succ_top hk]
    ring

/- English proof (translation)
Introduce `K _ _ _ d ψ₀ τ hψ hτ`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Rewrite using `[← wh_top K 0 ψ₀ τ]`. Establish `h1 : colGe 0 0 = fun i j : Fin 0 => i < j`. Use function extensionality and compare the values at `i`.

Conclude with `i.elim0`. Establish `h2 : colGeE K 0 0 = cutE K 0 0`. Use function extensionality and compare the values at `i`. Conclude with `i.elim0`. Rewrite using `[h1, h2]`.

Simplify using the standard rewrite rules. Rewrite using `[← wh_top K d ψ₀ τ, wh_prod K d ψ₀ τ hψ hτ d hd le_rfl, wh_one_eq]`.
-/
theorem cuspWh : ReciprocityTheory.Ty.Fin.St.CuspWh := by
  intro K _ _ _ d ψ₀ τ hψ hτ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [← wh_top K 0 ψ₀ τ]
    have h1 : colGe 0 0 = fun i j : Fin 0 => i < j := by
      funext i; exact i.elim0
    have h2 : colGeE K 0 0 = cutE K 0 0 := by
      funext i; exact i.elim0
    rw [h1, h2]
    simp
  · rw [← wh_top K d ψ₀ τ, wh_prod K d ψ₀ τ hψ hτ d hd le_rfl, wh_one_eq]

end GlobalTheory.CompanionTheory.TyFin.ColStep
