import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Avg

open Classical in

/- English proof (translation)
Use `set S : ℂ := ∑ u : G, if u ∈ N then L u * χ u else 0 with hS`. Establish `hv : ∀ v ∈ A, (∑ u : G, if u ∈ N then L u * χ (u * v) else 0) = S`. Introduce `v hvA`. Rewrite using `[hS, ← Equiv.sum_comp (Equiv.mulRight v) (fun u => if u ∈ N then L u * χ u else 0)]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulRight, hN v hvA u]`. Use `split_ifs with hu`. Rewrite using `[hL u hu v hvA]`. Both sides reduce to the same expression. Establish `h2 : (∑ v : G, if v ∈ A then S else 0) = 0`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Use `split_ifs with hvA`. Conclude with `(hv v hvA).symm`. Simplify using the standard rewrite rules.

Use `_ = ∑ u : G, ∑ v : G, if v ∈ A then (if u ∈ N then L u * χ (u * v) else 0) else 0 := Finset.sum_comm`. Use `_ = ∑ u : G, if u ∈ N then L u * ∑ v : G, (if v ∈ A then χ (u * v) else 0) else 0 := by`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Use `split_ifs with hu`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Simplify using the standard rewrite rules. Use `_ = 0 := by`. Use `Finset.sum_eq_zero fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[hs u]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`. Establish `hc : (((Finset.univ.filter fun v => v ∈ A).card : ℕ) : ℂ) ≠ 0`. Apply `Nat.cast_ne_zero.2` to reduce the goal to its premises.

Conclude with `(Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'`. Conclude with `(mul_eq_zero.1 h2).resolve_left hc`.
-/
theorem sum_eq_zero_of_translates {G : Type} [Group G] [Fintype G] (N A : Set G) (h1 : (1 : G) ∈ A)
    (hN : ∀ v ∈ A, ∀ u, u * v ∈ N ↔ u ∈ N) (L χ : G → ℂ)
    (hL : ∀ u ∈ N, ∀ v ∈ A, L (u * v) = L u)
    (hs : ∀ u, (∑ v : G, if v ∈ A then χ (u * v) else 0) = 0) :
    (∑ u : G, if u ∈ N then L u * χ u else 0) = 0 := by
  set S : ℂ := ∑ u : G, if u ∈ N then L u * χ u else 0 with hS
  have hv : ∀ v ∈ A, (∑ u : G, if u ∈ N then L u * χ (u * v) else 0) = S := by
    intro v hvA
    rw [hS, ← Equiv.sum_comp (Equiv.mulRight v) (fun u => if u ∈ N then L u * χ u else 0)]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Equiv.coe_mulRight, hN v hvA u]
    split_ifs with hu
    · rw [hL u hu v hvA]
    · rfl
  have h2 : (∑ v : G, if v ∈ A then S else 0) = 0 := by
    calc (∑ v : G, if v ∈ A then S else 0)
        = ∑ v : G, ∑ u : G, if v ∈ A then (if u ∈ N then L u * χ (u * v) else 0) else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          split_ifs with hvA
          · exact (hv v hvA).symm
          · simp
      _ = ∑ u : G, ∑ v : G, if v ∈ A then (if u ∈ N then L u * χ (u * v) else 0) else 0 :=
          Finset.sum_comm
      _ = ∑ u : G, if u ∈ N then L u * ∑ v : G, (if v ∈ A then χ (u * v) else 0) else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          split_ifs with hu
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => ?_
            split_ifs <;> simp
          · simp
      _ = 0 := by
          refine Finset.sum_eq_zero fun u _ => ?_
          rw [hs u]
          simp
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h2
  have hc : (((Finset.univ.filter fun v => v ∈ A).card : ℕ) : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.2
    exact (Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'
  exact (mul_eq_zero.1 h2).resolve_left hc

/- English proof (translation)
Use function extensionality and compare the values at `i l`. Simplify using `[colGeR]`.
-/
theorem colGeR_zero (K : Type) [Field K] (d j : ℕ) : colGeR K d j 0 = colGeE K d (j + 1) := by
  funext i l
  simp [colGeR]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i h => lt_irrefl _ h.1, fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2⟩⟩`.
-/
theorem isPat_colGe (d j : ℕ) : IsPat (colGe d j) :=
  ⟨fun i h => lt_irrefl _ h.1, fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2⟩⟩

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d j : ℕ}

/- English proof (translation)
Use `hv.2 k l ?_` and prove the remaining obligations. Simplify using `[Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, not_lt.2 hk, not_lt.2 hl]`.
-/
theorem unip_entry {v : GL (Fin d) K} (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j))
    {k l : Fin d} (hk : j ≤ (k : ℕ)) (hl : j ≤ (l : ℕ)) :
    (v : Matrix (Fin d) (Fin d) K) k l = if k = l then 1 else 0 := by
  refine hv.2 k l ?_
  simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, not_lt.2 hk, not_lt.2 hl]

/- English proof (translation)
Introduce `i l`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Use `hv.2 i i rfl` as an intermediate fact. Simplify using `using this`.

Introduce `e hn`. Distinguish the cases in `hi : (i : ℕ) < j`. Distinguish the cases in `hl : (l : ℕ) < j`. Use `hv.2 i l (by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, hi, hl])` as an intermediate fact. Simplify `this` using `[e]`.

Conclude with `absurd ⟨Fin.lt_def.2 (by`. Use `not_lt.1 hl` as an intermediate fact. Use the proof step `omega), not_lt.1 hl⟩ hn`. Distinguish the cases in `hl : (l : ℕ) < j`. Use `hv.1.1 i l ?_` and prove the remaining obligations.

Simplify using `[Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, hi, hl]`. Apply the tactic sequence `have := unip_entry hv (not_lt.1 hi) (not_lt.1 hl)`. Simplify `this` using `[e]`.
-/
theorem unip_subset_patSet {v : GL (Fin d) K}
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) :
    v ∈ patSet K (colGe d j) := by
  intro i l
  constructor
  · rintro rfl
    have := hv.2 i i rfl
    simpa using this
  · intro e hn
    by_cases hi : (i : ℕ) < j
    · by_cases hl : (l : ℕ) < j
      · have := hv.2 i l (by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, hi, hl])
        simpa [e] using this
      · exact absurd ⟨Fin.lt_def.2 (by
          have := not_lt.1 hl
          omega), not_lt.1 hl⟩ hn
    · by_cases hl : (l : ℕ) < j
      · refine hv.1.1 i l ?_
        simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock, hi, hl]
      · have := unip_entry hv (not_lt.1 hi) (not_lt.1 hl)
        simpa [e] using this

/- English proof (translation)
Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single l]`. Apply the tactic sequence `rw [unip_entry hv hl hl]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Distinguish the cases in `hik : (u : Matrix (Fin d) (Fin d) K) i k = 0`.

Simplify using `[hik]`. Establish `hjk : j ≤ (k : ℕ)`. Distinguish the cases in `e : i = k`. Conclude with `e ▸ hi`. Assume the negation of the conclusion as `hn`.

Conclude with `hik ((hu i k).2 e fun h => hn h.2)`. Apply the tactic sequence `rw [unip_entry hv hjk hl, if_neg hk, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem mul_entry {u v : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j))
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) {i l : Fin d}
    (hi : j ≤ (i : ℕ)) (hl : j ≤ (l : ℕ)) :
    ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i l = (u : Matrix (Fin d) (Fin d) K) i l := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single l]
  · rw [unip_entry hv hl hl]
    simp
  · intro k _ hk
    by_cases hik : (u : Matrix (Fin d) (Fin d) K) i k = 0
    · simp [hik]
    · have hjk : j ≤ (k : ℕ) := by
        by_cases e : i = k
        · exact e ▸ hi
        · by_contra hn
          exact hik ((hu i k).2 e fun h => hn h.2)
      rw [unip_entry hv hjk hl, if_neg hk, mul_zero]
  · simp

/- English proof (translation)
Unfold `patChar`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (l : ℕ) = i + 1 ∧ j + 1 ≤ (l : ℕ)`. Apply the tactic sequence `rw [mul_entry hu hv (by omega) (by omega)]`.

Establish `hz : colGeE K d (j + 1) i l = 0` using `if_neg h`. Rewrite using `[hz, zero_mul, zero_mul]`.
-/
theorem patChar_mul_unip (ψ₀ : AddChar K ℂ) {u v : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j))
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) :
    patChar (colGeE K d (j + 1)) ψ₀ (u * v) = patChar (colGeE K d (j + 1)) ψ₀ u := by
  unfold patChar
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases h : (l : ℕ) = i + 1 ∧ j + 1 ≤ (l : ℕ)
  · rw [mul_entry hu hv (by omega) (by omega)]
  · have hz : colGeE K d (j + 1) i l = 0 := if_neg h
    rw [hz, zero_mul, zero_mul]

/- English proof (translation)
Rewrite using `[colGeR_zero]`. Unfold `wh`. Establish `h1 : (1 : GL (Fin d) K) ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)`. Use `⟨one_mem _, fun i l _ => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`.

Establish `hP` using `isPat_colGe d j`. Establish `hN : ∀ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j), ∀ u : GL (Fin d) K, u * v ∈ patSet K (colGe d j) ↔ u ∈ patSet K (colGe d j)`. Introduce `v hv u`. Establish `hv' : v ∈ GlobalTheory.CompanionTheory.PatGrp.patSubgroup (K` using `K) hP := unip_subset_patSet hv`. Conclude with `(GlobalTheory.CompanionTheory.PatGrp.patSubgroup (K := K) hP).mul_mem_cancel_right hv'`.

Establish `key` using `sum_eq_zero_of_translates (patSet K (colGe d j)) (Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) h1 hN (fun u => (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹) χ (fun u hu v hv => by simp only [patChar_mul_unip ψ₀ hu hv]) (by si …`. Rewrite using `[key, mul_zero]`.
-/
theorem wh_zero_row (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ)
    (hs : ∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) :
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  classical
  rw [colGeR_zero]
  unfold wh
  have h1 : (1 : GL (Fin d) K) ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) := by
    refine ⟨one_mem _, fun i l _ => ?_⟩
    simp [Matrix.one_apply]
  have hP := isPat_colGe d j
  have hN : ∀ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j), ∀ u : GL (Fin d) K,
      u * v ∈ patSet K (colGe d j) ↔ u ∈ patSet K (colGe d j) := by
    intro v hv u
    have hv' : v ∈ GlobalTheory.CompanionTheory.PatGrp.patSubgroup (K := K) hP := unip_subset_patSet hv
    exact (GlobalTheory.CompanionTheory.PatGrp.patSubgroup (K := K) hP).mul_mem_cancel_right hv'
  have key := sum_eq_zero_of_translates (patSet K (colGe d j))
    (Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) h1 hN
    (fun u => (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹) χ
    (fun u hu v hv => by simp only [patChar_mul_unip ψ₀ hu hv]) (by simpa using hs)
  rw [key, mul_zero]

/- English proof (translation)
Introduce `K _ _ _ d j ψ₀ χ hs`. Conclude with `wh_zero_row K d j ψ₀ χ hs`.
-/
theorem wh_zero_row' : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ),
    (∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) →
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  intro K _ _ _ d j ψ₀ χ hs
  exact wh_zero_row K d j ψ₀ χ hs

end GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
