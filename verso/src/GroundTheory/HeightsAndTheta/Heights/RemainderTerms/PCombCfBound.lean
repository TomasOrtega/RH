import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

namespace CombCfBound

/- English proof (translation)
Rewrite using `[cf_perm hP σ v, abs_mul]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]`.
-/
theorem abs_cf_perm {m : ℕ} {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (σ : Perm (Fin m))
    (v : Fin m → ℕ) : |cf (v ∘ σ.symm) P| = |cf v P| := by
  rw [cf_perm hP σ v, abs_mul]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]

/- English proof (translation)
Unfold `alternantPsum`. Simplify using `only [List.map_cons, List.prod_cons]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alternantPsum_cons (m q : ℕ) (ρ : List ℕ) :
    alternantPsum m (q :: ρ) = alternantPsum m ρ * psum (Fin m) ℚ q := by
  unfold alternantPsum
  simp only [List.map_cons, List.prod_cons]
  ring

/- English proof (translation)
The claim follows from `isAlt_vandermonde_mul_prod ρ`.
-/
theorem isAlt_alternantPsum (m : ℕ) (ρ : List ℕ) : IsAlt (alternantPsum m ρ) :=
  isAlt_vandermonde_mul_prod ρ

/- English proof (translation)
Introduce `i j h`. Establish `hij : (i : ℕ) < j` using `h`. Use `j.isLt` as an intermediate fact. Simplify using `only [stair]`. Use linear arithmetic over natural numbers and integers.
-/
theorem stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro i j h
  have hij : (i : ℕ) < j := h
  have := j.isLt
  simp only [stair]
  omega

/- English proof (translation)
The claim follows from `|cf (fun i => lam i + stair m i) (alternantPsum m [])| ≤ ((latticeWords 0 lam).card : ℚ) := by have hA : alternantPsum m [] = alt (stair m) := by simp [alternantPsum, vandermondeOf_X_eq_alt] have hl : StrictAnti (fun i => lam i + stair m i) := fun i j h => Nat.add_lt_add_of_le_of …`.
-/
theorem bound_nil (m : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    |cf (fun i => lam i + stair m i) (alternantPsum m [])| ≤ ((latticeWords 0 lam).card : ℚ) := by
  have hA : alternantPsum m [] = alt (stair m) := by
    simp [alternantPsum, vandermondeOf_X_eq_alt]
  have hl : StrictAnti (fun i => lam i + stair m i) := fun i j h =>
    Nat.add_lt_add_of_le_of_lt (hlam h.le) (stair_strictAnti m h)
  rw [hA, cf_alt_of_strictAnti hl (stair_strictAnti m)]
  split_ifs with h
  · have h0 : lam = 0 := by
      funext i
      have := congrFun h i
      show lam i = 0
      omega
    subst h0
    have hne : (latticeWords 0 (0 : Fin m → ℕ)).Nonempty := by
      refine ⟨Fin.elim0, ?_⟩
      simp only [latticeWords, mem_filter, mem_univ, true_and]
      refine ⟨fun t _ i j _ => ?_, fun i => ?_⟩
      · simp [pcnt]
      · simp [pcnt]
    rw [abs_one, Nat.one_le_cast]
    exact Finset.card_pos.mpr hne
  · simp

/- English proof (translation)
Introduce `m ρ`. Proceed by induction on `ρ with`. Consider the case `nil => intro _ lam hlam`. Conclude with `bound_nil m lam hlam`. Consider the case `cons q ρ ih`.

Introduce `hpos lam hlam`. Establish `hq : 1 ≤ q` using `hpos q (by simp)`. Establish `ih'` using `ih (fun r hr => hpos r (List.mem_cons_of_mem _ hr))`. Establish `hterm : ∀ i : Fin m, |(if q ≤ lam i + stair m i then cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q)) (alternantPsum m ρ) else 0)| ≤ (if q ≤ lam i + stair m i then |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q)) (alternantPs …`. Introduce `i`.

Use `split_ifs with hqi`. Distinguish the cases in `hinj : Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))`. Take `⟨σ, μ, hμ, -, hσ⟩` from `h2 m lam hlam q i hqi hinj`. Establish `hu : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) = (fun k => μ k + stair m k) ∘ σ.symm`. Use function extensionality and compare the values at `k`.

Use `hσ (σ.symm k)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis. Rewrite using `[hu, abs_cf_perm (isAlt_alternantPsum m ρ), abs_cf_perm (isAlt_alternantPsum m _), h1 m ρ.sum μ hμ, Nat.abs_cast]`. Conclude with `ih' μ hμ`. Simplify using `only [Function.Injective, not_forall] at hinj`.

Take `⟨a, b, hab, hne⟩` from `hinj`. Rewrite using `[cf_eq_zero_of_eq (isAlt_alternantPsum m ρ) hne hab, abs_zero]`. Conclude with `abs_nonneg _`. Simplify using the standard rewrite rules. Rewrite using `[alternantPsum_cons, cf_mul_psum]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombStripSum.Statement) : CombCfBound.Statement := by
  intro m ρ
  induction ρ with
  | nil => intro _ lam hlam; exact bound_nil m lam hlam
  | cons q ρ ih =>
    intro hpos lam hlam
    have hq : 1 ≤ q := hpos q (by simp)
    have ih' := ih (fun r hr => hpos r (List.mem_cons_of_mem _ hr))
    have hterm : ∀ i : Fin m,
        |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| ≤
        (if q ≤ lam i + stair m i then
          |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m (List.replicate ρ.sum 1))| else 0) := by
      intro i
      split_ifs with hqi
      · by_cases hinj :
            Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        · obtain ⟨σ, μ, hμ, -, hσ⟩ := h2 m lam hlam q i hqi hinj
          have hu : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) =
              (fun k => μ k + stair m k) ∘ σ.symm := by
            funext k
            have := hσ (σ.symm k)
            rwa [Equiv.apply_symm_apply] at this
          rw [hu, abs_cf_perm (isAlt_alternantPsum m ρ), abs_cf_perm (isAlt_alternantPsum m _),
            h1 m ρ.sum μ hμ, Nat.abs_cast]
          exact ih' μ hμ
        · simp only [Function.Injective, not_forall] at hinj
          obtain ⟨a, b, hab, hne⟩ := hinj
          rw [cf_eq_zero_of_eq (isAlt_alternantPsum m ρ) hne hab, abs_zero]
          exact abs_nonneg _
      · simp
    rw [alternantPsum_cons, cf_mul_psum]
    calc _ ≤ ∑ i : Fin m, |(if q ≤ lam i + stair m i then
          cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
            (alternantPsum m ρ) else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ((latticeWords (ρ.sum + q) lam).card : ℚ) := h3 m ρ.sum q lam hlam hq
      _ = ((latticeWords (q :: ρ).sum lam).card : ℚ) := by rw [List.sum_cons, add_comm]

end CombCfBound

end

end GroundTheory.Heights₂.Heights.RestTerms
