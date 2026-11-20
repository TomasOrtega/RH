import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

def singleDecomp (d : IndexData) (τ : Fin d.f) (Q : XPoly d) : ℕ → Fin d.f → XPoly d :=
  fun k σ => if k = 1 then (if σ = τ then Q else 0) else 0

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hp : (RestTerms.blockPowerSum d.f d.N 1 τ).IsHomogeneous 1`. Unfold `RestTerms.blockPowerSum`. Conclude with `IsHomogeneous.sum _ _ _ (fun i _ => by simpa using isHomogeneous_X ℚ (τ, i))`. Simplify `hp.mul hQ` using `[add_comm]`.

Introduce `k hk σ`. Unfold `singleDecomp`. Use `split_ifs with h1 h2`. Substitute `h1` using the available equality. Simplify using `using hQ`.

Conclude with `isHomogeneous_zero _ _ _`. Conclude with `isHomogeneous_zero _ _ _`. Unfold `RestTerms.IsPowerSumDecomposition singleDecomp`. Establish `h1 : 1 ∈ Icc 1 d.N`. Use `d.two_le_N` as an intermediate fact.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_eq_single_of_mem 1 h1]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Simplify using `[hk]`.
-/
theorem singleDecomp_isHomDecomp (d : IndexData) (τ : Fin d.f) (Q : XPoly d)
    (hQ : Q.IsHomogeneous d.D) :
    IsHomDecomp d (RestTerms.blockPowerSum d.f d.N 1 τ * Q) (singleDecomp d τ Q) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp : (RestTerms.blockPowerSum d.f d.N 1 τ).IsHomogeneous 1 := by
      unfold RestTerms.blockPowerSum
      exact IsHomogeneous.sum _ _ _ (fun i _ => by simpa using isHomogeneous_X ℚ (τ, i))
    simpa [add_comm] using hp.mul hQ
  · intro k hk σ
    unfold singleDecomp
    split_ifs with h1 h2
    · subst h1; simpa using hQ
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_zero _ _ _
  · unfold RestTerms.IsPowerSumDecomposition singleDecomp
    have h1 : 1 ∈ Icc 1 d.N := by
      have := d.two_le_N
      simp; omega
    rw [Finset.sum_eq_single_of_mem 1 h1]
    · simp
    · intro k _ hk
      simp [hk]

/- English proof (translation)
Unfold `restTot rest₂`. Establish `h : ∀ (p : ℕ) (σ : Fin d.f), ∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p (S.frob p) (singleDecomp d τ Q) σ k n = 0`. Introduce `p σ`. Use `Finset.sum_eq_zero (fun k hk => ?_)` and prove the remaining obligations. Establish `hk1 : k ≠ 1`.

Simplify using `at hk`. Use linear arithmetic over natural numbers and integers. Establish `: ∀ n, restSeries d p (S.frob p) (singleDecomp d τ Q) σ k n = 0`. Introduce `n`. Simplify using `[restSeries, singleDecomp, hk1]`.

Simplify using `[this]`. Simplify using `[h]`.
-/
theorem restTot_singleDecomp (d : IndexData) (S : EndSystem d) (B0 : ℕ) (τ : Fin d.f)
    (Q : XPoly d) : restTot S B0 (singleDecomp d τ Q) = 0 := by
  unfold restTot rest₂
  have h : ∀ (p : ℕ) (σ : Fin d.f), ∑ k ∈ Icc 2 d.N,
      ∑' n : ℕ, restSeries d p (S.frob p) (singleDecomp d τ Q) σ k n = 0 := by
    intro p σ
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk1 : k ≠ 1 := by
      simp at hk; omega
    have : ∀ n, restSeries d p (S.frob p) (singleDecomp d τ Q) σ k n = 0 := by
      intro n
      simp [restSeries, singleDecomp, hk1]
    simp [this]
  simp [h]

/- English proof (translation)
Use `d.j_lt_N` as an intermediate fact. Rewrite using `[Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_lowerIdx_filter (d : IndexData) :
    (univ.filter (fun i : Fin d.N => i.val < d.j)).card = d.j := by
  have := d.j_lt_N
  rw [Fin.card_filter_val_lt]
  omega

/- English proof (translation)
Introduce `d S hI hH B0 A0 b0 hA hb τ Q hQ hint`. Use `set F := RestTerms.blockPowerSum d.f d.N 1 τ * Q with hF`. Establish `hdec` using `singleDecomp_isHomDecomp d τ Q hQ`. Establish `key` using `h83 d S hI B0 A0 b0 hA hb F (singleDecomp d τ Q) hdec`. Rewrite `key` using `[restTot_singleDecomp, hH τ Q hQ]`.

Establish `hsh : shSum d F = d.j`. Unfold `shSum`. Rewrite using `[Finset.sum_eq_single τ]`. Rewrite using `[hSh d τ F _ hdec.1 hdec.2.1 hdec.2.2]`. Establish `h1 : 1 ∈ Icc 1 d.N`.

Use `d.two_le_N` as an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_eq_single_of_mem 1 h1]`. Establish `hl : lowerPowerSum d (1 - 1) τ = (d.j : XPoly d)`.

Simplify using `[lowerPowerSum, card_lowerIdx_filter]`. Establish `hj : ((d.j : XPoly d)) * Q = d.j • Q` using `(nsmul_eq_mul _ _).symm`. Simplify using `only [singleDecomp, if_true, Nat.cast_one, one_mul, hl, hj, map_nsmul, hint]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Simplify using `[singleDecomp, hk]`. Introduce `σ _ hσ`. Rewrite using `[hSh d σ F _ hdec.1 hdec.2.1 hdec.2.2]`. Use `Finset.sum_eq_zero (fun k _ => ?_)` and prove the remaining obligations. Simplify using `[singleDecomp, hσ]`.

Simplify using the standard rewrite rules. Establish `htot : totSum d F = d.N`. Unfold `totSum`. Rewrite using `[Finset.sum_eq_single τ]`. Rewrite using `[hTot d τ F _ hdec.1 hdec.2.1 hdec.2.2]`.

Simplify using `[singleDecomp, hint]`. Introduce `σ _ hσ`. Rewrite using `[hTot d σ F _ hdec.1 hdec.2.1 hdec.2.2]`. Simplify using `[singleDecomp, hσ]`. Simplify using the standard rewrite rules.

Rewrite `key` using `[hsh, htot]`. Establish `hv` using `S.vol_pos`. Rewrite using `[key]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem HeightLimitIdentity.proof (h83 : HeightTauIdentity.Statement) (hSh : ShFormula.Statement)
    (hTot : TotFormula.Statement) : HeightLimitIdentity.Statement := by
  intro d S hI hH B0 A0 b0 hA hb τ Q hQ hint
  set F := RestTerms.blockPowerSum d.f d.N 1 τ * Q with hF
  have hdec := singleDecomp_isHomDecomp d τ Q hQ
  have key := h83 d S hI B0 A0 b0 hA hb F (singleDecomp d τ Q) hdec
  rw [restTot_singleDecomp, hH τ Q hQ] at key
  have hsh : shSum d F = d.j := by
    unfold shSum
    rw [Finset.sum_eq_single τ]
    · rw [hSh d τ F _ hdec.1 hdec.2.1 hdec.2.2]
      have h1 : 1 ∈ Icc 1 d.N := by
        have := d.two_le_N
        simp; omega
      rw [Finset.sum_eq_single_of_mem 1 h1]
      · have hl : lowerPowerSum d (1 - 1) τ = (d.j : XPoly d) := by
          simp [lowerPowerSum, card_lowerIdx_filter]
        have hj : ((d.j : XPoly d)) * Q = d.j • Q := (nsmul_eq_mul _ _).symm
        simp only [singleDecomp, if_true, Nat.cast_one, one_mul, hl, hj, map_nsmul, hint]
        simp
      · intro k _ hk
        simp [singleDecomp, hk]
    · intro σ _ hσ
      rw [hSh d σ F _ hdec.1 hdec.2.1 hdec.2.2]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      simp [singleDecomp, hσ]
    · simp
  have htot : totSum d F = d.N := by
    unfold totSum
    rw [Finset.sum_eq_single τ]
    · rw [hTot d τ F _ hdec.1 hdec.2.1 hdec.2.2]
      simp [singleDecomp, hint]
    · intro σ _ hσ
      rw [hTot d σ F _ hdec.1 hdec.2.1 hdec.2.2]
      simp [singleDecomp, hσ]
    · simp
  rw [hsh, htot] at key
  have hv := S.vol_pos
  rw [key]
  push_cast
  field_simp
  ring

end GroundTheory.Heights₂.Heights.TheoremB
