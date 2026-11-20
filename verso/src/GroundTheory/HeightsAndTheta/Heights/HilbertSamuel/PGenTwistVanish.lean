import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenKoszulStep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ V α hV hα e`. Take `⟨-, ⟨c₁, hc₁⟩, -⟩` from `hS S K ι (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance inferInstance (hG S K ι V hV)`. Take `⟨R, hR⟩` from `hK S K ι V α hV hα`. Use `set B : ℤ := ∑ k, (|e k| + (R : ℤ) * |α k|) with hB`. Use `⟨(c₁ + B).toNat, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ j n : ℕ, (c₁ + B).toNat ≤ n → ∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) i)`. Introduce `j`. Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`. Introduce `n hn i hi`.

Distinguish the cases in `hj : j < R`. Use `hc₁ _ i hi fun k => ?_` and prove the remaining obligations. Establish `h1 : |e k| + (R : ℤ) * |α k| ≤ B` using `Finset.single_le_sum (f := fun k => |e k| + (R : ℤ) * |α k|) (fun k _ => by positivity) (Finset.mem_univ k)`. Establish `h2 : c₁ + B ≤ n` using `by omega`. Establish `h3 : |((j : ℤ) - R) * α k| ≤ (R : ℤ) * |α k|`.

Rewrite using `[abs_mul]`. Use `mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)` and prove the remaining obligations. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> omega`. Establish `h4` using `neg_abs_le (((j : ℤ) - R) * α k)`.

Establish `h5` using `neg_abs_le (e k)`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hj` using `[not_lt]`. Use `hR _ (fun p hp1 hpR i' hi' => ?_) i hi` and prove the remaining obligations.

Establish `heq : (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) - (p : ℤ) • α = e + (((j - p : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ)`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Move the coercions through the operations in `[Nat.cast_sub (le_trans hpR hj)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq]`. Conclude with `ih (j - p) (by omega) n hn i' hi'`. Introduce `m n hn`. Establish `h` using `key (m + R) n hn 1 le_rfl`. Establish `heq : (e + (((m + R : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ)) = e + (m : ℤ) • α + fun _ => (n : ℤ)`.

Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[heq]`. Then use the resulting hypothesis.
-/
theorem GenTwistVanish.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hK : GenKoszulStep.Statement) : GenTwistVanish.Statement := by
  intro S _ K _ _ ι _ _ V α hV hα e
  obtain ⟨-, ⟨c₁, hc₁⟩, -⟩ := hS S K ι (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance
    inferInstance (hG S K ι V hV)
  obtain ⟨R, hR⟩ := hK S K ι V α hV hα
  set B : ℤ := ∑ k, (|e k| + (R : ℤ) * |α k|) with hB
  refine ⟨(c₁ + B).toNat, ?_⟩

  have key : ∀ j n : ℕ, (c₁ + B).toNat ≤ n → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro n hn i hi
      by_cases hj : j < R
      · refine hc₁ _ i hi fun k => ?_
        have h1 : |e k| + (R : ℤ) * |α k| ≤ B :=
          Finset.single_le_sum (f := fun k => |e k| + (R : ℤ) * |α k|)
            (fun k _ => by positivity) (Finset.mem_univ k)
        have h2 : c₁ + B ≤ n := by omega
        have h3 : |((j : ℤ) - R) * α k| ≤ (R : ℤ) * |α k| := by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]
          constructor <;> omega
        have h4 := neg_abs_le (((j : ℤ) - R) * α k)
        have h5 := neg_abs_le (e k)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      · rw [not_lt] at hj
        refine hR _ (fun p hp1 hpR i' hi' => ?_) i hi
        have heq : (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) - (p : ℤ) • α =
            e + (((j - p : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ) := by
          funext k
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          push_cast [Nat.cast_sub (le_trans hpR hj)]
          ring
        rw [heq]
        exact ih (j - p) (by omega) n hn i' hi'
  intro m n hn
  have h := key (m + R) n hn 1 le_rfl
  have heq : (e + (((m + R : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ)) =
      e + (m : ℤ) • α + fun _ => (n : ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rwa [heq] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
