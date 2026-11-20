import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ConvPhi
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
The claim follows from `continuous_mR.comp continuous_subtype_val`.
-/
theorem continuous_kR : Continuous (fun k : KR n => mR (k : GR n)) := continuous_mR.comp continuous_subtype_val

def kSet (S : Set (M2 n)) : Set (M2 n) := (fun p : KR n × M2 n => mR (p.1 : GR n) * p.2) '' (univ ×ˢ S)

/- English proof (translation)
The claim follows from `(isCompact_univ.prod hS).image ((continuous_kR.comp continuous_fst).mul continuous_snd)`.
-/
theorem isCompact_kSet {S : Set (M2 n)} (hS : IsCompact S) : IsCompact (kSet S) :=
  (isCompact_univ.prod hS).image ((continuous_kR.comp continuous_fst).mul continuous_snd)

/- English proof (translation)
Unfold `tw`. Establish `hz : ∀ k : KR n, β ((mR (k : GR n))ᴴ * X) = 0`. Introduce `k`. Assume the negation of the conclusion as `h`. Apply `hX` to reduce the goal to its premises.

Establish `hk : InK (mR (k : GR n))` using `k.2`. Establish `hkk : mR (k : GR n) * (mR (k : GR n))ᴴ = 1` using `mul_eq_one_comm.mp hk.2`. Use `⟨(k, (mR (k : GR n))ᴴ * X), ⟨mem_univ _, subset_tsupport _ h⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← Matrix.mul_assoc, hkk, Matrix.one_mul]`.

Simplify using `[hz]`.
-/
theorem tw_eq_zero (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) {X : M2 n} (hX : X ∉ kSet (tsupport β)) :
    tw m e μK β X = 0 := by
  unfold tw
  have hz : ∀ k : KR n, β ((mR (k : GR n))ᴴ * X) = 0 := by
    intro k
    by_contra h
    apply hX
    have hk : InK (mR (k : GR n)) := k.2
    have hkk : mR (k : GR n) * (mR (k : GR n))ᴴ = 1 := mul_eq_one_comm.mp hk.2
    refine ⟨(k, (mR (k : GR n))ᴴ * X), ⟨mem_univ _, subset_tsupport _ h⟩, ?_⟩
    simp only
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  simp [hz]

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_kSet hβ) fun X hX => tw_eq_zero m e μK β hX` and prove the remaining obligations.
-/
theorem tw_support (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (tw m e μK β) := by
  refine HasCompactSupport.intro (isCompact_kSet hβ) fun X hX => tw_eq_zero m e μK β hX

/- English proof (translation)
Rewrite using `[JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]`. Simplify using the standard rewrite rules.
-/
private theorem JJ_mul_JJ' : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

/- English proof (translation)
Establish `hJ` using `(JJ_mul_JJ' (n := n))`. Establish `hx' : xᴴ * JJ n * x = JJ n` using `hx`. Establish `h1 : (-(JJ n * xᴴ * JJ n)) * x = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.neg_mul, Matrix.mul_assoc]`.

Use `_ = 1 := by rw [hx', hJ, neg_neg]`. Establish `h2 : x * (-(JJ n * xᴴ * JJ n)) = 1` using `mul_eq_one_comm.mp h1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, neg_neg]`. Use `_ = JJ n := by rw [h2, Matrix.one_mul]`.
-/
private theorem mul_JJ_mul_conjTranspose_of_inG {x : M2 n} (hx : InG x) : x * JJ n * xᴴ = JJ n := by
  have hJ := (JJ_mul_JJ' (n := n))
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h1 : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hx', hJ, neg_neg]
  have h2 : x * (-(JJ n * xᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc x * JJ n * xᴴ = x * (-(JJ n * xᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, neg_neg]
    _ = JJ n := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Establish `e` using `mul_JJ_mul_conjTranspose_of_inG hx`. Rewrite `e` using `[← fromBlocks_toBlocks x]`. Simplify using `only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_inj, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂] at e`. Simplify using `at e`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `e.2.2.2`. Rewrite `h` using `[neg_add_eq_sub, sub_eq_zero]`. Conclude with `h`. Establish `h` using `e.2.2.1`. Rewrite `h` using `[neg_add_eq_sub]`. Then use the resulting hypothesis.
-/
private theorem toBlocks₂_conj_relations_of_inG {x : M2 n} (hx : InG x) :
    toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ = toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ ∧
    toBlocks₂₁ x * (toBlocks₁₂ x)ᴴ - toBlocks₂₂ x * (toBlocks₁₁ x)ᴴ = -1 := by
  have e := mul_JJ_mul_conjTranspose_of_inG hx
  rw [← fromBlocks_toBlocks x] at e
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_inj,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂] at e
  simp at e
  refine ⟨?_, ?_⟩
  · have h := e.2.2.2
    rw [neg_add_eq_sub, sub_eq_zero] at h
    exact h
  · have h := e.2.2.1
    rwa [neg_add_eq_sub] at h

/- English proof (translation)
Introduce `h0`. Take `⟨v, hv, hvM⟩` from `exists_vecMul_eq_zero_iff.mpr h0`. Take `⟨hC, hA⟩` from `toBlocks₂_conj_relations_of_inG hx`. Rewrite `hvM` using `[Matrix.vecMul_add, Matrix.vecMul_smul]`. Establish `hβ : v ᵥ* toBlocks₂₂ x = -t • (v ᵥ* toBlocks₂₁ x)`.

Rewrite using `[neg_smul, ← sub_eq_zero, sub_neg_eq_add, add_comm]`. Conclude with `hvM`. Establish `key : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x) = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x)`. Establish `h` using `congrArg (fun M => (v ᵥ* M) ⬝ᵥ star v) hC`. Establish `e1 : (v ᵥ* (toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ)) ⬝ᵥ star v = (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x)`.

Rewrite using `[← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]`. Establish `e2 : (v ᵥ* (toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ)) ⬝ᵥ star v = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x)`. Rewrite using `[← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]`. Rewrite using `[← e1, ← e2]`. Conclude with `h`.

Rewrite `key` using `[hβ, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]`. Establish `hs : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) = 0`. Establish `h3 : (t - star t) * ((v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x)) = 0`. Rewrite `key` using `[star_neg]`. Take the linear combination `key`.

Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h4) ht`. Conclude with `h4`. Establish `hα : v ᵥ* toBlocks₂₁ x = 0` using `by open scoped ComplexOrder in exact dotProduct_self_star_eq_zero.mp hs`. Establish `hβ0 : v ᵥ* toBlocks₂₂ x = 0` using `by rw [hβ, hα, smul_zero]`.

Establish `h5` using `congrArg (fun M => v ᵥ* M) hA`. Simplify using `only [Matrix.vecMul_sub, ← vecMul_vecMul, hα, hβ0, zero_vecMul, sub_self, vecMul_neg, vecMul_one] at h5`. Conclude with `hv (neg_eq_zero.mp h5.symm)`.
-/
private theorem det_smul_toBlocks₂₁_add_toBlocks₂₂_ne_zero_of_inG {x : M2 n} (hx : InG x) (t : ℂ) (ht : t ≠ star t) :
    (t • toBlocks₂₁ x + toBlocks₂₂ x).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hvM⟩ := exists_vecMul_eq_zero_iff.mpr h0
  obtain ⟨hC, hA⟩ := toBlocks₂_conj_relations_of_inG hx
  rw [Matrix.vecMul_add, Matrix.vecMul_smul] at hvM
  have hβ : v ᵥ* toBlocks₂₂ x = -t • (v ᵥ* toBlocks₂₁ x) := by
    rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hvM
  have key : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x)
      = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) := by
    have h := congrArg (fun M => (v ᵥ* M) ⬝ᵥ star v) hC
    have e1 : (v ᵥ* (toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ)) ⬝ᵥ star v
        = (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x) := by
      rw [← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]
    have e2 : (v ᵥ* (toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ)) ⬝ᵥ star v
        = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) := by
      rw [← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]
    rw [← e1, ← e2]
    exact h
  rw [hβ, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at key
  have hs : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) = 0 := by
    have h3 : (t - star t) * ((v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x)) = 0 := by
      rw [star_neg] at key
      linear_combination key
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) ht
    · exact h4
  have hα : v ᵥ* toBlocks₂₁ x = 0 := by
    open scoped ComplexOrder in exact dotProduct_self_star_eq_zero.mp hs
  have hβ0 : v ᵥ* toBlocks₂₂ x = 0 := by rw [hβ, hα, smul_zero]
  have h5 := congrArg (fun M => v ᵥ* M) hA
  simp only [Matrix.vecMul_sub, ← vecMul_vecMul, hα, hβ0, zero_vecMul, sub_self, vecMul_neg,
    vecMul_one] at h5
  exact hv (neg_eq_zero.mp h5.symm)

end PositivityTheory.Rg.Sw.HSt.Conv
