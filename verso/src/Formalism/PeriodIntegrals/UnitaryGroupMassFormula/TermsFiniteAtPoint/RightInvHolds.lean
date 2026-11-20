import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.SkewSolve

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open Formalism.MainNotions.S Matrix

/- English proof (translation)
Introduce `E _ r Z u hu hdep`. Establish `hcast : ∀ (h : r ≤ r + 1) (c : Fin r), Fin.castLE h c = Fin.castSucc c` using `fun h c => Fin.ext rfl`. Establish `hcast1 : ∀ (h : r + 1 ≤ r + 1) (c : Fin (r + 1)), Fin.castLE h c = c` using `fun h c => Fin.ext rfl`. Prove the components needed by the constructor for the conclusion. Unfold `leadMinorE`.

Rewrite using `[dif_pos le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]`. Use `⟨Fin.snoc (α := fun _ => E) u 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hu` to reduce the goal to its premises. Use function extensionality and compare the values at `c`.

Establish `h1` using `congrFun h0 (Fin.castSucc c)`. Simplify using `using h1`. Use function extensionality and compare the values at `b`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, hcast1, Pi.zero_apply]`. Rewrite using `[Fin.sum_univ_castSucc]`.

Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]`. Conclude with `hdep b`. Unfold `leadMinorE`. Rewrite using `[dif_pos (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `b`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, hcast, Pi.zero_apply]`. Conclude with `hdep (Fin.castSucc b)`.
-/
theorem rowsDep_holds : RowsDep := by
  intro E _ r Z u hu hdep
  have hcast : ∀ (h : r ≤ r + 1) (c : Fin r), Fin.castLE h c = Fin.castSucc c := fun h c => Fin.ext rfl
  have hcast1 : ∀ (h : r + 1 ≤ r + 1) (c : Fin (r + 1)), Fin.castLE h c = c := fun h c => Fin.ext rfl
  constructor
  · unfold leadMinorE
    rw [dif_pos le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨Fin.snoc (α := fun _ => E) u 0, ?_, ?_⟩
    · intro h0
      apply hu
      funext c
      have h1 := congrFun h0 (Fin.castSucc c)
      simpa using h1
    · funext b
      simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, hcast1, Pi.zero_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
      exact hdep b
  · unfold leadMinorE
    rw [dif_pos (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨u, hu, ?_⟩
    funext b
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, hcast, Pi.zero_apply]
    exact hdep (Fin.castSucc b)

/- English proof (translation)
Introduce `E _ r β hind`. Establish `hinjT : Function.Injective (Matrix.mulVecLin βᵀ)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Apply `hind u` to reduce the goal to its premises.

Introduce `b`. Establish `h1` using `congrFun hu b`. Rewrite `h1` using `[Matrix.mulVecLin_apply, Matrix.mulVec_transpose]`. Conclude with `h1`. Establish `hrank : β.rank = r`.

Rewrite using `[← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj hinjT]`. Simplify using the standard rewrite rules. Establish `hsurj : Function.Surjective (Matrix.mulVecLin β)`. Rewrite using `[← LinearMap.range_eq_top]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises.

Use `show β.rank = _`. Rewrite using `[hrank]`. Simplify using the standard rewrite rules. Establish `hker : Module.finrank E (LinearMap.ker (Matrix.mulVecLin β)) = 1`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin β)`.

Rewrite `h1` using `[LinearMap.range_eq_top.2 hsurj, finrank_top]`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers. Take `⟨v0, hv0⟩` from `Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < Module.finrank E (LinearMap.ker (Matrix.mulVecLin β)))`. Establish `hspan` using `(finrank_eq_one_iff_of_nonzero' v0 hv0).1 hker`.

Use `set vv : Fin (r + 1) → E := (v0 : Fin (r + 1) → E) with hvv`. Establish `hvv0 : vv ≠ 0` using `fun h => hv0 (Subtype.ext h)`. Establish `hfv : β *ᵥ vv = 0` using `v0.2`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hvv0`. Establish `hj' : vv j ≠ 0` using `hj`.

Use `choose x hx using fun c : Fin r => hsurj (Pi.single c 1)`. Use `set x' : Fin r → Fin (r + 1) → E := fun c => x c - ((vv j)⁻¹ * x c j) • vv with hx'`. Establish `hx'f : ∀ c, β *ᵥ x' c = Pi.single c 1`. Introduce `c`. Establish `h1 : β *ᵥ x c = Pi.single c 1` using `hx c`.

Simplify using `only [hx', Matrix.mulVec_sub, Matrix.mulVec_smul, hfv, smul_zero, sub_zero, h1]`. Establish `hx'j : ∀ c, x' c j = 0`. Introduce `c`. Simplify using `only [hx', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Establish `h2 : (vv j)⁻¹ * x c j * vv j = x c j`.

Rewrite using `[mul_comm, ← mul_assoc, mul_inv_cancel₀ hj', one_mul]`. Rewrite using `[h2, sub_self]`. Use `⟨Matrix.of (fun b c => x' c b), vv, fun k => if k = j then (vv j)⁻¹ else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a c`. Establish `h1` using `congrFun (hx'f c) a`.

Establish `h2 : ∑ b, β a b * x' c b = (Pi.single c (1 : E) : Fin r → E) a`. Rewrite using `[← h1]`. Both sides reduce to the same expression. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.of_apply]`.

Rewrite using `[h2, Pi.single_apply]`. Introduce `c`. Establish `h1` using `congrFun hfv c`. Simplify `h1` using `[Matrix.mulVec, dotProduct]`. Introduce `i k set y : Fin (r + 1) → E := ∑ c, β c k • x' c with hy`.

Establish `hQ : (Matrix.of (fun b c => x' c b) * β) i k = y i`. Simplify using `[Matrix.mul_apply, hy, Finset.sum_apply, mul_comm]`. Establish `hyf : β *ᵥ y = β *ᵥ Pi.single k 1`. Use function extensionality and compare the values at `a`. Simplify using `only [hy, Matrix.mulVec_sum, Matrix.mulVec_smul, hx'f]`.

Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]`. Establish `hyj : y j = 0`. Simplify using `[hy, Finset.sum_apply, hx'j]`. Establish `hmem : Pi.single k 1 - y ∈ LinearMap.ker (Matrix.mulVecLin β)`. Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, hyf, sub_self]`.

Take `⟨t, ht⟩` from `hspan ⟨_, hmem⟩`. Establish `ht' : t • vv = Pi.single k 1 - y` using `congrArg Subtype.val ht`. Establish `htj` using `congrFun ht' j`. Establish `hti` using `congrFun ht' i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hyj, sub_zero, Pi.single_apply] at htj hti`.

Use `show (Matrix.of (fun b c => x' c b) * β) i k = _`. Rewrite using `[hQ]`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality. Simplify using `only [if_true] at htj`.

Establish `htv : t = (vv k)⁻¹`. Clear the denominators using the available nonvanishing facts. Take the linear combination `htj`. Simplify using `only [if_true]`. Rewrite `hti` using `[htv]`.

Take the linear combination `hti`. Establish `hjk : j ≠ k` using `fun h => hkj h.symm`. Simplify using `only [if_neg hjk] at htj`. Establish `ht0 : t = 0`. Break down `mul_eq_zero.1 htj with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hj`. Simplify using `only [if_neg hkj, mul_zero, sub_zero]`. Rewrite `hti` using `[ht0, zero_mul]`. Take the linear combination `hti`.
-/
theorem rightInv_holds : RightInv := by
  intro E _ r β hind
  have hinjT : Function.Injective (Matrix.mulVecLin βᵀ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hind u
    intro b
    have h1 := congrFun hu b
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at h1
    exact h1
  have hrank : β.rank = r := by
    rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj hinjT]
    simp
  have hsurj : Function.Surjective (Matrix.mulVecLin β) := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    show β.rank = _
    rw [hrank]
    simp
  have hker : Module.finrank E (LinearMap.ker (Matrix.mulVecLin β)) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin β)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
    simp at h1
    omega
  obtain ⟨v0, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < Module.finrank E (LinearMap.ker (Matrix.mulVecLin β)))
  have hspan := (finrank_eq_one_iff_of_nonzero' v0 hv0).1 hker
  set vv : Fin (r + 1) → E := (v0 : Fin (r + 1) → E) with hvv
  have hvv0 : vv ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hfv : β *ᵥ vv = 0 := v0.2
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hvv0
  have hj' : vv j ≠ 0 := hj
  choose x hx using fun c : Fin r => hsurj (Pi.single c 1)
  set x' : Fin r → Fin (r + 1) → E := fun c => x c - ((vv j)⁻¹ * x c j) • vv with hx'
  have hx'f : ∀ c, β *ᵥ x' c = Pi.single c 1 := by
    intro c
    have h1 : β *ᵥ x c = Pi.single c 1 := hx c
    simp only [hx', Matrix.mulVec_sub, Matrix.mulVec_smul, hfv, smul_zero, sub_zero, h1]
  have hx'j : ∀ c, x' c j = 0 := by
    intro c
    simp only [hx', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : (vv j)⁻¹ * x c j * vv j = x c j := by
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hj', one_mul]
    rw [h2, sub_self]
  refine ⟨Matrix.of (fun b c => x' c b), vv, fun k => if k = j then (vv j)⁻¹ else 0, ?_, ?_, ?_⟩
  · ext a c
    have h1 := congrFun (hx'f c) a
    have h2 : ∑ b, β a b * x' c b = (Pi.single c (1 : E) : Fin r → E) a := by
      rw [← h1]
      rfl
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [h2, Pi.single_apply]
  · intro c
    have h1 := congrFun hfv c
    simpa [Matrix.mulVec, dotProduct] using h1
  · intro i k
    set y : Fin (r + 1) → E := ∑ c, β c k • x' c with hy
    have hQ : (Matrix.of (fun b c => x' c b) * β) i k = y i := by
      simp [Matrix.mul_apply, hy, Finset.sum_apply, mul_comm]
    have hyf : β *ᵥ y = β *ᵥ Pi.single k 1 := by
      funext a
      simp only [hy, Matrix.mulVec_sum, Matrix.mulVec_smul, hx'f]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have hyj : y j = 0 := by
      simp [hy, Finset.sum_apply, hx'j]
    have hmem : Pi.single k 1 - y ∈ LinearMap.ker (Matrix.mulVecLin β) := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, hyf, sub_self]
    obtain ⟨t, ht⟩ := hspan ⟨_, hmem⟩
    have ht' : t • vv = Pi.single k 1 - y := congrArg Subtype.val ht
    have htj := congrFun ht' j
    have hti := congrFun ht' i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hyj, sub_zero, Pi.single_apply] at htj hti
    show (Matrix.of (fun b c => x' c b) * β) i k = _
    rw [hQ]
    by_cases hkj : k = j
    · subst hkj
      simp only [if_true] at htj
      have htv : t = (vv k)⁻¹ := by
        field_simp
        linear_combination htj
      simp only [if_true]
      rw [htv] at hti
      linear_combination hti
    · have hjk : j ≠ k := fun h => hkj h.symm
      simp only [if_neg hjk] at htj
      have ht0 : t = 0 := by
        rcases mul_eq_zero.1 htj with h | h
        · exact h
        · exact absurd h hj
      simp only [if_neg hkj, mul_zero, sub_zero]
      rw [ht0, zero_mul] at hti
      linear_combination hti

end PI.TermsAtPtFiniteW
