import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeOfAddOneLeSucc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Unfold `divCycle at h`. Use `split_ifs at h with hW`. Conclude with `hW`. Conclude with `absurd rfl h`.
-/
theorem mem_minimalPrimes_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)}
    (h : divCycle P f W ≠ 0) : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h

/- English proof (translation)
Use function extensionality and compare the values at `W`. Rewrite using `[ratDiv, divCycle_one, sub_zero]`.
-/
theorem ratDiv_one {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) : ratDiv P f 1 = divCycle P f := by
  funext W
  rw [ratDiv, divCycle_one, sub_zero]

/- English proof (translation)
Unfold `mixedDiff`. Rewrite using `[List.ofFn_succ, List.foldr_cons, Matrix.cons_val_zero]`. Use function extensionality and compare the values at `m`. Simplify using `[diffStep]`.
-/
theorem mixedDiff_cons_zero {K : Type*} {n : ℕ} (L : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Matrix.vecCons 0 L) h = 0 := by
  unfold mixedDiff
  rw [List.ofFn_succ, List.foldr_cons, Matrix.cons_val_zero]
  funext m
  simp [diffStep]

/- English proof (translation)
Unfold `eventualValue`. Use `split_ifs with hc`. Take `⟨m, hm⟩` from `hc.choose_spec.exists`. Conclude with `hm.symm`. Both sides reduce to the same expression.
-/
theorem eventualValue_zero {K : Type*} : eventualValue (0 : (K → ℤ) → ℤ) = 0 := by
  unfold eventualValue
  split_ifs with hc
  · obtain ⟨m, hm⟩ := hc.choose_spec.exists
    exact hm.symm
  · rfl

/- English proof (translation)
Rewrite using `[vNum, intNum, mixedDiff_cons_zero, eventualValue_zero]`.
-/
theorem vNum_cons_zero {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (W : Ideal (MRing ι O)) {n : ℕ}
    (L : Fin n → K → ℤ) : vNum W (Matrix.vecCons 0 L) = 0 := by
  rw [vNum, intNum, mixedDiff_cons_zero, eventualValue_zero]

/- English proof (translation)
Use `(Submodule.eq_bot_iff _).mpr fun a ha => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `ha0`. Take `⟨n, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ`. Rewrite `ha` using `[Ideal.mem_comap, map_mul, map_pow]`. Break down `hH.mem_or_mem ha with hv | hp` into its components or cases.

Conclude with `hH.ne_top (Ideal.eq_top_of_isUnit_mem _ hv ((Units.isUnit v).map C))`. Conclude with `hϖH (hH.mem_of_pow_mem n hp)`.
-/
theorem comap_C_eq_bot_of_not_mem {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (H : Ideal (MRing ι O)) [hH : H.IsPrime] (hϖH : (C ϖ : MRing ι O) ∉ H) :
    H.comap (C : O →+* MRing ι O) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
  by_contra ha0
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rw [Ideal.mem_comap, map_mul, map_pow] at ha
  rcases hH.mem_or_mem ha with hv | hp
  · exact hH.ne_top (Ideal.eq_top_of_isUnit_mem _ hv ((Units.isUnit v).map C))
  · exact hϖH (hH.mem_of_pow_mem n hp)

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ <;> assumption`.
-/
theorem withBot_le_of_add_one_le (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ ((N : ℕ) : WithBot ℕ∞) :=
  by apply _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ <;> assumption

/- English proof (translation)
Use `lt_of_le_of_lt (withBot_le_of_add_one_le x N hx) ?_` and prove the remaining obligations. Conclude with `Nat.lt_succ_self N` after adjusting the coercions.
-/
theorem withBot_lt_of_add_one_le (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < ((N + 1 : ℕ) : WithBot ℕ∞) := by
  refine lt_of_le_of_lt (withBot_le_of_add_one_le x N hx) ?_
  exact_mod_cast Nat.lt_succ_self N

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP c s hs hsP L`. Establish `hdim : ringKrullDim (MRing ι O ⧸ P) = ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)` using `hP.dim`. Use `hP.multiProj.isPrime` as an intermediate fact. Establish `hL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P (C ϖ) 1) = gNum P (Matrix.vecCons (fun k => (c k : ℤ)) L)`. Rewrite using `[ratDiv_one]`.

Conclude with `h1 O ϖ hϖ K ι P (d + 1) hP.multiProj hP.noTorsion hdim.le _`. Take `⟨hGprime, hGhom, hGs⟩` from `h3 O K ι P hP.multiProj hP.noTorsion`. Take `⟨hsG, hsG'⟩` from `hGs s c hs hsP`. Establish `hGdim : ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) < ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Establish `e : d + 2 + Fintype.card K = (d + 1 + Fintype.card K) + 1` using `by omega`.

Rewrite using `[e]`. Use `withBot_lt_of_add_one_le _ _ ?_` and prove the remaining obligations. Use `h2 O K ι P hP.multiProj hP.noTorsion` as an intermediate fact. Rewrite `this` using `[hdim]`. Rewrite `this` using `[show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega]`. Then use the resulting hypothesis.

Establish `hcut` using `h8 (FractionRing O) K ι d (genFib P) hGprime hGhom hGdim _ c hsG hsG' L`. Establish `hcorr` using `h4 O ϖ hϖ K ι P s hP.multiProj.isPrime hP.noTorsion hsP (fun V => intNum (FractionRing O) V L)`. Rewrite using `[cutIdentity, hL, gNum, hcut, ← hcorr]`. Unfold `cycEval`. Use `finsum_congr fun W => ?_` and prove the remaining obligations.

Distinguish the cases in `hW : divCycle P s W = 0`. Rewrite using `[hW, zero_mul, zero_mul]`. Use `congr 1`. Simplify using `only`. Distinguish the cases in `hϖW : (C ϖ : MRing ι O) ∈ W`.

Rewrite using `[if_pos hϖW, if_pos hϖW, vNum_cons_zero]`. Rewrite using `[if_neg hϖW, if_neg hϖW]`. Take `⟨hWmin, hWrel⟩` from `mem_minimalPrimes_of_divCycle_ne_zero hW`. Take `⟨hWprime, hPW, -⟩` from `le_and_isRelevant_of_divCycle_ne_zero hW`. Use `hWprime` as an intermediate fact.

Establish `hWhom : IsMultiHomogIdeal W` using `h5 O K ι (P ⊔ Ideal.span {s}) W (h6 O K ι P s c hP.multiProj.multiHomog hs) hWmin`. Establish `hlt : P < W` using `lt_of_le_of_ne hPW fun h => hsP (h ▸ hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))`. Establish `hWdim : ringKrullDim (MRing ι O ⧸ W) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Use `withBot_le_of_add_one_le _ _ ?_` and prove the remaining obligations. Use `h7 (MRing ι O) P W hlt` as an intermediate fact.

Rewrite `this` using `[hdim]`. Rewrite `this` using `[show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega]`. Then use the resulting hypothesis. Rewrite using `[ratDiv_one]`. Conclude with `(h1 O ϖ hϖ K ι W d ⟨hWprime, hWhom, hWrel⟩ (comap_C_eq_bot_of_not_mem hϖ W hϖW) hWdim L).symm`.
-/
theorem UniformiserCase.proof (h1 : ConservationOfNumberLE.Statement.{u})
    (h2 : GenericDimBound.Statement.{u}) (h3 : GenericFibProps.Statement.{u})
    (h4 : GenericCycleCorresp.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : DimStrictDrop.Statement.{u})
    (h8 : CutByForm.Statement.{u}) : UniformiserCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c s hs hsP L
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    hP.dim
  have := hP.multiProj.isPrime

  have hL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P (C ϖ) 1) =
      gNum P (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
    rw [ratDiv_one]
    exact h1 O ϖ hϖ K ι P (d + 1) hP.multiProj hP.noTorsion hdim.le _

  obtain ⟨hGprime, hGhom, hGs⟩ := h3 O K ι P hP.multiProj hP.noTorsion
  obtain ⟨hsG, hsG'⟩ := hGs s c hs hsP
  have hGdim : ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) <
      ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have e : d + 2 + Fintype.card K = (d + 1 + Fintype.card K) + 1 := by omega
    rw [e]
    refine withBot_lt_of_add_one_le _ _ ?_
    have := h2 O K ι P hP.multiProj hP.noTorsion
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  have hcut := h8 (FractionRing O) K ι d (genFib P) hGprime hGhom hGdim _ c hsG hsG' L
  have hcorr := h4 O ϖ hϖ K ι P s hP.multiProj.isPrime hP.noTorsion hsP
    (fun V => intNum (FractionRing O) V L)
  rw [cutIdentity, hL, gNum, hcut, ← hcorr]

  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : divCycle P s W = 0
  · rw [hW, zero_mul, zero_mul]
  congr 1
  dsimp only
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · rw [if_pos hϖW, if_pos hϖW, vNum_cons_zero]
  rw [if_neg hϖW, if_neg hϖW]
  obtain ⟨hWmin, hWrel⟩ := mem_minimalPrimes_of_divCycle_ne_zero hW
  obtain ⟨hWprime, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have := hWprime
  have hWhom : IsMultiHomogIdeal W :=
    h5 O K ι (P ⊔ Ideal.span {s}) W (h6 O K ι P s c hP.multiProj.multiHomog hs) hWmin
  have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hWmin.1.2
    (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have hWdim : ringKrullDim (MRing ι O ⧸ W) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine withBot_le_of_add_one_le _ _ ?_
    have := h7 (MRing ι O) P W hlt
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  rw [ratDiv_one]
  exact (h1 O ϖ hϖ K ι W d ⟨hWprime, hWhom, hWrel⟩ (comap_C_eq_bot_of_not_mem hϖ W hϖW) hWdim L).symm

end

end GroundTheory.Heights₂.Heights.NumbersDVR
