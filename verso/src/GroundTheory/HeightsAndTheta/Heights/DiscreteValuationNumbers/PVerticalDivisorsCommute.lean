import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Use `((h4 O K ι P f).union (h4 O K ι P g)).subset ?_` and prove the remaining obligations. Introduce `W hW`. Assume the negation of the conclusion as `h`. Simplify using `only [Set.mem_union, Function.mem_support, not_or, not_not] at h`. Conclude with `hW (by simp [ratDiv, h.1, h.2])`.
-/
theorem ratDiv_support_finite (h4 : DivCycleFiniteSupport.Statement.{u}) {O : Type u} [CommRing O]
    [IsNoetherianRing O] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) : (Function.support (ratDiv P f g)).Finite := by
  refine ((h4 O K ι P f).union (h4 O K ι P g)).subset ?_
  intro W hW
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `bot => exact WithBot.bot_lt_coe _`. Consider the case `coe e`. Establish `h' : e + 1 ≤ (n : ℕ∞)` using `by exact_mod_cast h`. Establish `h'' : e < (n : ℕ∞)` using `(ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'`.

Conclude with `h''` after adjusting the coercions.
-/
theorem lt_natCast_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (n : ℕ∞) := by exact_mod_cast h
    have h'' : e < (n : ℕ∞) := (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'
    exact_mod_cast h''

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP b b' f g f' g' hD hD' L`. Take `⟨c', c'', hc', hc'', hb'⟩` from `hD'.degrees`. Take `⟨bf, bg, hbf, hbg, -⟩` from `hD.degrees`. Establish `hPmh : IsMultiHomogIdeal P` using `hP.multiProj.multiHomog`. Establish `: P.IsPrime` using `hP.multiProj.isPrime`.

Establish `hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 → IsMultiHomogIdeal W ∧ W ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant W`. Introduce `h e he W hW`. Unfold `divCycle at hW`. Use `split_ifs at hW with hW'`. Conclude with `⟨h5 O K ι _ W (h6 O K ι P h e hPmh he) hW'.1, hW'.1, hW'.2⟩`.

Conclude with `absurd rfl hW`. Establish `hϖP : (C ϖ : MRing ι O) ∉ P`. Introduce `h`. Establish `h' : ϖ ∈ P.comap (C : O →+* MRing ι O)` using `h`. Rewrite `h'` using `[hP.noTorsion, Ideal.mem_bot]`.

Conclude with `hϖ.ne_zero h'`. Establish `hTfin : {H : Ideal (MRing ι O) | (divCycle P f' H ≠ 0 ∨ divCycle P g' H ≠ 0) ∧ (C ϖ : MRing ι O) ∉ H}.Finite` using `((h4 O K ι P f').union (h4 O K ι P g')).subset fun H hH => hH.1`. Take `⟨f₁, g₁, hV₁, hrat, hT₁⟩` from `h2 O ϖ hϖ K ι P b f g hP.multiProj hD hTfin.toFinset (by`. Introduce `H hH`. Rewrite `hH` using `[Set.Finite.mem_toFinset]`.

Take `⟨hne, hϖH⟩` from `hH`. Break down `hne with hne | hne` into its components or cases. Take `⟨hm, hmin, hrel⟩` from `hmh f' c' hc' H hne`. Conclude with `⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, f', hD'.num_not_mem, hmin⟩`. Take `⟨hm, hmin, hrel⟩` from `hmh g' c'' hc'' H hne`.

Conclude with `⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, g', hD'.den_not_mem, hmin⟩)`. Establish `e1` using `h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c' f' hc' hD'.num_not_mem (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inl hH, hϖH⟩)) L`. Establish `e2` using `h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c'' g' hc'' hD'.den_not_mem (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inr hH, hϖH⟩)) L`. Rewrite `e1`, `e2` using `[hrat]`. Establish `hadd : ∀ W, ratDiv P f g W ≠ 0 → vNum W (Matrix.vecCons b' L) = vNum W (Matrix.vecCons (fun k => (c' k : ℤ)) L) - vNum W (Matrix.vecCons (fun k => (c'' k : ℤ)) L)`.

Introduce `W hW`. Establish `hϖW : (C ϖ : MRing ι O) ∈ W` using `hD.vertical W hW`. Establish `hWdata : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W`. Distinguish the cases in `hWf : divCycle P f W = 0`. Establish `hWg : divCycle P g W ≠ 0`.

Introduce `hWg`. Apply `hW` to reduce the goal to its premises. Simplify using `[ratDiv, hWf, hWg]`. Take `⟨hm, hmin, -⟩` from `hmh g bg hbg W hWg`. Conclude with `⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩`.

Take `⟨hm, hmin, -⟩` from `hmh f bf hbf W hWf`. Conclude with `⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩`. Take `⟨hWm, hWp, hPW⟩` from `hWdata`. Use `hWp` as an intermediate fact. Establish `hlt : P < W` using `lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))`.

Establish `hdrop` using `h10 (MRing ι O) P W hlt`. Rewrite `hdrop` using `[hP.dim]`. Establish `hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) < ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Rewrite using `[h7 O ϖ hϖ K ι W hϖW]`. Establish `e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K` using `by omega`.

Rewrite `hdrop` using `[e]`. Conclude with `lt_natCast_of_add_one_le hdrop`. Establish `key` using `h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W) (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b' (fun k => (c'' k : ℤ)) L`. Establish `hsum : b' + (fun k => (c'' k : ℤ)) = fun k => (c' k : ℤ)`. Rewrite using `[← hb']`.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Rewrite `key` using `[hsum]`. Unfold `vNum`. Rewrite using `[key]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hZfin` using `ratDiv_support_finite h4 P f g`. Combine the equalities or inequalities in the displayed calculation. Unfold `cycEval`. Rewrite using `[← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _)) (hZfin.subset (Function.support_mul_subset_left _ _))]`.

Use `finsum_congr fun W => ?_` and prove the remaining obligations. Distinguish the cases in `hW : ratDiv P f g W = 0`. Simplify using `[hW]`. Use `beta_reduce`. Rewrite using `[hadd W hW, mul_sub]`.

Use `_ = _ := by rw [e1, e2]`. Use `_ = cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g') := by`. Unfold `cycEval`. Rewrite using `[← finsum_sub_distrib ((h4 O K ι P f').subset (Function.support_mul_subset_left _ _)) ((h4 O K ι P g').subset (Function.support_mul_subset_left _ _))]`. Use `finsum_congr fun W => ?_` and prove the remaining obligations.

Rewrite using `[← sub_mul]`. Express the relevant statement in the definitionally equal form `ratDiv P f' g' W * _ = ratDiv P f' g' W * _`. Distinguish the cases in `hW : ratDiv P f' g' W = 0`. Simplify using `[hW]`. Use `beta_reduce`.

Rewrite using `[if_pos (hD'.vertical W hW)]`.
-/
theorem VerticalDivisorsCommute.proof (h1 : CutByEffectiveDivisor.Statement.{u})
    (h2 : Representative.Statement.{u}) (h3 : IntNumAddFirst.Statement.{u})
    (h4 : DivCycleFiniteSupport.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : VerticalDivisorsCommute.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b b' f g f' g' hD hD' L
  obtain ⟨c', c'', hc', hc'', hb'⟩ := hD'.degrees
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P h e hPmh he) hW'.1, hW'.1, hW'.2⟩
    · exact absurd rfl hW
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hTfin : {H : Ideal (MRing ι O) | (divCycle P f' H ≠ 0 ∨ divCycle P g' H ≠ 0) ∧
      (C ϖ : MRing ι O) ∉ H}.Finite :=
    ((h4 O K ι P f').union (h4 O K ι P g')).subset fun H hH => hH.1
  obtain ⟨f₁, g₁, hV₁, hrat, hT₁⟩ := h2 O ϖ hϖ K ι P b f g hP.multiProj hD hTfin.toFinset (by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    obtain ⟨hne, hϖH⟩ := hH
    rcases hne with hne | hne
    · obtain ⟨hm, hmin, hrel⟩ := hmh f' c' hc' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, f', hD'.num_not_mem, hmin⟩
    · obtain ⟨hm, hmin, hrel⟩ := hmh g' c'' hc'' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, g', hD'.den_not_mem, hmin⟩)
  have e1 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c' f' hc' hD'.num_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inl hH, hϖH⟩)) L
  have e2 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c'' g' hc'' hD'.den_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inr hH, hϖH⟩)) L
  rw [hrat] at e1 e2

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons b' L) = vNum W (Matrix.vecCons (fun k => (c' k : ℤ)) L) -
        vNum W (Matrix.vecCons (fun k => (c'' k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    have hWdata : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · have hWg : divCycle P g W ≠ 0 := by
          intro hWg; apply hW; simp [ratDiv, hWf, hWg]
        obtain ⟨hm, hmin, -⟩ := hmh g bg hbg W hWg
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
      · obtain ⟨hm, hmin, -⟩ := hmh f bf hbf W hWf
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
    obtain ⟨hWm, hWp, hPW⟩ := hWdata
    have := hWp
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := h10 (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b' (fun k => (c'' k : ℤ)) L
    have hsum : b' + (fun k => (c'' k : ℤ)) = fun k => (c' k : ℤ) := by
      rw [← hb']; funext k; simp
    rw [hsum] at key
    unfold vNum
    rw [key]; ring
  have hZfin := ratDiv_support_finite h4 P f g
  calc cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g)
      = cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c' k : ℤ)) L)) (ratDiv P f g) -
          cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c'' k : ℤ)) L)) (ratDiv P f g) := by
        unfold cycEval
        rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
          (hZfin.subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        by_cases hW : ratDiv P f g W = 0
        · simp [hW]
        · beta_reduce
          rw [hadd W hW, mul_sub]
    _ = _ := by rw [e1, e2]
    _ = cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g') := by
        unfold cycEval
        rw [← finsum_sub_distrib ((h4 O K ι P f').subset (Function.support_mul_subset_left _ _))
          ((h4 O K ι P g').subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        rw [← sub_mul]
        change ratDiv P f' g' W * _ = ratDiv P f' g' W * _
        by_cases hW : ratDiv P f' g' W = 0
        · simp [hW]
        · beta_reduce
          rw [if_pos (hD'.vertical W hW)]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
