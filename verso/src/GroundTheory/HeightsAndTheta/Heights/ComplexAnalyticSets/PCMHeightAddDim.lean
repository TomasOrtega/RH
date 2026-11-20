import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightAddDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRegularElement
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CMDepthAssoc
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HeightCoheightQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `B _ _ hn P hP`. Use `le_antisymm (height_add_ringKrullDim_quotient_le P) ?_` and prove the remaining obligations.

Distinguish the cases in `hmin : P ∈ minimalPrimes B`. Rewrite using `[Ideal.height_eq_zero_iff.mpr hmin, ringKrullDim_quotient_eq_of_mem_minimalPrimes hmin]`. Simplify using the standard rewrite rules. Establish `hfin` using `minimalPrimes.finite_of_isNoetherianRing (R := B)`. Take `⟨y, hyP, hyq⟩ : ∃ y ∈ P, ∀ q ∈ minimalPrimes B, y ∉ q` from `by by_contra! h`.

Establish `hsub : (P : Set B) ⊆ ⋃ i ∈ (↑hfin.toFinset : Set (Ideal B)), (id i : Set B)`. Introduce `z hz`. Take `⟨q, hq, hzq⟩` from `h z hz`. Conclude with `Set.mem_biUnion (by simpa using hq) hzq`. Take `⟨q, hq, hPq⟩` from `(Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥ (fun i hi _ _ => ((Set.Finite.mem_toFinset hfin).mp hi).1.1)).mp hsub`.

Establish `hq' : q ∈ minimalPrimes B` using `(Set.Finite.mem_toFinset hfin).mp hq`. Establish `hqP : q ≤ P` using `hq'.2 ⟨hP, bot_le⟩ hPq`. Conclude with `hmin (le_antisymm hPq hqP ▸ hq')`. Establish `hym : y ∈ maximalIdeal B` using `le_maximalIdeal hP.ne_top hyP`. Take `⟨hynzd, hCM⟩` from `hreg B y hym hyq`.

Establish `hdim` using `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hynzd hym`. Take `⟨rs', -, -, hd'⟩` from `IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B ⧸ Ideal.span {y})`. Establish `hlt : rs'.length < n`. Establish `h1 : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞)`. Rewrite using `[← hn, ← hdim, hd']`.

Use `push_cast`. Both sides reduce to the same expression. Establish `h2 : rs'.length + 1 = n` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers. Establish `hle : Ideal.span {y} ≤ P` using `(Ideal.span_singleton_le_iff_mem P).mpr hyP`.

Establish `hP' : (P.map (Ideal.Quotient.mk (Ideal.span {y}))).IsPrime` using `Ideal.isPrime_map_quotientMk_of_isPrime hle`. Establish `hIH` using `ih rs'.length hlt (B ⧸ Ideal.span {y}) hd' (P.map (Ideal.Quotient.mk (Ideal.span {y})))`. Rewrite `hIH` using `[ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)]`. Establish `hc` using `height_map_add_one_le_of_mem_nonZeroDivisors hynzd P hyP`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hIH]`. Use `_ = (((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by`. Rewrite using `[WithBot.coe_add, WithBot.coe_one, add_right_comm]`. Use `_ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by gcongr`. Conclude with `hc` after adjusting the coercions.
-/
theorem CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime (hreg : CMRegularElement.Statement.{u}) :
    ∀ (n : ℕ) (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B], ringKrullDim B = n →
      ∀ (P : Ideal B) [P.IsPrime], (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) = ringKrullDim B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B _ _ hn P hP
  refine le_antisymm (height_add_ringKrullDim_quotient_le P) ?_
  by_cases hmin : P ∈ minimalPrimes B
  · rw [Ideal.height_eq_zero_iff.mpr hmin, ringKrullDim_quotient_eq_of_mem_minimalPrimes hmin]
    simp

  have hfin := minimalPrimes.finite_of_isNoetherianRing (R := B)
  obtain ⟨y, hyP, hyq⟩ : ∃ y ∈ P, ∀ q ∈ minimalPrimes B, y ∉ q := by
    by_contra! h
    have hsub : (P : Set B) ⊆ ⋃ i ∈ (↑hfin.toFinset : Set (Ideal B)), (id i : Set B) := by
      intro z hz
      obtain ⟨q, hq, hzq⟩ := h z hz
      exact Set.mem_biUnion (by simpa using hq) hzq
    obtain ⟨q, hq, hPq⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun i hi _ _ => ((Set.Finite.mem_toFinset hfin).mp hi).1.1)).mp hsub
    have hq' : q ∈ minimalPrimes B := (Set.Finite.mem_toFinset hfin).mp hq
    have hqP : q ≤ P := hq'.2 ⟨hP, bot_le⟩ hPq
    exact hmin (le_antisymm hPq hqP ▸ hq')
  have hym : y ∈ maximalIdeal B := le_maximalIdeal hP.ne_top hyP
  obtain ⟨hynzd, hCM⟩ := hreg B y hym hyq
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hynzd hym
  obtain ⟨rs', -, -, hd'⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B ⧸ Ideal.span {y})
  have hlt : rs'.length < n := by
    have h1 : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hn, ← hdim, hd']
      push_cast
      rfl
    have h2 : rs'.length + 1 = n := by exact_mod_cast h1
    omega
  have hle : Ideal.span {y} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk (Ideal.span {y}))).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hle
  have hIH := ih rs'.length hlt (B ⧸ Ideal.span {y}) hd' (P.map (Ideal.Quotient.mk (Ideal.span {y})))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hIH
  have hc := height_map_add_one_le_of_mem_nonZeroDivisors hynzd P hyP
  calc ringKrullDim B = ringKrullDim (B ⧸ Ideal.span {y}) + 1 := hdim.symm
    _ = ((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) + 1 := by
        rw [hIH]
    _ = (((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        rw [WithBot.coe_add, WithBot.coe_one, add_right_comm]
    _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        gcongr
        exact_mod_cast hc

/- English proof (translation)
Introduce `B _ _ J hJ`. Take `⟨rs, -, -, hd⟩` from `IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)`. Establish `hprime` using `CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime hreg rs.length B hd`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Establish `: Nontrivial (B ⧸ J)` using `Ideal.Quotient.nontrivial_iff.mpr hJ`.

Establish `: Nonempty (PrimeSpectrum (B ⧸ J))` using `inferInstance`. Rewrite using `[show ringKrullDim (B ⧸ J) = Order.krullDim (PrimeSpectrum (B ⧸ J)) from rfl, Order.krullDim_eq_iSup_coheight_of_nonempty, ← WithBot.coe_add, ENat.add_iSup, WithBot.coe_iSup (OrderTop.bddAbove _)]`. Use `iSup_le fun a => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `a`. Use `set Q := a.comap (Ideal.Quotient.mk J) with hQdef`.

Establish `hQ : Q.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hJQ : J ≤ Q` using `fun z hz => by`. Rewrite using `[hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]`. Conclude with `Ideal.zero_mem _`. Establish `hmap : a = Q.map (Ideal.Quotient.mk J)` using `(Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective a).symm`.

Establish `hco : (Order.coheight (⟨a, ha⟩ : PrimeSpectrum (B ⧸ J)) : WithBot ℕ∞) = ringKrullDim (B ⧸ Q)`. Rewrite using `[← ringKrullDim_quotient_eq_coheight a, ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE hJQ))]`. Rewrite using `[WithBot.coe_add, hco, ← hprime Q]`. Use `gcongr`. Conclude with `Ideal.height_mono hJQ` after adjusting the coercions.

Take `⟨P, hPmin, hPle⟩` from `Set.exists_min_image J.minimalPrimes Ideal.height (Ideal.finite_minimalPrimes_of_isNoetherianRing B J) (Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes hJ))`. Establish `: P.IsPrime` using `hPmin.1.1`. Establish `hht : J.height = P.height`. Rewrite using `[Ideal.height_eq_inf_minimalPrimes]`. Conclude with `le_antisymm (iInf₂_le P hPmin) (le_iInf₂ fun Q hQ => hPle Q hQ)`.

Rewrite using `[hht, ← hprime P]`. Use `gcongr`. Conclude with `ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hPmin.1.2)`.
-/
theorem CMHeightAddDim.proof (hreg : CMRegularElement.Statement.{u}) : CMHeightAddDim.Statement.{u} := by
  intro B _ _ J hJ
  obtain ⟨rs, -, -, hd⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hprime := CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime hreg rs.length B hd
  refine le_antisymm ?_ ?_
  ·
    have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    have : Nonempty (PrimeSpectrum (B ⧸ J)) := inferInstance
    rw [show ringKrullDim (B ⧸ J) = Order.krullDim (PrimeSpectrum (B ⧸ J)) from rfl,
      Order.krullDim_eq_iSup_coheight_of_nonempty, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (OrderTop.bddAbove _)]
    refine iSup_le fun a => ?_
    obtain ⟨a, ha⟩ := a
    set Q := a.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hJQ : J ≤ Q := fun z hz => by
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact Ideal.zero_mem _
    have hmap : a = Q.map (Ideal.Quotient.mk J) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective a).symm
    have hco : (Order.coheight (⟨a, ha⟩ : PrimeSpectrum (B ⧸ J)) : WithBot ℕ∞) = ringKrullDim (B ⧸ Q) := by
      rw [← ringKrullDim_quotient_eq_coheight a,
        ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE hJQ))]
    rw [WithBot.coe_add, hco, ← hprime Q]
    gcongr
    exact_mod_cast Ideal.height_mono hJQ
  ·
    obtain ⟨P, hPmin, hPle⟩ := Set.exists_min_image J.minimalPrimes Ideal.height
      (Ideal.finite_minimalPrimes_of_isNoetherianRing B J) (Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes hJ))
    have : P.IsPrime := hPmin.1.1
    have hht : J.height = P.height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      exact le_antisymm (iInf₂_le P hPmin) (le_iInf₂ fun Q hQ => hPle Q hQ)
    rw [hht, ← hprime P]
    gcongr
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hPmin.1.2)

end GroundTheory.Heights₂.Heights
