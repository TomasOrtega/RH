import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hdiv`. Establish `hsupp : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W`. Assume the negation of the conclusion as `h`. Conclude with `hdiv (by unfold divCycle; rw [dif_neg h])`. Establish `hWp : W.IsPrime` using `hsupp.1.1.1`.

Use `hP.multiProj.isPrime` as an intermediate fact. Take `⟨i, hi⟩` from `powMonomial_not_mem hWp hsupp.2 c`. Establish `hg : IsMultiHomog (powMonomial c i : MRing ι O) c` using `isMultiHomog_powMonomial c i`. Establish `hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (powMonomial c i)) ∈ homLocRing P W` using `Subring.subset_closure ⟨c, x, _, hx, hg, hi, rfl⟩`. Take `⟨hloc, hnoeth, hdim⟩` from `ha O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2`.

Use `hloc` as an intermediate fact. Use `hnoeth` as an intermediate fact. Take `⟨B, _, _, _, hfin, hinj, hrank, e, he⟩` from `hd O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hsupp.1 hsupp.2 _ hg hi hz`. Establish `hz0 : (⟨_, hz⟩ : homLocRing P W) ≠ 0`. Introduce `h0`.

Establish `h1` using `congrArg (fun w : homLocRing P W => (w : FractionRing (MRing ι O ⧸ P))) h0`. Simplify using `only [ZeroMemClass.coe_zero] at h1`. Break down `div_eq_zero_iff.mp h1 with h | h` into its components or cases. Conclude with `hxP (Ideal.Quotient.eq_zero_iff_mem.mp ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))`. Conclude with `hi (hsupp.1.1.2 (Ideal.mem_sup_left (Ideal.Quotient.eq_zero_iff_mem.mp ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))))`.

Take `⟨hfinite, hlen⟩` from `hc (homLocRing P W) B hdim hinj hrank _ hz0`. Establish `hmult` using `hb O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2 _ hg hi hz`. Establish `hdivW : divCycle P x W = ((multAt (P ⊔ Ideal.span {x}) W).toNat : ℤ)`. Unfold `divCycle`. Rewrite using `[dif_pos hsupp]`.

Use `Fintype.ofFinite {𝔫 : Ideal B // 𝔫.IsMaximal}` as an intermediate fact. Establish `hterm : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal}, (have` using `𝔫.2.isPrime Module.length (Localization.AtPrime 𝔫.1) (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1) (algebraMap (homLocRing P W) B ⟨_, hz⟩)})) * (𝔫.1.inertiaDeg (homLocRing P W) : ℕ∞) = (((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat * spec …`. Introduce `𝔫`. Rewrite using `[(he 𝔫).1, (he 𝔫).2, Nat.cast_mul]`. Rewrite `hlen` using `[finsum_congr hterm, finsum_eq_sum_of_fintype, ← Nat.cast_sum]`.

Rewrite using `[hdivW, hmult, hlen, ENat.toNat_natCast, Nat.cast_sum]`. Set `p : Ideal (MRing (extIdx ι J) O) → Prop` to `fun W' => W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧ W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W`. Establish `hite : ∀ W' : Ideal (MRing (extIdx ι J) O), (if W'.comap (liftForm (ι` using `ι) (J := J) (R := O)) = W then divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) = ∑ᶠ (_ : p W'), divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) := by`. Introduce `W'`. Rewrite using `[finsum_eq_if]`.

Distinguish the cases in `hc' : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W`. Distinguish the cases in `hp : p W'`. Rewrite using `[if_pos hc', if_pos hp]`. Rewrite using `[if_pos hc', if_neg hp]`. Establish `h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0`.

Unfold `divCycle`. Rewrite using `[dif_neg]`. Conclude with `fun h => hp ⟨h.1, h.2, hc'⟩`. Rewrite using `[h0, zero_mul]`. Rewrite using `[if_neg hc', if_neg (fun h => hc' h.2.2)]`.

Rewrite using `[finsum_congr hite, ← finsum_subtype_eq_finsum_cond p, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]`. Use `Finset.sum_congr rfl fun 𝔫 _ => ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1`. Unfold `divCycle`. Apply the tactic sequence `split_ifs <;> positivity`.

Rewrite using `[Nat.cast_mul, Int.toNat_of_nonneg h0]`.
-/
theorem BlowUpFibreDegree.proof (ha : HomLocRingLocal.Statement.{u}) (hb : DivCycleHomLoc.Statement.{u})
    (hc : FiniteBirationalLength.Statement.{u}) (hd : BlowUpFibreSemilocal.Statement.{u}) :
    BlowUpFibreDegree.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hdiv
  have hsupp : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hdiv (by unfold divCycle; rw [dif_neg h])
  have hWp : W.IsPrime := hsupp.1.1.1
  have := hP.multiProj.isPrime
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hsupp.2 c
  have hg : IsMultiHomog (powMonomial c i : MRing ι O) c := isMultiHomog_powMonomial c i
  have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
        (Ideal.Quotient.mk P (powMonomial c i)) ∈ homLocRing P W :=
    Subring.subset_closure ⟨c, x, _, hx, hg, hi, rfl⟩
  obtain ⟨hloc, hnoeth, hdim⟩ := ha O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2
  have := hloc
  have := hnoeth
  obtain ⟨B, _, _, _, hfin, hinj, hrank, e, he⟩ :=
    hd O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hsupp.1 hsupp.2 _ hg hi hz
  have hz0 : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun w : homLocRing P W => (w : FractionRing (MRing ι O ⧸ P))) h0
    simp only [ZeroMemClass.coe_zero] at h1
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))
    · exact hi (hsupp.1.1.2 (Ideal.mem_sup_left (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))))
  obtain ⟨hfinite, hlen⟩ := hc (homLocRing P W) B hdim hinj hrank _ hz0
  have hmult := hb O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2 _ hg hi hz
  have hdivW : divCycle P x W = ((multAt (P ⊔ Ideal.span {x}) W).toNat : ℤ) := by
    unfold divCycle
    rw [dif_pos hsupp]
  have := Fintype.ofFinite {𝔫 : Ideal B // 𝔫.IsMaximal}

  have hterm : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
      (have := 𝔫.2.isPrime
       Module.length (Localization.AtPrime 𝔫.1)
         (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1)
           (algebraMap (homLocRing P W) B ⟨_, hz⟩)})) * (𝔫.1.inertiaDeg (homLocRing P W) : ℕ∞) =
        (((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat * specialRelDeg (e 𝔫).1 : ℕ) : ℕ∞) := by
    intro 𝔫
    rw [(he 𝔫).1, (he 𝔫).2, Nat.cast_mul]
  rw [finsum_congr hterm, finsum_eq_sum_of_fintype, ← Nat.cast_sum] at hlen
  rw [hdivW, hmult, hlen, ENat.toNat_natCast, Nat.cast_sum]

  classical
  let p : Ideal (MRing (extIdx ι J) O) → Prop := fun W' =>
    W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
  have hite : ∀ W' : Ideal (MRing (extIdx ι J) O),
      (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
        divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) =
      ∑ᶠ (_ : p W'), divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) := by
    intro W'
    rw [finsum_eq_if]
    by_cases hc' : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
    · by_cases hp : p W'
      · rw [if_pos hc', if_pos hp]
      · rw [if_pos hc', if_neg hp]
        have h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0 := by
          unfold divCycle
          rw [dif_neg]
          exact fun h => hp ⟨h.1, h.2, hc'⟩
        rw [h0, zero_mul]
    · rw [if_neg hc', if_neg (fun h => hc' h.2.2)]
  rw [finsum_congr hite, ← finsum_subtype_eq_finsum_cond p,
    ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have h0 : 0 ≤ divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1 := by
    unfold divCycle
    split_ifs <;> positivity
  rw [Nat.cast_mul, Int.toNat_of_nonneg h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
