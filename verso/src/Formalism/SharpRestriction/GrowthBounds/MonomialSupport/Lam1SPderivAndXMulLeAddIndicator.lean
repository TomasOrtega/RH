import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.SupportSubNuSet

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.LetterSubstitution

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.PairMembershipBlocks

section TotallyRealRoots

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

/- English proof (translation)
Distinguish the cases in `hx : x0 ∈ S`. Simplify using `only [hx, if_true]`. Use `⟨Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_pderiv_le_add_one LL S Fp (x0, b), Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_le_add_one LL S Fp (x0, b), ?_⟩` and prove the remaining obligations. Consider the cases of `hv : LL.vec x0`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hx, if_false, WithBot.coe_zero, add_zero]`. Establish `h1` using `Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_pderiv_le_of LL S Fp (x0, b) (fun h => absurd h hx)`. Establish `h2` using `Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_le_of LL S Fp (x0, b) (fun h => absurd h hx)`. Establish `h3` using `Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_le_of LL S (pderiv (x0, b) Fp) (x0, b) (fun h => absurd h hx)`.

Conclude with `⟨h1, h2, h3.trans h1⟩`.
-/
theorem lam1S_pderiv_and_X_mul_le_add_indicator (x0 : ι) (b : Fin n) (Fp : MvPolynomial (ι × Fin n) R) :
    lam1S LL S (pderiv (x0, b) Fp) ≤ lam1S LL S Fp + (((if x0 ∈ S then 1 else 0 : ℤ)) : WithBot ℤ) ∧
    lam1S LL S (X (x0, b) * Fp) ≤ lam1S LL S Fp + (((if x0 ∈ S then 1 else 0 : ℤ)) : WithBot ℤ) ∧
    lam1S LL S (X (x0, b) * pderiv (x0, b) Fp) ≤ lam1S LL S Fp + (((if x0 ∈ S then 1 else 0 : ℤ)) : WithBot ℤ) := by
  by_cases hx : x0 ∈ S
  · simp only [hx, if_true]
    refine ⟨Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_pderiv_le_add_one LL S Fp (x0, b), Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_le_add_one LL S Fp (x0, b), ?_⟩
    cases hv : LL.vec x0
    · calc lam1S LL S (X (x0, b) * pderiv (x0, b) Fp) ≤ lam1S LL S (pderiv (x0, b) Fp) :=
            Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_le_of LL S _ (x0, b) (fun _ => hv)
        _ ≤ lam1S LL S Fp + ((1 : ℤ) : WithBot ℤ) := Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_pderiv_le_add_one LL S Fp (x0, b)
    · calc lam1S LL S (X (x0, b) * pderiv (x0, b) Fp) ≤ lam1S LL S (pderiv (x0, b) Fp) + ((1 : ℤ) : WithBot ℤ) :=
            Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_le_add_one LL S _ (x0, b)
        _ ≤ lam1S LL S Fp + ((1 : ℤ) : WithBot ℤ) :=
            add_le_add (Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_pderiv_le_of LL S Fp (x0, b) (fun _ => hv)) le_rfl
  · simp only [hx, if_false, WithBot.coe_zero, add_zero]
    have h1 := Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_pderiv_le_of LL S Fp (x0, b) (fun h => absurd h hx)
    have h2 := Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_le_of LL S Fp (x0, b) (fun h => absurd h hx)
    have h3 := Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_X_mul_le_of LL S (pderiv (x0, b) Fp) (x0, b) (fun h => absurd h hx)
    exact ⟨h1, h2, h3.trans h1⟩

end TotallyRealRoots

/- English proof (translation)
Introduce `D p _ O _ _ _ _ r J n' _ _ K _ hSet hR Dt x0 b T hT d th thL G ka' e he hG nu`. Establish `hee` using `fun i => (eeN_spec D K Dt i).1`. Establish `hdec` using `fun i => (eeN_spec D K Dt i).2`. Establish `hcomm` using `eeN_comm D K Dt hSet hR`. Establish `hin0 : ∀ j u, 0 ≤ inN Dt.nL x0 j u`.

Introduce `j u`. Unfold `inN`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hTb : ∀ (j : ZMod J) (u : ℕ) (z : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)), lam1S Dt.trueLet (NSet Dt.nL j u) (T z) ≤ lam1S Dt.trueLet (NSet Dt.nL j u) z + ((inN Dt.nL x0 j u : ℤ) : WithBot ℤ)`. Introduce `j u z`.

Establish `h3` using `lam1S_pderiv_and_X_mul_le_add_indicator Dt.trueLet (NSet Dt.nL j u) x0 b z`. Establish `hin : inN Dt.nL x0 j u = (if x0 ∈ NSet Dt.nL j u then 1 else 0 : ℤ)` using `rfl`. Rewrite using `[hin]`. Break down `hT with rfl | rfl | rfl` into its components or cases. Conclude with `h3.1`.

Conclude with `h3.2.1`. Conclude with `h3.2.2`. Establish `hkill : ∀ (κ : (Σ j : ZMod J, Fin (Dt.nL j + r + 1)) → Fin K → ℤ) (i : Σ j : ZMod J, Fin (Dt.nL j + r + 1)), κ i 0 + inN Dt.nL x0 i.1 i.2.val < ka' i.1 i.2.val 0 → ∀ y, e (T (jointE (eeN D K Dt) κ y)) = 0`. Introduce `κ i hlt y`. Use `set z := jointE (eeN D K Dt) κ y`.

Establish `hz : z ∈ isoSub (normE p K Dt i) (κ i)` using `(jointN_props D K Dt hSet hR κ).2.2.2 y i`. Establish `hV` using `(Formalism.MainNotions.G.GLWeightTheory.valuation_field D).2 (KK O) (TL J Dt.nL r) Dt.trueLet K (NSet Dt.nL i.1 i.2.val) (eeN D K Dt i) (hee i)`. Establish `hzb : lam1S Dt.trueLet (NSet Dt.nL i.1 i.2.val) z ≤ ((κ i 0 : ℤ) : WithBot ℤ)`. Use `(hV.2 z (κ i 0)).2 (fun mu hmu => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Conclude with `hmu ((hee i mu).2 (κ i) (fun h => hne (le_of_eq (congrFun h.symm 0))) z hz)`. Establish `hwb : lam1S Dt.trueLet (NSet Dt.nL i.1 i.2.val) (T z) ≤ ((κ i 0 + inN Dt.nL x0 i.1 i.2.val : ℤ) : WithBot ℤ)`. Combine the equalities or inequalities in the displayed calculation. Use `set w := T z`. Establish `hw0 : eeN D K Dt i (ka' i.1 i.2.val) w = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `absurd ((hV.2 w (κ i 0 + inN Dt.nL x0 i.1 i.2.val)).1 hwb _ hne) (not_le.mpr hlt)`. Take `⟨Sw, hSw⟩` from `joint_dec (normE p K Dt) (eeN D K Dt) hee hcomm hdec w`. Rewrite using `[hSw (insert (fun i => ka' i.1 i.2.val) Sw) (Finset.subset_insert _ _), map_sum]`. Use `Finset.sum_eq_zero (fun κ' _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hk : κ' = fun i => ka' i.1 i.2.val`. Substitute `hk` using the available equality. Take `⟨rest, _, h2⟩` from `jointE_factor hcomm (fun i => ka' i.1 i.2.val) i`. Rewrite using `[h2]`. Simplify using `[hw0]`.

Use `he.2 κ' hk _ ?_` and prove the remaining obligations. Simplify using `only [jIso, Submodule.mem_iInf]`. Conclude with `fun i' => (jointN_props D K Dt hSet hR κ').2.2.2 w i'`. Establish `hJ : ∀ y : MvPolynomial (TL J Dt.nL r × Fin K) (KK O), ∃ Sy : Finset ((Σ j : ZMod J, Fin (Dt.nL j + r + 1)) → Fin K → ℤ), ∀ S', Sy ≤ S' → y = ∑ κ ∈ S', jointE (eeN D K Dt) κ y` using `fun y => joint_dec (normE p K Dt) (eeN D K Dt) hee hcomm hdec y`. Use `choose Sy hSy using hJ`.

Establish `hsplit : oneT (e * T) G = ∑ κ ∈ G.support.biUnion (fun mo => Sy (G.coeff mo)), oneT (e * T * jointE (eeN D K Dt) κ) G`. Use extensionality with `mo : 1`. Rewrite using `[MvPolynomial.coeff_sum, coeff_oneT]`. Simplify using `only [coeff_oneT]`. Distinguish the cases in `hmo : mo ∈ G.support`.

Use `conv_lhs => rw [hSy (G.coeff mo) _ (Finset.subset_biUnion_of_mem (fun mo => Sy (G.coeff mo)) hmo)]`. Rewrite using `[map_sum]`. Simplify using `only [Module.End.mul_apply]`. Simplify using `only [MvPolynomial.mem_support_iff, not_not] at hmo`. Simplify using `[hmo]`.

Rewrite using `[hsplit, planeCoeff_sum]`. Use `XXg_sum Dt d th thL _ _ (fun κ _ => ?_)` and prove the remaining obligations. Use `show XXg Dt d th thL (planeCoeff nu (oneT (e * T * jointE (eeN D K Dt) κ) G))`. Set `ka : ZMod J → ℕ → Fin K → ℤ` to `fun j u => if h : u < Dt.nL j + r + 1 then κ ⟨j, ⟨u, h⟩⟩ else ka' j u`. Establish `hka : (fun i : (Σ j : ZMod J, Fin (Dt.nL j + r + 1)) => ka i.1 i.2.val) = κ`.

Use function extensionality and compare the values at `i`. Take `⟨j, u⟩` from `i`. Conclude with `dif_pos u.isLt`. Distinguish the cases in `hC : ∀ j u, ka' j u 0 ≤ ka j u 0 + inN Dt.nL x0 j u`. Establish `hP : IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} (jointE (eeN D K Dt) κ)`.

Rewrite using `[hka]`. Conclude with `(jointN_props D K Dt hSet hR κ).1`. Establish `hX` using `hG ka hC (jointE (eeN D K Dt) κ) hP`. Rewrite using `[oneT_mul, planeCoeff_oneT]`. Conclude with `XXg_sum Dt d th thL _ _ (fun nu' _ => XXg_smul Dt d th thL _ (hX nu'))`.

Simplify using `only [not_forall, not_le] at hC`. Take `⟨j, u, hju⟩` from `hC`. Establish `hu : u < Dt.nL j + r + 1`. Assume the negation of the conclusion as `hu`. Establish `hk : ka j u = ka' j u` using `dif_neg hu`.

Rewrite `hju` using `[hk]`. Combine the linear relations using `[hin0 j u]`. Establish `hki : κ ⟨j, ⟨u, hu⟩⟩ = ka j u` using `by show κ ⟨j, ⟨u, hu⟩⟩ = (if h : u < Dt.nL j + r + 1 then κ ⟨j, ⟨u, h⟩⟩ else ka' j u)`. Rewrite using `[dif_pos hu]`. Establish `hlt : κ ⟨j, ⟨u, hu⟩⟩ 0 + inN Dt.nL x0 j u < ka' j u 0`.

Rewrite using `[hki]`. Conclude with `hju`. Rewrite using `[oneT_eq_zero _ _ (fun mo => hkill κ ⟨j, ⟨u, hu⟩⟩ hlt (G.coeff mo)), planeCoeff_zero']`. Conclude with `XXg_zero Dt d th thL`.
-/
theorem noOpStep : NoOpStep := by
  intro D p _ O _ _ _ _ r J n' _ _ K _ hSet hR Dt x0 b T hT d th thL G ka' e he hG nu
  have hee := fun i => (eeN_spec D K Dt i).1
  have hdec := fun i => (eeN_spec D K Dt i).2
  have hcomm := eeN_comm D K Dt hSet hR
  have hin0 : ∀ j u, 0 ≤ inN Dt.nL x0 j u := by
    intro j u
    unfold inN
    split_ifs <;> norm_num
  have hTb : ∀ (j : ZMod J) (u : ℕ) (z : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)),
      lam1S Dt.trueLet (NSet Dt.nL j u) (T z) ≤
        lam1S Dt.trueLet (NSet Dt.nL j u) z + ((inN Dt.nL x0 j u : ℤ) : WithBot ℤ) := by
    intro j u z
    have h3 := lam1S_pderiv_and_X_mul_le_add_indicator Dt.trueLet (NSet Dt.nL j u) x0 b z
    have hin : inN Dt.nL x0 j u = (if x0 ∈ NSet Dt.nL j u then 1 else 0 : ℤ) := rfl
    rw [hin]
    rcases hT with rfl | rfl | rfl
    · exact h3.1
    · exact h3.2.1
    · exact h3.2.2
  have hkill : ∀ (κ : (Σ j : ZMod J, Fin (Dt.nL j + r + 1)) → Fin K → ℤ)
      (i : Σ j : ZMod J, Fin (Dt.nL j + r + 1)),
      κ i 0 + inN Dt.nL x0 i.1 i.2.val < ka' i.1 i.2.val 0 →
      ∀ y, e (T (jointE (eeN D K Dt) κ y)) = 0 := by
    intro κ i hlt y
    set z := jointE (eeN D K Dt) κ y
    have hz : z ∈ isoSub (normE p K Dt i) (κ i) := (jointN_props D K Dt hSet hR κ).2.2.2 y i
    have hV := (Formalism.MainNotions.G.GLWeightTheory.valuation_field D).2 (KK O) (TL J Dt.nL r) Dt.trueLet K
      (NSet Dt.nL i.1 i.2.val) (eeN D K Dt i) (hee i)
    have hzb : lam1S Dt.trueLet (NSet Dt.nL i.1 i.2.val) z ≤ ((κ i 0 : ℤ) : WithBot ℤ) := by
      refine (hV.2 z (κ i 0)).2 (fun mu hmu => ?_)
      by_contra hne
      exact hmu ((hee i mu).2 (κ i) (fun h => hne (le_of_eq (congrFun h.symm 0))) z hz)
    have hwb : lam1S Dt.trueLet (NSet Dt.nL i.1 i.2.val) (T z) ≤
        ((κ i 0 + inN Dt.nL x0 i.1 i.2.val : ℤ) : WithBot ℤ) := by
      calc lam1S Dt.trueLet (NSet Dt.nL i.1 i.2.val) (T z)
          ≤ lam1S Dt.trueLet (NSet Dt.nL i.1 i.2.val) z + ((inN Dt.nL x0 i.1 i.2.val : ℤ) : WithBot ℤ) :=
            hTb i.1 i.2.val z
        _ ≤ ((κ i 0 : ℤ) : WithBot ℤ) + ((inN Dt.nL x0 i.1 i.2.val : ℤ) : WithBot ℤ) :=
            add_le_add hzb le_rfl
        _ = ((κ i 0 + inN Dt.nL x0 i.1 i.2.val : ℤ) : WithBot ℤ) := by norm_cast
    set w := T z
    have hw0 : eeN D K Dt i (ka' i.1 i.2.val) w = 0 := by
      by_contra hne
      exact absurd ((hV.2 w (κ i 0 + inN Dt.nL x0 i.1 i.2.val)).1 hwb _ hne) (not_le.mpr hlt)
    obtain ⟨Sw, hSw⟩ := joint_dec (normE p K Dt) (eeN D K Dt) hee hcomm hdec w
    rw [hSw (insert (fun i => ka' i.1 i.2.val) Sw) (Finset.subset_insert _ _), map_sum]
    refine Finset.sum_eq_zero (fun κ' _ => ?_)
    by_cases hk : κ' = fun i => ka' i.1 i.2.val
    · subst hk
      obtain ⟨rest, _, h2⟩ := jointE_factor hcomm (fun i => ka' i.1 i.2.val) i
      rw [h2]
      simp [hw0]
    · refine he.2 κ' hk _ ?_
      simp only [jIso, Submodule.mem_iInf]
      exact fun i' => (jointN_props D K Dt hSet hR κ').2.2.2 w i'
  have hJ : ∀ y : MvPolynomial (TL J Dt.nL r × Fin K) (KK O),
      ∃ Sy : Finset ((Σ j : ZMod J, Fin (Dt.nL j + r + 1)) → Fin K → ℤ),
        ∀ S', Sy ≤ S' → y = ∑ κ ∈ S', jointE (eeN D K Dt) κ y :=
    fun y => joint_dec (normE p K Dt) (eeN D K Dt) hee hcomm hdec y
  choose Sy hSy using hJ
  have hsplit : oneT (e * T) G =
      ∑ κ ∈ G.support.biUnion (fun mo => Sy (G.coeff mo)), oneT (e * T * jointE (eeN D K Dt) κ) G := by
    ext mo : 1
    rw [MvPolynomial.coeff_sum, coeff_oneT]
    simp only [coeff_oneT]
    by_cases hmo : mo ∈ G.support
    · conv_lhs => rw [hSy (G.coeff mo) _ (Finset.subset_biUnion_of_mem (fun mo => Sy (G.coeff mo)) hmo)]
      rw [map_sum]
      simp only [Module.End.mul_apply]
    · simp only [MvPolynomial.mem_support_iff, not_not] at hmo
      simp [hmo]
  rw [hsplit, planeCoeff_sum]
  refine XXg_sum Dt d th thL _ _ (fun κ _ => ?_)
  show XXg Dt d th thL (planeCoeff nu (oneT (e * T * jointE (eeN D K Dt) κ) G))
  let ka : ZMod J → ℕ → Fin K → ℤ := fun j u =>
    if h : u < Dt.nL j + r + 1 then κ ⟨j, ⟨u, h⟩⟩ else ka' j u
  have hka : (fun i : (Σ j : ZMod J, Fin (Dt.nL j + r + 1)) => ka i.1 i.2.val) = κ := by
    funext i
    obtain ⟨j, u⟩ := i
    exact dif_pos u.isLt
  by_cases hC : ∀ j u, ka' j u 0 ≤ ka j u 0 + inN Dt.nL x0 j u
  · have hP : IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} (jointE (eeN D K Dt) κ) := by
      rw [hka]
      exact (jointN_props D K Dt hSet hR κ).1
    have hX := hG ka hC (jointE (eeN D K Dt) κ) hP
    rw [oneT_mul, planeCoeff_oneT]
    exact XXg_sum Dt d th thL _ _ (fun nu' _ => XXg_smul Dt d th thL _ (hX nu'))
  · simp only [not_forall, not_le] at hC
    obtain ⟨j, u, hju⟩ := hC
    have hu : u < Dt.nL j + r + 1 := by
      by_contra hu
      have hk : ka j u = ka' j u := dif_neg hu
      rw [hk] at hju
      linarith [hin0 j u]
    have hki : κ ⟨j, ⟨u, hu⟩⟩ = ka j u := by
      show κ ⟨j, ⟨u, hu⟩⟩ = (if h : u < Dt.nL j + r + 1 then κ ⟨j, ⟨u, h⟩⟩ else ka' j u)
      rw [dif_pos hu]
    have hlt : κ ⟨j, ⟨u, hu⟩⟩ 0 + inN Dt.nL x0 j u < ka' j u 0 := by
      rw [hki]
      exact hju
    rw [oneT_eq_zero _ _ (fun mo => hkill κ ⟨j, ⟨u, hu⟩⟩ hlt (G.coeff mo)), planeCoeff_zero']
    exact XXg_zero Dt d th thL

end Formalism.MainNotions.LetterSubstitution
