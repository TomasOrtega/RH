import Formalism.SharpRestriction.GrowthBounds.PathWeight.FixedSymbolFactorIntegral

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Asm

variable {p n' r K : ℕ} [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)

local notation "PP" => MvPolynomial (TV n' (r + K)) (KK O)

/- English proof (translation)
Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨o, ho⟩` from `hW2 p n' r K O X j x h`. Conclude with `SyS_of_Sy ho`. Consider the case `zero => simp only [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => simp only [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[map_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]`.

Conclude with `SyS_mul (SyS_of_Sy (Sy_IT (IT_C a))) hx`.
-/
theorem SyS_of_span (hW2 : GeneratorImageIsSymbol) (j : ℤ) {P : SegRing O r K} (hP : P ∈ Submodule.span O (PGen X.Fr j O K)) :
    MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p X.Fr j P) ∈ X.SyS := by
  induction hP using Submodule.span_induction with
  | mem x h =>
    obtain ⟨o, ho⟩ := hW2 p n' r K O X j x h
    exact SyS_of_Sy ho
  | zero => simp only [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [map_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    exact SyS_mul (SyS_of_Sy (Sy_IT (IT_C a))) hx

/- English proof (translation)
Proceed by induction on `hξ using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨P', h1, h2⟩` from `hG x h`. Conclude with `⟨P', h2, SyS_of_span X hW2 j (hW1 p n' r K O X j P' h1)⟩`. Consider the case `zero => exact ⟨0, by simp, by simp only [map_zero]; exact zero_mem _⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨x', a1, a2⟩` from `hx`. Take `⟨y', b1, b2⟩` from `hy`. Conclude with `⟨x' + y', by rw [a1, b1, mul_add], by simp only [map_add]; exact add_mem a2 b2⟩`. Consider the case `smul a x _ hx`.

Take `⟨x', a1, a2⟩` from `hx`. Use `⟨a • x', by rw [a1, mul_smul_comm], ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]`. Conclude with `SyS_mul (SyS_of_Sy (Sy_IT (IT_C a))) a2`.
-/
theorem good_of_span (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (j : ℤ) (Dvj : SegRing O r K) (Gs : Set (SegRing O r K))
    (hG : ∀ P ∈ Gs, ∃ P' ∈ MGen0 X.Fr j O K, P = Dvj * P') {ξ : SegRing O r K} (hξ : ξ ∈ Submodule.span O Gs) :
    ∃ ξ' : SegRing O r K, ξ = Dvj * ξ' ∧
      MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p X.Fr j ξ') ∈ X.SyS := by
  induction hξ using Submodule.span_induction with
  | mem x h =>
    obtain ⟨P', h1, h2⟩ := hG x h
    exact ⟨P', h2, SyS_of_span X hW2 j (hW1 p n' r K O X j P' h1)⟩
  | zero => exact ⟨0, by simp, by simp only [map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', a1, a2⟩ := hx
    obtain ⟨y', b1, b2⟩ := hy
    exact ⟨x' + y', by rw [a1, b1, mul_add], by simp only [map_add]; exact add_mem a2 b2⟩
  | smul a x _ hx =>
    obtain ⟨x', a1, a2⟩ := hx
    refine ⟨a • x', by rw [a1, mul_smul_comm], ?_⟩
    rw [map_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    exact SyS_mul (SyS_of_Sy (Sy_IT (IT_C a))) a2

end Asm

/- English proof (translation)
Introduce `p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII c' g hg n obd xi dd hxi hdd mon hmon hmonT o ho`. Establish `hII'` using `hII`. Unfold `Formalism.MainNotions.SourceCleaning.HypII at hII'`. Take `⟨g1, _, _, _, _, g6, _⟩` from `hII'`. Set `X : Ctx p n' r K O` to `⟨S, hO, hH, Fr, L₁, N₁, G', hV, hT, g1, by omega, g, hg⟩`.

Establish `hA : ∀ (i : Fin n) (j : ℕ), ∃ ξ' : SegRing O r K, j < Fr.J → (xi i j = Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c') * ξ' ∧ MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Fr (j : ℤ) ξ') ∈ X.SyS)`. Introduce `i j`. Distinguish the cases in `hj : j < Fr.J`. Take `⟨ξ', h1, h2⟩` from `good_of_span X hW1 hW2 (j : ℤ) (Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c')) _ (hDiv p n' r K O X deg a Y c0 c'' cStar Dd hII (j : ℤ) (dd j) (hdd j hj)) (hModel O n' r K Fr (j : ℤ) _ _ _ (dd j) (xi i j) (hxi i j hj).1 (hxi i j hj).2)`. Conclude with `⟨ξ', fun _ => ⟨h1, h2⟩⟩`.

Conclude with `⟨0, fun h => absurd h hj⟩`. Use `choose ξ' hξ' using hA`. Take `⟨H, Y0, hH1, hY0, hPhe⟩` from `hPh p n' r K O X c'`. Take `⟨om, hom⟩` from `hMon p n' r K O X mon hmon hmonT`. Use `set Sg : MvPolynomial (TV n' (r + K)) (KK O) := ∑ i, ∏ j ∈ Finset.range Fr.J, MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Fr (j : ℤ) (ξ' i j)) with hSg`.

Establish `hSgS : Sg ∈ X.SyS` using `sum_mem fun i _ => SyS_prod _ _ fun j hj => (hξ' i j (Finset.mem_range.1 hj)).2`. Establish `hSg0 : InWj S.w Sg 0`. Use `inWj_sum _ _ fun i _ => inWj_prod0 _ _ fun j _ => inWj_map _` and prove the remaining obligations. Establish `hT : MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) = (monomial mon 1 * X.DkQ * Sg * H) * X.fixedSymbolFactor c' + C (algebraMap O (KK O) ((p : O) ^ c')) * (monomial mon 1 * Sg * Y0)`. Establish `e1 : monPh O K p Fr mon xi = monomial mon 1 * ((∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (ξ' i j)) * ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c')))`.

Unfold `monPh`. Use `congr 1`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[(hξ' i j (Finset.mem_range.1 hj)).1, map_mul, mul_comm]`. Rewrite using `[e1, map_mul, map_mul, hPhe, map_monomial, map_one, map_sum]`. Simplify using `only [map_prod]`. Rewrite using `[← hSg]`.

Expand and normalize the polynomial expressions, which then agree. Use `core X D c' o _ (monomial mon 1 * X.DkQ * Sg * H) (monomial mon 1 * Sg * Y0) ?_ ?_ hT ?_` and prove the remaining obligations. Conclude with `SyS_mul (SyS_mul (SyS_of_Sy hom) hSgS) (SyS_of_Sy (Sy_IT hH1))`. Conclude with `inWPow_zero_mul (inWPow_zero_mul (bc_inWj_monomial S.w mon) hSg0) hY0`. Introduce `m hm`.

Conclude with `ho m (support_map_subset _ _ hm)`.
-/
theorem lemma4_of_remaining_statements (D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) (hModel : RestModel) (hDiv : RestDivM CLa CD Csz)
    (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (hMon : RestMon) (hPh : RestPh) : Conclusion6 D CLa CD Csz := by
  intro p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII c' g hg n obd xi dd hxi hdd
    mon hmon hmonT o ho
  have hII' := hII
  unfold Formalism.MainNotions.SourceCleaning.HypII at hII'
  obtain ⟨g1, _, _, _, _, g6, _⟩ := hII'
  let X : Ctx p n' r K O := ⟨S, hO, hH, Fr, L₁, N₁, G', hV, hT, g1, by omega, g, hg⟩

  have hA : ∀ (i : Fin n) (j : ℕ), ∃ ξ' : SegRing O r K, j < Fr.J →
      (xi i j = Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c') * ξ' ∧
        MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Fr (j : ℤ) ξ') ∈ X.SyS) := by
    intro i j
    by_cases hj : j < Fr.J
    · obtain ⟨ξ', h1, h2⟩ := good_of_span X hW1 hW2 (j : ℤ) (Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c')) _
        (hDiv p n' r K O X deg a Y c0 c'' cStar Dd hII (j : ℤ) (dd j) (hdd j hj))
        (hModel O n' r K Fr (j : ℤ) _ _ _ (dd j) (xi i j) (hxi i j hj).1 (hxi i j hj).2)
      exact ⟨ξ', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose ξ' hξ' using hA
  obtain ⟨H, Y0, hH1, hY0, hPhe⟩ := hPh p n' r K O X c'
  obtain ⟨om, hom⟩ := hMon p n' r K O X mon hmon hmonT

  set Sg : MvPolynomial (TV n' (r + K)) (KK O) :=
    ∑ i, ∏ j ∈ Finset.range Fr.J, MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Fr (j : ℤ) (ξ' i j)) with hSg
  have hSgS : Sg ∈ X.SyS := sum_mem fun i _ => SyS_prod _ _ fun j hj => (hξ' i j (Finset.mem_range.1 hj)).2
  have hSg0 : InWj S.w Sg 0 := by
    refine inWj_sum _ _ fun i _ => inWj_prod0 _ _ fun j _ => inWj_map _
  have hT : MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) =
      (monomial mon 1 * X.DkQ * Sg * H) * X.fixedSymbolFactor c' +
        C (algebraMap O (KK O) ((p : O) ^ c')) * (monomial mon 1 * Sg * Y0) := by
    have e1 : monPh O K p Fr mon xi = monomial mon 1 *
        ((∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (ξ' i j)) *
          ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c'))) := by
      unfold monPh
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [(hξ' i j (Finset.mem_range.1 hj)).1, map_mul, mul_comm]
    rw [e1, map_mul, map_mul, hPhe, map_monomial, map_one, map_sum]
    simp only [map_prod]
    rw [← hSg]
    ring
  refine core X D c' o _ (monomial mon 1 * X.DkQ * Sg * H) (monomial mon 1 * Sg * Y0) ?_ ?_ hT ?_
  · exact SyS_mul (SyS_mul (SyS_of_Sy hom) hSgS) (SyS_of_Sy (Sy_IT hH1))
  · exact inWPow_zero_mul (inWPow_zero_mul (bc_inWj_monomial S.w mon) hSg0) hY0
  · intro m hm
    exact ho m (support_map_subset _ _ hm)

/- English proof (translation)
Introduce `hA`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `h hA`. Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hE, _⟩` from `hA`. Conclude with `⟨theta_kernel_expansion D, splitting_package_holds D, segment_statement_holds D, order_lemma_holds D, divisibility_of_field_lemma D hE, lemma4_of_remaining_statements D CLa' CD Csz h1 h2 h3 h4 h5 h6⟩`.
-/
theorem stmt_of_rests (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz : ℝ)
    (h : admitted D CLa Ck Crk Cdeg → RestModel ∧ RestDivM CLa' CD Csz ∧ GeneratorSpanInclusion ∧ GeneratorImageIsSymbol ∧ RestMon ∧ RestPh) :
    Stmt D CLa Ck Crk Cdeg CLa' CD Csz := by
  intro hA
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h hA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hE, _⟩ := hA
  exact ⟨theta_kernel_expansion D, splitting_package_holds D, segment_statement_holds D, order_lemma_holds D,
    divisibility_of_field_lemma D hE, lemma4_of_remaining_statements D CLa' CD Csz h1 h2 h3 h4 h5 h6⟩

end Formalism.MainNotions.G.symbolGeneratorData
