import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : ∃ N : ℕ, ∀ τ i, i < Dw.mult τ → -(N : ℤ) ≤ G.1 (τ, i) := by`. Take `⟨B, hB⟩` from `(Set.finite_range fun x : Formalism.L2.Pj.Ix Dw => (Formalism.L2.Pj.exZ Dw G x).natAbs).bddAbove`. Use `⟨B, fun τ i hi => ?_⟩` and prove the remaining obligations. Establish `h1 : (G.1 (τ, i)).natAbs ≤ B` using `hB ⟨some ⟨τ, ⟨i, hi⟩⟩, rfl⟩`. Use linear arithmetic over natural numbers and integers.

Establish `hpos : ∀ τ i, i < Dw.mult τ → 1 ≤ (t : ℤ) * G.1 (τ, i) + ((t * N + 1 : ℕ) : ℤ) * a (τ, i)`. Introduce `τ i hi`. Establish `h1` using `hN τ i hi`. Establish `h3 : (2 : ℤ) ≤ a (τ, i)` using `by exact_mod_cast h2 τ i hi`. Establish `h4 : (t : ℤ) * (-(N : ℤ)) ≤ t * G.1 (τ, i)` using `mul_le_mul_of_nonneg_left h1 (by positivity)`.

Establish `h5 : ((t * N + 1 : ℕ) : ℤ) * 2 ≤ ((t * N + 1 : ℕ) : ℤ) * a (τ, i)` using `mul_le_mul_of_nonneg_left h3 (by positivity)`. Establish `h6 : (0 : ℤ) ≤ t * N` using `by positivity`. Move the coercions through the operations in `at h5 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨t * N, fun x => if x.2 < Dw.mult x.1 then ((t : ℤ) * G.1 x + ((t * N + 1 : ℕ) : ℤ) * a x).toNat else 0, ⟨fun τ i j hij => ?_, hD.2.mul_left _⟩, fun τ i hi => ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hj : j < Dw.mult τ`. Establish `hi : i < Dw.mult τ` using `lt_of_le_of_lt hij hj`. Simplify using `only [hi, hj, if_true]`. Use `Int.toNat_le_toNat (add_le_add ?_ ?_)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (hanti τ i j hij hj) (by positivity)`.

Conclude with `mul_le_mul_of_nonneg_left (by exact_mod_cast hD.1 τ hij) (by positivity)`. Simplify using `only [hj, if_false]`. Conclude with `Nat.zero_le _`. Use `hpos τ i hi` as an intermediate fact. Simplify using `only [hi, if_true]`.

Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `x`. Break down `x with _ | ⟨τ, i⟩` into its components or cases. Simplify using `[Formalism.L2.Pj.exZ, wtZ, hG]`. Use `hpos τ i i.2` as an intermediate fact.

Establish `e : (t • G + (t * N + 1) • wtZ a n).1 (τ, (i : ℕ)) = (t : ℤ) * G.1 (τ, i) + ((t * N + 1 : ℕ) : ℤ) * a (τ, i)`. Simplify using `[wtZ]`. Use `show ((if (i : ℕ) < Dw.mult τ then ((t : ℤ) * G.1 (τ, i) + ((t * N + 1 : ℕ) : ℤ) * a (τ, i)).toNat else 0 : ℕ) : ℤ) = (t • G + (t * N + 1) • wtZ a n).1 (τ, (i : ℕ))`. Rewrite using `[e, if_pos i.2, Int.toNat_of_nonneg (by omega)]`.
-/
private theorem exists_nat_wt (G : WTZ E) (hG : G.2 = 0)
    (hanti : ∀ τ i j, i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) (t : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Formalism.L2.Pj.Dom a n) (h2 : ∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) :
    ∃ (M : ℕ) (a' : (E →+* ℂ) × ℕ → ℕ), Formalism.L2.Pj.Dom a' ((M + 1) * n) ∧ (∀ τ i, i < Dw.mult τ → 1 ≤ a' (τ, i)) ∧
      Formalism.L2.Pj.exZ Dw (wtZ a' ((M + 1) * n)) = Formalism.L2.Pj.exZ Dw (t • G + (M + 1) • wtZ a n) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ τ i, i < Dw.mult τ → -(N : ℤ) ≤ G.1 (τ, i) := by
    obtain ⟨B, hB⟩ := (Set.finite_range fun x : Formalism.L2.Pj.Ix Dw => (Formalism.L2.Pj.exZ Dw G x).natAbs).bddAbove
    refine ⟨B, fun τ i hi => ?_⟩
    have h1 : (G.1 (τ, i)).natAbs ≤ B := hB ⟨some ⟨τ, ⟨i, hi⟩⟩, rfl⟩
    omega
  have hpos : ∀ τ i, i < Dw.mult τ → 1 ≤ (t : ℤ) * G.1 (τ, i) + ((t * N + 1 : ℕ) : ℤ) * a (τ, i) := by
    intro τ i hi
    have h1 := hN τ i hi
    have h3 : (2 : ℤ) ≤ a (τ, i) := by exact_mod_cast h2 τ i hi
    have h4 : (t : ℤ) * (-(N : ℤ)) ≤ t * G.1 (τ, i) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : ((t * N + 1 : ℕ) : ℤ) * 2 ≤ ((t * N + 1 : ℕ) : ℤ) * a (τ, i) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h6 : (0 : ℤ) ≤ t * N := by positivity
    push_cast at h5 ⊢
    linarith
  refine ⟨t * N, fun x => if x.2 < Dw.mult x.1 then
    ((t : ℤ) * G.1 x + ((t * N + 1 : ℕ) : ℤ) * a x).toNat else 0, ⟨fun τ i j hij => ?_, hD.2.mul_left _⟩,
    fun τ i hi => ?_, ?_⟩
  · by_cases hj : j < Dw.mult τ
    · have hi : i < Dw.mult τ := lt_of_le_of_lt hij hj
      simp only [hi, hj, if_true]
      refine Int.toNat_le_toNat (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left (hanti τ i j hij hj) (by positivity)
      · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hD.1 τ hij) (by positivity)
    · simp only [hj, if_false]
      exact Nat.zero_le _
  · have := hpos τ i hi
    simp only [hi, if_true]
    omega
  · funext x
    rcases x with _ | ⟨τ, i⟩
    · simp [Formalism.L2.Pj.exZ, wtZ, hG]
    · have := hpos τ i i.2
      have e : (t • G + (t * N + 1) • wtZ a n).1 (τ, (i : ℕ)) =
          (t : ℤ) * G.1 (τ, i) + ((t * N + 1 : ℕ) : ℤ) * a (τ, i) := by
        simp [wtZ]
      show ((if (i : ℕ) < Dw.mult τ then
        ((t : ℤ) * G.1 (τ, i) + ((t * N + 1 : ℕ) : ℤ) * a (τ, i)).toNat else 0 : ℕ) : ℤ) =
        (t • G + (t * N + 1) • wtZ a n).1 (τ, (i : ℕ))
      rw [e, if_pos i.2, Int.toNat_of_nonneg (by omega)]

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Use function extensionality and compare the values at `τ i`. Simplify using `[modelWt]`. Consider the case `succ t ih => rw [succ_nsmul, succ_nsmul, modelWt_add V (GlobalTheory.DegTop.even_nsmul hG t) hG, ih]`.
-/
private theorem modelWt_nsmul' {σ : c.F →+* ℂ} (V : Unf Xo c σ r) {G : WTZ E} (hG : Even G.2) (k : V.Comp) (t : ℕ) :
    modelWt V (t • G) k = t • modelWt V G k := by
  induction t with
  | zero =>
    funext τ i
    simp [modelWt]
  | succ t ih => rw [succ_nsmul, succ_nsmul, modelWt_add V (GlobalTheory.DegTop.even_nsmul hG t) hG, ih]

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => simpa using hf`. Consider the case `succ t ih`. Rewrite using `[pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]`. Conclude with `GlobalTheory.DegTop.mul_mem_cuspOn (hG.add (GlobalTheory.DegTop.even_nsmul hG' t)) hG' ih hg.1`.
-/
private theorem mul_pow_mem {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G G' : WTZ E} (hG : Even G.2)
    (hG' : Even G'.2) {f g : Rul Xo c} (hf : f ∈ cuspOn U Z G) (hg : g ∈ cuspOn U Z G') (t : ℕ) :
    f * g ^ t ∈ cuspOn U Z (G + t • G') := by
  induction t with
  | zero => simpa using hf
  | succ t ih =>
    rw [pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]
    exact GlobalTheory.DegTop.mul_mem_cuspOn (hG.add (GlobalTheory.DegTop.even_nsmul hG' t)) hG' ih hg.1

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U hL Z la w hw hw0`. Establish `hG0 : (wtOf Dw la 0).2 = 0` using `by rw [wtOf_snd, mul_zero]`. Generalize the expression as in `wtOf Dw la 0 = G at hw hG0 ⊢`. Establish `hGe : Even G.2` using `by rw [hG0]; exact Even.zero`. Establish `hr : 1 ≤ r` using `(hL.unf c.F.val.toRingHom rfl).1 ▸ hL.pos`.

Take `⟨s, hs⟩ : ∃ s, r = s + 1` from `⟨r - 1, by omega⟩`. Take `⟨a, n, hD, h2, hn, hdv, f, hf, hf0⟩` from `GlobalTheory.FlatAnyLevel.exists_cuspOn_two hL Z`. Establish `hAe : Even (wtZ a n).2`. Take `⟨m, hm⟩` from `hD.2`. Conclude with `⟨m, by simp [wtZ, hm]⟩`.

Establish `hanti : ∀ τ i j, i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)`. Introduce `τ i j hij hj`. Break down `hij.eq_or_lt with rfl | hij'` into its components or cases. Conclude with `le_rfl`. Assume the negation of the conclusion as `hlt`.

Conclude with `hw0 (GlobalTheory.IncrZero.secZ_eq_zero_of_lt E H Dw l Xo c (Formalism.L2.Pj.exZ Dw G) τ ⟨i, hij'.trans hj⟩ ⟨j, hj⟩ hij' (not_le.1 hlt) w (cuspW_le_secZ G hw.1))`. Take `⟨M, a', hD', h1', hex⟩` from `exists_nat_wt G hG0 hanti r a n hD h2`. Establish `hG₀e : Even (wtZ a n + M • wtZ a n + s • G).2` using `(hAe.add (GlobalTheory.DegTop.even_nsmul hAe M)).add (GlobalTheory.DegTop.even_nsmul hGe s)`. Establish `hh : f * f ^ M * w ^ s ∈ cuspOn U Z (wtZ a n + M • wtZ a n + s • G)` using `mul_pow_mem (hAe.add (GlobalTheory.DegTop.even_nsmul hAe M)) hGe (mul_pow_mem hAe hAe hf hf M) hw s`. Establish `hsum : G + (wtZ a n + M • wtZ a n + s • G) = r • G + (M + 1) • wtZ a n`.

Rewrite using `[hs, succ_nsmul, succ_nsmul]`. Normalize the expressions using the abelian group laws. Establish `hdv' : GlobalTheory.FlatAnyLevel.SumDvd U a' ((M + 1) * n)` using `fun σ hσ k τ => by`. Establish `e` using `congrFun (modelWt_congr (U σ) hσ (hL.unf σ hσ) hex) k`. Rewrite `e` using `[modelWt_add (U σ) (GlobalTheory.DegTop.even_nsmul hGe r) (GlobalTheory.DegTop.even_nsmul hAe _), modelWt_nsmul' _ hGe, modelWt_nsmul' _ hAe, modelWt_wtZ, modelWt_wtZ]`.

Rewrite using `[e]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum]`. Rewrite using `[nsmul_eq_mul, nsmul_eq_mul]`. Conclude with `(dvd_mul_right _ _).add ((hdv σ hσ k τ).mul_left _)`. Use `⟨_, _, hh, fun h0 => ?_, fun σ hσ P hP hoff => ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg (genVal Z) h0`. Rewrite `e` using `[map_mul, map_mul, map_pow, map_pow, map_zero]`. Establish `e1 : genVal Z f ≠ 0` using `fun h => hf0 (GlobalTheory.DegTop.eq_zero_of_genVal hf h)`. Establish `e2 : genVal Z w ≠ 0` using `fun h => hw0 (GlobalTheory.DegTop.eq_zero_of_genVal hw h)`. Conclude with `mul_ne_zero (mul_ne_zero e1 (pow_ne_zero _ e1)) (pow_ne_zero _ e2) e`.

Rewrite using `[hsum, ← GlobalTheory.FlatPair.cuspOn_congr hL.unf Z hex]`. Use `(GlobalTheory.FlatAnyLevel.cuspOn_fd_span E H Dw l Xo c r U hL Z σ hσ a' _ hD' h1' (hn.trans (Nat.le_mul_of_pos_left n (Nat.succ_pos M))) hdv').2 _ ?_ fun k y hy => ?_` and prove the remaining obligations. Rewrite using `[modelWt_congr (U σ) hσ (hL.unf σ hσ) hex, ← hsum, GlobalTheory.DegTop.mem_holSub_iff]`. Introduce `k`. Rewrite using `[modelWt_add (U σ) hGe hG₀e k]`.

Conclude with `(siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((GlobalTheory.DegTop.mem_holSub_iff _ _ _).1 hP k) _ ((GlobalTheory.DegTop.mem_holSub_iff _ _ _).1 ((mem_cuspW.1 hh.1).2 σ hσ) k).1`. Use `show P k y * _ = 0`. Rewrite using `[hoff k y hy, zero_mul]`.
-/
theorem UpperTheory.cusp_form_weight_reduction :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), GlobalTheory.FlatAnyLevel.NeatUnf U → ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (w : Rul Xo c), w ∈ cuspOn U Z (wtOf Dw la 0) → w ≠ 0 → ∃ (G₀ : WTZ E) (h : Rul Xo c), h ∈ cuspOn U Z G₀ ∧ h ≠ 0 ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtOf Dw la 0)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P * rdU (U σ) h ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtOf Dw la 0 + G₀) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U hL Z la w hw hw0
  have hG0 : (wtOf Dw la 0).2 = 0 := by rw [wtOf_snd, mul_zero]
  generalize wtOf Dw la 0 = G at hw hG0 ⊢
  have hGe : Even G.2 := by rw [hG0]; exact Even.zero
  have hr : 1 ≤ r := (hL.unf c.F.val.toRingHom rfl).1 ▸ hL.pos
  obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨a, n, hD, h2, hn, hdv, f, hf, hf0⟩ := GlobalTheory.FlatAnyLevel.exists_cuspOn_two hL Z
  have hAe : Even (wtZ a n).2 := by
    obtain ⟨m, hm⟩ := hD.2
    exact ⟨m, by simp [wtZ, hm]⟩
  have hanti : ∀ τ i j, i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i) := by
    intro τ i j hij hj
    rcases hij.eq_or_lt with rfl | hij'
    · exact le_rfl
    by_contra hlt
    exact hw0 (GlobalTheory.IncrZero.secZ_eq_zero_of_lt E H Dw l Xo c (Formalism.L2.Pj.exZ Dw G) τ ⟨i, hij'.trans hj⟩ ⟨j, hj⟩ hij'
      (not_le.1 hlt) w (cuspW_le_secZ G hw.1))
  obtain ⟨M, a', hD', h1', hex⟩ := exists_nat_wt G hG0 hanti r a n hD h2
  have hG₀e : Even (wtZ a n + M • wtZ a n + s • G).2 :=
    (hAe.add (GlobalTheory.DegTop.even_nsmul hAe M)).add (GlobalTheory.DegTop.even_nsmul hGe s)
  have hh : f * f ^ M * w ^ s ∈ cuspOn U Z (wtZ a n + M • wtZ a n + s • G) :=
    mul_pow_mem (hAe.add (GlobalTheory.DegTop.even_nsmul hAe M)) hGe (mul_pow_mem hAe hAe hf hf M) hw s
  have hsum : G + (wtZ a n + M • wtZ a n + s • G) = r • G + (M + 1) • wtZ a n := by
    rw [hs, succ_nsmul, succ_nsmul]; abel
  have hdv' : GlobalTheory.FlatAnyLevel.SumDvd U a' ((M + 1) * n) := fun σ hσ k τ => by
    have e := congrFun (modelWt_congr (U σ) hσ (hL.unf σ hσ) hex) k
    rw [modelWt_add (U σ) (GlobalTheory.DegTop.even_nsmul hGe r) (GlobalTheory.DegTop.even_nsmul hAe _), modelWt_nsmul' _ hGe,
      modelWt_nsmul' _ hAe, modelWt_wtZ, modelWt_wtZ] at e
    rw [e]
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact (dvd_mul_right _ _).add ((hdv σ hσ k τ).mul_left _)
  refine ⟨_, _, hh, fun h0 => ?_, fun σ hσ P hP hoff => ?_⟩
  · have e := congrArg (genVal Z) h0
    rw [map_mul, map_mul, map_pow, map_pow, map_zero] at e
    have e1 : genVal Z f ≠ 0 := fun h => hf0 (GlobalTheory.DegTop.eq_zero_of_genVal hf h)
    have e2 : genVal Z w ≠ 0 := fun h => hw0 (GlobalTheory.DegTop.eq_zero_of_genVal hw h)
    exact mul_ne_zero (mul_ne_zero e1 (pow_ne_zero _ e1)) (pow_ne_zero _ e2) e
  · rw [hsum, ← GlobalTheory.FlatPair.cuspOn_congr hL.unf Z hex]
    refine (GlobalTheory.FlatAnyLevel.cuspOn_fd_span E H Dw l Xo c r U hL Z σ hσ a' _ hD' h1'
      (hn.trans (Nat.le_mul_of_pos_left n (Nat.succ_pos M))) hdv').2 _ ?_ fun k y hy => ?_
    · rw [modelWt_congr (U σ) hσ (hL.unf σ hσ) hex, ← hsum, GlobalTheory.DegTop.mem_holSub_iff]
      intro k
      rw [modelWt_add (U σ) hGe hG₀e k]
      exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((GlobalTheory.DegTop.mem_holSub_iff _ _ _).1 hP k) _
        ((GlobalTheory.DegTop.mem_holSub_iff _ _ _).1 ((mem_cuspW.1 hh.1).2 σ hσ) k).1
    · show P k y * _ = 0
      rw [hoff k y hy, zero_mul]
