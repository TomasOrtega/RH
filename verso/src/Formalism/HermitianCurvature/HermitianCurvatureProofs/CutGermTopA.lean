import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVNonloc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Conclude with `hQ (by unfold KB.Pl.V D.vecV; exact dif_neg hn)`.
-/
private theorem isLocPt_and_ptG_pos_of_vec_ne_zero {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt) (hQ : p.V G Q ≠ 0) :
    D.IsLocPt Q (P.r + 1) ∧ 0 < D.ptG (TBB.TTp p) P.r Q := by
  by_contra hn
  exact hQ (by unfold KB.Pl.V D.vecV; exact dif_neg hn)

/- English proof (translation)
Unfold `D.vecV`. Conclude with `dif_neg fun hh => hQ hh.1`.
-/
private theorem vecV_eq_zero_of_not_isLocPt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt) (hQ : ¬ D.IsLocPt Q (P.r + 1)) :
    D.vecV p.T.base p.ν' p.m₀ G Q = 0 := by
  unfold D.vecV
  exact dif_neg fun hh => hQ hh.1

/- English proof (translation)
Establish `h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0`. Unfold `B.hsVec`. Both sides reduce to the same expression. Unfold `B.hsInner`. Rewrite using `[h0]`.

Conclude with `⟨inner_zero_right _, inner_zero_left _, rfl⟩`.
-/
private theorem hsInner_zero_left_right_and_hsVec_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X : Wq →L[ℂ] Wp) :
    B.hsInner 0 X = 0 ∧ B.hsInner X 0 = 0 ∧ B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
    unfold B.hsVec
    rfl
  unfold B.hsInner
  rw [h0]
  exact ⟨inner_zero_right _, inner_zero_left _, rfl⟩

/- English proof (translation)
Unfold `KB.Pl.RR D.RRplace`. Distinguish the cases in `hl : D.IsLocPt Q (P.r + 1) ∧ D.IsLocPt Q' (P.r + 1)`. Rewrite using `[dif_pos hl, dif_neg (by omega), if_pos rfl]`. Both sides reduce to the same expression. Rewrite using `[dif_neg hl]`.

Establish `hz : ∀ G : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV p.T.base p.ν' p.m₀ G Q = 0 ∨ D.vecV p.T.base p.ν' p.m₀ G Q' = 0`. Introduce `G`. Break down `not_and_or.mp hl with h | h` into its components or cases. Conclude with `Or.inl (vecV_eq_zero_of_not_isLocPt p G Q h)`. Conclude with `Or.inr (vecV_eq_zero_of_not_isLocPt p G Q' h)`.

Use `split_ifs with hw`. Break down `hz F with h | h` into its components or cases. Use `show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')`. Rewrite using `[h, (hsInner_zero_left_right_and_hsVec_zero _).1]`. Use `show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')`.

Rewrite using `[h, (hsInner_zero_left_right_and_hsVec_zero _).2.1]`. Unfold `Top.topOf`. Use `symm`. Use `Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_` and prove the remaining obligations. Break down `hz (p.Θ.Θ w e F) with h | h` into its components or cases.

Rewrite using `[h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, mul_zero]`. Rewrite using `[h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, mul_zero]`.
-/
private theorem rr_succ_eq_ite_hsInner_else_leading {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Q Q' : C.LPt) :
    p.RR F (P.r + 1) w Q Q' =
      if w = [] then B.hsInner (p.V F Q) (p.V F Q')
      else Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w Q Q' := by
  unfold KB.Pl.RR D.RRplace
  by_cases hl : D.IsLocPt Q (P.r + 1) ∧ D.IsLocPt Q' (P.r + 1)
  · rw [dif_pos hl, dif_neg (by omega), if_pos rfl]
    rfl
  · rw [dif_neg hl]
    have hz : ∀ G : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
        D.vecV p.T.base p.ν' p.m₀ G Q = 0 ∨ D.vecV p.T.base p.ν' p.m₀ G Q' = 0 := by
      intro G
      rcases not_and_or.mp hl with h | h
      · exact Or.inl (vecV_eq_zero_of_not_isLocPt p G Q h)
      · exact Or.inr (vecV_eq_zero_of_not_isLocPt p G Q' h)
    split_ifs with hw
    · rcases hz F with h | h
      · show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')
        rw [h, (hsInner_zero_left_right_and_hsVec_zero _).1]
      · show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')
        rw [h, (hsInner_zero_left_right_and_hsVec_zero _).2.1]
    · unfold Top.topOf
      symm
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
      rcases hz (p.Θ.Θ w e F) with h | h
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, mul_zero]
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, mul_zero]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p nn F w Cb hCb hF hw hnn`. Establish `hnc : 0 < TBB.normC nn w`. Unfold `TBB.normC`. Apply `List.prod_pos` to reduce the goal to its premises. Introduce `a ha`.

Take `⟨l, -, rfl⟩` from `List.mem_map.mp ha`. Conclude with `hnn l.2`. Distinguish the cases in `hw0 : w = []`. Substitute `hw0` using the available equality. Use `⟨Unit, inferInstance, fun _ => 1 / TBB.normC nn [], fun _ => F, fun _ => GermRateSplit.hsLE (ContinuousLinearMap.id ℂ Wp), fun _ => by positivity, fun _ => hF, ?_⟩` and prove the remaining obligations.

Introduce `Q Q'`. Rewrite using `[TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_pos rfl, Fintype.sum_unique, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]`. Simplify using `only [ContinuousLinearMap.id_comp, List.length_nil, omT, pow_zero, Real.sqrt_one, mul_one]`. Unfold `B.hsInner`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hT : ∀ e : Wd.Ix (Fin w.length), ∃ F', KB.CptCoef p.T.base F' ∧ (∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w e F g = F' g) ∧ ∀ a, p.V (p.Θ.Θ w e F) a = p.V F' a` using `fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hw choose G hG _ hGV using hT`. Use `⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance, fun i => √(Top.cW P p.l0 w i.1 i.2).re * √(Top.cW P p.l0 w i.1 i.2).re / TBB.normC nn w, fun i => G i.1, fun i => GermRateSplit.hsLE (p.TP.E i.2), fun i => by positivity, fun i => hG i.1, ?_⟩` and prove the remaining obligations. Introduce `Q Q'`. Rewrite using `[TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_neg hw0]`.

Unfold `Top.topOf`. Rewrite using `[Fintype.sum_prod_type, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations.

Establish `hV : ∀ a, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) a = p.V (G e) a` using `hGV e`. Rewrite using `[hV, hV, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]`. Establish `key : ∀ R : C.LPt, p.V (G e) R ≠ 0 → √(TBB.nPt P.k P.r (TBB.TTp p) R) * Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w R e ρ = omT p w.length R * √(Top.cW P p.l0 w e ρ).re`. Introduce `R hR`. Establish `hpos` using `(isLocPt_and_ptG_pos_of_vec_ne_zero p (G e) R hR).2`.

Establish `hwp : 0 ≤ Top.wPt (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r R` using `div_nonneg (Complex.normSq_nonneg _) hpos.le`. Unfold `Top.dH omT`. Rewrite using `[Real.sqrt_mul (pow_nonneg hwp _)]`. Unfold `TBB.TTp`. Expand and normalize the polynomial expressions, which then agree.

Distinguish the cases in `hz : p.V (G e) Q = 0 ∨ p.V (G e) Q' = 0`. Break down `hz with h | h` into its components or cases. Rewrite using `[h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2, inner_zero_right]`. Simplify using the standard rewrite rules. Rewrite using `[h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2, inner_zero_left]`.

Simplify using the standard rewrite rules. Use `push Not at hz`. Establish `hreal : √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') / TBB.normC nn w * (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ * Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) = √(Top.cW P p.l0 w e ρ).re * √(Top.c …`. Rewrite using `[div_mul_eq_mul_div, show √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') * (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ * Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) = (√(TBB.nPt P.k P.r (TBB.TTp p) Q) …`. Expand and normalize the polynomial expressions, which then agree.

Unfold `B.hsInner`. Establish `hc` using `congrArg (fun x : ℝ => (x : ℂ) * inner ℂ (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q'))) (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q)))) hreal`. Move the coercions through the operations in `at hc ⊢`. Take the linear combination `hc`.
-/
theorem top_level_gram : TopGram1 := by
  intro Wp Wq _ _ _ _ _ _ P p nn F w Cb hCb hF hw hnn
  have hnc : 0 < TBB.normC nn w := by
    unfold TBB.normC
    apply List.prod_pos
    intro a ha
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    exact hnn l.2
  by_cases hw0 : w = []
  · subst hw0
    refine ⟨Unit, inferInstance, fun _ => 1 / TBB.normC nn [], fun _ => F,
      fun _ => GermRateSplit.hsLE (ContinuousLinearMap.id ℂ Wp), fun _ => by positivity, fun _ => hF, ?_⟩
    intro Q Q'
    rw [TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_pos rfl, Fintype.sum_unique, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [ContinuousLinearMap.id_comp, List.length_nil, omT, pow_zero, Real.sqrt_one, mul_one]
    unfold B.hsInner
    push_cast
    ring
  · have hT : ∀ e : Wd.Ix (Fin w.length), ∃ F', KB.CptCoef p.T.base F' ∧
        (∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w e F g = F' g) ∧ ∀ a, p.V (p.Θ.Θ w e F) a = p.V F' a :=
      fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hw
    choose G hG _ hGV using hT
    refine ⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance,
      fun i => √(Top.cW P p.l0 w i.1 i.2).re * √(Top.cW P p.l0 w i.1 i.2).re / TBB.normC nn w,
      fun i => G i.1, fun i => GermRateSplit.hsLE (p.TP.E i.2), fun i => by positivity, fun i => hG i.1, ?_⟩
    intro Q Q'
    rw [TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_neg hw0]
    unfold Top.topOf
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hV : ∀ a, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) a = p.V (G e) a := hGV e
    rw [hV, hV, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    have key : ∀ R : C.LPt, p.V (G e) R ≠ 0 →
        √(TBB.nPt P.k P.r (TBB.TTp p) R) *
            Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w R e ρ =
          omT p w.length R * √(Top.cW P p.l0 w e ρ).re := by
      intro R hR
      have hpos := (isLocPt_and_ptG_pos_of_vec_ne_zero p (G e) R hR).2
      have hwp : 0 ≤ Top.wPt (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r R :=
        div_nonneg (Complex.normSq_nonneg _) hpos.le
      unfold Top.dH omT
      rw [Real.sqrt_mul (pow_nonneg hwp _)]
      unfold TBB.TTp
      ring
    by_cases hz : p.V (G e) Q = 0 ∨ p.V (G e) Q' = 0
    · rcases hz with h | h
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2,
          inner_zero_right]
        simp
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2,
          inner_zero_left]
        simp
    · push Not at hz
      have hreal : √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') /
            TBB.normC nn w *
            (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ *
              Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) =
          √(Top.cW P p.l0 w e ρ).re * √(Top.cW P p.l0 w e ρ).re / TBB.normC nn w *
            (omT p w.length Q' * omT p w.length Q) := by
        rw [div_mul_eq_mul_div,
          show √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') *
              (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) =
              (√(TBB.nPt P.k P.r (TBB.TTp p) Q) *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ) *
              (√(TBB.nPt P.k P.r (TBB.TTp p) Q') *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) by ring,
          key Q hz.1, key Q' hz.2]
        ring
      unfold B.hsInner
      have hc := congrArg (fun x : ℝ => (x : ℂ) *
        inner ℂ (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q'))) (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q)))) hreal
      push_cast at hc ⊢
      linear_combination hc

/- English proof (translation)
Establish `hgg : (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) = fun c => (Complex.normSq c - TBB.TTp p, c)`. Use function extensionality and compare the values at `c`. Simplify using `[D.ptGG, D.ptLast]`. Establish `hn : ContinuousAt (fun c : ℂ => TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m, c)])) c0`. Establish `h1` using `(LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) m h 1).continuousAt (x := (D.ptGG (TBB.TTp p) (h ++ [(m, c0)]), c0)) ((isOpen_univ.prod isOpen_compl_singleton).mem_nhds ⟨trivial, hc0⟩)`.

Establish `h2 : ContinuousAt (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) c0`. Rewrite using `[hgg]`. Conclude with `((Complex.continuous_normSq.sub continuous_const).prodMk continuous_id).continuousAt`. Conclude with `h1.comp (f := fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) h2`. Establish `hw : ContinuousAt (fun c : ℂ => Top.wPt (TBB.TTp p) P.r (h ++ [(m, c)])) c0`.

Unfold `Top.wPt`. Conclude with `(Complex.continuous_normSq.comp (LastBlockContinuity.ptMatN_cont h m (P.r + 1)).matrix_det).continuousAt.div (LastBlockContinuity.ptG_cont (TBB.TTp p) P.r h m).continuousAt hG.ne'`. Unfold `omT`. Conclude with `(hn.sqrt).mul ((hw.pow N).sqrt)`.
-/
private theorem continuousAt_omT_append_last_of_ptG_pos {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N m : ℕ) (h : C.LPt) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hG : 0 < D.ptG (TBB.TTp p) P.r (h ++ [(m, c0)])) :
    ContinuousAt (fun c : ℂ => omT p N (h ++ [(m, c)])) c0 := by
  have hgg : (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) =
      fun c => (Complex.normSq c - TBB.TTp p, c) := by
    funext c
    simp [D.ptGG, D.ptLast]
  have hn : ContinuousAt (fun c : ℂ => TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m, c)])) c0 := by
    have h1 := (LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) m h 1).continuousAt
      (x := (D.ptGG (TBB.TTp p) (h ++ [(m, c0)]), c0))
      ((isOpen_univ.prod isOpen_compl_singleton).mem_nhds ⟨trivial, hc0⟩)
    have h2 : ContinuousAt (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) c0 := by
      rw [hgg]
      exact ((Complex.continuous_normSq.sub continuous_const).prodMk continuous_id).continuousAt
    exact h1.comp (f := fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) h2
  have hw : ContinuousAt (fun c : ℂ => Top.wPt (TBB.TTp p) P.r (h ++ [(m, c)])) c0 := by
    unfold Top.wPt
    exact (Complex.continuous_normSq.comp (LastBlockContinuity.ptMatN_cont h m (P.r + 1)).matrix_det).continuousAt.div
      (LastBlockContinuity.ptG_cont (TBB.TTp p) P.r h m).continuousAt hG.ne'
  unfold omT
  exact (hn.sqrt).mul ((hw.pow N).sqrt)

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p F' hF N m h hh hm hsz c0 hc0`. Establish `hc0' : c0 ≠ 0` using `hc0`. Establish `hA` using `LastBlockContinuity.smulV_continuousAt P p F' hF h hh m hm hsz (fun c => omT p N (h ++ [(m, c)])) (ContinuousLinearMap.id ℂ Wp) c0 hc0' (fun hG => continuousAt_omT_append_last_of_ptG_pos p N m h c0 hc0' hG)`. Simplify using `only [ContinuousLinearMap.id_comp] at hA`. Conclude with `hA.continuousWithinAt`.
-/
theorem top_level_Y_continuity : YCont := by
  intro Wp Wq _ _ _ _ _ _ P p F' hF N m h hh hm hsz c0 hc0
  have hc0' : c0 ≠ 0 := hc0
  have hA := LastBlockContinuity.smulV_continuousAt P p F' hF h hh m hm hsz (fun c => omT p N (h ++ [(m, c)]))
    (ContinuousLinearMap.id ℂ Wp) c0 hc0' (fun hG => continuousAt_omT_append_last_of_ptG_pos p N m h c0 hc0' hG)
  simp only [ContinuousLinearMap.id_comp] at hA
  exact hA.continuousWithinAt

end

end Formalism.FourierDecayAlt.P.CutBP.GT
