import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

namespace Formalism.FourierDecayAlt.TL

open Finset MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

open Classical

/- English proof (translation)
Unfold `P5.act Top.firstStateVector`. Rewrite using `[Finset.sum_eq_single (fun _ => 0)]`. Simplify using `only [if_true]`. Both sides reduce to the same expression. Introduce `b _ hb`.

Rewrite using `[if_neg hb, map_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem act_e1Vec {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (e : Wd.Ix S) :
    P5.act M (Top.firstStateVector Φ) e = (M e e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp only [if_true]
    rfl
  · intro b _ hb
    rw [if_neg hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Introduce `hW hC hId hF hCap hA hX`. Use `⟨11, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 h1 h2 hD`. Take `⟨hAH, hcst, hpoly⟩` from `hA Wp Wq P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 hD`. Take `⟨cm, c0, ca, cs, cmul⟩` from `hC Wp Wq P Bs`.

Take `⟨f1, f2, f3, f4, f5, f6, f7, f8⟩` from `hF Wp Wq P Bs X L hD.2.2.1`. Establish `hx` using `hX Wp Wq P Bs X μ L st l0 hD`. Establish `hS : LiftSys L st (2 * P.r + P.k + 1) (Lifts P Bs)` using `{ mono := fun h h' => cm _ _ _ _ _ h h' zero := c0 add := ca _ _ _ _ smul := fun z => cs _ _ _ z one := f1 mul := cmul _ _ _ _ _ _ fns := ⟨f2, f3, f4, f5, f6, f7, f8⟩ x := fun Y _ => hx Y xi := fun Y hY _ => by`. Take `⟨p, hp⟩` from `hpoly Y hY`. Rewrite using `[hp]`.

Establish `hpow : ∀ n : ℕ, Lifts P Bs 0 0 (st.x Y ^ n)` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `f1`. Consider the case `succ n ih => rw [pow_succ]`.

Simplify using `using cmul _ _ _ _ _ _ ih (hx Y)`. Use `Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `ca _ _ _ _ hp hq`. Rewrite using `[Polynomial.aeval_monomial, ← Algebra.smul_def]`.

Conclude with `cs _ _ _ a (hpow n)`. Use `cap := fun Y hY => by rw [← hcst Y hY]; exact hCap Wp Wq P Bs X μ L st l0 hD Y }`. Establish `key : ∀ w : List C.Letter, KB.CutWord P l0 w → ∀ e : Wd.Ix (Fin w.length), Lifts P Bs (w.length * (2 * P.r + P.k + 1)) (11 * w.length * (P.r + 1) * (2 * P.r + P.k + 1)) (((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) e e1)`. Introduce `w hw e`. Establish `hok` using `Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P Bs.z Bs.z' Bs.π Bs.π' st l0 hD.1.1 h1 h2 hD.2.2.2.2.1 hD.2.2.2.2.2.1 w hw.1 hw.2`.

Use `hW _ (Fin w.length) P.r (2 * P.r + P.k + 1) L st (Lifts P Bs) (D.positionted w) hAH hS (by omega) hok.1 e` as an intermediate fact. Establish `hl : (D.positionted w).length = w.length` using `by simp [D.positionted]`. Rewrite `this` using `[hl]`. Conclude with `this`. Use `choose nf fib Dop hfib hIn hRad using key`.

Take `⟨D1, hD1, hD1'⟩` from `hId P.k P.r Wp Wq Bs`. Use `⟨⟨fun w e F => if hw : w ≠ [] ∧ KB.CutWord P l0 w then B.opApply (Dop w hw.2 e) F else F, fun e F => by simp⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw F hF Φ hΦ e`. Rewrite using `[act_e1Vec]`. Distinguish the cases in `hn : w = []`.

Substitute `hn` using the available equality. Establish `h1' : D.positionted ([] : List C.Letter) = []` using `by simp [D.positionted]`. Establish `h2' : P5.bTall L ([] : List (Wd.Letter ℂ (Fin ([] : List C.Letter).length))) = 1`. Simplify using `[P5.bTall, P5.bTl, Wd.bT]`. Simplify using `only [ne_eq, not_true_eq_false, false_and, dite_false]`.

Rewrite using `[h1', h2', mul_one]`. Establish `h3 : (Fr.ofWord L st ([] : List (Wd.Letter ℂ (Fin ([] : List C.Letter).length)))).F e e1 = 1`. Express the relevant statement in the definitionally equal form `(1 : Wd.SlopeTestRemainingChoices (Fin 0) _) e e1 = 1`. Rewrite using `[Matrix.one_apply, if_pos (funext fun i => i.elim0)]`. Rewrite using `[h3]`.

Conclude with `hΦ`. Simplify using `only [dif_pos (And.intro hn hw)]`. Conclude with `hRad w hw e F hF Φ hΦ`. Introduce `w hw e`. Distinguish the cases in `hn : w = []`.

Substitute `hn` using the available equality. Use `⟨0, fun j => j.elim0, 0, 0, D1, fun j => j.elim0, hD1, by simp, by simp, fun F g _ => ?_⟩` and prove the remaining obligations. Simplify using `only [ne_eq, not_true_eq_false, false_and, dite_false]`. Rewrite using `[hD1']`. Use `⟨nf w hw e, fib w hw e, _, _, Dop w hw e, hfib w hw e, hIn w hw e, ?_, ?_, fun F g _ => ?_⟩` and prove the remaining obligations.

Use the proof step `push_cast; nlinarith [show (0 : ℝ) ≤ (w.length : ℝ) * (2 * P.r + P.k + 1) by positivity]`. Use the proof step `push_cast; exact le_of_eq (by ring)`. Simplify using `only [dif_pos (And.intro hn hw)]`.
-/
theorem topLiftOfParts : TopLiftOfParts := by
  intro hW hC hId hF hCap hA hX
  refine ⟨11, by norm_num, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 h1 h2 hD
  obtain ⟨hAH, hcst, hpoly⟩ := hA Wp Wq P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 hD
  obtain ⟨cm, c0, ca, cs, cmul⟩ := hC Wp Wq P Bs
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hF Wp Wq P Bs X L hD.2.2.1
  have hx := hX Wp Wq P Bs X μ L st l0 hD
  have hS : LiftSys L st (2 * P.r + P.k + 1) (Lifts P Bs) :=
    { mono := fun h h' => cm _ _ _ _ _ h h'
      zero := c0
      add := ca _ _ _ _
      smul := fun z => cs _ _ _ z
      one := f1
      mul := cmul _ _ _ _ _ _
      fns := ⟨f2, f3, f4, f5, f6, f7, f8⟩
      x := fun Y _ => hx Y
      xi := fun Y hY _ => by
        obtain ⟨p, hp⟩ := hpoly Y hY
        rw [hp]
        have hpow : ∀ n : ℕ, Lifts P Bs 0 0 (st.x Y ^ n) := fun n => by
          induction n with
          | zero => rw [pow_zero]; exact f1
          | succ n ih => rw [pow_succ]; simpa using cmul _ _ _ _ _ _ ih (hx Y)
        refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
        · rw [map_add]; exact ca _ _ _ _ hp hq
        · rw [Polynomial.aeval_monomial, ← Algebra.smul_def]; exact cs _ _ _ a (hpow n)
      cap := fun Y hY => by rw [← hcst Y hY]; exact hCap Wp Wq P Bs X μ L st l0 hD Y }
  have key : ∀ w : List C.Letter, KB.CutWord P l0 w → ∀ e : Wd.Ix (Fin w.length),
      Lifts P Bs (w.length * (2 * P.r + P.k + 1)) (11 * w.length * (P.r + 1) * (2 * P.r + P.k + 1))
        (((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) e e1) := by
    intro w hw e
    have hok := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P Bs.z Bs.z' Bs.π Bs.π' st l0 hD.1.1 h1 h2 hD.2.2.2.2.1 hD.2.2.2.2.2.1 w hw.1 hw.2
    have := hW _ (Fin w.length) P.r (2 * P.r + P.k + 1) L st (Lifts P Bs) (D.positionted w) hAH hS (by omega) hok.1 e
    have hl : (D.positionted w).length = w.length := by simp [D.positionted]
    rw [hl] at this
    exact this
  choose nf fib Dop hfib hIn hRad using key
  obtain ⟨D1, hD1, hD1'⟩ := hId P.k P.r Wp Wq Bs
  refine ⟨⟨fun w e F => if hw : w ≠ [] ∧ KB.CutWord P l0 w then B.opApply (Dop w hw.2 e) F else F,
    fun e F => by simp⟩, ?_, ?_⟩
  · intro w hw F hF Φ hΦ e
    rw [act_e1Vec]
    by_cases hn : w = []
    · subst hn
      have h1' : D.positionted ([] : List C.Letter) = [] := by simp [D.positionted]
      have h2' : P5.bTall L ([] : List (Wd.Letter ℂ (Fin ([] : List C.Letter).length))) = 1 := by
        simp [P5.bTall, P5.bTl, Wd.bT]
      simp only [ne_eq, not_true_eq_false, false_and, dite_false]
      rw [h1', h2', mul_one]
      have h3 : (Fr.ofWord L st ([] : List (Wd.Letter ℂ (Fin ([] : List C.Letter).length)))).F e e1 = 1 := by
        change (1 : Wd.SlopeTestRemainingChoices (Fin 0) _) e e1 = 1
        rw [Matrix.one_apply, if_pos (funext fun i => i.elim0)]
      rw [h3]
      exact hΦ
    · simp only [dif_pos (And.intro hn hw)]
      exact hRad w hw e F hF Φ hΦ
  · intro w hw e
    by_cases hn : w = []
    · subst hn
      refine ⟨0, fun j => j.elim0, 0, 0, D1, fun j => j.elim0, hD1, by simp, by simp, fun F g _ => ?_⟩
      simp only [ne_eq, not_true_eq_false, false_and, dite_false]
      rw [hD1']
    · refine ⟨nf w hw e, fib w hw e, _, _, Dop w hw e, hfib w hw e, hIn w hw e, ?_, ?_, fun F g _ => ?_⟩
      · push_cast; nlinarith [show (0 : ℝ) ≤ (w.length : ℝ) * (2 * P.r + P.k + 1) by positivity]
      · push_cast; exact le_of_eq (by ring)
      · simp only [dif_pos (And.intro hn hw)]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, h8⟩` from `hD`. Use `⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩` and prove the remaining obligations. Conclude with `{ start := h8.start lowerLeftEntry_commute := h8.lowerLeftEntry_commute x_xi := h8.x_xi x_commute := h8.x_commute x_fn := h8.x_fn x_nab := h8.x_nab x_star := h8.x_star ee_fn := by`. Introduce `Y g hg`. Distinguish the cases in `hY0 : Y = Y0`.

Simplify `hE g hg` using `[Function.update_apply, hY0]`. Simplify `h8.ee_fn Y g hg` using `[Function.update_apply, hY0]`. Use `tau := h8.tau`. Use `low := by`. Introduce `Y hYi`.

Establish `hne : Y ≠ Y0` using `fun h => hY (h ▸ hYi)`. Simplify `h8.low Y hYi }` using `[Function.update_apply, hne]`.
-/
theorem isData_update {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : Q.ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : P5.IsData P z z' π π' X μ L st l0) (Y0 : ℂ) (hY : Y0 ∉ st.inv) (E : Q.Pr (Q.RadSp P.k P.r z z' π π'))
    (hE : ∀ g ∈ zfns L, Commute E g) :
    P5.IsData P z z' π π' X μ L { st with ee := Function.update st.ee Y0 E } l0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hD
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
  exact
    { start := h8.start
      lowerLeftEntry_commute := h8.lowerLeftEntry_commute
      x_xi := h8.x_xi
      x_commute := h8.x_commute
      x_fn := h8.x_fn
      x_nab := h8.x_nab
      x_star := h8.x_star
      ee_fn := by
        intro Y g hg
        by_cases hY0 : Y = Y0
        · simpa [Function.update_apply, hY0] using hE g hg
        · simpa [Function.update_apply, hY0] using h8.ee_fn Y g hg
      tau := h8.tau
      low := by
        intro Y hYi
        have hne : Y ≠ Y0 := fun h => hY (h ▸ hYi)
        simpa [Function.update_apply, hne] using h8.low Y hYi }

/- English proof (translation)
Introduce `g hg`. Establish `h1 : Commute (L.p l) g`. Simplify using `only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg`. Break down `hg with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `L.p_ζ l`.

Conclude with `L.p_ζi l`. Conclude with `L.p_ζb l`. Conclude with `L.p_ζbi l`. Conclude with `L.p_GG l`. Conclude with `L.p_GGi l`.

Conclude with `h1.pow_left m`.
-/
theorem p_pow_comm {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r) (l : Fin r) (m : ℕ) :
    ∀ g ∈ zfns L, Commute (L.p l ^ m) g := by
  intro g hg
  have h1 : Commute (L.p l) g := by
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.p_ζ l
    · exact L.p_ζi l
    · exact L.p_ζb l
    · exact L.p_ζbi l
    · exact L.p_GG l
    · exact L.p_GGi l
  exact h1.pow_left m

def P0 : M.Par := ⟨2, 1, 1, 1, fun i => if i = 0 then -2 else if i = 1 then 1 / 2 else -1 / 2,
  fun i => if i = 0 then 2 else if i = 1 then 1 / 2 else -1 / 2⟩

/- English proof (translation)
Use `⟨by simp [P0], by simp [P0], by simp [P0], ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Establish `hi' : i = 1 ∨ i = 2`. Simplify using `[P0, Finset.mem_Icc, Set.mem_Icc] at hi`. Use linear arithmetic over natural numbers and integers.

Break down `hi' with rfl | rfl` into its components or cases. Conclude with `⟨0, by simp [P0]⟩`. Conclude with `⟨-1, by norm_num [P0]⟩`. Introduce `i hi`. Establish `hi' : i = 1 ∨ i = 2`.

Simplify using `[P0, Finset.mem_Icc, Set.mem_Icc] at hi`. Use linear arithmetic over natural numbers and integers. Break down `hi' with rfl | rfl` into its components or cases. Conclude with `⟨0, by norm_num [P0]⟩`. Conclude with `⟨-1, by norm_num [P0]⟩`.

Introduce `i hi`. Establish `hi' : i = 1`. Simplify using `[P0, Finset.mem_Icc, Set.mem_Icc] at hi`. Use linear arithmetic over natural numbers and integers. Substitute `hi'` using the available equality.

Evaluate the numerical expressions using `[P0, M.Par.lo, M.Par.hi]`.
-/
theorem base_parameters_ok : P0.OK := by
  refine ⟨by simp [P0], by simp [P0], by simp [P0], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simp [P0, Finset.mem_Icc, Set.mem_Icc] at hi
      omega
    rcases hi' with rfl | rfl
    · exact ⟨0, by simp [P0]⟩
    · exact ⟨-1, by norm_num [P0]⟩
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simp [P0, Finset.mem_Icc, Set.mem_Icc] at hi
      omega
    rcases hi' with rfl | rfl
    · exact ⟨0, by norm_num [P0]⟩
    · exact ⟨-1, by norm_num [P0]⟩
  · intro i hi
    have hi' : i = 1 := by
      simp [P0, Finset.mem_Icc, Set.mem_Icc] at hi
      omega
    subst hi'
    norm_num [P0, M.Par.lo, M.Par.hi]

/- English proof (translation)
Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a`. Simplify using `[I.OnCut, P0]`. Introduce `a b hab`. It suffices to derive a contradiction.

Apply `hab` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Express the relevant statement in the definitionally equal form `_ < 1 at ha hb`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Set.mem_setOf_eq, not_forall, not_not]`. Use `⟨fun _ => 0, ?_⟩` and prove the remaining obligations. Unfold `M.xC`. Apply `Finset.prod_eq_zero (i := 1)` to reduce the goal to its premises.

Simplify using `[P0]`. Simplify using `[M.rho, P0, M.Par.lo]`. Evaluate the numerical expressions.
-/
theorem base_parameters_truncation_word : KB.CutWord P0 0 [(true, 0)] ∧ (0 : ℂ) ∉ {Y : ℂ | ∀ ρ : M.Ty P0, M.xC P0 ρ Y ≠ 0} := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a
    simp [I.OnCut, P0]
  · intro a b hab
    exfalso
    apply hab
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    change _ < 1 at ha hb
    omega
  · simp only [Set.mem_setOf_eq, not_forall, not_not]
    refine ⟨fun _ => 0, ?_⟩
    unfold M.xC
    apply Finset.prod_eq_zero (i := 1)
    · simp [P0]
    · simp [M.rho, P0, M.Par.lo]
      norm_num

end

end Formalism.FourierDecayAlt.TL
