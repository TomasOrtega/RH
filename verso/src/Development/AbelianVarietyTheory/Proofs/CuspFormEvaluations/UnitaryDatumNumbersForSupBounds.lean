import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.SupDict

/- English proof (translation)
Rewrite using `[D.host.der.finrank_E]`. Simplify using `only [Ranks.f, Ranks.n]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  simp only [Ranks.f, Ranks.n]
  ring

/- English proof (translation)
Unfold `xiR`. Use `norm_pos_iff.mpr ((map_ne_zero _).mpr ?_)` and prove the remaining obligations. Establish `hd : (D.host.d : D.host.E) ≠ 0`. Establish `hlt` using `D.host.qd_big.2`. Conclude with `(Nat.zero_lt_of_lt hlt).ne'` after adjusting the coercions.

Establish `hs : D.host.sqd ≠ 0`. Introduce `h0`. Establish `h2` using `D.host.sqd_sq`. Rewrite `h2` using `[h0]`. Apply `hd` to reduce the goal to its premises.

Establish `h3 : -(D.host.d : D.host.E) = 0` using `by rw [← h2]; ring`. Conclude with `neg_eq_zero.mp h3`. Establish `hn : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.mpr (fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))`. Simplify using `only [Host.xi0, Host.sqrtMinusD]`. Conclude with `div_ne_zero (neg_ne_zero.mpr one_ne_zero) (mul_ne_zero hn hs)`.
-/
theorem xiR_pos (D : D7) : 0 < xiR D := by
  unfold xiR
  refine norm_pos_iff.mpr ((map_ne_zero _).mpr ?_)
  have hd : (D.host.d : D.host.E) ≠ 0 := by
    have hlt := D.host.qd_big.2
    exact_mod_cast (Nat.zero_lt_of_lt hlt).ne'
  have hs : D.host.sqd ≠ 0 := by
    intro h0
    have h2 := D.host.sqd_sq
    rw [h0] at h2
    apply hd
    have h3 : -(D.host.d : D.host.E) = 0 := by rw [← h2]; ring
    exact neg_eq_zero.mp h3
  have hn : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  simp only [Host.xi0, Host.sqrtMinusD]
  exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) (mul_ne_zero hn hs)

/- English proof (translation)
Unfold `dE`. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs (NumberField.discr_ne_zero E)` after adjusting the coercions.
-/
theorem one_le_dE (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero E)

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => ext0 a i) M]`. Establish `h1 : ∑ i ∈ Finset.range M, ext0 a i = ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Use `split_ifs with hi`.

Both sides reduce to the same expression. Simplify using `[ext0, hi]`. Establish `h2 : ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i ≤ ∑ i ∈ Finset.range l, ext0 a i` using `Finset.sum_le_sum_of_subset (fun i hi => by simp at hi ⊢; omega)`. Establish `h3 : ∑ i ∈ Finset.range l, ext0 a i = ∑ i, a i`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => ext0 a i) l]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Simplify using `[ext0, i.isLt]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma sum_ext0_le_sum {l : ℕ} (a : Fin l → ℕ) (M : ℕ) : ∑ i : Fin M, ext0 a (i : ℕ) ≤ ∑ i, a i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ext0 a i) M]
  have h1 : ∑ i ∈ Finset.range M, ext0 a i = ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with hi
    · rfl
    · simp [ext0, hi]
  have h2 : ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i ≤ ∑ i ∈ Finset.range l, ext0 a i :=
    Finset.sum_le_sum_of_subset (fun i hi => by simp at hi ⊢; omega)
  have h3 : ∑ i ∈ Finset.range l, ext0 a i = ∑ i, a i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ext0 a i) l]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [ext0, i.isLt]
  omega

/- English proof (translation)
Introduce `D T h j hj w`. Establish `hfin` using `finrank_host D`. Establish `hdpos : 0 < dE D.host.E` using `lt_of_lt_of_le one_pos (one_le_dE _)`. Use `⟨?_, ?_, ?_, ?_, ?_, xiR_pos D, ?_, ?_, ?_, ?_, ?_, D.host.pde_prime.pos, D.host.pde'_prime.pos, ?_⟩` and prove the remaining obligations. Unfold `fdeg`.

Rewrite using `[hfin]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[rdE, Real.log_rpow hdpos, hfin, lrd, dE]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `rdE`. Conclude with `Real.one_le_rpow (one_le_dE _) (by positivity)`. Establish `h1` using `D.R.two_le_m`. Establish `h2` using `D.R.m_le_f`. Simplify using `only [Ranks.f, Ranks.n]`.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `D.R.two_le_m`. Simplify using `only [Ranks.r]`. Use linear arithmetic over natural numbers and integers. Unfold `wtA Formalism.L2.Pj.DF WeightAlgebra.DF WeightAlgebra.degP`.

Simplify using `only [Finset.sum_add_distrib]`. Apply `add_le_add` to reduce the goal to its premises. Rewrite using `[Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]`. Use `Finset.sum_le_sum (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (DV.tauEmb D t)]`.

Simplify using `only [↓reduceIte]`. Conclude with `sum_ext0_le_sum _ _`. Introduce `τ _ hτ`. Simplify using `[hτ]`. Introduce `hn`.

Conclude with `absurd (Finset.mem_univ _) hn`. Rewrite using `[Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]`. Use `Finset.sum_le_sum (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]`. Simplify using `only [↓reduceIte]`.

Conclude with `sum_ext0_le_sum _ _`. Introduce `τ _ hτ`. Simplify using `[hτ]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.

Unfold `absA WeightAlgebra.DF WeightAlgebra.degP`. Use `push_cast`. Both sides reduce to the same expression. Introduce `σ hσ k τ`. Unfold `Data.c`.

Rewrite using `[h.xiAbs j hj σ hσ k τ.1]`. Unfold `lieFac Formalism.L2.Pj.DF`. Rewrite using `[show (2 : ℝ) * Real.pi * xiR D = Real.pi * (2 * xiR D) by ring]`. Use `push_cast`. Both sides reduce to the same expression.

Take `⟨-, hl, -, -⟩` from `h.pins`. Unfold `Par.PinLevel at hl`. Conclude with `hl.2`. Introduce `ι σ P`. Unfold `l1At goodOf`.

Use `split_ifs with hg`. Both sides reduce to the same expression. Simplify using `only [RingHom.comp_apply, Complex.norm_conj]`.
-/
theorem record_dictionary : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), fdeg D.host.E = D.R.f ∧ Real.log (rdE D.host.E) = lrd D ∧ 1 ≤ rdE D.host.E ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ 0 < xiR D ∧ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w ∧ absA w = (WeightAlgebra.DF w : ℝ) ∧ (∀ σ, GoodEmb T.Q.c σ → ∀ k τ, ((T.U j σ).X k).c τ = 2 * xiR D) ∧ lieFac (T.Q.Dw j) (xiR D) (wtA w) = Real.exp (-(((Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) ∧ T.Q.l.A = 1 ∧ 0 < D.host.pde ∧ 0 < D.host.pde' ∧ ∀ (ι : Type) (σ : T.Q.c.F →+* ℂ) (P : MvPolynomial ι T.Q.c.F), l1At (goodOf T.Q.c σ) P = l1At σ P := by
  intro D T h j hj w
  have hfin := finrank_host D
  have hdpos : 0 < dE D.host.E := lt_of_lt_of_le one_pos (one_le_dE _)
  refine ⟨?_, ?_, ?_, ?_, ?_, xiR_pos D, ?_, ?_, ?_, ?_, ?_, D.host.pde_prime.pos, D.host.pde'_prime.pos, ?_⟩
  · unfold fdeg
    rw [hfin]
    omega
  · rw [rdE, Real.log_rpow hdpos, hfin, lrd, dE]
    push_cast
    ring
  · unfold rdE
    exact Real.one_le_rpow (one_le_dE _) (by positivity)
  · have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    simp only [Ranks.f, Ranks.n]
    omega
  · have h1 := D.R.two_le_m
    simp only [Ranks.r]
    omega
  · unfold wtA Formalism.L2.Pj.DF WeightAlgebra.DF WeightAlgebra.degP
    simp only [Finset.sum_add_distrib]
    apply add_le_add
    · rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_eq_single (DV.tauEmb D t)]
      · simp only [↓reduceIte]
        exact sum_ext0_le_sum _ _
      · intro τ _ hτ
        simp [hτ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
      · simp only [↓reduceIte]
        exact sum_ext0_le_sum _ _
      · intro τ _ hτ
        simp [hτ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
  · unfold absA WeightAlgebra.DF WeightAlgebra.degP
    push_cast
    rfl
  · intro σ hσ k τ
    unfold Data.c
    rw [h.xiAbs j hj σ hσ k τ.1]
  · unfold lieFac Formalism.L2.Pj.DF
    rw [show (2 : ℝ) * Real.pi * xiR D = Real.pi * (2 * xiR D) by ring]
    push_cast
    rfl
  · obtain ⟨-, hl, -, -⟩ := h.pins
    unfold Par.PinLevel at hl
    exact hl.2
  · intro ι σ P
    unfold l1At goodOf
    split_ifs with hg
    · rfl
    · simp only [RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.SupDict
