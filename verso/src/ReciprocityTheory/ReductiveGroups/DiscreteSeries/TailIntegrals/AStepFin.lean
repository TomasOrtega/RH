import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ExponentShiftEqLevelExponent

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Introduce `s hs μG hμG A hA`. Take `⟨hOSI, -, hHCL, hHI, -, -, hHGE, hHA, hGNL, hHC, hHCLM⟩` from `heisenbergFacts_of_inductiveInput hB2`. Take `⟨μ₁, hμ₁⟩` from `hHGE k r'`. Establish `: IsFiniteMeasureOnCompacts μ₁` using `⟨fun K hK => hμ₁.finite_compact K hK⟩`. Establish `hk1 : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`.

Establish `hr0 : (0 : ℝ) ≤ r'` using `Nat.cast_nonneg r'`. Establish `hs1 : SAdm k r' (fun l => s (sc r' l))` using `fun l => by`. Establish `h` using `hs (sc r' l)`. Establish `e : s0 k (1 + r') (sc r' l) = s0 k r' l`. Apply the tactic sequence `unfold s0 sc; split_ifs <;> first | rfl | (exfalso; simp_all; omega)`.

Rewrite `h` using `[e]`. Conclude with `h`. Establish `hAB : AB k r' ≤ A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)`. Unfold `AB at hA ⊢`. Move the coercions through the operations in `at hA ⊢`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hdA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A`. Unfold `AB at hA`. Move the coercions through the operations in `at hA ⊢`. Use polynomial arithmetic with `[mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hr0]`.

Establish `hJ1` using `hA' _ hs1 μ₁ hμ₁ _ hAB`. Take `⟨J1, hJ1d⟩ : ∃ J1, J1 = JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) (fun l => s (sc r' l))` from `⟨_, rfl⟩`. Rewrite `hJ1` using `[← hJ1d]`. Take `⟨C0, hC0⟩` from `eInt_bound hGNL hHA hHC hHCL hHCLM k r' hk A hdA`. Take `⟨C, -, hOS⟩` from `hOSI k r' μG μ₁ hμG hμ₁`.

Establish `hfm : Measurable (fun g : Mt k (1 + r') => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k (1 + r') s (Matrix.of g))` using `((by unfold gN; fun_prop : Continuous fun g : Mt k (1 + r') => gN (Matrix.of g)).measurable.pow_const _).ennreal_ofReal.mul (FsE_meas k (1 + r') s)`. Unfold `JInt`. Rewrite using `[hOS _ hfm]`. Use `ENNReal.mul_lt_top ENNReal.coe_lt_top ?_` and prove the remaining obligations. Take `⟨aw, haw⟩ : ∃ aw : ℝ, aw = 2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l` from `⟨_, rfl⟩`.

Establish `hc0 : ∀ᵐ c : ℂ, c ≠ 0`. Rewrite using `[ae_iff]`. Simplify using `only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]`. Conclude with `measure_singleton 0`. Establish `hYc : Continuous fun x : HPar k r' => Yx k r' x`.

Establish `e : (fun x : HPar k r' => Yx k r' x) = fun x a => heis0 k r' (-x.1, -x.2) *ᵥ phi2 k r' a`. Use function extensionality and compare the values at `x a`. Unfold `Yx`. Rewrite using `[hHI]`. Rewrite using `[e]`.

Use `heisenberg_map_continuous k r'` as an intermediate fact. Use `fun_prop`. Establish `hGac : ∀ l, Continuous fun x : HPar k r' => Ga k (1 + r') l (Yx k r' x)`. Introduce `l`. Unfold `Ga`.

Use `fun_prop`. Establish `hDm : Measurable fun x => Dx k r' x` using `by unfold Dx; exact (hGac 0).sqrt.measurable`. Establish `hPm : Measurable fun x => Psi k r' s x`. Unfold `Psi`. Conclude with `Finset.measurable_prod _ fun l _ => ((hGac _).measurable.div (hGac 0).measurable).pow_const _`.

Establish `hFm : Measurable (Function.uncurry fun (c : ℂ) (x : HPar k r') => ENNReal.ofReal (‖c‖ ^ aw) * (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ)))))` using `((measurable_norm.comp measurable_fst).pow_const _).ennreal_ofReal.mul ((hPm.comp measurable_snd).ennreal_ofReal.mul ((mw_meas k r').comp (measurable_fst.mul (Complex.measurable_ofReal.comp (hDm.comp measurable_snd)))).ennreal_ofReal)`. Establish `hS0 : ∑ l, s0 k (1 + r') l = 2 * (1 + (r' : ℝ)) + k`. Rewrite using `[sum_sc, levelExponent_first_eq_two, sum_levelExponents_shifted]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlt : ∑ l, s l < ∑ l, s0 k (1 + r') l` using `Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun l _ => by linarith [(hs l).1]`.

Establish `hge : ∑ l, (s0 k (1 + r') l - 1 / 10) ≤ ∑ l, s l` using `Finset.sum_le_sum fun l _ => by linarith [(hs l).2]`. Rewrite `hge` using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Move the coercions through the operations in `at hge`. Establish `hK1 : ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) < ⊤`. Establish `h` using `cInt_fin (2 * r' + k + 1) (∑ l, s l) (by linarith) (by push_cast; linarith)`.

Establish `e : (4 * r' + 2 * k + 3 : ℕ) = 2 * (2 * r' + k + 1) + 1` using `by ring`. Unfold `mw`. Rewrite using `[e, haw]`. Conclude with `h`. Establish `hCHc : CHCond (1 + r') fun l => (if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) - s0N (1 + r') (k - 1) l`.

Use `chcond_of _ (fun l => s0 k (1 + r') l - s l) (fun l => by linarith [(hs l).1]) ?_ ?_` and prove the remaining obligations. Simplify using `only [if_pos rfl]`. Rewrite using `[sum_erase0, exponentShift_eq_levelExponent k r' hk, levelExponent_first_eq_two, Finset.sum_sub_distrib, sum_levelExponents_shifted, haw, sum_sc r' s]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Introduce `l hl0`. Simplify using `only [if_neg hl0]`. Rewrite using `[exponentShift_eq_levelExponent k r' hk]`. Expand and normalize the polynomial expressions, which then agree. Establish `hTh : ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) < ⊤`.

Use `lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (th_fin hB2 hF hCH k r' hk _ hCHc)` and prove the remaining obligations. Establish `hg` using `yx_ga hB2 hIW k r' hk x`. Conclude with `th_ident k r' s aw x hg.1 hg.2`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono_ae (hc0.mono fun c hc => ?_)` and prove the remaining obligations.

Establish `h` using `inner_c_le k r' hB2 hIW hT hk A C0 hC0 s μ₁ hμ₁ c hc`. Rewrite `h` using `[← hJ1d, ← haw]`. Conclude with `h`. Use `_ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) * (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ)))) := by`. Rewrite using `[← lintegral_lintegral_swap hFm.aemeasurable, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]`.

Use `lintegral_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ aw)) _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul (abs_nonneg _)]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * (ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) * ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) := by`. Use `congr 1`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hD : 0 < Dx k r' x` using `Real.sqrt_pos.mpr (yx_ga hB2 hIW k r' hk x).1`. Rewrite using `[← scale_c k r' aw _ hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`.

Use `lintegral_congr fun c => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ENNReal.ofReal |C0| * J1 * ((∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2)))) := by`. Use `congr 1`. Rewrite using `[← lintegral_const_mul' _ _ hK1.ne]`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ1) (ENNReal.mul_lt_top hK1 hTh)`.
-/
theorem aStep_fin (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hF : FormulaF) (hCH : CH) (k r' : ℕ) (hk : 1 ≤ k)
    (hA' : AAt k r') : AAt k (1 + r') := by
  intro s hs μG hμG A hA
  obtain ⟨hOSI, -, hHCL, hHI, -, -, hHGE, hHA, hGNL, hHC, hHCLM⟩ := heisenbergFacts_of_inductiveInput hB2
  obtain ⟨μ₁, hμ₁⟩ := hHGE k r'
  have : IsFiniteMeasureOnCompacts μ₁ := ⟨fun K hK => hμ₁.finite_compact K hK⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg r'
  have hs1 : SAdm k r' (fun l => s (sc r' l)) := fun l => by
    have h := hs (sc r' l)
    have e : s0 k (1 + r') (sc r' l) = s0 k r' l := by
      unfold s0 sc; split_ifs <;> first | rfl | (exfalso; simp_all; omega)
    rw [e] at h; exact h
  have hAB : AB k r' ≤ A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ) := by
    unfold AB at hA ⊢; push_cast at hA ⊢; nlinarith
  have hdA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A := by
    unfold AB at hA; push_cast at hA ⊢; nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hr0]
  have hJ1 := hA' _ hs1 μ₁ hμ₁ _ hAB
  obtain ⟨J1, hJ1d⟩ : ∃ J1, J1 = JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) (fun l => s (sc r' l)) := ⟨_, rfl⟩
  rw [← hJ1d] at hJ1
  obtain ⟨C0, hC0⟩ := eInt_bound hGNL hHA hHC hHCL hHCLM k r' hk A hdA
  obtain ⟨C, -, hOS⟩ := hOSI k r' μG μ₁ hμG hμ₁
  have hfm : Measurable (fun g : Mt k (1 + r') =>
      ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k (1 + r') s (Matrix.of g)) :=
    ((by unfold gN; fun_prop : Continuous fun g : Mt k (1 + r') => gN (Matrix.of g)).measurable.pow_const
      _).ennreal_ofReal.mul (FsE_meas k (1 + r') s)
  unfold JInt
  rw [hOS _ hfm]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  obtain ⟨aw, haw⟩ : ∃ aw : ℝ, aw = 2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l := ⟨_, rfl⟩
  have hc0 : ∀ᵐ c : ℂ, c ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton 0
  have hYc : Continuous fun x : HPar k r' => Yx k r' x := by
    have e : (fun x : HPar k r' => Yx k r' x) = fun x a => heis0 k r' (-x.1, -x.2) *ᵥ phi2 k r' a := by
      funext x a; unfold Yx; rw [hHI]
    rw [e]; have := heisenberg_map_continuous k r'; fun_prop
  have hGac : ∀ l, Continuous fun x : HPar k r' => Ga k (1 + r') l (Yx k r' x) := by
    intro l; unfold Ga; fun_prop
  have hDm : Measurable fun x => Dx k r' x := by unfold Dx; exact (hGac 0).sqrt.measurable
  have hPm : Measurable fun x => Psi k r' s x := by
    unfold Psi
    exact Finset.measurable_prod _ fun l _ => ((hGac _).measurable.div (hGac 0).measurable).pow_const _
  have hFm : Measurable (Function.uncurry fun (c : ℂ) (x : HPar k r') => ENNReal.ofReal (‖c‖ ^ aw) *
      (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ))))) :=
    ((measurable_norm.comp measurable_fst).pow_const _).ennreal_ofReal.mul
      ((hPm.comp measurable_snd).ennreal_ofReal.mul ((mw_meas k r').comp
        (measurable_fst.mul (Complex.measurable_ofReal.comp (hDm.comp measurable_snd)))).ennreal_ofReal)
  have hS0 : ∑ l, s0 k (1 + r') l = 2 * (1 + (r' : ℝ)) + k := by
    rw [sum_sc, levelExponent_first_eq_two, sum_levelExponents_shifted]; ring
  have hlt : ∑ l, s l < ∑ l, s0 k (1 + r') l :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun l _ => by linarith [(hs l).1]
  have hge : ∑ l, (s0 k (1 + r') l - 1 / 10) ≤ ∑ l, s l := Finset.sum_le_sum fun l _ => by linarith [(hs l).2]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hge
  push_cast at hge
  have hK1 : ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) < ⊤ := by
    have h := cInt_fin (2 * r' + k + 1) (∑ l, s l) (by linarith) (by push_cast; linarith)
    have e : (4 * r' + 2 * k + 3 : ℕ) = 2 * (2 * r' + k + 1) + 1 := by ring
    unfold mw; rw [e, haw]; exact h
  have hCHc : CHCond (1 + r') fun l =>
      (if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) - s0N (1 + r') (k - 1) l := by
    refine chcond_of _ (fun l => s0 k (1 + r') l - s l) (fun l => by linarith [(hs l).1]) ?_ ?_
    · simp only [if_pos rfl]
      rw [sum_erase0, exponentShift_eq_levelExponent k r' hk, levelExponent_first_eq_two, Finset.sum_sub_distrib, sum_levelExponents_shifted, haw, sum_sc r' s]
      push_cast; ring
    · intro l hl0
      simp only [if_neg hl0]
      rw [exponentShift_eq_levelExponent k r' hk]; ring
  have hTh : ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (th_fin hB2 hF hCH k r' hk _ hCHc)
    have hg := yx_ga hB2 hIW k r' hk x
    exact th_ident k r' s aw x hg.1 hg.2
  calc ∫⁻ c, ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
        ∫⁻ p : (HPar k r' × HPar k r') × Mt k r',
          ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
            FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μ₁)
      ≤ ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
          (ENNReal.ofReal (|C0| * mw k r' (c * (Dx k r' x : ℂ))) * J1) := by
        refine lintegral_mono_ae (hc0.mono fun c hc => ?_)
        have h := inner_c_le k r' hB2 hIW hT hk A C0 hC0 s μ₁ hμ₁ c hc
        rw [← hJ1d, ← haw] at h; exact h
    _ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) *
          (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ)))) := by
        rw [← lintegral_lintegral_swap hFm.aemeasurable,
          ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]
        refine lintegral_congr fun c => ?_
        rw [← lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ aw)) _ ENNReal.ofReal_ne_top,
          ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_mul (abs_nonneg _)]; ring
    _ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
          (ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) *
            ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) := by
        congr 1
        refine lintegral_congr fun x => ?_
        have hD : 0 < Dx k r' x := Real.sqrt_pos.mpr (yx_ga hB2 hIW k r' hk x).1
        rw [← scale_c k r' aw _ hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun c => ?_; ring
    _ = ENNReal.ofReal |C0| * J1 * ((∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) *
          ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2)))) := by
        congr 1
        rw [← lintegral_const_mul' _ _ hK1.ne]
        refine lintegral_congr fun x => ?_; ring
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ1) (ENNReal.mul_lt_top hK1 hTh)

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
