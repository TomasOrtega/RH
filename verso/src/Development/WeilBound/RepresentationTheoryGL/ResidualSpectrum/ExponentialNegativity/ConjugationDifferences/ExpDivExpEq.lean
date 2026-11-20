import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExistsNatCastConjMem
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExistsNormConjArchLe

noncomputable section

open NumberField MeasureTheory Filter Topology
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

namespace PositivityTheory.Rg.Rs

namespace diffstep

/- English proof (translation)
Establish `h : ∀ i, Function.update m r (m r - 1) i * s i = m i * s i - (if r = i then s i else 0)`. Introduce `i`. Distinguish the cases in `hi : i = r`. Substitute `hi` using the available equality. Simplify using `only [Function.update_self, if_true]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[Function.update_of_ne hi, Ne.symm hi]`. Rewrite using `[Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hrn)]`.
-/
theorem sum_update_sub {n r : ℕ} (hrn : r < n) (m s : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, Function.update m r (m r - 1) i * s i =
      ∑ i ∈ Finset.range n, m i * s i - s r := by
  have h : ∀ i, Function.update m r (m r - 1) i * s i = m i * s i - (if r = i then s i else 0) := by
    intro i
    by_cases hi : i = r
    · subst hi
      simp only [Function.update_self, if_true]
      ring
    · simp [Function.update_of_ne hi, Ne.symm hi]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_range.2 hrn)]

/- English proof (translation)
Introduce `i j hij`. Establish `h` using `hx j`. Simplify using `only [An.sr] at h`. Rewrite `h` using `[dif_pos (show 0 < (j : ℕ) ∧ (j : ℕ) < n from ⟨by omega, j.2⟩)]`. Establish `e : x ⟨(j : ℕ) - 1, by omega⟩ = x i` using `congrArg x (Fin.ext (by simp; omega))`.

Rewrite `h` using `[e]`. Rewrite using `[← Real.exp_add]`. Conclude with `Real.exp_le_exp.2 (by linarith)`.
-/
theorem siegel_of_sr {n : ℕ} {x : Fin n → ℝ} {t₀ : ℝ} (hx : ∀ r, -t₀ ≤ An.sr x r) :
    ∀ i j : Fin n, (j : ℕ) = i + 1 → Real.exp (-t₀) * Real.exp (x j) ≤ Real.exp (x i) := by
  intro i j hij
  have h := hx j
  simp only [An.sr] at h
  rw [dif_pos (show 0 < (j : ℕ) ∧ (j : ℕ) < n from ⟨by omega, j.2⟩)] at h
  have e : x ⟨(j : ℕ) - 1, by omega⟩ = x i := congrArg x (Fin.ext (by simp; omega))
  rw [e] at h
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/- English proof (translation)
Rewrite using `[An.sr, dif_pos ⟨hr, hrn⟩, ← Real.exp_sub]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_div_exp_eq {n r : ℕ} (hr : 0 < r) (hrn : r < n) (x : Fin n → ℝ) :
    Real.exp (x ⟨r, hrn⟩) / Real.exp (x ⟨r - 1, by omega⟩) = Real.exp (-An.sr x r) := by
  rw [An.sr, dif_pos ⟨hr, hrn⟩, ← Real.exp_sub]
  congr 1
  ring

end diffstep

open diffstep in
/- English proof (translation)
Introduce `K _ _ n φ m r hr hrn hN hB ω hω hωB t₀ Q hQ`. Take `⟨U, hU, hlev⟩` from `hN.level`. Take `⟨M, hM, hMc⟩` from `exists_natCast_conj_mem U hU hω hQ r`. Take `⟨C₁, hC₁0, hC₁⟩` from `exists_norm_conjArch_le hω hωB hQ (Real.exp_pos (-t₀)) hr hrn (isCompact_scaledInfSet (K := K) M)`. Take `⟨Q₀, C₂, hQ₀, hC₂, hlip⟩` from `hN.lip (C₁ * Real.exp t₀)`.

Take `⟨C₃, hC₃⟩` from `hB ω hω hωB t₀ (Q * Q₀) (hQ.mul hQ₀)`. Use `set C₃' := max C₃ 0 with hC₃'`. Establish `hC₃'0 : 0 ≤ C₃'` using `le_max_right _ _`. Use `⟨C₂ * C₁ * C₃', ?_⟩` and prove the remaining obligations. Introduce `b hb x hx q hq`.

Use `set g := b * An.tor K x * q with hg`. Use `set S := ∑ i ∈ Finset.range n, m i * An.sr x i with hS`. Establish `hsieg` using `siegel_of_sr hx`. Establish `hpt : ∀ X ∈ scaledUnipFD K n r M, ‖φ g - φ (unipGL X * g)‖ ≤ C₂ * (C₁ * Real.exp (-An.sr x r)) * (C₃' * Real.exp S)`. Introduce `X hX`.

Use `set Y := conjArch K n g (truncInf X) with hY`. Establish `hYn : ‖Y‖ ≤ C₁ * Real.exp (-An.sr x r)`. Establish `h` using `hC₁ b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) hsieg q hq (truncInf X) (fun p => rfl) (fun p => infinite_mem_scaledInfSet hM hX p)`. Rewrite `h` using `[exp_div_exp_eq hr hrn x]`. Conclude with `h`.

Establish `hYR : ‖Y‖ ≤ C₁ * Real.exp t₀` using `hYn.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hx r])) hC₁0)`. Take `⟨u, hu⟩` from `hMc b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) q hq (truncFin X) (fun p => rfl) (fun p => exists_finite_eq_natCast_mul hM hX p)`. Establish `hu' : g⁻¹ * unipGL (truncFin X) * g = finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)` using `hu`. Establish `hdecomp : unipGL X * g = g * archExp Y * (g⁻¹ * unipGL (truncFin X) * g)`. Rewrite using `[hY, ← conj_unipGL_eq_archExp g (truncInf X) (fun p => rfl)]`.

Use `conv_lhs => rw [← truncInf_add_truncFin X, unipGL_add]`. Use `group`. Establish `heq : φ (unipGL X * g) = φ (g * archExp Y)` using `by rw [hdecomp, hu', hlev]`. Establish `hMg : ∀ q' ∈ Q₀, ‖φ (g * q')‖ ≤ C₃' * Real.exp S`. Introduce `q' hq'`.

Establish `h` using `hC₃ b hb x hx (q * q') (Set.mul_mem_mul hq hq')`. Rewrite using `[show g * q' = b * An.tor K x * (q * q') by rw [hg, mul_assoc]]`. Conclude with `h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)`. Establish `hl` using `hlip g Y (C₃' * Real.exp S) (conjArch_mul_conjArch _ _ _) hYR hMg`. Rewrite using `[norm_sub_rev, heq]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hD` using `isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM`. Establish `hD1` using `unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM`. Take `⟨Cc, hCc, hDC⟩` from `exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM`. Establish `hint : IntegrableOn (fun X => φ (unipGL X * g)) (scaledUnipFD K n r M) (unipMeasure K n r)` using `((hN.cont.comp (continuous_unipGL.mul continuous_const)).continuousOn.integrableOn_compact hCc).mono_set hDC`.

Establish `hfin : unipMeasure K n r (scaledUnipFD K n r M) < ⊤`. Rewrite using `[hD1]`. Conclude with `ENNReal.one_lt_top`. Establish `hct : An.ctn r φ g = ∫ X in scaledUnipFD K n r M, φ (unipGL X * g) ∂unipMeasure K n r`. Rewrite using `[An.ctn, measureReal_def, unipMeasure_unipFundamentalDomain, ENNReal.toReal_one, Complex.ofReal_one, inv_one, one_mul]`.

Conclude with `constantTerm_eq_setIntegral hN.left hD g`. Establish `hdiff : φ g - An.ctn r φ g = ∫ X in scaledUnipFD K n r M, (φ g - φ (unipGL X * g)) ∂unipMeasure K n r`. Establish `hconst : IntegrableOn (fun _ => φ g) (scaledUnipFD K n r M) (unipMeasure K n r)` using `integrableOn_const hfin.ne enorm_ne_top`. Rewrite using `[hct, integral_sub hconst hint, setIntegral_const, measureReal_def, hD1, ENNReal.toReal_one, one_smul]`. Express the relevant statement in the definitionally equal form `‖φ g - An.ctn r φ g‖ ≤ _`.

Rewrite using `[hdiff]`. Use `(norm_setIntegral_le_of_norm_le_const hfin hpt).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[measureReal_def, hD1, ENNReal.toReal_one, mul_one, sum_update_sub hrn, ← hS, sub_eq_add_neg, Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diffstep_holds : An.DiffStep := by
  intro K _ _ n φ m r hr hrn hN hB ω hω hωB t₀ Q hQ
  obtain ⟨U, hU, hlev⟩ := hN.level
  obtain ⟨M, hM, hMc⟩ := exists_natCast_conj_mem U hU hω hQ r
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_conjArch_le hω hωB hQ (Real.exp_pos (-t₀)) hr hrn
    (isCompact_scaledInfSet (K := K) M)
  obtain ⟨Q₀, C₂, hQ₀, hC₂, hlip⟩ := hN.lip (C₁ * Real.exp t₀)
  obtain ⟨C₃, hC₃⟩ := hB ω hω hωB t₀ (Q * Q₀) (hQ.mul hQ₀)
  set C₃' := max C₃ 0 with hC₃'
  have hC₃'0 : 0 ≤ C₃' := le_max_right _ _
  refine ⟨C₂ * C₁ * C₃', ?_⟩
  intro b hb x hx q hq
  set g := b * An.tor K x * q with hg
  set S := ∑ i ∈ Finset.range n, m i * An.sr x i with hS
  have hsieg := siegel_of_sr hx
  have hpt : ∀ X ∈ scaledUnipFD K n r M, ‖φ g - φ (unipGL X * g)‖ ≤
      C₂ * (C₁ * Real.exp (-An.sr x r)) * (C₃' * Real.exp S) := by
    intro X hX
    set Y := conjArch K n g (truncInf X) with hY
    have hYn : ‖Y‖ ≤ C₁ * Real.exp (-An.sr x r) := by
      have h := hC₁ b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) hsieg q hq (truncInf X)
        (fun p => rfl) (fun p => infinite_mem_scaledInfSet hM hX p)
      rw [exp_div_exp_eq hr hrn x] at h
      exact h
    have hYR : ‖Y‖ ≤ C₁ * Real.exp t₀ :=
      hYn.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hx r])) hC₁0)
    obtain ⟨u, hu⟩ := hMc b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) q hq (truncFin X)
      (fun p => rfl) (fun p => exists_finite_eq_natCast_mul hM hX p)
    have hu' : g⁻¹ * unipGL (truncFin X) * g =
        finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := hu
    have hdecomp : unipGL X * g = g * archExp Y * (g⁻¹ * unipGL (truncFin X) * g) := by
      rw [hY, ← conj_unipGL_eq_archExp g (truncInf X) (fun p => rfl)]
      conv_lhs => rw [← truncInf_add_truncFin X, unipGL_add]
      group
    have heq : φ (unipGL X * g) = φ (g * archExp Y) := by rw [hdecomp, hu', hlev]
    have hMg : ∀ q' ∈ Q₀, ‖φ (g * q')‖ ≤ C₃' * Real.exp S := by
      intro q' hq'
      have h := hC₃ b hb x hx (q * q') (Set.mul_mem_mul hq hq')
      rw [show g * q' = b * An.tor K x * (q * q') by rw [hg, mul_assoc]]
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hl := hlip g Y (C₃' * Real.exp S) (conjArch_mul_conjArch _ _ _) hYR hMg
    rw [norm_sub_rev, heq]
    calc _ ≤ C₂ * ‖Y‖ * (C₃' * Real.exp S) := hl
      _ ≤ _ := by gcongr
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨Cc, hCc, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : IntegrableOn (fun X => φ (unipGL X * g)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    ((hN.cont.comp (continuous_unipGL.mul continuous_const)).continuousOn.integrableOn_compact
      hCc).mono_set hDC
  have hfin : unipMeasure K n r (scaledUnipFD K n r M) < ⊤ := by
    rw [hD1]
    exact ENNReal.one_lt_top
  have hct : An.ctn r φ g = ∫ X in scaledUnipFD K n r M, φ (unipGL X * g) ∂unipMeasure K n r := by
    rw [An.ctn, measureReal_def, unipMeasure_unipFundamentalDomain, ENNReal.toReal_one,
      Complex.ofReal_one, inv_one, one_mul]
    exact constantTerm_eq_setIntegral hN.left hD g
  have hdiff : φ g - An.ctn r φ g =
      ∫ X in scaledUnipFD K n r M, (φ g - φ (unipGL X * g)) ∂unipMeasure K n r := by
    have hconst : IntegrableOn (fun _ => φ g) (scaledUnipFD K n r M) (unipMeasure K n r) :=
      integrableOn_const hfin.ne enorm_ne_top
    rw [hct, integral_sub hconst hint, setIntegral_const, measureReal_def, hD1,
      ENNReal.toReal_one, one_smul]
  change ‖φ g - An.ctn r φ g‖ ≤ _
  rw [hdiff]
  refine (norm_setIntegral_le_of_norm_le_const hfin hpt).trans (le_of_eq ?_)
  rw [measureReal_def, hD1, ENNReal.toReal_one, mul_one, sum_update_sub hrn, ← hS, sub_eq_add_neg,
    Real.exp_add]
  ring

end PositivityTheory.Rg.Rs

end
