import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientsOfVectorGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentLatticeLift

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules.
-/
theorem norm_cexp_neg_four_pi_I_real (a : ℝ) : ‖cexp (-(4 * Real.pi * I) * (a : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/- English proof (translation)
Introduce `τ i k`. Establish `h : ∀ j, ω j τ k i = conj (ω j τ i k)` using `fun j => FourierCoefficientLattice.herm_of_LZ (X := X) (g := g) (hb := hω j) τ i k`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal, h]`.
-/
theorem isHermFam_real_linear_comb {r : ℕ} (X : Data E r) (g N : ℕ) (ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ)
    (hω : ∀ j, ω j ∈ X.LZ g) (t : Fin N → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k
  have h : ∀ j, ω j τ k i = conj (ω j τ i k) := fun j => FourierCoefficientLattice.herm_of_LZ (X := X) (g := g) (hb := hω j) τ i k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal, h]

/- English proof (translation)
Introduce `r X u hu hΛ la P hP hχ1 ν χ x hx`. Establish `hiso : ∀ i k, herm X.Gm (u i) (u k) = 0` using `hu.1`. Establish `hu0 : herm X.Gm (u 0) (u 0) = 0` using `hiso 0 0`. Establish `hper : ∀ b ∈ X.LZ X.g, ∀ y ∈ X.dom, P (X.Zb u b y) = P y` using `(h2 r X u hu hΛ).2.1 la P hP hχ1`. Establish `hcov : ∀ b, IsHermFam b → ∀ y ∈ X.dom, X.fz u X.g χ P (X.Zb u b y) = cexp (4 * Real.pi * I * X.pairR χ b) * X.fz u X.g χ P y` using `(h3 r X.toData u X.g hu X.g_pos la P hP.1 hP.2.1 hper χ).1.2.2`.

Distinguish the cases in `hf : IsHermFam χ ∧ X.IsFreqZ X.g χ`. Use `swap`. Establish `e : ∀ G, X.fz u X.g χ G x = 0` using `fun G => by simp only [Data.fz, if_neg hf]`. Rewrite using `[e, e]`. Apply the tactic sequence `split_ifs <;> rfl`.

Distinguish the cases in `hb : ∃ ω, X.IsLZBasis X.g ω`. Use `swap`. Establish `e : ∀ G, X.fz u X.g χ G x = 0` using `fun G => by simp only [Data.fz, if_pos hf, dif_neg hb]`. Rewrite using `[e, e]`. Apply the tactic sequence `split_ifs <;> rfl`.

Use `set ω := hb.choose with hωdef`. Establish `hωLZ : ∀ j, ω j ∈ X.LZ X.g` using `hb.choose_spec.1`. Use `set C : Set (Fin (4 * Fintype.card X.Ψ) → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) with hC`. Use `set B : (Fin (4 * Fintype.card X.Ψ) → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ := fun t => ∑ j, (t j : ℂ) • ω j with hB`. Establish `hBh : ∀ t, IsHermFam (B t)` using `fun t => isHermFam_real_linear_comb X.toData X.g _ ω hωLZ t`.

Establish `hfz : ∀ (G : Frame X.Ψ r → ℂ) y, X.fz u X.g χ G y = ∫ t in C, G (X.Zb u (B t) y) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t))`. Introduce `G y`. Simplify using `only [Data.fz, if_pos hf, dif_pos hb]`. Both sides reduce to the same expression. Use `set χr : X.Ψ → ℝ := fun τ => (χ τ 0 0).re with hχrdef`.

Establish `hflowcov : ∀ (s : X.Ψ → ℝ), ∀ y ∈ X.dom, X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) y) = cexp (4 * Real.pi * I * ((∑ τ, χr τ * s τ : ℝ) : ℂ)) * X.fz u X.g χ P y`. Introduce `s y hy`. Rewrite using `[flow_eq_Zb X.toData u s y, hcov _ (diag_unit_family_hermitian X.toData s) y hy, real_pairing_diag_unit]`. Establish `hpinv : ∀ p ∈ X.periods la, X.fz u X.g χ P (X.flow (u 0) (cR X.toData p) x) = X.fz u X.g χ P x`. Introduce `p hp`.

Rewrite using `[hfz, hfz]`. Use `setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc) fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← flow_Zb_comm X.toData u hiso, sec_periodic X.toData la P hP (hΛ 0) hu0 hp _ (Data.Zb_dom X.toData u hiso _ (hBh t) hx)]`. Establish `hfreq : X.fz u X.g χ P x ≠ 0 → ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, χr τ * p τ = k`. Introduce `hne p hp`.

Establish `h1` using `hflowcov p x hx`. Rewrite `h1` using `[hpinv p hp]`. Establish `h2 : cexp (4 * Real.pi * I * ((∑ τ, χr τ * p τ : ℝ) : ℂ)) = 1` using `mul_right_cancel₀ hne (h1.symm.trans (one_mul _).symm)`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h2`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `hpi : (2 * Real.pi * I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, I_ne_zero]`. Establish `h3' : ((2 * ∑ τ, χr τ * p τ : ℝ) : ℂ) = (n : ℂ)`. Apply `mul_right_cancel₀ hpi` to reduce the goal to its premises. Move the coercions through the operations in `at hn ⊢`. Take the linear combination `hn`.

Conclude with `h3'` after adjusting the coercions. Establish `hcond : (∀ τ, χ τ 0 0 = (ν τ : ℂ)) ↔ χr = ν`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `τ`.

Simplify `congrArg Complex.re (h τ)` using `[hχrdef]`. Introduce `h τ`. Establish `h1 : χ τ 0 0 = ((χ τ 0 0).re : ℂ)` using `(Complex.conj_eq_iff_re.1 (hf.1 τ 0 0).symm).symm`. Rewrite using `[h1]`. Conclude with `congrArg (fun z : ℝ => (z : ℂ)) (congrFun h τ)`.

Distinguish the cases in `hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k`. Use `swap`. Establish `hfj0 : X.fj la (u 0) ν P = fun _ => 0`. Use function extensionality and compare the values at `y`. Simplify using `only [Data.fj, if_neg hν]`.

Establish `hL : X.fz u X.g χ (X.fj la (u 0) ν P) x = 0`. Rewrite using `[hfj0, hfz]`. Simplify using the standard rewrite rules. Rewrite using `[hL]`. Use `split_ifs with hc`.

Assume the negation of the conclusion as `hne`. Apply `hν` to reduce the goal to its premises. Introduce `p hp`. Establish `hr` using `hcond.1 hc`. Take `⟨k, hk⟩` from `hfreq (fun h => hne h.symm) p hp`.

Conclude with `⟨k, by rw [← hr]; exact hk⟩`. Both sides reduce to the same expression. Establish `hDe` using `fd_exists X.toData la`. Use `set D := hDe.choose with hDdef`. Take `⟨hDm, hDfd, hDpos, hDfin⟩` from `hDe.choose_spec`.

Establish `hfj : ∀ y, X.fj la (u 0) ν P y = ((volume D).toReal : ℂ)⁻¹ * ∫ s in D, P (X.flow (u 0) (cR X.toData s) y) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)`. Introduce `y`. Simplify using `only [Data.fj, if_pos hν, dif_pos hDe]`. Both sides reduce to the same expression. Establish `hCm : MeasurableSet C` using `MeasurableSet.univ_pi fun _ => measurableSet_Icc`.

Establish `hCc : IsCompact C` using `isCompact_univ_pi fun _ => isCompact_Icc`. Use `set F : (Fin (4 * Fintype.card X.Ψ) → ℝ) → (X.Ψ → ℝ) → ℂ := fun t s => P (X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x)) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t)) with hF`. Establish `hherm_add : ∀ a b : X.Ψ → Fin 2 → Fin 2 → ℂ, IsHermFam a → IsHermFam b → IsHermFam (a + b)`. Introduce `a b ha hb' τ i k`. Simplify using `only [Pi.add_apply, map_add, ha τ i k, hb' τ i k]`.

Establish `hflowZ : ∀ (s : X.Ψ → ℝ) t, X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x) = X.Zb u (e00 X.toData s + B t) x`. Introduce `s t`. Rewrite using `[flow_eq_Zb, Data.Zb_Zb X.toData u hiso]`. Establish `hdom : ∀ (s : X.Ψ → ℝ) t, X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x) ∈ X.dom`. Introduce `s t`.

Rewrite using `[hflowZ]`. Conclude with `Data.Zb_dom X.toData u hiso _ (hherm_add _ _ (diag_unit_family_hermitian X.toData s) (hBh t)) hx`. Establish `he00c : Continuous (e00 X.toData)`. Use `continuous_pi fun τ => continuous_pi fun i => continuous_pi fun k => ?_` and prove the remaining obligations. Simplify using `only [e00]`.

Use `split_ifs`. Use `fun_prop`. Conclude with `continuous_const`. Establish `hBc : Continuous B`. Simplify using `only [hB]`.

Use `fun_prop`. Establish `hPc : Continuous fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) => P (X.flow (u 0) (cR X.toData q.2) (X.Zb u (B q.1) x))`. Establish `e : (fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) => P (X.flow (u 0) (cR X.toData q.2) (X.Zb u (B q.1) x))) = fun q => P (X.Zb u (e00 X.toData q.2 + B q.1) x)`. Use function extensionality and compare the values at `q`. Rewrite using `[hflowZ]`.

Rewrite using `[e]`. Use `hP.1.continuousOn.comp_continuous ((Zb_cont X.toData u x).comp ?_) fun q => ?_` and prove the remaining obligations. Conclude with `(he00c.comp continuous_snd).add (hBc.comp continuous_fst)`. Conclude with `Data.Zb_dom X.toData u hiso _ (hherm_add _ _ (diag_unit_family_hermitian X.toData q.2) (hBh q.1)) hx`. Establish `hFc : Continuous (Function.uncurry F)`.

Simplify using `only [hF, Function.uncurry_def]`. Use `(hPc.mul ?_).mul ?_` and prove the remaining obligations. Use `fun_prop`. Establish `: Continuous fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) => X.pairR χ (B q.1)`. Simplify using `only [Data.pairR]`.

Use `fun_prop`. Use `fun_prop`. Take `⟨K, hK, hKrep⟩` from `compact_reps X.toData la`. Take `⟨M, hM⟩` from `(hK.prod hCc).exists_bound_of_continuousOn ((continuous_norm.comp (hPc.comp (continuous_snd.prodMk continuous_fst))).continuousOn)`. Establish `hbound : ∀ t ∈ C, ∀ s, ‖F t s‖ ≤ M`.

Introduce `t ht s`. Take `⟨p, hp, hsp⟩` from `hKrep s`. Establish `hy : X.Zb u (B t) x ∈ X.dom` using `Data.Zb_dom X.toData u hiso _ (hBh t) hx`. Establish `hPs : P (X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x)) = P (X.flow (u 0) (cR X.toData (s - p)) (X.Zb u (B t) x))`. Establish `e1 : cR X.toData s = cR X.toData p + cR X.toData (s - p)`.

Rewrite using `[← cR_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[e1, ← flow_flow X.toData hu0, sec_periodic X.toData la P hP (hΛ 0) hu0 hp _ (flow_real_mem_dom X.toData hu0 _ _ hy)]`. Establish `h1` using `hM (s - p, t) ⟨hsp, ht⟩`.

Simplify using `only [Function.comp, norm_norm] at h1`. Simplify using `only [hF, norm_mul, Complex.norm_exp]`. Rewrite using `[hPs]`. Establish `h2 : (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ)).re = 0` using `by simp`. Establish `h3 : (-(4 * (Real.pi : ℂ) * I) * (X.pairR χ (B t) : ℂ)).re = 0` using `by simp`.

Rewrite using `[h2, h3, Real.exp_zero, mul_one, mul_one]`. Conclude with `h1`. Establish `hfinC : volume C < ⊤` using `hCc.measure_lt_top`. Establish `hint : Integrable (Function.uncurry F) ((volume.restrict C).prod (volume.restrict D))`. Rewrite using `[Measure.prod_restrict]`.

Establish `: IsFiniteMeasure ((volume.prod volume).restrict (C ×ˢ D))`. Use `isFiniteMeasure_restrict.2 ?_` and prove the remaining obligations. Rewrite using `[Measure.prod_prod]`. Conclude with `ENNReal.mul_ne_top hfinC.ne hDfin.ne`. Use `(integrable_const M).mono' hFc.aestronglyMeasurable ?_` and prove the remaining obligations.

Use `(ae_restrict_mem (hCm.prod hDm)).mono fun q hq => ?_` and prove the remaining obligations. Conclude with `hbound q.1 hq.1 q.2`. Rewrite using `[hfz]`. Establish `e1 : ∀ t, X.fj la (u 0) ν P (X.Zb u (B t) x) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t)) = ((volume D).toReal : ℂ)⁻¹ * ∫ s in D, F t s`. Introduce `t`.

Rewrite using `[hfj, mul_assoc, ← integral_mul_const]`. Repeatedly rewrite using `[e1]`. Rewrite using `[integral_const_mul, integral_integral_swap hint]`. Establish `e2 : ∀ s, ∫ t in C, F t s = cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) * X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) x)`. Introduce `s`.

Rewrite using `[hfz, ← integral_const_mul]`. Use `setIntegral_congr_fun hCm fun t _ => ?_` and prove the remaining obligations. Simplify using `only [hF]`. Rewrite using `[flow_Zb_comm X.toData u hiso]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[e2]`. Establish `e3 : ∀ s : X.Ψ → ℝ, cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) * X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) x) = X.fz u X.g χ P x * cexp (4 * Real.pi * I * ∑ τ, (((χr - ν) τ : ℝ) : ℂ) * s τ)`. Introduce `s`. Rewrite using `[hflowcov s x hx, mul_left_comm, ← mul_assoc, ← Complex.exp_add, mul_comm]`. Use `congr 2`.

Simplify using `only [Pi.sub_apply]`. Use `push_cast`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e3]`.

Rewrite using `[integral_const_mul]`. Distinguish the cases in `h0 : X.fz u X.g χ P x = 0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Establish `hμ : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, (χr - ν) τ * p τ = k`.

Introduce `p hp`. Take `⟨k1, hk1⟩` from `hfreq h0 p hp`. Take `⟨k2, hk2⟩` from `hν p hp`. Use `⟨k1 - k2, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]`.

Use `push_cast`. Rewrite using `[hk1, hk2]`. Rewrite using `[orth (X.periods la) D hDfd (χr - ν) hμ]`. Establish `hvD : ((volume D).toReal : ℂ) ≠ 0`. Establish `: 0 < (volume D).toReal` using `ENNReal.toReal_pos hDpos.ne' hDfin.ne`.

Conclude with `this.ne'` after adjusting the coercions. Distinguish the cases in `hc : χr = ν`. Rewrite using `[if_pos (sub_eq_zero.2 hc), if_pos (hcond.2 hc)]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[if_neg (fun h => hc (sub_eq_zero.1 h)), if_neg (fun h => hc (hcond.1 h))]`.

Simplify using the standard rewrite rules.
-/
theorem fourier_coefficient_support_of (h3 : FourierCoefficientProperties (E := E)) (h2 : UnipotentLatticeLift (E := E)) :
    FourierCoefficientSupport (E := E) := by
  intro r X u hu hΛ la P hP hχ1 ν χ x hx
  classical
  have hiso : ∀ i k, herm X.Gm (u i) (u k) = 0 := hu.1
  have hu0 : herm X.Gm (u 0) (u 0) = 0 := hiso 0 0
  have hper : ∀ b ∈ X.LZ X.g, ∀ y ∈ X.dom, P (X.Zb u b y) = P y :=
    (h2 r X u hu hΛ).2.1 la P hP hχ1
  have hcov : ∀ b, IsHermFam b → ∀ y ∈ X.dom,
      X.fz u X.g χ P (X.Zb u b y) = cexp (4 * Real.pi * I * X.pairR χ b) * X.fz u X.g χ P y :=
    (h3 r X.toData u X.g hu X.g_pos la P hP.1 hP.2.1 hper χ).1.2.2
  by_cases hf : IsHermFam χ ∧ X.IsFreqZ X.g χ
  swap
  · have e : ∀ G, X.fz u X.g χ G x = 0 := fun G => by simp only [Data.fz, if_neg hf]
    rw [e, e]
    split_ifs <;> rfl
  by_cases hb : ∃ ω, X.IsLZBasis X.g ω
  swap
  · have e : ∀ G, X.fz u X.g χ G x = 0 := fun G => by simp only [Data.fz, if_pos hf, dif_neg hb]
    rw [e, e]
    split_ifs <;> rfl
  set ω := hb.choose with hωdef
  have hωLZ : ∀ j, ω j ∈ X.LZ X.g := hb.choose_spec.1
  set C : Set (Fin (4 * Fintype.card X.Ψ) → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) with hC
  set B : (Fin (4 * Fintype.card X.Ψ) → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ := fun t => ∑ j, (t j : ℂ) • ω j with hB
  have hBh : ∀ t, IsHermFam (B t) := fun t => isHermFam_real_linear_comb X.toData X.g _ ω hωLZ t
  have hfz : ∀ (G : Frame X.Ψ r → ℂ) y, X.fz u X.g χ G y =
      ∫ t in C, G (X.Zb u (B t) y) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t)) := by
    intro G y
    simp only [Data.fz, if_pos hf, dif_pos hb]
    rfl
  set χr : X.Ψ → ℝ := fun τ => (χ τ 0 0).re with hχrdef
  have hflowcov : ∀ (s : X.Ψ → ℝ), ∀ y ∈ X.dom,
      X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) y) =
        cexp (4 * Real.pi * I * ((∑ τ, χr τ * s τ : ℝ) : ℂ)) * X.fz u X.g χ P y := by
    intro s y hy
    rw [flow_eq_Zb X.toData u s y, hcov _ (diag_unit_family_hermitian X.toData s) y hy, real_pairing_diag_unit]
  have hpinv : ∀ p ∈ X.periods la,
      X.fz u X.g χ P (X.flow (u 0) (cR X.toData p) x) = X.fz u X.g χ P x := by
    intro p hp
    rw [hfz, hfz]
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc) fun t _ => ?_
    rw [← flow_Zb_comm X.toData u hiso,
      sec_periodic X.toData la P hP (hΛ 0) hu0 hp _ (Data.Zb_dom X.toData u hiso _ (hBh t) hx)]
  have hfreq : X.fz u X.g χ P x ≠ 0 → ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, χr τ * p τ = k := by
    intro hne p hp
    have h1 := hflowcov p x hx
    rw [hpinv p hp] at h1
    have h2 : cexp (4 * Real.pi * I * ((∑ τ, χr τ * p τ : ℝ) : ℂ)) = 1 :=
      mul_right_cancel₀ hne (h1.symm.trans (one_mul _).symm)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have h3' : ((2 * ∑ τ, χr τ * p τ : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_right_cancel₀ hpi
      push_cast at hn ⊢
      linear_combination hn
    exact_mod_cast h3'
  have hcond : (∀ τ, χ τ 0 0 = (ν τ : ℂ)) ↔ χr = ν := by
    constructor
    · intro h
      funext τ
      simpa [hχrdef] using congrArg Complex.re (h τ)
    · intro h τ
      have h1 : χ τ 0 0 = ((χ τ 0 0).re : ℂ) :=
        (Complex.conj_eq_iff_re.1 (hf.1 τ 0 0).symm).symm
      rw [h1]
      exact congrArg (fun z : ℝ => (z : ℂ)) (congrFun h τ)
  by_cases hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k
  swap
  · have hfj0 : X.fj la (u 0) ν P = fun _ => 0 := by
      funext y
      simp only [Data.fj, if_neg hν]
    have hL : X.fz u X.g χ (X.fj la (u 0) ν P) x = 0 := by
      rw [hfj0, hfz]
      simp
    rw [hL]
    split_ifs with hc
    · by_contra hne
      apply hν
      intro p hp
      have hr := hcond.1 hc
      obtain ⟨k, hk⟩ := hfreq (fun h => hne h.symm) p hp
      exact ⟨k, by rw [← hr]; exact hk⟩
    · rfl

  have hDe := fd_exists X.toData la
  set D := hDe.choose with hDdef
  obtain ⟨hDm, hDfd, hDpos, hDfin⟩ := hDe.choose_spec
  have hfj : ∀ y, X.fj la (u 0) ν P y = ((volume D).toReal : ℂ)⁻¹ *
      ∫ s in D, P (X.flow (u 0) (cR X.toData s) y) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) := by
    intro y
    simp only [Data.fj, if_pos hν, dif_pos hDe]
    rfl
  have hCm : MeasurableSet C := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hCc : IsCompact C := isCompact_univ_pi fun _ => isCompact_Icc

  set F : (Fin (4 * Fintype.card X.Ψ) → ℝ) → (X.Ψ → ℝ) → ℂ := fun t s =>
    P (X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x)) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t)) with hF
  have hherm_add : ∀ a b : X.Ψ → Fin 2 → Fin 2 → ℂ, IsHermFam a → IsHermFam b → IsHermFam (a + b) := by
    intro a b ha hb' τ i k
    simp only [Pi.add_apply, map_add, ha τ i k, hb' τ i k]
  have hflowZ : ∀ (s : X.Ψ → ℝ) t, X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x) =
      X.Zb u (e00 X.toData s + B t) x := by
    intro s t
    rw [flow_eq_Zb, Data.Zb_Zb X.toData u hiso]
  have hdom : ∀ (s : X.Ψ → ℝ) t, X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x) ∈ X.dom := by
    intro s t
    rw [hflowZ]
    exact Data.Zb_dom X.toData u hiso _ (hherm_add _ _ (diag_unit_family_hermitian X.toData s) (hBh t)) hx
  have he00c : Continuous (e00 X.toData) := by
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun k => ?_
    simp only [e00]
    split_ifs
    · fun_prop
    · exact continuous_const
  have hBc : Continuous B := by
    simp only [hB]
    fun_prop
  have hPc : Continuous fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) =>
      P (X.flow (u 0) (cR X.toData q.2) (X.Zb u (B q.1) x)) := by
    have e : (fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) =>
        P (X.flow (u 0) (cR X.toData q.2) (X.Zb u (B q.1) x))) =
        fun q => P (X.Zb u (e00 X.toData q.2 + B q.1) x) := by
      funext q
      rw [hflowZ]
    rw [e]
    refine hP.1.continuousOn.comp_continuous ((Zb_cont X.toData u x).comp ?_) fun q => ?_
    · exact (he00c.comp continuous_snd).add (hBc.comp continuous_fst)
    · exact Data.Zb_dom X.toData u hiso _ (hherm_add _ _ (diag_unit_family_hermitian X.toData q.2) (hBh q.1)) hx
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    refine (hPc.mul ?_).mul ?_
    · fun_prop
    · have : Continuous fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) => X.pairR χ (B q.1) := by
        simp only [Data.pairR]
        fun_prop
      fun_prop

  obtain ⟨K, hK, hKrep⟩ := compact_reps X.toData la
  obtain ⟨M, hM⟩ := (hK.prod hCc).exists_bound_of_continuousOn
    ((continuous_norm.comp (hPc.comp (continuous_snd.prodMk continuous_fst))).continuousOn)
  have hbound : ∀ t ∈ C, ∀ s, ‖F t s‖ ≤ M := by
    intro t ht s
    obtain ⟨p, hp, hsp⟩ := hKrep s
    have hy : X.Zb u (B t) x ∈ X.dom := Data.Zb_dom X.toData u hiso _ (hBh t) hx
    have hPs : P (X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x)) =
        P (X.flow (u 0) (cR X.toData (s - p)) (X.Zb u (B t) x)) := by
      have e1 : cR X.toData s = cR X.toData p + cR X.toData (s - p) := by
        rw [← cR_add]
        congr 1
        abel
      rw [e1, ← flow_flow X.toData hu0,
        sec_periodic X.toData la P hP (hΛ 0) hu0 hp _ (flow_real_mem_dom X.toData hu0 _ _ hy)]
    have h1 := hM (s - p, t) ⟨hsp, ht⟩
    simp only [Function.comp, norm_norm] at h1
    simp only [hF, norm_mul, Complex.norm_exp]
    rw [hPs]
    have h2 : (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ)).re = 0 := by simp
    have h3 : (-(4 * (Real.pi : ℂ) * I) * (X.pairR χ (B t) : ℂ)).re = 0 := by simp
    rw [h2, h3, Real.exp_zero, mul_one, mul_one]
    exact h1
  have hfinC : volume C < ⊤ := hCc.measure_lt_top
  have hint : Integrable (Function.uncurry F) ((volume.restrict C).prod (volume.restrict D)) := by
    rw [Measure.prod_restrict]
    have : IsFiniteMeasure ((volume.prod volume).restrict (C ×ˢ D)) := by
      refine isFiniteMeasure_restrict.2 ?_
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top hfinC.ne hDfin.ne
    refine (integrable_const M).mono' hFc.aestronglyMeasurable ?_
    refine (ae_restrict_mem (hCm.prod hDm)).mono fun q hq => ?_
    exact hbound q.1 hq.1 q.2

  rw [hfz]
  have e1 : ∀ t, X.fj la (u 0) ν P (X.Zb u (B t) x) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t)) =
      ((volume D).toReal : ℂ)⁻¹ * ∫ s in D, F t s := by
    intro t
    rw [hfj, mul_assoc, ← integral_mul_const]
  simp_rw [e1]
  rw [integral_const_mul, integral_integral_swap hint]
  have e2 : ∀ s, ∫ t in C, F t s = cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) *
      X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) x) := by
    intro s
    rw [hfz, ← integral_const_mul]
    refine setIntegral_congr_fun hCm fun t _ => ?_
    simp only [hF]
    rw [flow_Zb_comm X.toData u hiso]
    ring
  simp_rw [e2]
  have e3 : ∀ s : X.Ψ → ℝ, cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) *
      X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) x) =
      X.fz u X.g χ P x * cexp (4 * Real.pi * I * ∑ τ, (((χr - ν) τ : ℝ) : ℂ) * s τ) := by
    intro s
    rw [hflowcov s x hx, mul_left_comm, ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 2
    simp only [Pi.sub_apply]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  simp_rw [e3]
  rw [integral_const_mul]
  by_cases h0 : X.fz u X.g χ P x = 0
  · rw [h0]
    simp
  have hμ : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, (χr - ν) τ * p τ = k := by
    intro p hp
    obtain ⟨k1, hk1⟩ := hfreq h0 p hp
    obtain ⟨k2, hk2⟩ := hν p hp
    refine ⟨k1 - k2, ?_⟩
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
    push_cast
    rw [hk1, hk2]
  rw [orth (X.periods la) D hDfd (χr - ν) hμ]
  have hvD : ((volume D).toReal : ℂ) ≠ 0 := by
    have : 0 < (volume D).toReal := ENNReal.toReal_pos hDpos.ne' hDfin.ne
    exact_mod_cast this.ne'
  by_cases hc : χr = ν
  · rw [if_pos (sub_eq_zero.2 hc), if_pos (hcond.2 hc)]
    field_simp
  · rw [if_neg (fun h => hc (sub_eq_zero.1 h)), if_neg (fun h => hc (hcond.1 h))]
    simp

/- English proof (translation)
The claim follows from `fourier_coefficient_support_of fourier_coefficients_holds unipotent_lattice_lift`.
-/
theorem fourier_coefficient_support_holds : FourierCoefficientSupport (E := E) := fourier_coefficient_support_of fourier_coefficients_holds unipotent_lattice_lift

end ReciprocityTheory.ChartRestriction.G.FD
