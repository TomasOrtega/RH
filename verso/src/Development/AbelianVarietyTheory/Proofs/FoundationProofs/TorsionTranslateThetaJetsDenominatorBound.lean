import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstMulLogEqNSer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicWeierstrassModelAbscissaTwoTorsionLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormJetExpNegMulLe

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TorsionJets

open PowerSeries GlobalTheory.ThetaParam

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `h : (n : ℂ) ∈ Qbar` using `natCast_mem _ n`. Simplify using `only [lamC, dif_pos h]`. Rewrite using `[← map_natCast lam n]`. Both sides reduce to the same expression.
-/
theorem lamC_natCast (lam : Qbar →+* ℂ_[p]) (n : ℕ) : lamC lam (n : ℂ) = n := by
  have h : (n : ℂ) ∈ Qbar := natCast_mem _ n
  simp only [lamC, dif_pos h]
  rw [← map_natCast lam n]; rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Use function extensionality and compare the values at `z`. Rewrite using `[iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ, smul_eq_mul, pow_succ, mul_assoc]`.
-/
theorem iteratedDeriv_scale (G : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => G (c * z)) = fun z => c ^ n * iteratedDeriv n G (c * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ,
      smul_eq_mul, pow_succ, mul_assoc]

/- English proof (translation)
Establish `h : ((n.factorial : ℕ) : ℂ) ∈ Qbar` using `natCast_mem _ _`. Establish `h0 : ((n.factorial : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce `hG`. Conclude with `div_mem hG h`.

Introduce `hG`. Use `mul_mem h hG` as an intermediate fact. Rewrite `this` using `[coef1, mul_div_cancel₀ _ h0]`. Then use the resulting hypothesis.
-/
theorem deriv_mem_iff (G : ℂ → ℂ) (n : ℕ) : iteratedDeriv n G 0 ∈ Qbar ↔ coef1 G n ∈ Qbar := by
  have h : ((n.factorial : ℕ) : ℂ) ∈ Qbar := natCast_mem _ _
  have h0 : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  constructor
  · intro hG
    exact div_mem hG h
  · intro hG
    have := mul_mem h hG
    rwa [coef1, mul_div_cancel₀ _ h0] at this

/- English proof (translation)
Establish `hex : HasSubst g.ex` using `HasSubst.of_constantCoeff_zero' hOk.2.2.1`. Establish `harg` using `HasSubst.of_constantCoeff_zero' (constantCoeff_arg g)`. Establish `e : (subst g.ex (g.atU G) : PowerSeries ℂ_[p]) = rescale ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) (GL3Theta.ser1 g.lam G)`. Rewrite using `[GL3Theta.G1.atU, subst_comp_subst_apply harg hex, rescale_eq_subst]`. Use `congr 1`.

Rewrite using `[← Algebra.smul_def, subst_smul hex, hOk.2.2.2]`. Establish `h : ((n.factorial : ℕ) : ℂ) ∈ Qbar` using `natCast_mem _ _`. Establish `h0 : ((n.factorial : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Rewrite using `[e, coeff_rescale, GL3Theta.ser1, coeff_mk, mul_left_comm, ← lamC_natCast g.lam, ← lamC_mul _ h (div_mem hG h), mul_div_cancel₀ _ h0]`.
-/
theorem jet_atU (g : GL3Theta.G1 p) (hOk : g.Ok) (G : ℂ → ℂ) (n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    (n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU G) : PowerSeries ℂ_[p]) =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ n * lamC g.lam (iteratedDeriv n G 0) := by
  have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' hOk.2.2.1
  have harg := HasSubst.of_constantCoeff_zero' (constantCoeff_arg g)
  have e : (subst g.ex (g.atU G) : PowerSeries ℂ_[p]) =
      rescale ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) (GL3Theta.ser1 g.lam G) := by
    rw [GL3Theta.G1.atU, subst_comp_subst_apply harg hex, rescale_eq_subst]
    congr 1
    rw [← Algebra.smul_def, subst_smul hex, hOk.2.2.2]
  have h : ((n.factorial : ℕ) : ℂ) ∈ Qbar := natCast_mem _ _
  have h0 : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [e, coeff_rescale, GL3Theta.ser1, coeff_mk, mul_left_comm, ← lamC_natCast g.lam,
    ← lamC_mul _ h (div_mem hG h), mul_div_cancel₀ _ h0]

/- English proof (translation)
Rewrite using `[jet_atU g hOk G n hG, norm_mul, norm_pow, Units.val_inv_eq_inv_val, norm_inv, hu]`. Simplify using the standard rewrite rules.
-/
theorem norm_jet_atU (g : GL3Theta.G1 p) (hOk : g.Ok) (hu : ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1)
    (G : ℂ → ℂ) (n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    ‖(n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU G) : PowerSeries ℂ_[p])‖ =
      ‖lamC g.lam (iteratedDeriv n G 0)‖ := by
  rw [jet_atU g hOk G n hG, norm_mul, norm_pow, Units.val_inv_eq_inv_val, norm_inv, hu]
  simp

/- English proof (translation)
Establish `hN : ((N : ℂ)) ^ n ∈ Qbar` using `pow_mem (natCast_mem _ _) _`. Establish `e : iteratedDeriv n (fun z => G ((N : ℂ) * z)) 0 = (N : ℂ) ^ n * iteratedDeriv n G 0`. Rewrite using `[iteratedDeriv_scale]`. Simplify using the standard rewrite rules. Rewrite using `[norm_jet_atU g hOk hu _ n (e ▸ mul_mem hN hG), e, lamC_mul _ hN hG, ← Nat.cast_pow, lamC_natCast, norm_mul, Nat.cast_pow, norm_pow]`.
-/
theorem norm_jet_atU_scale (g : GL3Theta.G1 p) (hOk : g.Ok) (hu : ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1)
    (G : ℂ → ℂ) (N n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    ‖(n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU fun z => G ((N : ℂ) * z)) : PowerSeries ℂ_[p])‖ =
      ‖(N : ℂ_[p])‖ ^ n * ‖lamC g.lam (iteratedDeriv n G 0)‖ := by
  have hN : ((N : ℂ)) ^ n ∈ Qbar := pow_mem (natCast_mem _ _) _
  have e : iteratedDeriv n (fun z => G ((N : ℂ) * z)) 0 = (N : ℂ) ^ n * iteratedDeriv n G 0 := by
    rw [iteratedDeriv_scale]; simp
  rw [norm_jet_atU g hOk hu _ n (e ▸ mul_mem hN hG), e, lamC_mul _ hN hG, ← Nat.cast_pow,
    lamC_natCast, norm_mul, Nat.cast_pow, norm_pow]

/- English proof (translation)
Establish `h0 : constantCoeff (logOf F) = 0` using `constantCoeff_logOf hF`. Establish `h1 : constantCoeff (-logOf F) = 0` using `by simp [h0]`. Establish `e : expPS (logOf F) * expPS (-logOf F) = 1`. Use `derivative.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, GlobalTheory.ExpJets.derivative_expPS _ h0, GlobalTheory.ExpJets.derivative_expPS _ h1, map_neg, derivative_one]`.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[constantCoeff_expPS]`. Establish `e2` using `exp_neg_log_mul F hF`. Take the linear combination `F * e - expPS (logOf F) * e2`.
-/
theorem expPS_logOf (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 1) : expPS (logOf F) = F := by
  have h0 : constantCoeff (logOf F) = 0 := constantCoeff_logOf hF
  have h1 : constantCoeff (-logOf F) = 0 := by simp [h0]
  have e : expPS (logOf F) * expPS (-logOf F) = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, GlobalTheory.ExpJets.derivative_expPS _ h0,
        GlobalTheory.ExpJets.derivative_expPS _ h1, map_neg, derivative_one]
      simp only [smul_eq_mul]
      ring
    · simp [constantCoeff_expPS]
  have e2 := exp_neg_log_mul F hF
  linear_combination F * e - expPS (logOf F) * e2

/- English proof (translation)
Rewrite using `[GlobalTheory.ExpJets.expPS_eq_subst F hF, GlobalTheory.ExpJets.expPS_eq_subst _ (by rw [constantCoeff_subst' ha, hF]), subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hF) (HasSubst.of_constantCoeff_zero' ha)]`.
-/
theorem subst_expPS {a F : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (hF : constantCoeff F = 0) :
    (subst a (expPS F) : PowerSeries ℂ_[p]) = expPS (subst a F) := by
  rw [GlobalTheory.ExpJets.expPS_eq_subst F hF,
    GlobalTheory.ExpJets.expPS_eq_subst _ (by rw [constantCoeff_subst' ha, hF]),
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hF) (HasSubst.of_constantCoeff_zero' ha)]

/- English proof (translation)
Use `set L := lamOf D cc δ with hL`. Take `⟨⟨-, hd, -, hq⟩, -⟩` from `GlobalTheory.OddTheta.sgStar_laws L (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1`. Establish `halg : ∀ x, InRationalLattice L x → ∀ n, coef1 (U1 L x (sgStar L)) n ∈ Qbar` using `(hI.use1 cc δ hCrv).1`. Establish `hne : ∃ z, sgStar L z ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Rewrite `hd` using `[show sgStar L = fun _ => 0 from funext h]`. Simplify using `at hd`. Establish `h2 : ((2 : ℕ) : ℂ) * t0 ∈ L` using `by simpa using hT.1`. Use `set c := U1 L t0 (sgStar L) 0 with hcdef`.

Establish `hcQ : c ∈ Qbar`. Use `halg t0 ⟨2, two_pos, h2⟩ 0` as an intermediate fact. Simplify `this` using `[coef1]`. Establish `hth : GL3Theta.th0 L t0 = fun z => c⁻¹ * U1 L t0 (sgStar L) z`. Use function extensionality and compare the values at `z`.

Rewrite using `[GL3Theta.th0, div_eq_inv_mul]`. Establish `hU : U1 L y (GL3Theta.th0 L t0) = fun z => (c⁻¹ * cocy L y t0) * U1 L (y + t0) (sgStar L) z`. Rewrite using `[hth, thetaTranslation_const_mul]`. Use function extensionality and compare the values at `z`. Rewrite using `[thetaTranslation_comp_eq_cocycle_mul, mul_assoc]`.

Establish `hr` using `cocy_root hne hq hy h2`. Establish `hsum : ((N * 2 : ℕ) : ℂ) * (y + t0) ∈ L`. Use `add_mem (nsmul_mem hy 2) (nsmul_mem h2 N)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hU, iteratedDeriv_const_mul_field]`. Conclude with `mul_mem (mul_mem (inv_mem hcQ) (root_mem (by positivity) hr)) ((deriv_mem_iff _ n).2 (halg _ ⟨N * 2, by positivity, hsum⟩ n))`.
-/
theorem deriv_translate_mem (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hCrv : Crv D cc δ) (t0 : ℂ) (hT : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (y : ℂ) (N : ℕ) (hN : 0 < N)
    (hy : (N : ℂ) * y ∈ lamOf D cc δ) (n : ℕ) :
    iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0 ∈ Qbar := by
  set L := lamOf D cc δ with hL
  obtain ⟨⟨-, hd, -, hq⟩, -⟩ :=
    GlobalTheory.OddTheta.sgStar_laws L (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1
  have halg : ∀ x, InRationalLattice L x → ∀ n, coef1 (U1 L x (sgStar L)) n ∈ Qbar := (hI.use1 cc δ hCrv).1
  have hne : ∃ z, sgStar L z ≠ 0 := by
    by_contra h
    push Not at h
    rw [show sgStar L = fun _ => 0 from funext h] at hd
    simp at hd
  have h2 : ((2 : ℕ) : ℂ) * t0 ∈ L := by simpa using hT.1
  set c := U1 L t0 (sgStar L) 0 with hcdef
  have hcQ : c ∈ Qbar := by
    have := halg t0 ⟨2, two_pos, h2⟩ 0
    simpa [coef1] using this
  have hth : GL3Theta.th0 L t0 = fun z => c⁻¹ * U1 L t0 (sgStar L) z := by
    funext z
    rw [GL3Theta.th0, div_eq_inv_mul]
  have hU : U1 L y (GL3Theta.th0 L t0) =
      fun z => (c⁻¹ * cocy L y t0) * U1 L (y + t0) (sgStar L) z := by
    rw [hth, thetaTranslation_const_mul]
    funext z
    rw [thetaTranslation_comp_eq_cocycle_mul, mul_assoc]
  have hr := cocy_root hne hq hy h2
  have hsum : ((N * 2 : ℕ) : ℂ) * (y + t0) ∈ L := by
    have := add_mem (nsmul_mem hy 2) (nsmul_mem h2 N)
    convert this using 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hU, iteratedDeriv_const_mul_field]
  exact mul_mem (mul_mem (inv_mem hcQ) (root_mem (by positivity) hr))
    ((deriv_mem_iff _ n).2 (halg _ ⟨N * 2, by positivity, hsum⟩ n))

/- English proof (translation)
Establish `e : (N : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (N : ℚ_[p])` using `(map_natCast _ _).symm`. Rewrite using `[e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Fact.out).2 h`.
-/
theorem norm_natCast_of_coprime {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have e : (N : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (N : ℚ_[p]) := (map_natCast _ _).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h

/- English proof (translation)
Introduce `D hI p hp lam cc δ hCrv hcop t0 hT y N hN hy hsp n`. Establish `halg` using `deriv_translate_mem D hI cc δ hCrv t0 hT y N hN hy`. Establish `halg0 : ∀ m, iteratedDeriv m (GL3Theta.th0 (lamOf D cc δ) t0) 0 ∈ Qbar` using `fun m => (deriv_mem_iff _ m).2 ((hI.use1 cc δ hCrv).2.1 t0 hT m)`. Use `⟨halg n, ?_⟩` and prove the remaining obligations. Take `⟨g, hAt, rfl, hu⟩` from `GlobalTheory.GenusOneDatum.exists_genusOne_datum D hI.model p lam cc δ hCrv hcop`.

Establish `hL : g.abelian₂ = lamOf D cc δ` using `hAt.2.2.2.1`. Establish `hOk` using `hAt.2.2.2.2`. Rewrite `hT`, `hy`, `halg`, `halg0`, the goal using `[← hL]`. Establish `hex0 : constantCoeff g.ex = 0` using `hOk.2.2.1`. Establish `hex : HasSubst g.ex` using `HasSubst.of_constantCoeff_zero' hex0`.

Establish `hD` using `(GlobalTheory.IntDLog.int_dlog p g hOk).1`. Take `⟨hodd, hsplit⟩` from `theta_param_integral D hI p cc δ g hAt t0 hT`. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast hp.out.one_le`. Establish `hfac : (1 : ℝ) ≤ (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1)` using `by split_ifs`. Conclude with `Real.one_le_rpow hp1 (by positivity)`.

Conclude with `le_rfl`. Distinguish the cases in `hpN : p ∣ N`. Take `⟨h, hh, e⟩` from `GlobalTheory.PullBackSplit.pull_back_split D hI p cc δ g hAt t0 hT y N hN hy hpN (hsp hpN)`. Establish `h0` using `(integral_iff _).1 (hsplit (hsp hpN)).1`. Establish `hN1 : ‖(N : ℂ_[p])‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one _ _`.

Establish `hN0 : 0 < ‖(N : ℂ_[p])‖` using `norm_pos_iff.2 (by exact_mod_cast hN.ne')`. Establish `key` using `norm_jet_atU_scale g hOk hu _ N n (halg n)`. Rewrite `key` using `[e, subst_mul hex]`. Establish `hle` using `GlobalTheory.ExpJets.norm_jet_mul_le (subst g.ex h) (subst g.ex (g.atU fun z => GL3Theta.th0 g.abelian₂ t0 ((N : ℂ) * z))) n 1 zero_le_one fun i j _ => by`. Use `mul_le_one₀ (hD h hh i) (norm_nonneg _) ?_` and prove the remaining obligations.

Rewrite using `[norm_jet_atU_scale g hOk hu _ N j (halg0 j), ← norm_jet_atU g hOk hu _ j (halg0 j)]`. Conclude with `mul_le_one₀ (pow_le_one₀ hN0.le hN1) (norm_nonneg _) (hD _ h0 j)`. Rewrite `hle` using `[key]`. Use `le_trans ?_ (le_mul_of_one_le_right (by positivity) hfac)` and prove the remaining obligations. Rewrite using `[inv_pow, ← mul_one (_ ^ n)⁻¹, le_inv_mul_iff₀ (by positivity)]`.

Conclude with `hle`. Establish `hc : Nat.Coprime N p` using `((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpN).symm`. Rewrite using `[norm_natCast_of_coprime hpN, inv_one, one_pow, one_mul, ← norm_jet_atU g hOk hu _ n (halg n)]`. Distinguish the cases in `hp2 : p = 2`. Conclude with `(hD _ ((integral_iff _).1 ((hsplit (Or.inl hp2)).2 y N hc hy)) n).trans hfac`.

Establish `hf` using `(integral_iff _).1 ((hodd hp2).2 y N hc hy)`. Take `⟨⟨-, hd, -, -⟩, -⟩` from `GlobalTheory.OddTheta.sgStar_laws g.abelian₂ (hL ▸ (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1)`. Establish `he` using `constantCoeff_ePhi1 g hOk.2.1 hd`. Use `set E := ePhi1 g.lam g.abelian₂ g.C g.wq with hE`. Use `set f := E⁻¹ * g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0)) with hfdef`.

Establish `hinv : E * E⁻¹ = 1` using `PowerSeries.mul_inv_cancel _ (by rw [he]; exact one_ne_zero)`. Establish `hph : -g.ph = logOf E`. Rewrite using `[GL3Theta.G1.ph, neg_neg]`. Conclude with `logMv_eq E he`. Establish `hph0 : constantCoeff g.ph = 0`.

Use `constantCoeff_logOf he` as an intermediate fact. Rewrite `this` using `[← hph]`. Simplify using `using this`. Establish `e : (subst g.ex (g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0))) : PowerSeries ℂ_[p]) = expPS (-(subst g.ex g.ph)) * subst g.ex f`. Establish `e1 : (-(subst g.ex g.ph) : PowerSeries ℂ_[p]) = subst g.ex (logOf E)`.

Rewrite using `[← hph, ← coe_substAlgHom hex, map_neg]`. Rewrite using `[e1, ← subst_expPS hex0 (constantCoeff_logOf he), expPS_logOf E he, ← subst_mul hex, hfdef, ← mul_assoc, hinv, one_mul]`. Take `⟨j1, -, j2, j3⟩` from `hI.jets p cc δ g hAt hp2`. Establish `hmain` using `fun (s : ℝ) (hs : 1 ≤ s) h2 => GlobalTheory.ExpJets.norm_jet_exp_neg_mul_le p (subst g.ex g.ph) s hs (by rw [constantCoeff_subst' hex0, hph0]) j1 h2 (subst g.ex f) (hD f hf) n`. Establish `hj : g.jetPh 2 = 2 * coeff 2 (subst g.ex g.ph : PowerSeries ℂ_[p])`.

Simplify using `[GL3Theta.G1.jetPh]`. Rewrite using `[e]`. Use `split_ifs with hd'`. Use `hmain ((p : ℝ) ^ ((1 : ℝ) / 4)) (Real.one_le_rpow hp1 (by positivity)) (by` as an intermediate fact. Rewrite using `[← hj, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]`.

Use `j3 hd' using 2` and compare the differences between its conclusion and the goal. Use the proof step `norm_num)`. Rewrite `this` using `[← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]`. Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Use `hmain 1 le_rfl (by rw [← hj, one_pow]; exact j2 hd')` as an intermediate fact. Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis.
-/
theorem jet_translate_le : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (y : ℂ) (Nn : ℕ), 0 < Nn → (Nn : ℂ) * y ∈ (lamOf D cc δ) → (p ∣ Nn → SplitIn D p) → ∀ n : ℕ, iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0 ∈ Qbar ∧ ‖lamC lam (iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0)‖ ≤ (‖(Nn : ℂ_[p])‖⁻¹) ^ n * (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
  intro D hI p hp lam cc δ hCrv hcop t0 hT y N hN hy hsp n
  have halg := deriv_translate_mem D hI cc δ hCrv t0 hT y N hN hy
  have halg0 : ∀ m, iteratedDeriv m (GL3Theta.th0 (lamOf D cc δ) t0) 0 ∈ Qbar := fun m =>
    (deriv_mem_iff _ m).2 ((hI.use1 cc δ hCrv).2.1 t0 hT m)
  refine ⟨halg n, ?_⟩
  obtain ⟨g, hAt, rfl, hu⟩ := GlobalTheory.GenusOneDatum.exists_genusOne_datum D hI.model p lam cc δ hCrv hcop
  have hL : g.abelian₂ = lamOf D cc δ := hAt.2.2.2.1
  have hOk := hAt.2.2.2.2
  rw [← hL] at hT hy halg halg0 ⊢
  have hex0 : constantCoeff g.ex = 0 := hOk.2.2.1
  have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' hex0
  have hD := (GlobalTheory.IntDLog.int_dlog p g hOk).1
  obtain ⟨hodd, hsplit⟩ := theta_param_integral D hI p cc δ g hAt t0 hT
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hfac : (1 : ℝ) ≤ (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
    split_ifs
    · exact Real.one_le_rpow hp1 (by positivity)
    · exact le_rfl
  by_cases hpN : p ∣ N
  · obtain ⟨h, hh, e⟩ := GlobalTheory.PullBackSplit.pull_back_split D hI p cc δ g hAt t0 hT y N hN hy hpN (hsp hpN)
    have h0 := (integral_iff _).1 (hsplit (hsp hpN)).1
    have hN1 : ‖(N : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    have hN0 : 0 < ‖(N : ℂ_[p])‖ := norm_pos_iff.2 (by exact_mod_cast hN.ne')
    have key := norm_jet_atU_scale g hOk hu _ N n (halg n)
    rw [e, subst_mul hex] at key
    have hle := GlobalTheory.ExpJets.norm_jet_mul_le (subst g.ex h)
      (subst g.ex (g.atU fun z => GL3Theta.th0 g.abelian₂ t0 ((N : ℂ) * z))) n 1 zero_le_one fun i j _ => by
        refine mul_le_one₀ (hD h hh i) (norm_nonneg _) ?_
        rw [norm_jet_atU_scale g hOk hu _ N j (halg0 j), ← norm_jet_atU g hOk hu _ j (halg0 j)]
        exact mul_le_one₀ (pow_le_one₀ hN0.le hN1) (norm_nonneg _) (hD _ h0 j)
    rw [key] at hle
    refine le_trans ?_ (le_mul_of_one_le_right (by positivity) hfac)
    rw [inv_pow, ← mul_one (_ ^ n)⁻¹, le_inv_mul_iff₀ (by positivity)]
    exact hle
  · have hc : Nat.Coprime N p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpN).symm
    rw [norm_natCast_of_coprime hpN, inv_one, one_pow, one_mul, ← norm_jet_atU g hOk hu _ n (halg n)]
    by_cases hp2 : p = 2
    · exact (hD _ ((integral_iff _).1 ((hsplit (Or.inl hp2)).2 y N hc hy)) n).trans hfac
    have hf := (integral_iff _).1 ((hodd hp2).2 y N hc hy)
    obtain ⟨⟨-, hd, -, -⟩, -⟩ :=
      GlobalTheory.OddTheta.sgStar_laws g.abelian₂ (hL ▸ (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1)
    have he := constantCoeff_ePhi1 g hOk.2.1 hd
    set E := ePhi1 g.lam g.abelian₂ g.C g.wq with hE
    set f := E⁻¹ * g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0)) with hfdef
    have hinv : E * E⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [he]; exact one_ne_zero)
    have hph : -g.ph = logOf E := by
      rw [GL3Theta.G1.ph, neg_neg]
      exact logMv_eq E he
    have hph0 : constantCoeff g.ph = 0 := by
      have := constantCoeff_logOf he
      rw [← hph] at this
      simpa using this
    have e : (subst g.ex (g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0))) : PowerSeries ℂ_[p]) =
        expPS (-(subst g.ex g.ph)) * subst g.ex f := by
      have e1 : (-(subst g.ex g.ph) : PowerSeries ℂ_[p]) = subst g.ex (logOf E) := by
        rw [← hph, ← coe_substAlgHom hex, map_neg]
      rw [e1, ← subst_expPS hex0 (constantCoeff_logOf he), expPS_logOf E he, ← subst_mul hex,
        hfdef, ← mul_assoc, hinv, one_mul]
    obtain ⟨j1, -, j2, j3⟩ := hI.jets p cc δ g hAt hp2
    have hmain := fun (s : ℝ) (hs : 1 ≤ s) h2 =>
      GlobalTheory.ExpJets.norm_jet_exp_neg_mul_le p (subst g.ex g.ph) s hs
        (by rw [constantCoeff_subst' hex0, hph0]) j1 h2 (subst g.ex f) (hD f hf) n
    have hj : g.jetPh 2 = 2 * coeff 2 (subst g.ex g.ph : PowerSeries ℂ_[p]) := by
      simp [GL3Theta.G1.jetPh]
    rw [e]
    split_ifs with hd'
    · have := hmain ((p : ℝ) ^ ((1 : ℝ) / 4)) (Real.one_le_rpow hp1 (by positivity)) (by
        rw [← hj, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        convert j3 hd' using 2
        norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
      convert this using 2
      ring
    · have := hmain 1 le_rfl (by rw [← hj, one_pow]; exact j2 hd')
      rwa [one_pow] at this

end GlobalTheory.TorsionJets
