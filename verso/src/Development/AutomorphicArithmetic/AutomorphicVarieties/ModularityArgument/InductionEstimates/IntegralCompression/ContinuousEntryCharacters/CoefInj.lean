import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefIdem
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.PeterWeyl

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

/- English proof (translation)
Establish `key : (fun k => conj (f k)) = 0`. Use `PW.eq_zero_of_forall_integral_coeff (Complex.continuous_conj.comp hf) fun n q l₁ l₂ => ?_` and prove the remaining obligations. Establish `h1` using `h n q l₁⁻¹ l₂⁻¹`. Rewrite `h1` using `[← integral_mul_left_K _ l₁, ← integral_mul_right_K _ l₂]`. Establish `h2` using `congrArg conj h1`.

Rewrite `h2` using `[← integral_conj, map_zero]`. Establish `hne : ((l₁ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q * (l₂ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q) ≠ 0` using `mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_U2 _)) (zpow_ne_zero _ (det_ne_zero_of_U2 _))`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[mul_zero, ← integral_const_mul, ← h2]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Establish `e : l₁⁻¹ * (l₁ * (k * l₂)) * l₂⁻¹ = k` using `by group`. Rewrite using `[e, map_mul, starRingEnd_self_apply, ← mul_assoc l₁, KT.psi_mul_mul]`. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `k`.

Simplify using `using congrFun key k`.
-/
private theorem pw2 {f : U2 → ℂ} (hf : Continuous f)
    (h : ∀ (n : ℕ) (q : ℤ) (l r : U2), ∫ m, conj (KT.psi n q n m) * f (l * m * r) ∂μK = 0) : f = 0 := by
  have key : (fun k => conj (f k)) = 0 := by
    refine PW.eq_zero_of_forall_integral_coeff (Complex.continuous_conj.comp hf) fun n q l₁ l₂ => ?_
    have h1 := h n q l₁⁻¹ l₂⁻¹
    rw [← integral_mul_left_K _ l₁, ← integral_mul_right_K _ l₂] at h1
    have h2 := congrArg conj h1
    rw [← integral_conj, map_zero] at h2
    have hne : ((l₁ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q * (l₂ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q) ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_U2 _)) (zpow_ne_zero _ (det_ne_zero_of_U2 _))
    apply mul_left_cancel₀ hne
    rw [mul_zero, ← integral_const_mul, ← h2]
    congr 1; funext k
    have e : l₁⁻¹ * (l₁ * (k * l₂)) * l₂⁻¹ = k := by group
    rw [e, map_mul, starRingEnd_self_apply, ← mul_assoc l₁, KT.psi_mul_mul]
    ring
  funext k
  simpa using congrFun key k

/- English proof (translation)
The claim follows from `hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))`.
-/
private theorem int2 {f : U2 × U2 → ℂ} (hf : Continuous f) : Integrable f (μK.prod μK) :=
  hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

/- English proof (translation)
Take `⟨-, hmul, -, -, -, -, -, -, hdg, -, hchi, -⟩` from `UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4`. Assume the negation of the conclusion as `hI`. Use `hν (hchi _ _ fun θ => ?_)` and prove the remaining obligations. Apply `mul_right_cancel₀ hI` to reduce the goal to its premises. Use `conv_rhs => rw [← integral_mul_left_eq_self _ ((tC (θ 0) (θ 1), tC (θ 2) (θ 3)) : U2 × U2)]`.

Rewrite using `[← integral_const_mul, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Establish `hθ : θ = ![θ 0, θ 1, θ 2, θ 3]`. Apply the tactic sequence `funext i; fin_cases i <;> rfl`.

Establish `e : bd (tC (θ 0) (θ 1) * p.1) (tC (θ 2) (θ 3) * p.2) * g = dg θ * (bd p.1 p.2 * g)`. Rewrite using `[← hmul, ← hdg, ← hθ, mul_assoc]`. Simplify using `only [Prod.fst_mul, Prod.snd_mul]`. Rewrite using `[e, hb, KT.psi_tC_mul n₁ q₁ le_rfl, KT.psi_tC_mul n₂ q₂ le_rfl, map_mul, map_mul]`. Establish `hc : chi (wt n₁ q₁ n₂ q₂) θ * (conj (Complex.exp (Complex.I * ((((n₁ : ℝ) + q₁) * θ 0 + ((n₁ : ℝ) - n₁ + q₁) * θ 1 : ℝ) : ℂ))) * conj (Complex.exp (Complex.I * ((((n₂ : ℝ) + q₂) * θ 2 + ((n₂ : ℝ) - n₂ + q₂) * θ 3 : ℝ) : ℂ)))) = 1`.

Rewrite using `[chi, ← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]`. Use `congr 1`. Establish `hs : ∑ i, ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ) = ((n₁ : ℂ) + q₁) * θ 0 + q₁ * θ 1 + ((n₂ : ℂ) + q₂) * θ 2 + q₂ * θ 3`. Use `Fin.sum_univ_four (fun i : Fin 4 => ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations.

Simplify using `[wt]`. Rewrite using `[hs]`. Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take the linear combination `(-(chi ν θ * conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g))) * hc`.
-/
private theorem tor2 (n₁ : ℕ) (q₁ : ℤ) (n₂ : ℕ) (q₂ : ℤ) (ν : Fin (2 + 2) → ℤ) (b : U4 → ℂ)
    (hb : ∀ θ h, b (dg θ * h) = chi ν θ * b h) (hν : ν ≠ wt n₁ q₁ n₂ q₂) (g : U4) :
    ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g) ∂(μK.prod μK) = 0 := by
  obtain ⟨-, hmul, -, -, -, -, -, -, hdg, -, hchi, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  by_contra hI
  refine hν (hchi _ _ fun θ => ?_)
  apply mul_right_cancel₀ hI
  conv_rhs => rw [← integral_mul_left_eq_self _ ((tC (θ 0) (θ 1), tC (θ 2) (θ 3)) : U2 × U2)]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; funext p
  have hθ : θ = ![θ 0, θ 1, θ 2, θ 3] := by
    funext i; fin_cases i <;> rfl
  have e : bd (tC (θ 0) (θ 1) * p.1) (tC (θ 2) (θ 3) * p.2) * g = dg θ * (bd p.1 p.2 * g) := by
    rw [← hmul, ← hdg, ← hθ, mul_assoc]
  simp only [Prod.fst_mul, Prod.snd_mul]
  rw [e, hb, KT.psi_tC_mul n₁ q₁ le_rfl, KT.psi_tC_mul n₂ q₂ le_rfl, map_mul, map_mul]
  have hc : chi (wt n₁ q₁ n₂ q₂) θ * (conj (Complex.exp (Complex.I * ((((n₁ : ℝ) + q₁) * θ 0 + ((n₁ : ℝ) - n₁ + q₁) * θ 1 : ℝ) : ℂ))) *
      conj (Complex.exp (Complex.I * ((((n₂ : ℝ) + q₂) * θ 2 + ((n₂ : ℝ) - n₂ + q₂) * θ 3 : ℝ) : ℂ)))) = 1 := by
    rw [chi, ← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    have hs : ∑ i, ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ) =
        ((n₁ : ℂ) + q₁) * θ 0 + q₁ * θ 1 + ((n₂ : ℂ) + q₂) * θ 2 + q₂ * θ 3 := by
      have := Fin.sum_univ_four (fun i : Fin 4 => ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ))
      refine this.trans ?_
      simp [wt]
    rw [hs]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  linear_combination (-(chi ν θ * conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g))) * hc

/- English proof (translation)
Establish `hs : ∀ (a : ℕ) (b : ℤ) (c : ℕ) (d : ℤ), ∑ i, wt a b c d i ^ 2 = (a + b) ^ 2 + b ^ 2 + (c + d) ^ 2 + d ^ 2`. Introduce `a b c d`. Use `(Fin.sum_univ_four (fun i : Fin 4 => wt a b c d i ^ 2)).trans ?_` and prove the remaining obligations. Simplify using `[wt]`. Rewrite `h` using `[hs, hs]`.

Take `⟨a1, a2⟩` from `h₁`. Take `⟨b1, b2⟩` from `h₂`. Establish `a1' : (n : ℤ) ≤ n₁` using `by exact_mod_cast a1`. Establish `b1' : (n' : ℤ) ≤ n₂` using `by exact_mod_cast b1`. Establish `hn : (0 : ℤ) ≤ n` using `by positivity`.

Establish `hn' : (0 : ℤ) ≤ n'` using `by positivity`. Establish `e : ∀ a b : ℤ, 2 * ((a + b) ^ 2 + b ^ 2) = (a + 2 * b) ^ 2 + a ^ 2` using `by intros; ring`. Establish `e1` using `e n₁ q₁`. Establish `e2` using `e n₂ q₂`. Establish `e3` using `e n q`.

Establish `e4` using `e n' q'`. Rewrite `e1` using `[a2]`. Rewrite `e2` using `[b2]`. Establish `s1 : (n : ℤ) ^ 2 ≤ (n₁ : ℤ) ^ 2` using `by gcongr`. Establish `s2 : (n' : ℤ) ^ 2 ≤ (n₂ : ℤ) ^ 2` using `by gcongr`.

Establish `t1 : (n₁ : ℤ) = n` using `(pow_left_inj₀ (by omega) hn two_ne_zero).1 (by linarith)`. Establish `t2 : (n₂ : ℤ) = n'` using `(pow_left_inj₀ (by omega) hn' two_ne_zero).1 (by linarith)`. Establish `u1 : q₁ = q` using `by omega`. Establish `u2 : q₂ = q'` using `by omega`. Simplify using `only [wt, t1, t2, u1, u2]`.
-/
private theorem wt_eq {n : ℕ} {q : ℤ} {n' : ℕ} {q' : ℤ} {n₁ : ℕ} {q₁ : ℤ} {n₂ : ℕ} {q₂ : ℤ} (h₁ : Above n q n₁ q₁)
    (h₂ : Above n' q' n₂ q₂) (h : ∑ i, wt n₁ q₁ n₂ q₂ i ^ 2 ≤ ∑ i, wt n q n' q' i ^ 2) : wt n₁ q₁ n₂ q₂ = wt n q n' q' := by
  have hs : ∀ (a : ℕ) (b : ℤ) (c : ℕ) (d : ℤ), ∑ i, wt a b c d i ^ 2 = (a + b) ^ 2 + b ^ 2 + (c + d) ^ 2 + d ^ 2 := by
    intro a b c d
    refine (Fin.sum_univ_four (fun i : Fin 4 => wt a b c d i ^ 2)).trans ?_
    simp [wt]
  rw [hs, hs] at h
  obtain ⟨a1, a2⟩ := h₁
  obtain ⟨b1, b2⟩ := h₂
  have a1' : (n : ℤ) ≤ n₁ := by exact_mod_cast a1
  have b1' : (n' : ℤ) ≤ n₂ := by exact_mod_cast b1
  have hn : (0 : ℤ) ≤ n := by positivity
  have hn' : (0 : ℤ) ≤ n' := by positivity
  have e : ∀ a b : ℤ, 2 * ((a + b) ^ 2 + b ^ 2) = (a + 2 * b) ^ 2 + a ^ 2 := by intros; ring
  have e1 := e n₁ q₁
  have e2 := e n₂ q₂
  have e3 := e n q
  have e4 := e n' q'
  rw [a2] at e1
  rw [b2] at e2
  have s1 : (n : ℤ) ^ 2 ≤ (n₁ : ℤ) ^ 2 := by gcongr
  have s2 : (n' : ℤ) ^ 2 ≤ (n₂ : ℤ) ^ 2 := by gcongr
  have t1 : (n₁ : ℤ) = n := (pow_left_inj₀ (by omega) hn two_ne_zero).1 (by linarith)
  have t2 : (n₂ : ℤ) = n' := (pow_left_inj₀ (by omega) hn' two_ne_zero).1 (by linarith)
  have u1 : q₁ = q := by omega
  have u2 : q₂ = q' := by omega
  simp only [wt, t1, t2, u1, u2]

/- English proof (translation)
Introduce `μ ψ n q n' q' hμ _ hψ Φ hΦ hfix hL hR h0`. Take `⟨-, hmul, hone, -, hcont, -, -, -, -, -, -, hcpt, -⟩` from `UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4`. Take `⟨J, _, j₀, a, b, ν, hc, hexp, ha0, hb0, hν0, htor, hgood, hgood'⟩` from `hψ.exp`. Use `haveI := hμ.prob`. Use `haveI : μ.IsMulLeftInvariant := ⟨fun k => (hμ.left k).map_eq⟩`.

Establish `int4 : ∀ f : U4 → ℂ, Continuous f → Integrable f μ` using `fun f hf => hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))`. Use `set c : ℂ := ((∫ h, ‖ψ h‖ ^ 2 ∂μ : ℝ) : ℂ)⁻¹ with hcdef`. Establish `hrep : ∀ g, Φ g = ∫ k, c * ψ (k⁻¹ * g) * Φ k ∂μ`. Introduce `g`. Rewrite using `[← integral_mul_left_eq_self _ g, ← hfix g]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Establish `e : (g * k)⁻¹ * g = k⁻¹` using `by group`. Rewrite using `[e, hψ.star, eOf]`. Establish `hsum : ∀ h x, Φ (h * x) = ∑ j, (∫ k, c * a j (k⁻¹ * h) * Φ k ∂μ) * b j x`.

Introduce `h x`. Rewrite using `[hrep]`. Repeatedly rewrite using `[← integral_mul_const]`. Rewrite using `[← integral_finset_sum]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[← mul_assoc, hexp, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Introduce `j _`. Use `(hc j).1` as an intermediate fact.

Conclude with `int4 _ (by fun_prop)`. Establish `hp` using `fun m r => KT.continuous_conj_psi m r m`. Establish `hbd : ∀ l l' : U2, Continuous fun p : U2 × U2 => bd (l * p.1) (l' * p.2)` using `fun l l' => hcont.comp (f := fun p : U2 × U2 => (l * p.1, l' * p.2)) (by fun_prop)`. Establish `hint : ∀ n₁ q₁ n₂ q₂ l l' g, Integrable (fun p : U2 × U2 => conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * Φ (bd (l * p.1) (l' * p.2) * g)) (μK.prod μK)` using `fun n₁ q₁ n₂ q₂ l l' g => int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul (hΦ.comp ((hbd l l').mul continuous_const)))`. Establish `main : ∀ n₁ q₁ n₂ q₂ l l' g, ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * Φ (bd (l * p.1) (l' * p.2) * g) ∂(μK.prod μK) = 0`.

Introduce `n₁ q₁ n₂ q₂ l l' g`. Distinguish the cases in `h₁ : Above n q n₁ q₁`. Distinguish the cases in `h₂ : Above n' q' n₂ q₂`. Repeatedly rewrite using `[← hmul l l', mul_assoc (bd l l'), hsum (bd l l'), Finset.mul_sum]`. Rewrite using `[integral_finset_sum]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[mul_left_comm _ (∫ k, c * a j (k⁻¹ * bd l l') * Φ k ∂μ)]`. Rewrite using `[integral_const_mul]`. Distinguish the cases in `hj : j = j₀`. Rewrite using `[hj, ha0, ← hrep, h0, zero_mul]`.

Rewrite using `[tor2 n₁ q₁ n₂ q₂ (ν j) (b j) (fun θ h => (htor j θ h).2.2), mul_zero]`. Introduce `hν`. Establish `h3` using `hgood j`. Simplify using `only [hν] at h3`. Conclude with `hgood' j hj (hν.trans (wt_eq h₁ h₂ h3))`.

Introduce `j _`. Conclude with `int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul (continuous_const.mul ((hc j).2.comp (hcont.mul continuous_const))))`. Rewrite using `[integral_prod _ (hint n₁ q₁ n₂ q₂ l l' g)]`. Use `(integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)` and prove the remaining obligations. Establish `h3` using `hR n₂ q₂ h₂ l' (bd (l * x) 1 * g)`.

Simplify using `only [← mul_assoc, hmul, one_mul, mul_one] at h3`. Simplify using `only [mul_assoc (conj (KT.psi n₁ q₁ n₁ x))]`. Rewrite using `[integral_const_mul, h3, mul_zero]`. Rewrite using `[integral_prod_symm _ (hint n₁ q₁ n₂ q₂ l l' g)]`. Use `(integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)` and prove the remaining obligations.

Establish `h3` using `hL n₁ q₁ h₁ l (bd 1 (l' * x) * g)`. Simplify using `only [← mul_assoc, hmul, one_mul, mul_one] at h3`. Simplify using `only [mul_comm _ (conj (KT.psi n₂ q₂ n₂ x)), mul_assoc (conj (KT.psi n₂ q₂ n₂ x))]`. Rewrite using `[integral_const_mul, h3, mul_zero]`. Establish `step : ∀ n₂ q₂ l' g, (fun x => ∫ y, conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g) ∂μK) = 0`.

Introduce `n₂ q₂ l' g`. Use `pw2 ?_ fun n₁ q₁ l r => ?_` and prove the remaining obligations. Establish `h3` using `continuous_parametric_integral_of_continuous (μ := μK) (f := fun x y : U2 => conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g)) (((hp _ _).comp continuous_snd).mul (hΦ.comp ((by simpa using hbd 1 l' : Continuous fun p : U2 × U2 => bd p.1 (l' * p.2)).mul continuous_const))) isCompa …`. Simplify `h3` using `only [Measure.restrict_univ]`. Establish `h3` using `main n₁ q₁ n₂ q₂ l l' (bd r 1 * g)`.

Rewrite `h3` using `[integral_prod _ (hint n₁ q₁ n₂ q₂ l l' _)]`. Rewrite using `[← h3]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [← mul_assoc, hmul, mul_one]`. Use function extensionality and compare the values at `g`. Establish `fin : (fun y => Φ (bd 1 y * g)) = 0`.

Use `pw2 (hΦ.comp ((hcont.comp (f := fun y : U2 => ((1 : U2), y)) (by fun_prop)).mul continuous_const)) fun n₂ q₂ l r => ?_` and prove the remaining obligations. Establish `h3` using `congrFun (step n₂ q₂ l (bd 1 r * g)) 1`. Simplify `h3` using `only [← mul_assoc, hmul, mul_one, Pi.zero_apply]`. Simplify `congrFun fin 1` using `[hone]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefInj :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → ∀ Φ : U4 → ℂ, Continuous Φ → RFix μ (eOf μ ψ) Φ →
      LAbove (fun m => bd m 1) n q Φ → LAbove (fun m => bd 1 m) n' q' Φ → (∀ a b, Φ (bd a b) = 0) → Φ = 0 := by
  intro μ ψ n q n' q' hμ _ hψ Φ hΦ hfix hL hR h0
  obtain ⟨-, hmul, hone, -, hcont, -, -, -, -, -, -, hcpt, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  obtain ⟨J, _, j₀, a, b, ν, hc, hexp, ha0, hb0, hν0, htor, hgood, hgood'⟩ := hψ.exp
  haveI := hμ.prob
  haveI : μ.IsMulLeftInvariant := ⟨fun k => (hμ.left k).map_eq⟩
  have int4 : ∀ f : U4 → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  set c : ℂ := ((∫ h, ‖ψ h‖ ^ 2 ∂μ : ℝ) : ℂ)⁻¹ with hcdef
  have hrep : ∀ g, Φ g = ∫ k, c * ψ (k⁻¹ * g) * Φ k ∂μ := by
    intro g
    rw [← integral_mul_left_eq_self _ g, ← hfix g]
    congr 1; funext k
    have e : (g * k)⁻¹ * g = k⁻¹ := by group
    rw [e, hψ.star, eOf]
  have hsum : ∀ h x, Φ (h * x) = ∑ j, (∫ k, c * a j (k⁻¹ * h) * Φ k ∂μ) * b j x := by
    intro h x
    rw [hrep]
    simp_rw [← integral_mul_const]
    rw [← integral_finset_sum]
    · congr 1; funext k
      rw [← mul_assoc, hexp, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro j _
      have := (hc j).1
      exact int4 _ (by fun_prop)
  have hp := fun m r => KT.continuous_conj_psi m r m
  have hbd : ∀ l l' : U2, Continuous fun p : U2 × U2 => bd (l * p.1) (l' * p.2) := fun l l' =>
    hcont.comp (f := fun p : U2 × U2 => (l * p.1, l' * p.2)) (by fun_prop)
  have hint : ∀ n₁ q₁ n₂ q₂ l l' g, Integrable (fun p : U2 × U2 => conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) *
      Φ (bd (l * p.1) (l' * p.2) * g)) (μK.prod μK) := fun n₁ q₁ n₂ q₂ l l' g =>
    int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul
      (hΦ.comp ((hbd l l').mul continuous_const)))
  have main : ∀ n₁ q₁ n₂ q₂ l l' g, ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) *
      Φ (bd (l * p.1) (l' * p.2) * g) ∂(μK.prod μK) = 0 := by
    intro n₁ q₁ n₂ q₂ l l' g
    by_cases h₁ : Above n q n₁ q₁
    · by_cases h₂ : Above n' q' n₂ q₂
      · simp_rw [← hmul l l', mul_assoc (bd l l'), hsum (bd l l'), Finset.mul_sum]
        rw [integral_finset_sum]
        · refine Finset.sum_eq_zero fun j _ => ?_
          simp_rw [mul_left_comm _ (∫ k, c * a j (k⁻¹ * bd l l') * Φ k ∂μ)]
          rw [integral_const_mul]
          by_cases hj : j = j₀
          · rw [hj, ha0, ← hrep, h0, zero_mul]
          · rw [tor2 n₁ q₁ n₂ q₂ (ν j) (b j) (fun θ h => (htor j θ h).2.2), mul_zero]
            intro hν
            have h3 := hgood j
            simp only [hν] at h3
            exact hgood' j hj (hν.trans (wt_eq h₁ h₂ h3))
        · intro j _
          exact int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul
            (continuous_const.mul ((hc j).2.comp (hcont.mul continuous_const))))
      · rw [integral_prod _ (hint n₁ q₁ n₂ q₂ l l' g)]
        refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
        have h3 := hR n₂ q₂ h₂ l' (bd (l * x) 1 * g)
        simp only [← mul_assoc, hmul, one_mul, mul_one] at h3
        simp only [mul_assoc (conj (KT.psi n₁ q₁ n₁ x))]
        rw [integral_const_mul, h3, mul_zero]
    · rw [integral_prod_symm _ (hint n₁ q₁ n₂ q₂ l l' g)]
      refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
      have h3 := hL n₁ q₁ h₁ l (bd 1 (l' * x) * g)
      simp only [← mul_assoc, hmul, one_mul, mul_one] at h3
      simp only [mul_comm _ (conj (KT.psi n₂ q₂ n₂ x)), mul_assoc (conj (KT.psi n₂ q₂ n₂ x))]
      rw [integral_const_mul, h3, mul_zero]
  have step : ∀ n₂ q₂ l' g, (fun x => ∫ y, conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g) ∂μK) = 0 := by
    intro n₂ q₂ l' g
    refine pw2 ?_ fun n₁ q₁ l r => ?_
    · have h3 := continuous_parametric_integral_of_continuous (μ := μK)
        (f := fun x y : U2 => conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g))
        (((hp _ _).comp continuous_snd).mul (hΦ.comp ((by simpa using hbd 1 l' : Continuous fun p : U2 × U2 => bd p.1 (l' * p.2)).mul
          continuous_const))) isCompact_univ
      simpa only [Measure.restrict_univ] using h3
    · have h3 := main n₁ q₁ n₂ q₂ l l' (bd r 1 * g)
      rw [integral_prod _ (hint n₁ q₁ n₂ q₂ l l' _)] at h3
      rw [← h3]
      congr 1; funext x
      rw [← integral_const_mul]
      congr 1; funext y
      simp only [← mul_assoc, hmul, mul_one]
  funext g
  have fin : (fun y => Φ (bd 1 y * g)) = 0 := by
    refine pw2 (hΦ.comp ((hcont.comp (f := fun y : U2 => ((1 : U2), y)) (by fun_prop)).mul continuous_const)) fun n₂ q₂ l r => ?_
    have h3 := congrFun (step n₂ q₂ l (bd 1 r * g)) 1
    simpa only [← mul_assoc, hmul, mul_one, Pi.zero_apply] using h3
  simpa [hone] using congrFun fin 1
