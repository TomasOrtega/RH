import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.UnipotentTruncatedIntegral

open UpperTheory.Esk

/- English proof (translation)
Simplify using `[pt]`.
-/
theorem pt_im (x y : ℝ) (hy : y ≠ 0) : (pt x y hy).1.im = y := by simp [pt]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pt_val (x y : ℝ) (hy : y ≠ 0) : (pt x y hy).1 = (y : ℂ) * ((x : ℂ) + Complex.I) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[pt]`. Clear denominators, using `[z.2]` for the nonvanishing conditions. Simplify using `[pt]`.
-/
theorem pt_eta (z : P) : pt (z.1.re / z.1.im) z.1.im z.2 = z := by
  apply Subtype.ext
  apply Complex.ext
  · simp [pt]; field_simp [z.2]
  · simp [pt]

/- English proof (translation)
Substitute `hx` using the available equality. Substitute `hy` using the available equality. Both sides reduce to the same expression.
-/
theorem pt_congr {x x' y y' : ℝ} (hx : x = x') (hy : y = y') (h : y ≠ 0) (h' : y' ≠ 0) : pt x y h = pt x' y' h' := by
  subst hx; subst hy; rfl

/- English proof (translation)
Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[pt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pt_normsq (x y : ℝ) (hy : y ≠ 0) : ‖(pt x y hy).1‖ ^ 2 = y ^ 2 * (1 + x ^ 2) := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [pt]; ring

/- English proof (translation)
Introduce `h`. Apply `g.det_ne_zero` to reduce the goal to its premises. Rewrite using `[det_eq, h, h01]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lower_right_ne_zero_of_upper_right_zero {g : GL (Fin 2) ℝ} (h01 : g 0 1 = 0) : g 1 1 ≠ 0 := by
  intro h; apply g.det_ne_zero; rw [det_eq, h, h01]; ring

/- English proof (translation)
Establish `h11` using `lower_right_ne_zero_of_upper_right_zero h01`. Rewrite using `[coe_smul]`. Simplify using `only [num, den, h01, h10]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem diag_smul {g : GL (Fin 2) ℝ} (h01 : g 0 1 = 0) (h10 : g 1 0 = 0) (z : P) :
    (g • z).1 = ((g 0 0 / g 1 1 : ℝ) : ℂ) * z.1 := by
  have h11 := lower_right_ne_zero_of_upper_right_zero h01
  rw [coe_smul]; simp only [num, den, h01, h10]; push_cast
  field_simp
  ring

/- English proof (translation)
Rewrite using `[diag_smul h01 h10, Complex.im_ofReal_mul]`.
-/
theorem diag_im {g : GL (Fin 2) ℝ} (h01 : g 0 1 = 0) (h10 : g 1 0 = 0) (z : P) :
    (g • z).1.im = g 0 0 / g 1 1 * z.1.im := by
  rw [diag_smul h01 h10, Complex.im_ofReal_mul]

/- English proof (translation)
Take `⟨z, hz⟩` from `QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin 2) F)) γ`. Take `⟨z1, z2, _⟩` from `center_entries z.2`. Rewrite using `[hz]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, h01, h10, z1, z2]`.
-/
theorem out_diag {F : Type} [Field F] (γ : GL (Fin 2) F) (h01 : γ 0 1 = 0) (h10 : γ 1 0 = 0) :
    ((γ : PG F).out) 0 1 = 0 ∧ ((γ : PG F).out) 1 0 = 0 := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin 2) F)) γ
  obtain ⟨z1, z2, _⟩ := center_entries z.2
  rw [hz]
  simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, z1, z2]

/- English proof (translation)
Rewrite using `[inv_mul_le_iff₀ (mul_pos hPy hQ), div_div, div_le_iff₀ (mul_pos hT hQ), le_div_iff₀ hh1]`. Establish `e : Py * Q * T = Py * (T * Q)` using `by ring`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b⟩; exact ⟨by linarith, a⟩`. Introduce and unpack `⟨a, b⟩; exact ⟨b, by linarith⟩`.
-/
theorem cond_iff (Py Q h1 h2 T : ℝ) (hPy : 0 < Py) (hQ : 0 < Q) (hh1 : 0 < h1) (hT : 0 < T) :
    (Py * h1 ≤ T ∧ (Py * Q)⁻¹ * h2 ≤ T) ↔ (h2 / T / Q ≤ Py ∧ Py ≤ T / h1) := by
  rw [inv_mul_le_iff₀ (mul_pos hPy hQ), div_div, div_le_iff₀ (mul_pos hT hQ), le_div_iff₀ hh1]
  have e : Py * Q * T = Py * (T * Q) := by ring
  constructor
  · rintro ⟨a, b⟩; exact ⟨by linarith, a⟩
  · rintro ⟨a, b⟩; exact ⟨b, by linarith⟩

/- English proof (translation)
Rewrite using `[pt_normsq, ← sq_abs y]`. Establish `: |y| ≠ 0` using `abs_ne_zero.2 hy`. Establish `: (1 + x ^ 2) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem abs_im_div_norm_sq_half_plane_point (x y : ℝ) (hy : y ≠ 0) : |y| / ‖(pt x y hy).1‖ ^ 2 = (|y| * (1 + x ^ 2))⁻¹ := by
  rw [pt_normsq, ← sq_abs y]
  have : |y| ≠ 0 := abs_ne_zero.2 hy
  have : (1 + x ^ 2) ≠ 0 := by positivity
  field_simp

/- English proof (translation)
Establish `: ∏ v, |t * y v| = t ^ Fintype.card I * ∏ v, |y v|`. Simplify using `only [abs_mul, Finset.prod_mul_distrib, Finset.prod_const, abs_of_pos ht, Finset.card_univ]`. Rewrite using `[this, Real.mul_rpow (by positivity) (Finset.prod_nonneg fun v _ => abs_nonneg _), Real.pow_rpow_inv_natCast ht.le Fintype.card_ne_zero]`.
-/
theorem prod_scale {I : Type} [Fintype I] [Nonempty I] (y : I → ℝ) (t : ℝ) (ht : 0 < t) :
    (∏ v, |t * y v|) ^ ((Fintype.card I : ℝ)⁻¹) = t * (∏ v, |y v|) ^ ((Fintype.card I : ℝ)⁻¹) := by
  have : ∏ v, |t * y v| = t ^ Fintype.card I * ∏ v, |y v| := by
    simp only [abs_mul, Finset.prod_mul_distrib, Finset.prod_const, abs_of_pos ht, Finset.card_univ]
  rw [this, Real.mul_rpow (by positivity) (Finset.prod_nonneg fun v _ => abs_nonneg _),
    Real.pow_rpow_inv_natCast ht.le Fintype.card_ne_zero]

end UpperTheory.Esk.UnipotentTruncatedIntegral

open UpperTheory.Esk.UnipotentTruncatedIntegral in
/- English proof (translation)
Introduce `_ _ hB5b hC1 hE0a hE0c hE0d hEcut hFcen hF6c`. Introduce `F I Gf ι _ _ _ _ D k a hH T hT γ ω h01 h10 β hβ hint`. Take `⟨hcount, _, hpres, _, _, _, _, _⟩` from `hE0a F I Gf D hH.ax`. Take `⟨_, hinv, hmeas, _, hsupp, htr⟩` from `hE0c F I Gf ι D k a hH`. Take `⟨_, e2, e3, _, _, _, _, e8, _, _, _⟩` from `hE0d F I Gf D hH.ax`.

Use `haveI := hH.ax.two`. Take `⟨g, hg⟩ : ∃ g, (γ : PG F).out = g` from `⟨_, rfl⟩`. Establish `hgq : (g : PG F) = (γ : PG F)` using `by rw [← hg]; exact QuotientGroup.out_eq' _`. Take `⟨g01, g10⟩` from `out_diag γ h01 h10`. Rewrite `g01`, `g10` using `[hg]`.

Establish `hkk : ∀ z : D.Xs, D.kk k a (γ : PG F) (ω, z) = D.Te a g (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v g • z v) * j1 (k v) (D.r v g) (z v))`. Introduce `z`. Simplify using `only [Dat.kk, Dat.kt, qq, Dat.J, Dat.act, Finset.prod_mul_distrib, hg]`. Distinguish the cases in `hc : D.Te a g (D.rep ω) = 0`. Establish `h0 : ∀ z, β z • (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z) = 0`.

Introduce `z`. Simplify using `[Set.indicator_apply, hkk, hc]`. Simplify using `[h0]`. Take `⟨i, hi⟩` from `hsupp (γ : PG F) ω (by rw [hg]; exact hc)`. Take `⟨htr0, htr1⟩` from `htr (γ : PG F) ω i hi`.

Rewrite `htr0`, `htr1` using `[hg]`. Establish `hne : g 0 0 ≠ g 1 1`. Introduce `h`. Apply `htr1` to reduce the goal to its premises. Rewrite using `[Matrix.trace_fin_two, Matrix.det_fin_two]`.

Rewrite using `[g01, g10, h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hφ : ∀ v, ∃ φ : ℝ → ℂ, Continuous φ ∧ (∀ x y hy, q1 (k v) (pt x y hy) (D.r v g • pt x y hy) * j1 (k v) (D.r v g) (pt x y hy) = φ x) ∧ Integrable φ ∧ Integrable (fun x => (Real.log (1 + x ^ 2) : ℂ) * φ x) ∧ ∫ x, φ x = 0 ∧ (φ = 0 ∨ ∀ x, φ x ≠ 0)` using `fun v => hB5b (k v) (hH.four v) (D.r v g) (show D.σ v (g 0 1) = 0 by rw [g01, map_zero]) (show D.σ v (g 1 0) = 0 by rw [g10, map_zero]) (show D.σ v (g 0 0) ≠ D.σ v (g 1 1) from fun h => hne ((D.σ v).injective h))`. Use `choose φ hφc hφe hφi hφl hφ0 hφn using hφ`. Establish `hfac : ∀ v (w : P), q1 (k v) w (D.r v g • w) * j1 (k v) (D.r v g) w = φ v (w.1.re / w.1.im)`.

Introduce `v w`. Use `hφe v (w.1.re / w.1.im) w.1.im w.2` as an intermediate fact. Rewrite `this` using `[pt_eta]`. Then use the resulting hypothesis. Distinguish the cases in `hz : ∃ v, φ v = 0`. Take `⟨v, hv⟩` from `hz`.

Establish `h0 : ∀ z, β z • (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z) = 0`. Introduce `z`. Establish `hp : ∏ w, (q1 (k w) (z w) (D.r w g • z w) * j1 (k w) (D.r w g) (z w)) = 0` using `Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hfac, hv]; rfl)`. Simplify using `[hkk, hp]`. Simplify using `[h0]`.

Use `push_neg at hz`. Establish `hφn' : ∀ v x, φ v x ≠ 0` using `fun v => (hφn v).resolve_left (hz v)`. Establish `h1pos : 0 < D.hf ![0, 1] (D.rep ω)` using `hH.ax.pos _ (by simp) _`. Establish `h2pos : 0 < D.hf ![1, 0] (D.rep ω)` using `hH.ax.pos _ (by simp) _`. Establish `h12 : D.hf ![0, 1] (D.rep ω) * D.hf ![1, 0] (D.rep ω) ≤ 1`.

Simplify using `using hH.ax.prod ![0, 1] ![1, 0] (by simp) (D.rep ω)`. Establish `hH01 : ∀ z : D.Xs, D.HtY ![0, 1] (ω, z) = (∏ v, |(z v).1.im|) * D.hf ![0, 1] (D.rep ω)`. Introduce `z`. Simplify using `[Dat.HtY, Dat.Ht]`. Establish `hH10 : ∀ z : D.Xs, D.HtY ![1, 0] (ω, z) = (∏ v, |(z v).1.im| / ‖(z v).1‖ ^ 2) * D.hf ![1, 0] (D.rep ω)`.

Introduce `z`. Simplify using `[Dat.HtY, Dat.Ht]`. Establish `hLam : ∀ z : D.Xs, (ω, z) ∈ D.LamF T (γ : PG F) ↔ D.HtY ![0, 1] (ω, z) ≤ T ∧ D.HtY ![1, 0] (ω, z) ≤ T`. Introduce `z`. Simplify using `only [Dat.LamF, Set.mem_setOf_eq, Fix, hg]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨h _ (by simp) ⟨g 1 1, ?_⟩, h _ (by simp) ⟨g 0 0, ?_⟩⟩` and prove the remaining obligations. Apply the tactic sequence `ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, g01, g10]`. Apply the tactic sequence `ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, g01, g10]`.

Introduce and unpack `⟨h1, h2⟩ s hs ⟨c, hc⟩`. Establish `e0 : s 0 * g 0 0 = c * s 0`. Simplify `congrFun hc 0` using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two, g01, g10]`. Establish `e1 : s 1 * g 1 1 = c * s 1`. Simplify `congrFun hc 1` using `[Matrix.vecMul, dotProduct, Fin.sum_univ_two, g01, g10]`.

Distinguish the cases in `hs0 : s 0 = 0`. Establish `hs1 : s 1 ≠ 0`. Apply the tactic sequence `intro h; apply hs; ext j; fin_cases j <;> simp [hs0, h]`. Apply the tactic sequence `have : s = s 1 • ![0, 1] := by ext j; fin_cases j <;> simp [hs0]`. Rewrite using `[this, e3 _ (by simp) _ hs1]; exact h1`.

Establish `hs1 : s 1 = 0`. Assume the negation of the conclusion as `h`. Apply `hne` to reduce the goal to its premises. Establish `a0 : g 0 0 = c` using `mul_left_cancel₀ hs0 (by rw [e0, mul_comm])`. Establish `a1 : g 1 1 = c` using `mul_left_cancel₀ h (by rw [e1, mul_comm])`.

Rewrite using `[a0, a1]`. Apply the tactic sequence `have : s = s 0 • ![1, 0] := by ext j; fin_cases j <;> simp [hs1]`. Rewrite using `[this, e3 _ (by simp) _ hs0]; exact h2`. Establish `hstab : ∀ δ : PG F, δ ∈ MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om) → δ * (γ : PG F) * δ⁻¹ = γ ∧ δ • ω = ω`. Introduce `δ hδ`.

Rewrite `hδ` using `[MulAction.mem_stabilizer_iff]`. Establish `hδ1 : δ • (show D.Cj from (γ : PG F)) = (show D.Cj from (γ : PG F))` using `congrArg Prod.fst hδ`. Use `⟨?_, congrArg Prod.snd hδ⟩` and prove the remaining obligations. Use `D.smulC δ (γ : PG F)` as an intermediate fact. Rewrite `this` using `[hδ1]`.

Conclude with `this.symm`. Establish `hdiag : ∀ δ : PG F, δ ∈ MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om) → δ.out 0 1 = 0 ∧ δ.out 1 0 = 0 ∧ ∏ v, |D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1)| = 1`. Introduce `δ hδ`. Take `⟨h3, h2⟩` from `hstab δ hδ`. Establish `hcomm` using `hFcen F g δ.out htr0 (by rw [QuotientGroup.out_eq', hgq]; exact h3)`.

Establish `a01` using `congrArg (fun m : GL (Fin 2) F => m 0 1) hcomm`. Establish `a10` using `congrArg (fun m : GL (Fin 2) F => m 1 0) hcomm`. Simplify using `only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at a01 a10`. Simplify using `only [g01, g10, mul_zero, zero_mul, add_zero, zero_add] at a01 a10`. Establish `d01 : δ.out 0 1 = 0`.

Assume the negation of the conclusion as `h; exact hne (mul_left_cancel₀ h (by linear_combination -a01))`. Establish `d10 : δ.out 1 0 = 0`. Assume the negation of the conclusion as `h; exact hne (mul_left_cancel₀ h (by linear_combination a10))`. Use `⟨d01, d10, ?_⟩` and prove the remaining obligations. Establish `hd11 : δ.out 1 1 ≠ 0`.

Introduce `h`. Apply `δ.out.det_ne_zero` to reduce the goal to its premises. Rewrite using `[Matrix.det_fin_two, h, d01]`. Expand and normalize the polynomial expressions, which then agree. Establish `hvec : ![0, 1] ᵥ* δ.out.val = δ.out 1 1 • ![0, 1]`.

Apply the tactic sequence `ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, d10]`. Establish `hr : ∀ v (w : P), (D.r v δ.out • w).1.im = D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) * w.1.im` using `fun v w => diag_im (show D.σ v (δ.out 0 1) = 0 by rw [d01, map_zero]) (show D.σ v (δ.out 1 0) = 0 by rw [d10, map_zero]) w`. Establish `hpair : δ • ((ω, fun _ => iP) : D.Y) = ((ω, D.act δ.out fun _ => iP) : D.Y)`. Use `Prod.ext h2 ?_` and prove the remaining obligations. Use `D.mk_smulX δ.out (fun _ => iP)` as an intermediate fact.

Rewrite `this` using `[QuotientGroup.out_eq']`. Conclude with `this`. Establish `key` using `e2 ![0, 1] (by simp) δ.out ((ω, fun _ => iP) : D.Y)`. Rewrite `key` using `[hvec, e3 _ (by simp) _ hd11, QuotientGroup.out_eq', hpair]`. Establish `key2` using `(hH01 (D.act δ.out fun _ => iP)).symm.trans (key.trans (hH01 (fun _ => iP)))`.

Simplify using `only [Dat.act, hr] at key2`. Simplify `key2` using `[iP, h1pos.ne']`. Take `⟨β0, hβ0⟩` from `(hEcut F I Gf D hH.ax).2 ω (MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)) (fun δ hδ => MulAction.mem_stabilizer_iff.2 (hstab δ hδ).2)`. Take `⟨N, hNdef⟩ : ∃ N : D.Xs → ℝ, ∀ z, N z = (∏ v, |(z v).1.im|) ^ ((Fintype.card I : ℝ)⁻¹)` from `⟨_, fun _ => rfl⟩`. Establish `hNpos : ∀ z, 0 < N z` using `fun z => by`.

Rewrite using `[hNdef]`. Conclude with `Real.rpow_pos_of_pos (Finset.prod_pos fun v _ => abs_pos.2 (z v).2) _`. Take `⟨p, hpdef⟩ : ∃ p : D.Xs → D.Xs, ∀ z v, p z v = pt 0 ((z v).1.im / N z) (div_ne_zero (z v).2 (hNpos z).ne')` from `⟨fun z v => pt 0 ((z v).1.im / N z) (div_ne_zero (z v).2 (hNpos z).ne'), fun _ _ => rfl⟩`. Establish `hNc : Continuous N`. Establish `: N = fun z => (∏ v, |(z v).1.im|) ^ ((Fintype.card I : ℝ)⁻¹)` using `funext hNdef`.

Rewrite using `[this]`. Apply `Continuous.rpow_const` to reduce the goal to its premises. Conclude with `continuous_finset_prod _ fun w _ => (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply w))).abs`. Introduce `z`. Use `left`.

Conclude with `(Finset.prod_pos fun w _ => abs_pos.2 (z w).2).ne'`. Establish `hpc : Continuous p`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `v`. Establish `: (fun z => p z v) = fun z => pt 0 ((z v).1.im / N z) (div_ne_zero (z v).2 (hNpos z).ne')` using `funext fun z => hpdef z v`.

Rewrite using `[this]`. Apply `continuous_induced_rng.2` to reduce the goal to its premises. Use `show Continuous fun z : D.Xs => (((z v).1.im / N z : ℝ) : ℂ) * (((0 : ℝ) : ℂ) + Complex.I)`. Conclude with `(Complex.continuous_ofReal.comp ((Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply v))).div hNc fun z => (hNpos z).ne')).mul continuous_const`. Establish `hpeq : ∀ δ ∈ MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om), ∀ z : D.Xs, p (δ • z) = δ • p z`.

Introduce `δ hδ z`. Take `⟨d01, d10, dprod⟩` from `hdiag δ hδ`. Establish `hsm : ∀ w : D.Xs, (δ • w : D.Xs) = D.act δ.out w`. Introduce `w`. Use `D.mk_smulX δ.out w` as an intermediate fact.

Rewrite `this` using `[QuotientGroup.out_eq']`. Conclude with `this`. Establish `h01' : ∀ v, (D.r v δ.out) 0 1 = 0` using `fun v => show D.σ v (δ.out 0 1) = 0 by rw [d01, map_zero]`. Establish `h10' : ∀ v, (D.r v δ.out) 1 0 = 0` using `fun v => show D.σ v (δ.out 1 0) = 0 by rw [d10, map_zero]`. Establish `hr : ∀ v (w : P), (D.r v δ.out • w).1.im = D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) * w.1.im` using `fun v w => diag_im (h01' v) (h10' v) w`.

Establish `hN : N (D.act δ.out z) = N z` using `by erw [hNdef, hNdef]; congr 1`. Simplify using `only [Dat.act, hr, abs_mul, Finset.prod_mul_distrib, dprod, one_mul]`. Rewrite using `[hsm, hsm]`. Use function extensionality and compare the values at `v`. Use `erw [hpdef]`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `e1 : ((D.act δ.out z) v).1.im = D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) * (z v).1.im` using `hr v (z v)`. Establish `e2 : ((D.act δ.out (p z)) v).1 = ((D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) : ℝ) : ℂ) * (p z v).1` using `diag_smul (h01' v) (h10' v) (p z v)`. Rewrite using `[pt_val, e2, e1, hN]`. Use `erw [hpdef]`.

Rewrite using `[pt_val]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hβ' : IsCut (MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)) (fun z : D.Xs => β0 (p z))`. Use `⟨hβ0.meas.comp hpc.measurable, fun z => hβ0.nonneg _, fun z => ?_⟩` and prove the remaining obligations.

Establish `: (fun δ : MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om) => β0 (p (δ • z))) = fun δ => β0 (δ • p z)` using `funext fun δ => congrArg β0 (hpeq δ.1 δ.2 z)`. Rewrite using `[this]`. Conclude with `hβ0.sum (p z)`. Take `⟨u, hudef⟩ : ∃ u : D.Xs → ℂ, u = fun z => (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z)` from `⟨_, rfl⟩`. It suffices to establish `hmain : ∫ z, β z • u z = 0 by subst hudef; exact hmain`.

Establish `hint2 : Integrable (fun z => β z • u z)` using `by subst hudef; exact hint`. Establish `hum : Measurable u`. Substitute `hudef` using the available equality. Conclude with `((hmeas _).indicator (e8 T _).1).comp measurable_prodMk_left`. Establish `huinv : ∀ (δ : MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)) (z : D.Xs), u (δ • z) = u z`.

Introduce `δ z`. Take `⟨h3, h2⟩` from `hstab δ.1 δ.2`. Establish `hy : ((ω, (δ.1 • z : D.Xs)) : D.Y) = δ.1 • ((ω, z) : D.Y)` using `Prod.ext h2.symm rfl`. Establish `hm` using `(e8 T (γ : PG F)).2 δ.1 (ω, z)`. Rewrite `hm` using `[h3]`.

Establish `hk` using `hinv δ.1 (γ : PG F) (ω, z)`. Rewrite `hk` using `[h3]`. Substitute `hudef` using the available equality. Use `show Set.indicator _ _ ((ω, (δ.1 • z : D.Xs)) : D.Y) = Set.indicator _ _ ((ω, z) : D.Y)`. Rewrite using `[hy]`.

Distinguish the cases in `h : ((ω, z) : D.Y) ∈ D.LamF T (γ : PG F)`. Rewrite using `[Set.indicator_of_mem (hm.2 h), Set.indicator_of_mem h, hk]`. Rewrite using `[Set.indicator_of_notMem (mt hm.1 h), Set.indicator_of_notMem h]`. Use `haveI := hcount`. Establish `hC` using `(hC1 (MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)) D.Xs volume (fun δ => hpres δ.1) β (fun z => β0 (p z)) hβ hβ').2 u hum huinv hint2`.

Rewrite using `[hC.2]`. Establish `hu' : ∀ (x y : I → ℝ) (hy : ∀ v, y v ≠ 0), (D.Te a g (D.rep ω))⁻¹ * u (fun v => pt (x v) (y v) (hy v)) = if D.hf ![1, 0] (D.rep ω) / T / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |y v| ∧ ∏ v, |y v| ≤ T / D.hf ![0, 1] (D.rep ω) then ∏ v, φ v (x v) else 0`. Introduce `x y hy`. Establish `hPy : 0 < ∏ v, |y v|` using `Finset.prod_pos fun v _ => abs_pos.2 (hy v)`. Establish `hQ : 0 < ∏ v, (1 + x v ^ 2)` using `Finset.prod_pos fun v _ => by positivity`.

Establish `hcond : ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) ∈ D.LamF T (γ : PG F) ↔ (D.hf ![1, 0] (D.rep ω) / T / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |y v| ∧ ∏ v, |y v| ≤ T / D.hf ![0, 1] (D.rep ω))`. Use `(hLam (fun v => pt (x v) (y v) (hy v))).trans ?_` and prove the remaining obligations. Use `erw [hH01, hH10]`. Simplify using `only [pt_im, abs_im_div_norm_sq_half_plane_point, Finset.prod_inv_distrib, Finset.prod_mul_distrib]`. Conclude with `cond_iff _ _ _ _ _ hPy hQ h1pos (by linarith)`.

Substitute `hudef` using the available equality. Use `show _ * Set.indicator _ _ ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) = _`. Rewrite using `[Set.indicator_apply]`. Distinguish the cases in `hm : ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) ∈ D.LamF T (γ : PG F)`. Rewrite using `[if_pos hm, if_pos (hcond.1 hm)] erw [hkk]`.

Rewrite using `[inv_mul_cancel_left₀ hc]`. Conclude with `Finset.prod_congr rfl fun v _ => hφe v _ _ _`. Rewrite using `[if_neg hm, if_neg (mt hcond.2 hm), mul_zero]`. Establish `hA : 0 < D.hf ![1, 0] (D.rep ω) / T` using `div_pos h2pos (by linarith)`. Establish `hAB : D.hf ![1, 0] (D.rep ω) / T < T / D.hf ![0, 1] (D.rep ω)`.

Rewrite using `[div_lt_div_iff₀ (by linarith) h1pos]; nlinarith`. Establish `hinvp : ∀ (x x' y : I → ℝ) (hy : ∀ v, y v ≠ 0) (t : ℝ) (ht : 0 < t), β0 (p fun v => pt (x v) (y v) (hy v)) = β0 (p fun v => pt (x' v) (t * y v) (mul_ne_zero ht.ne' (hy v)))`. Introduce `x x' y hy t ht`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Use `erw [hpdef, hpdef]`. Apply `pt_congr rfl` to reduce the goal to its premises. Use `erw [hNdef, hNdef]`. Simplify using `only [pt_im]`. Rewrite using `[prod_scale y t ht, mul_div_mul_left _ _ ht.ne']`.

Establish `hint3 : Integrable (fun z : X I => β0 (p z) • ((D.Te a g (D.rep ω))⁻¹ * u z))`. Use `(hC.1.const_mul (D.Te a g (D.rep ω))⁻¹).congr (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Conclude with `mul_smul_comm _ _ _`. Establish `hF` using `hF6c I φ (fun v => ⟨hφc v, hφi v, hφl v, hφ0 v, hφn' v⟩) (fun z => β0 (p z)) (hβ0.meas.comp hpc.measurable) (fun z => hβ0.nonneg _) hinvp _ _ hA hAB (fun z => (D.Te a g (D.rep ω))⁻¹ * u z) hu' hint3`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Rewrite using `[mul_smul_comm, mul_inv_cancel_left₀ hc]`. Use `_ = 0 := by rw [hF, mul_zero]`.
-/
theorem UpperTheory.Esk.diagonal_truncated_integral_zero : UpperTheory.Esk.B1a → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.DiagonalIntegrandVanishes → UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Ecut → UpperTheory.Esk.Fcen → UpperTheory.Esk.ConstantTermVanishingAlt → UpperTheory.Esk.DiagonalTruncatedIntegralZero := by
  intro _ _ hB5b hC1 hE0a hE0c hE0d hEcut hFcen hF6c
  intro F I Gf ι _ _ _ _ D k a hH T hT γ ω h01 h10 β hβ hint
  obtain ⟨hcount, _, hpres, _, _, _, _, _⟩ := hE0a F I Gf D hH.ax
  obtain ⟨_, hinv, hmeas, _, hsupp, htr⟩ := hE0c F I Gf ι D k a hH
  obtain ⟨_, e2, e3, _, _, _, _, e8, _, _, _⟩ := hE0d F I Gf D hH.ax
  haveI := hH.ax.two
  obtain ⟨g, hg⟩ : ∃ g, (γ : PG F).out = g := ⟨_, rfl⟩
  have hgq : (g : PG F) = (γ : PG F) := by rw [← hg]; exact QuotientGroup.out_eq' _
  obtain ⟨g01, g10⟩ := out_diag γ h01 h10
  rw [hg] at g01 g10
  have hkk : ∀ z : D.Xs, D.kk k a (γ : PG F) (ω, z) =
      D.Te a g (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v g • z v) * j1 (k v) (D.r v g) (z v)) := by
    intro z
    simp only [Dat.kk, Dat.kt, qq, Dat.J, Dat.act, Finset.prod_mul_distrib, hg]
  by_cases hc : D.Te a g (D.rep ω) = 0
  · have h0 : ∀ z, β z • (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z) = 0 := by
      intro z; simp [Set.indicator_apply, hkk, hc]
    simp [h0]
  obtain ⟨i, hi⟩ := hsupp (γ : PG F) ω (by rw [hg]; exact hc)
  obtain ⟨htr0, htr1⟩ := htr (γ : PG F) ω i hi
  rw [hg] at htr0 htr1
  have hne : g 0 0 ≠ g 1 1 := by
    intro h; apply htr1
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    rw [g01, g10, h]; ring
  have hφ : ∀ v, ∃ φ : ℝ → ℂ, Continuous φ ∧
      (∀ x y hy, q1 (k v) (pt x y hy) (D.r v g • pt x y hy) * j1 (k v) (D.r v g) (pt x y hy) = φ x) ∧
      Integrable φ ∧ Integrable (fun x => (Real.log (1 + x ^ 2) : ℂ) * φ x) ∧ ∫ x, φ x = 0 ∧ (φ = 0 ∨ ∀ x, φ x ≠ 0) :=
    fun v => hB5b (k v) (hH.four v) (D.r v g) (show D.σ v (g 0 1) = 0 by rw [g01, map_zero])
      (show D.σ v (g 1 0) = 0 by rw [g10, map_zero])
      (show D.σ v (g 0 0) ≠ D.σ v (g 1 1) from fun h => hne ((D.σ v).injective h))
  choose φ hφc hφe hφi hφl hφ0 hφn using hφ
  have hfac : ∀ v (w : P), q1 (k v) w (D.r v g • w) * j1 (k v) (D.r v g) w = φ v (w.1.re / w.1.im) := by
    intro v w
    have := hφe v (w.1.re / w.1.im) w.1.im w.2
    rwa [pt_eta] at this
  by_cases hz : ∃ v, φ v = 0
  · obtain ⟨v, hv⟩ := hz
    have h0 : ∀ z, β z • (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z) = 0 := by
      intro z
      have hp : ∏ w, (q1 (k w) (z w) (D.r w g • z w) * j1 (k w) (D.r w g) (z w)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hfac, hv]; rfl)
      simp [hkk, hp]
    simp [h0]
  push_neg at hz
  have hφn' : ∀ v x, φ v x ≠ 0 := fun v => (hφn v).resolve_left (hz v)

  have h1pos : 0 < D.hf ![0, 1] (D.rep ω) := hH.ax.pos _ (by simp) _
  have h2pos : 0 < D.hf ![1, 0] (D.rep ω) := hH.ax.pos _ (by simp) _
  have h12 : D.hf ![0, 1] (D.rep ω) * D.hf ![1, 0] (D.rep ω) ≤ 1 := by
    simpa using hH.ax.prod ![0, 1] ![1, 0] (by simp) (D.rep ω)
  have hH01 : ∀ z : D.Xs, D.HtY ![0, 1] (ω, z) = (∏ v, |(z v).1.im|) * D.hf ![0, 1] (D.rep ω) := by
    intro z; simp [Dat.HtY, Dat.Ht]
  have hH10 : ∀ z : D.Xs, D.HtY ![1, 0] (ω, z) = (∏ v, |(z v).1.im| / ‖(z v).1‖ ^ 2) * D.hf ![1, 0] (D.rep ω) := by
    intro z; simp [Dat.HtY, Dat.Ht]
  have hLam : ∀ z : D.Xs, (ω, z) ∈ D.LamF T (γ : PG F) ↔ D.HtY ![0, 1] (ω, z) ≤ T ∧ D.HtY ![1, 0] (ω, z) ≤ T := by
    intro z
    simp only [Dat.LamF, Set.mem_setOf_eq, Fix, hg]
    constructor
    · intro h
      refine ⟨h _ (by simp) ⟨g 1 1, ?_⟩, h _ (by simp) ⟨g 0 0, ?_⟩⟩
      · ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, g01, g10]
      · ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, g01, g10]
    · rintro ⟨h1, h2⟩ s hs ⟨c, hc⟩
      have e0 : s 0 * g 0 0 = c * s 0 := by
        simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two, g01, g10] using congrFun hc 0
      have e1 : s 1 * g 1 1 = c * s 1 := by
        simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two, g01, g10] using congrFun hc 1
      by_cases hs0 : s 0 = 0
      · have hs1 : s 1 ≠ 0 := by
          intro h; apply hs; ext j; fin_cases j <;> simp [hs0, h]
        have : s = s 1 • ![0, 1] := by ext j; fin_cases j <;> simp [hs0]
        rw [this, e3 _ (by simp) _ hs1]; exact h1
      · have hs1 : s 1 = 0 := by
          by_contra h
          apply hne
          have a0 : g 0 0 = c := mul_left_cancel₀ hs0 (by rw [e0, mul_comm])
          have a1 : g 1 1 = c := mul_left_cancel₀ h (by rw [e1, mul_comm])
          rw [a0, a1]
        have : s = s 0 • ![1, 0] := by ext j; fin_cases j <;> simp [hs1]
        rw [this, e3 _ (by simp) _ hs0]; exact h2

  have hstab : ∀ δ : PG F, δ ∈ MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om) →
      δ * (γ : PG F) * δ⁻¹ = γ ∧ δ • ω = ω := by
    intro δ hδ
    rw [MulAction.mem_stabilizer_iff] at hδ
    have hδ1 : δ • (show D.Cj from (γ : PG F)) = (show D.Cj from (γ : PG F)) := congrArg Prod.fst hδ
    refine ⟨?_, congrArg Prod.snd hδ⟩
    have := D.smulC δ (γ : PG F)
    rw [hδ1] at this
    exact this.symm
  have hdiag : ∀ δ : PG F, δ ∈ MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om) →
      δ.out 0 1 = 0 ∧ δ.out 1 0 = 0 ∧ ∏ v, |D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1)| = 1 := by
    intro δ hδ
    obtain ⟨h3, h2⟩ := hstab δ hδ
    have hcomm := hFcen F g δ.out htr0 (by rw [QuotientGroup.out_eq', hgq]; exact h3)
    have a01 := congrArg (fun m : GL (Fin 2) F => m 0 1) hcomm
    have a10 := congrArg (fun m : GL (Fin 2) F => m 1 0) hcomm
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at a01 a10
    simp only [g01, g10, mul_zero, zero_mul, add_zero, zero_add] at a01 a10
    have d01 : δ.out 0 1 = 0 := by
      by_contra h; exact hne (mul_left_cancel₀ h (by linear_combination -a01))
    have d10 : δ.out 1 0 = 0 := by
      by_contra h; exact hne (mul_left_cancel₀ h (by linear_combination a10))
    refine ⟨d01, d10, ?_⟩
    have hd11 : δ.out 1 1 ≠ 0 := by
      intro h; apply δ.out.det_ne_zero; rw [Matrix.det_fin_two, h, d01]; ring
    have hvec : ![0, 1] ᵥ* δ.out.val = δ.out 1 1 • ![0, 1] := by
      ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, d10]
    have hr : ∀ v (w : P), (D.r v δ.out • w).1.im = D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) * w.1.im := fun v w =>
      diag_im (show D.σ v (δ.out 0 1) = 0 by rw [d01, map_zero]) (show D.σ v (δ.out 1 0) = 0 by rw [d10, map_zero]) w
    have hpair : δ • ((ω, fun _ => iP) : D.Y) = ((ω, D.act δ.out fun _ => iP) : D.Y) := by
      refine Prod.ext h2 ?_
      have := D.mk_smulX δ.out (fun _ => iP)
      rw [QuotientGroup.out_eq'] at this
      exact this
    have key := e2 ![0, 1] (by simp) δ.out ((ω, fun _ => iP) : D.Y)
    rw [hvec, e3 _ (by simp) _ hd11, QuotientGroup.out_eq', hpair] at key
    have key2 := (hH01 (D.act δ.out fun _ => iP)).symm.trans (key.trans (hH01 (fun _ => iP)))
    simp only [Dat.act, hr] at key2
    simpa [iP, h1pos.ne'] using key2
  obtain ⟨β0, hβ0⟩ := (hEcut F I Gf D hH.ax).2 ω (MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om))
    (fun δ hδ => MulAction.mem_stabilizer_iff.2 (hstab δ hδ).2)

  obtain ⟨N, hNdef⟩ : ∃ N : D.Xs → ℝ, ∀ z, N z = (∏ v, |(z v).1.im|) ^ ((Fintype.card I : ℝ)⁻¹) := ⟨_, fun _ => rfl⟩
  have hNpos : ∀ z, 0 < N z := fun z => by
    rw [hNdef]; exact Real.rpow_pos_of_pos (Finset.prod_pos fun v _ => abs_pos.2 (z v).2) _
  obtain ⟨p, hpdef⟩ : ∃ p : D.Xs → D.Xs, ∀ z v, p z v = pt 0 ((z v).1.im / N z) (div_ne_zero (z v).2 (hNpos z).ne') :=
    ⟨fun z v => pt 0 ((z v).1.im / N z) (div_ne_zero (z v).2 (hNpos z).ne'), fun _ _ => rfl⟩
  have hNc : Continuous N := by
    have : N = fun z => (∏ v, |(z v).1.im|) ^ ((Fintype.card I : ℝ)⁻¹) := funext hNdef
    rw [this]
    apply Continuous.rpow_const
    · exact continuous_finset_prod _ fun w _ =>
        (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply w))).abs
    · intro z; left; exact (Finset.prod_pos fun w _ => abs_pos.2 (z w).2).ne'
  have hpc : Continuous p := by
    apply continuous_pi; intro v
    have : (fun z => p z v) = fun z => pt 0 ((z v).1.im / N z) (div_ne_zero (z v).2 (hNpos z).ne') := funext fun z => hpdef z v
    rw [this]
    apply continuous_induced_rng.2
    show Continuous fun z : D.Xs => (((z v).1.im / N z : ℝ) : ℂ) * (((0 : ℝ) : ℂ) + Complex.I)
    exact (Complex.continuous_ofReal.comp ((Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply v))).div
      hNc fun z => (hNpos z).ne')).mul continuous_const
  have hpeq : ∀ δ ∈ MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om), ∀ z : D.Xs, p (δ • z) = δ • p z := by
    intro δ hδ z
    obtain ⟨d01, d10, dprod⟩ := hdiag δ hδ
    have hsm : ∀ w : D.Xs, (δ • w : D.Xs) = D.act δ.out w := by
      intro w; have := D.mk_smulX δ.out w; rw [QuotientGroup.out_eq'] at this; exact this
    have h01' : ∀ v, (D.r v δ.out) 0 1 = 0 := fun v => show D.σ v (δ.out 0 1) = 0 by rw [d01, map_zero]
    have h10' : ∀ v, (D.r v δ.out) 1 0 = 0 := fun v => show D.σ v (δ.out 1 0) = 0 by rw [d10, map_zero]
    have hr : ∀ v (w : P), (D.r v δ.out • w).1.im = D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) * w.1.im :=
      fun v w => diag_im (h01' v) (h10' v) w
    have hN : N (D.act δ.out z) = N z := by
      erw [hNdef, hNdef]; congr 1
      simp only [Dat.act, hr, abs_mul, Finset.prod_mul_distrib, dprod, one_mul]
    rw [hsm, hsm]; funext v
    erw [hpdef]
    apply Subtype.ext
    have e1 : ((D.act δ.out z) v).1.im = D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) * (z v).1.im := hr v (z v)
    have e2 : ((D.act δ.out (p z)) v).1 = ((D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) : ℝ) : ℂ) * (p z v).1 :=
      diag_smul (h01' v) (h10' v) (p z v)
    rw [pt_val, e2, e1, hN]
    erw [hpdef]; rw [pt_val]; push_cast; ring
  have hβ' : IsCut (MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)) (fun z : D.Xs => β0 (p z)) := by
    refine ⟨hβ0.meas.comp hpc.measurable, fun z => hβ0.nonneg _, fun z => ?_⟩
    have : (fun δ : MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om) => β0 (p (δ • z))) =
        fun δ => β0 (δ • p z) := funext fun δ => congrArg β0 (hpeq δ.1 δ.2 z)
    rw [this]; exact hβ0.sum (p z)

  obtain ⟨u, hudef⟩ : ∃ u : D.Xs → ℂ, u = fun z => (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z) := ⟨_, rfl⟩
  suffices hmain : ∫ z, β z • u z = 0 by subst hudef; exact hmain
  have hint2 : Integrable (fun z => β z • u z) := by subst hudef; exact hint
  have hum : Measurable u := by
    subst hudef; exact ((hmeas _).indicator (e8 T _).1).comp measurable_prodMk_left
  have huinv : ∀ (δ : MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)) (z : D.Xs), u (δ • z) = u z := by
    intro δ z
    obtain ⟨h3, h2⟩ := hstab δ.1 δ.2
    have hy : ((ω, (δ.1 • z : D.Xs)) : D.Y) = δ.1 • ((ω, z) : D.Y) := Prod.ext h2.symm rfl
    have hm := (e8 T (γ : PG F)).2 δ.1 (ω, z)
    rw [h3] at hm
    have hk := hinv δ.1 (γ : PG F) (ω, z)
    rw [h3] at hk
    subst hudef
    show Set.indicator _ _ ((ω, (δ.1 • z : D.Xs)) : D.Y) = Set.indicator _ _ ((ω, z) : D.Y)
    rw [hy]
    by_cases h : ((ω, z) : D.Y) ∈ D.LamF T (γ : PG F)
    · rw [Set.indicator_of_mem (hm.2 h), Set.indicator_of_mem h, hk]
    · rw [Set.indicator_of_notMem (mt hm.1 h), Set.indicator_of_notMem h]
  haveI := hcount
  have hC := (hC1 (MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)) D.Xs volume (fun δ => hpres δ.1)
    β (fun z => β0 (p z)) hβ hβ').2 u hum huinv hint2
  rw [hC.2]

  have hu' : ∀ (x y : I → ℝ) (hy : ∀ v, y v ≠ 0),
      (D.Te a g (D.rep ω))⁻¹ * u (fun v => pt (x v) (y v) (hy v)) =
        if D.hf ![1, 0] (D.rep ω) / T / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |y v| ∧ ∏ v, |y v| ≤ T / D.hf ![0, 1] (D.rep ω)
        then ∏ v, φ v (x v) else 0 := by
    intro x y hy
    classical
    have hPy : 0 < ∏ v, |y v| := Finset.prod_pos fun v _ => abs_pos.2 (hy v)
    have hQ : 0 < ∏ v, (1 + x v ^ 2) := Finset.prod_pos fun v _ => by positivity
    have hcond : ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) ∈ D.LamF T (γ : PG F) ↔
        (D.hf ![1, 0] (D.rep ω) / T / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |y v| ∧ ∏ v, |y v| ≤ T / D.hf ![0, 1] (D.rep ω)) := by
      refine (hLam (fun v => pt (x v) (y v) (hy v))).trans ?_
      erw [hH01, hH10]
      simp only [pt_im, abs_im_div_norm_sq_half_plane_point, Finset.prod_inv_distrib, Finset.prod_mul_distrib]
      exact cond_iff _ _ _ _ _ hPy hQ h1pos (by linarith)
    subst hudef
    show _ * Set.indicator _ _ ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) = _
    rw [Set.indicator_apply]
    by_cases hm : ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) ∈ D.LamF T (γ : PG F)
    · rw [if_pos hm, if_pos (hcond.1 hm)]
      erw [hkk]
      rw [inv_mul_cancel_left₀ hc]
      exact Finset.prod_congr rfl fun v _ => hφe v _ _ _
    · rw [if_neg hm, if_neg (mt hcond.2 hm), mul_zero]
  have hA : 0 < D.hf ![1, 0] (D.rep ω) / T := div_pos h2pos (by linarith)
  have hAB : D.hf ![1, 0] (D.rep ω) / T < T / D.hf ![0, 1] (D.rep ω) := by
    rw [div_lt_div_iff₀ (by linarith) h1pos]; nlinarith
  have hinvp : ∀ (x x' y : I → ℝ) (hy : ∀ v, y v ≠ 0) (t : ℝ) (ht : 0 < t),
      β0 (p fun v => pt (x v) (y v) (hy v)) = β0 (p fun v => pt (x' v) (t * y v) (mul_ne_zero ht.ne' (hy v))) := by
    intro x x' y hy t ht
    congr 1; funext v
    erw [hpdef, hpdef]
    apply pt_congr rfl
    erw [hNdef, hNdef]
    simp only [pt_im]
    rw [prod_scale y t ht, mul_div_mul_left _ _ ht.ne']
  have hint3 : Integrable (fun z : X I => β0 (p z) • ((D.Te a g (D.rep ω))⁻¹ * u z)) := by
    refine (hC.1.const_mul (D.Te a g (D.rep ω))⁻¹).congr (Filter.Eventually.of_forall fun z => ?_)
    exact mul_smul_comm _ _ _
  have hF := hF6c I φ (fun v => ⟨hφc v, hφi v, hφl v, hφ0 v, hφn' v⟩) (fun z => β0 (p z))
    (hβ0.meas.comp hpc.measurable) (fun z => hβ0.nonneg _) hinvp _ _ hA hAB
    (fun z => (D.Te a g (D.rep ω))⁻¹ * u z) hu' hint3
  calc ∫ z, β0 (p z) • u z = D.Te a g (D.rep ω) * ∫ z : X I, β0 (p z) • ((D.Te a g (D.rep ω))⁻¹ * u z) := by
        rw [← integral_const_mul]; congr 1; funext z
        rw [mul_smul_comm, mul_inv_cancel_left₀ hc]
    _ = 0 := by rw [hF, mul_zero]
