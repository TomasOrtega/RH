import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatakePolarizationOfCuspidalTransfer

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial Formalism.L2.Host Neutral.B1
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open scoped Matrix
/- English proof (translation)
Use `set N : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) k).map f with hN`. Use `set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) k).map f with hQ`. Establish `hdet : ∀ U : GL (Fin n) k, ((U : Matrix (Fin n) (Fin n) k).map f).det ≠ 0` using `fun U => by`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero f).2 (Matrix.GeneralLinearGroup.det U).ne_zero`.

Establish `h' : Nᵀ * Q * N = f t • Q`. Use `congrArg (fun Z : Matrix (Fin n) (Fin n) k => Z.map f) h` as an intermediate fact. Simplify using `only [Matrix.map_mul, Matrix.transpose_map] at this`. Rewrite using `[this]`. Use extensionality with `i j`.

Simplify using `[hQ]`. Rewrite `hB` using `[← Matrix.charpoly_map, ← hN]`. Establish `hc : B.card = n`. Use `congrArg natDegree hB` as an intermediate fact. Rewrite `this` using `[Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card]`.

Simplify using `using this.symm`. Establish `ev : ∀ x : ℂ, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = (B.map fun b => x - b).prod` using `fun x => by`. Use `congrArg (eval x) hB` as an intermediate fact. Rewrite `this` using `[Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map]`. Simplify `this` using `[Matrix.smul_one_eq_diagonal]`.

Establish `e0 : N.det = B.prod`. Use `ev 0` as an intermediate fact. Simplify using `only [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin] at this`. Rewrite `this` using `[Multiset.prod_map_neg, hc]`. Conclude with `mul_left_cancel₀ (pow_ne_zero _ (by simp)) this`.

Establish `hb : ∀ b ∈ B, b ≠ 0` using `fun b hb h0 => hdet M (e0.trans (Multiset.prod_eq_zero (h0 ▸ hb)))`. Establish `key : ∀ x : ℂ, x ≠ 0 → ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod = (B.map fun b => x - b).prod`. Introduce `x hx`. Establish `e1 : Nᵀ * Q * (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N) = (-x) • (((f t / x) • (1 : Matrix (Fin n) (Fin n) ℂ) - N)ᵀ * Q)`. Rewrite using `[mul_sub, h', Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_mul, smul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, neg_mul, mul_div_cancel₀ _ hx, neg_smul, neg_smul]`.

Normalize the expressions using the abelian group laws. Establish `e2` using `congrArg Matrix.det e1`. Rewrite `e2` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, ev, ev, e0, Fintype.card_fin]`. Establish `e3 : B.prod * ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod = (-x) ^ n * (B.map fun b => f t / x - b).prod`. Rewrite using `[← hc, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul, Multiset.map_map]`.

Use `conv_lhs => rw [← Multiset.map_id' B, Multiset.map_map, ← Multiset.prod_map_mul]`. Use `congrArg _ (Multiset.map_congr rfl fun b h => ?_)` and prove the remaining obligations. Use `hb b h` as an intermediate fact. Simplify using `only [Function.comp_apply]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Use `mul_left_cancel₀ (mul_ne_zero (e0 ▸ hdet M) (hdet P)) ?_` and prove the remaining obligations. Rewrite using `[← hQ]`. Take the linear combination `Q.det * e3 - e2`. Establish `hp : ((B.map fun b => f t * b⁻¹).map fun b => X - C b).prod = (B.map fun b => X - C b).prod`.

Use `eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_)` and prove the remaining obligations. Use `key x hx` as an intermediate fact. Simplify `this` using `[eval_multiset_prod, Multiset.map_map]`. Use `congrArg roots hp` as an intermediate fact. Rewrite `this` using `[roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C]`. Then use the resulting hypothesis.
-/
private theorem roots_stable {k : Type} [Field k] {n : ℕ} (f : k →+* ℂ) (M P : GL (Fin n) k) (t : kˣ)
    (h : (M : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (M : Matrix (Fin n) (Fin n) k) =
      (t : k) • (P : Matrix (Fin n) (Fin n) k)) (B : Multiset ℂ)
    (hB : (M : Matrix (Fin n) (Fin n) k).charpoly.map f = (B.map fun b => X - C b).prod) :
    B.map (fun b => f t * b⁻¹) = B := by
  set N : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) k).map f with hN
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) k).map f with hQ
  have hdet : ∀ U : GL (Fin n) k, ((U : Matrix (Fin n) (Fin n) k).map f).det ≠ 0 := fun U => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero f).2 (Matrix.GeneralLinearGroup.det U).ne_zero
  have h' : Nᵀ * Q * N = f t • Q := by
    have := congrArg (fun Z : Matrix (Fin n) (Fin n) k => Z.map f) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [this]
    ext i j
    simp [hQ]
  rw [← Matrix.charpoly_map, ← hN] at hB
  have hc : B.card = n := by
    have := congrArg natDegree hB
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have ev : ∀ x : ℂ, (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N).det = (B.map fun b => x - b).prod := fun x => by
    have := congrArg (eval x) hB
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at this
    simpa [Matrix.smul_one_eq_diagonal] using this
  have e0 : N.det = B.prod := by
    have := ev 0
    simp only [zero_smul, zero_sub, Matrix.det_neg, Fintype.card_fin] at this
    rw [Multiset.prod_map_neg, hc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ (by simp)) this
  have hb : ∀ b ∈ B, b ≠ 0 := fun b hb h0 => hdet M (e0.trans (Multiset.prod_eq_zero (h0 ▸ hb)))
  have key : ∀ x : ℂ, x ≠ 0 → ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod = (B.map fun b => x - b).prod := by
    intro x hx
    have e1 : Nᵀ * Q * (x • (1 : Matrix (Fin n) (Fin n) ℂ) - N) =
        (-x) • (((f t / x) • (1 : Matrix (Fin n) (Fin n) ℂ) - N)ᵀ * Q) := by
      rw [mul_sub, h', Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_mul, smul_sub,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, neg_mul, mul_div_cancel₀ _ hx, neg_smul, neg_smul]
      abel
    have e2 := congrArg Matrix.det e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
      ev, ev, e0, Fintype.card_fin] at e2
    have e3 : B.prod * ((B.map fun b => f t * b⁻¹).map fun b => x - b).prod =
        (-x) ^ n * (B.map fun b => f t / x - b).prod := by
      rw [← hc, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul, Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id' B, Multiset.map_map, ← Multiset.prod_map_mul]
      refine congrArg _ (Multiset.map_congr rfl fun b h => ?_)
      have := hb b h
      simp only [Function.comp_apply]
      field_simp
      ring
    refine mul_left_cancel₀ (mul_ne_zero (e0 ▸ hdet M) (hdet P)) ?_
    rw [← hQ]
    linear_combination Q.det * e3 - e2
  have hp : ((B.map fun b => f t * b⁻¹).map fun b => X - C b).prod = (B.map fun b => X - C b).prod := by
    refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_)
    have := key x hx
    simpa [eval_multiset_prod, Multiset.map_map] using this
  have := congrArg roots hp
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at this
/- English proof (translation)
Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Take `⟨σ, hσ⟩` from `exists_isFrob hA`. Take `⟨P, hP⟩` from `hr`. Establish `h1` using `roots_stable ι.toRingHom _ P _ (hP σ⁻¹) _ ((hB A hA).2 σ hσ)`. Establish `h2` using `hχ.frob_unr ha (Or.inl hw) hu hA hσ`.

Establish `h3 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l)`. Rewrite using `[cycBar, MonoidHom.comp_apply, Units.coe_map, cycZ_of_isFrob hw hA hσ]`. Simplify using the standard rewrite rules. Establish `hq : (0 : ℝ) < normV w`. Establish `: 1 < Ideal.absNorm w.asIdeal` using `NumberField.HeightOneSpectrum.one_lt_absNorm w`.

Establish `h : 0 < normV w` using `zero_lt_one.trans this`. Conclude with `h` after adjusting the coercions. Use `set c : ℂ := (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hc`. Establish `hc0 : c ≠ 0` using `Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'`. Establish `hcc : c * c = (normV w : ℂ) ^ ((n : ℤ) - 1)`.

Rewrite using `[hc, ← Complex.ofReal_mul, ← Real.rpow_add hq, add_halves, show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; rfl, Real.rpow_intCast]`. Simplify using the standard rewrite rules. Establish `h4 : ι ((θ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c * c * (χ.val w : ℂˣ)`. Establish `h5` using `congrArg ι h2`. Rewrite `h5` using `[MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, h3, map_mul, map_zpow₀, map_natCast, map_inv₀, ι.apply_symm_apply, ← hcc]`.

Rewrite using `[map_inv, Units.val_inv_eq_inv_val, map_inv₀]`. Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, h5, inv_mul_cancel₀ (Units.ne_zero _)]`. Use `Multiset.map_injective (f := fun α : ℂˣ => c * (α : ℂ)) (fun x y e => Units.ext (mul_left_cancel₀ hc0 e)) ?_` and prove the remaining obligations. Establish `h6 : algSat n (normV w) B = B.map fun α : ℂˣ => c * (α : ℂ)`.

Express the relevant statement in the definitionally equal form `Multiset.map _ (B.bind fun a : ℂˣ => ({(a : ℂ)} : Multiset ℂ)) = _`. Rewrite using `[Multiset.bind_singleton, Multiset.map_map]`. Both sides reduce to the same expression. Rewrite `h1` using `[h6]`. Use `Eq.trans ?_ h1` and prove the remaining obligations.

Simplify using `only [Multiset.map_map]`. Use `Multiset.map_congr rfl fun α _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c * _ = ι _ * (c * _)⁻¹`. Rewrite using `[h4]`. Simplify using `only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val]`.

Clear the denominators using the available nonvanishing facts.
-/
private theorem sat_stable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {θ : G F Ω →* (Qbar l)ˣ}
    (hr : DualTw r θ) {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) {χ : HChar F} {a : (F →+* ℂ) → ℤ}
    (hχ : IsLAdicOf art ι χ a (θ * cycBar F Ω l ^ ((n : ℤ) - 1))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (hu : χ.UnrAt w) {B : Multiset ℂˣ}
    (hB : FrobEig ι r w (algSat n (normV w) B)) : (B.map (·⁻¹)).map (· * χ.val w) = B := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  obtain ⟨P, hP⟩ := hr
  have h1 := roots_stable ι.toRingHom _ P _ (hP σ⁻¹) _ ((hB A hA).2 σ hσ)
  have h2 := hχ.frob_unr ha (Or.inl hw) hu hA hσ
  have h3 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
    rw [cycBar, MonoidHom.comp_apply, Units.coe_map, cycZ_of_isFrob hw hA hσ]
    simp
  have hq : (0 : ℝ) < normV w := by
    have : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
    have h : 0 < normV w := zero_lt_one.trans this
    exact_mod_cast h
  set c : ℂ := (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  have hcc : c * c = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hc, ← Complex.ofReal_mul, ← Real.rpow_add hq, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; rfl, Real.rpow_intCast]
    simp
  have h4 : ι ((θ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c * c * (χ.val w : ℂˣ) := by
    have h5 := congrArg ι h2
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, h3, map_mul, map_zpow₀,
      map_natCast, map_inv₀, ι.apply_symm_apply, ← hcc] at h5
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, h5, inv_mul_cancel₀ (Units.ne_zero _)]
  refine Multiset.map_injective (f := fun α : ℂˣ => c * (α : ℂ))
    (fun x y e => Units.ext (mul_left_cancel₀ hc0 e)) ?_
  have h6 : algSat n (normV w) B = B.map fun α : ℂˣ => c * (α : ℂ) := by
    change Multiset.map _ (B.bind fun a : ℂˣ => ({(a : ℂ)} : Multiset ℂ)) = _
    rw [Multiset.bind_singleton, Multiset.map_map]
    rfl
  rw [h6] at h1
  refine Eq.trans ?_ h1
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  change c * _ = ι _ * (c * _)⁻¹
  rw [h4]
  simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp
/- English proof (translation)
Introduce `H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ θ χ hr hχ`. Establish `hd : π.IsSelfDualBy χ`. Take `⟨-, art, a, ha, -, h2⟩` from `hχ`. Use `_root_.UpperTheory.satake_polarization_real_of_printed_results H.toClassicalTheorems F n hn π χ ?_` and prove the remaining obligations. Establish `h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0`.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `(Fact.out : l.Prime).ne_zero` after adjusting the coercions. Establish `hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal` using `(Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)`. Use `filter_upwards [hπ.2, hl, (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1] with w ⟨S, hS, hE⟩ hw hu`. Use `⟨hu, S, hS, ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← sat_stable hr ha h2 hw hu hE]`. Simplify using `[Multiset.map_map]`. Use `⟨hd, fun hs => ⟨UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel F Ω l ι χ _ hχ fun c c' hc hc' => ?_, hd⟩⟩` and prove the remaining obligations. Simplify using `only [MonoidHom.mul_apply, MonoidHom.zpow_apply, hs c c' hc hc', UpperTheory.cyclotomic_char_conj_invariant F Ω l c hc, UpperTheory.cyclotomic_char_conj_invariant F Ω l c' hc']`.
-/
theorem UpperTheory.V.Af.self_dual_real_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.SelfDualR := by
  intro H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ θ χ hr hχ
  have hd : π.IsSelfDualBy χ := by
    obtain ⟨-, art, a, ha, -, h2⟩ := hχ
    refine _root_.UpperTheory.satake_polarization_real_of_printed_results H.toClassicalTheorems F n hn π χ ?_
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
      (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
    filter_upwards [hπ.2, hl, (GlobalTheory.Mem.UnrAe.unr_ae_and_level F χ).1] with w ⟨S, hS, hE⟩ hw hu
    refine ⟨hu, S, hS, ?_⟩
    conv_rhs => rw [← sat_stable hr ha h2 hw hu hE]
    simp [Multiset.map_map]
  refine ⟨hd, fun hs => ⟨UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel F Ω l ι χ _ hχ fun c c' hc hc' => ?_, hd⟩⟩
  simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, hs c c' hc hc', UpperTheory.cyclotomic_char_conj_invariant F Ω l c hc,
    UpperTheory.cyclotomic_char_conj_invariant F Ω l c' hc']
end
