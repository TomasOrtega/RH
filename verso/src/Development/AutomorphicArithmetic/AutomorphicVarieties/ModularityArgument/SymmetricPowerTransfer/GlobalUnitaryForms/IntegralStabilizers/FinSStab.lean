import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h` using `Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, ‖φ c‖ * (‖φ A‖ + 1))`. Use `(h.preimage (f := fun x : F => c * x) (mul_right_injective₀ hc).injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hA⟩`. Use `⟨hx, fun φ => ?_⟩` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ c‖ * (‖φ A‖ + 1)) (fun _ _ => by positivity) (Finset.mem_univ φ))` and prove the remaining obligations.

Establish `hr : ComplexEmbedding.IsReal φ` using `IsTotallyReal.complexEmbedding_isReal φ`. Establish `e : ∀ y, ‖φ y‖ = |hr.embedding y|` using `fun y => by`. Rewrite using `[← hr.coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs]`. Establish `h1` using `hA hr.embedding`. Simplify using `only [map_mul, norm_mul]`.

Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[e, e]`. Use polynomial arithmetic with `[le_abs_self (hr.embedding A), sq_abs (hr.embedding x), abs_nonneg (hr.embedding x), sq_nonneg (|hr.embedding x| - 1)]`.
-/
private theorem fin_box [IsTotallyReal F] (c : F) (hc : c ≠ 0) (A : F) :
    {x : F | IsIntegral ℤ (c * x) ∧ ∀ σ : F →+* ℝ, σ x ^ 2 ≤ σ A}.Finite := by
  have h := Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, ‖φ c‖ * (‖φ A‖ + 1))
  refine (h.preimage (f := fun x : F => c * x) (mul_right_injective₀ hc).injOn).subset ?_
  rintro x ⟨hx, hA⟩
  refine ⟨hx, fun φ => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ c‖ * (‖φ A‖ + 1)) (fun _ _ => by positivity)
    (Finset.mem_univ φ))
  have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  have e : ∀ y, ‖φ y‖ = |hr.embedding y| := fun y => by
    rw [← hr.coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hA hr.embedding
  simp only [map_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [e, e]
  nlinarith [le_abs_self (hr.embedding A), sq_abs (hr.embedding x), abs_nonneg (hr.embedding x),
    sq_nonneg (|hr.embedding x| - 1)]

variable {Δ : F}

/- English proof (translation)
Use `fun v : Pl F => isIntegral_coords (h v) (m := (m : Kv v)) (isIntegral_natCast _) (by simpa using isIntegral_glob.1 hm v)` as an intermediate fact. Use `⟨isIntegral_glob.2 fun v => ?_, isIntegral_glob.2 fun v => ?_⟩` and prove the remaining obligations. Simplify `(this v).1` using `[lmap, map_ofNat]`. Simplify `(this v).2` using `[lmap, map_ofNat]`.
-/
theorem coords_glob {a : Lsq F Δ} (h : ∀ v : Pl F, IsIntegral (Ov v) (lmap (cv v) Δ a)) {m : ℕ} (hm : IsIntegral ℤ ((m : F) * Δ)) :
    IsIntegral ℤ (2 * m * Δ * a.re) ∧ IsIntegral ℤ (2 * m * Δ * a.im) := by
  have := fun v : Pl F => isIntegral_coords (h v) (m := (m : Kv v)) (isIntegral_natCast _)
    (by simpa using isIntegral_glob.1 hm v)
  refine ⟨isIntegral_glob.2 fun v => ?_, isIntegral_glob.2 fun v => ?_⟩
  · simpa [lmap, map_ofNat] using (this v).1
  · simpa [lmap, map_ofNat] using (this v).2

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (F →+* ℂ)` from `inferInstance`. Introduce `h`. Simplify `hneg (IsTotallyReal.complexEmbedding_isReal φ).embedding` using `[h]`.
-/
theorem ne_zero_of_neg [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) : Δ ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  intro h
  simpa [h] using hneg (IsTotallyReal.complexEmbedding_isReal φ).embedding

/- English proof (translation)
Take `⟨m, hm0, hm⟩` from `exists_nat_mul Δ`. Establish `hΔ` using `ne_zero_of_neg hneg`. Establish `hc : (2 * m * Δ * n : F) ≠ 0` using `by simp [hΔ, hm0, hn]`. Establish `h1` using `fin_box _ hc 1`. Establish `h2` using `fin_box _ hc (-Δ⁻¹)`.

Use `(((h1.prod h2).prod (h1.prod h2)).preimage (f := fun γ : SU Δ => (((mt (γ : DX Δ) 0 0).re, (mt (γ : DX Δ) 0 0).im), ((mt (γ : DX Δ) 0 1).re, (mt (γ : DX Δ) 0 1).im))) ?_).subset ?_` and prove the remaining obligations. Introduce `γ _ γ' _ h`. Simplify using `only [Prod.mk.injEq] at h`. Establish `e0 : mt (γ : DX Δ) 0 0 = mt (γ' : DX Δ) 0 0` using `QuadraticAlgebra.ext h.1.1 h.1.2`. Establish `e1 : mt (γ : DX Δ) 0 1 = mt (γ' : DX Δ) 0 1` using `QuadraticAlgebra.ext h.2.1 h.2.2`.

Use `Subtype.ext (Subtype.ext (Units.ext ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mt (γ : DX Δ) = mt (γ' : DX Δ)`. Use extensionality with `i j : 1`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `e0`.

Conclude with `e1`. Conclude with `(mt_mem _).2.trans (e1 ▸ (mt_mem _).2.symm)`. Conclude with `(mt_mem _).1.trans (e0 ▸ (mt_mem _).1.symm)`. Introduce `γ hγ`. Establish `hi` using `fun i j => coords_glob (a := (n : Lsq F Δ) * mt (γ : DX Δ) i j) (fun v => by`.

Rewrite using `[map_mul, map_natCast]`. Conclude with `hγ v i j) hm`. Establish `hd : (mt (γ : DX Δ)).det = 1` using `congrArg Units.val γ.2`. Rewrite `hd` using `[det_Dm (mt_mem _)]`. Establish `hd'` using `congrArg QuadraticAlgebra.re hd`.

Rewrite `hd'` using `[QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_one]`. Establish `hs` using `fun σ : F →+* ℝ => congrArg σ hd'`. Simplify using `only [map_sub, map_add, map_mul, map_pow, map_one] at hs`. Establish `key : ∀ (σ : F →+* ℝ) (x : ℝ), -σ Δ * x ^ 2 ≤ 1 → x ^ 2 ≤ σ (-Δ⁻¹)` using `fun σ x h => by`. Rewrite using `[map_neg, map_inv₀, ← inv_neg, inv_eq_one_div, le_div_iff₀ (neg_pos.2 (hneg σ))]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `pos : ∀ (σ : F →+* ℝ) (x : ℝ), σ Δ * x ^ 2 ≤ 0` using `fun σ x => mul_nonpos_of_nonpos_of_nonneg (hneg σ).le (sq_nonneg _)`. Use `⟨⟨⟨by simpa [mul_assoc] using (hi 0 0).1, fun σ => ?_⟩, by simpa [mul_assoc] using (hi 0 0).2, fun σ => key σ _ ?_⟩, ⟨by simpa [mul_assoc] using (hi 0 1).1, fun σ => ?_⟩, by simpa [mul_assoc] using (hi 0 1).2, fun σ => key σ _ ?_⟩` and prove the remaining obligations. Use `all_goals`. Use `hs σ` as an intermediate fact.

Use `pos σ (σ (mt (γ : DX Δ) 0 0).im)` as an intermediate fact. Use `pos σ (σ (mt (γ : DX Δ) 0 1).im)` as an intermediate fact. Use `sq_nonneg (σ (mt (γ : DX Δ) 0 0).re)` as an intermediate fact. Use `sq_nonneg (σ (mt (γ : DX Δ) 0 1).re)` as an intermediate fact. Simplify using `only [map_one]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fin_SU [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (n : ℕ) (hn : n ≠ 0) :
    {γ : SU Δ | ∀ (v : Pl F) i j, IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * lmap (cv v) Δ (mt (γ : DX Δ) i j))}.Finite := by
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul Δ
  have hΔ := ne_zero_of_neg hneg
  have hc : (2 * m * Δ * n : F) ≠ 0 := by simp [hΔ, hm0, hn]
  have h1 := fin_box _ hc 1
  have h2 := fin_box _ hc (-Δ⁻¹)
  refine (((h1.prod h2).prod (h1.prod h2)).preimage (f := fun γ : SU Δ =>
    (((mt (γ : DX Δ) 0 0).re, (mt (γ : DX Δ) 0 0).im), ((mt (γ : DX Δ) 0 1).re, (mt (γ : DX Δ) 0 1).im))) ?_).subset ?_
  · intro γ _ γ' _ h
    simp only [Prod.mk.injEq] at h
    have e0 : mt (γ : DX Δ) 0 0 = mt (γ' : DX Δ) 0 0 := QuadraticAlgebra.ext h.1.1 h.1.2
    have e1 : mt (γ : DX Δ) 0 1 = mt (γ' : DX Δ) 0 1 := QuadraticAlgebra.ext h.2.1 h.2.2
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    change mt (γ : DX Δ) = mt (γ' : DX Δ)
    ext i j : 1
    fin_cases i <;> fin_cases j
    · exact e0
    · exact e1
    · exact (mt_mem _).2.trans (e1 ▸ (mt_mem _).2.symm)
    · exact (mt_mem _).1.trans (e0 ▸ (mt_mem _).1.symm)
  · intro γ hγ
    have hi := fun i j => coords_glob (a := (n : Lsq F Δ) * mt (γ : DX Δ) i j) (fun v => by
      rw [map_mul, map_natCast]; exact hγ v i j) hm
    have hd : (mt (γ : DX Δ)).det = 1 := congrArg Units.val γ.2
    rw [det_Dm (mt_mem _)] at hd
    have hd' := congrArg QuadraticAlgebra.re hd
    rw [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_one] at hd'
    have hs := fun σ : F →+* ℝ => congrArg σ hd'
    simp only [map_sub, map_add, map_mul, map_pow, map_one] at hs
    have key : ∀ (σ : F →+* ℝ) (x : ℝ), -σ Δ * x ^ 2 ≤ 1 → x ^ 2 ≤ σ (-Δ⁻¹) := fun σ x h => by
      rw [map_neg, map_inv₀, ← inv_neg, inv_eq_one_div, le_div_iff₀ (neg_pos.2 (hneg σ))]
      linarith
    have pos : ∀ (σ : F →+* ℝ) (x : ℝ), σ Δ * x ^ 2 ≤ 0 := fun σ x => mul_nonpos_of_nonpos_of_nonneg (hneg σ).le (sq_nonneg _)
    refine ⟨⟨⟨by simpa [mul_assoc] using (hi 0 0).1, fun σ => ?_⟩, by simpa [mul_assoc] using (hi 0 0).2, fun σ => key σ _ ?_⟩,
      ⟨by simpa [mul_assoc] using (hi 0 1).1, fun σ => ?_⟩, by simpa [mul_assoc] using (hi 0 1).2, fun σ => key σ _ ?_⟩
    all_goals
      have := hs σ
      have := pos σ (σ (mt (γ : DX Δ) 0 0).im)
      have := pos σ (σ (mt (γ : DX Δ) 0 1).im)
      have := sq_nonneg (σ (mt (γ : DX Δ) 0 0).re)
      have := sq_nonneg (σ (mt (γ : DX Δ) 0 1).re)
      simp only [map_one]
      linarith

/- English proof (translation)
Establish `e : mt ((y * k * y⁻¹).1 v) = mt (y.1 v) * mt (k.1 v) * mt (y⁻¹.1 v)` using `rfl`. Establish `hk'` using `(mem_KD.1 (hk v)).1`. Use `(((h v i 0).mul (hk' 0 0)).add ((h v i 1).mul (hk' 1 0))).mul (h' v 0 j) |>.add ((((h v i 0).mul (hk' 0 1)).add ((h v i 1).mul (hk' 1 1))).mul (h' v 1 j))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[e]`.

Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem int_conj (y k : DA Δ) (hk : ∀ v, k.1 v ∈ KD (cv v Δ) (Ov v)) {n n' : ℕ}
    (h : ∀ v i j, IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * mt (y.1 v) i j))
    (h' : ∀ v i j, IsIntegral (Ov v) ((n' : Lsq (Kv v) (cv v Δ)) * mt (y⁻¹.1 v) i j)) (v : Pl F) (i j : Fin 2) :
    IsIntegral (Ov v) (((n * n' : ℕ) : Lsq (Kv v) (cv v Δ)) * mt ((y * k * y⁻¹).1 v) i j) := by
  have e : mt ((y * k * y⁻¹).1 v) = mt (y.1 v) * mt (k.1 v) * mt (y⁻¹.1 v) := rfl
  have hk' := (mem_KD.1 (hk v)).1
  have := (((h v i 0).mul (hk' 0 0)).add ((h v i 1).mul (hk' 1 0))).mul (h' v 0 j) |>.add
    ((((h v i 0).mul (hk' 0 1)).add ((h v i 1).mul (hk' 1 1))).mul (h' v 1 j))
  convert this using 1
  rw [e]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_mul]
  ring

/- English proof (translation)
Use `h.real` as an intermediate fact. Take `⟨n, hn, h1⟩` from `den_DA ((g : DA Δ) * x)`. Take `⟨n', hn', h2⟩` from `den_DA ((g : DA Δ) * x)⁻¹`. Rewrite using `[hB.Γ₀, Subgroup.relIndex_bot_left]`. Use `Nat.card_ne_zero.2 ⟨inferInstance, ?_⟩` and prove the remaining obligations.

Use `((fin_SU h.neg (n * n') (mul_ne_zero hn hn')).subset ?_).to_subtype` and prove the remaining obligations. Introduce and unpack `γ ⟨u, hu, e⟩ v i j`. Establish `hk` using `Subgroup.mem_iInf.1 (hU ((hB.U u).1 hu))`. Use `int_conj _ (x⁻¹ * (u : DA Δ) * x) hk h1 h2 v i j` as an intermediate fact. Establish `e2 : (g : DA Δ) * x * (x⁻¹ * u * x) * ((g : DA Δ) * x)⁻¹ = (B.ι γ : DA Δ)`.

Rewrite using `[← e]`. Express the relevant statement in the definitionally equal form `_ = (g : DA Δ) * u * (g : DA Δ)⁻¹`. Use `group`. Rewrite `this` using `[e2, hB.ι]`. Conclude with `this`.
-/
theorem finS_stab (D : Dat Δ) (h : D.Ok) (hU : D.U2 ≤ (rpg _ _).box fun v : Pl F => KD (cv v Δ) (Ov v))
    {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {x : DA Δ} {B : Base (SU Δ) (SA Δ) V} (hB : D.IsBS ch x B)
    (g : SA Δ) : B.Γ₀.relIndex ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) ≠ 0 := by
  have := h.real
  obtain ⟨n, hn, h1⟩ := den_DA ((g : DA Δ) * x)
  obtain ⟨n', hn', h2⟩ := den_DA ((g : DA Δ) * x)⁻¹
  rw [hB.Γ₀, Subgroup.relIndex_bot_left]
  refine Nat.card_ne_zero.2 ⟨inferInstance, ?_⟩
  refine ((fin_SU h.neg (n * n') (mul_ne_zero hn hn')).subset ?_).to_subtype
  rintro γ ⟨u, hu, e⟩ v i j
  have hk := Subgroup.mem_iInf.1 (hU ((hB.U u).1 hu))
  have := int_conj _ (x⁻¹ * (u : DA Δ) * x) hk h1 h2 v i j
  have e2 : (g : DA Δ) * x * (x⁻¹ * u * x) * ((g : DA Δ) * x)⁻¹ = (B.ι γ : DA Δ) := by
    rw [← e]
    change _ = (g : DA Δ) * u * (g : DA Δ)⁻¹
    group
  rw [e2, hB.ι] at this
  exact this

end UpperTheory.V.Z.Sym.Glob
