import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.GapTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
/- English proof (translation)
Establish `e2 : lie E a (Central.scL a z) = ∑ i, lieS E a i i z`. Simplify using `only [lieS_apply, ← map_sum]`. Conclude with `congrArg (lie E a) (Matrix.sum_single_eq_diagonal (fun _ : Fin a => z)).symm`. Rewrite using `[← LinearMap.sum_apply, ← e2]`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations.

Establish `h1` using `Central.hasDerivAt_scalar z ψ g`. Establish `h2 : (fun t : ℝ => ψ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) = fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g`. Use function extensionality and compare the values at `t`. Establish `h3` using `congrFun (congrArg Subtype.val (hω (infId E (expU (t • z))) ψ hψ)) g`. Establish `h4` using `chiInf_expU ω (t • z)`.

Rewrite `h4` using `[map_smul, Complex.real_smul]`. Rewrite using `[← h4]`. Conclude with `h3`. Rewrite `h1` using `[h2]`. Establish `h5` using `(((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)`.

Establish `h6` using `h1.unique h5`. Express the relevant statement in the definitionally equal form `lieD _ ψ.1 g = dchi ω z * ψ.1 g`. Rewrite using `[h6]`. Simplify using the standard rewrite rules.
-/
private theorem lie_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    ∑ i, lieS E a i i z ψ = dchi ω z • ψ := by
  have e2 : lie E a (Central.scL a z) = ∑ i, lieS E a i i z := by
    simp only [lieS_apply, ← map_sum]
    exact congrArg (lie E a) (Matrix.sum_single_eq_diagonal (fun _ : Fin a => z)).symm
  rw [← LinearMap.sum_apply, ← e2]
  refine Subtype.ext (funext fun g => ?_)
  have h1 := Central.hasDerivAt_scalar z ψ g
  have h2 : (fun t : ℝ => ψ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    have h3 := congrFun (congrArg Subtype.val (hω (infId E (expU (t • z))) ψ hψ)) g
    have h4 := chiInf_expU ω (t • z)
    rw [map_smul, Complex.real_smul] at h4
    rw [← h4]
    exact h3
  rw [h2] at h1
  have h5 := (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)
  have h6 := h1.unique h5
  change lieD _ ψ.1 g = dchi ω z * ψ.1 g
  rw [h6]
  simp
/- English proof (translation)
Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Use `smul_left_injective ℂ h0 ?_` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[← GlobalTheory.trace_Eop_of_hasInfChar E a π τ m hm φ hφ]`. Establish `h1` using `lie_central hω (atEmb τ 1) hφ`.

Establish `h2` using `lie_central hω (atEmb τ Complex.I) hφ`. Simplify using `only [Eop, expo, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, ← Finset.smul_sum, Finset.sum_sub_distrib, h1, h2]`. Use `module`.
-/
private theorem expo_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : π.HasInfChar τ m) : expo ω τ = m.sum := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine smul_left_injective ℂ h0 ?_
  beta_reduce
  rw [← GlobalTheory.trace_Eop_of_hasInfChar E a π τ m hm φ hφ]
  have h1 := lie_central hω (atEmb τ 1) hφ
  have h2 := lie_central hω (atEmb τ Complex.I) hφ
  simp only [Eop, expo, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, ← Finset.smul_sum, Finset.sum_sub_distrib, h1, h2]
  module
/- English proof (translation)
Establish `hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q`. Rewrite using `[← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]`. Evaluate the numerical expressions. Establish `hq'` using `congrArg (fun x : ℝ => (x : ℂ)) hq`. Simplify using `only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'`.

Establish `e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x, (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y}`. Simplify using `[algSat]`. Rewrite using `[Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, mul_mul_mul_comm, hq', Units.val_mul]`.
-/
private theorem det_algSat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = (q : ℂ) * ((x * y : ℂˣ) : ℂ) := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  have e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x,
      (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y} := by
    simp [algSat]
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, mul_mul_mul_comm, hq',
    Units.val_mul]
/- English proof (translation)
Establish `h0 : i + j = 0`. Establish `: ((i + j : ℤ) : ℂ) = 0` using `by push_cast; linear_combination hs - hi - hj`. Conclude with `this` after adjusting the coercions. Establish `h1 : i ≠ j` using `fun e => hne (by rw [hi, hj, e])`. Break down `lt_or_gt_of_ne h1 with h | h` into its components or cases.

Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)`. Use `⟨x, k, by omega, ?_⟩` and prove the remaining obligations. Establish `: ((j - i : ℤ) : ℂ) = k` using `by rw [hk]; simp`. Move the coercions through the operations in `at this`. Rewrite using `[show x + k = y by linear_combination hi - hj - this]`.

Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)`. Use `⟨y, k, by omega, ?_⟩` and prove the remaining obligations. Establish `: ((i - j : ℤ) : ℂ) = k` using `by rw [hk]; simp`. Move the coercions through the operations in `at this`. Rewrite using `[show y + k = x by linear_combination hj - hi - this, Multiset.pair_comm]`.
-/
private theorem gap_of_sum {x y : ℂ} (hne : x ≠ y) {i j : ℤ} (hi : x = i + 1 / 2) (hj : y = j + 1 / 2) (hs : x + y = 1) :
    ∃ (c : ℂ) (k : ℕ), 2 ≤ k ∧ ({x, y} : Multiset ℂ) = {c, c + k} := by
  have h0 : i + j = 0 := by
    have : ((i + j : ℤ) : ℂ) = 0 := by push_cast; linear_combination hs - hi - hj
    exact_mod_cast this
  have h1 : i ≠ j := fun e => hne (by rw [hi, hj, e])
  rcases lt_or_gt_of_ne h1 with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨x, k, by omega, ?_⟩
    have : ((j - i : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show x + k = y by linear_combination hi - hj - this]
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨y, k, by omega, ?_⟩
    have : ((i - j : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show y + k = x by linear_combination hj - hi - this, Multiset.pair_comm]
end SlopeTestRemainingChoices
/- English proof (translation)
Introduce `_ F Ω _ _ _ _ _ _ l _ ι r P hreg hatt ⟨N, hN, hdet⟩ τ`. Take `⟨ω, hω⟩` from `Central.exists_hasCentral F 2 P`. Establish `hone : (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) ^ N = 1`. Use `PositivityTheory.jumpWindows.FiniteInfinitePlaceProduct.eq_one _ ?_` and prove the remaining obligations. Use `filter_upwards [hatt.2] with w ⟨B, hB, hF⟩`.

Take `⟨x, y, rfl⟩` from `Multiset.card_eq_two.1 hB.card`. Establish `h1` using `PositivityTheory.jumpWindows.PSmo.val_eq_prod (CuspSub.hasCentral_iff.1 hω) hB`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Take `⟨σ, hσ⟩` from `ReciprocityTheory.Gal.exists_isFrob hA`. Establish `e2` using `(hF A hA).2 σ hσ`.

Rewrite `e2` using `[← Matrix.charpoly_map]`. Establish `e3` using `det_algSat _ _ _ _ e2`. Establish `e4 : ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ((r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom).det` using `ι.toRingHom.map_det _`. Establish `e5` using `congrArg (fun u : (Qbar l)ˣ => ι (u : Qbar l)) (hdet σ⁻¹)`. Simplify using `only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, Matrix.GeneralLinearGroup.val_det_apply] at e5`.

Rewrite `e5` using `[e4, e3]`. Establish `e6` using `(GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (-1)).2.1 w`. Use `Units.ext ?_` and prove the remaining obligations. Establish `hp : ∀ ν : HChar F, (ν ^ N).val w = ν.val w ^ N` using `fun ν => MonoidHom.pow_apply ν.1 N _`. Rewrite using `[hp, HChar.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, e6, h1, Multiset.prod_pair, Units.val_one, ← e5, mul_comm]`.

Simplify using `[normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hsum : ((CG.mk P).infChar τ).sum = 1`. Establish `h1` using `GlobalTheory.BCT.TwistDisc.expo_pow (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) N τ`. Establish `h2` using `GlobalTheory.BCT.TwistDisc.expo_pow (1 : HChar F) 0 τ`. Rewrite `h2` using `[pow_zero, Nat.cast_zero, zero_mul]`.

Establish `h3` using `(CG.hasInfChar_ofChar ω τ).twist (GlobalTheory.HeckeGal.Model.absPow F (-1))`. Rewrite `h3` using `[CG.twist_ofChar, Multiset.map_singleton]`. Establish `h4` using `h3.infChar_eq`. Rewrite `h4` using `[CG.infChar_ofChar, Multiset.singleton_inj]`. Establish `h5 : expo (GlobalTheory.HeckeGal.Model.absPow F (-1)) τ = ((-1 : ℝ) : ℂ)` using `GlobalTheory.CuspRep.Model.expo_absC _ τ`.

Rewrite `h1` using `[hone, h2, h4, h5, expo_central hω (ParLaws.hasInfChar_infChar (CG.mk P) τ)]`. Establish `h6` using `(mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hN.ne')`. Move the coercions through the operations in `at h6`. Take the linear combination `h6`. Establish `hm : P.HasInfChar τ ((CG.mk P).infChar τ)` using `ParLaws.hasInfChar_infChar (CG.mk P) τ`.

Take `⟨hnd, hint⟩` from `hreg τ`. Take `⟨x, y, e⟩` from `Multiset.card_eq_two.1 (CG.card_infChar (CG.mk P) τ)`. Rewrite `hm`, `hnd`, `hint`, `hsum` using `[e]`. Take `⟨i, hi⟩` from `hint x (by simp)`. Take `⟨j, hj⟩` from `hint y (by simp)`.

Take `⟨c, k, hk, e'⟩` from `gap_of_sum (x := x) (y := y) (by simpa using hnd) (i := i) (j := j) (by rw [hi]; norm_num) (by rw [hj]; norm_num) (by simpa using hsum)`. Conclude with `⟨c, k, hk, e' ▸ hm⟩`.
-/
theorem UpperTheory.V.Z.Bc.gapTwo_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Bc.GapTwo := by
  intro _ F Ω _ _ _ _ _ _ l _ ι r P hreg hatt ⟨N, hN, hdet⟩ τ
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral F 2 P
  have hone : (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) ^ N = 1 := by
    refine PositivityTheory.jumpWindows.FiniteInfinitePlaceProduct.eq_one _ ?_
    filter_upwards [hatt.2] with w ⟨B, hB, hF⟩
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have h1 := PositivityTheory.jumpWindows.PSmo.val_eq_prod (CuspSub.hasCentral_iff.1 hω) hB
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have e3 := det_algSat _ _ _ _ e2
    have e4 : ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom).det := ι.toRingHom.map_det _
    have e5 := congrArg (fun u : (Qbar l)ˣ => ι (u : Qbar l)) (hdet σ⁻¹)
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, Matrix.GeneralLinearGroup.val_det_apply] at e5
    rw [e4, e3] at e5
    have e6 := (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (-1)).2.1 w
    refine Units.ext ?_
    have hp : ∀ ν : HChar F, (ν ^ N).val w = ν.val w ^ N := fun ν => MonoidHom.pow_apply ν.1 N _
    rw [hp, HChar.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, e6, h1, Multiset.prod_pair, Units.val_one, ← e5, mul_comm]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsum : ((CG.mk P).infChar τ).sum = 1 := by
    have h1 := GlobalTheory.BCT.TwistDisc.expo_pow (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) N τ
    have h2 := GlobalTheory.BCT.TwistDisc.expo_pow (1 : HChar F) 0 τ
    rw [pow_zero, Nat.cast_zero, zero_mul] at h2
    have h3 := (CG.hasInfChar_ofChar ω τ).twist (GlobalTheory.HeckeGal.Model.absPow F (-1))
    rw [CG.twist_ofChar, Multiset.map_singleton] at h3
    have h4 := h3.infChar_eq
    rw [CG.infChar_ofChar, Multiset.singleton_inj] at h4
    have h5 : expo (GlobalTheory.HeckeGal.Model.absPow F (-1)) τ = ((-1 : ℝ) : ℂ) := GlobalTheory.CuspRep.Model.expo_absC _ τ
    rw [hone, h2, h4, h5, expo_central hω (ParLaws.hasInfChar_infChar (CG.mk P) τ)] at h1
    have h6 := (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hN.ne')
    push_cast at h6
    linear_combination h6
  have hm : P.HasInfChar τ ((CG.mk P).infChar τ) := ParLaws.hasInfChar_infChar (CG.mk P) τ
  obtain ⟨hnd, hint⟩ := hreg τ
  obtain ⟨x, y, e⟩ := Multiset.card_eq_two.1 (CG.card_infChar (CG.mk P) τ)
  rw [e] at hm hnd hint hsum
  obtain ⟨i, hi⟩ := hint x (by simp)
  obtain ⟨j, hj⟩ := hint y (by simp)
  obtain ⟨c, k, hk, e'⟩ := gap_of_sum (x := x) (y := y) (by simpa using hnd) (i := i) (j := j) (by rw [hi]; norm_num)
    (by rw [hj]; norm_num) (by simpa using hsum)
  exact ⟨c, k, hk, e' ▸ hm⟩
end
