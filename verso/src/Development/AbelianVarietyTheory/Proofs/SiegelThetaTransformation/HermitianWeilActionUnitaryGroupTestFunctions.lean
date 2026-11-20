import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.QuadCocycle
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatRationalCoordsIntegralProportionalStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticOfUnitaryCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFnStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplecticStatement

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

namespace WeilAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Unfold `thH`. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem thH_smul (c : ℂ) (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    thH Ψ (c • φ) Z z z' = c * thH Ψ φ Z z z' := by
  unfold thH
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Establish `h1` using `((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N φ hφ Z hZ).1 z z').of_norm`. Establish `h2` using `((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ Z hZ).1 z z').of_norm`. Unfold `thH`. Rewrite using `[← h1.tsum_add h2]`. Use `tsum_congr fun x => ?_` and prove the remaining obligations.

Simplify using `only [Pi.add_apply, add_mul]`.
-/
theorem thH_add (hΨ : IsType Ψ) {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (z z' : CM Ψ n N) :
    thH Ψ (φ + ψ) Z z z' = thH Ψ φ Z z z' + thH Ψ ψ Z z z' := by
  have h1 := ((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N φ hφ Z hZ).1 z z').of_norm
  have h2 := ((GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ Z hZ).1 z z').of_norm
  unfold thH
  rw [← h1.tsum_add h2]
  refine tsum_congr fun x => ?_
  simp only [Pi.add_apply, add_mul]

/- English proof (translation)
Establish `hZ` using `Base.I_mem_Hn (N := N) Ψ`. Use `set Z : CM Ψ N N := fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) with hZdef`. Take `⟨hd, hA, -⟩` from `(unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ`. Use `(GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ _ hA).2 ψ' hψ' fun w w' => ?_` and prove the remaining obligations. Establish `u1 : ∀ τ, IsUnit (hDen Ψ γ Z τ).det` using `fun τ => (hd τ).1.isUnit`.

Establish `u2 : ∀ τ, IsUnit (hDen' Ψ γ Z τ).det` using `fun τ => by`. Use `Ne.isUnit fun h => (hd τ).1 ?_` and prove the remaining obligations. Rewrite using `[← (hd τ).2.1, h, zero_mul]`. Establish `e1` using `t Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k) (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)`. Establish `e2` using `t' Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k) (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)`.

Establish `a1 : (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ (Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k) k : CM Ψ n N) = w`. Use function extensionality and compare the values at `τ`. Use extensionality with `k i`. Express the relevant statement in the definitionally equal form `((hDen' Ψ γ Z τ)⁻¹ *ᵥ (hDen' Ψ γ Z τ *ᵥ w τ k)) i = _`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (u2 τ), Matrix.one_mulVec]`.

Establish `a2 : (fun τ => Matrix.of fun k => (Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ) k ᵥ* (hDen Ψ γ Z τ)⁻¹ : CM Ψ n N) = w'`. Use function extensionality and compare the values at `τ`. Use extensionality with `k i`. Express the relevant statement in the definitionally equal form `((w' τ k ᵥ* hDen Ψ γ Z τ) ᵥ* (hDen Ψ γ Z τ)⁻¹) i = _`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (u1 τ), Matrix.vecMul_one]`.

Establish `e` using `e1.trans e2.symm`. Use `beta_reduce at e`. Rewrite `e` using `[a1, a2]`. Conclude with `e`.
-/
theorem unique (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ ψ ψ' : Matrix (Fin n) (Fin N) E → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ')
    (t : TransH Ψ γ φ ψ) (t' : TransH Ψ γ φ ψ') : ψ = ψ' := by
  have hZ := Base.I_mem_Hn (N := N) Ψ
  set Z : CM Ψ N N := fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) with hZdef
  obtain ⟨hd, hA, -⟩ := (unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  refine (GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N ψ hψ _ hA).2 ψ' hψ' fun w w' => ?_
  have u1 : ∀ τ, IsUnit (hDen Ψ γ Z τ).det := fun τ => (hd τ).1.isUnit
  have u2 : ∀ τ, IsUnit (hDen' Ψ γ Z τ).det := fun τ => by
    refine Ne.isUnit fun h => (hd τ).1 ?_
    rw [← (hd τ).2.1, h, zero_mul]
  have e1 := t Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k)
    (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)
  have e2 := t' Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k)
    (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)
  have a1 : (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ
      (Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k) k : CM Ψ n N) = w := by
    funext τ
    ext k i
    change ((hDen' Ψ γ Z τ)⁻¹ *ᵥ (hDen' Ψ γ Z τ *ᵥ w τ k)) i = _
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (u2 τ), Matrix.one_mulVec]
  have a2 : (fun τ => Matrix.of fun k =>
      (Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ) k ᵥ* (hDen Ψ γ Z τ)⁻¹ : CM Ψ n N) = w' := by
    funext τ
    ext k i
    change ((w' τ k ᵥ* hDen Ψ γ Z τ) ᵥ* (hDen Ψ γ Z τ)⁻¹) i = _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (u1 τ), Matrix.vecMul_one]
  have e := e1.trans e2.symm
  beta_reduce at e
  rw [a1, a2] at e
  exact e

/- English proof (translation)
Take `⟨d, hd, h⟩` from `GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional E n N`. Use `⟨d, by exact_mod_cast hd.ne', fun φ ψ hφ hψ => ?_⟩` and prove the remaining obligations. Establish `h1 : IsSB fun x => conj (ψ x)` using `(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ ψ ψ hψ hψ).2.2.2.1`. Conclude with `h (fun x => φ x * conj (ψ x)) (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ _ hφ h1).2.2.1`.
-/
theorem ip_ofQ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ψ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB ψ →
      ip (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) (fun m => ψ (ofQ m)) = d * ip φ ψ := by
  obtain ⟨d, hd, h⟩ := GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional E n N
  refine ⟨d, by exact_mod_cast hd.ne', fun φ ψ hφ hψ => ?_⟩
  have h1 : IsSB fun x => conj (ψ x) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ ψ ψ hψ hψ).2.2.2.1
  exact h (fun x => φ x * conj (ψ x)) (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ _ hφ h1).2.2.1

/- English proof (translation)
Unfold `ip`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `: c * conj c = 1` using `by rw [Complex.mul_conj', hc]; simp`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`.

Take the linear combination `(φ x * conj (ψ x)) * this`.
-/
theorem ip_smul {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] {c : ℂ}
    (hc : ‖c‖ = 1) (φ ψ : Matrix κ ι K → ℂ) : ip (c • φ) (c • ψ) = ip φ ψ := by
  unfold ip
  congr 1
  funext x
  have : c * conj c = 1 := by rw [Complex.mul_conj', hc]; simp
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  linear_combination (φ x * conj (ψ x)) * this

/- English proof (translation)
Take `⟨hb, hS, -, hth, hsb⟩` from `thH_eq_thS_dictionary E Ψ hΨ n N`. Take `⟨σ, hσ, c, hc, hdict⟩` from `GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField E Ψ hΨ n N γ hγ`. Take `⟨ω, hω⟩` from `GlobalTheory.T.exists_weil_of_symplectic' (Fin n) (QI E N) σ (by simpa using hn) hσ`. Take `⟨d, hd, hip⟩` from `ip_ofQ E n N`. Set `e` to `Equiv.ofBijective _ hb`.

Set `V : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ` to `fun φ x => ω (fun m => φ (ofQ m)) (e.symm x)`. Establish `hV : ∀ φ, (fun m => V φ (ofQ m)) = ω fun m => φ (ofQ m)` using `fun φ => by`. Use function extensionality and compare the values at `m`. Conclude with `congrArg _ (e.symm_apply_apply m)`. Establish `hVsb : ∀ φ, IsSB φ → IsSB (V φ)` using `fun φ hφ => by`.

Rewrite using `[hsb, hV]`. Conclude with `(hω _ ((hsb φ).1 hφ)).1`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hc`.

Use `⟨fun φ => (c ^ (n / 2))⁻¹ • V φ, fun φ hφ => ⟨?_, ?_, fun φ' hφ' => ?_⟩⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hVsb φ hφ) (hVsb φ hφ)).2.1 _`. Introduce `Z hZ z z'`. Take `⟨h1, h2, h3⟩` from `hdict Z hZ`. Take `⟨h3, h4⟩` from `h3 z z'`.

Establish `key` using `(hω _ ((hsb φ).1 hφ)).2.1 _ (hS Z hZ) (zetaOf Ψ z z')`. Rewrite using `[thH_smul, hth, hth, hV, ← h1, h3, key, h2, Finset.sum_congr rfl fun k _ => h4 k, Fintype.card_fin, mul_pow, ← Finset.prod_pow, hFac, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]`. Establish `hp : ∀ τ : Ψ, ((hDen Ψ γ Z τ).det ^ 2) ^ (n / 2) = (hDen Ψ γ Z τ).det ^ n` using `fun τ => by`. Rewrite using `[← pow_mul, Nat.mul_div_cancel' hn.two_dvd]`. Simplify using `only [hp]`.

Use `pow_ne_zero (n / 2) hc0` as an intermediate fact. Rewrite using `[← mul_assoc (π * I : ℂ) 2, show (π * I * 2 : ℂ) = 2 * π * I by ring]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[ip_smul (by simp [hc])]`. Use `mul_left_cancel₀ hd ?_` and prove the remaining obligations.

Rewrite using `[← hip _ _ (hVsb φ hφ) (hVsb φ' hφ'), ← hip _ _ hφ hφ', hV, hV]`. Conclude with `(hω _ ((hsb φ).1 hφ)).2.2 _ ((hsb φ').1 hφ')`.
-/
theorem exists_op (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N) :
    ∃ W : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ, ∀ φ, IsSB φ →
      IsSB (W φ) ∧ TransH Ψ γ φ (W φ) ∧ ∀ φ', IsSB φ' → ip (W φ) (W φ') = ip φ φ' := by
  obtain ⟨hb, hS, -, hth, hsb⟩ := thH_eq_thS_dictionary E Ψ hΨ n N
  obtain ⟨σ, hσ, c, hc, hdict⟩ := GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField E Ψ hΨ n N γ hγ
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weil_of_symplectic' (Fin n) (QI E N) σ (by simpa using hn) hσ
  obtain ⟨d, hd, hip⟩ := ip_ofQ E n N
  let e := Equiv.ofBijective _ hb
  let V : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ := fun φ x =>
    ω (fun m => φ (ofQ m)) (e.symm x)
  have hV : ∀ φ, (fun m => V φ (ofQ m)) = ω fun m => φ (ofQ m) := fun φ => by
    funext m
    exact congrArg _ (e.symm_apply_apply m)
  have hVsb : ∀ φ, IsSB φ → IsSB (V φ) := fun φ hφ => by
    rw [hsb, hV]
    exact (hω _ ((hsb φ).1 hφ)).1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨fun φ => (c ^ (n / 2))⁻¹ • V φ, fun φ hφ => ⟨?_, ?_, fun φ' hφ' => ?_⟩⟩
  · exact (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hVsb φ hφ) (hVsb φ hφ)).2.1 _
  · intro Z hZ z z'
    obtain ⟨h1, h2, h3⟩ := hdict Z hZ
    obtain ⟨h3, h4⟩ := h3 z z'
    have key := (hω _ ((hsb φ).1 hφ)).2.1 _ (hS Z hZ) (zetaOf Ψ z z')
    rw [thH_smul, hth, hth, hV, ← h1, h3, key, h2, Finset.sum_congr rfl fun k _ => h4 k,
      Fintype.card_fin, mul_pow, ← Finset.prod_pow, hFac, Finset.prod_mul_distrib,
      ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    have hp : ∀ τ : Ψ, ((hDen Ψ γ Z τ).det ^ 2) ^ (n / 2) = (hDen Ψ γ Z τ).det ^ n := fun τ => by
      rw [← pow_mul, Nat.mul_div_cancel' hn.two_dvd]
    simp only [hp]
    have := pow_ne_zero (n / 2) hc0
    rw [← mul_assoc (π * I : ℂ) 2, show (π * I * 2 : ℂ) = 2 * π * I by ring]
    field_simp
  · rw [ip_smul (by simp [hc])]
    refine mul_left_cancel₀ hd ?_
    rw [← hip _ _ (hVsb φ hφ) (hVsb φ' hφ'), ← hip _ _ hφ hφ', hV, hV]
    exact (hω _ ((hsb φ).1 hφ)).2.2 _ ((hsb φ').1 hφ')

/- English proof (translation)
Take `⟨W, hW⟩` from `exists_op hΨ hn hγ`. Establish `h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ` using `⟨W φ, (hW φ hφ).1, (hW φ hφ).2.1⟩`. Rewrite using `[weil, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem weil_spec (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) :
    IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) := by
  obtain ⟨W, hW⟩ := exists_op hΨ hn hγ
  have h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ := ⟨W φ, (hW φ hφ).1, (hW φ hφ).2.1⟩
  rw [weil, dif_pos h]
  exact h.choose_spec

end WeilAct

open WeilAct in

/- English proof (translation)
Introduce `E _ _ _ Ψ hΨ n N hn γ hγ φ hφ`. Take `⟨s1, t1⟩` from `weil_spec hΨ hn hγ hφ`. Use `⟨s1, t1, fun ψ hψ t => unique hΨ hγ hψ s1 t t1, fun ψ hψ => ⟨?_, ?_⟩, fun c => ?_, fun γ' hγ' => ?_, ?_⟩` and prove the remaining obligations. Take `⟨s2, t2⟩` from `weil_spec hΨ hn hγ hψ`. Take `⟨W, hW⟩` from `exists_op (n := n) hΨ hn hγ`.

Rewrite using `[unique hΨ hγ s1 (hW φ hφ).1 t1 (hW φ hφ).2.1, unique hΨ hγ s2 (hW ψ hψ).1 t2 (hW ψ hψ).2.1]`. Conclude with `(hW φ hφ).2.2 ψ hψ`. Take `⟨s2, t2⟩` from `weil_spec hΨ hn hγ hψ`. Take `⟨s3, t3⟩` from `weil_spec hΨ hn hγ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ ψ hφ hψ).1`. Use `unique hΨ hγ s3 (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ s1 s2).1 t3 fun Z hZ z z' => ?_` and prove the remaining obligations.

Rewrite using `[thH_add hΨ s1 s2 ((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).2.1, thH_add hΨ hφ hψ hZ, t1 Z hZ, t2 Z hZ, mul_add]`. Take `⟨s3, t3⟩` from `weil_spec hΨ hn hγ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ φ hφ hφ).2.1 c)`. Use `unique hΨ hγ s3 ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ s1 s1).2.1 c) t3 fun Z hZ z z' => ?_` and prove the remaining obligations. Rewrite using `[thH_smul, thH_smul, t1 Z hZ, mul_left_comm]`. Establish `hm` using `(unitary_act_halfSpace E Ψ N γ hγ).1.2.2.2.2 γ' hγ'`.

Take `⟨s2, t2⟩` from `weil_spec hΨ hn hγ' s1`. Take `⟨s3, t3⟩` from `weil_spec hΨ hn hm hφ`. Conclude with `unique hΨ hm s3 s2 t3 ((transH_comp E Ψ n N γ γ' hγ hγ').2 _ _ _ t1 t2)`. Take `⟨s3, t3⟩` from `weil_spec hΨ hn Base.one_mem_UU hφ`. Conclude with `unique hΨ Base.one_mem_UU s3 hφ t3 (Base.transH_one Ψ φ)`.
-/
theorem weil_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ γ ∈ UU E N, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → TransH Ψ γ φ ψ → ψ = weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → ip (weil Ψ γ φ) (weil Ψ γ ψ) = ip φ ψ ∧ weil Ψ γ (φ + ψ) = weil Ψ γ φ + weil Ψ γ ψ) ∧ (∀ c : ℂ, weil Ψ γ (c • φ) = c • weil Ψ γ φ) ∧ (∀ γ' ∈ UU E N, weil Ψ (γ' * γ) φ = weil Ψ γ' (weil Ψ γ φ)) ∧ weil Ψ 1 φ = φ := by
  intro E _ _ _ Ψ hΨ n N hn γ hγ φ hφ
  obtain ⟨s1, t1⟩ := weil_spec hΨ hn hγ hφ
  refine ⟨s1, t1, fun ψ hψ t => unique hΨ hγ hψ s1 t t1, fun ψ hψ => ⟨?_, ?_⟩, fun c => ?_,
    fun γ' hγ' => ?_, ?_⟩
  · obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ hψ
    obtain ⟨W, hW⟩ := exists_op (n := n) hΨ hn hγ
    rw [unique hΨ hγ s1 (hW φ hφ).1 t1 (hW φ hφ).2.1,
      unique hΨ hγ s2 (hW ψ hψ).1 t2 (hW ψ hψ).2.1]
    exact (hW φ hφ).2.2 ψ hψ
  · obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ hψ
    obtain ⟨s3, t3⟩ := weil_spec hΨ hn hγ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ ψ hφ hψ).1
    refine unique hΨ hγ s3 (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ s1 s2).1 t3 fun Z hZ z z' => ?_
    rw [thH_add hΨ s1 s2 ((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).2.1, thH_add hΨ hφ hψ hZ,
      t1 Z hZ, t2 Z hZ, mul_add]
  · obtain ⟨s3, t3⟩ := weil_spec hΨ hn hγ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ φ hφ hφ).2.1 c)
    refine unique hΨ hγ s3 ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ s1 s1).2.1 c) t3 fun Z hZ z z' => ?_
    rw [thH_smul, thH_smul, t1 Z hZ, mul_left_comm]
  · have hm := (unitary_act_halfSpace E Ψ N γ hγ).1.2.2.2.2 γ' hγ'
    obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ' s1
    obtain ⟨s3, t3⟩ := weil_spec hΨ hn hm hφ
    exact unique hΨ hm s3 s2 t3 ((transH_comp E Ψ n N γ γ' hγ hγ').2 _ _ _ t1 t2)
  · obtain ⟨s3, t3⟩ := weil_spec hΨ hn Base.one_mem_UU hφ
    exact unique hΨ Base.one_mem_UU s3 hφ t3 (Base.transH_one Ψ φ)

end GlobalTheory.SW
