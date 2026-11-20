import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneScalarAvoidingMatrixEigenvaluesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorVacuumExactConstantEvenRankStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackSecondGroupRationalPointEqDetSmulStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatEqui

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]`. Simplify using the standard rewrite rules.
-/
theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

/- English proof (translation)
Distinguish the cases in `h : 1 + u = 0`. Establish `hs : D.host.sqrtMinusD ≠ 0`. Introduce `h0`. Use `D.host.sqrtMinusD_sq` as an intermediate fact. Rewrite `this` using `[h0]`.

Establish `hd : (D.host.d : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 D.host.hyp.2.1.ne_zero`. Conclude with `hd (by linear_combination this)`. Use `⟨Units.mk0 _ hs, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, D.host.conj_sqrtMinusD]`. Take the linear combination `D.host.sqrtMinusD * h`.

Use `⟨Units.mk0 _ h, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, map_add, map_one]`. Take the linear combination `-hu`.
-/
theorem exists_root (D : D7) (u : D.host.E) (hu : u * D.host.conj u = 1) :
    ∃ b : D.host.Eˣ, (b : D.host.E) = u * D.host.conj b := by
  by_cases h : 1 + u = 0
  · have hs : D.host.sqrtMinusD ≠ 0 := by
      intro h0
      have := D.host.sqrtMinusD_sq
      rw [h0] at this
      have hd : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 D.host.hyp.2.1.ne_zero
      exact hd (by linear_combination this)
    refine ⟨Units.mk0 _ hs, ?_⟩
    rw [Units.val_mk0, D.host.conj_sqrtMinusD]
    linear_combination D.host.sqrtMinusD * h
  · refine ⟨Units.mk0 _ h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination -hu

/- English proof (translation)
Rewrite using `[Units.val_zpow_eq_zpow_val, eq_inv_of_mul_eq_one_left (χ.aut b), inv_zpow, ← Finset.prod_zpow, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_mul, mul_comm, ← hk, zpow_mul, zpow_neg]`. Use `congr 2`. Establish `h0 : embT D τ b ≠ 0` using `(map_ne_zero _).2 b.ne_zero`.

Establish `h1` using `congrArg (embT D τ) hb`. Rewrite `h1` using `[map_mul, embT_conj]`. Establish `h2 : (starRingEnd ℂ) (embT D τ b) ≠ 0` using `(map_ne_zero _).2 h0`. Rewrite using `[zpow_ofNat, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h0, div_eq_iff h2]`. Conclude with `h1`.
-/
theorem char_value {D : D7} {N : ℕ} (χ : HeckeU D N) (ep : ℤ) (u : D.host.E) (b : D.host.Eˣ)
    (hb : (b : D.host.E) = u * D.host.conj b) (k : D.what₂.Tau → ℤ) (hk : ∀ τ, 2 * k τ = ep * χ.n τ) :
    ((χ.f (Units.map (inc D).toMonoidHom b) ^ ep : ℂˣ) : ℂ) = ∏ τ, embT D τ u ^ (-(k τ)) := by
  rw [Units.val_zpow_eq_zpow_val, eq_inv_of_mul_eq_one_left (χ.aut b), inv_zpow, ← Finset.prod_zpow,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm, ← hk, zpow_mul, zpow_neg]
  congr 2
  have h0 : embT D τ b ≠ 0 := (map_ne_zero _).2 b.ne_zero
  have h1 := congrArg (embT D τ) hb
  rw [map_mul, embT_conj] at h1
  have h2 : (starRingEnd ℂ) (embT D τ b) ≠ 0 := (map_ne_zero _).2 h0
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h0, div_eq_iff h2]
  exact h1

/- English proof (translation)
Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_one]`. Rewrite using `[← this]`. Use `congr 1`. Conclude with `RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ`.
-/
theorem det_norm {D : D7} {n : ℕ} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : γ * (γ.map D.host.conj).transpose = 1) : γ.det * D.host.conj γ.det = 1 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [← this]
  congr 1
  exact RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ

/- English proof (translation)
Use `ext`. Express the relevant statement in the definitionally equal form `inc D b = (g : Matrix (Fin n) (Fin n) (AE D)).det * sgA D (inc D b)`. Rewrite using `[GlobalTheory.NormSum.PtsMem.sgA_inc, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_mul, ← hb]`.
-/
theorem det_root {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : IsRat D g γ) (b : D.host.Eˣ) (hb : (b : D.host.E) = γ.det * D.host.conj b) :
    Units.map (inc D).toMonoidHom b =
      Matrix.GeneralLinearGroup.det g * sgU D (Units.map (inc D).toMonoidHom b) := by
  ext
  change inc D b = (g : Matrix (Fin n) (Fin n) (AE D)).det * sgA D (inc D b)
  rw [GlobalTheory.NormSum.PtsMem.sgA_inc, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_mul, ← hb]

/- English proof (translation)
Unfold `IsRat`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Both sides reduce to the same expression.
-/
theorem isRat_one (D : D7) (n : ℕ) : IsRat D ((1 : GA D n) : GL (Fin n) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

/- English proof (translation)
Take `⟨Lt, h1, h2, -⟩` from `GlobalTheory.NormSum.exists_lattice_of_adelic_point D n`. Conclude with `h2 ▸ (h1 1).1`.
-/
theorem moves_one (D : D7) (n : ℕ) : Moves D ((1 : GA D n) : GL (Fin n) (AE D)) (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
  exact h2 ▸ (h1 1).1

/- English proof (translation)
Take `⟨-, -, hex, hun, -⟩` from `GlobalTheory.NormSum.mem_ratG_intG D n`. Take `⟨z, hz, hz1, hdet⟩` from `GlobalTheory.T.exists_normOne_scalar_avoiding_matrix_eigenvalues D n γ`. Establish `hγ` using `hun g γ h`. Take `⟨g₁, hg₁⟩` from `hex (z • γ) (by`. Establish `: (z • γ).map D.host.conj = D.host.conj z • γ.map D.host.conj`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hγ, smul_smul, hz, one_smul])`. Take `⟨g₂, hg₂⟩` from `hex (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) (by`. Establish `: (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)).map D.host.conj = z • 1`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij, conj_conj]`. Rewrite using `[this, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_one, Matrix.mul_one, smul_smul, mul_comm, hz, one_smul])`. Establish `e : γ = (z • γ) * (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E))`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hz, one_smul]`.

Use `⟨g₁, g₂, _, _, hg₁, hg₂, ?_, e, hdet, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Unfold `IsRat at h hg₁ hg₂`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, h, hg₁, hg₂, ← Matrix.map_mul, ← e]`.

Rewrite using `[show (1 : Matrix (Fin n) (Fin n) D.host.E) - D.host.conj z • 1 = (1 - D.host.conj z) • 1 by`. Rewrite using `[sub_smul, one_smul], Matrix.det_smul, Matrix.det_one, mul_one]`. Use `pow_ne_zero _ (sub_ne_zero.2 fun h1 => hz1 ?_)` and prove the remaining obligations. Rewrite using `[← conj_conj D z, ← h1, map_one]`.
-/
theorem exists_factor {D : D7} {n : ℕ} (g : GA D n) (γ : Matrix (Fin n) (Fin n) D.host.E)
    (h : IsRat D (g : GL (Fin n) (AE D)) γ) :
    ∃ (g₁ g₂ : GA D n) (γ₁ γ₂ : Matrix (Fin n) (Fin n) D.host.E), IsRat D (g₁ : GL (Fin n) (AE D)) γ₁ ∧
      IsRat D (g₂ : GL (Fin n) (AE D)) γ₂ ∧ g = g₁ * g₂ ∧ γ = γ₁ * γ₂ ∧ (1 - γ₁).det ≠ 0 ∧ (1 - γ₂).det ≠ 0 := by
  obtain ⟨-, -, hex, hun, -⟩ := GlobalTheory.NormSum.mem_ratG_intG D n
  obtain ⟨z, hz, hz1, hdet⟩ := GlobalTheory.T.exists_normOne_scalar_avoiding_matrix_eigenvalues D n γ
  have hγ := hun g γ h
  obtain ⟨g₁, hg₁⟩ := hex (z • γ) (by
    have : (z • γ).map D.host.conj = D.host.conj z • γ.map D.host.conj := by
      ext i j; simp
    rw [this, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hγ, smul_smul, hz, one_smul])
  obtain ⟨g₂, hg₂⟩ := hex (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) (by
    have : (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)).map D.host.conj = z • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, conj_conj]
    rw [this, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_one, Matrix.mul_one,
      smul_smul, mul_comm, hz, one_smul])
  have e : γ = (z • γ) * (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hz, one_smul]
  refine ⟨g₁, g₂, _, _, hg₁, hg₂, ?_, e, hdet, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    unfold IsRat at h hg₁ hg₂
    rw [Subgroup.coe_mul, Units.val_mul, h, hg₁, hg₂, ← Matrix.map_mul, ← e]
  · rw [show (1 : Matrix (Fin n) (Fin n) D.host.E) - D.host.conj z • 1 = (1 - D.host.conj z) • 1 by
      rw [sub_smul, one_smul], Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ (sub_ne_zero.2 fun h1 => hz1 ?_)
    rw [← conj_conj D z, ← h1, map_one]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ}

def IsPull (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (a : ℂ) : Prop :=
  ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om g g' F = fun z => a * pull D (tor0 D cc δ) γ γ' F z

/- English proof (translation)
Introduce `F hF`. Rewrite using `[W.mul _ _ _ _ F hF, h₁ _ (W.maps _ _ F hF), h₂ F hF]`. Use function extensionality and compare the values at `z`. Simplify using `only [pull_eq, mulV_mulV, adj_mul, mul_assoc]`.
-/
theorem IsPull.mul {W : WeilO D cc δ N N' e0} {g₁ g₂ : GA D N} {g₁' g₂' : GA D N'}
    {γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E} {γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E} {a₁ a₂ : ℂ}
    (h₁ : IsPull W g₁ g₁' γ₁ γ₁' a₁) (h₂ : IsPull W g₂ g₂' γ₂ γ₂' a₂) :
    IsPull W (g₁ * g₂) (g₁' * g₂') (γ₁ * γ₂) (γ₁' * γ₂') (a₁ * a₂) := by
  intro F hF
  rw [W.mul _ _ _ _ F hF, h₁ _ (W.maps _ _ F hF), h₂ F hF]
  funext z
  simp only [pull_eq, mulV_mulV, adj_mul, mul_assoc]

/- English proof (translation)
Establish `key : ∀ (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E), IsRat D (g : GL (Fin N) (AE D)) γ → (1 - γ).det ≠ 0 → IsPull W g 1 γ 1 (∏ τ, embT D τ γ.det ^ (-(a τ)))`. Introduce `g γ h hdet`. Take `⟨Lt, hLt, -⟩` from `GlobalTheory.NormSum.exists_lattice_of_adelic_point D N`. Establish `hu` using `det_norm ((GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 g γ h)`. Take `⟨b, hb⟩` from `exists_root D _ hu`.

Use `GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum D cc δ hc N N' e0 he (GlobalTheory.T.theta_span_rational_translates_vacuum D cc δ hc N N' e0 he W.nz) W g 1 γ 1 _ h (isRat_one D N') ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.weilOperator_vacuum_exact_constant_evenRank D cc δ hc N N' hN hN' e0 he W g 1 _ 1 (Lt g) (stdL D N') (det_root h b hb) (by simp) (hLt g).1 (moves_one D N'), GlobalTheory.T.thetaPullback_firstGroup_rationalPoint_eq_smul D cc δ hc N N' hN hN' e0 he g γ (Lt g) h hdet …`. Use function extensionality and compare the values at `z`. Rewrite using `[map_one, one_zpow, one_mul, char_value W.chV' W.ep' γ.det b hb (fun τ => a τ + ((N' / 2 : ℕ) : ℤ)) (fun τ => by have := ha τ; obtain ⟨k, hk⟩ := hN'; omega), Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[neg_add, zpow_add₀ ((map_ne_zero _).2 (left_ne_zero_of_mul_eq_one hu))]`. Take `⟨g₁, g₂, γ₁, γ₂, h₁, h₂, rfl, rfl, d₁, d₂⟩` from `exists_factor g γ h`. Use `(key g₁ γ₁ h₁ d₁).mul (key g₂ γ₂ h₂ d₂)` as an intermediate fact. Simplify `this` using `only [mul_one, ← Finset.prod_mul_distrib, ← mul_zpow, ← map_mul, ← Matrix.det_mul]`.
-/
theorem isPull_row (hc : Crv D cc δ) (hN : Even N) (hN' : Even N')
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) (a : D.what₂.Tau → ℤ)
    (ha : ∀ τ, 2 * a τ = W.ep' * W.chV'.n τ - (N' : ℤ)) (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : IsRat D (g : GL (Fin N) (AE D)) γ) : IsPull W g 1 γ 1 (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
  have key : ∀ (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E), IsRat D (g : GL (Fin N) (AE D)) γ →
      (1 - γ).det ≠ 0 → IsPull W g 1 γ 1 (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
    intro g γ h hdet
    obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    have hu := det_norm ((GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 g γ h)
    obtain ⟨b, hb⟩ := exists_root D _ hu
    refine GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum D cc δ hc N N' e0 he (GlobalTheory.T.theta_span_rational_translates_vacuum D cc δ hc N N' e0 he W.nz) W g 1 γ 1 _ h
      (isRat_one D N') ?_
    rw [GlobalTheory.T.weilOperator_vacuum_exact_constant_evenRank D cc δ hc N N' hN hN' e0 he W g 1 _ 1 (Lt g) (stdL D N') (det_root h b hb) (by simp)
      (hLt g).1 (moves_one D N'), GlobalTheory.T.thetaPullback_firstGroup_rationalPoint_eq_smul D cc δ hc N N' hN hN' e0 he g γ (Lt g) h hdet (hLt g).1]
    funext z
    rw [map_one, one_zpow, one_mul, char_value W.chV' W.ep' γ.det b hb (fun τ => a τ + ((N' / 2 : ℕ) : ℤ))
      (fun τ => by have := ha τ; obtain ⟨k, hk⟩ := hN'; omega), Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [neg_add, zpow_add₀ ((map_ne_zero _).2 (left_ne_zero_of_mul_eq_one hu))]
  obtain ⟨g₁, g₂, γ₁, γ₂, h₁, h₂, rfl, rfl, d₁, d₂⟩ := exists_factor g γ h
  have := (key g₁ γ₁ h₁ d₁).mul (key g₂ γ₂ h₂ d₂)
  simpa only [mul_one, ← Finset.prod_mul_distrib, ← mul_zpow, ← map_mul, ← Matrix.det_mul] using this

/- English proof (translation)
Establish `key : ∀ (g : GA D N') (γ : Matrix (Fin N') (Fin N') D.host.E), IsRat D (g : GL (Fin N') (AE D)) γ → (1 - γ).det ≠ 0 → IsPull W 1 g 1 γ (∏ τ, embT D τ γ.det ^ (-(a τ)))`. Introduce `g γ h hdet`. Take `⟨Lt, hLt, -⟩` from `GlobalTheory.NormSum.exists_lattice_of_adelic_point D N'`. Establish `hu` using `det_norm ((GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 g γ h)`. Take `⟨b, hb⟩` from `exists_root D _ hu`.

Use `GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum D cc δ hc N N' e0 he (GlobalTheory.T.theta_span_rational_translates_vacuum D cc δ hc N N' e0 he W.nz) W 1 g 1 γ _ (isRat_one D N) h ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.weilOperator_vacuum_exact_constant_evenRank D cc δ hc N N' hN hN' e0 he W 1 g 1 _ (stdL D N) (Lt g) (by simp) (det_root h b hb) (moves_one D N) (hLt g).1, GlobalTheory.T.thetaPullback_secondGroup_rationalPoint_eq_det_smul D cc δ hc N N' hN hN' e0 he g γ (Lt g) h h …`. Use function extensionality and compare the values at `z`. Rewrite using `[map_one, one_zpow, mul_one, char_value W.chV W.ep γ.det b hb (fun τ => a τ - ((N / 2 : ℕ) : ℤ)) (fun τ => by have := ha τ; obtain ⟨k, hk⟩ := hN; omega), Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[neg_sub', sub_neg_eq_add, zpow_add₀ ((map_ne_zero _).2 (left_ne_zero_of_mul_eq_one hu)), zpow_natCast]`. Take `⟨g₁, g₂, γ₁, γ₂, h₁, h₂, rfl, rfl, d₁, d₂⟩` from `exists_factor g γ h`. Use `(key g₁ γ₁ h₁ d₁).mul (key g₂ γ₂ h₂ d₂)` as an intermediate fact. Simplify `this` using `only [mul_one, ← Finset.prod_mul_distrib, ← mul_zpow, ← map_mul, ← Matrix.det_mul]`.
-/
theorem isPull_col (hc : Crv D cc δ) (hN : Even N) (hN' : Even N')
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) (a : D.what₂.Tau → ℤ)
    (ha : ∀ τ, 2 * a τ = W.ep * W.chV.n τ + (N : ℤ)) (g : GA D N') (γ : Matrix (Fin N') (Fin N') D.host.E)
    (h : IsRat D (g : GL (Fin N') (AE D)) γ) : IsPull W 1 g 1 γ (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
  have key : ∀ (g : GA D N') (γ : Matrix (Fin N') (Fin N') D.host.E), IsRat D (g : GL (Fin N') (AE D)) γ →
      (1 - γ).det ≠ 0 → IsPull W 1 g 1 γ (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
    intro g γ h hdet
    obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N'
    have hu := det_norm ((GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 g γ h)
    obtain ⟨b, hb⟩ := exists_root D _ hu
    refine GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum D cc δ hc N N' e0 he (GlobalTheory.T.theta_span_rational_translates_vacuum D cc δ hc N N' e0 he W.nz) W 1 g 1 γ _
      (isRat_one D N) h ?_
    rw [GlobalTheory.T.weilOperator_vacuum_exact_constant_evenRank D cc δ hc N N' hN hN' e0 he W 1 g 1 _ (stdL D N) (Lt g) (by simp) (det_root h b hb)
      (moves_one D N) (hLt g).1, GlobalTheory.T.thetaPullback_secondGroup_rationalPoint_eq_det_smul D cc δ hc N N' hN hN' e0 he g γ (Lt g) h hdet (hLt g).1]
    funext z
    rw [map_one, one_zpow, mul_one, char_value W.chV W.ep γ.det b hb (fun τ => a τ - ((N / 2 : ℕ) : ℤ))
      (fun τ => by have := ha τ; obtain ⟨k, hk⟩ := hN; omega), Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [neg_sub', sub_neg_eq_add, zpow_add₀ ((map_ne_zero _).2 (left_ne_zero_of_mul_eq_one hu)), zpow_natCast]
  obtain ⟨g₁, g₂, γ₁, γ₂, h₁, h₂, rfl, rfl, d₁, d₂⟩ := exists_factor g γ h
  have := (key g₁ γ₁ h₁ d₁).mul (key g₂ γ₂ h₂ d₂)
  simpa only [mul_one, ← Finset.prod_mul_distrib, ← mul_zpow, ← map_mul, ← Matrix.det_mul] using this

/- English proof (translation)
Introduce `D cc δ hc t0 _ N N' hN hN' e0 he W γA γA' γ γ' a a' h h' ha' ha`. Use `(isPull_row hc hN hN' he.1 W a ha γA γ h).mul (isPull_col hc hN hN' he.1 W a' ha' γA' γ' h')` as an intermediate fact. Rewrite `this` using `[mul_one, one_mul, mul_one, one_mul, ← Finset.prod_mul_distrib]`. Conclude with `this`.
-/
theorem oddEq_of_even : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ N N' : ℕ, Even N → Even N' → ∀ e0 : VC D N N' → ℂ, oddE0 D cc δ t0 N N' e0 → oddEq D cc δ N N' e0 := by
  intro D cc δ hc t0 _ N N' hN hN' e0 he W γA γA' γ γ' a a' h h' ha' ha
  have := (isPull_row hc hN hN' he.1 W a ha γA γ h).mul (isPull_col hc hN hN' he.1 W a' ha' γA' γ' h')
  rw [mul_one, one_mul, mul_one, one_mul, ← Finset.prod_mul_distrib] at this
  exact this

end GlobalTheory.RatEqui
