import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.CompactStab

open scoped ComplexOrder

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Establish `hJ` using `Formalism.REAL.Jm_mul_self ε`. Use `set J := Formalism.REAL.Jm ε with hJd`. Establish `h1 : (J * hᴴ * J) * h = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, hJ]`. Establish `h2 : h * (J * hᴴ * J) = 1` using `mul_eq_one_comm.1 h1`.

Establish `h3 : h * J * hᴴ = J`. Combine the equalities or inequalities in the displayed calculation. Use `set P := hᴴ * h with hP`. Establish `hPh : Pᴴ = P` using `by rw [hP, conjTranspose_mul, conjTranspose_conjTranspose]`. Establish `hb' : ∀ j k, ε j ≠ ε k → P j k = 0`.

Introduce `j k hjk`. Break down `hb j k hjk with h0 | h0` into its components or cases. Conclude with `h0`. Rewrite using `[← hPh, conjTranspose_apply, h0, star_zero]`. Establish `hc : P * J = J * P`.

Use extensionality with `j k`. Simplify using `only [hJd, Formalism.REAL.Jm, mul_diagonal, diagonal_mul]`. Distinguish the cases in `hjk : ε j = ε k`. Rewrite using `[hjk, mul_comm]`. Simplify using `[hb' j k hjk]`.

Establish `h4 : P * J * P = J`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : P * P = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h6 : IsUnit (1 + P)` using `(Matrix.PosDef.add_posSemidef Matrix.PosDef.one (Matrix.posSemidef_conjTranspose_mul_self h)).isUnit`.

Establish `h7 : P = 1`. Apply `h6.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[add_mul, h5, one_mul, mul_one, add_comm]`. Use `⟨Matrix.mem_unitaryGroup_iff'.2 h7, ?_⟩` and prove the remaining obligations. Establish `h8 : h * hᴴ = 1` using `mul_eq_one_comm.1 h7`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mem_kset_of_block {h : Matrix (Fin n) (Fin n) ℂ} (hh : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε)
    (hb : ∀ j k, ε j ≠ ε k → (hᴴ * h) j k = 0 ∨ (hᴴ * h) k j = 0) : h ∈ Formalism.REAL.Kset ε := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  set J := Formalism.REAL.Jm ε with hJd
  have h1 : (J * hᴴ * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, hJ]
  have h2 : h * (J * hᴴ * J) = 1 := mul_eq_one_comm.1 h1
  have h3 : h * J * hᴴ = J := by
    calc h * J * hᴴ = h * J * hᴴ * (J * J) := by rw [hJ, Matrix.mul_one]
      _ = (h * (J * hᴴ * J)) * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h2, Matrix.one_mul]
  set P := hᴴ * h with hP
  have hPh : Pᴴ = P := by rw [hP, conjTranspose_mul, conjTranspose_conjTranspose]
  have hb' : ∀ j k, ε j ≠ ε k → P j k = 0 := by
    intro j k hjk
    rcases hb j k hjk with h0 | h0
    · exact h0
    · rw [← hPh, conjTranspose_apply, h0, star_zero]
  have hc : P * J = J * P := by
    ext j k
    simp only [hJd, Formalism.REAL.Jm, mul_diagonal, diagonal_mul]
    by_cases hjk : ε j = ε k
    · rw [hjk, mul_comm]
    · simp [hb' j k hjk]
  have h4 : P * J * P = J := by
    calc P * J * P = hᴴ * (h * J * hᴴ) * h := by simp only [hP, Matrix.mul_assoc]
      _ = J := by rw [h3, hh]
  have h5 : P * P = 1 := by
    calc P * P = (J * J) * P * P := by rw [hJ, Matrix.one_mul]
      _ = J * (P * J * P) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h4, hJ]
  have h6 : IsUnit (1 + P) :=
    (Matrix.PosDef.add_posSemidef Matrix.PosDef.one (Matrix.posSemidef_conjTranspose_mul_self h)).isUnit
  have h7 : P = 1 := by
    apply h6.mul_left_cancel
    rw [add_mul, h5, one_mul, mul_one, add_comm]
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 h7, ?_⟩
  have h8 : h * hᴴ = 1 := mul_eq_one_comm.1 h7
  calc h * J = h * (hᴴ * J * h) := by rw [hh]
    _ = (h * hᴴ) * J * h := by simp only [Matrix.mul_assoc]
    _ = J * h := by rw [h8, Matrix.one_mul]

/- English proof (translation)
Establish `h1 : (Complex.I • Formalism.REAL.Jm ε)ᴴ = -(Complex.I • Formalism.REAL.Jm ε)`. Rewrite using `[conjTranspose_smul, Formalism.REAL.Jm_conjTranspose]`. Simplify using the standard rewrite rules. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, h1, star_trivial, smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • (Complex.I • Formalism.REAL.Jm ε))).neg_right, add_neg_cancel, NormedSpace.exp_zero]`.

Conclude with `(((Commute.refl (Formalism.REAL.Jm ε)).smul_left _).smul_left t).exp_left`.
-/
theorem exp_iJ_mem (t : ℝ) : NormedSpace.exp (t • (Complex.I • Formalism.REAL.Jm ε)) ∈ Formalism.REAL.Kset ε := by
  have h1 : (Complex.I • Formalism.REAL.Jm ε)ᴴ = -(Complex.I • Formalism.REAL.Jm ε) := by
    rw [conjTranspose_smul, Formalism.REAL.Jm_conjTranspose]; simp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, h1,
      star_trivial, smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • (Complex.I • Formalism.REAL.Jm ε))).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  · exact (((Commute.refl (Formalism.REAL.Jm ε)).smul_left _).smul_left t).exp_left

/- English proof (translation)
Establish `hb : a⁻¹ = b` using `Matrix.inv_eq_right_inv hab`. Establish `ha : IsUnit a` using `IsUnit.of_mul_eq_one b hab`. Rewrite using `[← hb, ← Matrix.exp_conj _ _ ha, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem exp_conj_of_mul {a b X : Matrix (Fin n) (Fin n) ℂ} (hab : a * b = 1) (t : ℝ) :
    NormedSpace.exp (t • (a * X * b)) = a * NormedSpace.exp (t • X) * b := by
  have hb : a⁻¹ = b := Matrix.inv_eq_right_inv hab
  have ha : IsUnit a := IsUnit.of_mul_eq_one b hab
  rw [← hb, ← Matrix.exp_conj _ _ ha, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `ht : Filter.Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) • (f t - f 0)) (nhdsWithin 0 {0}ᶜ) (nhds v)`. Rewrite using `[tendsto_pi_nhds]`. Introduce `z`. Use `hasDerivAt_iff_tendsto_slope.1 (hd z)` as an intermediate fact. Use `this.congr fun t => ?_` and prove the remaining obligations.

Simplify using `[slope]`. Conclude with `F.closed_of_finiteDimensional.mem_of_tendsto ht (Filter.Eventually.of_forall fun t => F.smul_mem _ (F.sub_mem (hf t) (hf 0)))`.
-/
theorem deriv_mem {Z : Type} (F : Submodule ℂ (Z → ℂ)) [FiniteDimensional ℂ F] {f : ℝ → Z → ℂ} {v : Z → ℂ}
    (hf : ∀ t, f t ∈ F) (hd : ∀ z, HasDerivAt (fun t => f t z) (v z) 0) : v ∈ F := by
  have ht : Filter.Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) • (f t - f 0)) (nhdsWithin 0 {0}ᶜ) (nhds v) := by
    rw [tendsto_pi_nhds]
    intro z
    have := hasDerivAt_iff_tendsto_slope.1 (hd z)
    refine this.congr fun t => ?_
    simp [slope]
  exact F.closed_of_finiteDimensional.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun t => F.smul_mem _ (F.sub_mem (hf t) (hf 0)))

/- English proof (translation)
Introduce `n ε fr G σ Z _ pt R L hfr hG hinj hR1 hmul hder hK hgrow g hg φ φ' hφ hφ'`. Establish `hJ` using `Formalism.REAL.Jm_mul_self ε`. Establish `hJh` using `Formalism.REAL.Jm_conjTranspose ε`. Use `set J := Formalism.REAL.Jm ε with hJd`. Establish `hdet` using `(Matrix.isUnit_iff_isUnit_det fr).1 hfr`.

Establish `f1 : fr * fr⁻¹ = 1` using `Matrix.mul_nonsing_inv fr hdet`. Establish `f2 : fr⁻¹ * fr = 1` using `Matrix.nonsing_inv_mul fr hdet`. Establish `f1' : ∀ x : Matrix (Fin n) (Fin n) ℂ, fr * (fr⁻¹ * x) = x` using `fun x => by`. Rewrite using `[← Matrix.mul_assoc, f1, Matrix.one_mul]`. Establish `f2' : ∀ x : Matrix (Fin n) (Fin n) ℂ, fr⁻¹ * (fr * x) = x` using `fun x => by`.

Rewrite using `[← Matrix.mul_assoc, f2, Matrix.one_mul]`. Establish `f3' : ∀ x : Matrix (Fin n) (Fin n) ℂ, (fr⁻¹)ᴴ * (frᴴ * x) = x` using `fun x => by`. Rewrite using `[← Matrix.mul_assoc, ← conjTranspose_mul, f1, conjTranspose_one, Matrix.one_mul]`. Establish `J' : ∀ x : Matrix (Fin n) (Fin n) ℂ, J * (J * x) = x` using `fun x => by`. Rewrite using `[← Matrix.mul_assoc, hJ, Matrix.one_mul]`.

Establish `cU : ∀ x : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → fr⁻¹ * x * fr ∈ Formalism.QuantumDeterminants.UH G`. Introduce `x hx`. Use `show (fr⁻¹ * x * fr)ᴴ * G * (fr⁻¹ * x * fr) = G`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [← hG, conjTranspose_mul, Matrix.mul_assoc, f1', f3']`.

Use `_ = G := by rw [hx, hG]`. Take `⟨h, rfl⟩ : ∃ h, g = fr⁻¹ * h * fr` from `⟨fr * g * fr⁻¹, by simp only [Matrix.mul_assoc, f2', f2, Matrix.mul_one]⟩`. Establish `hh : hᴴ * J * h = J`. Establish `e : (fr⁻¹ * h * fr)ᴴ * G * (fr⁻¹ * h * fr) = G` using `hg`. Establish `e2` using `congrArg (fun x => (fr⁻¹)ᴴ * x * fr⁻¹) e`.

Simplify `e2` using `only [← hG, conjTranspose_mul, Matrix.mul_assoc, f1', f3', f1, Matrix.mul_one]`. Use `⟨h, mem_kset_of_block hh ?_, rfl⟩` and prove the remaining obligations. Use `set h' := J * hᴴ * J with hh'`. Establish `h1 : h' * h = 1`. Rewrite using `[hh', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, hJ]`.

Establish `h2 : h * h' = 1` using `mul_eq_one_comm.1 h1`. Establish `h3 : h'ᴴ * J * h' = J`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hh', conjTranspose_mul, hJh, conjTranspose_conjTranspose, Matrix.mul_assoc, J']`. Use `_ = J := by rw [h2, Matrix.mul_one]`.

Establish `hY' : h' * (Complex.I • J) * h = Complex.I • (J * (hᴴ * h))`. Simplify using `only [hh', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, J']`. Use `set Y := fr⁻¹ * (h' * (Complex.I • J) * h) * fr with hY`. Establish `hYG : Yᴴ * G + G * Y = 0`. Rewrite using `[hY, hY']`.

Simplify using `only [← hG, conjTranspose_mul, conjTranspose_smul, hJh, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, J', f1', f3']`. Simplify using the standard rewrite rules. Establish `cm : ∀ x y : Matrix (Fin n) (Fin n) ℂ, (fr⁻¹ * x * fr) * (fr⁻¹ * y * fr) = fr⁻¹ * (x * y) * fr`. Introduce `x y`. Simplify using `only [Matrix.mul_assoc, f1']`.

Establish `cR : ∀ x y : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → yᴴ * J * y = J → R (fr⁻¹ * (x * y) * fr) = R (fr⁻¹ * x * fr) * R (fr⁻¹ * y * fr)`. Introduce `x y hx hy`. Rewrite using `[← cm, hmul _ (cU x hx) _ (cU y hy)]`. Establish `kU : ∀ k ∈ Formalism.REAL.Kset ε, kᴴ * J * k = J`. Introduce `k hk`.

Establish `e1 : kᴴ * k = 1` using `Matrix.mem_unitaryGroup_iff'.1 hk.1`. Establish `e2 : k * J = J * k` using `hk.2`. Rewrite using `[Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, e1, Matrix.one_mul]`. Establish `mU : ∀ x y : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → yᴴ * J * y = J → (x * y)ᴴ * J * (x * y) = J`. Introduce `x y hx hy`.

Combine the equalities or inequalities in the displayed calculation. Set `F₀ : Submodule ℂ (Z → ℂ)` to `(MvPolynomial.restrictTotalDegree σ ℂ φ'.totalDegree).map (R (fr⁻¹ * h' * fr) ∘ₗ pt)`. Establish `: FiniteDimensional ℂ F₀` using `inferInstance`. Establish `m0 : pt φ ∈ F₀`. Use `⟨φ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, hφ', ← Module.End.mul_apply, ← cR _ _ h3 hh, h1, Matrix.mul_one, f2, hR1, Module.End.one_apply]`. Establish `st : ∀ (t : ℝ), ∀ v ∈ F₀, R (NormedSpace.exp (t • Y)) v ∈ F₀`. Introduce and unpack `t _ ⟨ψ, hψ, rfl⟩`. Establish `hk` using `exp_iJ_mem (ε := ε) t`. Take `⟨ψ', hd, he⟩` from `hK _ hk ψ`.

Use `⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hd.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hψ)), ?_⟩` and prove the remaining obligations. Rewrite using `[hY, exp_conj_of_mul f2, exp_conj_of_mul h1, LinearMap.comp_apply, LinearMap.comp_apply, ← he, ← Module.End.mul_apply, ← Module.End.mul_apply, ← cR _ _ h3 (kU _ hk), ← cR _ _ (mU _ _ (mU _ _ h3 (kU _ hk)) hh) h3, Matrix.mul_assoc _ h, h2, Matrix.mul_one]`. Establish `hm : ∀ m : ℕ, (L Y ^ m) φ ∈ F₀.comap pt`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => exact m0`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `deriv_mem F₀ (fun t => st t _ ih) (hder Y hYG _)`. Establish `hF : FiniteDimensional ℂ (F₀.comap pt)` using `FiniteDimensional.of_injective (pt.submoduleComap F₀) (by`.

Introduce `a b hab`. Conclude with `Subtype.ext (hinj (congrArg Subtype.val hab)))`. Introduce `j k hjk`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_or]`.

Use `hgrow Y hYG ⟨j, k, hjk, ?_⟩ φ hφ _ hF hm` and prove the remaining obligations. Establish `e : fr * Y * fr⁻¹ = Complex.I • (J * (hᴴ * h))`. Rewrite using `[hY, hY']`. Simplify using `only [Matrix.mul_assoc, f1', f1, Matrix.mul_one]`. Rewrite using `[e]`.

Simplify using `only [hJd, Formalism.REAL.Jm, Matrix.smul_apply, diagonal_mul, smul_eq_mul]`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `refine mul_ne_zero Complex.I_ne_zero (mul_ne_zero ?_ hc.1) split_ifs <;> norm_num`. Apply the tactic sequence `refine mul_ne_zero Complex.I_ne_zero (mul_ne_zero ?_ hc.2) split_ifs <;> norm_num`.
-/
theorem mem_compact : ∀ (n : ℕ) (ε : Fin n → Bool) (fr G : Matrix (Fin n) (Fin n) ℂ) (σ Z : Type) [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (Z → ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (MvPolynomial σ ℂ)), IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → Function.Injective pt → R 1 = 1 → (∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, R (g * g') = R g * R g') → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ φ z, HasDerivAt (fun t : ℝ => R (NormedSpace.exp (t • X)) (pt φ) z) (pt (L X φ) z) 0) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R (fr⁻¹ * k * fr) (pt φ) = pt ψ) → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → (∃ j k, ε j ≠ ε k ∧ (fr * X * fr⁻¹) j k ≠ 0 ∧ (fr * X * fr⁻¹) k j ≠ 0) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ m : ℕ, (L X ^ m) φ ∈ F) → ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ φ φ', φ ≠ 0 → pt φ' = R g (pt φ) → ∃ k ∈ Formalism.REAL.Kset ε, g = fr⁻¹ * k * fr := by
  intro n ε fr G σ Z _ pt R L hfr hG hinj hR1 hmul hder hK hgrow g hg φ φ' hφ hφ'
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hJh := Formalism.REAL.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJd
  have hdet := (Matrix.isUnit_iff_isUnit_det fr).1 hfr
  have f1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hdet
  have f2 : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul fr hdet
  have f1' : ∀ x : Matrix (Fin n) (Fin n) ℂ, fr * (fr⁻¹ * x) = x := fun x => by
    rw [← Matrix.mul_assoc, f1, Matrix.one_mul]
  have f2' : ∀ x : Matrix (Fin n) (Fin n) ℂ, fr⁻¹ * (fr * x) = x := fun x => by
    rw [← Matrix.mul_assoc, f2, Matrix.one_mul]
  have f3' : ∀ x : Matrix (Fin n) (Fin n) ℂ, (fr⁻¹)ᴴ * (frᴴ * x) = x := fun x => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, f1, conjTranspose_one, Matrix.one_mul]
  have J' : ∀ x : Matrix (Fin n) (Fin n) ℂ, J * (J * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have cU : ∀ x : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → fr⁻¹ * x * fr ∈ Formalism.QuantumDeterminants.UH G := by
    intro x hx
    show (fr⁻¹ * x * fr)ᴴ * G * (fr⁻¹ * x * fr) = G
    calc (fr⁻¹ * x * fr)ᴴ * G * (fr⁻¹ * x * fr) = frᴴ * (xᴴ * J * x) * fr := by
          simp only [← hG, conjTranspose_mul, Matrix.mul_assoc, f1', f3']
      _ = G := by rw [hx, hG]
  obtain ⟨h, rfl⟩ : ∃ h, g = fr⁻¹ * h * fr := ⟨fr * g * fr⁻¹, by simp only [Matrix.mul_assoc, f2', f2, Matrix.mul_one]⟩
  have hh : hᴴ * J * h = J := by
    have e : (fr⁻¹ * h * fr)ᴴ * G * (fr⁻¹ * h * fr) = G := hg
    have e2 := congrArg (fun x => (fr⁻¹)ᴴ * x * fr⁻¹) e
    simpa only [← hG, conjTranspose_mul, Matrix.mul_assoc, f1', f3', f1, Matrix.mul_one] using e2
  refine ⟨h, mem_kset_of_block hh ?_, rfl⟩
  set h' := J * hᴴ * J with hh'
  have h1 : h' * h = 1 := by
    rw [hh', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, hJ]
  have h2 : h * h' = 1 := mul_eq_one_comm.1 h1
  have h3 : h'ᴴ * J * h' = J := by
    calc h'ᴴ * J * h' = J * (h * h') := by
          simp only [hh', conjTranspose_mul, hJh, conjTranspose_conjTranspose, Matrix.mul_assoc, J']
      _ = J := by rw [h2, Matrix.mul_one]
  have hY' : h' * (Complex.I • J) * h = Complex.I • (J * (hᴴ * h)) := by
    simp only [hh', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, J']
  set Y := fr⁻¹ * (h' * (Complex.I • J) * h) * fr with hY
  have hYG : Yᴴ * G + G * Y = 0 := by
    rw [hY, hY']
    simp only [← hG, conjTranspose_mul, conjTranspose_smul, hJh, conjTranspose_conjTranspose, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, J', f1', f3']
    simp
  have cm : ∀ x y : Matrix (Fin n) (Fin n) ℂ, (fr⁻¹ * x * fr) * (fr⁻¹ * y * fr) = fr⁻¹ * (x * y) * fr := by
    intro x y
    simp only [Matrix.mul_assoc, f1']
  have cR : ∀ x y : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → yᴴ * J * y = J →
      R (fr⁻¹ * (x * y) * fr) = R (fr⁻¹ * x * fr) * R (fr⁻¹ * y * fr) := by
    intro x y hx hy
    rw [← cm, hmul _ (cU x hx) _ (cU y hy)]
  have kU : ∀ k ∈ Formalism.REAL.Kset ε, kᴴ * J * k = J := by
    intro k hk
    have e1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
    have e2 : k * J = J * k := hk.2
    rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have mU : ∀ x y : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → yᴴ * J * y = J → (x * y)ᴴ * J * (x * y) = J := by
    intro x y hx hy
    calc (x * y)ᴴ * J * (x * y) = yᴴ * (xᴴ * J * x) * y := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [hx, hy]
  let F₀ : Submodule ℂ (Z → ℂ) :=
    (MvPolynomial.restrictTotalDegree σ ℂ φ'.totalDegree).map (R (fr⁻¹ * h' * fr) ∘ₗ pt)
  have : FiniteDimensional ℂ F₀ := inferInstance
  have m0 : pt φ ∈ F₀ := by
    refine ⟨φ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_⟩
    rw [LinearMap.comp_apply, hφ', ← Module.End.mul_apply, ← cR _ _ h3 hh, h1, Matrix.mul_one, f2, hR1,
      Module.End.one_apply]
  have st : ∀ (t : ℝ), ∀ v ∈ F₀, R (NormedSpace.exp (t • Y)) v ∈ F₀ := by
    rintro t _ ⟨ψ, hψ, rfl⟩
    have hk := exp_iJ_mem (ε := ε) t
    obtain ⟨ψ', hd, he⟩ := hK _ hk ψ
    refine ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2
      (hd.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hψ)), ?_⟩
    rw [hY, exp_conj_of_mul f2, exp_conj_of_mul h1, LinearMap.comp_apply, LinearMap.comp_apply, ← he,
      ← Module.End.mul_apply, ← Module.End.mul_apply, ← cR _ _ h3 (kU _ hk),
      ← cR _ _ (mU _ _ (mU _ _ h3 (kU _ hk)) hh) h3, Matrix.mul_assoc _ h, h2, Matrix.mul_one]
  have hm : ∀ m : ℕ, (L Y ^ m) φ ∈ F₀.comap pt := by
    intro m
    induction m with
    | zero => exact m0
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact deriv_mem F₀ (fun t => st t _ ih) (hder Y hYG _)
  have hF : FiniteDimensional ℂ (F₀.comap pt) :=
    FiniteDimensional.of_injective (pt.submoduleComap F₀) (by
      intro a b hab
      exact Subtype.ext (hinj (congrArg Subtype.val hab)))
  intro j k hjk
  by_contra hc
  rw [not_or] at hc
  refine hgrow Y hYG ⟨j, k, hjk, ?_⟩ φ hφ _ hF hm
  have e : fr * Y * fr⁻¹ = Complex.I • (J * (hᴴ * h)) := by
    rw [hY, hY']
    simp only [Matrix.mul_assoc, f1', f1, Matrix.mul_one]
  rw [e]
  simp only [hJd, Formalism.REAL.Jm, Matrix.smul_apply, diagonal_mul, smul_eq_mul]
  constructor
  · refine mul_ne_zero Complex.I_ne_zero (mul_ne_zero ?_ hc.1)
    split_ifs <;> norm_num
  · refine mul_ne_zero Complex.I_ne_zero (mul_ne_zero ?_ hc.2)
    split_ifs <;> norm_num

end GlobalTheory.Chain.RealIt.CompactStab

end
