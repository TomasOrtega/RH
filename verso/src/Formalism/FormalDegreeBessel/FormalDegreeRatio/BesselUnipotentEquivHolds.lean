import Formalism.FormalDegreeBessel.StatementBF
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix MeasureTheory

noncomputable section

namespace Formalism.QuantumDeterminants

namespace BesselUnipotentEquiv

variable {k r : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact (continuous_const.matrix_mul continuous_id : Continuous fun x : Mt k r => a * Matrix.of x)`. Consider the case `exact continuous_pi fun i => continuous_pi fun j => by`. Simplify using `only [lmulM, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem continuous_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (lmulM (k := k) (r := r) a) := by
  first
  | exact (continuous_const.matrix_mul continuous_id : Continuous fun x : Mt k r => a * Matrix.of x)
  | exact continuous_pi fun i => continuous_pi fun j => by
      simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
      fun_prop

def lmulEquiv (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left a (Matrix.of x) ha
  right_inv x := Matrix.mul_nonsing_inv_cancel_left a (Matrix.of x) ha
  measurable_toFun := (continuous_lmulM a).measurable
  measurable_invFun := (continuous_lmulM a⁻¹).measurable

/- English proof (translation)
Establish `h : ell k r z 1 = 0`. Unfold `ell`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Use `split_ifs with h'`.

Rewrite using `[Matrix.one_apply_ne]`. Introduce `he`. Use `congrArg Fin.val he` as an intermediate fact. Simplify using `[eI] at this`. Rewrite using `[Matrix.one_mulVec]`.

Conclude with `hz _ (Or.inl (by simp [eI]))`. Simplify using `[psi, h]`.
-/
theorem psi_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) :
    psi k r z c 1 = 1 := by
  have h : ell k r z 1 = 0 := by
    unfold ell
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with h'
    · rw [Matrix.one_apply_ne]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact hz _ (Or.inl (by simp [eI]))
  simp [psi, h]

/- English proof (translation)
Establish `hinv` using `(unipotent_subgroup_holds k r).2.2 n hn`. Establish `hu` using `WeylGroupFacts.isUnit_of_uh hn.1`. Establish `h1 : psi k r z c n⁻¹ * psi k r z c n = 1`. Rewrite using `[← (additive_character_holds k r z c hz n⁻¹ hinv).1 n hn, Matrix.nonsing_inv_mul _ hu, psi_one z c hz]`. Establish `h2 : star (psi k r z c n⁻¹) * psi k r z c n⁻¹ = 1`.

Rewrite using `[Complex.star_def, Complex.conj_mul', (additive_character_holds k r z c hz n⁻¹ hinv).2]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, mul_one]`. Use `_ = psi k r z c n := by rw [← mul_assoc, h2, one_mul]`.
-/
theorem star_psi_inv (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z)
    (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hn : n ∈ Nset k r) :
    star (psi k r z c n⁻¹) = psi k r z c n := by
  have hinv := (unipotent_subgroup_holds k r).2.2 n hn
  have hu := WeylGroupFacts.isUnit_of_uh hn.1
  have h1 : psi k r z c n⁻¹ * psi k r z c n = 1 := by
    rw [← (additive_character_holds k r z c hz n⁻¹ hinv).1 n hn, Matrix.nonsing_inv_mul _ hu, psi_one z c hz]
  have h2 : star (psi k r z c n⁻¹) * psi k r z c n⁻¹ = 1 := by
    rw [Complex.star_def, Complex.conj_mul', (additive_character_holds k r z c hz n⁻¹ hinv).2]
    simp
  calc star (psi k r z c n⁻¹) = star (psi k r z c n⁻¹) * (psi k r z c n⁻¹ * psi k r z c n) := by
        rw [h1, mul_one]
    _ = psi k r z c n := by rw [← mul_assoc, h2, one_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_lmulEquiv (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    ⇑(lmulEquiv (k := k) (r := r) a ha) = lmulM a := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) :
    Matrix.of (lmulM a x) = a * Matrix.of x := rfl

end BesselUnipotentEquiv

open BesselUnipotentEquiv in
/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ k r z z' c π π' μW μN μW' _ _ _ F hz hz' hNc hinvN g n₀ hn₀ n₀' hn₀'`. Establish `hinv' : n₀'⁻¹ ∈ Nset k r` using `(unipotent_subgroup_holds k r).2.2 n₀' hn₀'`. Establish `hu0 : IsUnit n₀.det` using `WeylGroupFacts.isUnit_of_uh hn₀.1`. Establish `hu0' : IsUnit n₀'.det` using `WeylGroupFacts.isUnit_of_uh hn₀'.1`. Establish `hui' : IsUnit (n₀'⁻¹).det` using `WeylGroupFacts.isUnit_of_uh hinv'.1`.

Set `e1` to `lmulEquiv (k := k) (r := r) n₀ hu0`. Set `e2` to `lmulEquiv (k := k) (r := r) n₀'⁻¹ hui'`. Set `Φ` to `((MeasurableEquiv.refl (Mt k r)).prodCongr e1).prodCongr ((MeasurableEquiv.refl (Mt k r)).prodCongr e2)`. Establish `hΦapp : ∀ q : (Mt k r × Mt k r) × (Mt k r × Mt k r), Φ q = ((q.1.1, lmulM n₀ q.1.2), (q.2.1, lmulM n₀'⁻¹ q.2.2))` using `fun q => rfl`. Establish `hp1 : MeasurePreserving e1 μN μN` using `⟨e1.measurable, by rw [coe_lmulEquiv]; exact hinvN n₀ hn₀⟩`.

Establish `hp2 : MeasurePreserving e2 μN μN` using `⟨e2.measurable, by rw [coe_lmulEquiv]; exact hinvN n₀'⁻¹ hinv'⟩`. Establish `hpΦ : MeasurePreserving Φ ((μW.prod μN).prod (μW'.prod μN)) ((μW.prod μN).prod (μW'.prod μN))` using `((MeasurePreserving.id μW).prod hp1).prod ((MeasurePreserving.id μW').prod hp2)`. Establish `haeN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r` using `ae_iff.2 hNc`. Establish `hae1 : ∀ᵐ q ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of q.1.2 ∈ Nset k r` using `Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae haeN)`. Establish `hae2 : ∀ᵐ q ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of q.2.2 ∈ Nset k r` using `Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae haeN)`.

Establish `key : ∀ h m h' m' : Mt k r, Matrix.of m ∈ Nset k r → Matrix.of m' ∈ Nset k r → (psi k r z c (n₀ * Matrix.of m) * star (psi k r z' c (n₀'⁻¹ * Matrix.of m'))) • ((π (Matrix.of h)).comp ((F ((Matrix.of h)⁻¹ * (n₀ * Matrix.of m)⁻¹ * (n₀ * g * n₀') * (n₀'⁻¹ * Matrix.of m') * Matrix.of …`. Introduce `h m h' m' hm hm'`. Establish `hmat : (Matrix.of h)⁻¹ * (n₀ * Matrix.of m)⁻¹ * (n₀ * g * n₀') * (n₀'⁻¹ * Matrix.of m') * Matrix.of h' = (Matrix.of h)⁻¹ * (Matrix.of m)⁻¹ * g * Matrix.of m' * Matrix.of h'`. Rewrite using `[Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ hu0, Matrix.mul_nonsing_inv_cancel_left _ _ hu0']`. Rewrite using `[hmat, smul_smul]`. Use `congr 1`. Rewrite using `[(additive_character_holds k r z c hz n₀ hn₀).1 _ hm, (additive_character_holds k r z' c hz' _ hinv').1 _ hm', star_mul', star_psi_inv z' c hz' n₀' hn₀']`. Expand and normalize the polynomial expressions, which then agree.

Unfold `besselJ`. Rewrite using `[← hpΦ.integral_comp', ← integral_smul]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae1, hae2] with q hm hm'`. Rewrite using `[hΦapp]`.

Simplify using `only [of_lmulM]`. Conclude with `key q.1.1 q.1.2 q.2.1 q.2.2 hm hm'`.
-/
theorem bessel_unipotent_equiv_holds : BesselNEquiv := by
  intro Wp Wq _ _ _ _ _ _ k r z z' c π π' μW μN μW' _ _ _ F hz hz' hNc hinvN g n₀ hn₀ n₀' hn₀'
  have hinv' : n₀'⁻¹ ∈ Nset k r := (unipotent_subgroup_holds k r).2.2 n₀' hn₀'
  have hu0 : IsUnit n₀.det := WeylGroupFacts.isUnit_of_uh hn₀.1
  have hu0' : IsUnit n₀'.det := WeylGroupFacts.isUnit_of_uh hn₀'.1
  have hui' : IsUnit (n₀'⁻¹).det := WeylGroupFacts.isUnit_of_uh hinv'.1
  let e1 := lmulEquiv (k := k) (r := r) n₀ hu0
  let e2 := lmulEquiv (k := k) (r := r) n₀'⁻¹ hui'
  let Φ := ((MeasurableEquiv.refl (Mt k r)).prodCongr e1).prodCongr
    ((MeasurableEquiv.refl (Mt k r)).prodCongr e2)
  have hΦapp : ∀ q : (Mt k r × Mt k r) × (Mt k r × Mt k r),
      Φ q = ((q.1.1, lmulM n₀ q.1.2), (q.2.1, lmulM n₀'⁻¹ q.2.2)) := fun q => rfl
  have hp1 : MeasurePreserving e1 μN μN :=
    ⟨e1.measurable, by rw [coe_lmulEquiv]; exact hinvN n₀ hn₀⟩
  have hp2 : MeasurePreserving e2 μN μN :=
    ⟨e2.measurable, by rw [coe_lmulEquiv]; exact hinvN n₀'⁻¹ hinv'⟩
  have hpΦ : MeasurePreserving Φ ((μW.prod μN).prod (μW'.prod μN))
      ((μW.prod μN).prod (μW'.prod μN)) :=
    ((MeasurePreserving.id μW).prod hp1).prod ((MeasurePreserving.id μW').prod hp2)
  have haeN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := ae_iff.2 hNc
  have hae1 : ∀ᵐ q ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of q.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae haeN)
  have hae2 : ∀ᵐ q ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of q.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae haeN)
  have key : ∀ h m h' m' : Mt k r, Matrix.of m ∈ Nset k r → Matrix.of m' ∈ Nset k r →
      (psi k r z c (n₀ * Matrix.of m) * star (psi k r z' c (n₀'⁻¹ * Matrix.of m'))) •
        ((π (Matrix.of h)).comp ((F ((Matrix.of h)⁻¹ * (n₀ * Matrix.of m)⁻¹ * (n₀ * g * n₀') *
          (n₀'⁻¹ * Matrix.of m') * Matrix.of h')).comp (π' (Matrix.of h')⁻¹))) =
      (psi k r z c n₀ * psi k r z' c n₀') •
        ((psi k r z c (Matrix.of m) * star (psi k r z' c (Matrix.of m'))) •
          ((π (Matrix.of h)).comp ((F ((Matrix.of h)⁻¹ * (Matrix.of m)⁻¹ * g *
            Matrix.of m' * Matrix.of h')).comp (π' (Matrix.of h')⁻¹)))) := by
    intro h m h' m' hm hm'
    have hmat : (Matrix.of h)⁻¹ * (n₀ * Matrix.of m)⁻¹ * (n₀ * g * n₀') *
        (n₀'⁻¹ * Matrix.of m') * Matrix.of h' =
        (Matrix.of h)⁻¹ * (Matrix.of m)⁻¹ * g * Matrix.of m' * Matrix.of h' := by
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu0, Matrix.mul_nonsing_inv_cancel_left _ _ hu0']
    rw [hmat, smul_smul]
    congr 1
    rw [(additive_character_holds k r z c hz n₀ hn₀).1 _ hm, (additive_character_holds k r z' c hz' _ hinv').1 _ hm',
      star_mul', star_psi_inv z' c hz' n₀' hn₀']
    ring
  unfold besselJ
  rw [← hpΦ.integral_comp', ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hae1, hae2] with q hm hm'
  rw [hΦapp]
  simp only [of_lmulM]
  exact key q.1.1 q.1.2 q.2.1 q.2.2 hm hm'

end Formalism.QuantumDeterminants
