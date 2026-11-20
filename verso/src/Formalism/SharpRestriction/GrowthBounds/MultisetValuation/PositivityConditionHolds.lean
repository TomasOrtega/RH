import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LocalComponentGL

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (WModel.nf WModel.norm_def WModel.abv_le_one_iff WModel.abv_le_pow_iff)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf

variable (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem sx_charZero : CharZero (K0 p) := inferInstance

attribute [local instance] sx_charZero

/- English proof (translation)
Rewrite using `[Formalism.InvariantFactorPaths.G7.WModel.norm_def]`. Conclude with `Formalism.InvariantFactorPaths.G7.WModel.abv_le_one_iff p x`.
-/
theorem sx_norm_le_one_iff (x : K0 p) : ‖x‖ ≤ 1 ↔ ∃ w : WW p, algebraMap (WW p) (K0 p) w = x := by
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  exact Formalism.InvariantFactorPaths.G7.WModel.abv_le_one_iff p x

/- English proof (translation)
Establish `h` using `Formalism.InvariantFactorPaths.G7.WModel.abv_le_pow_iff p 1 x`. Rewrite `h` using `[pow_one, pow_one]`. Rewrite using `[Formalism.InvariantFactorPaths.G7.WModel.norm_def]`. Conclude with `h`.
-/
theorem sx_norm_le_inv_iff (x : K0 p) :
    ‖x‖ ≤ (p : ℝ)⁻¹ ↔ ∃ w : WW p, x = (p : K0 p) * algebraMap (WW p) (K0 p) w := by
  have h := Formalism.InvariantFactorPaths.G7.WModel.abv_le_pow_iff p 1 x
  rw [pow_one, pow_one] at h
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  exact h

/- English proof (translation)
Rewrite using `[Formalism.InvariantFactorPaths.G7.WModel.norm_def]`. Conclude with `Formalism.InvariantFactorPaths.G7.WModel.abv_p p`.
-/
theorem sx_norm_p : ‖(p : K0 p)‖ = (p : ℝ)⁻¹ := by
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  exact Formalism.InvariantFactorPaths.G7.WModel.abv_p p

/- English proof (translation)
The claim follows from `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def, Formalism.InvariantFactorPaths.G7.WModel.norm_def, Formalism.InvariantFactorPaths.G7.WModel.norm_def] exact Formalism.InvariantFactorPaths.G7.WM …`.
-/
theorem sx_ultra : IsUltrametricDist (K0 p) := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def, Formalism.InvariantFactorPaths.G7.WModel.norm_def, Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  exact Formalism.InvariantFactorPaths.G7.WModel.abv_nonarch p x y

/- English proof (translation)
Apply `IsLocalization.ringHom_ext (nonZeroDivisors (WW p))` to reduce the goal to its premises. Use extensionality with `w`. Simplify using `[sigK, Formalism.InvariantFactorPaths.G7.WModel.sig, IsLocalization.map_eq]`.
-/
theorem sx_sigK_eq : (sigK p).toRingHom = Formalism.InvariantFactorPaths.G7.WModel.sig p := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (WW p))
  ext w
  simp [sigK, Formalism.InvariantFactorPaths.G7.WModel.sig, IsLocalization.map_eq]

/- English proof (translation)
Rewrite using `[sx_sigK_eq, Formalism.InvariantFactorPaths.G7.WModel.norm_def]`. Rewrite `ha` using `[Formalism.InvariantFactorPaths.G7.WModel.norm_def]`. Conclude with `Formalism.InvariantFactorPaths.G7.WModel.abv_sig p a ha`.
-/
theorem sx_sig_frob (a : K0 p) (ha : ‖a‖ ≤ 1) : ‖(sigK p).toRingHom a - a ^ p‖ ≤ (p : ℝ)⁻¹ := by
  rw [sx_sigK_eq, Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def] at ha
  exact Formalism.InvariantFactorPaths.G7.WModel.abv_sig p a ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h choose g hg using fun n => (sx_norm_le_one_iff p (MvPowerSeries.coeff n f)).mp (h n)`. Use `⟨fun n => g n, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Conclude with `(hg n).symm`.

Introduce and unpack `⟨g, rfl⟩ n`. Conclude with `(sx_norm_le_one_iff p _).mpr ⟨_, rfl⟩`.
-/
theorem sx_integral_iff {ι : Type} (f : MvPowerSeries ι (K0 p)) : Integral f ↔ IntS p f := by
  constructor
  · intro h
    choose g hg using fun n => (sx_norm_le_one_iff p (MvPowerSeries.coeff n f)).mp (h n)
    refine ⟨fun n => g n, ?_⟩
    ext n
    exact (hg n).symm
  · rintro ⟨g, rfl⟩ n
    exact (sx_norm_le_one_iff p _).mpr ⟨_, rfl⟩

/- English proof (translation)
Use extensionality with `n`. Unfold `mvExp`. Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf)]`. Establish `hord : (1 : ℕ∞) ≤ f.order`. Apply `MvPowerSeries.le_order` to reduce the goal to its premises.

Introduce `d hd`. Establish `hd0 : d = 0`. Establish `: Finsupp.degree d = 0` using `by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hd)`. Conclude with `(Finsupp.degree_eq_zero_iff d).mp this`. Rewrite using `[hd0, MvPowerSeries.coeff_zero_eq_constantCoeff]`.

Conclude with `hf`. Establish `hz : ∀ d : ℕ, Finsupp.degree n < d → MvPowerSeries.coeff n (f ^ d) = 0`. Introduce `d hd`. Apply `MvPowerSeries.coeff_of_lt_order` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[finsum_eq_sum_of_support_subset (s := Finset.range (Finsupp.degree n + 1))]`. Use `show ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k) = _`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_exp, smul_eq_mul]`. Simplify using the standard rewrite rules.

Introduce `d hd`. Rewrite `hd` using `[Function.mem_support]`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[hz d (by omega), smul_zero]`.
-/
theorem sx_expS_eq {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : MvPowerSeries.constantCoeff f = 0) :
    expS p f = mvExp f := by
  ext n
  unfold mvExp
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf)]
  have hord : (1 : ℕ∞) ≤ f.order := by
    apply MvPowerSeries.le_order
    intro d hd
    have hd0 : d = 0 := by
      have : Finsupp.degree d = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hd)
      exact (Finsupp.degree_eq_zero_iff d).mp this
    rw [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff]
    exact hf
  have hz : ∀ d : ℕ, Finsupp.degree n < d → MvPowerSeries.coeff n (f ^ d) = 0 := by
    intro d hd
    apply MvPowerSeries.coeff_of_lt_order
    calc ((Finsupp.degree n : ℕ) : ℕ∞) < d := by exact_mod_cast hd
      _ = d • (1 : ℕ∞) := by simp
      _ ≤ d • f.order := nsmul_le_nsmul_right hord d
      _ ≤ (f ^ d).order := MvPowerSeries.le_order_pow d
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (Finsupp.degree n + 1))]
  · show ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push_neg at h
    apply hd
    rw [hz d (by omega), smul_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h choose g hg using fun n => (sx_norm_le_inv_iff p (MvPowerSeries.coeff n f)).mp (h n)`. Use `⟨fun n => g n, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Simplify using `only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, smul_eq_mul]`.

Conclude with `hg n`. Introduce and unpack `⟨Q, rfl⟩ n`. Simplify using `only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, smul_eq_mul]`. Conclude with `(sx_norm_le_inv_iff p _).mpr ⟨_, rfl⟩`.
-/
theorem sx_div_p_iff {ι : Type} (f : MvPowerSeries ι (K0 p)) :
    (∀ n, ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ)⁻¹) ↔
      ∃ Q : MvPowerSeries ι (WW p), f = (p : K0 p) • MvPowerSeries.map (algebraMap (WW p) (K0 p)) Q := by
  constructor
  · intro h
    choose g hg using fun n => (sx_norm_le_inv_iff p (MvPowerSeries.coeff n f)).mp (h n)
    refine ⟨fun n => g n, ?_⟩
    ext n
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, smul_eq_mul]
    exact hg n
  · rintro ⟨Q, rfl⟩ n
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, smul_eq_mul]
    exact (sx_norm_le_inv_iff p _).mpr ⟨_, rfl⟩

/- English proof (translation)
Introduce `_ n Ps h0`. Use `sx_ultra p` as an intermediate fact. Establish `h` using `Formalism.InvariantFactorPaths.G7.dwork_multivariable (K0 p) (Fin n) p (sigK p).toRingHom hp.out (sx_norm_p p) (sx_sig_frob p) Ps h0`. Rewrite using `[sx_expS_eq p h0, ← sx_integral_iff, h, sx_div_p_iff]`. Unfold `Formalism.InvariantFactorPaths.G7.frobVar`.

Rewrite using `[MvPowerSeries.smul_eq_C_mul]`.
-/
theorem sx_dwork : DworkLemma p := by
  intro _ n Ps h0
  have := sx_ultra p
  have h := Formalism.InvariantFactorPaths.G7.dwork_multivariable (K0 p) (Fin n) p (sigK p).toRingHom hp.out (sx_norm_p p) (sx_sig_frob p) Ps h0
  rw [sx_expS_eq p h0, ← sx_integral_iff, h, sx_div_p_iff]
  unfold Formalism.InvariantFactorPaths.G7.frobVar
  rw [MvPowerSeries.smul_eq_C_mul]

/- English proof (translation)
Introduce `p _` and use `sx_dwork p`.
-/
theorem positivity_condition_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm1 D := fun p _ => sx_dwork p

end Formalism.MainNotions.FormalGroupSystem.Pf
