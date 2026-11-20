import Mathlib

namespace GlobalTheory

open MvPowerSeries

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simpa`.
-/
theorem hasSubst_pair {τ k : Type} [CommRing k] {z w : MvPowerSeries τ k}
    (hz : constantCoeff z = 0) (hw : constantCoeff w = 0) :
    HasSubst (![z, w] : Fin 2 → MvPowerSeries τ k) :=
  hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simpa

/- English proof (translation)
Establish `h1 : HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) k))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Unfold `PowerSeries.subst`. Rewrite using `[subst_comp_subst_apply h1 ha]`. Use `congr 1`. Use function extensionality and compare the values at `_`.

Conclude with `subst_X ha i`.
-/
theorem subst_pair_subst_X {k : Type} [CommRing k] (x : PowerSeries k) (i : Fin 2)
    {a : Fin 2 → PowerSeries k} (ha : HasSubst a) :
    subst a (x.subst (X i : MvPowerSeries (Fin 2) k)) = x.subst (a i) := by
  have h1 : HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext _
  exact subst_X ha i

/- English proof (translation)
Establish `ha : HasSubst (![z, w] : Fin 2 → PowerSeries k)` using `hasSubst_pair hz hw`. Establish `h1 : HasSubst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k)` using `hasSubst_pair (by simp) (by simp)`. Rewrite using `[subst_comp_subst_apply h1 ha]`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Use `fin_cases s`. Conclude with `subst_X ha 0`. Use `show subst _ (X 0 + X 1 : MvPowerSeries (Fin 2) k) = z + w`. Rewrite using `[subst_add ha, subst_X ha, subst_X ha]`. Both sides reduce to the same expression.
-/
theorem subst_pair_subst_shear {k : Type} [CommRing k] (h : MvPowerSeries (Fin 2) k)
    {z w : PowerSeries k} (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) :
    subst (![z, w] : Fin 2 → PowerSeries k)
      (subst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) =
      subst (![z, z + w] : Fin 2 → PowerSeries k) h := by
  have ha : HasSubst (![z, w] : Fin 2 → PowerSeries k) := hasSubst_pair hz hw
  have h1 : HasSubst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) :=
    hasSubst_pair (by simp) (by simp)
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext s
  fin_cases s
  · exact subst_X ha 0
  · show subst _ (X 0 + X 1 : MvPowerSeries (Fin 2) k) = z + w
    rw [subst_add ha, subst_X ha, subst_X ha]
    rfl

/- English proof (translation)
Establish `ha : HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k)` using `hasSubst_pair PowerSeries.constantCoeff_X (map_zero _)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩`. Rewrite using `[subst_mul ha, subst_X ha]`. Conclude with `zero_mul _`.

Introduce `hg`. Establish `h1 : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) k))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Establish `h2` using `subst_comp_subst_apply ha h1 g`. Rewrite `h2` using `[hg, ← coe_substAlgHom h1, map_zero]`. Establish `h3 : rescale (![1, 0] : Fin 2 → k) g = 0`.

Rewrite using `[rescale_eq_subst, h2]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Use `fin_cases s`. Use `show (1 : k) • (X 0 : MvPowerSeries (Fin 2) k) = substAlgHom h1 (X ())`.

Rewrite using `[substAlgHom_X, one_smul]`. Use `show (0 : k) • (X 1 : MvPowerSeries (Fin 2) k) = substAlgHom h1 0`. Rewrite using `[map_zero, zero_smul]`. Rewrite using `[X_dvd_iff]`. Introduce `m hm`.

Establish `h4` using `congrArg (coeff m) h3`. Rewrite `h4` using `[coeff_rescale, Finsupp.prod_fintype _ _ (by simp)]`. Simplify `h4` using `[hm]`.
-/
theorem X_one_dvd_iff_subst_eq_zero {k : Type} [CommRing k] (g : MvPowerSeries (Fin 2) k) :
    X 1 ∣ g ↔ subst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) g = 0 := by
  have ha : HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) :=
    hasSubst_pair PowerSeries.constantCoeff_X (map_zero _)
  constructor
  · rintro ⟨q, rfl⟩
    rw [subst_mul ha, subst_X ha]
    exact zero_mul _
  · intro hg
    have h1 : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have h2 := subst_comp_subst_apply ha h1 g
    rw [hg, ← coe_substAlgHom h1, map_zero] at h2
    have h3 : rescale (![1, 0] : Fin 2 → k) g = 0 := by
      rw [rescale_eq_subst, h2]
      congr 1
      funext s
      fin_cases s
      · show (1 : k) • (X 0 : MvPowerSeries (Fin 2) k) = substAlgHom h1 (X ())
        rw [substAlgHom_X, one_smul]
      · show (0 : k) • (X 1 : MvPowerSeries (Fin 2) k) = substAlgHom h1 0
        rw [map_zero, zero_smul]
    rw [X_dvd_iff]
    intro m hm
    have h4 := congrArg (coeff m) h3
    rw [coeff_rescale, Finsupp.prod_fintype _ _ (by simp)] at h4
    simpa [hm] using h4

/- English proof (translation)
Introduce `k _`. Use `⟨fun h => ⟨?_, fun z w hz hw => subst_pair_subst_shear h hz hw⟩, fun x z w hz hw => ⟨subst_pair_subst_X x 0 (hasSubst_pair hz hw), subst_pair_subst_X x 1 (hasSubst_pair hz hw)⟩⟩` and prove the remaining obligations. Rewrite using `[X_one_dvd_iff_subst_eq_zero, subst_pair_subst_shear h PowerSeries.constantCoeff_X (map_zero _), add_zero]`.
-/
theorem subst_two_variables_identities : ∀ (k : Type) [Field k], (∀ h : MvPowerSeries (Fin 2) k, (MvPowerSeries.X 1 ∣ MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h ↔ MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) h = 0) ∧ ∀ z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) = MvPowerSeries.subst (![z, z + w] : Fin 2 → PowerSeries k) h) ∧ ∀ x z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) = x.subst z ∧ MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)) = x.subst w := by
  intro k _
  refine ⟨fun h => ⟨?_, fun z w hz hw => subst_pair_subst_shear h hz hw⟩, fun x z w hz hw =>
    ⟨subst_pair_subst_X x 0 (hasSubst_pair hz hw), subst_pair_subst_X x 1 (hasSubst_pair hz hw)⟩⟩
  rw [X_one_dvd_iff_subst_eq_zero,
    subst_pair_subst_shear h PowerSeries.constantCoeff_X (map_zero _), add_zero]

end GlobalTheory
