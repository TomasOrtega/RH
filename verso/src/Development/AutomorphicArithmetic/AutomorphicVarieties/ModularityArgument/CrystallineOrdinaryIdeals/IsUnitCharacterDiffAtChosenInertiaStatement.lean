import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicPropertiesStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _`. Take `⟨-, -, -, hΨ, hs0⟩` from `GlobalTheory.T.galoisSubgroupL_basic_properties D`. Rewrite `hs0` using `[UpperTheory.V.Loc.Dat3.IsInertiaInfiniteCyclotomic.eq_1]`. Take `⟨hH, hI, hc⟩` from `hs0`. Establish `key : ∀ a : Fin 3, UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0 = algebraMap ℤ_[l] O ((cyc l l D.s0 ^ ((D.e : ℤ) * wt1 a) : ℤ_[l]ˣ) : ℤ_[l])`.

Introduce `a`. Rewrite using `[UpperTheory.V.UnitaryThreeInertia.psi.eq_1, hΨ _ hH hI, cycA.eq_1, MonoidHom.comp_apply, ← map_pow, ← map_zpow, Units.coe_map, zpow_mul, zpow_natCast]`. Both sides reduce to the same expression. Establish `unitQ : ∀ z : ℤ_[l], z ≠ 0 → IsUnit (algebraMap ℤ_[l] B z)`. Introduce `z hz`.

Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B]`. Apply `IsUnit.map` to reduce the goal to its premises. Apply `Ne.isUnit` to reduce the goal to its premises. Simplify using `using hz`. Establish `expo : ∀ a b : Fin 3, a ≠ b → (D.e : ℤ) * wt1 a ≠ (D.e : ℤ) * wt1 b`.

Introduce `a b hab hw`. Apply `hab` to reduce the goal to its premises. Establish `he0 : (D.e : ℤ) ≠ 0`. Establish `: (1 : ℤ) ≤ D.e` using `by exact_mod_cast D.e_pos`. Use linear arithmetic over natural numbers and integers.

Establish `hw'` using `mul_left_cancel₀ he0 hw`. Rewrite `hw'` using `[wt1.eq_1, wt1.eq_1]`. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Establish `ne : ∀ m n : ℤ, m ≠ n → ((cyc l l D.s0 ^ m : ℤ_[l]ˣ) : ℤ_[l]) - ((cyc l l D.s0 ^ n : ℤ_[l]ˣ) : ℤ_[l]) ≠ 0`.

Introduce `m n hmn hz`. Apply `hc` to reduce the goal to its premises. Rewrite using `[isOfFinOrder_iff_zpow_eq_one]`. Use `⟨m - n, sub_ne_zero.mpr hmn, ?_⟩` and prove the remaining obligations. Establish `hu : cyc l l D.s0 ^ m = cyc l l D.s0 ^ n` using `Units.ext (sub_eq_zero.mp hz)`.

Rewrite using `[zpow_sub, hu, mul_inv_cancel]`. Establish `diff : ∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0) - algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0))`. Introduce `a b hab`. Rewrite using `[key a, key b, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← map_sub]`. Conclude with `unitQ _ (ne _ _ (expo a b hab))`.

Use `⟨diff, ?_⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[UpperTheory.V.Loc.Dat3.cc.eq_1, map_mul, map_sub, map_sub]`. Use `IsUnit.mul (diff a (a + 1) ?_) (diff a (a + 2) ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases a <;> decide`.

Apply the tactic sequence `fin_cases a <;> decide`.
-/
theorem _root_.GlobalTheory.T.isUnit_characterDiff_at_chosenInertia : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B], (∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D)) - algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b (GlobalTheory.OrdLoc.s0 D)))) ∧ ∀ a, IsUnit (algebraMap O B (GlobalTheory.OrdLoc.cc D a)) := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _
  obtain ⟨-, -, -, hΨ, hs0⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  rw [UpperTheory.V.Loc.Dat3.IsInertiaInfiniteCyclotomic.eq_1] at hs0
  obtain ⟨hH, hI, hc⟩ := hs0
  have key : ∀ a : Fin 3, UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0 =
      algebraMap ℤ_[l] O ((cyc l l D.s0 ^ ((D.e : ℤ) * wt1 a) : ℤ_[l]ˣ) : ℤ_[l]) := by
    intro a
    rw [UpperTheory.V.UnitaryThreeInertia.psi.eq_1, hΨ _ hH hI, cycA.eq_1, MonoidHom.comp_apply, ← map_pow, ← map_zpow,
      Units.coe_map, zpow_mul, zpow_natCast]
    rfl
  have unitQ : ∀ z : ℤ_[l], z ≠ 0 → IsUnit (algebraMap ℤ_[l] B z) := by
    intro z hz
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B]
    apply IsUnit.map
    apply Ne.isUnit
    simpa using hz
  have expo : ∀ a b : Fin 3, a ≠ b → (D.e : ℤ) * wt1 a ≠ (D.e : ℤ) * wt1 b := by
    intro a b hab hw
    apply hab
    have he0 : (D.e : ℤ) ≠ 0 := by
      have : (1 : ℤ) ≤ D.e := by exact_mod_cast D.e_pos
      omega
    have hw' := mul_left_cancel₀ he0 hw
    rw [wt1.eq_1, wt1.eq_1] at hw'
    apply Fin.ext
    omega
  have ne : ∀ m n : ℤ, m ≠ n →
      ((cyc l l D.s0 ^ m : ℤ_[l]ˣ) : ℤ_[l]) - ((cyc l l D.s0 ^ n : ℤ_[l]ˣ) : ℤ_[l]) ≠ 0 := by
    intro m n hmn hz
    apply hc
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨m - n, sub_ne_zero.mpr hmn, ?_⟩
    have hu : cyc l l D.s0 ^ m = cyc l l D.s0 ^ n := Units.ext (sub_eq_zero.mp hz)
    rw [zpow_sub, hu, mul_inv_cancel]
  have diff : ∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0) -
      algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
    intro a b hab
    rw [key a, key b, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← map_sub]
    exact unitQ _ (ne _ _ (expo a b hab))
  refine ⟨diff, ?_⟩
  intro a
  rw [UpperTheory.V.Loc.Dat3.cc.eq_1, map_mul, map_sub, map_sub]
  refine IsUnit.mul (diff a (a + 1) ?_) (diff a (a + 2) ?_)
  · fin_cases a <;> decide
  · fin_cases a <;> decide
