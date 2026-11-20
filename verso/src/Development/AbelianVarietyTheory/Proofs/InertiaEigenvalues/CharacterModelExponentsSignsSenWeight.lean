import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityShiftLatticeVariablePow

noncomputable section
namespace GlobalTheory.Models.CharSign
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V]

/- English proof (translation)
Take `⟨a, u, h⟩` from `IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (R := k⟦X⟧) (K := k⸨X⸩) PowerSeries.X_irreducible hc`. Use `⟨a, u, ?_⟩` and prove the remaining obligations. Rewrite using `[h, Units.smul_def, Algebra.smul_def, vv_eq_coe_X]`. Both sides reduce to the same expression.
-/
theorem exists_unit_zpow {c : k⸨X⸩} (hc : c ≠ 0) :
    ∃ (a : ℤ) (u : (k⟦X⟧)ˣ), c = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ a := by
  obtain ⟨a, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := k⟦X⟧) (K := k⸨X⸩) PowerSeries.X_irreducible hc
  refine ⟨a, u, ?_⟩
  rw [h, Units.smul_def, Algebra.smul_def, vv_eq_coe_X]
  rfl

/- English proof (translation)
The claim follows from `algebraMap_smul k⸨X⸩ a x`.
-/
theorem coe_smul (a : k⟦X⟧) (x : V) : (a : k⸨X⸩) • x = a • x := algebraMap_smul k⸨X⸩ a x

/- English proof (translation)
Assume the negation of the conclusion as `hab`. Establish `h1 : N ≤ sh 1 N`. Establish `h2` using `sh_le_sh (-a) h`. Rewrite `h2` using `[sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq]`. Conclude with `h2.trans (sh_le_sh_of_le (by omega) N)`.

Apply `h0` to reduce the goal to its premises. Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {(PowerSeries.X : k⟦X⟧)}) N hN ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `mem_sh_iff_exists.1 (h1 hx)`. Rewrite using `[zpow_one, vv_eq_coe_X, coe_smul]`.

Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PowerSeries.maximalIdeal_eq_span_X]`.
-/
theorem le_of_sh_le_sh {N : Submodule k⟦X⟧ V} (hN : N.FG) (h0 : N ≠ ⊥) {a b : ℤ} (h : sh a N ≤ sh b N) :
    b ≤ a := by
  by_contra hab
  have h1 : N ≤ sh 1 N := by
    have h2 := sh_le_sh (-a) h
    rw [sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq] at h2
    exact h2.trans (sh_le_sh_of_le (by omega) N)
  apply h0
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {(PowerSeries.X : k⟦X⟧)}) N hN ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 (h1 hx)
    rw [zpow_one, vv_eq_coe_X, coe_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PowerSeries.maximalIdeal_eq_span_X]

/- English proof (translation)
Rewrite using `[sh, Submodule.map_span, Set.image_singleton, mul_smul, coe_smul, Submodule.span_singleton_smul_eq u.isUnit]`. Both sides reduce to the same expression.
-/
theorem span_unit_zpow (a : ℤ) (u : (k⟦X⟧)ˣ) (y : V) :
    Submodule.span k⟦X⟧ {(((u : k⟦X⟧) : k⸨X⸩) * vv k ^ a) • y} = sh a (Submodule.span k⟦X⟧ {y}) := by
  rw [sh, Submodule.map_span, Set.image_singleton, mul_smul, coe_smul,
    Submodule.span_singleton_smul_eq u.isUnit]
  rfl

/- English proof (translation)
Take `⟨u, hu⟩` from `R.φ_v`. Use `⟨u ^ a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zpow₀, hu, mul_zpow, zpow_mul, zpow_natCast]`. Use `congr 1`. Use `map_zpow (Units.map (HahnSeries.ofPowerSeries ℤ k : k⟦X⟧ →+* k⸨X⸩).toMonoidHom) u a` as an intermediate fact.

Establish `h2` using `congrArg Units.val this`. Rewrite `h2` using `[Units.val_zpow_eq_zpow_val]`. Conclude with `h2.symm`.
-/
theorem φ_zpow {l : ℕ} (R : RingPG k l) (a : ℤ) :
    ∃ u : (k⟦X⟧)ˣ, R.φ (vv k ^ a) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l * a) := by
  obtain ⟨u, hu⟩ := R.φ_v
  refine ⟨u ^ a, ?_⟩
  rw [map_zpow₀, hu, mul_zpow, zpow_mul, zpow_natCast]
  congr 1
  have := map_zpow (Units.map (HahnSeries.ofPowerSeries ℤ k : k⟦X⟧ →+* k⸨X⸩).toMonoidHom) u a
  have h2 := congrArg Units.val this
  rw [Units.val_zpow_eq_zpow_val] at h2
  exact h2.symm

variable [Module k V]

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨y, hy, rfl⟩` from `mem_sh_iff_exists.1 hx`. Take `⟨u, hu⟩` from `φ_zpow R a`. Rewrite using `[hf, hu, mul_smul, coe_smul]`.

Conclude with `Submodule.smul_mem _ _ (mem_sh_iff_exists.2 ⟨f y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩)`.
-/
theorem pull_sh_le {l : ℕ} (R : RingPG k l) {f : V →ₗ[k] V} (hf : Semi R.φ f) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    pull f (sh a N) ≤ sh (l * a) (pull f N) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := φ_zpow R a
  rw [hf, hu, mul_smul, coe_smul]
  exact Submodule.smul_mem _ _ (mem_sh_iff_exists.2 ⟨f y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩)

/- English proof (translation)
Use `le_antisymm (pull_sh_le R hf a N) ?_` and prove the remaining obligations. Establish `h` using `sh_le_sh (l * a) (pull_sh_le R hf (-a) (sh a N))`. Rewrite `h` using `[sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq, mul_neg, add_neg_cancel, sh_zero_eq]`. Then use the resulting hypothesis.
-/
theorem pull_sh {l : ℕ} (R : RingPG k l) {f : V →ₗ[k] V} (hf : Semi R.φ f) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    pull f (sh a N) = sh (l * a) (pull f N) := by
  refine le_antisymm (pull_sh_le R hf a N) ?_
  have h := sh_le_sh (l * a) (pull_sh_le R hf (-a) (sh a N))
  rwa [sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq, mul_neg, add_neg_cancel, sh_zero_eq] at h

end

section
variable {k : Type} [Field k]

/- English proof (translation)
Establish `h0 : y 0 ≠ 0` using `fun h => hy (funext fun j => by rw [Subsingleton.elim j 0]; exact h)`. Use `⟨x 0 / y 0, funext fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]`.
-/
theorem exists_smul_eq {y : Vc k 1} (hy : y ≠ 0) (x : Vc k 1) : ∃ c : k⸨X⸩, x = c • y := by
  have h0 : y 0 ≠ 0 := fun h => hy (funext fun j => by rw [Subsingleton.elim j 0]; exact h)
  refine ⟨x 0 / y 0, funext fun j => ?_⟩
  rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]

/- English proof (translation)
Take `⟨c, rfl⟩` from `exists_smul_eq hy x`. Take `⟨a, u, rfl⟩` from `exists_unit_zpow (c := c) (by rintro rfl; exact hx (zero_smul _ _))`. Conclude with `⟨a, span_unit_zpow a u y⟩`.
-/
theorem span_eq_sh {x y : Vc k 1} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a : ℤ, Submodule.span k⟦X⟧ {x} = sh a (Submodule.span k⟦X⟧ {y}) := by
  obtain ⟨c, rfl⟩ := exists_smul_eq hy x
  obtain ⟨a, u, rfl⟩ := exists_unit_zpow (c := c) (by rintro rfl; exact hx (zero_smul _ _))
  exact ⟨a, span_unit_zpow a u y⟩

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Use `left`. Simplify using `[hx]`. Distinguish the cases in `hy : y = 0`. Use `right`.

Simplify using `[hy]`. Take `⟨a, h⟩` from `span_eq_sh hx hy`. Rewrite using `[h]`. Break down `le_total 0 a with ha | ha` into its components or cases. Use `left`.

Conclude with `(sh_le_sh_of_le ha _).trans (sh_zero_eq _).le`. Use `right`. Conclude with `(sh_zero_eq _).ge.trans (sh_le_sh_of_le ha _)`.
-/
theorem span_total (x y : Vc k 1) : Submodule.span k⟦X⟧ {x} ≤ Submodule.span k⟦X⟧ {y} ∨
    Submodule.span k⟦X⟧ {y} ≤ Submodule.span k⟦X⟧ {x} := by
  by_cases hx : x = 0
  · left; simp [hx]
  by_cases hy : y = 0
  · right; simp [hy]
  obtain ⟨a, h⟩ := span_eq_sh hx hy
  rw [h]
  rcases le_total 0 a with ha | ha
  · left; exact (sh_le_sh_of_le ha _).trans (sh_zero_eq _).le
  · right; exact (sh_zero_eq _).ge.trans (sh_le_sh_of_le ha _)

/- English proof (translation)
Take `⟨s, rfl⟩` from `hN`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp⟩`. Consider the case `insert a s _ ih`. Take `⟨x, hx⟩` from `ih`.

Rewrite using `[Finset.coe_insert, Submodule.span_insert, hx]`. Break down `span_total a x with h | h` into its components or cases. Conclude with `⟨x, sup_eq_right.2 h⟩`. Conclude with `⟨a, sup_eq_left.2 h⟩`.
-/
theorem exists_gen {N : Submodule k⟦X⟧ (Vc k 1)} (hN : N.FG) : ∃ x, N = Submodule.span k⟦X⟧ {x} := by
  classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨x, hx⟩ := ih
    rw [Finset.coe_insert, Submodule.span_insert, hx]
    rcases span_total a x with h | h
    · exact ⟨x, sup_eq_right.2 h⟩
    · exact ⟨a, sup_eq_left.2 h⟩

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h` using `hN.2`. Simplify using `at h`.
-/
theorem ne_bot_of_isLat {N : Submodule k⟦X⟧ (Vc k 1)} (hN : IsLat N) : N ≠ ⊥ := by
  rintro rfl
  have h := hN.2
  simp at h

/- English proof (translation)
Take `⟨x, rfl⟩` from `exists_gen hN.1`. Take `⟨y, rfl⟩` from `exists_gen hN'.1`. Use `span_eq_sh ?_ ?_` and prove the remaining obligations. Introduce and unpack `rfl; exact ne_bot_of_isLat hN (by simp)`. Introduce and unpack `rfl; exact ne_bot_of_isLat hN' (by simp)`.
-/
theorem exists_eq_sh {N N' : Submodule k⟦X⟧ (Vc k 1)} (hN : IsLat N) (hN' : IsLat N') : ∃ a : ℤ, N = sh a N' := by
  obtain ⟨x, rfl⟩ := exists_gen hN.1
  obtain ⟨y, rfl⟩ := exists_gen hN'.1
  refine span_eq_sh ?_ ?_
  · rintro rfl; exact ne_bot_of_isLat hN (by simp)
  · rintro rfl; exact ne_bot_of_isLat hN' (by simp)

end

/- English proof (translation)
Introduce `k G _ _ l n _ _ _ R F r Dt M h1 _ _ e he0 het N hN`. Take `⟨-, hL, hAB, -⟩` from `GlobalTheory.T.obj_and_abc_of_model F M (chr (M.ω ^ (-e))) N hN`. Take `⟨-, hL0, hAB0, -⟩` from `GlobalTheory.T.obj_and_abc_of_model F M (chr (M.ω ^ (-e))) (M.Nχ e) (M.χ_model e he0 het)`. Establish `hχ` using `M.χ_lat e (by omega) het`. Use `choose κ hκ using fun i => exists_eq_sh (hL i) (hL0 i)`.

Establish `key : ∀ i {a b : ℤ}, sh a (M.Nχ e i) ≤ sh b (M.Nχ e i) → b ≤ a` using `fun i a b h => le_of_sh_le_sh (hL0 i).1 (ne_bot_of_isLat (hL0 i)) h`. Establish `habs : ∀ i, |κ i| ≤ Dt.sg l i`. Introduce `i`. Establish `a1` using `GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w N (M.Nχ e) hL hL0 hAB hAB0 i`. Establish `a2` using `GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w (M.Nχ e) N hL0 hL hAB0 hAB i`.

Rewrite `a1` using `[hκ i, sh_sh_eq]`. Rewrite `a2` using `[hκ i]`. Establish `b1` using `key i (a1.trans (sh_zero_eq _).ge)`. Establish `b2` using `key i a2`. Unfold `TopData.sg`.

Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> omega`. Establish `hJ : ∀ i, -Dt.w i + κ i ≤ l * κ (i - 1) + e ∧ l * κ (i - 1) + e ≤ Dt.wst i + κ i`. Introduce `i`. Take `⟨a1, a2⟩` from `hAB i`.

Establish `hp : pull ((F.D (chr (M.ω ^ (-e)))).φ i) (N (i - 1)) = sh (l * κ (i - 1) + e) (M.Nχ e i)`. Rewrite using `[hκ (i - 1), pull_sh R ((F.D (chr (M.ω ^ (-e)))).φ_semi i), (hχ i).2.2.1, sh_sh_eq]`. Rewrite `a1`, `a2` using `[hp, hκ i, sh_sh_eq]`. Conclude with `⟨key i a1, key i a2⟩`. Use `⟨κ, fun i => ⟨hκ i, habs i, fun hi => ?_, fun hi => ?_, fun x => ?_⟩⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hneg`. Establish `c1` using `(Dt.lowG i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).2`. Establish `c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l` using `by exact_mod_cast h1 i`. Establish `c3` using `abs_le.1 (habs i)`. Establish `c4` using `(hJ i).1`.

Establish `c5 : (l : ℤ) * κ (i - 1) ≤ l * (-1)` using `mul_le_mul_of_nonneg_left (by omega) (by positivity)`. Use linear arithmetic over natural numbers and integers. Assume the negation of the conclusion as `hneg`. Establish `c1` using `(Dt.lowBd i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).1`. Establish `c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l` using `by exact_mod_cast h1 i`.

Establish `c3` using `abs_le.1 (habs i)`. Establish `c4` using `(hJ i).2`. Unfold `TopData.wst at c4`. Establish `c5 : (l : ℤ) * 1 ≤ l * κ (i - 1)` using `mul_le_mul_of_nonneg_left (by omega) (by positivity)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hκ i, GlobalTheory.PhiGam.SenShift.sen_sh R _ ((F.D (chr (M.ω ^ (-e)))).γ_semi i) _ (hχ i).1 (hχ i).2.1, (hχ i).2.2.2]`. Unfold `resCount`. Establish `: (((e - 0 : ℤ) : k) = x + (κ i : k)) ↔ (((e - κ i - 0 : ℤ) : k) = x)`. Use `push_cast`. Rewrite using `[sub_zero, sub_zero, sub_eq_iff_eq_add]`.

Simplify using `only [Multiset.filter_singleton, this]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem model_char_sign : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → ∃ κ : ZMod n → ℤ, ∀ i, N i = sh (κ i) (M.Nχ e i) ∧ |κ i| ≤ Dt.sg l i ∧ (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧ ∀ x, sen ((F.D (chr (M.ω ^ (-e)))).γ i) (N i) x = resCount {e - κ i} 0 x := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 _ _ e he0 het N hN
  obtain ⟨-, hL, hAB, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M (chr (M.ω ^ (-e))) N hN
  obtain ⟨-, hL0, hAB0, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M (chr (M.ω ^ (-e))) (M.Nχ e) (M.χ_model e he0 het)
  have hχ := M.χ_lat e (by omega) het
  choose κ hκ using fun i => exists_eq_sh (hL i) (hL0 i)
  have key : ∀ i {a b : ℤ}, sh a (M.Nχ e i) ≤ sh b (M.Nχ e i) → b ≤ a :=
    fun i a b h => le_of_sh_le_sh (hL0 i).1 (ne_bot_of_isLat (hL0 i)) h
  have habs : ∀ i, |κ i| ≤ Dt.sg l i := by
    intro i
    have a1 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w N (M.Nχ e) hL hL0 hAB hAB0 i
    have a2 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w (M.Nχ e) N hL0 hL hAB0 hAB i
    rw [hκ i, sh_sh_eq] at a1
    rw [hκ i] at a2
    have b1 := key i (a1.trans (sh_zero_eq _).ge)
    have b2 := key i a2
    unfold TopData.sg
    rw [abs_le]
    constructor <;> omega
  have hJ : ∀ i, -Dt.w i + κ i ≤ l * κ (i - 1) + e ∧ l * κ (i - 1) + e ≤ Dt.wst i + κ i := by
    intro i
    obtain ⟨a1, a2⟩ := hAB i
    have hp : pull ((F.D (chr (M.ω ^ (-e)))).φ i) (N (i - 1)) = sh (l * κ (i - 1) + e) (M.Nχ e i) := by
      rw [hκ (i - 1), pull_sh R ((F.D (chr (M.ω ^ (-e)))).φ_semi i), (hχ i).2.2.1, sh_sh_eq]
    rw [hp, hκ i, sh_sh_eq] at a1 a2
    exact ⟨key i a1, key i a2⟩
  refine ⟨κ, fun i => ⟨hκ i, habs i, fun hi => ?_, fun hi => ?_, fun x => ?_⟩⟩
  · by_contra hneg
    have c1 := (Dt.lowG i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).2
    have c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l := by exact_mod_cast h1 i
    have c3 := abs_le.1 (habs i)
    have c4 := (hJ i).1
    have c5 : (l : ℤ) * κ (i - 1) ≤ l * (-1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  · by_contra hneg
    have c1 := (Dt.lowBd i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).1
    have c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l := by exact_mod_cast h1 i
    have c3 := abs_le.1 (habs i)
    have c4 := (hJ i).2
    unfold TopData.wst at c4
    have c5 : (l : ℤ) * 1 ≤ l * κ (i - 1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  · rw [hκ i, GlobalTheory.PhiGam.SenShift.sen_sh R _ ((F.D (chr (M.ω ^ (-e)))).γ_semi i) _ (hχ i).1 (hχ i).2.1,
      (hχ i).2.2.2]
    unfold resCount
    have : (((e - 0 : ℤ) : k) = x + (κ i : k)) ↔ (((e - κ i - 0 : ℤ) : k) = x) := by
      push_cast
      rw [sub_zero, sub_zero, sub_eq_iff_eq_add]
    classical
    simp only [Multiset.filter_singleton, this]
    split_ifs <;> simp

end GlobalTheory.Models.CharSign
