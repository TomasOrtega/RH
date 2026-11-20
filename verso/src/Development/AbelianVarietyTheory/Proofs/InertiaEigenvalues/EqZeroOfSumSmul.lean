import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries

noncomputable section

open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

namespace GlobalTheory.WachTie

def Laur (L M : Type) [Field L] [AddCommGroup M] [Module L M] : Type := HahnModule ℤ L M

namespace Laur

variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']

instance : AddCommGroup (Laur L M) := inferInstanceAs (AddCommGroup (HahnModule ℤ L M))

instance : Module L⟦X⟧ (Laur L M) :=
  Module.compHom (HahnModule ℤ L M) (HahnSeries.ofPowerSeries ℤ L)

def co : Laur L M →+ (ℤ → M) where
  toFun x := ((HahnModule.of L).symm x).coeff
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Introduce `x y h`. Conclude with `HahnModule.ext x y h`.
-/
theorem co_injective : Function.Injective (co : Laur L M → ℤ → M) := by
  intro x y h
  exact HahnModule.ext x y h

/- English proof (translation)
Conclude with `⟨((HahnModule.of L).symm x).order, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩`.
-/
theorem isLaurent_co (x : Laur L M) : IsLaurent (co x) := by
  exact ⟨((HahnModule.of L).symm x).order, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩

def mk (u : ℤ → M) (hu : IsLaurent u) : Laur L M :=
  HahnModule.of L (HahnSeries.ofSuppBddBelow u (by
    obtain ⟨m, hm⟩ := hu
    exact ⟨m, fun k hk => not_lt.1 fun h => hk (hm k h)⟩))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem co_mk (u : ℤ → M) (hu : IsLaurent u) : co (mk u hu : Laur L M) = u := rfl

/- English proof (translation)
Use `set F := HahnSeries.ofPowerSeries ℤ L f with hFdef`. Establish `hF : ∀ j : ℕ, F.coeff (j : ℤ) = PowerSeries.coeff j f` using `fun j => HahnSeries.ofPowerSeries_apply_coeff f j`. Establish `hneg : ∀ i : ℤ, F.coeff i ≠ 0 → 0 ≤ i`. Introduce `i hi`. Assume the negation of the conclusion as `hlt`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[hFdef, HahnSeries.ofPowerSeries_apply]`. Apply `HahnSeries.embDomain_notin_image_support` to reduce the goal to its premises. Introduce and unpack `⟨j, -, hj⟩`. Express the relevant statement in the definitionally equal form `(j : ℤ) = i at hj`.

Use linear arithmetic over natural numbers and integers. Establish `key : ∀ ij : ℤ × ℤ, F.coeff ij.1 ≠ 0 → ij.1 + ij.2 = k → ((ij.1.toNat : ℕ) : ℤ) = ij.1 ∧ k - ((ij.1.toNat : ℕ) : ℤ) = ij.2`. Introduce `ij h1 h3`. Use `hneg _ h1` as an intermediate fact. Apply the tactic sequence `constructor <;> omega`.

Establish `hlau : IsLaurent ((HahnModule.of L).symm y).coeff` using `⟨_, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩`. Establish `hfin` using `serMul_finite f hlau k`. Rewrite using `[HahnModule.coeff_smul]`. Use `show _ = ∑ᶠ j : ℕ, PowerSeries.coeff j f • ((HahnModule.of L).symm y).coeff (k - (j : ℤ))`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]`.

Apply `Finset.sum_bij_ne_zero (fun ij _ _ => ij.1.toNat)` to reduce the goal to its premises. Introduce `ij hij hne`. Simplify using `only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij`. Take `⟨e1, e2⟩` from `key ij hij.1 hij.2.2`. Rewrite using `[Set.Finite.mem_toFinset, Function.mem_support, e2, ← hF, e1]`.

Conclude with `hne`. Introduce `a ha _ b hb _ hab`. Simplify using `only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at ha hb`. Take `⟨ea1, ea2⟩` from `key a ha.1 ha.2.2`. Take `⟨eb1, eb2⟩` from `key b hb.1 hb.2.2`.

Apply the tactic sequence `apply Prod.ext <;> omega`. Introduce `j _ hne`. Use `⟨((j : ℤ), k - j), ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add]`. Use `⟨?_, right_ne_zero_of_smul hne, by omega⟩` and prove the remaining obligations.

Rewrite using `[hF]`. Conclude with `left_ne_zero_of_smul hne`. Use `show F.coeff (j : ℤ) • ((HahnModule.of L).symm y).coeff (k - j) ≠ 0`. Rewrite using `[hF]`. Conclude with `hne`.

Use `show ((j : ℤ)).toNat = j`. Simplify using the standard rewrite rules. Introduce `ij hij _`. Simplify using `only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij`. Take `⟨e1, e2⟩` from `key ij hij.1 hij.2.2`.

Use `show F.coeff ij.1 • ((HahnModule.of L).symm y).coeff ij.2 = PowerSeries.coeff ij.1.toNat f • ((HahnModule.of L).symm y).coeff (k - (ij.1.toNat : ℤ))`. Rewrite using `[e2, ← hF, e1]`.
-/
private theorem coeff_ofPowerSeries_smul_eq_serMul (f : L⟦X⟧) (y : HahnModule ℤ L M) (k : ℤ) :
    ((HahnModule.of L).symm (HahnSeries.ofPowerSeries ℤ L f • y)).coeff k =
      serMul f ((HahnModule.of L).symm y).coeff k := by
  set F := HahnSeries.ofPowerSeries ℤ L f with hFdef
  have hF : ∀ j : ℕ, F.coeff (j : ℤ) = PowerSeries.coeff j f := fun j =>
    HahnSeries.ofPowerSeries_apply_coeff f j
  have hneg : ∀ i : ℤ, F.coeff i ≠ 0 → 0 ≤ i := by
    intro i hi
    by_contra hlt
    apply hi
    rw [hFdef, HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨j, -, hj⟩
    change (j : ℤ) = i at hj
    omega
  have key : ∀ ij : ℤ × ℤ, F.coeff ij.1 ≠ 0 → ij.1 + ij.2 = k →
      ((ij.1.toNat : ℕ) : ℤ) = ij.1 ∧ k - ((ij.1.toNat : ℕ) : ℤ) = ij.2 := by
    intro ij h1 h3
    have := hneg _ h1
    constructor <;> omega
  have hlau : IsLaurent ((HahnModule.of L).symm y).coeff :=
    ⟨_, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩
  have hfin := serMul_finite f hlau k
  rw [HahnModule.coeff_smul]
  show _ = ∑ᶠ j : ℕ, PowerSeries.coeff j f • ((HahnModule.of L).symm y).coeff (k - (j : ℤ))
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
  apply Finset.sum_bij_ne_zero (fun ij _ _ => ij.1.toNat)
  · intro ij hij hne
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij
    obtain ⟨e1, e2⟩ := key ij hij.1 hij.2.2
    rw [Set.Finite.mem_toFinset, Function.mem_support, e2, ← hF, e1]
    exact hne
  · intro a ha _ b hb _ hab
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at ha hb
    obtain ⟨ea1, ea2⟩ := key a ha.1 ha.2.2
    obtain ⟨eb1, eb2⟩ := key b hb.1 hb.2.2
    apply Prod.ext <;> omega
  · intro j _ hne
    refine ⟨((j : ℤ), k - j), ?_, ?_, ?_⟩
    · simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add]
      refine ⟨?_, right_ne_zero_of_smul hne, by omega⟩
      rw [hF]
      exact left_ne_zero_of_smul hne
    · show F.coeff (j : ℤ) • ((HahnModule.of L).symm y).coeff (k - j) ≠ 0
      rw [hF]
      exact hne
    · show ((j : ℤ)).toNat = j
      simp
  · intro ij hij _
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij
    obtain ⟨e1, e2⟩ := key ij hij.1 hij.2.2
    show F.coeff ij.1 • ((HahnModule.of L).symm y).coeff ij.2 =
      PowerSeries.coeff ij.1.toNat f • ((HahnModule.of L).symm y).coeff (k - (ij.1.toNat : ℤ))
    rw [e2, ← hF, e1]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Conclude with `coeff_ofPowerSeries_smul_eq_serMul f x k`.
-/
theorem co_smul (f : L⟦X⟧) (x : Laur L M) : co (f • x) = serMul f (co x) := by
  funext k
  exact coeff_ofPowerSeries_smul_eq_serMul f x k

/- English proof (translation)
Rewrite using `[co_smul]`. Use `show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (m + n - j) = _`. Rewrite using `[finsum_eq_single _ n]`. Simplify using the standard rewrite rules. Introduce `j hj`.

Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hf j h, zero_smul]`. Rewrite using `[hx (m + n - j) (by omega), smul_zero]`.
-/
private theorem co_smul_add_eq_coeff_smul_co (f : L⟦X⟧) (x : Laur L M) (m : ℤ) (n : ℕ)
    (hf : ∀ j < n, PowerSeries.coeff j f = 0) (hx : ∀ k < m, co x k = 0) :
    co (f • x) (m + n) = PowerSeries.coeff n f • co x m := by
  rw [co_smul]
  show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (m + n - j) = _
  rw [finsum_eq_single _ n]
  · simp
  · intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hf j h, zero_smul]
    · rw [hx (m + n - j) (by omega), smul_zero]

/- English proof (translation)
Use `⟨fun k hk => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[co_smul] show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j) = 0`. Conclude with `(finsum_congr fun j => by rw [hx (k - j) (by omega), smul_zero]).trans finsum_zero`. Establish `e` using `co_smul_add_eq_coeff_smul_co f x m 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) hx`. Simplify using `using e`.
-/
theorem co_smul_low (f : L⟦X⟧) (x : Laur L M) (m : ℤ) (hx : ∀ k < m, co x k = 0) :
    (∀ k < m, co (f • x) k = 0) ∧ co (f • x) m = constantCoeff f • co x m := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [co_smul]
    show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j) = 0
    exact (finsum_congr fun j => by rw [hx (k - j) (by omega), smul_zero]).trans finsum_zero
  · have e := co_smul_add_eq_coeff_smul_co f x m 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) hx
    simpa using e

def single (k : ℤ) (d : M) : Laur L M :=
  mk (Pi.single k d) ⟨k, fun _ h => Pi.single_eq_of_ne h.ne _⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem co_single (k : ℤ) (d : M) : co (single k d : Laur L M) = Pi.single k d := rfl

def tw (c : L) (g : M →ₗ[L] M') : Laur L M →+ Laur L M' where
  toFun x := mk (fun k => c ^ k • g (co x k)) (by
    obtain ⟨m, hm⟩ := isLaurent_co x
    exact ⟨m, fun k hk => by simp [hm k hk]⟩)
  map_zero' := co_injective (by funext k; simp)
  map_add' x y := co_injective (by funext k; simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem co_tw (c : L) (g : M →ₗ[L] M') (x : Laur L M) (k : ℤ) :
    co (tw c g x) k = c ^ k • g (co x k) := rfl

/- English proof (translation)
Apply `co_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Rewrite using `[co_tw, co_smul, co_smul]`. Use `show (c ^ k • g) (∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j)) = ∑ᶠ j : ℕ, PowerSeries.coeff j (rescale c f) • co (tw c g x) (k - j)`. Rewrite using `[map_finsum (c ^ k • g) (serMul_finite f (isLaurent_co x) k)]`.

Use `finsum_congr fun j => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, map_smul, co_tw, PowerSeries.coeff_rescale, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[show c ^ k = c ^ (j : ℤ) * c ^ (k - j) by rw [← zpow_add₀ hc, add_sub_cancel], zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tw_smul {c : L} (hc : c ≠ 0) (g : M →ₗ[L] M') (f : L⟦X⟧) (x : Laur L M) :
    tw c g (f • x) = rescale c f • tw c g x := by
  apply co_injective
  funext k
  rw [co_tw, co_smul, co_smul]
  show (c ^ k • g) (∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j)) =
    ∑ᶠ j : ℕ, PowerSeries.coeff j (rescale c f) • co (tw c g x) (k - j)
  rw [map_finsum (c ^ k • g) (serMul_finite f (isLaurent_co x) k)]
  refine finsum_congr fun j => ?_
  rw [LinearMap.smul_apply, map_smul, co_tw, PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show c ^ k = c ^ (j : ℤ) * c ^ (k - j) by rw [← zpow_add₀ hc, add_sub_cancel], zpow_natCast]
  ring

end Laur

end GlobalTheory.WachTie
