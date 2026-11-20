import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.LevelLift

/- English proof (translation)
Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Set `E : V →+ Additive G` to `AddMonoidHom.mk' (fun z => Additive.ofMul (ex z)) (fun z w => by`. Rewrite using `[hadd]`. Use the proof step `rfl)`. Set `F : (J → ℤ) →+ Additive G` to `AddMonoidHom.mk' (fun z => Additive.ofMul (lev z)) (fun z w => by`.

Rewrite using `[hl]`. Use the proof step `rfl)`. Use `choose z hz using fun j : J => honto (lev (Pi.single j 1))`. Establish `hw : ∀ j, k • z j ∈ Λ` using `fun j => by`. Rewrite using `[← hker]`.

Establish `h1 : E (k • z j) = k • E (z j)` using `map_nsmul E k (z j)`. Establish `h2 : ex (k • z j) = ex (z j) ^ k` using `congrArg Additive.toMul h1`. Rewrite using `[h2, hz, hp]`. Set `l : (J → ℤ) →ₗ[ℤ] Λ` to `(Pi.basisFun ℤ J).constr ℤ fun j => ⟨k • z j, hw j⟩`. Establish `hlj : ∀ j, (l (Pi.single j 1) : V) = k • z j` using `fun j => by`.

Use `(Pi.basisFun ℤ J).constr_basis ℤ (fun j => (⟨k • z j, hw j⟩ : Λ)) j` as an intermediate fact. Rewrite `this` using `[Pi.basisFun_apply]`. Conclude with `congrArg Subtype.val this`. Set `F' : (J → ℤ) →+ Additive G` to `AddMonoidHom.mk' (fun a => E ((k : ℂ)⁻¹ • (l a : V))) (fun a b => by`. Rewrite using `[map_add, Submodule.coe_add, smul_add, map_add])`.

Use `⟨l, fun a => ?_⟩` and prove the remaining obligations. Establish `hmem : a ∈ F.eqLocus F'`. Establish `ha : a = ∑ j, a j • (Pi.single j 1 : J → ℤ)`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Rewrite using `[ha]`. Use `AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ ?_ _` and prove the remaining obligations. Use `show Additive.ofMul (lev (Pi.single j 1)) = Additive.ofMul (ex ((k : ℂ)⁻¹ • (l (Pi.single j 1) : V)))`. Rewrite using `[hlj, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul, hz]`. Conclude with `congrArg Additive.toMul (show F a = F' a from hmem)`.
-/
theorem exists_linear_lift {J G V : Type} [Fintype J] [DecidableEq J] [Group G] [AddCommGroup V] [Module ℂ V]
    (ex : V → G) (hadd : ∀ z w, ex (z + w) = ex z * ex w) (honto : Function.Surjective ex)
    (Λ : Submodule ℤ V) (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (k : ℕ) (hk : 0 < k) (lev : (J → ℤ) → G)
    (hl : ∀ a b, lev (a + b) = lev a * lev b) (hp : ∀ a, lev a ^ k = 1) :
    ∃ l : (J → ℤ) →ₗ[ℤ] Λ, ∀ a, lev a = ex ((k : ℂ)⁻¹ • (l a : V)) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  let E : V →+ Additive G := AddMonoidHom.mk' (fun z => Additive.ofMul (ex z)) (fun z w => by
    rw [hadd]; rfl)
  let F : (J → ℤ) →+ Additive G := AddMonoidHom.mk' (fun z => Additive.ofMul (lev z)) (fun z w => by
    rw [hl]; rfl)
  choose z hz using fun j : J => honto (lev (Pi.single j 1))
  have hw : ∀ j, k • z j ∈ Λ := fun j => by
    rw [← hker]
    have h1 : E (k • z j) = k • E (z j) := map_nsmul E k (z j)
    have h2 : ex (k • z j) = ex (z j) ^ k := congrArg Additive.toMul h1
    rw [h2, hz, hp]
  let l : (J → ℤ) →ₗ[ℤ] Λ := (Pi.basisFun ℤ J).constr ℤ fun j => ⟨k • z j, hw j⟩
  have hlj : ∀ j, (l (Pi.single j 1) : V) = k • z j := fun j => by
    have := (Pi.basisFun ℤ J).constr_basis ℤ (fun j => (⟨k • z j, hw j⟩ : Λ)) j
    rw [Pi.basisFun_apply] at this
    exact congrArg Subtype.val this
  let F' : (J → ℤ) →+ Additive G := AddMonoidHom.mk' (fun a => E ((k : ℂ)⁻¹ • (l a : V))) (fun a b => by
    rw [map_add, Submodule.coe_add, smul_add, map_add])
  refine ⟨l, fun a => ?_⟩
  have hmem : a ∈ F.eqLocus F' := by
    have ha : a = ∑ j, a j • (Pi.single j 1 : J → ℤ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [ha]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ ?_ _
    show Additive.ofMul (lev (Pi.single j 1)) = Additive.ofMul (ex ((k : ℂ)⁻¹ • (l (Pi.single j 1) : V)))
    rw [hlj, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul, hz]
  exact congrArg Additive.toMul (show F a = F' a from hmem)

/- English proof (translation)
Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Take `⟨c, hc⟩` from `Complex.exp_eq_exp_iff_exists_int.1 h`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Establish `: ((n - m : ℤ) : ℂ) = ((k * c : ℤ) : ℂ)`.

Use `push_cast`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Clear denominators, using `at hc` for the nonvanishing conditions. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Use `first`.

Consider the case `linear_combination (2 * Real.pi * Complex.I) * hc`. Consider the case `linear_combination -(2 * Real.pi * Complex.I) * hc`. Consider the case `linear_combination hc`. Consider the case `linear_combination -hc`. Conclude with `this` after adjusting the coercions.
-/
theorem dvd_sub_of_exp_eq (k : ℕ) (hk : 0 < k) (m n : ℤ)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : (k : ℤ) ∣ n - m := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  obtain ⟨c, hc⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨c, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : ((n - m : ℤ) : ℂ) = ((k * c : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hc
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    first
      | linear_combination (2 * Real.pi * Complex.I) * hc
      | linear_combination -(2 * Real.pi * Complex.I) * hc
      | linear_combination hc
      | linear_combination -hc
  exact_mod_cast this

/- English proof (translation)
Introduce `h k P lev u Ef hk hl hp hW hE`. Take `⟨l, hlift⟩` from `exists_linear_lift u.ex u.ex_add u.ex_onto u.Λ u.ker k hk lev hl hp`. Use `⟨l, hlift, fun a b => ?_⟩` and prove the remaining obligations. Establish `h1` using `hW a b (Units.mk0 _ (Complex.exp_ne_zero _)) rfl`. Establish `h2` using `hE (l a) (l b) (Units.mk0 _ (Complex.exp_ne_zero _)) rfl`.

Rewrite `h2` using `[← hlift a, ← hlift b]`. Establish `h3` using `GlobalTheory.weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k (lev a) (lev b) _ _ h1 h2`. Conclude with `dvd_sub_of_exp_eq k hk _ _ (congrArg Units.val h3)`.
-/
theorem exists_lattice_lift : ∀ (h k : ℕ) (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (u : HolUnif P.A P.L h) (Ef : LinearMap.BilinForm ℤ u.Λ), 0 < k → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → (∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e)) → (∀ (x y : u.Λ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((k : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e)) → ∃ l : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] u.Λ, (∀ a, lev a = u.ex ((k : ℂ)⁻¹ • (l a : Fin h → ℂ))) ∧ ∀ a b, (k : ℤ) ∣ Ef (l a) (l b) - omegaStd a b := by
  intro h k P lev u Ef hk hl hp hW hE
  obtain ⟨l, hlift⟩ := exists_linear_lift u.ex u.ex_add u.ex_onto u.Λ u.ker k hk lev hl hp
  refine ⟨l, hlift, fun a b => ?_⟩
  have h1 := hW a b (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  have h2 := hE (l a) (l b) (Units.mk0 _ (Complex.exp_ne_zero _)) rfl
  rw [← hlift a, ← hlift b] at h2
  have h3 := GlobalTheory.weilIs_unique_fieldPoint _ P.A P.L P.isLB ℂ (𝟙 _) k (lev a) (lev b) _ _ h1 h2
  exact dvd_sub_of_exp_eq k hk _ _ (congrArg Units.val h3)

end GlobalTheory.LevelLift
