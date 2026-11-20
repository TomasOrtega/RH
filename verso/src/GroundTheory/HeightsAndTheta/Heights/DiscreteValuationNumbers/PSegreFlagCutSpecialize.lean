import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutSpecialize
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTruncSpecialize
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Ring

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]

def flagCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (w e : Module.Basis (Fin N) Ω E) (u : Fin N → B)
    (k : ℕ) : Fin N → B :=
  fun j => if (j : ℕ) < k then ∑ i, u i * algebraMap Ω B (w.repr (e i) j) else 0

def pairCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (u : Fin N → B) : (Σ o, bundleIdx (bundleIdx ι M) M' o) → B
  | ⟨none, l⟩ => ∑ i, u i * algebraMap Ω B (φ' l (w i))
  | ⟨some o, j⟩ => projCoordRing y w φ u ⟨o, j⟩

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases hj : (j : ℕ) < k <;> simp [flagCoordRing, hj, map_sum]`.
-/
theorem flagCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (w e : Module.Basis (Fin N) Ω E) (u : Fin N → B) (k : ℕ) :
    g ∘ flagCoordRing w e u k = flagCoordRing w e (g ∘ u) k := by
  funext j
  by_cases hj : (j : ℕ) < k <;> simp [flagCoordRing, hj, map_sum]

/- English proof (translation)
Break down `p with ⟨_ | o, l⟩` into its components or cases. Simplify using `[pairCoordRing, map_sum]`. Simplify using `only [pairCoordRing]`. Conclude with `projCoordRing_map g y w φ u _`.
-/
theorem pairCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (u : Fin N → B) (p : Σ o, bundleIdx (bundleIdx ι M) M' o) :
    g (pairCoordRing y w φ φ' u p) = pairCoordRing y w φ φ' (g ∘ u) p := by
  rcases p with ⟨_ | o, l⟩
  · simp [pairCoordRing, map_sum]
  · simp only [pairCoordRing]
    exact projCoordRing_map g y w φ u _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flagCoord_eq_flagCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (w e : Module.Basis (Fin N) Ω E)
    (t : Fin N → Φ) (k : ℕ) : flagCoord w e t k = flagCoordRing w e t k := rfl

/- English proof (translation)
Use function extensionality and compare the values at `p`. Break down `p with ⟨_ | o, l⟩` into its components or cases. Both sides reduce to the same expression. Simplify using `only [pairProjCoord, pairCoordRing]`. Rewrite using `[projCoord_eq_projCoordRing]`.
-/
theorem pairProjCoord_eq_pairCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (t : Fin N → Φ) : pairProjCoord y w φ φ' t = pairCoordRing y w φ φ' t := by
  funext p
  rcases p with ⟨_ | o, l⟩
  · rfl
  · simp only [pairProjCoord, pairCoordRing]
    rw [projCoord_eq_projCoordRing]

/- English proof (translation)
Use `set S : MvPolynomial (Fin N) Ω := ∑ m, X m * C (w.repr (e m) k) with hS`. Establish `hsum : ∑ i, e.repr (w k) i * w.repr (e i) j = if k = j then 1 else 0`. Establish `h` using `congrArg (fun v => w.repr v j) (e.sum_repr (w k))`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] at h`. Rewrite using `[h]`.

Establish `hx : ∀ x, aeval (fun i => X i - S * C (e.repr (w k) i)) (X x * C (w.repr (e x) j)) = X x * C (w.repr (e x) j) - S * C (e.repr (w k) x * w.repr (e x) j)`. Introduce `x`. Rewrite using `[map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq, sub_mul, map_mul, mul_assoc]`. Rewrite using `[map_sum, Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum, hsum]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Rewrite using `[map_one, mul_one]`. Rewrite using `[map_zero, mul_zero]`.
-/
theorem aeval_flagSub_sigma (w e : Module.Basis (Fin N) Ω E) (k j : Fin N) :
    aeval (fun i => X i - (∑ m, X m * C (w.repr (e m) k)) * C (e.repr (w k) i))
        (∑ i, X i * C (w.repr (e i) j) : MvPolynomial (Fin N) Ω) =
      (∑ i, X i * C (w.repr (e i) j)) - if k = j then ∑ i, X i * C (w.repr (e i) k) else 0 := by
  set S : MvPolynomial (Fin N) Ω := ∑ m, X m * C (w.repr (e m) k) with hS
  have hsum : ∑ i, e.repr (w k) i * w.repr (e i) j = if k = j then 1 else 0 := by
    have h := congrArg (fun v => w.repr v j) (e.sum_repr (w k))
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] at h
    rw [h]
  have hx : ∀ x, aeval (fun i => X i - S * C (e.repr (w k) i)) (X x * C (w.repr (e x) j)) =
      X x * C (w.repr (e x) j) - S * C (e.repr (w k) x * w.repr (e x) j) := by
    intro x
    rw [map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq, sub_mul, map_mul, mul_assoc]
  rw [map_sum, Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum, hsum]
  split_ifs with h
  · subst h; rw [map_one, mul_one]
  · rw [map_zero, mul_zero]

end Ring

/- English proof (translation)
Introduce `O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' _ _ Φ _ _ _ _ e t ht k hk`. Set `ev : (MvPolynomial (Fin N) Ω) →ₐ[Ω] Φ` to `aeval t`. Establish `hev : Function.Injective ev` using `ht`. Set `kk : Fin N` to `⟨k, hk⟩`. Set `sub : (MvPolynomial (Fin N) Ω) →ₐ[Ω] (MvPolynomial (Fin N) Ω)` to `aeval fun i => X i - (∑ m, X m * C (w.repr (e m) kk)) * C (e.repr (w kk) i)`.

Establish `hevF : ∀ j : ℕ, ev ∘ flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) j = flagCoordRing w e t j`. Introduce `j`. Rewrite using `[flagCoordRing_map]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[ev, aeval_X]`. Establish `hsubF : sub ∘ flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) (k + 1) = flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) k`. Use function extensionality and compare the values at `j`. Establish `hs` using `aeval_flagSub_sigma w e kk j`. Simplify using `only [Function.comp_apply, flagCoordRing]`.

Break down `lt_trichotomy (j : ℕ) k with h | h | h` into its components or cases. Establish `hkj : kk ≠ j` using `fun h' => by rw [← h'] at h; exact lt_irrefl _ h`. Rewrite using `[if_pos (by omega), if_pos h]`. Simplify using `only [MvPolynomial.algebraMap_eq]`. Use `hs.trans ?_` and prove the remaining obligations.

Rewrite using `[if_neg hkj, sub_zero]`. Establish `hkj : kk = j` using `Fin.ext h.symm`. Rewrite using `[if_pos (by omega), if_neg (by omega)]`. Simplify using `only [MvPolynomial.algebraMap_eq]`. Use `hs.trans ?_` and prove the remaining obligations.

Rewrite using `[if_pos hkj, hkj, sub_self]`. Rewrite using `[if_neg (by omega), if_neg (by omega), map_zero]`. Set `cA : ℕ → (Σ o, bundleIdx (bundleIdx ι M) M' o) → (MvPolynomial (Fin N) Ω)` to `fun j => pairCoordRing y w φ φ' (flagCoordRing w e X j)`. Establish `hcoord : ∀ j : ℕ, flagClosurePt y w e φ φ' t j = fun p => ev (cA j p)`. Introduce `j`.

Use function extensionality and compare the values at `p`. Simplify using `only [cA, flagClosurePt, pairProjCoord_eq_pairCoordRing, flagCoord_eq_flagCoordRing, pairCoordRing_map, hevF]`. Establish `hsubc : ∀ p, sub (cA (k + 1) p) = cA k p`. Introduce `p`. Simplify using `only [cA]`.

Rewrite using `[pairCoordRing_map, hsubF]`. Set `algA : O →+* (MvPolynomial (Fin N) Ω)` to `(algebraMap Ω (MvPolynomial (Fin N) Ω)).comp (algebraMap O Ω)`. Establish `hevA : (ev : (MvPolynomial (Fin N) Ω) →+* Φ).comp algA = algebraMap O Φ` using `RingHom.ext fun a => by simp [algA, ← IsScalarTower.algebraMap_apply]`. Establish `hsubA : (sub : (MvPolynomial (Fin N) Ω) →+* (MvPolynomial (Fin N) Ω)).comp algA = algA` using `RingHom.ext fun a => by simp [algA]`. Use `⟨fun s hs => ?_, fun s h hsh => ?_⟩` and prove the remaining obligations.

Establish `key : ∀ j : ℕ, pointConeMap O (flagClosurePt y w e φ φ' t j) s = map (ev : (MvPolynomial (Fin N) Ω) →+* Φ) (eval₂ (C.comp algA) (fun p => C (cA j p) * X p.1) s)`. Introduce `j`. Rewrite using `[map_coneMap, hevA, hcoord]`. Simplify using `only [pointConeMap, aeval_def, MvPolynomial.algebraMap_eq]`. Both sides reduce to the same expression.

Establish `ksub : map (sub : (MvPolynomial (Fin N) Ω) →+* (MvPolynomial (Fin N) Ω)) (eval₂ (C.comp algA) (fun p => C (cA (k + 1) p) * X p.1) s) = eval₂ (C.comp algA) (fun p => C (cA k p) * X p.1) s`. Rewrite using `[map_coneMap, hsubA]`. Simplify using `only [AlgHom.coe_toRingHom, hsubc]`. Simplify using `only [pointIdeal, RingHom.mem_ker] at hs ⊢`. Rewrite `hs`, the goal using `[key]`.

Establish `h0 : eval₂ (C.comp algA) (fun p => C (cA (k + 1) p) * X p.1) s = 0` using `map_injective _ hev (hs.trans (map_zero _).symm)`. Rewrite using `[← ksub, h0, map_zero, map_zero]`. Establish `val : ∀ (j : ℕ) (v : MRing (bundleIdx (bundleIdx ι M) M') O), aeval (flagClosurePt y w e φ φ' t j) v = ev (eval₂ algA (cA j) v)`. Introduce `j v`. Rewrite using `[aeval_def, ← AlgHom.coe_toRingHom, eval₂_comp_left, hevA, hcoord]`.

Both sides reduce to the same expression. Establish `vsub : ∀ v : MRing (bundleIdx (bundleIdx ι M) M') O, sub (eval₂ algA (cA (k + 1)) v) = eval₂ algA (cA k) v`. Introduce `v`. Rewrite using `[← AlgHom.coe_toRingHom, eval₂_comp_left, hsubA]`. Use `congr 1`.

Use function extensionality and compare the values at `p`. Conclude with `hsubc p`. Set `τA : (MvPolynomial (Fin N) Ω)` to `∑ j, flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) (k + 1) j * algebraMap Ω (MvPolynomial (Fin N) Ω) (w'.repr (w j) kk)`. Establish `hτ : flagLineCoord w' w e t (k + 1) kk = ev τA`. Simplify using `only [τA, flagLineCoord, map_sum, map_mul, AlgHom.commutes, flagCoord_eq_flagCoordRing, ← hevF, Function.comp_apply]`.

Establish `hsubτ : sub τA = 0`. Simplify using `only [τA, map_sum, map_mul, AlgHom.commutes]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hj` using `congrFun hsubF j`. Simplify using `only [Function.comp_apply] at hj`.

Rewrite using `[hj]`. Distinguish the cases in `hjk : (j : ℕ) < k`. Rewrite using `[repr_flag_inv w w' hF.sameFlag j kk (Fin.lt_def.mpr hjk), map_zero, mul_zero]`. Simplify using `[flagCoordRing, hjk]`. Rewrite `hsh` using `[val, val, hτ]`.

Establish `hs' : eval₂ algA (cA (k + 1)) s = τA * eval₂ algA (cA (k + 1)) h` using `hev (by rw [hsh, map_mul])`. Rewrite using `[val, ← vsub, hs', map_mul, hsubτ, zero_mul, map_zero]`.
-/
theorem SegreFlagCutSpecialize.proof : SegreFlagCutSpecialize.Statement := by
  intro O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' _ _ Φ _ _ _ _ e t ht
    k hk
  classical
  let ev : (MvPolynomial (Fin N) Ω) →ₐ[Ω] Φ := aeval t
  have hev : Function.Injective ev := ht
  let kk : Fin N := ⟨k, hk⟩
  let sub : (MvPolynomial (Fin N) Ω) →ₐ[Ω] (MvPolynomial (Fin N) Ω) := aeval fun i => X i - (∑ m, X m * C (w.repr (e m) kk)) * C (e.repr (w kk) i)
  have hevF : ∀ j : ℕ, ev ∘ flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) j = flagCoordRing w e t j := by
    intro j
    rw [flagCoordRing_map]
    congr 1
    funext i
    simp [ev, aeval_X]
  have hsubF : sub ∘ flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) (k + 1) = flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) k := by
    funext j
    have hs := aeval_flagSub_sigma w e kk j
    simp only [Function.comp_apply, flagCoordRing]
    rcases lt_trichotomy (j : ℕ) k with h | h | h
    · have hkj : kk ≠ j := fun h' => by rw [← h'] at h; exact lt_irrefl _ h
      rw [if_pos (by omega), if_pos h]
      simp only [MvPolynomial.algebraMap_eq]
      refine hs.trans ?_
      rw [if_neg hkj, sub_zero]
    · have hkj : kk = j := Fin.ext h.symm
      rw [if_pos (by omega), if_neg (by omega)]
      simp only [MvPolynomial.algebraMap_eq]
      refine hs.trans ?_
      rw [if_pos hkj, hkj, sub_self]
    · rw [if_neg (by omega), if_neg (by omega), map_zero]
  let cA : ℕ → (Σ o, bundleIdx (bundleIdx ι M) M' o) → (MvPolynomial (Fin N) Ω) :=
    fun j => pairCoordRing y w φ φ' (flagCoordRing w e X j)
  have hcoord : ∀ j : ℕ, flagClosurePt y w e φ φ' t j = fun p => ev (cA j p) := by
    intro j
    funext p
    simp only [cA, flagClosurePt, pairProjCoord_eq_pairCoordRing, flagCoord_eq_flagCoordRing, pairCoordRing_map,
      hevF]
  have hsubc : ∀ p, sub (cA (k + 1) p) = cA k p := by
    intro p
    simp only [cA]
    rw [pairCoordRing_map, hsubF]
  let algA : O →+* (MvPolynomial (Fin N) Ω) := (algebraMap Ω (MvPolynomial (Fin N) Ω)).comp (algebraMap O Ω)
  have hevA : (ev : (MvPolynomial (Fin N) Ω) →+* Φ).comp algA = algebraMap O Φ :=
    RingHom.ext fun a => by simp [algA, ← IsScalarTower.algebraMap_apply]
  have hsubA : (sub : (MvPolynomial (Fin N) Ω) →+* (MvPolynomial (Fin N) Ω)).comp algA = algA := RingHom.ext fun a => by simp [algA]
  refine ⟨fun s hs => ?_, fun s h hsh => ?_⟩
  · have key : ∀ j : ℕ, pointConeMap O (flagClosurePt y w e φ φ' t j) s =
        map (ev : (MvPolynomial (Fin N) Ω) →+* Φ) (eval₂ (C.comp algA) (fun p => C (cA j p) * X p.1) s) := by
      intro j
      rw [map_coneMap, hevA, hcoord]
      simp only [pointConeMap, aeval_def, MvPolynomial.algebraMap_eq]
      rfl
    have ksub : map (sub : (MvPolynomial (Fin N) Ω) →+* (MvPolynomial (Fin N) Ω)) (eval₂ (C.comp algA) (fun p => C (cA (k + 1) p) * X p.1) s) =
        eval₂ (C.comp algA) (fun p => C (cA k p) * X p.1) s := by
      rw [map_coneMap, hsubA]
      simp only [AlgHom.coe_toRingHom, hsubc]
    simp only [pointIdeal, RingHom.mem_ker] at hs ⊢
    rw [key] at hs ⊢
    have h0 : eval₂ (C.comp algA) (fun p => C (cA (k + 1) p) * X p.1) s = 0 :=
      map_injective _ hev (hs.trans (map_zero _).symm)
    rw [← ksub, h0, map_zero, map_zero]
  · have val : ∀ (j : ℕ) (v : MRing (bundleIdx (bundleIdx ι M) M') O),
        aeval (flagClosurePt y w e φ φ' t j) v = ev (eval₂ algA (cA j) v) := by
      intro j v
      rw [aeval_def, ← AlgHom.coe_toRingHom, eval₂_comp_left, hevA, hcoord]
      rfl
    have vsub : ∀ v : MRing (bundleIdx (bundleIdx ι M) M') O,
        sub (eval₂ algA (cA (k + 1)) v) = eval₂ algA (cA k) v := by
      intro v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hsubA]
      congr 1
      funext p
      exact hsubc p
    let τA : (MvPolynomial (Fin N) Ω) := ∑ j, flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) (k + 1) j * algebraMap Ω (MvPolynomial (Fin N) Ω) (w'.repr (w j) kk)
    have hτ : flagLineCoord w' w e t (k + 1) kk = ev τA := by
      simp only [τA, flagLineCoord, map_sum, map_mul, AlgHom.commutes, flagCoord_eq_flagCoordRing, ← hevF,
        Function.comp_apply]
    have hsubτ : sub τA = 0 := by
      simp only [τA, map_sum, map_mul, AlgHom.commutes]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj := congrFun hsubF j
      simp only [Function.comp_apply] at hj
      rw [hj]
      by_cases hjk : (j : ℕ) < k
      · rw [repr_flag_inv w w' hF.sameFlag j kk (Fin.lt_def.mpr hjk), map_zero, mul_zero]
      · simp [flagCoordRing, hjk]
    rw [val, val, hτ] at hsh
    have hs' : eval₂ algA (cA (k + 1)) s = τA * eval₂ algA (cA (k + 1)) h :=
      hev (by rw [hsh, map_mul])
    rw [val, ← vsub, hs', map_mul, hsubτ, zero_mul, map_zero]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
