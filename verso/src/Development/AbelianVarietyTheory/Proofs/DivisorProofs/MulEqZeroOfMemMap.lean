import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.LiftSys

/- English proof (translation)
Establish `h` using `Ideal.mem_map_of_mem (α : B →+* B') hb`. Rewrite `h` using `[Ideal.map_map, AlgHom.comp_algebraMap]`. Then use the resulting hypothesis.
-/
theorem algHom_mem_map {R B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (I : Ideal R) (α : B →ₐ[R] B') {b : B} (hb : b ∈ I.map (algebraMap R B)) :
    α b ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (α : B →+* B') hb
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at h

/- English proof (translation)
Establish `h` using `Ideal.mul_mem_mul hx hy`. Rewrite `h` using `[← pow_two, map_sq hI B']`. Simplify using `using h`.
-/
theorem mul_eq_zero_of_mem_map {R B' : Type} [CommRing R] [CommRing B'] [Algebra R B'] {I : Ideal R}
    (hI : I ^ 2 = 0) {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) :
    x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_two, map_sq hI B'] at h
  simpa using h

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk X₀ s₀ hpar U B B' _ _ _ _ p hsemi hsurj hker α E hE hEmem`. Establish `hb : IsBaseChange (Sec s₀ U.unop.1) (evForm s₀ U)` using `hpar U`. Set `l : Sec s₀ U.unop.1 → B` to `Function.surjInv hsurj`. Establish `hl : ∀ s, p (l s) = s` using `Function.surjInv_eq hsurj`. Establish `key : ∀ b b' : B, p b = p b' → ∀ x ∈ I.map (algebraMap R B'), α b * x = α b' * x`.

Introduce `b b' h x hx`. Establish `h1 : b - b' ∈ I.map (algebraMap R B)` using `(hker _).1 (by rw [map_sub, h, sub_self])`. Establish `h2` using `mul_eq_zero_of_mem_map hI (algHom_mem_map I α h1) hx`. Rewrite `h2` using `[map_sub, sub_mul]`. Conclude with `sub_eq_zero.1 h2`.

Set `g : Sec s₀ U.unop.1 → GlobForm s₀ →+ B'` to `fun s => AddMonoidHom.mk' (fun w => α (l s) * E w) (fun w w' => by simp [mul_add])`. Set `f : Sec s₀ U.unop.1 →+ GlobForm s₀ →+ B'` to `AddMonoidHom.mk' g (fun s t => by`. Use extensionality with `w`. Use `show α (l (s + t)) * E w = α (l s) * E w + α (l t) * E w`. Rewrite using `[key (l (s + t)) (l s + l t) (by rw [map_add, hl, hl, hl]) _ (hEmem w), map_add, add_mul])`.

Establish `hf : ∀ (r : R₀) (s : Sec s₀ U.unop.1) (w : GlobForm s₀), f (r • s) w = f s (r • w)`. Introduce `r s w`. Take `⟨r', rfl⟩` from `hπ r`. Use `show α (l (π r' • s)) * E w = α (l s) * E (π r' • w)`. Rewrite using `[key (l (π r' • s)) (r' • l s) (by rw [hl, hsemi, hl]) _ (hEmem w), hE, map_smul, smul_mul_assoc, mul_smul_comm]`.

Set `T` to `TensorProduct.liftAddHom f hf`. Set `θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B'` to `T.comp (hb.equiv.symm.toLinearMap.toAddMonoidHom)`. Establish `hθ : ∀ x, θ x = T (hb.equiv.symm x)` using `fun _ => rfl`. Establish `hsm : ∀ (b : B) (t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀), T (p b • t) = α b * T t`. Introduce `b t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s w`. Rewrite using `[TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]`. Use `show α (l (p b • s)) * E w = α b * (α (l s) * E w)`.

Rewrite using `[key (l (p b • s)) (b * l s) (by rw [hl, map_mul, hl, smul_eq_mul]) _ (hEmem w), map_mul, mul_assoc]`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]`. Establish `hmem : ∀ t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀, T t ∈ I.map (algebraMap R B')`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul s w => exact Ideal.mul_mem_left _ _ (hEmem w)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Ideal.add_mem _ hx hy`. Establish `hev : ∀ w : GlobForm s₀, θ (w.1 U) = E w`.

Introduce `w`. Establish `h1 : hb.equiv.symm (w.1 U) = 1 ⊗ₜ w`. Rewrite using `[LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]`. Both sides reduce to the same expression. Rewrite using `[hθ, h1, TensorProduct.liftAddHom_tmul]`.

Use `show α (l 1) * E w = E w`. Rewrite using `[key (l 1) 1 (by rw [hl, map_one]) _ (hEmem w), map_one, one_mul]`. Use `⟨θ, ⟨fun b w => ?_, fun w => hmem _, hev⟩, fun y ⟨hy1, _, hy3⟩ => ?_⟩` and prove the remaining obligations. Rewrite using `[hθ, hθ, LinearEquiv.map_smul, hsm]`. Use extensionality with `x`.

Use `hb.inductionOn x _ ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `w`. Conclude with `(hy3 w).trans (hev w).symm`. Introduce `s n hn`.

Rewrite using `[← hl s, hy1, hn, hθ, hθ, LinearEquiv.map_smul, hsm]`. Introduce `n₁ n₂ h₁ h₂`. Rewrite using `[map_add, map_add, h₁, h₂]`.
-/
theorem exists_unique_formExt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (U : AffOp X₀) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (p : B →+* Sec s₀ U.unop.1), SemiHom π p → Function.Surjective p → (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ (α : B →ₐ[R] B') (E : GlobForm s₀ →+ B'), (∀ (r : R) w, E (π r • w) = r • E w) → (∀ w, E w ∈ I.map (algebraMap R B')) → ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) ∧ (∀ w, θ w ∈ I.map (algebraMap R B')) ∧ ∀ w : GlobForm s₀, θ (w.1 U) = E w := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar U B B' _ _ _ _ p hsemi hsurj hker α E hE hEmem
  have hb : IsBaseChange (Sec s₀ U.unop.1) (evForm s₀ U) := hpar U
  let l : Sec s₀ U.unop.1 → B := Function.surjInv hsurj
  have hl : ∀ s, p (l s) = s := Function.surjInv_eq hsurj
  have key : ∀ b b' : B, p b = p b' → ∀ x ∈ I.map (algebraMap R B'), α b * x = α b' * x := by
    intro b b' h x hx
    have h1 : b - b' ∈ I.map (algebraMap R B) := (hker _).1 (by rw [map_sub, h, sub_self])
    have h2 := mul_eq_zero_of_mem_map hI (algHom_mem_map I α h1) hx
    rw [map_sub, sub_mul] at h2
    exact sub_eq_zero.1 h2
  let g : Sec s₀ U.unop.1 → GlobForm s₀ →+ B' := fun s =>
    AddMonoidHom.mk' (fun w => α (l s) * E w) (fun w w' => by simp [mul_add])
  let f : Sec s₀ U.unop.1 →+ GlobForm s₀ →+ B' :=
    AddMonoidHom.mk' g (fun s t => by
      ext w
      show α (l (s + t)) * E w = α (l s) * E w + α (l t) * E w
      rw [key (l (s + t)) (l s + l t) (by rw [map_add, hl, hl, hl]) _ (hEmem w), map_add, add_mul])
  have hf : ∀ (r : R₀) (s : Sec s₀ U.unop.1) (w : GlobForm s₀), f (r • s) w = f s (r • w) := by
    intro r s w
    obtain ⟨r', rfl⟩ := hπ r
    show α (l (π r' • s)) * E w = α (l s) * E (π r' • w)
    rw [key (l (π r' • s)) (r' • l s) (by rw [hl, hsemi, hl]) _ (hEmem w), hE, map_smul,
      smul_mul_assoc, mul_smul_comm]
  let T := TensorProduct.liftAddHom f hf
  let θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B' := T.comp (hb.equiv.symm.toLinearMap.toAddMonoidHom)
  have hθ : ∀ x, θ x = T (hb.equiv.symm x) := fun _ => rfl
  have hsm : ∀ (b : B) (t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀), T (p b • t) = α b * T t := by
    intro b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show α (l (p b • s)) * E w = α b * (α (l s) * E w)
      rw [key (l (p b • s)) (b * l s) (by rw [hl, map_mul, hl, smul_eq_mul]) _ (hEmem w), map_mul, mul_assoc]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]
  have hmem : ∀ t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀, T t ∈ I.map (algebraMap R B') := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w => exact Ideal.mul_mem_left _ _ (hEmem w)
    | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  have hev : ∀ w : GlobForm s₀, θ (w.1 U) = E w := by
    intro w
    have h1 : hb.equiv.symm (w.1 U) = 1 ⊗ₜ w := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]; rfl
    rw [hθ, h1, TensorProduct.liftAddHom_tmul]
    show α (l 1) * E w = E w
    rw [key (l 1) 1 (by rw [hl, map_one]) _ (hEmem w), map_one, one_mul]
  refine ⟨θ, ⟨fun b w => ?_, fun w => hmem _, hev⟩, fun y ⟨hy1, _, hy3⟩ => ?_⟩
  · rw [hθ, hθ, LinearEquiv.map_smul, hsm]
  · ext x
    refine hb.inductionOn x _ ?_ ?_ ?_ ?_
    · simp
    · intro w
      exact (hy3 w).trans (hev w).symm
    · intro s n hn
      rw [← hl s, hy1, hn, hθ, hθ, LinearEquiv.map_smul, hsm]
    · intro n₁ n₂ h₁ h₂
      rw [map_add, map_add, h₁, h₂]

end GlobalTheory.LiftSys
