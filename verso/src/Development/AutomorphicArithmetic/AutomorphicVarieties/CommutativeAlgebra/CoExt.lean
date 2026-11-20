import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LayerApproximation

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx m A T h0 hT hm N x`.
-/
private theorem co_ext_approx {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (m : Ideal R)
    (A : Subalgebra O R) (T : Set R) (h0 : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ 2) (N : ℕ) (x : R) :
    ∃ a ∈ A, x - a ∈ m ^ N :=
  _root_.UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx m A T h0 hT hm N x

/- English proof (translation)
Introduce `O _ _ R _ _ _ B _ _ _ R' _ _ I _ i S hS hm f f' ⟨n, hn⟩ hi hs`. Establish `hT : ∀ t ∈ S ∪ i '' (maximalIdeal B : Set B), t ∈ AlgHom.equalizer f f' ∧ t ∈ maximalIdeal R`. Introduce and unpack `t (ht | ⟨b, hb, rfl⟩)`. Conclude with `⟨hs t ht, hS ht⟩`. Use `⟨DFunLike.congr_fun hi b, ?_⟩` and prove the remaining obligations.

Rewrite using `[← res_eq_zero_iff O, res_map, res_eq_zero_iff]`. Conclude with `hb`. Establish `hm' : maximalIdeal R ≤ Ideal.span (S ∪ i '' (maximalIdeal B : Set B)) ⊔ maximalIdeal R ^ 2`. Rewrite using `[Ideal.span_union]`. Conclude with `hm`.

Establish `key : ∀ g : R →ₐ[O] R', (∀ x ∈ maximalIdeal R ^ n, g x ∈ I) → ∀ k : ℕ, ∀ x ∈ maximalIdeal R ^ (n * k), g x ∈ I ^ k`. Introduce `g hg k x hx`. Rewrite `hx` using `[pow_mul]`. Establish `hle : (maximalIdeal R ^ n) ^ k ≤ (I ^ k).comap (g : R →+* R')` using `le_trans (Ideal.pow_right_mono (fun y hy => hg y hy) k) (Ideal.le_comap_pow _ k)`. Conclude with `hle hx`.

Use extensionality with `x`. Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus (I := I) inferInstance _ fun k => ?_` and prove the remaining obligations. Take `⟨a, ha, h⟩` from `co_ext_approx (maximalIdeal R) (AlgHom.equalizer f f') _ (IsCO.res_surj (O := O)) hT hm' (n * k) x`. Establish `ha' : f a = f' a` using `ha`.

Establish `: f x - f' x = f (x - a) - f' (x - a)` using `by rw [map_sub, map_sub, ha']; ring`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, this]`. Conclude with `sub_mem (key f (fun y hy => (hn y hy).1) k _ h) (key f' (fun y hy => (hn y hy).2) k _ h)`.
-/
theorem UpperTheory.V.Alg.co_ext :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (R' : Type) [CommRing R'] [Algebra O R'] (I : Ideal R') [IsHausdorff I R'] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R → maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
      ∀ f f' : R →ₐ[O] R', (∃ n : ℕ, ∀ x ∈ maximalIdeal R ^ n, f x ∈ I ∧ f' x ∈ I) → f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f' := by
  intro O _ _ R _ _ _ B _ _ _ R' _ _ I _ i S hS hm f f' ⟨n, hn⟩ hi hs
  have hT : ∀ t ∈ S ∪ i '' (maximalIdeal B : Set B), t ∈ AlgHom.equalizer f f' ∧ t ∈ maximalIdeal R := by
    rintro t (ht | ⟨b, hb, rfl⟩)
    · exact ⟨hs t ht, hS ht⟩
    · refine ⟨DFunLike.congr_fun hi b, ?_⟩
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hb
  have hm' : maximalIdeal R ≤ Ideal.span (S ∪ i '' (maximalIdeal B : Set B)) ⊔ maximalIdeal R ^ 2 := by
    rw [Ideal.span_union]
    exact hm
  have key : ∀ g : R →ₐ[O] R', (∀ x ∈ maximalIdeal R ^ n, g x ∈ I) →
      ∀ k : ℕ, ∀ x ∈ maximalIdeal R ^ (n * k), g x ∈ I ^ k := by
    intro g hg k x hx
    rw [pow_mul] at hx
    have hle : (maximalIdeal R ^ n) ^ k ≤ (I ^ k).comap (g : R →+* R') :=
      le_trans (Ideal.pow_right_mono (fun y hy => hg y hy) k) (Ideal.le_comap_pow _ k)
    exact hle hx
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  obtain ⟨a, ha, h⟩ := co_ext_approx (maximalIdeal R) (AlgHom.equalizer f f') _
    (IsCO.res_surj (O := O)) hT hm' (n * k) x
  have ha' : f a = f' a := ha
  have : f x - f' x = f (x - a) - f' (x - a) := by rw [map_sub, map_sub, ha']; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, this]
  exact sub_mem (key f (fun y hy => (hn y hy).1) k _ h) (key f' (fun y hy => (hn y hy).2) k _ h)
