import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

/- English proof (translation)
Establish `h` using `Ideal.mul_mem_mul hx hy`. Rewrite `h` using `[← sq, map_sq hI B', Ideal.zero_eq_bot, Ideal.mem_bot]`. Conclude with `h`.
-/
theorem mul_eq_zero_of_mem_map_sq {R : Type} [CommRing R] {I : Ideal R} (hI : I ^ 2 = 0) {B' : Type} [CommRing B']
    [Algebra R B'] {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B', Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

/- English proof (translation)
Establish `hd : (a x - b x) * t = 0`. Rewrite using `[← h.der x]`. Conclude with `mul_eq_zero_of_mem_map_sq hI (h.mem _) ht`. Rewrite `hd` using `[sub_mul, sub_eq_zero]`. Conclude with `hd`.
-/
theorem isTheta_mul_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {B B₀ B' : Type}
    [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {p : B →+* B₀}
    {a b : B →ₐ[R] B'} {θ : Ω[B₀⁄R₀] →+ B'} (h : IsTheta I p a b θ) (x : B) {t : B'}
    (ht : t ∈ I.map (algebraMap R B')) : a x * t = b x * t := by
  have hd : (a x - b x) * t = 0 := by
    rw [← h.der x]; exact mul_eq_zero_of_mem_map_sq hI (h.mem _) ht
  rw [sub_mul, sub_eq_zero] at hd
  exact hd

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' _ _ a b c θ θ' h`. Use `⟨⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ?_, fun h0 ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, h.smul, mul_neg, isTheta_mul_eq hI h x (h.mem w)]`. Rewrite using `[AddMonoidHom.neg_apply, h.der, neg_sub]`. Conclude with `(Ideal.neg_mem_iff _).2 (h.mem w)`.

Rewrite using `[AddMonoidHom.add_apply, AddMonoidHom.add_apply, h.smul, h'.smul, mul_add, isTheta_mul_eq hI h x (h'.mem w)]`. Rewrite using `[AddMonoidHom.add_apply, h.der, h'.der]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Ideal.add_mem _ (h.mem w) (h'.mem w)`. Use extensionality with `w`.

Establish `hw : w ∈ Submodule.span B₀ (Set.range (KaehlerDifferential.D R₀ B₀))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨y, rfl⟩` from `hy`. Take `⟨x, rfl⟩` from `hp y`. Rewrite using `[h.der, h'.der]`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [map_add, map_add, hu, hv]`.

Consider the case `smul r u _ hu`. Take `⟨x, rfl⟩` from `hp r`. Rewrite using `[h.smul, h'.smul, hu]`. Use extensionality with `x`. Use `h.der x` as an intermediate fact.

Rewrite `this` using `[h0, AddMonoidHom.zero_apply]`. Conclude with `(sub_eq_zero.1 this.symm)`.
-/
theorem isTheta_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' : Type) [CommRing B'] [Algebra R B'] (a b c : B →ₐ[R] B') (θ θ' : Ω[B₀⁄R₀] →+ B'), IsTheta I p a b θ → (IsTheta I p b a (-θ) ∧ (IsTheta I p b c θ' → IsTheta I p a c (θ + θ')) ∧ (IsTheta I p a b θ' → θ = θ') ∧ (θ = 0 → a = b)) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' _ _ a b c θ θ' h
  refine ⟨⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ?_,
    fun h0 ↦ ?_⟩
  · rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, h.smul, mul_neg, isTheta_mul_eq hI h x (h.mem w)]
  · rw [AddMonoidHom.neg_apply, h.der, neg_sub]
  · exact (Ideal.neg_mem_iff _).2 (h.mem w)
  · rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, h.smul, h'.smul, mul_add,
      isTheta_mul_eq hI h x (h'.mem w)]
  · rw [AddMonoidHom.add_apply, h.der, h'.der]; ring
  · exact Ideal.add_mem _ (h.mem w) (h'.mem w)
  · ext w
    have hw : w ∈ Submodule.span B₀ (Set.range (KaehlerDifferential.D R₀ B₀)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, rfl⟩ := hy
      obtain ⟨x, rfl⟩ := hp y
      rw [h.der, h'.der]
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, map_add, hu, hv]
    | smul r u _ hu =>
      obtain ⟨x, rfl⟩ := hp r
      rw [h.smul, h'.smul, hu]
  · ext x
    have := h.der x
    rw [h0, AddMonoidHom.zero_apply] at this
    exact (sub_eq_zero.1 this.symm)

end GlobalTheory.Obs
