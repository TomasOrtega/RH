import Mathlib
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ D y hy t ht ι z hz f hf hft`. Use `choose p hp using hz`. Use `set F := Subfield.closure (Set.range y) with hF`. Establish `hsub : ∀ u : K, u ∈ Subring.closure (Set.range y) ↔ ∃ q : MvPolynomial (Fin D) ℤ, aeval y q = u`. Introduce `u`.

Establish `e1 : u ∈ Subring.closure (Set.range y) ↔ u ∈ Algebra.adjoin ℤ (Set.range y)`. Rewrite using `[Algebra.adjoin_int]`. Both sides reduce to the same expression. Rewrite using `[e1, Algebra.adjoin_range_eq_range_aeval]`. Both sides reduce to the same expression.

Establish `hmem : ∀ q : MvPolynomial (Fin D) ℤ, aeval y q ∈ F`. Introduce `q`. Conclude with `Subfield.subring_closure_le _ ((hsub _).mpr ⟨q, rfl⟩)`. Set `φ : MvPolynomial (Fin D) ℤ →+* F` to `(aeval y).toRingHom.codRestrict F hmem`. Use `letI : Algebra (MvPolynomial (Fin D) ℤ) F := φ.toAlgebra`.

Establish `hφ : ∀ q, ((algebraMap (MvPolynomial (Fin D) ℤ) F q : F) : K) = aeval y q` using `fun q => rfl`. Establish `hinj : Function.Injective (aeval y : MvPolynomial (Fin D) ℤ →ₐ[ℤ] K)` using `algebraicIndependent_iff_injective_aeval.mp hy`. Use `haveI : FaithfulSMul (MvPolynomial (Fin D) ℤ) F := by`. Rewrite using `[faithfulSMul_iff_algebraMap_injective]`. Introduce `a b h`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hφ a, ← hφ b, h]`. Use `haveI : IsFractionRing (MvPolynomial (Fin D) ℤ) F := by`. Use `IsFractionRing.of_field _ _ ?_` and prove the remaining obligations. Introduce `w`.

Take `⟨u, hu, v, hv, huv⟩` from `Subfield.mem_closure_iff.mp w.2`. Take `⟨a, ha⟩` from `(hsub u).mp hu`. Take `⟨b, hb⟩` from `(hsub v).mp hv`. Use `⟨a, b, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Subfield.coe_div, hφ, ha, hb, huv]`. Use `haveI : IsIntegrallyClosed (MvPolynomial (Fin D) ℤ) := UniqueFactorizationMonoid.instIsIntegrallyClosed`. Establish `hcomp : (aeval y).toRingHom.comp (bind₁ p).toRingHom = (aeval z).toRingHom`. Use `RingHom.ext fun q => ?_` and prove the remaining obligations. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_bind₁]`.

Establish `: (fun i => aeval y (p i)) = z` using `funext hp`. Rewrite using `[this]`. Set `t' : F` to `⟨t, ht⟩`. Establish `hint : IsIntegral (MvPolynomial (Fin D) ℤ) t'`. Use `⟨f.map (bind₁ p).toRingHom, hf.map _, ?_⟩` and prove the remaining obligations.

Apply `Subtype.val_injective` to reduce the goal to its premises. Establish `h1` using `Polynomial.hom_eval₂ (f.map (bind₁ p).toRingHom) (algebraMap (MvPolynomial (Fin D) ℤ) F) F.subtype t'`. Use `show F.subtype (Polynomial.eval₂ _ t' _) = F.subtype 0`. Rewrite using `[h1, map_zero]`. Establish `h2 : F.subtype.comp (algebraMap (MvPolynomial (Fin D) ℤ) F) = (aeval y).toRingHom`.

Conclude with `RingHom.ext fun q => rfl`. Rewrite using `[h2, Polynomial.eval₂_map, hcomp]`. Conclude with `hft`. Take `⟨T₀, hT⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Conclude with `⟨T₀, by rw [← hφ, hT]⟩`.
-/
theorem mem_polyring_of_integral_closure_range : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by
  intro K _ D y hy t ht ι z hz f hf hft
  choose p hp using hz
  set F := Subfield.closure (Set.range y) with hF
  have hsub : ∀ u : K, u ∈ Subring.closure (Set.range y) ↔ ∃ q : MvPolynomial (Fin D) ℤ, aeval y q = u := by
    intro u
    have e1 : u ∈ Subring.closure (Set.range y) ↔ u ∈ Algebra.adjoin ℤ (Set.range y) := by
      rw [Algebra.adjoin_int]; rfl
    rw [e1, Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hmem : ∀ q : MvPolynomial (Fin D) ℤ, aeval y q ∈ F := by
    intro q
    exact Subfield.subring_closure_le _ ((hsub _).mpr ⟨q, rfl⟩)
  let φ : MvPolynomial (Fin D) ℤ →+* F := (aeval y).toRingHom.codRestrict F hmem
  letI : Algebra (MvPolynomial (Fin D) ℤ) F := φ.toAlgebra
  have hφ : ∀ q, ((algebraMap (MvPolynomial (Fin D) ℤ) F q : F) : K) = aeval y q := fun q => rfl
  have hinj : Function.Injective (aeval y : MvPolynomial (Fin D) ℤ →ₐ[ℤ] K) :=
    algebraicIndependent_iff_injective_aeval.mp hy
  haveI : FaithfulSMul (MvPolynomial (Fin D) ℤ) F := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinj
    rw [← hφ a, ← hφ b, h]
  haveI : IsFractionRing (MvPolynomial (Fin D) ℤ) F := by
    refine IsFractionRing.of_field _ _ ?_
    intro w
    obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.mp w.2
    obtain ⟨a, ha⟩ := (hsub u).mp hu
    obtain ⟨b, hb⟩ := (hsub v).mp hv
    refine ⟨a, b, ?_⟩
    apply Subtype.ext
    simp only [Subfield.coe_div, hφ, ha, hb, huv]
  haveI : IsIntegrallyClosed (MvPolynomial (Fin D) ℤ) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  have hcomp : (aeval y).toRingHom.comp (bind₁ p).toRingHom = (aeval z).toRingHom := by
    refine RingHom.ext fun q => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_bind₁]
    have : (fun i => aeval y (p i)) = z := funext hp
    rw [this]
  let t' : F := ⟨t, ht⟩
  have hint : IsIntegral (MvPolynomial (Fin D) ℤ) t' := by
    refine ⟨f.map (bind₁ p).toRingHom, hf.map _, ?_⟩
    apply Subtype.val_injective
    have h1 := Polynomial.hom_eval₂ (f.map (bind₁ p).toRingHom) (algebraMap (MvPolynomial (Fin D) ℤ) F) F.subtype t'
    show F.subtype (Polynomial.eval₂ _ t' _) = F.subtype 0
    rw [h1, map_zero]
    have h2 : F.subtype.comp (algebraMap (MvPolynomial (Fin D) ℤ) F) = (aeval y).toRingHom := by
      exact RingHom.ext fun q => rfl
    rw [h2, Polynomial.eval₂_map, hcomp]
    exact hft
  obtain ⟨T₀, hT⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨T₀, by rw [← hφ, hT]⟩

end GlobalTheory
