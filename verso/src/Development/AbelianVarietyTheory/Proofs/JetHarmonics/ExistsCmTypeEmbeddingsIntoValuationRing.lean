import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

/- English proof (translation)
Establish `hint : ∀ a, ∃ x : V, algebraMap V K x = φ a`. Introduce `a`. Establish `h1 : IsIntegral ℤ a` using `Algebra.IsIntegral.isIntegral a`. Establish `h2 : IsIntegral ℤ (φ a)` using `map_isIntegral_int φ h1`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top`.

Use `choose f hf using hint`. Establish `hinj` using `IsFractionRing.injective V K`. Use `⟨{ toFun := f map_one' := hinj (by rw [hf, map_one, map_one]) map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul]) map_zero' := hinj (by rw [hf, map_zero, map_zero]) map_add' := fun a b => hinj (by rw [map_add, hf, hf, hf, map_add]) }, hf⟩` and prove the remaining obligations.
-/
theorem exists_ringHom_ringOfIntegers_lift {E : Type} [Field E] [NumberField E] {V K : Type} [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] [Field K] [Algebra V K] [IsFractionRing V K] (φ : 𝓞 E →+* K) :
    ∃ ψ : 𝓞 E →+* V, ∀ a, algebraMap V K (ψ a) = φ a := by
  have hint : ∀ a, ∃ x : V, algebraMap V K x = φ a := by
    intro a
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral ℤ (φ a) := map_isIntegral_int φ h1
    exact IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top
  choose f hf using hint
  have hinj := IsFractionRing.injective V K
  refine ⟨{ toFun := f
            map_one' := hinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := hinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [map_add, hf, hf, hf, map_add]) }, hf⟩

/- English proof (translation)
Introduce `E _ _ _ H l c T io p _ X`. Establish `hinj` using `IsFractionRing.injective T.V T.Fr`. Use `choose σV hσV using fun τ : E →+* ℂ => exists_ringHom_ringOfIntegers_lift (V := T.V) (io.comp (embK c τ))`. Establish `hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a)` using `hσV`. Establish `hT : ∀ τ a, algebraMap X.O X.C (X.ι (σV τ a)) = X.ιF (io (embK c τ a))`.

Introduce `τ a`. Rewrite using `[← X.comp, hσV']`. Establish `key : ∀ τ τ' (a : 𝓞 E), τ (a : E) = τ' (a : E) ↔ X.ι (σV τ a) = X.ι (σV τ' a)`. Introduce `τ τ' a`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h1 : embK c τ a = embK c τ' a`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[embK_coe, embK_coe]`. Conclude with `h`.

Establish `h2 : σV τ a = σV τ' a` using `hinj (by rw [hσV', hσV', h1])`. Rewrite using `[h2]`. Introduce `h`. Establish `h1 : embK c τ a = embK c τ' a` using `io.injective (X.ιF.injective (by rw [← hT, ← hT, h]))`. Conclude with `congrArg (fun z : c.F => (z : ℂ)) h1`.

Use `⟨σV, hσV', hT, ?_, fun τ τ' => key τ τ' H.rt, fun τ a => ?_⟩` and prove the remaining obligations. Introduce `τ τ' h`. Use `IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_` and prove the remaining obligations. Conclude with `(key τ τ' a).2 (RingHom.congr_fun h a)`. Establish `h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj]`. Conclude with `hinj (by rw [hσV', hσV', h])`.
-/
theorem exists_types_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ (τT : (E →+* ℂ) → (𝓞 E →+* T.V)), (∀ τ a, algebraMap T.V T.Fr (τT τ a) = io (embK c τ a)) ∧ IsTypes X io (fun τ => X.ι.comp (τT τ)) ∧ Function.Injective (fun τ => X.ι.comp (τT τ)) ∧ (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ X.ι (τT τ H.rt) = X.ι (τT τ' H.rt)) ∧ ∀ τ a, τT (ComplexEmbedding.conjugate τ) a = τT τ (H.bar a) := by
  intro E _ _ _ H l c T io p _ X
  have hinj := IsFractionRing.injective T.V T.Fr
  choose σV hσV using fun τ : E →+* ℂ =>
    exists_ringHom_ringOfIntegers_lift (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hT : ∀ τ a, algebraMap X.O X.C (X.ι (σV τ a)) = X.ιF (io (embK c τ a)) := by
    intro τ a
    rw [← X.comp, hσV']
  have key : ∀ τ τ' (a : 𝓞 E), τ (a : E) = τ' (a : E) ↔ X.ι (σV τ a) = X.ι (σV τ' a) := by
    intro τ τ' a
    constructor
    · intro h
      have h1 : embK c τ a = embK c τ' a := by
        apply Subtype.ext
        rw [embK_coe, embK_coe]
        exact h
      have h2 : σV τ a = σV τ' a := hinj (by rw [hσV', hσV', h1])
      rw [h2]
    · intro h
      have h1 : embK c τ a = embK c τ' a :=
        io.injective (X.ιF.injective (by rw [← hT, ← hT, h]))
      exact congrArg (fun z : c.F => (z : ℂ)) h1
  refine ⟨σV, hσV', hT, ?_, fun τ τ' => key τ τ' H.rt, fun τ a => ?_⟩
  · intro τ τ' h
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    exact (key τ τ' a).2 (RingHom.congr_fun h a)
  · have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    exact hinj (by rw [hσV', hσV', h])

end GlobalTheory.CharDepth
