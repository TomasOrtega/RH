import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

noncomputable section
namespace GlobalTheory.ModuliProbe
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `h : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Simplify using `only [constPt]`. Rewrite using `[reassoc_of% h]`.
-/
theorem constPt_idem {k : Type} [Field k] {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) :
    constPt (constPt x) = constPt x := by
  have h : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  simp only [constPt]
  rw [reassoc_of% h]

/- English proof (translation)
Establish `h1` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E`. Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Rewrite `h1` using `[h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_half_degree : 2 * (Module.finrank ℚ E / 2) = Module.finrank ℚ E := by
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rw [h2] at h1
  omega

/- English proof (translation)
The claim follows from `Complex.isPrimitiveRoot_exp n hn.ne'`.
-/
theorem zeta_prim (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn.ne'

/- English proof (translation)
Rewrite using `[KA, IntermediateField.adjoin_le_iff]`. Introduce and unpack `x (rfl | rfl)`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h0 : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact.

Simplify using `using this`. Establish `h1 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2`. Rewrite using `[← map_pow, h0, H.sqrt_neg_disc_sq]`. Simplify using the standard rewrite rules. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases.

Rewrite using `[← h]`. Conclude with `hc τ _`. Establish `: H.rt0 = τ (-(H.rt : E))` using `by rw [map_neg, h, neg_neg]`. Rewrite using `[this]`. Conclude with `hc τ _`.

Establish `hM : 0 < l.M'` using `Nat.lcm_pos (by have := l.three_le; omega) l.A_pos haveI : NeZero l.M' := ⟨hM.ne'⟩`. Establish `hp : zeta l.A ^ l.M' = 1`. Take `⟨c, hc⟩ : l.A ∣ l.M'` from `Nat.dvd_lcm_right _ _`. Rewrite using `[hc, pow_mul, (zeta_prim _ l.A_pos).pow_eq_one, one_pow]`. Take `⟨i, -, hi⟩` from `(zeta_prim _ hM).eq_pow_of_pow_eq_one hp`.

Rewrite using `[← hi]`. Conclude with `pow_mem hz i`.
-/
theorem le_of_conj (l : Level H) (F : IntermediateField ℚ ℂ) (hc : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F)
    (hz : zeta l.M' ∈ F) : KA l ≤ F := by
  rw [KA, IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    have h1 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, h0, H.sqrt_neg_disc_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · rw [← h]; exact hc τ _
    · have : H.rt0 = τ (-(H.rt : E)) := by rw [map_neg, h, neg_neg]
      rw [this]; exact hc τ _
  · have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
    haveI : NeZero l.M' := ⟨hM.ne'⟩
    have hp : zeta l.A ^ l.M' = 1 := by
      obtain ⟨c, hc⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
      rw [hc, pow_mul, (zeta_prim _ l.A_pos).pow_eq_one, one_pow]
    obtain ⟨i, -, hi⟩ := (zeta_prim _ hM).eq_pow_of_pow_eq_one hp
    rw [← hi]
    exact pow_mem hz i

/- English proof (translation)
Establish `hM : 0 < l.M'` using `Nat.lcm_pos (by have := l.three_le; omega) l.A_pos`. Set `F : IntermediateField ℚ ℂ` to `IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'}`. Establish `hc : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F` using `fun τ a => (le_sup_left : _ ≤ F) (AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩)`. Establish `hz : zeta l.M' ∈ F` using `(le_sup_right : _ ≤ F) (IntermediateField.mem_adjoin_simple_self _ _)`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l.M'}) := IntermediateField.adjoin.finiteDimensional ((zeta_prim _ hM).isIntegral hM).tower_top`.

Conclude with `⟨⟨F, inferInstance, hc, hz, le_of_conj l F hc hz⟩⟩`.
-/
theorem coeff_nonempty (l : Level H) : Nonempty (Coeff l) := by
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  let F : IntermediateField ℚ ℂ :=
    IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'}
  have hc : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F := fun τ a =>
    (le_sup_left : _ ≤ F) (AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩)
  have hz : zeta l.M' ∈ F := (le_sup_right : _ ≤ F) (IntermediateField.mem_adjoin_simple_self _ _)
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l.M'}) :=
    IntermediateField.adjoin.finiteDimensional ((zeta_prim _ hM).isIntegral hM).tower_top
  exact ⟨⟨F, inferInstance, hc, hz, le_of_conj l F hc hz⟩⟩

end GlobalTheory.ModuliProbe
