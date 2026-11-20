import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveRingFinite
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain

noncomputable section

namespace CurveRingFiniteAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Rewrite using `[Valuation.mem_integer_iff, map_div₀]`. Break down `eq_or_ne (v.valuation F (z ⟨p.1, c p.1⟩)) 0 with h0 | h0` into its components or cases.

Simplify using `[h0]`. Conclude with `(div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hc p)`. Consider the case `algebraMap r => rw [eq_intCast]`. Conclude with `intCast_mem _ r`. Consider the case `add x w _ _ hx hw => exact add_mem hx hw`.

Consider the case `mul x w _ _ hx hw => exact mul_mem hx hw`.
-/
theorem mem_integer_of_mem_chartRingZ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (z : (Σ k, ι k) → F) (c : ∀ k, ι k)
    (hc : ∀ p : Σ k, ι k, v.valuation F (z p) ≤ v.valuation F (z ⟨p.1, c p.1⟩)) {b : F}
    (hb : b ∈ chartRingZ z c) : b ∈ (v.valuation F).integer := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    rw [Valuation.mem_integer_iff, map_div₀]
    rcases eq_or_ne (v.valuation F (z ⟨p.1, c p.1⟩)) 0 with h0 | h0
    · simp [h0]
    · exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hc p)
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x w _ _ hx hw => exact add_mem hx hw
  | mul x w _ _ hx hw => exact mul_mem hx hw

omit [Fintype K] in

/- English proof (translation)
It suffices to establish `hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F b ≤ 1 by`. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F b hv`. Rewrite using `[← hr]`. Conclude with `r.2`. Introduce `v`.

Establish `hmax : ∀ k, ∃ i, ∀ j, v.valuation F (z ⟨k, j⟩) ≤ v.valuation F (z ⟨k, i⟩)` using `fun k => by`. Take `⟨i, -, hi⟩` from `Finset.exists_max_image Finset.univ (fun j => v.valuation F (z ⟨k, j⟩)) ⟨c0 k, Finset.mem_univ _⟩`. Conclude with `⟨i, fun j => hi j (Finset.mem_univ _)⟩`. Use `choose c hc using hmax`. Establish `hcz : ∀ k, z ⟨k, c k⟩ ≠ 0` using `fun k h0 => by`.

Establish `h1` using `hc k (c0 k)`. Rewrite `h1` using `[h0, map_zero]`. Conclude with `hc0 k ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))`. Conclude with `mem_integer_of_mem_chartRingZ v z c (fun p => hc p.1 p.2) (hb c hcz)`.
-/
theorem mem_integralClosure {F : Type} [Field F] [NumberField F] (z : (Σ k, ι k) → F) (c0 : ∀ k, ι k)
    (hc0 : ∀ k, z ⟨k, c0 k⟩ ≠ 0) {b : F}
    (hb : ∀ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ z c) :
    b ∈ integralClosure ℤ F := by
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F b ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F b hv
    rw [← hr]
    exact r.2
  intro v
  have hmax : ∀ k, ∃ i, ∀ j, v.valuation F (z ⟨k, j⟩) ≤ v.valuation F (z ⟨k, i⟩) := fun k => by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => v.valuation F (z ⟨k, j⟩))
      ⟨c0 k, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hcz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    have h1 := hc k (c0 k)
    rw [h0, map_zero] at h1
    exact hc0 k ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  exact mem_integer_of_mem_chartRingZ v z c (fun p => hc p.1 p.2) (hb c hcz)

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `charZero_of_injective_algebraMap (R := ℤ) ((injective_iff_map_eq_zero _).mpr fun m hm => ?_)` and prove the remaining obligations. Establish `h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)`. Rewrite using `[Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C, MvPolynomial.algebraMap_apply, hm, C_0]`. Rewrite `h` using `[show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hy, Ideal.mem_bot]`. Then use the resulting hypothesis.
-/
theorem charZero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) ((injective_iff_map_eq_zero _).mpr fun m hm => ?_)
  have h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, hm, C_0]
  rwa [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hy, Ideal.mem_bot] at h

end CurveRingFiniteAlt

open CurveRingFiniteAlt IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y hy`. Use `CurveRingFiniteAlt.charZero y hy.2.2.1` as an intermediate fact. Use `choose c0 hc0 using hy.2.1.2.2`. Establish `hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0` using `fun k h => hc0 k (X_mem_of_eq_zero h)`. Set `r : (Σ k, ι k) → Ω` to `fun p => y p / y ⟨p.1, c0 p.1⟩`.

Set `κ : IntermediateField ℚ Ω` to `IntermediateField.adjoin ℚ (Set.range r)`. Establish `: FiniteDimensional ℚ κ` using `IntermediateField.finiteDimensional_adjoin fun x hx => by`. Take `⟨p, rfl⟩` from `hx`. Conclude with `(isAlgebraic_ratio hy c0 hy0 p).isIntegral`. Establish `: NumberField κ` using `{ to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ κ).injective to_finiteDimensional := inferInstance }`.

Set `z : (Σ k, ι k) → κ` to `fun p => ⟨r p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩`. Establish `hzy : ∀ p q : Σ k, ι k, p.1 = q.1 → ((z p / z q : κ) : Ω) = y p / y q`. Introduce and unpack `⟨k, i⟩ ⟨k', j⟩ h`. Simplify using `only at h`. Substitute `h` using the available equality.

Conclude with `div_div_div_cancel_right₀ (hy0 k) _ _`. Establish `hyz : ∀ p, z p ≠ 0 → y p ≠ 0` using `fun p h hp => h (Subtype.ext (by show y p / y ⟨p.1, c0 p.1⟩ = 0`. Rewrite using `[hp, zero_div]))`. Set `φ : κ →ₐ[ℤ] Ω` to `(IntermediateField.val κ).toRingHom.toIntAlgHom`. Establish `hmap : ∀ c : ∀ k, ι k, chartRingZ y c = (chartRingZ z c).map φ` using `fun c => by`.

Rewrite using `[chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `p`. Conclude with `(hzy p ⟨p.1, c p.1⟩ rfl).symm`. Establish `hκ : ∀ b ∈ curveRing y, b ∈ κ` using `fun b hb => by`.

Establish `h` using `mem_curveRing.mp hb c0 hy0`. Rewrite `h` using `[hmap, Subalgebra.mem_map]`. Take `⟨x, -, rfl⟩` from `h`. Conclude with `x.2`. Establish `hint : ∀ b (hb : b ∈ curveRing y), (⟨b, hκ b hb⟩ : κ) ∈ integralClosure ℤ κ` using `fun b hb => by`.

Use `mem_integralClosure z c0 (fun k h => ?_) fun c hc => ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun x : κ => (x : Ω)) h`. Establish `h2 : y ⟨k, c0 k⟩ / y ⟨k, c0 k⟩ = 0` using `h1`. Conclude with `one_ne_zero ((div_self (hy0 k)).symm.trans h2)`. Establish `h` using `mem_curveRing.mp hb c (fun k => hyz _ (hc k))`.

Rewrite `h` using `[hmap, Subalgebra.mem_map]`. Take `⟨x, hx, hxb⟩` from `h`. Establish `e : x = ⟨b, hκ b hb⟩` using `Subtype.ext hxb`. Conclude with `e ▸ hx`. Establish `: Module.Finite ℤ (integralClosure ℤ κ)` using `inferInstanceAs (Module.Finite ℤ (𝓞 κ))`.

Set `f : curveRing y →ₗ[ℤ] integralClosure ℤ κ` to `{ toFun := fun b => ⟨⟨b, hκ b b.2⟩, hint b b.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Conclude with `Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg (fun w : integralClosure ℤ κ => ((w : κ) : Ω)) h)`.
-/
theorem CurveRingFinite.proof : CurveRingFinite.Statement := by
  intro K _ ι _ Ω _ y hy
  classical
  have := CurveRingFiniteAlt.charZero y hy.2.2.1
  choose c0 hc0 using hy.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k h => hc0 k (X_mem_of_eq_zero h)
  let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c0 p.1⟩
  let κ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (Set.range r)
  have : FiniteDimensional ℚ κ := IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨p, rfl⟩ := hx
    exact (isAlgebraic_ratio hy c0 hy0 p).isIntegral
  have : NumberField κ :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ κ).injective
      to_finiteDimensional := inferInstance }
  let z : (Σ k, ι k) → κ := fun p => ⟨r p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  have hzy : ∀ p q : Σ k, ι k, p.1 = q.1 → ((z p / z q : κ) : Ω) = y p / y q := by
    rintro ⟨k, i⟩ ⟨k', j⟩ h
    simp only at h
    subst h
    exact div_div_div_cancel_right₀ (hy0 k) _ _
  have hyz : ∀ p, z p ≠ 0 → y p ≠ 0 := fun p h hp => h (Subtype.ext (by
    show y p / y ⟨p.1, c0 p.1⟩ = 0
    rw [hp, zero_div]))
  let φ : κ →ₐ[ℤ] Ω := (IntermediateField.val κ).toRingHom.toIntAlgHom
  have hmap : ∀ c : ∀ k, ι k, chartRingZ y c = (chartRingZ z c).map φ := fun c => by
    rw [chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    funext p
    exact (hzy p ⟨p.1, c p.1⟩ rfl).symm
  have hκ : ∀ b ∈ curveRing y, b ∈ κ := fun b hb => by
    have h := mem_curveRing.mp hb c0 hy0
    rw [hmap, Subalgebra.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    exact x.2
  have hint : ∀ b (hb : b ∈ curveRing y), (⟨b, hκ b hb⟩ : κ) ∈ integralClosure ℤ κ := fun b hb => by
    refine mem_integralClosure z c0 (fun k h => ?_) fun c hc => ?_
    · have h1 := congrArg (fun x : κ => (x : Ω)) h
      have h2 : y ⟨k, c0 k⟩ / y ⟨k, c0 k⟩ = 0 := h1
      exact one_ne_zero ((div_self (hy0 k)).symm.trans h2)
    · have h := mem_curveRing.mp hb c (fun k => hyz _ (hc k))
      rw [hmap, Subalgebra.mem_map] at h
      obtain ⟨x, hx, hxb⟩ := h
      have e : x = ⟨b, hκ b hb⟩ := Subtype.ext hxb
      exact e ▸ hx
  have : Module.Finite ℤ (integralClosure ℤ κ) := inferInstanceAs (Module.Finite ℤ (𝓞 κ))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ κ :=
    { toFun := fun b => ⟨⟨b, hκ b b.2⟩, hint b b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h =>
    Subtype.ext (congrArg (fun w : integralClosure ℤ κ => ((w : κ) : Ω)) h)

end

end GroundTheory.Heights₂.Heights.Targets
