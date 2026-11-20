import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlmostNormFinDiag
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

/- English proof (translation)
Establish `h : IsIntegral A b` using `hb.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[A.valuation_le_one_iff, ← hy]`. Conclude with `y.2`.
-/
private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h⟩`. Take `⟨δ, e, hδ, h0, h1⟩` from `GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq F E`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) δ`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hb1 : algebraMap (𝓞 F) F b ≠ 0` using `by simpa using hb0`.

Establish `hb2 : algebraMap F E (algebraMap (𝓞 F) F b) ≠ 0` using `by simpa using hb0`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `hδ (by simp)`. Use `⟨a * b, algebraMap F E (algebraMap (𝓞 F) F b) * e 1, mul_ne_zero ha0 hb0, ?_, fun c hc => ?_, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_mul_mul_comm, h1, ← map_mul, ← map_mul]`. Use `congr 1`. Use `show _ = algebraMap (𝓞 F) F (a * b)`. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts.

Apply `hδ` to reduce the goal to its premises. Use `⟨c / algebraMap (𝓞 F) F b, (algebraMap F E).injective ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, map_mul, map_div₀, hc]`. Clear the denominators using the available nonvanishing facts. Use `⟨e.repr x 0, e.repr x 1 / algebraMap (𝓞 F) F b, ?_⟩ conv_lhs => rw [← e.sum_repr x]` and prove the remaining obligations.

Rewrite using `[Fin.sum_univ_two, h0, map_div₀, Algebra.smul_def, Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem exists_gen (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ (d : 𝓞 F) (t : E), d ≠ 0 ∧ t * t = algebraMap F E d ∧ (∀ c : F, algebraMap F E c ≠ t) ∧
      ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * t := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h⟩
  obtain ⟨δ, e, hδ, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq F E
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) δ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap (𝓞 F) F b ≠ 0 := by simpa using hb0
  have hb2 : algebraMap F E (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hδ (by simp)
  refine ⟨a * b, algebraMap F E (algebraMap (𝓞 F) F b) * e 1, mul_ne_zero ha0 hb0, ?_, fun c hc => ?_, fun x => ?_⟩
  · rw [mul_mul_mul_comm, h1, ← map_mul, ← map_mul]
    congr 1
    show _ = algebraMap (𝓞 F) F (a * b)
    rw [map_mul]
    field_simp
  · apply hδ
    refine ⟨c / algebraMap (𝓞 F) F b, (algebraMap F E).injective ?_⟩
    rw [← h1, map_mul, map_div₀, hc]
    field_simp
  · refine ⟨e.repr x 0, e.repr x 1 / algebraMap (𝓞 F) F b, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, map_div₀, Algebra.smul_def, Algebra.smul_def]
    field_simp

/- English proof (translation)
Introduce `F E Ω _ _ _ _ _ _ _ _ _ _ l _ h`. Take `⟨d, t, hd, ht, hn, hx⟩` from `exists_gen F E h`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F E Ω`.

Use `haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩`. Use `set θ : Ω := algebraMap E Ω t with hθ`. Establish `hθ2 : θ * θ = algebraMap F Ω d`. Rewrite using `[hθ, ← map_mul, ht, ← IsScalarTower.algebraMap_apply]`. Establish `hd' : algebraMap F Ω d ≠ 0` using `by simpa using hd`.

Establish `hθ0 : θ ≠ 0` using `fun h0 => hd' (by rw [← hθ2, h0, zero_mul])`. Establish `hne : -θ ≠ θ` using `fun h0 => hθ0 (by linear_combination (-1 / 2 : Ω) * h0)`. Establish `hpm : ∀ s : G F Ω, s θ = θ ∨ s θ = -θ` using `fun s => by`. Apply `mul_self_eq_mul_self_iff.1` to reduce the goal to its premises. Rewrite using `[← map_mul, hθ2, AlgEquiv.commutes]`.

Establish `hm1 : (-1 : (Qbar l)ˣ) ≠ 1` using `fun h0 => by`. Use `congrArg Units.val h0` as an intermediate fact. Simplify using `only [Units.val_neg, Units.val_one] at this`. Conclude with `absurd this (by norm_num)`. Set `δ : G F Ω →* (Qbar l)ˣ` to `MonoidHom.mk' (fun s => if s θ = θ then 1 else -1) fun a b => by`.

Apply the tactic sequence `rcases hpm a with ha | ha <;> rcases hpm b with hb | hb <;>`. Simplify using `[AlgEquiv.mul_apply, ha, hb, hne]`. Apply the tactic sequence `have hδ : ∀ s, δ s = 1 ↔ s θ = θ := fun s => by show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ↔ _ split_ifs with h0 <;> simp [h0, hm1]`. Use `⟨δ, continuous_of_isOpen_ker' δ ?_, fun h1 => ?_, ⟨fun s => ?_, fun s => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : δ.ker = MulAction.stabilizer (G F Ω) θ` using `Subgroup.ext fun s => hδ s`.

Rewrite using `[e]`. Conclude with `stabilizer_isOpen_of_isIntegral θ`. Establish `hfix : θ ∈ (⊥ : IntermediateField F Ω)`. Rewrite using `[← InfiniteGalois.fixedField_bot]`. Introduce `s`.

Conclude with `(hδ s.1).1 (by rw [h1]; rfl)`. Take `⟨c, hc⟩` from `IntermediateField.mem_bot.1 hfix`. Use `hn c ((algebraMap E Ω).injective ?_)` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_apply, hc]`. Rewrite using `[hδ]`.

Prove the components needed by the constructor for the conclusion. Introduce `hs`. Use `⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => ?_, rfl⟩` and prove the remaining obligations. Take `⟨a, b, rfl⟩` from `hx x`. Use `show s _ = _`.

Rewrite using `[map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, ← hθ, hs]`. Introduce and unpack `⟨u, rfl⟩`. Conclude with `u.commutes t`. Apply the tactic sequence `show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ∨ (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = -1 split_ifs <;> simp`. Establish `h4 : Ideal.span {(4 * d : 𝓞 F)} ≠ 0` using `by simpa using hd`.

Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors h4).subset fun v hv => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hv'`. Apply `hv` to reduce the goal to its premises. Introduce `A hA s hs`. Rewrite using `[hδ]`.

Use `(hpm s).resolve_right fun h0 => hv' ?_` and prove the remaining obligations. Establish `hle : A.valuation θ ≤ 1`. Establish `h1 : A.valuation (θ * θ) ≤ 1`. Rewrite using `[hθ2]`. Conclude with `int_le A (map_isIntegral_int (algebraMap F Ω) d.isIntegral_coe)`.

Rewrite `h1` using `[map_mul]`. Assume the negation of the conclusion as `h2`. Conclude with `absurd h1 (not_le.2 (one_lt_mul'' (not_le.1 h2) (not_le.1 h2)))`. Establish `hlt` using `hs.2 θ hle`. Rewrite `hlt` using `[h0]`.

Use `show v.asIdeal ∣ _`. Rewrite using `[Ideal.dvd_span_singleton, ← hA]`. Establish `e : algebraMap F Ω ((4 * d : 𝓞 F) : F) = (-θ - θ) * (-θ - θ)`. Establish `: ((4 * d : 𝓞 F) : F) = 4 * (d : F)` using `by show algebraMap (𝓞 F) F (4 * d) = _`. Rewrite using `[map_mul, map_ofNat]`.

Rewrite using `[this, map_mul, ← hθ2, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le`.
-/
theorem UpperTheory.exists_quadratic_sign_character :
    UpperTheory.V.Af.Bc.SignEx := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ h
  classical
  obtain ⟨d, t, hd, ht, hn, hx⟩ := exists_gen F E h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F E Ω
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  set θ : Ω := algebraMap E Ω t with hθ
  have hθ2 : θ * θ = algebraMap F Ω d := by
    rw [hθ, ← map_mul, ht, ← IsScalarTower.algebraMap_apply]
  have hd' : algebraMap F Ω d ≠ 0 := by simpa using hd
  have hθ0 : θ ≠ 0 := fun h0 => hd' (by rw [← hθ2, h0, zero_mul])
  have hne : -θ ≠ θ := fun h0 => hθ0 (by linear_combination (-1 / 2 : Ω) * h0)
  have hpm : ∀ s : G F Ω, s θ = θ ∨ s θ = -θ := fun s => by
    apply mul_self_eq_mul_self_iff.1
    rw [← map_mul, hθ2, AlgEquiv.commutes]
  have hm1 : (-1 : (Qbar l)ˣ) ≠ 1 := fun h0 => by
    have := congrArg Units.val h0
    simp only [Units.val_neg, Units.val_one] at this
    exact absurd this (by norm_num)
  let δ : G F Ω →* (Qbar l)ˣ := MonoidHom.mk' (fun s => if s θ = θ then 1 else -1) fun a b => by
    rcases hpm a with ha | ha <;> rcases hpm b with hb | hb <;>
      simp [AlgEquiv.mul_apply, ha, hb, hne]
  have hδ : ∀ s, δ s = 1 ↔ s θ = θ := fun s => by
    show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ↔ _
    split_ifs with h0 <;> simp [h0, hm1]
  refine ⟨δ, continuous_of_isOpen_ker' δ ?_, fun h1 => ?_, ⟨fun s => ?_, fun s => ?_⟩, ?_⟩
  · have e : δ.ker = MulAction.stabilizer (G F Ω) θ := Subgroup.ext fun s => hδ s
    rw [e]
    exact stabilizer_isOpen_of_isIntegral θ
  · have hfix : θ ∈ (⊥ : IntermediateField F Ω) := by
      rw [← InfiniteGalois.fixedField_bot]
      intro s
      exact (hδ s.1).1 (by rw [h1]; rfl)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
    refine hn c ((algebraMap E Ω).injective ?_)
    rw [← IsScalarTower.algebraMap_apply, hc]
  · rw [hδ]
    constructor
    · intro hs
      refine ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => ?_, rfl⟩
      obtain ⟨a, b, rfl⟩ := hx x
      show s _ = _
      rw [map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add, map_mul,
        AlgEquiv.commutes, AlgEquiv.commutes, ← hθ, hs]
    · rintro ⟨u, rfl⟩
      exact u.commutes t
  · show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ∨ (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = -1
    split_ifs <;> simp
  · have h4 : Ideal.span {(4 * d : 𝓞 F)} ≠ 0 := by simpa using hd
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h4).subset fun v hv => ?_)
    by_contra hv'
    apply hv
    intro A hA s hs
    rw [hδ]
    refine (hpm s).resolve_right fun h0 => hv' ?_
    have hle : A.valuation θ ≤ 1 := by
      have h1 : A.valuation (θ * θ) ≤ 1 := by
        rw [hθ2]
        exact int_le A (map_isIntegral_int (algebraMap F Ω) d.isIntegral_coe)
      rw [map_mul] at h1
      by_contra h2
      exact absurd h1 (not_le.2 (one_lt_mul'' (not_le.1 h2) (not_le.1 h2)))
    have hlt := hs.2 θ hle
    rw [h0] at hlt
    show v.asIdeal ∣ _
    rw [Ideal.dvd_span_singleton, ← hA]
    have e : algebraMap F Ω ((4 * d : 𝓞 F) : F) = (-θ - θ) * (-θ - θ) := by
      have : ((4 * d : 𝓞 F) : F) = 4 * (d : F) := by
        show algebraMap (𝓞 F) F (4 * d) = _
        rw [map_mul, map_ofNat]
      rw [this, map_mul, ← hθ2, map_ofNat]
      ring
    rw [e, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le
