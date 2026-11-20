import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.CountSpanEqZero
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.RelOfComap
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.ExistsOfFixed
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLevStatement
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 40000

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at h`.

Rewrite using `[← A.valuation_le_one_iff, h]`. Rewrite using `[← A.valuation_le_one_iff, map_inv₀, h, inv_one]`. Introduce and unpack `⟨h0, h1, h2⟩`. Rewrite `h1`, `h2` using `[← A.valuation_le_one_iff]`. Rewrite `h2` using `[map_inv₀]`.

Establish `h3 : A.valuation x ≠ 0` using `by simpa using h0`. Conclude with `le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h3)).1 h2)`.
-/
private theorem val_one_iff {K : Type} [Field K] (A : ValuationSubring K) (x : K) :
    A.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ A ∧ x⁻¹ ∈ A := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      simp at h
    · rw [← A.valuation_le_one_iff, h]
    · rw [← A.valuation_le_one_iff, map_inv₀, h, inv_one]
  · rintro ⟨h0, h1, h2⟩
    rw [← A.valuation_le_one_iff] at h1 h2
    rw [map_inv₀] at h2
    have h3 : A.valuation x ≠ 0 := by simpa using h0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h3)).1 h2)

/- English proof (translation)
Rewrite using `[val_one_iff, val_one_iff]`. Simplify using `[ValuationSubring.mem_comap]`.
-/
private theorem val_comap {K : Type} [Field K] (F : Subfield K) (W : ValuationSubring K) (x : F) :
    (W.comap F.subtype).valuation x = 1 ↔ W.valuation (x : K) = 1 := by
  rw [val_one_iff, val_one_iff]
  simp [ValuationSubring.mem_comap]

/- English proof (translation)
Take `⟨W, hW, hloc⟩` from `IsLocalRing.exists_factor_valuationRing (F.subtype.comp B.subtype)`. Use `⟨W, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_comap]`. Use `⟨fun hx => ?_, fun hx => hW ⟨x, hx⟩⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Establish `hi : x⁻¹ ∈ B` using `(B.mem_or_inv_mem x).resolve_left hn`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn B.zero_mem`.

Establish `hu : IsUnit ((F.subtype.comp B.subtype).codRestrict W.toSubring hW ⟨x⁻¹, hi⟩)`. Use `IsUnit.of_mul_eq_one ⟨F.subtype x, hx⟩ (Subtype.ext ?_)` and prove the remaining obligations. Use `show F.subtype x⁻¹ * F.subtype x = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hx0, map_one]`. Take `⟨y, hy⟩` from `(hloc.map_nonunit _ hu).exists_right_inv`.

Establish `hy' : x⁻¹ * (y : F) = 1` using `congrArg Subtype.val hy`. Establish `: (y : F) = x`. Clear denominators, using `at hy'` for the nonvanishing conditions. Conclude with `hy'`. Conclude with `hn (this ▸ y.2)`.
-/
private theorem exists_ext {K : Type} [Field K] (F : Subfield K) (B : ValuationSubring F) :
    ∃ W : ValuationSubring K, W.comap F.subtype = B := by
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (F.subtype.comp B.subtype)
  refine ⟨W, ?_⟩
  ext x
  rw [ValuationSubring.mem_comap]
  refine ⟨fun hx => ?_, fun hx => hW ⟨x, hx⟩⟩
  by_contra hn
  have hi : x⁻¹ ∈ B := (B.mem_or_inv_mem x).resolve_left hn
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hn B.zero_mem
  have hu : IsUnit ((F.subtype.comp B.subtype).codRestrict W.toSubring hW ⟨x⁻¹, hi⟩) := by
    refine IsUnit.of_mul_eq_one ⟨F.subtype x, hx⟩ (Subtype.ext ?_)
    show F.subtype x⁻¹ * F.subtype x = 1
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨y, hy⟩ := (hloc.map_nonunit _ hu).exists_right_inv
  have hy' : x⁻¹ * (y : F) = 1 := congrArg Subtype.val hy
  have : (y : F) = x := by
    field_simp at hy'
    exact hy'
  exact hn (this ▸ y.2)

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ p`. Rewrite using `[ValuationSubring.mem_comap]`. Use `show ((jPoly X H p : lev X H) : X.K) ∈ W`. Rewrite using `[coe_jPoly]`.

Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `W.add_mem _ _ hp hq`. Consider the case `monomial n c`. Rewrite using `[Polynomial.aeval_monomial]`.

Conclude with `W.mul_mem _ _ (h1 c) (pow_mem h2 n)`. Introduce `h`. Establish `h' : ∀ p : Polynomial Ω, Polynomial.aeval X.jK p ∈ W` using `fun p => by`. Rewrite using `[← coe_jPoly X H]`. Conclude with `h p`.

Conclude with `⟨fun c => by simpa using h' (C c), by simpa using h' Polynomial.X⟩`.
-/
private theorem over_iff (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (W : ValuationSubring X.K) :
    X.OverY W ↔ ∀ p : Polynomial Ω, jPoly X H p ∈ W.comap (lev X H).subtype := by
  constructor
  · rintro ⟨h1, h2⟩ p
    rw [ValuationSubring.mem_comap]
    show ((jPoly X H p : lev X H) : X.K) ∈ W
    rw [coe_jPoly]
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact W.add_mem _ _ hp hq
    | monomial n c =>
      rw [Polynomial.aeval_monomial]
      exact W.mul_mem _ _ (h1 c) (pow_mem h2 n)
  · intro h
    have h' : ∀ p : Polynomial Ω, Polynomial.aeval X.jK p ∈ W := fun p => by
      rw [← coe_jPoly X H]
      exact h p
    exact ⟨fun c => by simpa using h' (C c), by simpa using h' Polynomial.X⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h B hB`. Take `⟨W, rfl⟩` from `exists_ext (lev X H) B`. Take `⟨c, hc, hc0, hv⟩` from `h W ((over_iff X H W).2 hB)`. Use `⟨⟨c, hc⟩, fun e => hc0 (congrArg Subtype.val e), ?_⟩` and prove the remaining obligations.

Rewrite using `[val_comap]`. Simplify using `using hv`. Introduce `h W hW`. Take `⟨c, hc0, hv⟩` from `h _ ((over_iff X H W).1 hW)`. Rewrite `hv` using `[val_comap]`.

Conclude with `⟨c, c.2, fun e => hc0 (Subtype.ext e), by simpa using hv⟩`.
-/
private theorem lun_iff (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (m : ℕ) (f : lev X H) :
    (∀ W : ValuationSubring X.K, X.OverY W → ∃ c ∈ lev X H, c ≠ 0 ∧ W.valuation ((f : X.K) / c ^ m) = 1) ↔
      ∀ B : ValuationSubring (lev X H), (∀ p : Polynomial Ω, jPoly X H p ∈ B) → ∃ c : lev X H, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1 := by
  constructor
  · intro h B hB
    obtain ⟨W, rfl⟩ := exists_ext (lev X H) B
    obtain ⟨c, hc, hc0, hv⟩ := h W ((over_iff X H W).2 hB)
    refine ⟨⟨c, hc⟩, fun e => hc0 (congrArg Subtype.val e), ?_⟩
    rw [val_comap]
    simpa using hv
  · intro h W hW
    obtain ⟨c, hc0, hv⟩ := h _ ((over_iff X H W).1 hW)
    rw [val_comap] at hv
    exact ⟨c, c.2, fun e => hc0 (Subtype.ext e), by simpa using hv⟩

/- English proof (translation)
Introduce `f hf` and use `(mem_lev_iff X H' f).2 fun γ hγ => (mem_lev_iff X H f).1 hf γ (h hγ)`.
-/
private theorem lev_anti (X : Tower Ω ε) {H H' : Subgroup SL(2, ℤ)} (h : H' ≤ H) : lev X H ≤ lev X H' := fun f hf =>
  (mem_lev_iff X H' f).2 fun γ hγ => (mem_lev_iff X H f).1 hf γ (h hγ)

end

/- English proof (translation)
Establish `e : algebraMap (RatFunc k) K' = (algebraMap K K').comp (algebraMap (RatFunc k) K)`. Use `IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k)) (RingHom.ext fun p => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) K', ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) K, ← IsScalarTower.algebraMap_apply (Polynomial k) K K']`. Use `haveI : IsScalarTower (RatFunc k) K K' := IsScalarTower.of_algebraMap_eq' e`.

Conclude with `Module.Finite.of_restrictScalars_finite (RatFunc k) _ _`.
-/
private theorem fd_tower (k K K' : Type) [Field k] [Field K] [Field K'] [Algebra (Polynomial k) K] [Algebra (RatFunc k) K]
    [IsScalarTower (Polynomial k) (RatFunc k) K] [Algebra (Polynomial k) K'] [Algebra (RatFunc k) K']
    [IsScalarTower (Polynomial k) (RatFunc k) K'] [Algebra K K'] [IsScalarTower (Polynomial k) K K']
    [FiniteDimensional (RatFunc k) K'] : FiniteDimensional K K' := by
  have e : algebraMap (RatFunc k) K' = (algebraMap K K').comp (algebraMap (RatFunc k) K) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k)) (RingHom.ext fun p => ?_)
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) K', ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) K,
      ← IsScalarTower.algebraMap_apply (Polynomial k) K K']
  haveI : IsScalarTower (RatFunc k) K K' := IsScalarTower.of_algebraMap_eq' e
  exact Module.Finite.of_restrictScalars_finite (RatFunc k) _ _

section
variable {L Γ : Type} [Field L] [Group Γ] (a : Γ → L ≃+* L) (a1 : ∀ f, a 1 f = f)
  (am : ∀ x y f, a (x * y) f = a y (a x f)) {H H' : Subgroup Γ}
  (hn : ∀ γ ∈ H, ∀ δ ∈ H', γ * δ * γ⁻¹ ∈ H') {F F' : Subfield L}
  (hF : ∀ f, f ∈ F ↔ ∀ γ ∈ H, a γ f = f) (hF' : ∀ f, f ∈ F' ↔ ∀ γ ∈ H', a γ f = f)

include a1 am hn hF hF' in
/- English proof (translation)
Rewrite `hf`, the goal using `[hF']`. Introduce `δ hδ`. Establish `e : γ * δ = (γ * δ * γ⁻¹) * γ` using `by group`. Rewrite using `[← am, e, am, hf _ (hn γ hγ δ hδ)]`.
-/
private theorem a_mem {γ : Γ} (hγ : γ ∈ H) {f : L} (hf : f ∈ F') : a γ f ∈ F' := by
  rw [hF'] at hf ⊢
  intro δ hδ
  have e : γ * δ = (γ * δ * γ⁻¹) * γ := by group
  rw [← am, e, am, hf _ (hn γ hγ δ hδ)]

include a1 am hn hF hF' in
/- English proof (translation)
Use `⟨{ toFun := fun x => ⟨a γ x, a_mem a a1 am hn hF hF' hγ x.2⟩ invFun := fun x => ⟨a γ⁻¹ x, a_mem a a1 am hn hF hF' (H.inv_mem hγ) x.2⟩ left_inv := fun x => Subtype.ext ?_ right_inv := fun x => Subtype.ext ?_ map_mul' := fun x y => Subtype.ext ?_ map_add' := fun x y => Subtype.ext …` and prove the remaining obligations. Use `show a γ⁻¹ (a γ x) = x`. Rewrite using `[← am, mul_inv_cancel, a1]`. Use `show a γ (a γ⁻¹ x) = x`. Rewrite using `[← am, inv_mul_cancel, a1]`.

Conclude with `map_mul (a γ) (x : L) y`. Conclude with `map_add (a γ) (x : L) y`. Use `show a γ _ = _`. Rewrite using `[ha]`. Conclude with `(hF _).1 x.2 γ hγ`.
-/
private theorem exists_aut' [Algebra F F'] (ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x) {γ : Γ} (hγ : γ ∈ H) :
    ∃ τ : F' ≃ₐ[F] F', ∀ x : F', ((τ x : F') : L) = a γ x := by
  refine ⟨{ toFun := fun x => ⟨a γ x, a_mem a a1 am hn hF hF' hγ x.2⟩
            invFun := fun x => ⟨a γ⁻¹ x, a_mem a a1 am hn hF hF' (H.inv_mem hγ) x.2⟩
            left_inv := fun x => Subtype.ext ?_
            right_inv := fun x => Subtype.ext ?_
            map_mul' := fun x y => Subtype.ext ?_
            map_add' := fun x y => Subtype.ext ?_
            commutes' := fun x => Subtype.ext ?_ }, fun x => rfl⟩
  · show a γ⁻¹ (a γ x) = x
    rw [← am, mul_inv_cancel, a1]
  · show a γ (a γ⁻¹ x) = x
    rw [← am, inv_mul_cancel, a1]
  · exact map_mul (a γ) (x : L) y
  · exact map_add (a γ) (x : L) y
  · show a γ _ = _
    rw [ha]
    exact (hF _).1 x.2 γ hγ

include a1 am hn hF hF' in
/- English proof (translation)
Set `S : Subgroup (F' ≃ₐ[F] F')` to `{ carrier := {τ | ∃ γ ∈ H, ∀ x : F', ((τ x : F') : L) = a γ x} one_mem' := ⟨1, H.one_mem, fun x => (a1 _).symm⟩ mul_mem' := by`. Introduce and unpack `σ τ ⟨p, hpH, hσ⟩ ⟨q, hqH, hτ⟩`. Use `⟨q * p, H.mul_mem hqH hpH, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[am, ← hτ, ← hσ]`. Both sides reduce to the same expression.

Use the proof step `inv_mem' := by`. Introduce and unpack `σ ⟨p, hpH, hσ⟩`. Use `⟨p⁻¹, H.inv_mem hpH, fun x => ?_⟩` and prove the remaining obligations. Establish `e : (x : L) = a p (σ⁻¹ x : F')`. Rewrite using `[← hσ]`.

Conclude with `congrArg Subtype.val (σ.apply_symm_apply x).symm`. Rewrite using `[e, ← am, mul_inv_cancel, a1] }`. Establish `hS : IntermediateField.fixedField S = ⊥`. Use `le_bot_iff.1 fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`.

Establish `hxH : (x : L) ∈ F` using `(hF _).2 fun γ hγ => by`. Take `⟨τ, hτ⟩` from `exists_aut' a a1 am hn hF hF' ha hγ`. Rewrite using `[← hτ, hx τ ⟨γ, hγ, hτ⟩]`. Conclude with `IntermediateField.mem_bot.2 ⟨⟨x, hxH⟩, Subtype.ext (ha _)⟩`. Establish `hT : S = ⊤`.

Rewrite using `[← IntermediateField.fixingSubgroup_fixedField S, hS, IntermediateField.fixingSubgroup_bot]`. Use `⟨IsGalois.of_fixedField_eq_bot _ _ (hT ▸ hS), fun τ => ?_⟩` and prove the remaining obligations. Establish `: τ ∈ S` using `hT ▸ Subgroup.mem_top τ`. Conclude with `this`.
-/
private theorem gal_surj' [Algebra F F'] (ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x) [FiniteDimensional F F'] :
    IsGalois F F' ∧ ∀ τ : F' ≃ₐ[F] F', ∃ γ ∈ H, ∀ x : F', ((τ x : F') : L) = a γ x := by
  let S : Subgroup (F' ≃ₐ[F] F') :=
    { carrier := {τ | ∃ γ ∈ H, ∀ x : F', ((τ x : F') : L) = a γ x}
      one_mem' := ⟨1, H.one_mem, fun x => (a1 _).symm⟩
      mul_mem' := by
        rintro σ τ ⟨p, hpH, hσ⟩ ⟨q, hqH, hτ⟩
        refine ⟨q * p, H.mul_mem hqH hpH, fun x => ?_⟩
        rw [am, ← hτ, ← hσ]
        rfl
      inv_mem' := by
        rintro σ ⟨p, hpH, hσ⟩
        refine ⟨p⁻¹, H.inv_mem hpH, fun x => ?_⟩
        have e : (x : L) = a p (σ⁻¹ x : F') := by
          rw [← hσ]
          exact congrArg Subtype.val (σ.apply_symm_apply x).symm
        rw [e, ← am, mul_inv_cancel, a1] }
  have hS : IntermediateField.fixedField S = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxH : (x : L) ∈ F := (hF _).2 fun γ hγ => by
      obtain ⟨τ, hτ⟩ := exists_aut' a a1 am hn hF hF' ha hγ
      rw [← hτ, hx τ ⟨γ, hγ, hτ⟩]
    exact IntermediateField.mem_bot.2 ⟨⟨x, hxH⟩, Subtype.ext (ha _)⟩
  have hT : S = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField S, hS, IntermediateField.fixingSubgroup_bot]
  refine ⟨IsGalois.of_fixedField_eq_bot _ _ (hT ▸ hS), fun τ => ?_⟩
  have : τ ∈ S := hT ▸ Subgroup.mem_top τ
  exact this

include a1 am hn hF hF' in
/- English proof (translation)
Take `⟨-, hsurj⟩` from `gal_surj' a a1 am hn hF hF' ha`. Use `choose σ hσ using fun i => exists_aut' a a1 am hn hF hF' ha (hδ1 i)`. Establish `hbij : Function.Bijective σ`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`.

Establish `hfix : ∀ x ∈ F', a (δ i * (δ j)⁻¹) x = x` using `fun x hx => by`. Rewrite using `[am, ← hσ i ⟨x, hx⟩, hij, hσ j ⟨x, hx⟩, ← am, mul_inv_cancel, a1]`. Establish `hmem : δ i * (δ j)⁻¹ ∈ H'` using `faith _ (H.mul_mem (hδ1 i) (H.inv_mem (hδ1 j))) hfix`. Conclude with `(hδ2 (δ i) (hδ1 i)).unique (by rw [mul_inv_cancel]; exact H'.one_mem) hmem`. Introduce `τ`.

Take `⟨γ, hγ, hτ⟩` from `hsurj τ`. Take `⟨i, hi, -⟩` from `hδ2 γ hγ`. Use `⟨i, AlgEquiv.ext fun x => Subtype.ext ?_⟩` and prove the remaining obligations. Establish `e : γ = γ * (δ i)⁻¹ * δ i` using `by group`. Rewrite using `[hσ, hτ, e, am, (hF' _).1 x.2 _ hi]`.

Establish `h1` using `Algebra.norm_eq_prod_automorphisms F f'`. Rewrite `h1` using `[← hbij.prod_comp (fun τ => τ f')]`. Establish `h2` using `congrArg (fun y : F' => (y : L)) h1`. Simplify using `only [ha, SubmonoidClass.coe_finset_prod, hσ] at h2`. Conclude with `h2.symm`.
-/
private theorem prod_eq_norm [Algebra F F'] (ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x) [FiniteDimensional F F']
    [IsGalois F F'] (faith : ∀ γ ∈ H, (∀ f ∈ F', a γ f = f) → γ ∈ H') {ι : Type} [Fintype ι] (δ : ι → Γ)
    (hδ1 : ∀ i, δ i ∈ H) (hδ2 : ∀ x ∈ H, ∃! i, x * (δ i)⁻¹ ∈ H') (f' : F') :
    ∏ i, a (δ i) (f' : L) = ((Algebra.norm F f' : F) : L) := by
  classical
  obtain ⟨-, hsurj⟩ := gal_surj' a a1 am hn hF hF' ha
  choose σ hσ using fun i => exists_aut' a a1 am hn hF hF' ha (hδ1 i)
  have hbij : Function.Bijective σ := by
    constructor
    · intro i j hij
      have hfix : ∀ x ∈ F', a (δ i * (δ j)⁻¹) x = x := fun x hx => by
        rw [am, ← hσ i ⟨x, hx⟩, hij, hσ j ⟨x, hx⟩, ← am, mul_inv_cancel, a1]
      have hmem : δ i * (δ j)⁻¹ ∈ H' := faith _ (H.mul_mem (hδ1 i) (H.inv_mem (hδ1 j))) hfix
      exact (hδ2 (δ i) (hδ1 i)).unique (by rw [mul_inv_cancel]; exact H'.one_mem) hmem
    · intro τ
      obtain ⟨γ, hγ, hτ⟩ := hsurj τ
      obtain ⟨i, hi, -⟩ := hδ2 γ hγ
      refine ⟨i, AlgEquiv.ext fun x => Subtype.ext ?_⟩
      have e : γ = γ * (δ i)⁻¹ * δ i := by group
      rw [hσ, hτ, e, am, (hF' _).1 x.2 _ hi]
  have h1 := Algebra.norm_eq_prod_automorphisms F f'
  rw [← hbij.prod_comp (fun τ => τ f')] at h1
  have h2 := congrArg (fun y : F' => (y : L)) h1
  simp only [ha, SubmonoidClass.coe_finset_prod, hσ] at h2
  exact h2.symm
end

/- English proof (translation)
Use `letI : Algebra F F' := (Subfield.inclusion hle).toAlgebra`. Establish `ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x` using `fun _ => rfl`. Use `haveI : IsScalarTower (Polynomial k) F F' := IsScalarTower.of_algebraMap_eq fun p => Subtype.ext <| by`. Rewrite using `[ha]`. Conclude with `(hc p).symm`.

Use `haveI : FiniteDimensional F F' := fd_tower k F F'`. Use `haveI := (gal_surj' a a1 am hn hF hF' ha).1`. Take `⟨h, hh0, hh⟩` from `UpperTheory.Kd.K4.cdAbs k F m m' f hm hm' hf0 hf`. Take `⟨f', hf'0, hN, hf'⟩` from `UpperTheory.Kd.K4.nsAbs k F F' (m * m') (f / h ^ m) (Nat.mul_pos hm hm') (div_ne_zero hf0 (pow_ne_zero _ hh0)) hh`. Use `⟨f', hf'0, hf', (h : L)⁻¹, inv_ne_zero fun e => hh0 (Subtype.ext e), ?_⟩` and prove the remaining obligations.

Rewrite using `[prod_eq_norm a a1 am hn hF hF' ha faith δ hδ1 hδ2 f', hN, inv_pow, ← div_eq_mul_inv]`. Simplify using the standard rewrite rules.
-/
private theorem abs_step {k L Γ : Type} [Field k] [IsAlgClosed k] [CharZero k] [Field L] [Group Γ] (a : Γ → L ≃+* L)
    (a1 : ∀ f, a 1 f = f) (am : ∀ x y f, a (x * y) f = a y (a x f)) {H H' : Subgroup Γ}
    (hn : ∀ γ ∈ H, ∀ δ ∈ H', γ * δ * γ⁻¹ ∈ H') {F F' : Subfield L} (hle : F ≤ F')
    (hF : ∀ f, f ∈ F ↔ ∀ γ ∈ H, a γ f = f) (hF' : ∀ f, f ∈ F' ↔ ∀ γ ∈ H', a γ f = f)
    [Algebra (Polynomial k) F] [Algebra (RatFunc k) F] [IsScalarTower (Polynomial k) (RatFunc k) F]
    [FiniteDimensional (RatFunc k) F] [Algebra (Polynomial k) F'] [Algebra (RatFunc k) F']
    [IsScalarTower (Polynomial k) (RatFunc k) F'] [FiniteDimensional (RatFunc k) F']
    (hc : ∀ p : Polynomial k, ((algebraMap (Polynomial k) F p : F) : L) = (algebraMap (Polynomial k) F' p : F'))
    (faith : ∀ γ ∈ H, (∀ f ∈ F', a γ f = f) → γ ∈ H') {ι : Type} [Fintype ι] (δ : ι → Γ)
    (hδ1 : ∀ i, δ i ∈ H) (hδ2 : ∀ x ∈ H, ∃! i, x * (δ i)⁻¹ ∈ H') (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (f : F)
    (hf0 : f ≠ 0)
    (hf : ∀ B : ValuationSubring F, (∀ p : Polynomial k, algebraMap (Polynomial k) F p ∈ B) →
      ∃ c : F, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1) :
    ∃ f' : F', f' ≠ 0 ∧ (∀ B : ValuationSubring F', (∀ p : Polynomial k, algebraMap (Polynomial k) F' p ∈ B) →
      ∃ c : F', c ≠ 0 ∧ B.valuation (f' / c ^ (m * m')) = 1) ∧
      ∃ h : L, h ≠ 0 ∧ ∏ i, a (δ i) (f' : L) = (f : L) * h ^ m := by
  letI : Algebra F F' := (Subfield.inclusion hle).toAlgebra
  have ha : ∀ x : F, ((algebraMap F F' x : F') : L) = x := fun _ => rfl
  haveI : IsScalarTower (Polynomial k) F F' := IsScalarTower.of_algebraMap_eq fun p => Subtype.ext <| by
    rw [ha]
    exact (hc p).symm
  haveI : FiniteDimensional F F' := fd_tower k F F'
  haveI := (gal_surj' a a1 am hn hF hF' ha).1
  obtain ⟨h, hh0, hh⟩ := UpperTheory.Kd.K4.cdAbs k F m m' f hm hm' hf0 hf
  obtain ⟨f', hf'0, hN, hf'⟩ := UpperTheory.Kd.K4.nsAbs k F F' (m * m') (f / h ^ m) (Nat.mul_pos hm hm')
    (div_ne_zero hf0 (pow_ne_zero _ hh0)) hh
  refine ⟨f', hf'0, hf', (h : L)⁻¹, inv_ne_zero fun e => hh0 (Subtype.ext e), ?_⟩
  rw [prod_eq_norm a a1 am hn hF hF' ha faith δ hδ1 hδ2 f', hN, inv_pow, ← div_eq_mul_inv]
  simp

/- English proof (translation)
Introduce `Ω _ _ _ ε X H H' M m m' hM hm hm' hΓ hle hneg hn ι _ δ hδ f hf`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Take `⟨hf0, hfH, hfW⟩` from `hf`. Establish `hF0 : (⟨f, hfH⟩ : lev X H) ≠ 0` using `fun e => hf0 (congrArg Subtype.val e)`.

Establish `hfaith : ∀ γ ∈ H, (∀ g ∈ lev X H', X.sl (ofSL γ) g = g) → γ ∈ H'` using `fun γ hγ hfix => (UpperTheory.Kd.K4.faith ε X H' M hM hΓ γ hfix).resolve_right fun h1 => hneg <| by`. Establish `h2` using `H.mul_mem (hle h1) (H.inv_mem hγ)`. Rewrite `h2` using `[neg_mul, mul_inv_cancel]`. Then use the resulting hypothesis. Take `⟨f', hf'0, hf', h, hh0, hprod⟩` from `@abs_step Ω X.K SL(2, ℤ) _ _ _ _ _ (fun γ => (X.sl (ofSL γ)).toRingEquiv) (fun g => by simp [X.sl_one]) (fun x y g => by simp [X.sl_mul]) H H' hn (lev X H) (lev X H') (lev_anti X hle) (mem_lev_iff X H) (mem_lev_iff X H') (algPoly X H) (algRat X H) (isScalarTower_poly_rat X H) (Gl …`. Conclude with `⟨f', ⟨fun e => hf'0 (Subtype.ext e), f'.2, (lun_iff X H' (m * m') f').2 hf'⟩, h, hh0, hprod⟩`.
-/
theorem UpperTheory.Kd.K4.step :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (H H' : Subgroup SL(2, ℤ)) (M m m' : ℕ), 0 < M → 0 < m → 0 < m' → CongruenceSubgroup.Gamma M ≤ H' → H' ≤ H → -1 ∉ H →
      (∀ γ ∈ H, ∀ δ ∈ H', γ * δ * γ⁻¹ ∈ H') → ∀ (ι : Type) [Fintype ι] (δ : ι → SL(2, ℤ)), IsTr H' H δ → ∀ f : X.K, LUnH X H m f →
      ∃ f' : X.K, LUnH X H' (m * m') f' ∧ ∃ h : X.K, h ≠ 0 ∧ ∏ i, X.sl (ofSL (δ i)) f' = f * h ^ m := by
  intro Ω _ _ _ ε X H H' M m m' hM hm hm' hΓ hle hneg hn ι _ δ hδ f hf
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨hf0, hfH, hfW⟩ := hf
  have hF0 : (⟨f, hfH⟩ : lev X H) ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
  have hfaith : ∀ γ ∈ H, (∀ g ∈ lev X H', X.sl (ofSL γ) g = g) → γ ∈ H' := fun γ hγ hfix =>
    (UpperTheory.Kd.K4.faith ε X H' M hM hΓ γ hfix).resolve_right fun h1 => hneg <| by
      have h2 := H.mul_mem (hle h1) (H.inv_mem hγ)
      rwa [neg_mul, mul_inv_cancel] at h2
  obtain ⟨f', hf'0, hf', h, hh0, hprod⟩ :=
    @abs_step Ω X.K SL(2, ℤ) _ _ _ _ _ (fun γ => (X.sl (ofSL γ)).toRingEquiv)
      (fun g => by simp [X.sl_one]) (fun x y g => by simp [X.sl_mul]) H H' hn (lev X H) (lev X H') (lev_anti X hle)
      (mem_lev_iff X H) (mem_lev_iff X H') (algPoly X H) (algRat X H) (isScalarTower_poly_rat X H)
      (GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X H M hM (hΓ.trans hle)) (algPoly X H') (algRat X H') (isScalarTower_poly_rat X H')
      (GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X H' M hM hΓ) (fun p => (coe_jPoly X H p).trans (coe_jPoly X H' p).symm) hfaith ι _ δ hδ.1 hδ.2
      m m' hm hm' ⟨f, hfH⟩ hF0 ((lun_iff X H m ⟨f, hfH⟩).1 hfW)
  exact ⟨f', ⟨fun e => hf'0 (Subtype.ext e), f'.2, (lun_iff X H' (m * m') f').2 hf'⟩, h, hh0, hprod⟩
