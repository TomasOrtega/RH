import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalGenDefs

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

/- English proof (translation)
Establish `hN0 : l ^ r ≠ 0` using `pow_ne_zero r (Fact.out : l.Prime).ne_zero`. Establish `: NeZero (l ^ r)` using `⟨hN0⟩`. Establish `hy0 : y ≠ 0`. Introduce `h0`. Rewrite `hy` using `[h0, zero_pow hN0]`.

Conclude with `ha ((algebraMap F (AlgebraicClosure ℚ)).injective (by rw [← hy, map_zero]))`. Establish `hroot : ∀ σ : G F (AlgebraicClosure ℚ), (σ y / y) ^ (l ^ r) = 1`. Introduce `σ`. Rewrite using `[div_pow, ← map_pow, hy, AlgEquiv.commutes, ← hy, div_self (pow_ne_zero _ hy0)]`. Establish `hex : ∀ σ : G F (AlgebraicClosure ℚ), ∃ i < l ^ r, ζ ^ i = σ y / y` using `fun σ => hζ.eq_pow_of_pow_eq_one (hroot σ)`.

Establish `hmod : ∀ a b : ℕ, ζ ^ a = ζ ^ b ↔ a ≡ b [MOD l ^ r]`. Introduce `a b`. Establish `hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ r)` using `IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)`. Establish `e : ζ ^ a = ζ ^ b ↔ (hζ.isUnit hN0).unit ^ a = (hζ.isUnit hN0).unit ^ b`. Rewrite using `[Units.ext_iff]`.

Simplify using the standard rewrite rules. Rewrite using `[e, pow_eq_pow_iff_modEq, ← hu.eq_orderOf]`. Establish `huniq : ∀ a b : ℕ, ζ ^ a * y = ζ ^ b * y → (a : ZMod (l ^ r)) = b`. Introduce `a b h`. Establish `h' : ζ ^ a = ζ ^ b` using `mul_right_cancel₀ hy0 h`.

Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hmod a b).mp h')`. Set `κ : Dec (F` to `F) A → ZMod (l ^ r) := fun g => ((hex (g : G F (AlgebraicClosure ℚ))).choose : ZMod (l ^ r))`. Establish `hκ : ∀ g : Dec (F` using `F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y := by`. Introduce `g`. Establish `h1` using `(hex (g : G F (AlgebraicClosure ℚ))).choose_spec`.

Establish `hv : (κ g).val = (hex (g : G F (AlgebraicClosure ℚ))).choose` using `ZMod.val_cast_of_lt h1.1`. Rewrite using `[hv, h1.2, div_mul_cancel₀ _ hy0]`. Establish `hκ_iff : ∀ (g : Dec (F` using `F) A) (b : ZMod (l ^ r)), κ g = b ↔ (g : G F (AlgebraicClosure ℚ)) y = ζ ^ b.val * y := by`. Introduce `g b`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl`. Conclude with `hκ g`. Introduce `h`. Use `huniq _ _ ((hκ g).symm.trans h)` as an intermediate fact. Rewrite `this` using `[ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Then use the resulting hypothesis.

Establish `: Algebra.IsIntegral F (AlgebraicClosure ℚ)`. Establish `: Algebra.IsAlgebraic F (AlgebraicClosure ℚ)` using `IsAlgClosure.isAlgebraic`. Use `infer_instance`. Use `⟨κ, hκ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[continuous_discrete_rng]`.

Introduce `b`. Establish `hset : κ ⁻¹' {b} = Subtype.val ⁻¹' {τ : G F (AlgebraicClosure ℚ) | τ y = ζ ^ b.val * y}`. Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Conclude with `hκ_iff g b`.

Rewrite using `[hset]`. Conclude with `(isOpen_setOf_apply (F := F) y (fun z => z = ζ ^ b.val * y)).preimage continuous_subtype_val`. Introduce `g h set c := ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) with hc`. Establish `hgζ : (g : G F (AlgebraicClosure ℚ)) ζ = ζ ^ c.val`. Establish `hspec` using `cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l (MulSemiringAction.toRingAut (G F (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) (g : G F (AlgebraicClosure ℚ))) ζ hζ.pow_eq_one`.

Conclude with `hspec.trans (by rw [hc]; rfl)`. Rewrite using `[hκ_iff]`. Establish `e1 : ((g * h : Dec (F` using `F) A) : G F (AlgebraicClosure ℚ)) y = (g : G F (AlgebraicClosure ℚ)) ((h : G F (AlgebraicClosure ℚ)) y) := rfl`. Rewrite using `[e1, hκ h, map_mul, map_pow, hgζ, hκ g, ← pow_mul, ← mul_assoc, ← pow_add]`. Use `congr 1`.

Apply `(hmod _ _).mpr` to reduce the goal to its premises. Rewrite using `[← ZMod.natCast_eq_natCast_iff]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_kummer' (F : Type) [Field F] [NumberField F] {l r : ℕ} [Fact l.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra F (AlgebraicClosure ℚ)]
    [IsAlgClosure F (AlgebraicClosure ℚ)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r)) (a : F) (ha : a ≠ 0)
    (y : AlgebraicClosure ℚ) (hy : y ^ (l ^ r) = algebraMap F (AlgebraicClosure ℚ) a) :
    ∃ κ : Dec (F := F) A → ZMod (l ^ r),
      (∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y) ∧
      Continuous κ ∧
      ∀ g h : Dec (F := F) A, κ (g * h) =
        κ g + ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)) * κ h := by
  classical
  have hN0 : l ^ r ≠ 0 := pow_ne_zero r (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hN0⟩
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN0] at hy
    exact ha ((algebraMap F (AlgebraicClosure ℚ)).injective (by rw [← hy, map_zero]))

  have hroot : ∀ σ : G F (AlgebraicClosure ℚ), (σ y / y) ^ (l ^ r) = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, ← hy, div_self (pow_ne_zero _ hy0)]
  have hex : ∀ σ : G F (AlgebraicClosure ℚ), ∃ i < l ^ r, ζ ^ i = σ y / y := fun σ => hζ.eq_pow_of_pow_eq_one (hroot σ)
  have hmod : ∀ a b : ℕ, ζ ^ a = ζ ^ b ↔ a ≡ b [MOD l ^ r] := by
    intro a b
    have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ r) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
    have e : ζ ^ a = ζ ^ b ↔ (hζ.isUnit hN0).unit ^ a = (hζ.isUnit hN0).unit ^ b := by
      rw [Units.ext_iff]; simp
    rw [e, pow_eq_pow_iff_modEq, ← hu.eq_orderOf]

  have huniq : ∀ a b : ℕ, ζ ^ a * y = ζ ^ b * y → (a : ZMod (l ^ r)) = b := by
    intro a b h
    have h' : ζ ^ a = ζ ^ b := mul_right_cancel₀ hy0 h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hmod a b).mp h')
  let κ : Dec (F := F) A → ZMod (l ^ r) := fun g => ((hex (g : G F (AlgebraicClosure ℚ))).choose : ZMod (l ^ r))
  have hκ : ∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y := by
    intro g
    have h1 := (hex (g : G F (AlgebraicClosure ℚ))).choose_spec
    have hv : (κ g).val = (hex (g : G F (AlgebraicClosure ℚ))).choose := ZMod.val_cast_of_lt h1.1
    rw [hv, h1.2, div_mul_cancel₀ _ hy0]
  have hκ_iff : ∀ (g : Dec (F := F) A) (b : ZMod (l ^ r)),
      κ g = b ↔ (g : G F (AlgebraicClosure ℚ)) y = ζ ^ b.val * y := by
    intro g b
    constructor
    · rintro rfl; exact hκ g
    · intro h
      have := huniq _ _ ((hκ g).symm.trans h)
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  have : Algebra.IsIntegral F (AlgebraicClosure ℚ) := by
    have : Algebra.IsAlgebraic F (AlgebraicClosure ℚ) := IsAlgClosure.isAlgebraic
    infer_instance
  refine ⟨κ, hκ, ?_, ?_⟩
  · rw [continuous_discrete_rng]
    intro b
    have hset : κ ⁻¹' {b} = Subtype.val ⁻¹' {τ : G F (AlgebraicClosure ℚ) | τ y = ζ ^ b.val * y} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact hκ_iff g b
    rw [hset]
    exact (isOpen_setOf_apply (F := F) y (fun z => z = ζ ^ b.val * y)).preimage continuous_subtype_val
  · intro g h
    set c := ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) with hc
    have hgζ : (g : G F (AlgebraicClosure ℚ)) ζ = ζ ^ c.val := by
      have hspec := cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
        (MulSemiringAction.toRingAut (G F (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) (g : G F (AlgebraicClosure ℚ))) ζ hζ.pow_eq_one
      exact hspec.trans (by rw [hc]; rfl)
    rw [hκ_iff]
    have e1 : ((g * h : Dec (F := F) A) : G F (AlgebraicClosure ℚ)) y = (g : G F (AlgebraicClosure ℚ)) ((h : G F (AlgebraicClosure ℚ)) y) := rfl
    rw [e1, hκ h, map_mul, map_pow, hgζ, hκ g, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 1
    apply (hmod _ _).mpr
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring

end PositivityTheory.Lit1.PTN
