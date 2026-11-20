import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DinfNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l _ N U`. Establish `hQ : ∀ q : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0`. Introduce `q`. Use `revert q`. Use `show ∀ q : ℚ_[l] ⧸ ZlSub l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0`.

Introduce `q`. Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `_ x`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Take `⟨r, hr⟩` from `pow_unbounded_of_one_lt ‖x‖ hl`.

Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Establish `hn : ‖(l : ℚ_[l]) ^ r * x‖ ≤ 1`. Rewrite using `[norm_mul, norm_pow, Padic.norm_p]`. Establish `hp : (0 : ℝ) < (l : ℝ) ^ r` using `by positivity`.

Rewrite using `[inv_pow, inv_mul_le_iff₀ hp, mul_one]`. Conclude with `hr.le`. Use `⟨⟨(l : ℚ_[l]) ^ r * x, hn⟩, ?_⟩` and prove the remaining obligations. Simplify using `[Algebra.smul_def]`. Both sides reduce to the same expression.

Establish `hconj : ∀ [U.Normal] (g : G k Ω), g ∈ cycU l U → ∀ φ : Dinf l N U, dRep l N U g φ = φ`. Introduce `_ g hg φ`. Establish `hadd` using `φ.2.2.1`. Establish `h1 : (φ : cycU l U → QZ l) 1 = 0`. Use `hadd 1 1` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Simplify using `using this`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `u`. Establish `e1 : conjHom (cycU l U) g u = (⟨g, hg⟩ : cycU l U)⁻¹ * u * ⟨g, hg⟩` using `rfl`.

Express the relevant statement in the definitionally equal form `(φ : cycU l U → QZ l) (conjHom (cycU l U) g u) = _`. Rewrite using `[e1, hadd, hadd]`. Establish `h2` using `hadd (⟨g, hg⟩ : cycU l U)⁻¹ ⟨g, hg⟩`. Rewrite `h2` using `[inv_mul_cancel, h1]`. Rewrite using `[add_comm ((φ : cycU l U → QZ l) _) ((φ : cycU l U → QZ l) u), add_assoc, ← h2, add_zero]`.

Establish `hmono : Dinf l N U ≤ Dinf l 1 U` using `fun φ hφ => ⟨hφ.1, hφ.2.1, hφ.2.2.1, fun A hA => by simp at hA⟩`. Use `⟨fun hU φ => ?_, hmono, ?_, ?_⟩` and prove the remaining obligations. Establish `hC : IsClosed ((cycU l U : Subgroup (G k Ω)) : Set (G k Ω))` using `hU.inter (isClosed_singleton.preimage (continuous_cycZ k Ω l))`. Use `haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hC.isCompact`. Establish `hfin` using `IsLocallyConstant.range_finite φ.2.1`.

Use `choose r hr using hQ`. Use `⟨∑ q ∈ hfin.toFinset, r q, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `u`. Establish `hq : (φ : cycU l U → QZ l) u ∈ hfin.toFinset` using `by simp`.

Express the relevant statement in the definitionally equal form `(l : ℤ_[l]) ^ (∑ q ∈ hfin.toFinset, r q) • (φ : cycU l U → QZ l) u = 0`. Rewrite using `[← Finset.add_sum_erase _ _ hq, pow_add, mul_comm, mul_smul, hr, smul_zero]`. Use `Module.length_le_of_injective (LinearMap.restrict (Submodule.inclusion hmono) (p := Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l])) (q := Submodule.torsionBy ℤ_[l] (Dinf l 1 U) (l : ℤ_[l])) fun x hx => ?_) ?_` and prove the remaining obligations. Rewrite `hx`, the goal using `[Submodule.mem_torsionBy_iff]`. Rewrite using `[← LinearMap.map_smul, hx, map_zero]`.

Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Submodule.inclusion_injective hmono` to reduce the goal to its premises. Conclude with `congrArg Subtype.val hab`. Introduce `_ e g hg`.

Establish `hc : cycZ k Ω l g = 1` using `hg.2`. Establish `hd : dRep l N U g = 1` using `LinearMap.ext fun φ => hconj g hg φ`. Establish `hx : xRep l N U g = 1`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `φ`. Express the relevant statement in the definitionally equal form `((dRep l N U).linHom (Representation.trivial ℤ_[l] (G k Ω) (QZ l)) g f) φ = f φ`. Rewrite using `[Representation.linHom_apply]`. Simplify using `[hconj g⁻¹ (inv_mem hg)]`.

Use `⟨hd, hx, ?_, ?_⟩` and prove the remaining obligations. Use `show ((cycZ k Ω l ^ (-e)) g : ℤ_[l]) • dRep l N U g = 1`. Simplify using `[hc, hd]`. Use `show ((cycZ k Ω l ^ e) g : ℤ_[l]) • xRep l N U g = 1`. Simplify using `[hc, hx]`.
-/
theorem UpperTheory.V.Tower.dinfTors :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G k Ω)), (IsClosed (U : Set (G k Ω)) → ∀ φ : Dinf l N U, ∃ r : ℕ, (l : ℤ_[l]) ^ r • φ = 0) ∧
        Dinf l N U ≤ Dinf l 1 U ∧ xRank l N U ≤ xRank l 1 U ∧
        ∀ [U.Normal] (e : ℤ), ∀ g ∈ cycU l U, dRep l N U g = 1 ∧ xRep l N U g = 1 ∧ dTw l N U e g = 1 ∧ xTw l N U e g = 1 := by
  intro k Ω _ _ _ _ _ l _ N U
  have hQ : ∀ q : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0 := by
    intro q
    revert q
    show ∀ q : ℚ_[l] ⧸ ZlSub l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt ‖x‖ hl
      refine ⟨r, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have hn : ‖(l : ℚ_[l]) ^ r * x‖ ≤ 1 := by
        rw [norm_mul, norm_pow, Padic.norm_p]
        have hp : (0 : ℝ) < (l : ℝ) ^ r := by positivity
        rw [inv_pow, inv_mul_le_iff₀ hp, mul_one]
        exact hr.le
      refine ⟨⟨(l : ℚ_[l]) ^ r * x, hn⟩, ?_⟩
      simp [Algebra.smul_def]
      rfl
  have hconj : ∀ [U.Normal] (g : G k Ω), g ∈ cycU l U → ∀ φ : Dinf l N U, dRep l N U g φ = φ := by
    intro _ g hg φ
    have hadd := φ.2.2.1
    have h1 : (φ : cycU l U → QZ l) 1 = 0 := by
      have := hadd 1 1
      rw [mul_one] at this
      simpa using this
    apply Subtype.ext
    funext u
    have e1 : conjHom (cycU l U) g u = (⟨g, hg⟩ : cycU l U)⁻¹ * u * ⟨g, hg⟩ := rfl
    change (φ : cycU l U → QZ l) (conjHom (cycU l U) g u) = _
    rw [e1, hadd, hadd]
    have h2 := hadd (⟨g, hg⟩ : cycU l U)⁻¹ ⟨g, hg⟩
    rw [inv_mul_cancel, h1] at h2
    rw [add_comm ((φ : cycU l U → QZ l) _) ((φ : cycU l U → QZ l) u), add_assoc, ← h2, add_zero]
  have hmono : Dinf l N U ≤ Dinf l 1 U := fun φ hφ =>
    ⟨hφ.1, hφ.2.1, hφ.2.2.1, fun A hA => by simp at hA⟩
  refine ⟨fun hU φ => ?_, hmono, ?_, ?_⟩
  · classical
    have hC : IsClosed ((cycU l U : Subgroup (G k Ω)) : Set (G k Ω)) :=
      hU.inter (isClosed_singleton.preimage (continuous_cycZ k Ω l))
    haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hC.isCompact
    have hfin := IsLocallyConstant.range_finite φ.2.1
    choose r hr using hQ
    refine ⟨∑ q ∈ hfin.toFinset, r q, ?_⟩
    apply Subtype.ext
    funext u
    have hq : (φ : cycU l U → QZ l) u ∈ hfin.toFinset := by simp
    change (l : ℤ_[l]) ^ (∑ q ∈ hfin.toFinset, r q) • (φ : cycU l U → QZ l) u = 0
    rw [← Finset.add_sum_erase _ _ hq, pow_add, mul_comm, mul_smul, hr, smul_zero]
  · refine Module.length_le_of_injective
      (LinearMap.restrict (Submodule.inclusion hmono)
        (p := Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]))
        (q := Submodule.torsionBy ℤ_[l] (Dinf l 1 U) (l : ℤ_[l])) fun x hx => ?_) ?_
    · rw [Submodule.mem_torsionBy_iff] at hx ⊢
      rw [← LinearMap.map_smul, hx, map_zero]
    · intro a b hab
      apply Subtype.ext
      apply Submodule.inclusion_injective hmono
      exact congrArg Subtype.val hab
  · intro _ e g hg
    have hc : cycZ k Ω l g = 1 := hg.2
    have hd : dRep l N U g = 1 := LinearMap.ext fun φ => hconj g hg φ
    have hx : xRep l N U g = 1 := by
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro φ
      change ((dRep l N U).linHom (Representation.trivial ℤ_[l] (G k Ω) (QZ l)) g f) φ = f φ
      rw [Representation.linHom_apply]
      simp [hconj g⁻¹ (inv_mem hg)]
    refine ⟨hd, hx, ?_, ?_⟩
    · show ((cycZ k Ω l ^ (-e)) g : ℤ_[l]) • dRep l N U g = 1
      simp [hc, hd]
    · show ((cycZ k Ω l ^ e) g : ℤ_[l]) • xRep l N U g = 1
      simp [hc, hx]
