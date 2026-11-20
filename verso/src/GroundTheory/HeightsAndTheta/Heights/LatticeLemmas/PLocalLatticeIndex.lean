import Mathlib
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocalLatticeIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct Module

noncomputable section

section Card

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Establish `h1` using `(HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1 u.isUnit`. Establish `h0 : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0`. Introduce `h`. Conclude with `u.ne_zero (Subtype.ext h)`. Rewrite using `[← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v h0]`.

Rewrite using `[show Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 from h1]`. Simplify using the standard rewrite rules.
-/
theorem LocalLatticeIndex.norm_unit (u : (v.adicCompletionIntegers K)ˣ) :
    ‖((u : v.adicCompletionIntegers K) : v.adicCompletion K)‖ = 1 := by
  have h1 := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1 u.isUnit
  have h0 : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  rw [← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v h0]
  rw [show Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 from h1]
  simp

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Establish `hne : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ≠ ⊥`. Rewrite using `[hϖ.maximalIdeal_eq, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hϖ.ne_zero`.

Establish `hcard : Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(u : v.adicCompletionIntegers K) * ϖ ^ n}) = Ideal.absNorm v.asIdeal ^ n`. Rewrite using `[Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne, Submodule.cardQuot_apply, ← GroundTheory.Global.natCard_residueField_adicCompletionIntegers v]`. Both sides reduce to the same expression. Establish `hϖn : ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹` using `GroundTheory.Global.normalizedAbv_of_irreducible v hϖ`. Rewrite using `[hcard, Nat.cast_pow]`.

Use `push_cast`. Rewrite using `[norm_mul, norm_pow, LocalLatticeIndex.norm_unit, hϖn, one_mul, inv_pow, inv_inv]`.
-/
theorem LocalLatticeIndex.card_quot_span {a : v.adicCompletionIntegers K} (ha : a ≠ 0) :
    (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a}) : ℝ) =
      ‖(a : v.adicCompletion K)‖⁻¹ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hne : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ≠ ⊥ := by
    rw [hϖ.maximalIdeal_eq, Ne, Ideal.span_singleton_eq_bot]
    exact hϖ.ne_zero
  have hcard : Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {(u : v.adicCompletionIntegers K) * ϖ ^ n}) = Ideal.absNorm v.asIdeal ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne,
      Submodule.cardQuot_apply, ← GroundTheory.Global.natCard_residueField_adicCompletionIntegers v]
    rfl
  have hϖn : ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ :=
    GroundTheory.Global.normalizedAbv_of_irreducible v hϖ
  rw [hcard, Nat.cast_pow]
  push_cast
  rw [norm_mul, norm_pow, LocalLatticeIndex.norm_unit, hϖn, one_mul, inv_pow, inv_inv]

end Card

section General

variable {K : Type*} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {E : Type*} [AddCommGroup E] [Module (v.adicCompletion K) E]
  [Module (v.adicCompletionIntegers K) E]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]

/- English proof (translation)
Use `.of_smul_eq_zero fun r x h => ?_` and prove the remaining obligations. Establish `h' : algebraMap _ (v.adicCompletion K) r • (x : E) = 0`. Rewrite using `[algebraMap_smul, ← Submodule.coe_smul, h, Submodule.coe_zero]`. Break down `smul_eq_zero.1 h' with hr | hx` into its components or cases. Conclude with `Or.inl ((FaithfulSMul.algebraMap_injective _ (v.adicCompletion K)).eq_iff' (map_zero _) |>.1 hr)`.

Conclude with `Or.inr (Subtype.ext hx)`.
-/
theorem LocalLatticeIndex.isTorsionFree (A : Submodule (v.adicCompletionIntegers K) E) :
    Module.IsTorsionFree (v.adicCompletionIntegers K) A := by
  refine .of_smul_eq_zero fun r x h => ?_
  have h' : algebraMap _ (v.adicCompletion K) r • (x : E) = 0 := by
    rw [algebraMap_smul, ← Submodule.coe_smul, h, Submodule.coe_zero]
  rcases smul_eq_zero.1 h' with hr | hx
  · exact Or.inl ((FaithfulSMul.algebraMap_injective _ (v.adicCompletion K)).eq_iff' (map_zero _) |>.1 hr)
  · exact Or.inr (Subtype.ext hx)

/- English proof (translation)
Use `LocalLatticeIndex.isTorsionFree A` as an intermediate fact. Establish `: Module.Finite (v.adicCompletionIntegers K) A` using `Module.Finite.iff_fg.2 hfg`. Use `set ι := Module.Free.ChooseBasisIndex (v.adicCompletionIntegers K) A`. Set `b` to `Module.Free.chooseBasis (v.adicCompletionIntegers K) A`. Establish `hli : LinearIndependent (v.adicCompletion K) (fun i => (b i : E))`.

Rewrite using `[← LinearIndependent.iff_fractionRing (v.adicCompletionIntegers K) (v.adicCompletion K)]`. Conclude with `b.linearIndependent.map' A.subtype (Submodule.ker_subtype A)`. Establish `hspanR : Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => (b i : E)) = A`. Establish `: (Set.range fun i => (b i : E)) = A.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]`. Establish `hsp' : ⊤ ≤ Submodule.span (v.adicCompletion K) (Set.range fun i => (b i : E))`. Rewrite using `[← hsp]`. Apply `Submodule.span_le.2` to reduce the goal to its premises.

Introduce `x hx`. Establish `hx' : x ∈ Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => (b i : E))`. Rewrite using `[hspanR]`. Conclude with `hx`. Conclude with `Submodule.span_le_restrictScalars (v.adicCompletionIntegers K) (v.adicCompletion K) _ hx'`.

Set `c : Basis ι (v.adicCompletion K) E` to `Basis.mk hli hsp'`. Establish `hc : ∀ i, c i = (b i : E)` using `fun i => Basis.mk_apply hli hsp' i`. Establish `hrepr : ∀ (x : A) (i : ι), c.repr (x : E) i = algebraMap _ (v.adicCompletion K) (b.repr x i)`. Introduce `x i`. Establish `hx : (x : E) = ∑ j, algebraMap _ (v.adicCompletion K) (b.repr x j) • c j`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, hc, algebraMap_smul]`. Rewrite using `[hx, c.repr_sum_self]`. Establish `hmaps : ∀ x ∈ A, (g.toLinearMap.restrictScalars (v.adicCompletionIntegers K)) x ∈ A`. Introduce `x hx`.

Apply `hBA` to reduce the goal to its premises. Use `show g x ∈ (B : Set E)`. Rewrite using `[hB]`. Conclude with `⟨x, hx, rfl⟩`. Set `φ : A →ₗ[v.adicCompletionIntegers K] A` to `(g.toLinearMap.restrictScalars (v.adicCompletionIntegers K)).restrict hmaps`.

Establish `hφ : ∀ x : A, (φ x : E) = g x` using `fun x => rfl`. Establish `hdet : LinearMap.det (g : E →ₗ[v.adicCompletion K] E) = algebraMap _ (v.adicCompletion K) (LinearMap.det φ)`. Rewrite using `[← LinearMap.det_toMatrix c, ← LinearMap.det_toMatrix b, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Rewrite using `[LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, hc, LinearEquiv.coe_coe, ← hφ, hrepr]`. Establish `hinj : Function.Injective φ`. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `g.injective` to reduce the goal to its premises.

Rewrite using `[← hφ, ← hφ, h]`. Establish `hrank : finrank _ (LinearMap.range φ) = finrank _ A` using `LinearMap.finrank_range_of_inj hinj`. Use `set a := Submodule.smithNormalFormCoeffs b hrank`. Set `b'` to `Submodule.smithNormalFormTopBasis b hrank`. Set `ab` to `Submodule.smithNormalFormBotBasis b hrank`.

Establish `ha : ∀ i, a i ≠ 0` using `Submodule.smithNormalFormCoeffs_ne_zero b hrank`. Establish `hcomap : Submodule.comap A.subtype B = LinearMap.range φ`. Use extensionality with `x`. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `hx' : (x : E) ∈ (B : Set E)` using `hx`. Rewrite `hx'` using `[hB]`. Take `⟨y, hy, hxy⟩` from `hx'`. Conclude with `⟨⟨y, hy⟩, Subtype.ext hxy⟩`.

Introduce and unpack `⟨y, rfl⟩ show g y ∈ (B : Set E)`. Rewrite using `[hB]`. Conclude with `⟨y, y.2, rfl⟩`. Establish `hidx : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A ⧸ LinearMap.range φ)`. Rewrite using `[← hcomap, AddSubgroup.relIndex, AddSubgroup.index_eq_card]`.

Both sides reduce to the same expression. Establish `hq : Nat.card (A ⧸ LinearMap.range φ) = ∏ i, Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a i})`. Rewrite using `[Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range φ) b hrank).toEquiv, Nat.card_pi]`. Set `w : Basis ι _ A` to `ab.map (LinearEquiv.ofInjective φ hinj).symm`. Establish `hw : ∀ i, φ (w i) = a i • b' i`.

Introduce `i`. Establish `h1 : φ (w i) = ((LinearEquiv.ofInjective φ hinj) (w i) : A)` using `(LinearEquiv.ofInjective_apply _ _).symm`. Rewrite using `[h1]`. Simplify using `only [w, Basis.map_apply, LinearEquiv.apply_symm_apply]`. Conclude with `Submodule.smithNormalFormBotBasis_def b hrank i`.

Establish `hdetprod : LinearMap.det φ * b'.det w = ∏ i, a i`. Rewrite using `[← Basis.det_comp]`. Establish `: (⇑φ ∘ ⇑w) = fun i => a i • b' i` using `funext hw`. Rewrite using `[this, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]`. Take `⟨u, hu⟩` from `b'.isUnit_det w`.

Establish `hdetφ : LinearMap.det φ = (∏ i, a i) * ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)`. Rewrite using `[← hdetprod, ← hu, mul_assoc, Units.mul_inv, mul_one]`. Establish `hu1 : ‖algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)‖ = 1` using `LocalLatticeIndex.norm_unit v u⁻¹`. Rewrite using `[hidx, hq, Nat.cast_prod, hdet, hdetφ, map_mul, map_prod, norm_mul, norm_prod, hu1, mul_one, ← Finset.prod_inv_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => LocalLatticeIndex.card_quot_span v (ha i)`.
-/
theorem LocalLatticeIndex.index_eq_det (A B : Submodule (v.adicCompletionIntegers K) E)
    (g : E ≃ₗ[v.adicCompletion K] E) (hfg : A.FG)
    (hsp : Submodule.span (v.adicCompletion K) (A : Set E) = ⊤)
    (hB : (B : Set E) = g '' A) (hBA : B ≤ A) :
    (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ‖LinearMap.det (g : E →ₗ[v.adicCompletion K] E)‖⁻¹ := by
  classical
  have := LocalLatticeIndex.isTorsionFree A
  have : Module.Finite (v.adicCompletionIntegers K) A := Module.Finite.iff_fg.2 hfg
  set ι := Module.Free.ChooseBasisIndex (v.adicCompletionIntegers K) A
  let b := Module.Free.chooseBasis (v.adicCompletionIntegers K) A

  have hli : LinearIndependent (v.adicCompletion K) (fun i => (b i : E)) := by
    rw [← LinearIndependent.iff_fractionRing (v.adicCompletionIntegers K) (v.adicCompletion K)]
    exact b.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hspanR : Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => (b i : E)) = A := by
    have : (Set.range fun i => (b i : E)) = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hsp' : ⊤ ≤ Submodule.span (v.adicCompletion K) (Set.range fun i => (b i : E)) := by
    rw [← hsp]
    apply Submodule.span_le.2
    intro x hx
    have hx' : x ∈ Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => (b i : E)) := by
      rw [hspanR]; exact hx
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers K) (v.adicCompletion K) _ hx'
  let c : Basis ι (v.adicCompletion K) E := Basis.mk hli hsp'
  have hc : ∀ i, c i = (b i : E) := fun i => Basis.mk_apply hli hsp' i
  have hrepr : ∀ (x : A) (i : ι),
      c.repr (x : E) i = algebraMap _ (v.adicCompletion K) (b.repr x i) := by
    intro x i
    have hx : (x : E) = ∑ j, algebraMap _ (v.adicCompletion K) (b.repr x j) • c j := by
      calc (x : E) = ((∑ j, b.repr x j • b j : A) : E) := by rw [b.sum_repr]
        _ = ∑ j, algebraMap _ (v.adicCompletion K) (b.repr x j) • c j := by
          simp only [Submodule.coe_sum, Submodule.coe_smul, hc, algebraMap_smul]
    rw [hx, c.repr_sum_self]

  have hmaps : ∀ x ∈ A, (g.toLinearMap.restrictScalars (v.adicCompletionIntegers K)) x ∈ A := by
    intro x hx
    apply hBA
    show g x ∈ (B : Set E)
    rw [hB]
    exact ⟨x, hx, rfl⟩
  let φ : A →ₗ[v.adicCompletionIntegers K] A :=
    (g.toLinearMap.restrictScalars (v.adicCompletionIntegers K)).restrict hmaps
  have hφ : ∀ x : A, (φ x : E) = g x := fun x => rfl

  have hdet : LinearMap.det (g : E →ₗ[v.adicCompletion K] E) =
      algebraMap _ (v.adicCompletion K) (LinearMap.det φ) := by
    rw [← LinearMap.det_toMatrix c, ← LinearMap.det_toMatrix b, RingHom.map_det]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply, hc, LinearEquiv.coe_coe, ← hφ, hrepr]

  have hinj : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply g.injective
    rw [← hφ, ← hφ, h]
  have hrank : finrank _ (LinearMap.range φ) = finrank _ A := LinearMap.finrank_range_of_inj hinj
  set a := Submodule.smithNormalFormCoeffs b hrank
  let b' := Submodule.smithNormalFormTopBasis b hrank
  let ab := Submodule.smithNormalFormBotBasis b hrank
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank

  have hcomap : Submodule.comap A.subtype B = LinearMap.range φ := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    constructor
    · intro hx
      have hx' : (x : E) ∈ (B : Set E) := hx
      rw [hB] at hx'
      obtain ⟨y, hy, hxy⟩ := hx'
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      show g y ∈ (B : Set E)
      rw [hB]
      exact ⟨y, y.2, rfl⟩
  have hidx : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A ⧸ LinearMap.range φ) := by
    rw [← hcomap, AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    rfl
  have hq : Nat.card (A ⧸ LinearMap.range φ) =
      ∏ i, Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a i}) := by
    rw [Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range φ) b hrank).toEquiv,
      Nat.card_pi]

  let w : Basis ι _ A := ab.map (LinearEquiv.ofInjective φ hinj).symm
  have hw : ∀ i, φ (w i) = a i • b' i := by
    intro i
    have h1 : φ (w i) = ((LinearEquiv.ofInjective φ hinj) (w i) : A) :=
      (LinearEquiv.ofInjective_apply _ _).symm
    rw [h1]
    simp only [w, Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact Submodule.smithNormalFormBotBasis_def b hrank i
  have hdetprod : LinearMap.det φ * b'.det w = ∏ i, a i := by
    rw [← Basis.det_comp]
    have : (⇑φ ∘ ⇑w) = fun i => a i • b' i := funext hw
    rw [this, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  obtain ⟨u, hu⟩ := b'.isUnit_det w
  have hdetφ : LinearMap.det φ = (∏ i, a i) * ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K) := by
    rw [← hdetprod, ← hu, mul_assoc, Units.mul_inv, mul_one]
  have hu1 : ‖algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)‖ = 1 :=
    LocalLatticeIndex.norm_unit v u⁻¹
  rw [hidx, hq, Nat.cast_prod, hdet, hdetφ, map_mul, map_prod, norm_mul, norm_prod, hu1, mul_one,
    ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => LocalLatticeIndex.card_quot_span v (ha i)

end General

/- English proof (translation)
Introduce `K _ _ V _ _ _ _ v A B g hA hB hBA`. Conclude with `LocalLatticeIndex.index_eq_det A B g hA.1 hA.2 hB hBA`.
-/
theorem LocalLatticeIndex.proof : LocalLatticeIndex.Statement := by
  intro K _ _ V _ _ _ _ v A B g hA hB hBA
  exact LocalLatticeIndex.index_eq_det A B g hA.1 hA.2 hB hBA

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
