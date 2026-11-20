import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSpanBundleTrdegGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

/- English proof (translation)
Set `L : Matrix (Fin i) (Fin i) Ω → MvPolynomial (Fin i) Ω →ₐ[Ω] MvPolynomial (Fin i) Ω` to `fun B => aeval fun r => ∑ j, C (B r j) * X j`. Establish `hcomp : ∀ B B', (L B').comp (L B) = L (B * B')`. Introduce `B B'`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `only [L, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`. Establish `hid : L 1 = AlgHom.id Ω _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[L, Matrix.one_apply]`. Establish `heq : (aeval fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) = (aeval s).comp (L A)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[L, mul_comm]`.

Establish `hAinv : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)`. Establish `hinj : Function.Injective (L A)` using `Function.LeftInverse.injective (g := L A⁻¹) fun p => by`. Rewrite using `[← AlgHom.comp_apply, hcomp, hAinv, hid, AlgHom.id_apply]`. Rewrite using `[algebraicIndependent_iff_injective_aeval, heq]`. Conclude with `(algebraicIndependent_iff_injective_aeval.1 hs).comp hinj`.
-/
theorem SpanBundleTrdegGe.algebraicIndependent_linComb {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    {i : ℕ} (s : Fin i → Φ) (hs : AlgebraicIndependent Ω s) (A : Matrix (Fin i) (Fin i) Ω)
    (hA : IsUnit A) : AlgebraicIndependent Ω (fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) := by
  classical
  let L : Matrix (Fin i) (Fin i) Ω → MvPolynomial (Fin i) Ω →ₐ[Ω] MvPolynomial (Fin i) Ω :=
    fun B => aeval fun r => ∑ j, C (B r j) * X j
  have hcomp : ∀ B B', (L B').comp (L B) = L (B * B') := by
    intro B B'
    apply MvPolynomial.algHom_ext
    intro r
    simp only [L, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hid : L 1 = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, Matrix.one_apply]
  have heq : (aeval fun r => ∑ j, s j * algebraMap Ω Φ (A r j)) = (aeval s).comp (L A) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [L, mul_comm]
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have hinj : Function.Injective (L A) := Function.LeftInverse.injective (g := L A⁻¹) fun p => by
    rw [← AlgHom.comp_apply, hcomp, hAinv, hid, AlgHom.id_apply]
  rw [algebraicIndependent_iff_injective_aeval, heq]
  exact (algebraicIndependent_iff_injective_aeval.1 hs).comp hinj

/- English proof (translation)
Set `H : MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial (MvPolynomial (Fin i) Ω)` to `aeval fun r => Polynomial.C (X r) * Polynomial.X`. Establish `hH : Function.Injective H`. Establish `h1 : ((Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω).comp H = AlgHom.id Ω _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[H]`. Conclude with `Function.LeftInverse.injective (g := (Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω) fun p => by rw [← AlgHom.comp_apply, h1, AlgHom.id_apply]`. Establish `heq : (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) : MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) = (Polynomial.mapAlgHom (aeval σ)).comp H`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[H]`. Rewrite using `[heq]`. Conclude with `(Polynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.1 hσ)).comp hH`.
-/
theorem SpanBundleTrdegGe.injective_aeval_mul_X {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ] {i : ℕ}
    (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    Function.Injective (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) := by
  let H : MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial (MvPolynomial (Fin i) Ω) :=
    aeval fun r => Polynomial.C (X r) * Polynomial.X
  have hH : Function.Injective H := by
    have h1 : ((Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω).comp H =
        AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro r
      simp [H]
    exact Function.LeftInverse.injective (g := (Polynomial.aeval (1 : MvPolynomial (Fin i) Ω)).restrictScalars Ω)
      fun p => by rw [← AlgHom.comp_apply, h1, AlgHom.id_apply]
  have heq : (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ) = (Polynomial.mapAlgHom (aeval σ)).comp H := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [H]
  rw [heq]
  exact (Polynomial.map_injective _ (algebraicIndependent_iff_injective_aeval.1 hσ)).comp hH

/- English proof (translation)
Set `θ : MvPolynomial (Fin i) Ω →+* Polynomial Φ` to `(aeval (fun r => Polynomial.C (σ r) * Polynomial.X) : MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ).toRingHom`. Establish `hθ : Function.Injective θ` using `SpanBundleTrdegGe.injective_aeval_mul_X σ hσ`. Set `e` to `(optionEquivRight Φ K).symm`. Establish `heC : ∀ a : Φ, e (C (Polynomial.C a)) = C a` using `fun a => (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_C Φ K a).symm`. Establish `heX : ∀ k, e (X k) = X (some k)` using `fun k => (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_some Φ K k).symm`.

Establish `heN : e (C Polynomial.X) = X none` using `(AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_none Φ K).symm`. Use `⟨e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom), e.injective.comp ((map_injective θ hθ).comp (commAlgEquiv Ω (Fin i) K).injective), ?_, ?_⟩` and prove the remaining obligations. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`.

Establish `h1 : θ (C a) = Polynomial.C (algebraMap Ω Φ a)` using `by simp [θ]`. Simplify using `[h1, heC]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p k hp`. Rewrite using `[C_mul, map_mul, hp, map_mul, map_mul]`.

Establish `h2 : (e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom)) (C (X k)) = X (some k)`. Simplify using `[heX]`. Rewrite using `[h2, map_X, rename_X]`. Introduce `r`. Establish `h3 : θ (X r) = Polynomial.C (σ r) * Polynomial.X` using `by simp [θ]`.

Establish `h4 : e (C (Polynomial.C (σ r) * Polynomial.X)) = C (σ r) * X none`. Rewrite using `[C_mul, map_mul, heC, heN]`. Simplify using `[h3, heC, heN]`.
-/
theorem SpanBundleTrdegGe.exists_injective_cone {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
    (K : Type*) {i : ℕ} (σ : Fin i → Φ) (hσ : AlgebraicIndependent Ω σ) :
    ∃ Ψ : MvPolynomial (Fin i) (MvPolynomial K Ω) →+* MvPolynomial (Option K) Φ, Function.Injective Ψ ∧
      (∀ p, Ψ (C p) = rename some (map (algebraMap Ω Φ) p)) ∧ ∀ r, Ψ (X r) = C (σ r) * X none := by
  let θ : MvPolynomial (Fin i) Ω →+* Polynomial Φ :=
    (aeval (fun r => Polynomial.C (σ r) * Polynomial.X) :
      MvPolynomial (Fin i) Ω →ₐ[Ω] Polynomial Φ).toRingHom
  have hθ : Function.Injective θ := SpanBundleTrdegGe.injective_aeval_mul_X σ hσ
  let e := (optionEquivRight Φ K).symm
  have heC : ∀ a : Φ, e (C (Polynomial.C a)) = C a := fun a =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_C Φ K a).symm
  have heX : ∀ k, e (X k) = X (some k) := fun k =>
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_some Φ K k).symm
  have heN : e (C Polynomial.X) = X none :=
    (AlgEquiv.symm_apply_eq _).2 (optionEquivRight_X_none Φ K).symm
  refine ⟨e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom),
    e.injective.comp ((map_injective θ hθ).comp (commAlgEquiv Ω (Fin i) K).injective), ?_, ?_⟩
  · intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h1 : θ (C a) = Polynomial.C (algebraMap Ω Φ a) := by simp [θ]
      simp [h1, heC]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p k hp =>
      rw [C_mul, map_mul, hp, map_mul, map_mul]
      have h2 : (e.toRingEquiv.toRingHom.comp ((map θ).comp (commAlgEquiv Ω (Fin i) K).toRingEquiv.toRingHom))
          (C (X k)) = X (some k) := by
        simp [heX]
      rw [h2, map_X, rename_X]
  · intro r
    have h3 : θ (X r) = Polynomial.C (σ r) * Polynomial.X := by simp [θ]
    have h4 : e (C (Polynomial.C (σ r) * Polynomial.X)) = C (σ r) * X none := by
      rw [C_mul, map_mul, heC, heN]
    simp [h3, heC, heN]

/- English proof (translation)
Introduce `F _ Ω _ _ K ι y M i G hG Φ _ _ s hs`. Set `: Algebra F Φ` to `((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra`. Establish `: IsScalarTower F Ω Φ` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `set z := projCoord y (Pi.basisFun Ω (Fin i)) (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s with hz`. Express the relevant statement in the definitionally equal form `Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤ Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ pointIdeal F z)`.

Establish `hzn : ∀ m, z ⟨none, m⟩ = ∑ j, s j * algebraMap Ω Φ (G m j)`. Introduce `m`. Simplify using `[hz, projCoord, Matrix.col]`. Both sides reduce to the same expression. Establish `hzs : ∀ k (q : ι k), z ⟨some k, q⟩ = algebraMap Ω Φ (y ⟨k, q⟩)` using `fun _ _ => rfl`.

Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : Fin i → Fin M, IsUnit (Matrix.of fun r j => G (l r) j) := by`. Establish `hrk : (Matrix.of G).rank = i`. Rewrite using `[← Matrix.rank_transpose]`. Simplify using `using LinearIndependent.rank_matrix (M := Matrix.transpose (Matrix.of G)) hG`. Take `⟨κ, a, -, hsp, hli⟩` from `exists_linearIndependent' Ω (Matrix.of G).row`.

Establish `: Finite κ` using `hli.finite`. Set `: Fintype κ` to `Fintype.ofFinite κ`. Establish `hcard : Fintype.card κ = i`. Rewrite using `[← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrk]`. Set `e : Fin i ≃ κ` to `(Fintype.equivFinOfCardEq hcard).symm`.

Use `⟨a ∘ e, Matrix.linearIndependent_rows_iff_isUnit.1 ?_⟩` and prove the remaining obligations. Conclude with `hli.comp e e.injective`. Use `set σ : Fin i → Φ := fun r => ∑ j, s j * algebraMap Ω Φ (G (l r) j) with hσdef`. Establish `hσ : AlgebraicIndependent Ω σ` using `SpanBundleTrdegGe.algebraicIndependent_linComb s hs _ hl`. Establish `: (pointIdeal F y).IsPrime` using `RingHom.ker_isPrime _`.

Establish `: (pointIdeal F z).IsPrime` using `RingHom.ker_isPrime _`. Use `set Ay := MRing ι F ⧸ pointIdeal F y`. Use `set Az := MRing (bundleIdx ι M) F ⧸ pointIdeal F z`. Set `qy : Ay →ₐ[F] MvPolynomial K Ω` to `Ideal.kerLiftAlg (pointConeMap F y)`. Establish `hqy : Function.Injective qy` using `Ideal.kerLiftAlg_injective _`.

Set `qz : Az →ₐ[F] MvPolynomial (Option K) Φ` to `Ideal.kerLiftAlg (pointConeMap F z)`. Set `emb : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ` to `(rename (R := Φ) some).toRingHom.comp (map (algebraMap Ω Φ))`. Set `σ' : (Σ k, ι k) → (Σ o, bundleIdx ι M o)` to `fun p => ⟨some p.1, p.2⟩`. Establish `hE1 : ∀ g : MRing ι F, pointConeMap F z (rename σ' g) = emb (pointConeMap F y g)`. Introduce `g`.

Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [pointConeMap, emb, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p q hp`. Simplify using `only [map_mul, hp, rename_X]`.

Simplify using `[pointConeMap, emb, σ', hzs]`. Establish `hle : pointIdeal F y ≤ (pointIdeal F z).comap (rename σ' : MRing ι F →ₐ[F] _)`. Introduce `g hg`. Simplify using `only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker] at hg ⊢`. Rewrite using `[hE1, hg, map_zero]`.

Set `fy : Ay →ₐ[F] Az` to `Ideal.quotientMapₐ (pointIdeal F z) (rename σ') hle`. Set `Θ : MvPolynomial (Fin i) Ay →ₐ[F] Az` to `aevalTower fy fun r => Ideal.Quotient.mk _ (X ⟨none, l r⟩)`. Take `⟨Ψ, hΨ, hΨC, hΨX⟩` from `SpanBundleTrdegGe.exists_injective_cone K σ hσ`. Establish `key : ∀ a, qz (Θ a) = Ψ (map qy.toRingHom a)`. Introduce `a`.

Proceed by induction on `a using MvPolynomial.induction_on with`. Consider the case `C c`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Simplify using `only [Θ, aevalTower_C, map_C]`. Rewrite using `[hΨC]`.

Express the relevant statement in the definitionally equal form `qz (Ideal.Quotient.mk _ (rename σ' g)) = emb (qy (Ideal.Quotient.mk _ g))`. Simplify using `only [qz, qy]`. Conclude with `hE1 g`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p r hp`.

Simplify using `only [map_mul, hp, map_X, hΨX]`. Use `congr 1`. Simplify using `only [Θ, aevalTower_X]`. Use `(Ideal.kerLiftAlg_mk (pointConeMap F z) _).trans ?_` and prove the remaining obligations. Simplify using `only [pointConeMap, aeval_X]`.

Conclude with `congrArg (fun a => C a * X none) (hzn (l r))`. Establish `hΘ : Function.Injective Θ`. Introduce `a b hab`. Apply `map_injective qy.toRingHom hqy` to reduce the goal to its premises. Apply `hΨ` to reduce the goal to its premises.

Rewrite using `[← key, ← key, hab]`. Establish `: FaithfulSMul F Ay` using `(faithfulSMul_iff_algebraMap_injective F Ay).2 (algebraMap F Ay).injective`. Establish `: FaithfulSMul Ay (MvPolynomial (Fin i) Ay)` using `(faithfulSMul_iff_algebraMap_injective Ay _).2 (C_injective _ _)`. Establish `e1` using `trdeg_add_eq F Ay (A := MvPolynomial (Fin i) Ay)`. Rewrite `e1` using `[MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin]`.

Rewrite using `[e1]`. Conclude with `trdeg_le_of_injective Θ hΘ`.
-/
theorem SpanBundleTrdegGe.proof : SpanBundleTrdegGe.Statement := by
  intro F _ Ω _ _ K ι y M i G hG Φ _ _ s hs
  classical
  let : Algebra F Φ := ((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra
  have : IsScalarTower F Ω Φ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set z := projCoord y (Pi.basisFun Ω (Fin i))
    (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s with hz
  change Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
    Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ pointIdeal F z)
  have hzn : ∀ m, z ⟨none, m⟩ = ∑ j, s j * algebraMap Ω Φ (G m j) := by
    intro m
    simp [hz, projCoord, Matrix.col]
    rfl
  have hzs : ∀ k (q : ι k), z ⟨some k, q⟩ = algebraMap Ω Φ (y ⟨k, q⟩) := fun _ _ => rfl

  obtain ⟨l, hl⟩ : ∃ l : Fin i → Fin M, IsUnit (Matrix.of fun r j => G (l r) j) := by
    have hrk : (Matrix.of G).rank = i := by
      rw [← Matrix.rank_transpose]
      simpa using LinearIndependent.rank_matrix (M := Matrix.transpose (Matrix.of G)) hG
    obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' Ω (Matrix.of G).row
    have : Finite κ := hli.finite
    let : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = i := by
      rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrk]
    let e : Fin i ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨a ∘ e, Matrix.linearIndependent_rows_iff_isUnit.1 ?_⟩
    exact hli.comp e e.injective
  set σ : Fin i → Φ := fun r => ∑ j, s j * algebraMap Ω Φ (G (l r) j) with hσdef
  have hσ : AlgebraicIndependent Ω σ :=
    SpanBundleTrdegGe.algebraicIndependent_linComb s hs _ hl

  have : (pointIdeal F y).IsPrime := RingHom.ker_isPrime _
  have : (pointIdeal F z).IsPrime := RingHom.ker_isPrime _
  set Ay := MRing ι F ⧸ pointIdeal F y
  set Az := MRing (bundleIdx ι M) F ⧸ pointIdeal F z
  let qy : Ay →ₐ[F] MvPolynomial K Ω := Ideal.kerLiftAlg (pointConeMap F y)
  have hqy : Function.Injective qy := Ideal.kerLiftAlg_injective _
  let qz : Az →ₐ[F] MvPolynomial (Option K) Φ := Ideal.kerLiftAlg (pointConeMap F z)
  let emb : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (R := Φ) some).toRingHom.comp (map (algebraMap Ω Φ))
  let σ' : (Σ k, ι k) → (Σ o, bundleIdx ι M o) := fun p => ⟨some p.1, p.2⟩
  have hE1 : ∀ g : MRing ι F, pointConeMap F z (rename σ' g) = emb (pointConeMap F y g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [pointConeMap, emb, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      simp only [map_mul, hp, rename_X]
      simp [pointConeMap, emb, σ', hzs]
  have hle : pointIdeal F y ≤ (pointIdeal F z).comap (rename σ' : MRing ι F →ₐ[F] _) := by
    intro g hg
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker] at hg ⊢
    rw [hE1, hg, map_zero]
  let fy : Ay →ₐ[F] Az := Ideal.quotientMapₐ (pointIdeal F z) (rename σ') hle
  let Θ : MvPolynomial (Fin i) Ay →ₐ[F] Az :=
    aevalTower fy fun r => Ideal.Quotient.mk _ (X ⟨none, l r⟩)

  obtain ⟨Ψ, hΨ, hΨC, hΨX⟩ := SpanBundleTrdegGe.exists_injective_cone K σ hσ
  have key : ∀ a, qz (Θ a) = Ψ (map qy.toRingHom a) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [Θ, aevalTower_C, map_C]
      rw [hΨC]
      change qz (Ideal.Quotient.mk _ (rename σ' g)) = emb (qy (Ideal.Quotient.mk _ g))
      simp only [qz, qy]
      exact hE1 g
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p r hp =>
      simp only [map_mul, hp, map_X, hΨX]
      congr 1
      simp only [Θ, aevalTower_X]
      refine (Ideal.kerLiftAlg_mk (pointConeMap F z) _).trans ?_
      simp only [pointConeMap, aeval_X]
      exact congrArg (fun a => C a * X none) (hzn (l r))
  have hΘ : Function.Injective Θ := by
    intro a b hab
    apply map_injective qy.toRingHom hqy
    apply hΨ
    rw [← key, ← key, hab]

  have : FaithfulSMul F Ay :=
    (faithfulSMul_iff_algebraMap_injective F Ay).2 (algebraMap F Ay).injective
  have : FaithfulSMul Ay (MvPolynomial (Fin i) Ay) :=
    (faithfulSMul_iff_algebraMap_injective Ay _).2 (C_injective _ _)
  have e1 := trdeg_add_eq F Ay (A := MvPolynomial (Fin i) Ay)
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at e1
  rw [e1]
  exact trdeg_le_of_injective Θ hΘ

end

end GroundTheory.Heights₂.Heights.NumbersDVR
