import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.Normal

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module

variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]

/- English proof (translation)
Use `letI : Field (R ⧸ I) := Ideal.Quotient.field I`. Establish `hT : Module.IsTorsionBySet R W I` using `fun y z => hW z z.2 y`. Use `letI : Module (R ⧸ I) W := hT.module`. Establish `hmk : ∀ (z : R) (y : W), (Ideal.Quotient.mk I z) • y = z • y` using `fun z y => rfl`. Use `haveI : IsScalarTower k (R ⧸ I) W := ⟨fun c e y => by`.

Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective e`. Establish `: c • Ideal.Quotient.mk I z = Ideal.Quotient.mk I (c • z)` using `(map_smul (Ideal.Quotient.mkₐ k I) c z).symm`. Rewrite using `[this, hmk, hmk, smul_assoc]⟩`. Use `haveI : FiniteDimensional (R ⧸ I) W := Module.Finite.of_restrictScalars_finite k (R ⧸ I) W`. Set `toE : (W →ₗ[R] W) → (W →ₗ[R ⧸ I] W)` to `fun f => { toFun := f map_add' := f.map_add map_smul' := fun c y => by`.

Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Simplify using `only [RingHom.id_apply, hmk]`. Conclude with `f.map_smul z y }`. Establish `htoE : ∀ f y, toE f y = f y` using `fun f y => rfl`. Establish `hNE : IsNilpotent (toE N)`.

Take `⟨m, hm⟩` from `hN`. Use `⟨m, LinearMap.ext fun y => ?_⟩` and prove the remaining obligations. Establish `: ((toE N) ^ m) y = (N ^ m) y`. Rewrite using `[Module.End.pow_apply, Module.End.pow_apply]`. Both sides reduce to the same expression.

Rewrite using `[this, hm]`. Both sides reduce to the same expression. Take `⟨ι, _, l, s, B, hB, hl, hs, hv, hA⟩` from `exists_normal (toE N) hNE v`. Use `⟨ι, inferInstance, l, s, b.smulTower B, hl, hs, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z p j`.

Rewrite using `[Basis.smulTower_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Basis.smulTower_apply, smul_assoc]`.

Introduce `p a i`. Rewrite using `[Basis.smulTower_apply]`. Establish `h1 : N (b p • B ⟨a, i⟩) = b p • (toE N) (B ⟨a, i⟩)` using `(toE N).map_smul (b p) (B ⟨a, i⟩)`. Rewrite using `[h1, hB a i]`. Use `split_ifs with h`.

Rewrite using `[Basis.smulTower_apply]`. Rewrite using `[smul_zero]`. Rewrite using `[Finset.sum_comm] conv_lhs => rw [hv]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : s a < l a`.

Simplify using `only [h, dif_pos, Basis.smulTower_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc]`.

Simplify using `only [h, dif_neg, not_false_eq_true, Finset.sum_const_zero]`. Introduce `A hAN p a i hi`. Establish `hc : toE A ∘ₗ toE N = toE N ∘ₗ toE A`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Conclude with `LinearMap.congr_fun hAN y`.

Rewrite using `[Basis.smulTower_repr]`. Use `hA (toE A) hc a i hi` as an intermediate fact. Rewrite `this` using `[htoE]`. Rewrite using `[this, map_zero, Finsupp.zero_apply]`.
-/
theorem dex_block_frame (I : Ideal R) [I.IsMaximal] {L : Type} [Fintype L] (b : Basis L k (R ⧸ I))
    {W : Type} [AddCommGroup W] [Module R W] [Module k W] [IsScalarTower k R W] [FiniteDimensional k W]
    (hW : ∀ z ∈ I, ∀ y : W, z • y = 0) (N : W →ₗ[R] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (β : Basis (L × Σ a : ι, Fin (l a)) k W),
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧
      (∀ (z : R) (p : L) (j : Σ a : ι, Fin (l a)),
        z • β (p, j) = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • β (q, j)) ∧
      (∀ (p : L) (a : ι) (i : Fin (l a)), N (β (p, ⟨a, i⟩)) =
        if h : (i : ℕ) + 1 < l a then β (p, ⟨a, ⟨i + 1, h⟩⟩) else 0) ∧
      v = ∑ p, ∑ a, (if h : s a < l a then b.repr 1 p • β (p, ⟨a, ⟨s a, h⟩⟩) else 0) ∧
      ∀ A : W →ₗ[R] W, A ∘ₗ N = N ∘ₗ A → ∀ (p : L) (a : ι) (i : Fin (l a)), (i : ℕ) < s a →
        β.repr (A v) (p, ⟨a, i⟩) = 0 := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hT : Module.IsTorsionBySet R W I := fun y z => hW z z.2 y
  letI : Module (R ⧸ I) W := hT.module
  have hmk : ∀ (z : R) (y : W), (Ideal.Quotient.mk I z) • y = z • y := fun z y => rfl
  haveI : IsScalarTower k (R ⧸ I) W := ⟨fun c e y => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective e
    have : c • Ideal.Quotient.mk I z = Ideal.Quotient.mk I (c • z) := (map_smul (Ideal.Quotient.mkₐ k I) c z).symm
    rw [this, hmk, hmk, smul_assoc]⟩
  haveI : FiniteDimensional (R ⧸ I) W := Module.Finite.of_restrictScalars_finite k (R ⧸ I) W
  let toE : (W →ₗ[R] W) → (W →ₗ[R ⧸ I] W) := fun f =>
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c y => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
        simp only [RingHom.id_apply, hmk]
        exact f.map_smul z y }
  have htoE : ∀ f y, toE f y = f y := fun f y => rfl
  have hNE : IsNilpotent (toE N) := by
    obtain ⟨m, hm⟩ := hN
    refine ⟨m, LinearMap.ext fun y => ?_⟩
    have : ((toE N) ^ m) y = (N ^ m) y := by
      rw [Module.End.pow_apply, Module.End.pow_apply]
      rfl
    rw [this, hm]
    rfl
  obtain ⟨ι, _, l, s, B, hB, hl, hs, hv, hA⟩ := exists_normal (toE N) hNE v
  refine ⟨ι, inferInstance, l, s, b.smulTower B, hl, hs, ?_, ?_, ?_, ?_⟩
  · intro z p j
    rw [Basis.smulTower_apply]
    calc z • (b p • B j) = (Ideal.Quotient.mk I z) • (b p • B j) := rfl
      _ = (Ideal.Quotient.mk I z * b p) • B j := by rw [smul_smul]
      _ = (∑ q, b.repr (Ideal.Quotient.mk I z * b p) q • b q) • B j := by rw [b.sum_repr]
      _ = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • (b.smulTower B) (q, j) := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Basis.smulTower_apply, smul_assoc]
  · intro p a i
    rw [Basis.smulTower_apply]
    have h1 : N (b p • B ⟨a, i⟩) = b p • (toE N) (B ⟨a, i⟩) := (toE N).map_smul (b p) (B ⟨a, i⟩)
    rw [h1, hB a i]
    split_ifs with h
    · rw [Basis.smulTower_apply]
    · rw [smul_zero]
  · rw [Finset.sum_comm]
    conv_lhs => rw [hv]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : s a < l a
    · simp only [h, dif_pos, Basis.smulTower_apply]
      calc B ⟨a, ⟨s a, h⟩⟩ = (1 : R ⧸ I) • B ⟨a, ⟨s a, h⟩⟩ := (one_smul _ _).symm
        _ = (∑ p, b.repr 1 p • b p) • B ⟨a, ⟨s a, h⟩⟩ := by rw [b.sum_repr]
        _ = ∑ p, b.repr 1 p • (b p • B ⟨a, ⟨s a, h⟩⟩) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [smul_assoc]
    · simp only [h, dif_neg, not_false_eq_true, Finset.sum_const_zero]
  · intro A hAN p a i hi
    have hc : toE A ∘ₗ toE N = toE N ∘ₗ toE A := by
      refine LinearMap.ext fun y => ?_
      exact LinearMap.congr_fun hAN y
    rw [Basis.smulTower_repr]
    have := hA (toE A) hc a i hi
    rw [htoE] at this
    rw [this, map_zero, Finsupp.zero_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
