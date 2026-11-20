import Mathlib

namespace GlobalTheory.NormDetIndex

open Module Submodule

/- English proof (translation)
Establish `h1 : Ideal.span ({x} : Set ℤ_[l]) = RingHom.ker (PadicInt.toZModPow (p` using `l) x.valuation) := by`. Rewrite using `[PadicInt.ker_toZModPow, Ideal.span_singleton_eq_span_singleton]`. Use `Associated.symm ⟨PadicInt.unitCoeff hx, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(PadicInt.unitCoeff_spec hx).symm`.

Establish `h2 : Function.Surjective (PadicInt.toZModPow (p` using `l) x.valuation) := ZMod.ringHom_surjective _`. Rewrite using `[h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective h2).toEquiv, Nat.card_zmod, PadicInt.norm_eq_zpow_neg_valuation hx, Nat.cast_pow, Padic.norm_p_pow]`.
-/
theorem norm_card_quotient_span (l : ℕ) [Fact (Nat.Prime l)] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span ({x} : Set ℤ_[l])) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span ({x} : Set ℤ_[l]) = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_singleton_eq_span_singleton]
    refine Associated.symm ⟨PadicInt.unitCoeff hx, ?_⟩
    rw [mul_comm]
    exact (PadicInt.unitCoeff_spec hx).symm
  have h2 : Function.Surjective (PadicInt.toZModPow (p := l) x.valuation) :=
    ZMod.ringHom_surjective _
  rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective h2).toEquiv, Nat.card_zmod,
    PadicInt.norm_eq_zpow_neg_valuation hx, Nat.cast_pow, Padic.norm_p_pow]

/- English proof (translation)
Take `⟨u, rfl⟩` from `h`. Rewrite using `[norm_mul, PadicInt.isUnit_iff.mp u.isUnit, mul_one]`.
-/
theorem norm_eq_of_associated (l : ℕ) [Fact (Nat.Prime l)] {x y : ℤ_[l]} (h : Associated x y) :
    ‖x‖ = ‖y‖ := by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul, PadicInt.isUnit_iff.mp u.isUnit, mul_one]

/- English proof (translation)
Use `set N := LinearMap.range M.mulVecLin with hN`. Establish `hinj : Function.Injective M.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hM hv`.

Set `e : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N` to `LinearEquiv.ofInjective _ hinj`. Set `b : Basis κ ℤ_[l] (κ → ℤ_[l])` to `Pi.basisFun _ _`. Establish `h : finrank ℤ_[l] N = finrank ℤ_[l] (κ → ℤ_[l])` using `e.symm.finrank_eq`. Set `a` to `smithNormalFormCoeffs b h`. Set `b'` to `smithNormalFormTopBasis b h`.

Set `ab` to `smithNormalFormBotBasis b h`. Set `e' : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N` to `b'.equiv ab (Equiv.refl _)`. Establish `h1 : M.det = LinearMap.det (N.subtype ∘ₗ (e : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N))`. Rewrite using `[← LinearMap.det_toLin' M]`. Both sides reduce to the same expression.

Establish `h2 : LinearMap.det (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) = ∏ i, a i`. Rewrite using `[← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]`. Use `congr 1`. Use extensionality with `i j`. Establish `ha : (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) (b' j) = a j • b' j`.

Express the relevant statement in the definitionally equal form `((b'.equiv ab (Equiv.refl _) (b' j) : N) : κ → ℤ_[l]) = _`. Rewrite using `[b'.equiv_apply, Equiv.refl_apply]`. Conclude with `smithNormalFormBotBasis_def b h j`. Rewrite using `[LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]`. Distinguish the cases in `hij : i = j`.

Rewrite using `[hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]`. Establish `h3 : N.toAddSubgroup.index = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span ({a i} : Set ℤ_[l]))`. Express the relevant statement in the definitionally equal form `Nat.card ((κ → ℤ_[l]) ⧸ N) = _`. Rewrite using `[Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]`.

Rewrite using `[h1, norm_eq_of_associated l (LinearMap.associated_det_comp_equiv N.subtype e e'), h2, h3, Nat.cast_prod, norm_prod, norm_prod]`. Conclude with `Finset.prod_congr rfl fun i _ => (norm_card_quotient_span l (smithNormalFormCoeffs_ne_zero b h i)).symm`.
-/
theorem norm_det_eq_norm_index (l : ℕ) [Fact (Nat.Prime l)] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℚ_[l])‖ := by
  set N := LinearMap.range M.mulVecLin with hN
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hM hv
  let e : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective _ hinj
  let b : Basis κ ℤ_[l] (κ → ℤ_[l]) := Pi.basisFun _ _
  have h : finrank ℤ_[l] N = finrank ℤ_[l] (κ → ℤ_[l]) := e.symm.finrank_eq
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  let e' : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := b'.equiv ab (Equiv.refl _)
  have h1 : M.det = LinearMap.det (N.subtype ∘ₗ (e : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) := by
    rw [← LinearMap.det_toLin' M]
    rfl
  have h2 : LinearMap.det (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    have ha : (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) (b' j) = a j • b' j := by
      change ((b'.equiv ab (Equiv.refl _) (b' j) : N) : κ → ℤ_[l]) = _
      rw [b'.equiv_apply, Equiv.refl_apply]
      exact smithNormalFormBotBasis_def b h j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have h3 : N.toAddSubgroup.index
      = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span ({a i} : Set ℤ_[l])) := by
    change Nat.card ((κ → ℤ_[l]) ⧸ N) = _
    rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  rw [h1, norm_eq_of_associated l (LinearMap.associated_det_comp_equiv N.subtype e e'), h2, h3,
    Nat.cast_prod, norm_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ =>
    (norm_card_quotient_span l (smithNormalFormCoeffs_ne_zero b h i)).symm

end GlobalTheory.NormDetIndex
