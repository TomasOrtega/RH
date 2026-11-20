import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory
namespace DetIndexPadic

/- English proof (translation)
Establish `h1 : Ideal.span {x} = RingHom.ker (PadicInt.toZModPow (p` using `l) x.valuation) := by`. Rewrite using `[PadicInt.ker_toZModPow]`. Use `conv_lhs => rw [PadicInt.unitCoeff_spec hx]`. Conclude with `Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _`. Establish `h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {x}) = l ^ x.valuation`.

Rewrite using `[h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) x.valuation))).toEquiv, Nat.card_zmod]`. Rewrite using `[h2, PadicInt.norm_eq_zpow_neg_valuation hx]`. Use `push_cast`. Rewrite using `[Padic.norm_p_pow]`.
-/
theorem norm_card_quot_span (l : ℕ) [Fact l.Prime] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {x}) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span {x} = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow]
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _
  have h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {x}) = l ^ x.valuation := by
    rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) x.valuation))).toEquiv, Nat.card_zmod]
  rw [h2, PadicInt.norm_eq_zpow_neg_valuation hx]
  push_cast
  rw [Padic.norm_p_pow]

/- English proof (translation)
Use `set n := Nat.card (T ⧸ LinearMap.range φ)`. Establish `hk : ∀ x : T, ∃ y, φ y = ((n : ℤ_[l])) • x`. Introduce `x`. Establish `h0` using `card_nsmul_eq_zero' (G := T ⧸ LinearMap.range φ) (x := Submodule.Quotient.mk x)`. Rewrite `h0` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Take `⟨y, hy⟩` from `h0`. Conclude with `⟨y, by rw [hy, Nat.cast_smul_eq_nsmul]⟩`. Set `b` to `Module.Free.chooseBasis ℤ_[l] T`. Use `choose c hc' using fun i => hk (b i)`. Set `ψ : T →ₗ[ℤ_[l]] T` to `b.constr ℤ_[l] c`.

Establish `hcomp : φ ∘ₗ ψ = (n : ℤ_[l]) • LinearMap.id`. Use `b.ext fun i => ?_` and prove the remaining obligations. Simplify using `[ψ, hc']`. Establish `hd` using `congrArg LinearMap.det hcomp`. Rewrite `hd` using `[LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, _root_.mul_one]`.

Introduce `h0`. Rewrite `hd` using `[h0, zero_mul]`. Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.2 hc) hd.symm`.
-/
theorem det_ne_zero_of_finite_coker (l : ℕ) [Fact l.Prime] {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T)
    (hc : Nat.card (T ⧸ LinearMap.range φ) ≠ 0) : LinearMap.det φ ≠ 0 := by
  classical
  set n := Nat.card (T ⧸ LinearMap.range φ)
  have hk : ∀ x : T, ∃ y, φ y = ((n : ℤ_[l])) • x := by
    intro x
    have h0 := card_nsmul_eq_zero' (G := T ⧸ LinearMap.range φ)
      (x := Submodule.Quotient.mk x)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨y, hy⟩ := h0
    exact ⟨y, by rw [hy, Nat.cast_smul_eq_nsmul]⟩
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose c hc' using fun i => hk (b i)
  let ψ : T →ₗ[ℤ_[l]] T := b.constr ℤ_[l] c
  have hcomp : φ ∘ₗ ψ = (n : ℤ_[l]) • LinearMap.id := by
    refine b.ext fun i => ?_
    simp [ψ, hc']
  have hd := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, _root_.mul_one] at hd
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) hd.symm

/- English proof (translation)
Introduce `l _ T _ _ _ _ φ a hcard`. Establish `hl` using `(Fact.out : l.Prime)`. Establish `hdet : LinearMap.det φ ≠ 0` using `det_ne_zero_of_finite_coker l φ (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero)`. Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot]`.

Assume the negation of the conclusion as `h`. Conclude with `hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)`. Use `set N := LinearMap.range φ with hN`. Set `e : T ≃ₗ[ℤ_[l]] N` to `LinearEquiv.ofInjective φ hinj`. Set `b` to `Module.Free.chooseBasis ℤ_[l] T`.

Establish `h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] T` using `e.symm.finrank_eq`. Set `c` to `Submodule.smithNormalFormCoeffs b h`. Set `b'` to `Submodule.smithNormalFormTopBasis b h`. Set `cb` to `Submodule.smithNormalFormBotBasis b h`. Establish `cb_eq` using `Submodule.smithNormalFormBotBasis_def b h`.

Set `e' : T ≃ₗ[ℤ_[l]] N` to `b'.equiv cb (Equiv.refl _)`. Set `f : T →ₗ[ℤ_[l]] T` to `N.subtype ∘ₗ (e' : T →ₗ[ℤ_[l]] N)`. Establish `hc : ∀ i, f (b' i) = c i • b' i`. Introduce `i`. Establish `: f (b' i) = b'.equiv cb (Equiv.refl _) (b' i)` using `rfl`.

Rewrite using `[this, b'.equiv_apply, Equiv.refl_apply]`. Conclude with `cb_eq i`. Establish `hm : LinearMap.toMatrix b' b' f = Matrix.diagonal c`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, hc, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, _root_.mul_one]`.

Distinguish the cases in `hij : i = j`. Rewrite using `[hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]`. Establish `hass` using `LinearMap.associated_det_comp_equiv N.subtype e e'`. Establish `h0 : N.subtype ∘ₗ (e : T →ₗ[ℤ_[l]] N) = φ`.

Use extensionality with `x`. Both sides reduce to the same expression. Rewrite `hass` using `[h0]`. Establish `h1 : LinearMap.det f = ∏ i, c i`. Rewrite using `[← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]`.

Express the relevant statement in the definitionally equal form `Associated (LinearMap.det φ) (LinearMap.det f) at hass`. Rewrite `hass` using `[h1]`. Establish `hcq : Nat.card (T ⧸ N) = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span {c i})`. Rewrite using `[← Nat.card_pi]`. Conclude with `Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv`.

Establish `hne : ∏ i, c i ≠ 0` using `fun h0 => hdet (hass.eq_zero_iff.2 h0)`. Take `⟨u, hu⟩` from `hass`. Establish `h2 : ‖LinearMap.det φ‖ = ‖∏ i, c i‖`. Rewrite using `[← hu, norm_mul, PadicInt.norm_units, _root_.mul_one]`. Establish `h3 : ‖∏ i, c i‖ = ‖((Nat.card (T ⧸ N) : ℕ) : ℚ_[l])‖`.

Rewrite using `[hcq, Nat.cast_prod, norm_prod, norm_prod]`. Conclude with `Finset.prod_congr rfl fun i hi => (norm_card_quot_span l (Finset.prod_ne_zero_iff.1 hne i hi)).symm`. Rewrite using `[h2, h3, hcard]`. Use `push_cast`. Rewrite using `[Padic.norm_p_pow]`.
-/
theorem norm_det_eq_of_card_coker : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (φ : T →ₗ[ℤ_[l]] T) (a : ℕ),
    Nat.card (T ⧸ LinearMap.range φ) = l ^ a → ‖LinearMap.det φ‖ = (l : ℝ) ^ (-(a : ℤ)) := by
  intro l _ T _ _ _ _ φ a hcard
  classical
  have hl := (Fact.out : l.Prime)
  have hdet : LinearMap.det φ ≠ 0 := det_ne_zero_of_finite_coker l φ
    (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)
  set N := LinearMap.range φ with hN
  let e : T ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective φ hinj
  let b := Module.Free.chooseBasis ℤ_[l] T
  have h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] T := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let cb := Submodule.smithNormalFormBotBasis b h
  have cb_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : T ≃ₗ[ℤ_[l]] N := b'.equiv cb (Equiv.refl _)
  let f : T →ₗ[ℤ_[l]] T := N.subtype ∘ₗ (e' : T →ₗ[ℤ_[l]] N)
  have hc : ∀ i, f (b' i) = c i • b' i := by
    intro i
    have : f (b' i) = b'.equiv cb (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact cb_eq i
  have hm : LinearMap.toMatrix b' b' f = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hc, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, _root_.mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hass := LinearMap.associated_det_comp_equiv N.subtype e e'
  have h0 : N.subtype ∘ₗ (e : T →ₗ[ℤ_[l]] N) = φ := by
    ext x; rfl
  rw [h0] at hass
  have h1 : LinearMap.det f = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  change Associated (LinearMap.det φ) (LinearMap.det f) at hass
  rw [h1] at hass
  have hcq : Nat.card (T ⧸ N) = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span {c i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
  have hne : ∏ i, c i ≠ 0 := fun h0 => hdet (hass.eq_zero_iff.2 h0)
  obtain ⟨u, hu⟩ := hass
  have h2 : ‖LinearMap.det φ‖ = ‖∏ i, c i‖ := by
    rw [← hu, norm_mul, PadicInt.norm_units, _root_.mul_one]
  have h3 : ‖∏ i, c i‖ = ‖((Nat.card (T ⧸ N) : ℕ) : ℚ_[l])‖ := by
    rw [hcq, Nat.cast_prod, norm_prod, norm_prod]
    exact Finset.prod_congr rfl fun i hi =>
      (norm_card_quot_span l (Finset.prod_ne_zero_iff.1 hne i hi)).symm
  rw [h2, h3, hcard]
  push_cast
  rw [Padic.norm_p_pow]

end DetIndexPadic
end GlobalTheory
