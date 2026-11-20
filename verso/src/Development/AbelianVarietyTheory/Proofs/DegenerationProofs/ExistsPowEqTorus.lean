import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftOfRetraction

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorsLift

/- English proof (translation)
Use `choose r hr using h`. Set `b` to `Module.Free.chooseBasis ℤ X`. Set `g : X →ₗ[ℤ] Additive M` to `b.constr ℤ fun i => Additive.ofMul (r (f (Multiplicative.ofAdd (b i))))`. Establish `hg : n • g = (MonoidHom.toAdditiveRight f).toIntLinearMap`. Use `b.ext fun i => ?_` and prove the remaining obligations.

Simplify using `only [g, LinearMap.smul_apply, Module.Basis.constr_basis]`. Rewrite using `[← ofMul_pow, hr]`. Both sides reduce to the same expression. Use `⟨AddMonoidHom.toMultiplicativeLeft g.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Additive.toMul (LinearMap.congr_fun hg x.toAdd)`.
-/
theorem exists_pow_eq_hom {X M : Type} [AddCommGroup X] [Module.Free ℤ X] [CommGroup M] (n : ℕ)
    (h : ∀ m : M, ∃ r : M, r ^ n = m) (f : Multiplicative X →* M) :
    ∃ g : Multiplicative X →* M, g ^ n = f := by
  choose r hr using h
  let b := Module.Free.chooseBasis ℤ X
  let g : X →ₗ[ℤ] Additive M :=
    b.constr ℤ fun i => Additive.ofMul (r (f (Multiplicative.ofAdd (b i))))
  have hg : n • g = (MonoidHom.toAdditiveRight f).toIntLinearMap := by
    refine b.ext fun i => ?_
    simp only [g, LinearMap.smul_apply, Module.Basis.constr_basis]
    rw [← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft g.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hg x.toAdd)

/- English proof (translation)
Set `e : Γ(Sp k, ⊤) ≃+* k` to `(Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (e m.val) (n := n) hn`. Establish `h1 : (e.symm z) ^ n = m.val`. Rewrite using `[← map_pow, hz, RingEquiv.symm_apply_apply]`. Establish `hu : IsUnit (e.symm z)` using `(isUnit_pow_iff (by omega : n ≠ 0)).1 (h1 ▸ m.isUnit)`.

Conclude with `⟨hu.unit, Units.ext (by simpa using h1)⟩`.
-/
theorem exists_pow_eq_unit (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 1 ≤ n)
    (m : Γ(Sp k, ⊤)ˣ) : ∃ r : Γ(Sp k, ⊤)ˣ, r ^ n = m := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e m.val) (n := n) hn
  have h1 : (e.symm z) ^ n = m.val := by
    rw [← map_pow, hz, RingEquiv.symm_apply_apply]
  have hu : IsUnit (e.symm z) := (isUnit_pow_iff (by omega : n ≠ 0)).1 (h1 ▸ m.isUnit)
  exact ⟨hu.unit, Units.ext (by simpa using h1)⟩

/- English proof (translation)
Set `e` to `splitTorusPointsEquiv (Sp k) X (Out.baseOver (Sp k))`. Take `⟨g, hg⟩` from `exists_pow_eq_hom n (exists_pow_eq_unit k n hn) (e t)`. Use `⟨e.symm g, e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, e.apply_symm_apply]`. Conclude with `hg`.
-/
theorem exists_pow_eq_torus (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] (n : ℕ) (hn : 1 ≤ n) (t : Out.baseOver (Sp k) ⟶ splitTorus (Sp k) X) :
    ∃ s : Out.baseOver (Sp k) ⟶ splitTorus (Sp k) X, s ^ n = t := by
  let e := splitTorusPointsEquiv (Sp k) X (Out.baseOver (Sp k))
  obtain ⟨g, hg⟩ := exists_pow_eq_hom n (exists_pow_eq_unit k n hn) (e t)
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_pow, e.apply_symm_apply]
  exact hg

/- English proof (translation)
Introduce `k _ _ E G _ _ D n hn`. Use `D.q_hom` as an intermediate fact. Use `D.i_hom` as an intermediate fact. Establish `h1 : ∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b` using `RatLift.exists_point_over k E G D`. Establish `h3 : ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 → ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x`.

Introduce `x hx`. Take `⟨s, hs⟩` from `exists_pow_eq_torus k E.X n hn (D.isKernel.lift x (toUnit _) hx)`. Use `⟨s ≫ D.i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, D.isKernel.w, ← Category.assoc, comp_toUnit]`. Both sides reduce to the same expression.

Rewrite using `[← MonObj.pow_comp, hs, D.isKernel.lift_fst]`. Use `⟨h1, fun b hb => ?_, h3⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `h1 b`. Take `⟨y, hy, hyx⟩` from `h3 (x ^ n) (by rw [MonObj.pow_comp, hx, hb])`. Use `⟨x * y⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_pow, inv_pow, hyx, mul_inv_cancel]`. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, hx, hy, inv_one, _root_.mul_one]`.
-/
theorem points_lift :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G) (n : ℕ), 1 ≤ n → (∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b) ∧ (∀ b : Out.baseOver (Sp k) ⟶ E.B, b ^ n = 1 → ∃ x : Out.baseOver (Sp k) ⟶ G, x ^ n = 1 ∧ x ≫ D.q = b) ∧ ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 → ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x := by
  intro k _ _ E G _ _ D n hn
  have := D.q_hom
  have := D.i_hom
  have h1 : ∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b :=
    RatLift.exists_point_over k E G D
  have h3 : ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 →
      ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_pow_eq_torus k E.X n hn (D.isKernel.lift x (toUnit _) hx)
    refine ⟨s ≫ D.i, ?_, ?_⟩
    · rw [Category.assoc, D.isKernel.w, ← Category.assoc, comp_toUnit]
      rfl
    · rw [← MonObj.pow_comp, hs, D.isKernel.lift_fst]
  refine ⟨h1, fun b hb => ?_, h3⟩
  obtain ⟨x, hx⟩ := h1 b
  obtain ⟨y, hy, hyx⟩ := h3 (x ^ n) (by rw [MonObj.pow_comp, hx, hb])
  refine ⟨x * y⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hyx, mul_inv_cancel]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, hx, hy, inv_one, _root_.mul_one]

end GlobalTheory.TorsLift
