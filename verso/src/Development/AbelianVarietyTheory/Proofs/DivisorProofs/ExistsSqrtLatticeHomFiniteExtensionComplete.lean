import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteNormalExtSqrtFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootHom

/- English proof (translation)
Introduce `R _ _ _ X _ _ _ h m t hR hh`. Set `b` to `Module.Free.chooseBasis ℤ X`. Establish `hpq : ∀ k, ∃ p q : R, q ∈ nonZeroDivisors R ∧ algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q = (h (b k) : FractionRing R)` using `fun k => IsFractionRing.div_surjective R _`. Use `choose p q hq hpq using hpq`. Take `⟨R', _, _, _, ρ, r, hR', hinj, hfin, hloc, hr⟩` from `GlobalTheory.T.exists_finite_completeNormal_ext_sqrt_family R (Fin m ⊕ Module.Free.ChooseBasisIndex ℤ X) (Sum.elim t (fun k => p k * q k)) hR`.

Establish `hι : Function.Injective (algebraMap R' (FractionRing R'))` using `IsFractionRing.injective R' (FractionRing R')`. Establish `hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ)` using `hι.comp hinj`. Set `gam : FractionRing R →+* FractionRing R'` to `IsFractionRing.lift hinj'`. Establish `hgam : ∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)` using `fun x => IsFractionRing.lift_algebraMap hinj' x`. Establish `hq0 : ∀ k, algebraMap R' (FractionRing R') (ρ (q k)) ≠ 0`.

Introduce `k h0`. Establish `: ρ (q k) = 0` using `hι (by simpa using h0)`. Conclude with `nonZeroDivisors.ne_zero (hq k) (hinj (by simpa using this))`. Establish `hp0 : ∀ k, p k ≠ 0`. Introduce `k h0`.

Use `hpq k` as an intermediate fact. Rewrite `this` using `[h0, map_zero, zero_div]`. Conclude with `(h (b k)).ne_zero this.symm`. Establish `hs : ∀ k, (r (Sum.inr k)) ^ 2 = ρ (p k * q k)` using `fun k => by simpa using hr (Sum.inr k)`. Establish `hs0 : ∀ k, algebraMap R' (FractionRing R') (r (Sum.inr k)) ≠ 0`.

Introduce `k h0`. Establish `h1 : r (Sum.inr k) = 0` using `hι (by simpa using h0)`. Establish `h2` using `hs k`. Rewrite `h2` using `[h1, zero_pow two_ne_zero]`. Conclude with `mul_ne_zero (hp0 k) (nonZeroDivisors.ne_zero (hq k)) (hinj (by simpa using h2.symm))`.

Set `e : Module.Free.ChooseBasisIndex ℤ X → (FractionRing R')ˣ` to `fun k => Units.mk0 (algebraMap R' _ (r (Sum.inr k)) / algebraMap R' _ (ρ (q k))) (div_ne_zero (hs0 k) (hq0 k))`. Set `L : X →ₗ[ℤ] Additive (FractionRing R')ˣ` to `b.constr ℤ (fun k => Additive.ofMul (e k))`. Set `H : X →+ Additive (FractionRing R)ˣ` to `AddMonoidHom.mk' (fun a => Additive.ofMul (h a)) (fun a c => by`. Simplify using `[hh a c])`. Set `G : X →+ Additive (FractionRing R')ˣ` to `(MonoidHom.toAdditive (Units.map gam.toMonoidHom)).comp H`.

Establish `hLG : L + L = G.toIntLinearMap`. Use `b.ext fun k => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, L, Module.Basis.constr_basis, AddMonoidHom.coe_toIntLinearMap, G, H, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.mk'_apply, MonoidHom.toAdditive_apply_apply]`. Rewrite using `[← ofMul_mul]`. Use `congr 1`.

Use `ext`. Simplify using `only [Units.val_mul, e, Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, toMul_ofMul]`. Rewrite using `[← hpq k, map_div₀, hgam, hgam, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (hq0 k) (hq0 k)) (hq0 k)]`. Use `congrArg (algebraMap R' (FractionRing R')) (hs k)` as an intermediate fact. Rewrite `this` using `[map_pow, map_mul, map_mul]`.

Rewrite using `[← sq, this]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨R', inferInstance, inferInstance, inferInstance, ρ, gam, fun i => r (Sum.inl i), fun a => Additive.toMul (L a), hR', hinj, hfin, hloc, hgam, fun i => by simpa using hr (Sum.inl i), fun a c => by simp [map_add], fun a => ?_⟩` and prove the remaining obligations. Establish `h2 : Additive.toMul (L a + L a) = Units.map gam.toMonoidHom (h a)`. Rewrite using `[← LinearMap.add_apply, LinearMap.congr_fun hLG a]`.

Both sides reduce to the same expression. Rewrite using `[sq, ← toMul_add]`. Conclude with `h2`.
-/
theorem exists_sqrt_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  intro R _ _ _ X _ _ _ h m t hR hh
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hpq : ∀ k, ∃ p q : R, q ∈ nonZeroDivisors R ∧
      algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q = (h (b k) : FractionRing R) :=
    fun k => IsFractionRing.div_surjective R _
  choose p q hq hpq using hpq
  obtain ⟨R', _, _, _, ρ, r, hR', hinj, hfin, hloc, hr⟩ :=
    GlobalTheory.T.exists_finite_completeNormal_ext_sqrt_family R (Fin m ⊕ Module.Free.ChooseBasisIndex ℤ X) (Sum.elim t (fun k => p k * q k)) hR
  have hι : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' (FractionRing R')
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := hι.comp hinj
  let gam : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hgam : ∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x) := fun x => IsFractionRing.lift_algebraMap hinj' x
  have hq0 : ∀ k, algebraMap R' (FractionRing R') (ρ (q k)) ≠ 0 := by
    intro k h0
    have : ρ (q k) = 0 := hι (by simpa using h0)
    exact nonZeroDivisors.ne_zero (hq k) (hinj (by simpa using this))
  have hp0 : ∀ k, p k ≠ 0 := by
    intro k h0
    have := hpq k
    rw [h0, map_zero, zero_div] at this
    exact (h (b k)).ne_zero this.symm
  have hs : ∀ k, (r (Sum.inr k)) ^ 2 = ρ (p k * q k) := fun k => by simpa using hr (Sum.inr k)
  have hs0 : ∀ k, algebraMap R' (FractionRing R') (r (Sum.inr k)) ≠ 0 := by
    intro k h0
    have h1 : r (Sum.inr k) = 0 := hι (by simpa using h0)
    have h2 := hs k
    rw [h1, zero_pow two_ne_zero] at h2
    exact mul_ne_zero (hp0 k) (nonZeroDivisors.ne_zero (hq k)) (hinj (by simpa using h2.symm))
  let e : Module.Free.ChooseBasisIndex ℤ X → (FractionRing R')ˣ := fun k =>
    Units.mk0 (algebraMap R' _ (r (Sum.inr k)) / algebraMap R' _ (ρ (q k))) (div_ne_zero (hs0 k) (hq0 k))
  let L : X →ₗ[ℤ] Additive (FractionRing R')ˣ := b.constr ℤ (fun k => Additive.ofMul (e k))
  let H : X →+ Additive (FractionRing R)ˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (h a)) (fun a c => by
    simp [hh a c])
  let G : X →+ Additive (FractionRing R')ˣ := (MonoidHom.toAdditive (Units.map gam.toMonoidHom)).comp H
  have hLG : L + L = G.toIntLinearMap := by
    refine b.ext fun k => ?_
    simp only [LinearMap.add_apply, L, Module.Basis.constr_basis, AddMonoidHom.coe_toIntLinearMap, G, H,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.mk'_apply, MonoidHom.toAdditive_apply_apply]
    rw [← ofMul_mul]
    congr 1
    ext
    simp only [Units.val_mul, e, Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, toMul_ofMul]
    rw [← hpq k, map_div₀, hgam, hgam, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (hq0 k) (hq0 k)) (hq0 k)]
    have := congrArg (algebraMap R' (FractionRing R')) (hs k)
    rw [map_pow, map_mul, map_mul] at this
    rw [← sq, this]
    ring
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, gam, fun i => r (Sum.inl i), fun a => Additive.toMul (L a),
    hR', hinj, hfin, hloc, hgam, fun i => by simpa using hr (Sum.inl i), fun a c => by simp [map_add], fun a => ?_⟩
  have h2 : Additive.toMul (L a + L a) = Units.map gam.toMonoidHom (h a) := by
    rw [← LinearMap.add_apply, LinearMap.congr_fun hLG a]
    rfl
  rw [sq, ← toMul_add]
  exact h2

end GlobalTheory.RootHom
