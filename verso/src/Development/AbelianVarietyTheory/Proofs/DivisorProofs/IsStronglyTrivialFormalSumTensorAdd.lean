import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

/- English proof (translation)
The claim follows from `Finset.prod_coe_sort d.support (fun v => g v (d v))`.
-/
theorem prod_support_eq {U : Type} [CommGroup U] {r : ℕ} (g : Vec r → ℤ → U) (d : Vec r →₀ ℤ) :
    ∏ v : d.support, g v.1 (d v.1) = d.prod g :=
  Finset.prod_coe_sort d.support (fun v => g v (d v))

/- English proof (translation)
Introduce `R _ _ D D' r W T c c' ⟨Ξ, hΞ, h1, h2⟩ ⟨Ξ', hΞ', h1', h2'⟩`. Establish `hform : FormEq (Sum.elim (fun v : c.support => (vecHom T v.1).left) (fun v : c'.support => (vecHom T v.1).left)) (Sum.elim (fun v : c.support => c v.1) (fun v : c'.support => c' v.1)) (fun v : (c + c').support => (vecHom T v.1).left) (fun v => (c + c') v.1)`. Introduce `U _ h`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`.

Rewrite using `[prod_support_eq (fun v n => h (vecHom T v).left ^ n) c, prod_support_eq (fun v n => h (vecHom T v).left ^ n) c', prod_support_eq (fun v n => h (vecHom T v).left ^ n) (c + c'), Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]`. Take `⟨Ξ'', hΞ'', hv⟩` from `exists_gen D.P.isLB hform _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hΞ hΞ')`. Use `⟨Ξ'', hΞ'', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩` and prove the remaining obligations. Rewrite using `[hv _ _ z J hJ, val_mul hJ, h1 z J hJ, h1' z J hJ, _root_.mul_one]`. Rewrite using `[hv _ _ z J hJ, val_mul hJ, h2 z J hJ y y', h2' z J hJ y y']`.

Conclude with `(Finsupp.prod_add_index' (f := c) (g := c') (h := fun v n => val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-n)) (fun _ => by simp only [neg_zero, zpow_zero]) (fun _ _ _ => by simp only [neg_add, zpow_add])).symm`.
-/
theorem triv_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c c' : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T c' →
    GlobalTheory.TensBal.Triv T (c + c') := by
  intro R _ _ D D' r W T c c' ⟨Ξ, hΞ, h1, h2⟩ ⟨Ξ', hΞ', h1', h2'⟩
  have hform : FormEq (Sum.elim (fun v : c.support => (vecHom T v.1).left) (fun v : c'.support => (vecHom T v.1).left))
      (Sum.elim (fun v : c.support => c v.1) (fun v : c'.support => c' v.1))
      (fun v : (c + c').support => (vecHom T v.1).left) (fun v => (c + c') v.1) := by
    intro U _ h
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_support_eq (fun v n => h (vecHom T v).left ^ n) c,
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) c',
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) (c + c'),
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  obtain ⟨Ξ'', hΞ'', hv⟩ := exists_gen D.P.isLB hform _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hΞ hΞ')
  refine ⟨Ξ'', hΞ'', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_mul hJ, h1 z J hJ, h1' z J hJ, _root_.mul_one]
  · rw [hv _ _ z J hJ, val_mul hJ, h2 z J hJ y y', h2' z J hJ y y']
    exact (Finsupp.prod_add_index' (f := c) (g := c')
      (h := fun v n => val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-n))
      (fun _ => by simp only [neg_zero, zpow_zero]) (fun _ _ _ => by simp only [neg_add, zpow_add])).symm

end GlobalTheory.TensBal
