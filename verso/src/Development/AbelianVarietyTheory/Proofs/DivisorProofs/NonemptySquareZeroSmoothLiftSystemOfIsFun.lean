import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

/- English proof (translation)
Use `set e := L.ρ (𝟙 T) with he`. Establish `idem : ∀ x, e (e x) = e x` using `fun x ↦ by`. Use `hL (𝟙 T) (𝟙 T) x` as an intermediate fact. Rewrite `this` using `[Category.comp_id]`. Conclude with `this.symm`.

Establish `hJ` using `LiftSys.map_sq hI (L.B T)`. Establish `memJ : ∀ x, x - e x ∈ I.map (algebraMap R (L.B T))` using `fun x ↦ by`. Rewrite using `[← L.ker]`. Rewrite using `[map_sub, L.nat, mp_id, sub_self]`. Establish `sq0 : ∀ u v, u ∈ I.map (algebraMap R (L.B T)) → v ∈ I.map (algebraMap R (L.B T)) → u * v = 0`.

Introduce `u v hu hv`. Establish `: u * v ∈ I.map (algebraMap R (L.B T)) ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hu hv`. Rewrite `this` using `[hJ]`.

Simplify using `using this`. Establish `fix : ∀ z ∈ I.map (algebraMap R (L.B T)), e z = z`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨i, -, rfl⟩` from `hx`. Conclude with `e.commutes i`. Consider the case `zero => exact map_zero e`. Consider the case `add x w _ _ hx hw => rw [map_add, hx, hw]`. Consider the case `smul b x hxm hx`.

Rewrite using `[smul_eq_mul, map_mul, hx]`. Use `sq0 _ _ (memJ b) hxm` as an intermediate fact. Rewrite `this` using `[sub_mul]`. Conclude with `(sub_eq_zero.1 this).symm`. Establish `h1` using `fix _ (memJ y)`.

Rewrite `h1` using `[map_sub, idem, sub_self]`. Conclude with `(sub_eq_zero.1 h1.symm).symm`.
-/
theorem rho_id_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀}
    {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀} (L : Pre I π F) (hL : L.IsFun) (T : C) (y : L.B T) :
    L.ρ (𝟙 T) y = y := by
  set e := L.ρ (𝟙 T) with he
  have idem : ∀ x, e (e x) = e x := fun x ↦ by
    have := hL (𝟙 T) (𝟙 T) x
    rw [Category.comp_id] at this
    exact this.symm
  have hJ := LiftSys.map_sq hI (L.B T)
  have memJ : ∀ x, x - e x ∈ I.map (algebraMap R (L.B T)) := fun x ↦ by
    rw [← L.ker]
    rw [map_sub, L.nat, mp_id, sub_self]
  have sq0 : ∀ u v, u ∈ I.map (algebraMap R (L.B T)) → v ∈ I.map (algebraMap R (L.B T)) → u * v = 0 := by
    intro u v hu hv
    have : u * v ∈ I.map (algebraMap R (L.B T)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hu hv
    rw [hJ] at this
    simpa using this
  have fix : ∀ z ∈ I.map (algebraMap R (L.B T)), e z = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, -, rfl⟩ := hx
      exact e.commutes i
    | zero => exact map_zero e
    | add x w _ _ hx hw => rw [map_add, hx, hw]
    | smul b x hxm hx =>
      rw [smul_eq_mul, map_mul, hx]
      have := sq0 _ _ (memJ b) hxm
      rw [sub_mul] at this
      exact (sub_eq_zero.1 this).symm
  have h1 := fix _ (memJ y)
  rw [map_sub, idem, sub_self] at h1
  exact (sub_eq_zero.1 h1.symm).symm

/- English proof (translation)
Introduce `R R₀ _ _ I hI π _ _ X₀ s₀ L hL`. Conclude with `⟨{ F := { obj := L.B map := fun a ↦ CommAlgCat.ofHom (L.ρ a) map_id := fun T ↦ CommAlgCat.hom_ext (AlgHom.ext fun y ↦ rho_id_eq hI L hL T y) map_comp := fun a b ↦ CommAlgCat.hom_ext (AlgHom.ext fun x ↦ hL a b x) } p := L.p semi := L.semi nat := fun a b ↦ L.nat a b surj := L.surj …`.
-/
theorem nonempty_sys_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ L hL
  exact ⟨{
    F := {
      obj := L.B
      map := fun a ↦ CommAlgCat.ofHom (L.ρ a)
      map_id := fun T ↦ CommAlgCat.hom_ext (AlgHom.ext fun y ↦ rho_id_eq hI L hL T y)
      map_comp := fun a b ↦ CommAlgCat.hom_ext (AlgHom.ext fun x ↦ hL a b x) }
    p := L.p
    semi := L.semi
    nat := fun a b ↦ L.nat a b
    surj := L.surj
    ker := L.ker
    smooth := L.smooth }⟩

end GlobalTheory.Obs
