import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem preimage_spMap_comp_eq_top {Y : Scheme.{0}} {V : Y.Opens} {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') {u : Sp S ⟶ Y} (h : u ⁻¹ᵁ V = ⊤) : (spMap g ≫ u) ⁻¹ᵁ V = ⊤ := by
  rw [Scheme.Hom.comp_preimage, h, Scheme.Hom.preimage_top]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem chartHom_spMap_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (u : Sp S ⟶ Y) (h : u ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ u) ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V (spMap g ≫ u) h' x = g (chartHom V u h x) := by
  have e1 : ((spMap g ≫ u).appLE V ⊤ h'.ge).hom x = (spMap g).appTop.hom ((u.appLE V ⊤ h.ge).hom x) := by
    have e : (spMap g).appTop = (spMap g).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [e]
    exact (congrArg (fun q => q.hom x) (Scheme.Hom.appLE_comp_appLE (spMap g) u V ⊤ ⊤ h.ge le_top)).symm
  have e2 := congrArg (fun q => q.hom ((u.appLE V ⊤ h.ge).hom x))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g))
  simp only [chartHom, RingHom.comp_apply]
  rw [e1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e2
  exact e2

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem isCombIn_spMap_comp (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S']
    (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) (hC : IsCombIn V u c w a) :
    IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  obtain ⟨hu, hc, hw, hx⟩ := hC
  refine ⟨preimage_spMap_comp_eq_top g hu, preimage_spMap_comp_eq_top g hc,
    fun i => preimage_spMap_comp_eq_top g (hw i), fun x => ?_⟩
  rw [chartHom_spMap_comp V g c hc, chartHom_spMap_comp V g u hu, hx x, map_add, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [chartHom_spMap_comp V g (w i) (hw i), map_mul, map_sub]

end GlobalTheory.SecGlue
