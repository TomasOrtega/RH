import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem spaceP_le_filTop {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) :
    spaceP X s ≤ filTop X.str (X.adj X.T) X.U (X.ideal s) (X.T - X.D) := by
  unfold spaceP
  refine iSup_le fun α => ?_
  rintro _ ⟨m, -, rfl⟩
  exact vanishesTo_mulMono _ _ _ α _ m

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem fil_spaceV_eq_spaceP (hF : FilMono) (K : Type) [Field K] [NumberField K] (X : Data K)
    (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (hn : IsNef K X.LA) (hb : IsBig K X.LA) :
    Fil (X.ideal s) (X.T - X.D) (spaceV X s) = spaceP X s := by
  apply le_antisymm
  · rintro f ⟨hfV, hfv⟩
    obtain ⟨g, hg, p, hp, rfl⟩ := Submodule.mem_sup.1 hfV
    have hpv : VanishesTo (X.ideal s) (X.T - X.D) p := spaceP_le_filTop X s hp
    have hgv : VanishesTo (X.ideal s) (X.T - X.D) g := by
      have : g = (g + p) - p := by abel
      rw [this]
      exact (filTop X.str (X.adj X.T) X.U (X.ideal s) (X.T - X.D)).sub_mem hfv hpv
    obtain ⟨m, hm, hgm⟩ := hF K X.toGeo hn hb s hs (X.T - X.D) X.D X.T (add_sub_D X) (Nat.le_refl _) g ⟨hg, hgv⟩
    refine (spaceP X s).add_mem ?_ hp
    rw [hgm]
    refine Submodule.sum_mem _ fun α _ => ?_
    unfold spaceP
    exact Submodule.mem_iSup_of_mem α ⟨m α, X.global_le X.D (by have := X.le_T; omega) (hm α), rfl⟩
  · intro f hf
    exact ⟨Submodule.mem_sup_right hf, spaceP_le_filTop X s hf⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem filP : FilMono → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K),
    X.IsGood s → IsNef K X.LA → IsBig K X.LA → Fil (X.ideal s) (X.T - X.D) (spaceV X s) = spaceP X s :=
  fun hF K _ _ X s hs hn hb => fil_spaceV_eq_spaceP hF K X s hs hn hb

end GlobalTheory.HSCore
