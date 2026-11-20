import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStableLatticeModIrreducibleEqBot

noncomputable section

namespace GlobalTheory.TopSteps.FinSummandDim

open Module TensorProduct
open GlobalTheory.AdmLoc GlobalTheory.TopSteps GlobalTheory.TopSteps.FinSummand Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace Qp] [TopologicalSpace LL]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) : H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ = ⊥ := by
  obtain ⟨_, _, _⟩ := hO.1
  refine invariants_stableLattice_mod_irreducible_eq_bot (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hlam ?_
  change (coefRep (latRep (twLattice Γ.T₀.L Γ.χ₁⁻¹)) (O ⧸ Ideal.span {Γ.lam})).invariants = ⊥
  rw [latRep_twLattice]
  exact h0

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) :
    finrank LL ↥(H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) = 0 := by
  rw [h0V_tw hO Γ hχ hlam h0, finrank_bot]

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isCompl_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hfin : Module.Finite O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ)) :
    ∃ C : Submodule O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) C := by
  obtain ⟨_, _, _⟩ := hO.1
  exact exists_isCompl_of_saturated _ (h1fT_saturated PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L)

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem finrank_tw [CompactSpace G] (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hT : IsOpen (Γ.T₀.L.T : Set Γ.T₀.V)) :
    finrank O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) = finrank LL (FiniteCohomology PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) := by
  obtain ⟨_, _, _⟩ := hO.1
  exact finrank_h1fT PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hT

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem cont_inv (hC : S.CrysCalc) : Continuous fun g => algebraMap S.O ↥S.LL.1 (S.Γ.χ₁⁻¹ g) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2.1

abbrev tw (hC : S.CrysCalc) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O := twLat S.Γ.T₀ S.Γ.χ₁⁻¹ (cont_inv S hC)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem tw_crysWith (hC : S.CrysCalc) :
    CrysWith (P.PD S.K) S.emb (tw S hC).ρ (fun i => (S.D.U i).map (· + -S.D.w i)) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  have h1 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁⁻¹ _ hρ h1).1

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem tw_h0V (hC : S.CrysCalc) (hV : S.Vanish) : H0V (tw S hC).ρ = ⊥ := by
  obtain ⟨⟨-, -, -, -, -, hlam⟩, -⟩ := S.hyp
  exact h0V_tw (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hlam hV.1

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem tw_finrank_h0V (hC : S.CrysCalc) (hV : S.Vanish) : finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) = 0 := by
  obtain ⟨⟨-, -, -, -, -, hlam⟩, -⟩ := S.hyp
  exact finrank_h0V_tw (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hlam hV.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_isCompl (hC : S.CrysCalc) (hH : S.FreeH) :
    ∃ C : Submodule S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) C :=
  isCompl_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hH.1.2.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank_hf (hC : S.CrysCalc) :
    finrank S.O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) = finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) :=
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  finrank_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC)
    (GlobalTheory.Cyc.locLat_isOpen (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ.T₀)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_card_neg :
    ∑ i, Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) = S.D.dsum := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.filter_map, Multiset.card_map, TopData.d]
  exact congrArg _ (Multiset.filter_congr fun u _ => by simp)

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem bijective_maxUnramifiedSubfield_algebraMap : Function.Bijective (algebraMap ↥(K0 S.K) ↥S.K.1) := by
  obtain ⟨⟨-, hA, -⟩, -⟩ := S.hyp
  exact ⟨RingHom.injective _, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem fSummand_of_finrank (hC : S.CrysCalc) (hH : S.FreeH)
    (hd : finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) = S.D.dsum) : S.FSummand :=
  ⟨exists_isCompl S hC hH, (finrank_hf S hC).trans hd⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem fSummand_of_dim (hC : S.CrysCalc) (hV : S.Vanish) (hH : S.FreeH)
    (hd : (finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) : ℤ) = (finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) : ℤ) +
      ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ)) : S.FSummand := by
  refine fSummand_of_finrank S hC hH ?_
  have h0 := tw_finrank_h0V S hC hV
  have h1 : ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ) = (S.D.dsum : ℤ) := by
    rw [← sum_card_neg S, Nat.cast_sum]
  have key : ∀ (a b c : ℕ) (s : ℤ), (a : ℤ) = (b : ℤ) + s → b = 0 → s = (c : ℤ) → a = c := by
    intro a b c s h h' h''
    omega
  exact key _ _ _ _ hd h0 h1

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem fSummand_of_codim (hC : S.CrysCalc) (hV : S.Vanish) (hH : S.FreeH)
    (hD : Module.Finite ↥S.LL.1 ↥(DdR (P.PD S.K) (tw S hC).ρ))
    (hd : (finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) : ℤ) = (finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) : ℤ) +
      ((finrank ↥S.LL.1 ↥(DdR (P.PD S.K) (tw S hC).ρ) : ℤ) -
        finrank ↥S.LL.1 ↥(DdR (P.PD S.K) (tw S hC).ρ ⊓
          FilV (P.PD S.K) (LL := ↥S.LL.1) (V := (tw S hC).V) 0))) : S.FSummand := by
  obtain ⟨⟨-, -, hn, hemb, -⟩, -⟩ := S.hyp
  exact fSummand_of_dim S hC hV hH (hd.trans (congrArg _
    (codim_fil_zero (P.PD S.K) S.emb hemb (bijective_maxUnramifiedSubfield_algebraMap S) hn _ (tw_crysWith S hC).2)))

end GlobalTheory.TopSteps.FinSummandDim
