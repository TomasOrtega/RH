import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section

/- English proof (translation)
Introduce `hPr F _ _ Y T _ p d t U r₀ hs hpY hpT hU hr`. Take `⟨N, i, hi, hit⟩` from `hpT`. Establish `hφ : (r₀ ≫ i) ≫ PSpace.str F N = U.ι ≫ p` using `by rw [Category.assoc, hit, hr]`. Take `⟨w, i₀, hw₀, hwU, hext⟩` from `GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace F Y p N U (r₀ ≫ i) hφ hU`. Take `⟨I, hI0, hIU, hC⟩` from `GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family Y N w i₀ U hw₀ hwU`.

Take `⟨Y', s, hY', hs', hp', -, hiso, hEC, -⟩` from `hPr F d Y p inferInstance hs hpY I hI0`. Establish `hUle : U ≤ I.support.compl` using `fun y hy => hIU y hy`. Establish `hisoU : IsIso (s ∣_ U)` using `ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le s hUle`. Establish `: Nonempty U` using `hU.to_subtype`. Set `c : U.toScheme ⟶ Y'` to `inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι`.

Establish `hc : c ≫ s = U.ι` using `by simp [c, morphismRestrict_ι]`. Establish `hcη : c (genericPoint U) = genericPoint Y'` using `genericPoint_eq_of_isOpenImmersion c`. Establish `hη : s (genericPoint Y') = genericPoint Y`. Rewrite using `[← hcη, ← Scheme.Hom.comp_apply, hc]`. Conclude with `genericPoint_eq_of_isOpenImmersion U.ι`.

Establish `hne : ((s ⁻¹ᵁ U : Y'.Opens) : Set Y').Nonempty` using `⟨genericPoint Y', show s (genericPoint Y') ∈ U from hη ▸ GlobalTheory.Cartier.gen_mem hU.some_mem⟩`. Establish `hdense : Dense ((s ⁻¹ᵁ U : Y'.Opens) : Set Y')` using `(s ⁻¹ᵁ U).isOpen.dense hne`. Set `M : Modif p U d` to `⟨Y', s, hs', hp', hisoU, hdense⟩`. Take `⟨g, hg1, hg2⟩` from `hext Y' s hη (hC Y' s hη hEC)`. Take `⟨r, hr'⟩` from `GlobalTheory.exists_lift_closedImmersion_of_dense i g _ hdense fun x hx => by`.

Use `⟨(s ∣_ U ≫ r₀) ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun f : (s ⁻¹ᵁ U).toScheme ⟶ PSpace F N => f ⟨x, hx⟩) hg2`. Conclude with `e.symm`. Use `⟨M, r, hY', ?_, ?_⟩` and prove the remaining obligations. Use `show r ≫ t = s ≫ p`.

Rewrite using `[← hit, ← Category.assoc, hr', hg1]`. Use `show (s ⁻¹ᵁ U).ι ≫ r = (s ∣_ U) ≫ r₀`. Rewrite using `[← cancel_mono i, Category.assoc, hr', hg2, Category.assoc]`.
-/
theorem GlobalTheory.CompHS.exists_modif_map_of_open : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (Y T : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) (t : T ⟶ Sp F) (U : Y.Opens) (r₀ : U.toScheme ⟶ T), SmoothOfRelativeDimension d p → IsProjOver p → IsProjOver t → (U : Set Y).Nonempty → r₀ ≫ t = U.ι ≫ p → ∃ (M : Modif p U d) (r : M.X ⟶ T), IsIntegral M.X ∧ r ≫ t = M.str ∧ M.opn.ι ≫ r = (M.σ ∣_ U) ≫ r₀ := by
  intro hPr F _ _ Y T _ p d t U r₀ hs hpY hpT hU hr
  obtain ⟨N, i, hi, hit⟩ := hpT
  have hφ : (r₀ ≫ i) ≫ PSpace.str F N = U.ι ≫ p := by rw [Category.assoc, hit, hr]
  obtain ⟨w, i₀, hw₀, hwU, hext⟩ := GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace F Y p N U (r₀ ≫ i) hφ hU
  obtain ⟨I, hI0, hIU, hC⟩ := GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family Y N w i₀ U hw₀ hwU
  obtain ⟨Y', s, hY', hs', hp', -, hiso, hEC, -⟩ := hPr F d Y p inferInstance hs hpY I hI0
  have hUle : U ≤ I.support.compl := fun y hy => hIU y hy
  have hisoU : IsIso (s ∣_ U) := ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le s hUle
  have : Nonempty U := hU.to_subtype
  let c : U.toScheme ⟶ Y' := inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι
  have hc : c ≫ s = U.ι := by simp [c, morphismRestrict_ι]
  have hcη : c (genericPoint U) = genericPoint Y' := genericPoint_eq_of_isOpenImmersion c
  have hη : s (genericPoint Y') = genericPoint Y := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have hne : ((s ⁻¹ᵁ U : Y'.Opens) : Set Y').Nonempty :=
    ⟨genericPoint Y', show s (genericPoint Y') ∈ U from hη ▸ GlobalTheory.Cartier.gen_mem hU.some_mem⟩
  have hdense : Dense ((s ⁻¹ᵁ U : Y'.Opens) : Set Y') := (s ⁻¹ᵁ U).isOpen.dense hne
  let M : Modif p U d := ⟨Y', s, hs', hp', hisoU, hdense⟩
  obtain ⟨g, hg1, hg2⟩ := hext Y' s hη (hC Y' s hη hEC)
  obtain ⟨r, hr'⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i g _ hdense fun x hx => by
    refine ⟨(s ∣_ U ≫ r₀) ⟨x, hx⟩, ?_⟩
    have e := congrArg (fun f : (s ⁻¹ᵁ U).toScheme ⟶ PSpace F N => f ⟨x, hx⟩) hg2
    exact e.symm
  refine ⟨M, r, hY', ?_, ?_⟩
  · show r ≫ t = s ≫ p
    rw [← hit, ← Category.assoc, hr', hg1]
  · show (s ⁻¹ᵁ U).ι ≫ r = (s ∣_ U) ≫ r₀
    rw [← cancel_mono i, Category.assoc, hr', hg2, Category.assoc]
