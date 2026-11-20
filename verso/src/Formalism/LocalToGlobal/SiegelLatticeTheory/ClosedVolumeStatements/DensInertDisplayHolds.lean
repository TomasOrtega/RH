import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.LemmaN
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.GramJoint
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ClassAct
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DiamondFree
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.MassRatio
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMDegEq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMDiscSq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMEulerEq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdRedOne
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FlagRelevScalar
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RootUnitModP
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitNormRoot
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensInert
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FlagGramNonneg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiaFixDim
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ColsDecomp_holds : Formalism.L2.SG.ColsDim.ColsDecomp := Formalism.L2.SG.ColsDim.columns_decomposition
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ColsDim_holds : Formalism.L2.SG.ColsDim.ColsDim := Formalism.L2.SG.ColsDim.columns_dimension
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SharpDim_holds : Formalism.L2.SG.ColsDim.SharpDim := Formalism.L2.SG.ColsDim.sharp_dimension
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SharpBij_holds : Formalism.L2.SG.ColsDim.SharpBij := Formalism.L2.SG.ColsDim.sharp_bijective
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ColsDimU_holds : Formalism.L2.SG.ColsDim.ColsDimU := Formalism.L2.SG.ColsDim.columns_dimension_unitary

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DensExactInert_holds : Formalism.L2.SG.DensExact.DensExactInert := density_exact_inert
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DensExactSplit_holds : Formalism.L2.SG.DensExact.DensExactSplit := bilinearDensityFormula
/- English proof (translation)
Supply the required witnesses or components.
-/
theorem DensExact_holds : Formalism.L2.SG.DensExact.DensExact := ⟨DensExactInert_holds, DensExactSplit_holds⟩
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DensInertDisplay_holds : Formalism.L2.SG.DensExact.DensInertDisplay :=
  Formalism.L2.SG.DensExact.densInertDisplay_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DensSplitDisplay_holds : Formalism.L2.SG.DensExact.DensSplitDisplay :=
  Formalism.L2.SG.DensExact.densSplitDisplay_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LemmaNa_holds : Formalism.L2.SG.LemmaN.LemmaNa := finite_order_reduction_one
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LemmaNb_holds : Formalism.L2.SG.LemmaN.LemmaNb := Formalism.L2.SG.LemmaN.lemmaNb_of_lemmaNa LemmaNa_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LemmaNc_holds : Formalism.L2.SG.LemmaN.LemmaNc := Formalism.L2.SG.LemmaN.lemmaNc
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LemmaNcGlob_holds : Formalism.L2.SG.LemmaN.LemmaNcGlob := Formalism.L2.SG.LemmaN.lemmaNcGlob

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelevScalar_holds (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Algebra K E] :
    Formalism.L2.SG.IdCell.RelevScalar E K := flagRelevScalar E K
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NormRoot_holds (E : Type) [Field E] [NumberField E] [StarRing E] :
    Formalism.L2.SG.IdCell.NormRoot E := unitNormRoot E
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rootModP₂ (E : Type) [Field E] [NumberField E] :
    Formalism.L2.SG.IdCell.RootModP E := root_of_unity_mod_p E
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IdCellFrame_holds (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Algebra K E] :
    Formalism.L2.SG.IdCell.IdCellFrame E K :=
  Formalism.L2.SG.IdCell.idCellFrame_of (RelevScalar_holds E K) (NormRoot_holds E) (rootModP₂ E)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GramBlocks_holds : Formalism.L2.SG.GramJoint.GramBlocks := Formalism.L2.SG.GramJoint.gramBlocks
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GramDetFlag_holds : Formalism.L2.SG.GramJoint.GramDetFlag := Formalism.L2.SG.GramJoint.gramDetFlag
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GramIndep_holds : Formalism.L2.SG.GramJoint.GramIndep := Formalism.L2.SG.GramJoint.gramIndep
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GmatScale_holds : Formalism.L2.SG.GramJoint.GmatScale := Formalism.L2.SG.GramJoint.gmatScale
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GtermGram_holds (D : D7) : Formalism.L2.SG.GramJoint.GtermGram D := Formalism.L2.SG.GramJoint.gtermGram D

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem GNonnegAt_holds : Formalism.L2.SG.GramJoint.GNonnegAt := by
  have h : PI.FlagGramNonneg := flag_gram_nonneg
  intro E _ _ _ S τ hτ hsig r T T' hr hT hT' F F'
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.HasSignature (S.gram.map τ) p (r + 1) := ⟨(S.sig τ).1, hr ▸ hsig τ⟩
  exact h E S.V S.hT S.herm S.nondeg S.rank S.frame τ hτ p r T T' hp hT hT' F.e F'.e F.z F'.z
    ⟨F.e_indep, F.e_iso, F.z_orth, F.z_norm⟩ ⟨F'.e_indep, F'.e_iso, F'.z_orth, F'.z_norm⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DNeZeroAt_holds : Formalism.L2.SG.GramJoint.DNeZeroAt := Formalism.L2.SG.GramJoint.dNeZeroAt_of GNonnegAt_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GtermJoint_holds (D : D7) : Formalism.L2.SG.GramJoint.GtermJoint D :=
  Formalism.L2.SG.GramJoint.gtermJoint_of GNonnegAt_holds D
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GtermNonneg_holds (D : D7) : Formalism.L2.SG.GramJoint.GtermNonneg D :=
  Formalism.L2.SG.GramJoint.gtermNonneg_of GNonnegAt_holds D

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FixedDim_holds : Formalism.L2.SG.ClassAct.FixedDim := diagonal_fixed_dimension

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DiaFree_holds {G : Type} [Group G] {Γ K K₀ D : Subgroup G} (hK : K ≤ K₀) (hD : D ≤ K₀)
    (hn : Formalism.UG.IsNeat Γ K₀) : Formalism.L2.SG.ClassAct.DiaFree Γ K D :=
  Formalism.L2.SG.ClassAct.diaFree_of_isNeat hK hD hn

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DiaFreeCols_holds {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks}
    (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    Formalism.L2.SG.DiamondFree.DiaFreeCols W Ch u :=
  Formalism.L2.SG.DiamondFree.diaFreeCols_holds W Ch hX hPr hbig u

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FixedDimCols_holds {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks}
    (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (P : ↥(Pr.vT u)) :
    Formalism.L2.SG.DiamondFree.FixedDimCols W Ch u P :=
  Formalism.L2.SG.DiamondFree.fixedDimCols_holds W Ch hX hPr hbig u P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem diamond_group_free {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks}
    (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (hX : X.Ok) (hPr : Pr.Ok) (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) :
    Formalism.L2.SG.DiamondFree.IsDiamondFreeWord W Ch u :=
  Formalism.L2.SG.DiamondFree.diamondFree_holds W Ch hX hPr hbig u

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegEq_holds : Formalism.L2.SG.MassRatio.DegEq := Formalism.L2.SG.MassRatio.cm_degree_eq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DiscSq_holds : Formalism.L2.SG.MassRatio.DiscSq := Formalism.L2.SG.MassRatio.cm_discriminant_square
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EulerEq_holds : Formalism.L2.SG.MassRatio.EulerEq := Formalism.L2.SG.MassRatio.mass_ratio_euler_eq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FormsEq_holds : Formalism.L2.SG.MassRatio.FormsEq :=
  Formalism.L2.SG.MassRatio.formsEq_of DegEq_holds DiscSq_holds EulerEq_holds
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MassRatio_holds : Formalism.L2.SG.MassRatio.MassRatio :=
  Formalism.L2.SG.MassRatio.massRatio_of_siegel FormsEq_holds Formalism.HermitianLattices.Ext.L3.siegelMassRatio

end Formalism.L2.SG.Closed
