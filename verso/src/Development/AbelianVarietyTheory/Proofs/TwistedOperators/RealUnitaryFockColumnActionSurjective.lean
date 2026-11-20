import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped Matrix

namespace GlobalTheory.RealColAct

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem compAt_eq_infMat {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = infMat D.sp.cm.sig V.gram (θ τ) h := rfl

/- English proof (translation)
Introduce `u`. Establish `hex : ∀ τ, ∃ h : GA D V, IsAtTau θ V τ ((u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) h` using `fun τ => by`. Use `(GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ ?_).exists` and prove the remaining obligations. Establish `hu` using `transpose_mem_unitary (u τ).2`. Rewrite `hu` using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`.

Use `show _ * _ * _ = _`. Rewrite using `[gramAt_of_gram_one hV, Matrix.mul_one, hu]`. Use `choose hτ hhτ using hex`. Establish `key : ∀ (L : List D.what₂.Tau), L.Nodup → ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt V (L.map hτ).prod) = if ρ ∈ L then ((u ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) else 1`. Introduce `L`.

Proceed by induction on `L with`. Consider the case `nil => intro _ ρ`. Simplify using `only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]`. Conclude with `GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ ρ V`. Consider the case `cons a L ih`.

Introduce `hL ρ`. Rewrite `hL` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, ih hL.2 ρ, compAt_eq_infMat]`. Distinguish the cases in `c : ρ = a`. Substitute `c` using the available equality.

Rewrite using `[(hhτ ρ).2.1, if_neg hL.1, if_pos List.mem_cons_self, Matrix.mul_one]`. Rewrite using `[(hhτ a).2.2 ρ c, Matrix.one_mul]`. Distinguish the cases in `d : ρ ∈ L`. Rewrite using `[if_pos d, if_pos (List.mem_cons_of_mem a d)]`. Rewrite using `[if_neg d, if_neg (by simp [c, d])]`.

Set `L` to `(Finset.univ : Finset D.what₂.Tau).toList`. Establish `hmem : (L.map hτ).prod ∈ GinfC V`. Apply `Subgroup.list_prod_mem` to reduce the goal to its premises. Introduce `x hx`. Take `⟨τ, -, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `(hhτ τ).1`. Use `⟨(⟨(L.map hτ).prod, hmem⟩ : GinfC V)⁻¹, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ρ`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[realCol_apply]`.

Simplify using `only [InvMemClass.coe_inv, inv_inv]`. Rewrite using `[key L (Finset.nodup_toList _) ρ, if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ)), Matrix.transpose_transpose]`.
-/
theorem realCol_surjective {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  classical
  intro u
  have hex : ∀ τ, ∃ h : GA D V, IsAtTau θ V τ ((u τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) h := fun τ => by
    refine (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ ?_).exists
    have hu := transpose_mem_unitary (u τ).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    show _ * _ * _ = _
    rw [gramAt_of_gram_one hV, Matrix.mul_one, hu]
  choose hτ hhτ using hex
  have key : ∀ (L : List D.what₂.Tau), L.Nodup → ∀ ρ,
      compAt θ ρ (Formalism.L2.Theta.mt V (L.map hτ).prod) =
        if ρ ∈ L then ((u ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ) else 1 := by
    intro L
    induction L with
    | nil => intro _ ρ; simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]; exact GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ ρ V
    | cons a L ih =>
      intro hL ρ
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, ih hL.2 ρ, compAt_eq_infMat]
      by_cases c : ρ = a
      · subst c
        rw [(hhτ ρ).2.1, if_neg hL.1, if_pos List.mem_cons_self, Matrix.mul_one]
      · rw [(hhτ a).2.2 ρ c, Matrix.one_mul]
        by_cases d : ρ ∈ L
        · rw [if_pos d, if_pos (List.mem_cons_of_mem a d)]
        · rw [if_neg d, if_neg (by simp [c, d])]
  let L := (Finset.univ : Finset D.what₂.Tau).toList
  have hmem : (L.map hτ).prod ∈ GinfC V := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact (hhτ τ).1
  refine ⟨(⟨(L.map hτ).prod, hmem⟩ : GinfC V)⁻¹, ?_⟩
  funext ρ
  apply Subtype.ext
  rw [realCol_apply]
  simp only [InvMemClass.coe_inv, inv_inv]
  rw [key L (Finset.nodup_toList _) ρ, if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ)), Matrix.transpose_transpose]

end GlobalTheory.RealColAct
