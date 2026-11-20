import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieConclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
import Formalism.SharpRestriction.Divisibility.WeightFamilies
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open scoped ENNReal

noncomputable section

namespace GlobalTheory.NLink.RowE

open GlobalTheory.IndefiniteRowSideFullHecke

/- English proof (translation)
Proceed by induction on `a using ENat.recTopCoe with`. Consider the case `top => simp`. Consider the case `coe n => simp`.
-/
theorem toReal_enat (a : ℕ∞) : ((a : ℝ≥0∞)).toReal = (a.toNat : ℝ) := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/- English proof (translation)
Unfold `BaseSizes.nlen lenUnit`. Rewrite using `[ENNReal.toReal_div, toReal_enat, toReal_enat]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem nlen_toReal (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] :
    (BaseSizes.nlen O l M).toReal = (lenUnit (O := O) l M : ℝ) := by
  unfold BaseSizes.nlen lenUnit
  rw [ENNReal.toReal_div, toReal_enat, toReal_enat]
  push_cast
  rfl

/- English proof (translation)
Unfold `BaseSizes.nlen`. Conclude with `ENNReal.div_ne_top (by simpa using hM) (by simpa using hl)`.
-/
theorem nlen_ne_top {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (hl : Module.length O (O ⧸ Ideal.span {(l : O)}) ≠ 0) :
    BaseSizes.nlen O l M ≠ ⊤ := by
  unfold BaseSizes.nlen
  exact ENNReal.div_ne_top (by simpa using hM) (by simpa using hl)

/- English proof (translation)
Establish `hI : Finset.Icc 1 D.R.t = (Finset.range D.R.t).map (addRightEmbedding 1)`. Use extensionality with `c`. Simplify using `only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨c - 1, by omega, by omega⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Use linear arithmetic over natural numbers and integers. Unfold `BaseSizes.param JumpDictionary.PP JumpDictionary.param JumpDictionary.run`. Use `congr 1`.

Rewrite using `[hI, Finset.map_val, Multiset.map_map, Finset.range_val]`. Use `Multiset.map_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, addRightEmbedding_apply]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem param_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) : BaseSizes.param D i ρ = JumpDictionary.PP D i ρ := by
  have hI : Finset.Icc 1 D.R.t = (Finset.range D.R.t).map (addRightEmbedding 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨c - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  unfold BaseSizes.param JumpDictionary.PP JumpDictionary.param JumpDictionary.run
  congr 1
  rw [hI, Finset.map_val, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, addRightEmbedding_apply]
  push_cast
  rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `[BaseSizes.embSide, JumpDictionary.embOver, ComplexEmbedding.conjugate_coe_eq, WeightFamilies.emb_conj]`.
-/
theorem embSide_false (D : D7) (ρ : D.what₂.Tau) : BaseSizes.embSide D ρ false = JumpDictionary.embOver D ρ true := by
  ext x
  simp [BaseSizes.embSide, JumpDictionary.embOver, ComplexEmbedding.conjugate_coe_eq, WeightFamilies.emb_conj]

/- English proof (translation)
Use `⟨true, fun ρ => ⟨-1 / 2, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[show BaseSizes.embSide D ρ true = JumpDictionary.embOver D ρ false from rfl, (h i ρ).1, param_eq]`. Use `Multiset.map_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[show BaseSizes.embSide D ρ (!true) = JumpDictionary.embOver D ρ true from embSide_false D ρ, (h i ρ).2, param_eq]`. Use `Multiset.map_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weightTie_of (D : D7) (h : JumpDictionary.WeightParam D) (i : D.nd.Loc) : BaseSizes.WeightTie D i := by
  refine ⟨true, fun ρ => ⟨-1 / 2, ?_, ?_⟩⟩
  · rw [show BaseSizes.embSide D ρ true = JumpDictionary.embOver D ρ false from rfl, (h i ρ).1, param_eq]
    refine Multiset.map_congr rfl fun p _ => ?_
    push_cast
    ring
  · rw [show BaseSizes.embSide D ρ (!true) = JumpDictionary.embOver D ρ true from embSide_false D ρ, (h i ρ).2, param_eq]
    refine Multiset.map_congr rfl fun p _ => ?_
    push_cast
    ring

/- English proof (translation)
Take `⟨e, he⟩` from `h.rho`. Use `⟨h.cont, e, fun g u => ?_⟩` and prove the remaining obligations. Use `he g u` as an intermediate fact. Rewrite `this` using `[BlockRepresentationsSemisimple.blockRep_apply]`. Conclude with `this`.
-/
theorem isRankRPart_of (D : D7) (i : D.nd.Loc) (r₀ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (ρ₀ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (h : BlockRepresentationsSemisimple.IsComplement D.nd i r₀ ρ₀) :
    BaseSizes.IsRankRPart D i r₀ ρ₀ := by
  obtain ⟨e, he⟩ := h.rho
  refine ⟨h.cont, e, fun g u => ?_⟩
  have := he g u
  rw [BlockRepresentationsSemisimple.blockRep_apply] at this
  exact this

end GlobalTheory.NLink.RowE

namespace GlobalTheory.NLink.RowE

open GlobalTheory.IndefiniteRowSideFullHecke

/- English proof (translation)
Introduce `D L r ρ exc hCB hW hP hK hS h3 hexc i hTw hl hg hx π hπ`. Establish `hg'` using `(D.Zgood_tie i π).1 hπ`. Establish `hZ : π ∈ D.nd.Z i` using `(D.Z_tie i π).2 hg'.1`. Establish `hHG : HG D.nd D.naut i` using `⟨π, hg'⟩`. Establish `hk : ∀ k, D.nd.l i ≠ D.host.g k`.

Introduce `k hk`. Apply `hg` to reduce the goal to its premises. Rewrite using `[hk]`. Apply the tactic sequence `fin_cases k <;> simp [TwistedPlaces.gset]`. Establish `hExc : D.nd.l i ∉ BaseSizes.Exc L`.

Rewrite using `[← hexc]`. Conclude with `hx` after adjusting the coercions. Establish `hB` using `hCB i hl hk hExc (GlobalTheory.NLink.RowE.weightTie_of D hW i) hHG (r i) (hP.good i) π hZ (ρ i π) (GlobalTheory.NLink.RowE.isRankRPart_of D i _ _ (hP.compl i π hZ))`. Take `⟨hK1, hK2⟩` from `hK i hTw`. Establish `hram` using `GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i`.

Establish `hsP : BaseSizes.sPi D i π (ρ i π) ≠ ⊤` using `GlobalTheory.NLink.RowE.nlen_ne_top _ _ (hK1 π hπ).1.ne hram.1`. Establish `hsR : (BaseSizes.sPi D i π (ρ i π)).toReal = (Br.sPi D.loc D.nbr i (ρ i) π : ℝ)` using `GlobalTheory.NLink.RowE.nlen_toReal _ _ _`. Establish `hodd : Odd (D.nd.l i)`. Use `(D.nd.lPrime i).out.odd_of_ne_two fun h2 => ?_` and prove the remaining obligations. Establish `h4 : (3 : ℝ) < (D.nd.l i : ℝ)` using `lt_of_le_of_lt h3 hl`.

Rewrite `h4` using `[h2]`. Evaluate the numerical expressions using `at h4`. Establish `hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) ≠ ⊤`. Introduce `e he`. Rewrite `he` using `[Finset.mem_Ioo]`.

Conclude with `@hS (D.nd.l i) (D.nd.lPrime i) e he.1 he.2`. Establish `hshaF : BaseSizes.shaSum D i ≠ ⊤`. Unfold `BaseSizes.shaSum`. Conclude with `ENNReal.sum_ne_top.2 fun e he => by simpa using hsha e he`. Establish `hshaR : (BaseSizes.shaSum D i).toReal = TwistedPlaces.VVr D (D.nd.l i)`.

Unfold `BaseSizes.shaSum TwistedPlaces.VVr`. Rewrite using `[ENNReal.toReal_sum (fun e he => by simpa using hsha e he)]`. Rewrite using `[show D.what₂.VV (D.nd.l i) = ∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e from rfl, show Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t by ext; simp; omega]`. Use `push_cast`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations.

Establish `he'` using `Finset.mem_Ioo.1 he`. Rewrite using `[GlobalTheory.NLink.RowE.toReal_enat, D.nd.sha_eq (D.nd.l i) e he'.1 he'.2 _ (ENat.coe_toNat (hsha e he)).symm]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hvC : BaseSizes.vClass D i ≠ ⊤`.

Unfold `BaseSizes.vClass`. Simplify using the standard rewrite rules. Establish `hvCR : (BaseSizes.vClass D i).toReal = TwistedPlaces.vhE D (D.nd.l i)`. Unfold `BaseSizes.vClass TwistedPlaces.vhE hE`. Simplify using the standard rewrite rules.

Establish `hzeta : ∀ P ∈ D.nd.Q i, BaseSizes.zetaP D i P - 1 ≠ 0`. Introduce `P hP`. Rewrite using `[BaseSizes.zetaP_eq D i P hP, sub_ne_zero]`. Conclude with `((GlobalTheory.TameDesign.main D i).2 P (Or.inr hP)).2.2.1 hP`. Establish `hvO : ∀ P ∈ D.nd.Q i, BaseSizes.vO (D.nd.O i) (D.nd.l i) (BaseSizes.zetaP D i P - 1) ≠ ⊤`.

Introduce `P hP`. Use `GlobalTheory.NLink.RowE.nlen_ne_top _ _ ?_ hram.1` and prove the remaining obligations. Rewrite using `[Module.length_ne_top_iff]`. Conclude with `isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (hzeta P hP))`. Establish `hepsF : BaseSizes.epsQ D i ≠ ⊤`.

Unfold `BaseSizes.epsQ`. Conclude with `ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 hvO)`. Establish `hepsR : (BaseSizes.epsQ D i).toReal ≤ TwistedPlaces.epsL (D.nd.l i)`. Use `Eq.trans_le ?_ hK2` and prove the remaining obligations. Unfold `BaseSizes.epsQ`.

Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_sum hvO]`. Use `push_cast`. Use `congr 1`. Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations. Unfold `BaseSizes.vO`.

Rewrite using `[GlobalTheory.NLink.RowE.nlen_toReal, BaseSizes.zetaP_eq D i P hP]`. Establish `hvcc : (BaseSizes.vCC D i π).toReal = (D.nd.vcc i π : ℝ)`. Rewrite using `[GlobalTheory.Proof.QuotientLengthInfimum.vCC_eq]`. Conclude with `GlobalTheory.NLink.RowE.nlen_toReal _ _ _`. Establish `hmono` using `ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩, hepsF⟩) hB`.

Rewrite `hmono` using `[ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩) hepsF, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩) hvC, ENNReal.toReal_add hsP hshaF, hvcc, hsR, hshaR, hvCR]`. Unfold `Bd`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  intro D L r ρ exc hCB hW hP hK hS h3 hexc i hTw hl hg hx π hπ
  have hg' := (D.Zgood_tie i π).1 hπ
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 hg'.1
  have hHG : HG D.nd D.naut i := ⟨π, hg'⟩
  have hk : ∀ k, D.nd.l i ≠ D.host.g k := by
    intro k hk
    apply hg
    rw [hk]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have hExc : D.nd.l i ∉ BaseSizes.Exc L := by
    rw [← hexc]
    exact_mod_cast hx
  have hB := hCB i hl hk hExc (GlobalTheory.NLink.RowE.weightTie_of D hW i) hHG (r i) (hP.good i) π hZ (ρ i π)
    (GlobalTheory.NLink.RowE.isRankRPart_of D i _ _ (hP.compl i π hZ))
  obtain ⟨hK1, hK2⟩ := hK i hTw
  have hram := GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i

  have hsP : BaseSizes.sPi D i π (ρ i π) ≠ ⊤ := GlobalTheory.NLink.RowE.nlen_ne_top _ _ (hK1 π hπ).1.ne hram.1
  have hsR : (BaseSizes.sPi D i π (ρ i π)).toReal = (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) :=
    GlobalTheory.NLink.RowE.nlen_toReal _ _ _

  have hodd : Odd (D.nd.l i) := by
    refine (D.nd.lPrime i).out.odd_of_ne_two fun h2 => ?_
    have h4 : (3 : ℝ) < (D.nd.l i : ℝ) := lt_of_le_of_lt h3 hl
    rw [h2] at h4
    norm_num at h4
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) ≠ ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact @hS (D.nd.l i) (D.nd.lPrime i) e he.1 he.2
  have hshaF : BaseSizes.shaSum D i ≠ ⊤ := by
    unfold BaseSizes.shaSum
    exact ENNReal.sum_ne_top.2 fun e he => by simpa using hsha e he
  have hshaR : (BaseSizes.shaSum D i).toReal = TwistedPlaces.VVr D (D.nd.l i) := by
    unfold BaseSizes.shaSum TwistedPlaces.VVr
    rw [ENNReal.toReal_sum (fun e he => by simpa using hsha e he)]
    rw [show D.what₂.VV (D.nd.l i) = ∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e from rfl,
      show Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t by ext; simp; omega]
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := Finset.mem_Ioo.1 he
    rw [GlobalTheory.NLink.RowE.toReal_enat, D.nd.sha_eq (D.nd.l i) e he'.1 he'.2 _ (ENat.coe_toNat (hsha e he)).symm]
    push_cast
    rfl

  have hvC : BaseSizes.vClass D i ≠ ⊤ := by
    unfold BaseSizes.vClass
    simp
  have hvCR : (BaseSizes.vClass D i).toReal = TwistedPlaces.vhE D (D.nd.l i) := by
    unfold BaseSizes.vClass TwistedPlaces.vhE hE
    simp

  have hzeta : ∀ P ∈ D.nd.Q i, BaseSizes.zetaP D i P - 1 ≠ 0 := by
    intro P hP
    rw [BaseSizes.zetaP_eq D i P hP, sub_ne_zero]
    exact ((GlobalTheory.TameDesign.main D i).2 P (Or.inr hP)).2.2.1 hP
  have hvO : ∀ P ∈ D.nd.Q i, BaseSizes.vO (D.nd.O i) (D.nd.l i) (BaseSizes.zetaP D i P - 1) ≠ ⊤ := by
    intro P hP
    refine GlobalTheory.NLink.RowE.nlen_ne_top _ _ ?_ hram.1
    rw [Module.length_ne_top_iff]
    exact isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (hzeta P hP))
  have hepsF : BaseSizes.epsQ D i ≠ ⊤ := by
    unfold BaseSizes.epsQ
    exact ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 hvO)
  have hepsR : (BaseSizes.epsQ D i).toReal ≤ TwistedPlaces.epsL (D.nd.l i) := by
    refine Eq.trans_le ?_ hK2
    unfold BaseSizes.epsQ
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum hvO]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun P hP => ?_
    unfold BaseSizes.vO
    rw [GlobalTheory.NLink.RowE.nlen_toReal, BaseSizes.zetaP_eq D i P hP]

  have hvcc : (BaseSizes.vCC D i π).toReal = (D.nd.vcc i π : ℝ) := by
    rw [GlobalTheory.Proof.QuotientLengthInfimum.vCC_eq]
    exact GlobalTheory.NLink.RowE.nlen_toReal _ _ _
  have hmono := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩, hepsF⟩) hB
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩) hepsF,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩) hvC, ENNReal.toReal_add hsP hshaF,
    hvcc, hsR, hshaR, hvCR] at hmono
  unfold Bd
  linarith

end GlobalTheory.NLink.RowE

end
