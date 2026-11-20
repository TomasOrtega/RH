import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadratiStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareChars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩`.
-/
theorem isHeckeChar_mul' {c c' : (AE D)ˣ →* Circle} (h : IsHeckeChar D c) (h' : IsHeckeChar D c') :
    IsHeckeChar D (c * c') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩`.
-/
theorem isHeckeChar_pow' {c : (AE D)ˣ →* Circle} (h : IsHeckeChar D c) (n : ℕ) : IsHeckeChar D (c ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩`.
-/
theorem resEta_pow' {c : (AE D)ˣ →* Circle} (h : ResEta D c 1) (n : ℕ) : ResEta D (c ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

/- English proof (translation)
Establish `h1 : 1 ≤ D.R.m - (i : ℕ)` using `by omega`. Establish `h2 : D.R.m - (i : ℕ) ≤ D.R.m` using `Nat.sub_le _ _`. Establish `hc` using `G.ch.chi_eq _ h1 h2`. Use `⟨⟨hc.1.1, hc.1.2⟩, ?_⟩` and prove the remaining obligations. Establish `hres` using `GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta`.

Use `⟨⟨_, hres⟩, fun η _ a => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, GlobalTheory.GridWeil.triv_base hc (G.ch.triv _ h1 h2) a]`.
-/
theorem chi_hecke_res (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (i : Fin D.R.m) :
    IsHeckeChar D (G.ch.chi (D.R.m - i)) ∧ ResEta D (G.ch.chi (D.R.m - i)) 0 := by
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hc := G.ch.chi_eq _ h1 h2
  refine ⟨⟨hc.1.1, hc.1.2⟩, ?_⟩
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η _ a => ?_⟩
  rw [pow_zero, GlobalTheory.GridWeil.triv_base hc (G.ch.triv _ h1 h2) a]

/- English proof (translation)
Establish `r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b` using `fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Establish `e1 : (spW G i j).rank = rankV D (i + 1) (j + 1)` using `r _ _ (by omega) (by omega)`. Establish `e2 : (spW₁ G i j).rank = rankV D i j` using `r _ _ (by omega) (by omega)`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps`. Rewrite using `[e1, e2]`. Take `⟨a, ha⟩` from `D.R.t_odd`. Take `⟨b, hb⟩` from `odd_sLen D`. Simplify using `only [rankV, ha, hb]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Nat.mod_mod]`. Put the polynomial expressions in normal form. Use linear arithmetic over natural numbers and integers. Rewrite using `[Nat.mod_mod]`.
-/
theorem rank_parity (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (i j : Fin D.R.m) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) % 2 = (spW G i j).rank % 2 ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) % 2 = (spW₁ G i j).rank % 2 := by
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := r _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := r _ _ (by omega) (by omega)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [e1, e2]
  obtain ⟨a, ha⟩ := D.R.t_odd
  obtain ⟨b, hb⟩ := odd_sLen D
  simp only [rankV, ha, hb]
  constructor
  · rw [Nat.mod_mod]; ring_nf; omega
  · rw [Nat.mod_mod]

end GlobalTheory.SquareChars

namespace GlobalTheory.SquareChars

/- English proof (translation)
Introduce `D T L sc G μ₀ hL t i j _`. Take `⟨hχ, hχ0⟩` from `chi_hecke_res G hL i`. Establish `hμ` using `GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j`. Establish `hμ0` using `GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j`. Establish `hη` using `isHeckeChar_pow' hL.eta.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)`.

Establish `hη1` using `resEta_pow' (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)`. Take `⟨p1, p2⟩` from `rank_parity G hL i j`. Establish `hβ : ResEta D (beta G i j) (spW G i j).rank` using `resEta_parity (resEta_mul hχ0 hη1) (by rw [zero_add]; exact p1)`. Establish `hα : ResEta D (alpha G t i j) (spW₁ G i j).rank` using `resEta_parity (resEta_mul hμ0 hη1) (by rw [zero_add]; exact p2)`. Establish `h2 : Module.finrank D.host.F D.host.E = 2` using `D.sp.cm.deg2`.

Conclude with `⟨isHeckeChar_mul' hχ hη, isHeckeChar_mul' hμ hη, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow D.host.F D.host.E h2 _ _ hβ, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow D.host.F D.host.E h2 _ _ hα⟩`.
-/
theorem square_chars : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t →
      GlobalTheory.LFun.IsHecke D.host.F D.host.E (beta G i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) ∧
      GlobalTheory.LFun.IsHecke D.host.F D.host.E (alpha G t i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) ∧
      GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F) : D.host.F →* AF D.host.F)).range
        (beta G i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (spW G i j).rank ∧
      GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F) : D.host.F →* AF D.host.F)).range
        (alpha G t i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL t i j _
  obtain ⟨hχ, hχ0⟩ := chi_hecke_res G hL i
  have hμ := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j
  have hμ0 := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hη := isHeckeChar_pow' hL.eta.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  have hη1 := resEta_pow' (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  obtain ⟨p1, p2⟩ := rank_parity G hL i j
  have hβ : ResEta D (beta G i j) (spW G i j).rank :=
    resEta_parity (resEta_mul hχ0 hη1) (by rw [zero_add]; exact p1)
  have hα : ResEta D (alpha G t i j) (spW₁ G i j).rank :=
    resEta_parity (resEta_mul hμ0 hη1) (by rw [zero_add]; exact p2)
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  exact ⟨isHeckeChar_mul' hχ hη, isHeckeChar_mul' hμ hη,
    GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow D.host.F D.host.E h2 _ _ hβ, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow D.host.F D.host.E h2 _ _ hα⟩

end GlobalTheory.SquareChars
