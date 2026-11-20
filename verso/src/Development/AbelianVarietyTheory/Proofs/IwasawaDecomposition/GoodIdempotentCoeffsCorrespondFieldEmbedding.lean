import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanCw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.GoodIdemBC

/- English proof (translation)
Introduce `x y h`. Apply `Units.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Units.val h`. Use extensionality with `i j`. Conclude with `hψ (congrFun (congrFun h' i) j)`.
-/
theorem bc_injective {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : Function.Injective (Formalism.UG.bc (n := n) ψ) := by
  intro x y h
  apply Units.ext
  have h' := congrArg Units.val h
  ext i j
  exact hψ (congrFun (congrFun h' i) j)

/- English proof (translation)
Substitute `h` using the available equality. Establish `e : (ψ1 : ZMod q →+* kP P1) = ψ2` using `Subsingleton.elim _ _`. Rewrite `hxy` using `[e]`. Conclude with `bc_injective _ ψ2.injective (eq_of_heq hxy)`.
-/
theorem eq_of_bc_heq {E : Type} [Field E] [NumberField E] {q r : ℕ} {P1 P2 : Pl E} (h : P1 = P2)
    (ψ1 : ZMod q ≃+* kP P1) (ψ2 : ZMod q ≃+* kP P2) (x y : GL (Fin r) (ZMod q))
    (hxy : HEq (Formalism.UG.bc (ψ1 : ZMod q →+* kP P1) x) (Formalism.UG.bc (ψ2 : ZMod q →+* kP P2) y)) : x = y := by
  subst h
  have e : (ψ1 : ZMod q →+* kP P1) = ψ2 := Subsingleton.elim _ _
  rw [e] at hxy
  exact bc_injective _ ψ2.injective (eq_of_heq hxy)

/- English proof (translation)
Substitute `hS hPg` using the available equality. Consider the cases of `he`. Consider the cases of `hg`. Rewrite using `[Subtype.ext hp]`.
-/
theorem eG_app_heq {E1 E2 : Type} [Field E1] [Field E2] [NumberField E2] {r : ℕ} {S S' : Finset (HeightOneSpectrum (𝓞 E1))}
    {Pg Pg' : Finset (Pl E2)} (hS : S' = S) (hPg : Pg' = Pg) (eG : Formalism.L2.Col.G0 E1 S r ≃* G0 Pg r)
    (eG' : Formalism.L2.Col.G0 E1 S' r ≃* G0 Pg' r) (he : HEq eG' eG) (g : Formalism.L2.Col.G0 E1 S r) (g' : Formalism.L2.Col.G0 E1 S' r)
    (hg : HEq g' g) (p : Pg) (p' : Pg') (hp : (p' : Pl E2) = p) : HEq (eG' g' p') (eG g p) := by
  subst hS hPg
  cases he
  cases hg
  rw [Subtype.ext hp]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `_ _ _ _ _ _ _`. Use `StepW.of_all ?_` and prove the remaining obligations. Introduce `K B' f' T' w' hO hFo hP' B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ g g' hg`. Establish `k1` using `z.good.2 g`. Establish `k2` using `z'.good.2 g'`.

Take `⟨plg, iso, hplg, -, -, hiso⟩` from `z.pins.keep.grp`. Take `⟨plg', iso', hplg', -, -, hiso'⟩` from `z'.pins.keep.grp`. Apply `(w'.st Z').B.embLL.injective` to reduce the goal to its premises. Use `k2.trans (Eq.trans ?_ ((hφ _).trans k1).symm)` and prove the remaining obligations. Take `⟨P, r⟩` from `B`.

Take `⟨P', r'⟩` from `B'`. Take `⟨h1, -⟩` from `hE`. Simplify using `only at h1`. Substitute `h1` using the available equality. Consider the cases of `hf`.

Establish `hp` using `eq_of_heq hpx`. Establish `hPg` using `eq_of_heq hEx.Pg`. Establish `key : (z'.R.eG.trans z'.cG) g' = grpEquiv Z.N.naut Z'.N.naut ((z.R.eG.trans z.cG) g)`. Use function extensionality and compare the values at `kv'`. Take `⟨k, v'⟩` from `kv'`.

Take `⟨v, rfl⟩` from `(plEquiv Z.N.naut Z'.N.naut k).surjective v'`. Use `Eq.trans ?_ (grpEquiv_apply' _ _ _ k v).symm` and prove the remaining obligations. Establish `hpl : (plg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1`. Rewrite using `[hplg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩, hplg ⟨k, v⟩]`. Conclude with `TypesTrue.plGw_plEquiv hG hG' k v`.

Use `eq_of_bc_heq hpl (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) (iso ⟨k, v⟩) _ _ ?_` and prove the remaining obligations. Use `(heq_of_eq (hiso' g' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)).symm.trans ((eG_app_heq ?_ hPg _ _ hEx.eG g g' hg _ _ hpl).trans (heq_of_eq (hiso g ⟨k, v⟩)))` and prove the remaining obligations. Conclude with `hp ▸ rfl`. Rewrite using `[key]`. Conclude with `TypesTrue.typeIdempotent_coeff_across_layers hG hG' _`.
-/
theorem idemOf_coeff_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (idemOf z'.Xg).coeff g' = φ ((idemOf z.Xg).coeff g)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all ?_
  intro K B' f' T' w' hO hFo hP' B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ g g' hg
  have k1 := z.good.2 g
  have k2 := z'.good.2 g'
  obtain ⟨plg, iso, hplg, -, -, hiso⟩ := z.pins.keep.grp
  obtain ⟨plg', iso', hplg', -, -, hiso'⟩ := z'.pins.keep.grp
  apply (w'.st Z').B.embLL.injective
  refine k2.trans (Eq.trans ?_ ((hφ _).trans k1).symm)
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  obtain ⟨h1, -⟩ := hE
  dsimp only at h1
  subst h1
  cases hf
  have hp := eq_of_heq hpx
  have hPg := eq_of_heq hEx.Pg
  have key : (z'.R.eG.trans z'.cG) g' = grpEquiv Z.N.naut Z'.N.naut ((z.R.eG.trans z.cG) g) := by
    funext kv'
    obtain ⟨k, v'⟩ := kv'
    obtain ⟨v, rfl⟩ := (plEquiv Z.N.naut Z'.N.naut k).surjective v'
    refine Eq.trans ?_ (grpEquiv_apply' _ _ _ k v).symm
    have hpl : (plg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
      rw [hplg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩, hplg ⟨k, v⟩]
      exact TypesTrue.plGw_plEquiv hG hG' k v
    refine eq_of_bc_heq hpl (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) (iso ⟨k, v⟩) _ _ ?_
    refine (heq_of_eq (hiso' g' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)).symm.trans
      ((eG_app_heq ?_ hPg _ _ hEx.eG g g' hg _ _ hpl).trans (heq_of_eq (hiso g ⟨k, v⟩)))
    exact hp ▸ rfl
  rw [key]
  exact TypesTrue.typeIdempotent_coeff_across_layers hG hG' _

end GlobalTheory.Mem.R3.GoodIdemBC

end
