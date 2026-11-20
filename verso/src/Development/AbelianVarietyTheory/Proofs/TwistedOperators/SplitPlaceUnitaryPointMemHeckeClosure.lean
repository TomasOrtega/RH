import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFrameLatticeIffIntegralCoords
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCartanGen

open Formalism.UG

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

def dg : (Fin n → (v.adicCompletion F)ˣ) →* GL (Fin n) (v.adicCompletion F) :=
  (Units.map (Matrix.diagonalRingHom (Fin n) (v.adicCompletion F)).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dg_val (u : Fin n → (v.adicCompletion F)ˣ) :
    (dg u).1 = Matrix.diagonal fun i => (u i : v.adicCompletion F) := rfl

def heckeL (ϖ : v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F)) :=
  {x | ∃ k : ℕ, (∀ i j, x.1 i j ∈ Ov F v) ∧ (∀ i j, ϖ * (x⁻¹).1 i j ∈ Ov F v) ∧
    Valued.v x.1.det = Valued.v ϖ ^ k}

/- English proof (translation)
Use `⟨1, fun a b => ?_, fun a b => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[dg_val, Matrix.diagonal_apply] split_ifs with hab`. Rewrite using `[Pi.mulSingle_apply] split_ifs`. Simplify using `using hϖO`. Simplify using `using one_mem (Ov F v)`.

Conclude with `zero_mem _`. Rewrite using `[← map_inv, dg_val, Matrix.diagonal_apply] split_ifs with hab`. Rewrite using `[Pi.inv_apply, Pi.mulSingle_apply] split_ifs`. Simplify `one_mem (Ov F v)` using `[h0]`. Simplify using `using hϖO`.

Rewrite using `[mul_zero]`. Conclude with `zero_mem _`. Rewrite using `[dg_val, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_pi_mulSingle']`. Simplify using the standard rewrite rules.
-/
theorem single_mem {ϖ : v.adicCompletion F} (h0 : ϖ ≠ 0) (hϖO : ϖ ∈ Ov F v) (i : Fin n) :
    dg (Pi.mulSingle i (Units.mk0 ϖ h0)) ∈ heckeL (n := n) ϖ := by
  classical
  refine ⟨1, fun a b => ?_, fun a b => ?_, ?_⟩
  · rw [dg_val, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [Pi.mulSingle_apply]
      split_ifs
      · simpa using hϖO
      · simpa using one_mem (Ov F v)
    · exact zero_mem _
  · rw [← map_inv, dg_val, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [Pi.inv_apply, Pi.mulSingle_apply]
      split_ifs
      · simpa [h0] using one_mem (Ov F v)
      · simpa using hϖO
    · rw [mul_zero]; exact zero_mem _
  · rw [dg_val, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_pi_mulSingle']
    simp

/- English proof (translation)
Establish `h0 : ϖ ≠ 0` using `(GlobalTheory.SplitPlace.unif_facts hϖ).1`. Use `set S := ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪ {x | x⁻¹ ∈ heckeL ϖ}) with hS`. Use `set M := (Submonoid.closure S).comap (dg (v := v) (n := n)) with hM`. Establish `hz : ∀ i (z : ℤ), Pi.mulSingle i (Units.mk0 ϖ h0 ^ z) ∈ M`. Introduce `i z`.

Establish `hmz` using `map_zpow (MonoidHom.mulSingle (fun _ : Fin n => (v.adicCompletion F)ˣ) i) (Units.mk0 ϖ h0) z`. Simplify using `only [MonoidHom.mulSingle_apply] at hmz`. Rewrite using `[hmz]`. Establish `m1 : Pi.mulSingle i (Units.mk0 ϖ h0) ∈ M` using `Submonoid.subset_closure (Or.inl (Or.inr (single_mem h0 hϖO i)))`. Establish `m2 : (Pi.mulSingle i (Units.mk0 ϖ h0))⁻¹ ∈ M`.

Use `Submonoid.subset_closure (Or.inr ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(dg _)⁻¹ ∈ heckeL ϖ`. Rewrite using `[map_inv, inv_inv]`. Conclude with `single_mem h0 hϖO i`. Break down `z with m | m` into its components or cases.

Rewrite using `[Int.ofNat_eq_coe, zpow_natCast]`. Conclude with `pow_mem m1 m`. Rewrite using `[zpow_negSucc, ← inv_pow]`. Conclude with `pow_mem m2 _`. Take `⟨a, -, k₁, hk₁, k₂, hk₂, e⟩` from `Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ g`.

Establish `hu : (fun i => Units.mk0 ϖ h0 ^ a i) ∈ M`. Rewrite using `[← Finset.univ_prod_mulSingle (fun i => Units.mk0 ϖ h0 ^ a i)]`. Conclude with `Submonoid.prod_mem M fun i _ => hz i (a i)`. Establish `hg : g = k₁ * dg (fun i => Units.mk0 ϖ h0 ^ a i) * k₂`. Use `Units.ext ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Units.val_mul, dg_val, e]`. Use `congr 2`. Simplify using `[diagPow, Units.val_zpow_eq_zpow_val]`. Rewrite using `[hg]`. Conclude with `mul_mem (mul_mem (Submonoid.subset_closure (Or.inl (Or.inl hk₁))) hu) (Submonoid.subset_closure (Or.inl (Or.inl hk₂)))`.
-/
theorem local_closure {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ Ov F v)
    (g : GL (Fin n) (v.adicCompletion F)) :
    g ∈ Submonoid.closure ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪
      {x | x⁻¹ ∈ heckeL ϖ}) := by
  classical
  have h0 : ϖ ≠ 0 := (GlobalTheory.SplitPlace.unif_facts hϖ).1
  set S := ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪
      {x | x⁻¹ ∈ heckeL ϖ}) with hS
  set M := (Submonoid.closure S).comap (dg (v := v) (n := n)) with hM
  have hz : ∀ i (z : ℤ), Pi.mulSingle i (Units.mk0 ϖ h0 ^ z) ∈ M := by
    intro i z
    have hmz := map_zpow (MonoidHom.mulSingle (fun _ : Fin n => (v.adicCompletion F)ˣ) i) (Units.mk0 ϖ h0) z
    simp only [MonoidHom.mulSingle_apply] at hmz
    rw [hmz]
    have m1 : Pi.mulSingle i (Units.mk0 ϖ h0) ∈ M :=
      Submonoid.subset_closure (Or.inl (Or.inr (single_mem h0 hϖO i)))
    have m2 : (Pi.mulSingle i (Units.mk0 ϖ h0))⁻¹ ∈ M := by
      refine Submonoid.subset_closure (Or.inr ?_)
      change (dg _)⁻¹ ∈ heckeL ϖ
      rw [map_inv, inv_inv]
      exact single_mem h0 hϖO i
    rcases z with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact pow_mem m1 m
    · rw [zpow_negSucc, ← inv_pow]; exact pow_mem m2 _
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ g
  have hu : (fun i => Units.mk0 ϖ h0 ^ a i) ∈ M := by
    rw [← Finset.univ_prod_mulSingle (fun i => Units.mk0 ϖ h0 ^ a i)]
    exact Submonoid.prod_mem M fun i _ => hz i (a i)
  have hg : g = k₁ * dg (fun i => Units.mk0 ϖ h0 ^ a i) * k₂ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, dg_val, e]
    congr 2
    simp [diagPow, Units.val_zpow_eq_zpow_val]
  rw [hg]
  exact mul_mem (mul_mem (Submonoid.subset_closure (Or.inl (Or.inl hk₁))) hu)
    (Submonoid.subset_closure (Or.inl (Or.inl hk₂)))

end Local

end GlobalTheory.SplitCartanGen

namespace GlobalTheory.SplitCartanGen

open Formalism.UG GlobalTheory.SplitPlace

/- English proof (translation)
Introduce `D V P e ϖ he hP hP2 h _ hs`. Take `⟨v, π, s, h1, h2, h3, h4, h5⟩` from `GlobalTheory.SplitCoord.exists_coord e he.1`. Take `⟨B, hB⟩` from `GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1.1 h2 h3 h4 (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2`. Take `⟨hex, hinj⟩` from `comp_bij (V := V) (B := B) he.1 h1 h2`. Establish `hK` using `fun g => K_iff (g := g) he.1 h2 h3 hB`.

Establish `hu` using `isUnif he h4 h5 ϖ hP hP2`. Establish `hH` using `hecke_iff he.1 h1 h2 h3 h4 hB (unif_facts hu).1`. Establish `hloc` using `local_closure hu (unif_facts hu).2 (comp V π B h)`. Establish `s1 : Formalism.L2.Theta.SuppAt e V 1`. Rewrite using `[suppAt_iff, mt_one, sub_self, smul_zero]`.

It suffices to establish `key : ∀ a ∈ Submonoid.closure ((GLint (Fin V.rank) (Ov D.host.F v) : Set (GL (Fin V.rank) (Fv D.host.F v))) ∪ heckeL (π (finPart D (incA D (ϖ : D.host.E)))) ∪ {x | x⁻¹ ∈ heckeL (π (finPart D (incA D (ϖ : D.host.E))))}), ∀ g, Formalism.L2.Theta.SuppAt e V g → comp V π B g = a → g …`. Introduce `a ha`. Proceed by induction on `ha using Submonoid.closure_induction with`. Consider the case `mem x hx`. Introduce `g hg hgx`.

Apply `Submonoid.subset_closure` to reduce the goal to its premises. Break down `hx with (hx | ⟨k, hx⟩) | ⟨k, hx⟩` into its components or cases. Conclude with `Or.inl (Or.inl ⟨(hK g hg).2 (hgx ▸ hx), hg⟩)`. Conclude with `Or.inl (Or.inr ⟨k, (hH k g).2 ⟨hg, hgx ▸ hx⟩⟩)`. Use `Or.inr ⟨k, (hH k g⁻¹).2 ⟨suppAt_inv hg, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[map_inv, hgx]`. Conclude with `hx`. Consider the case `one`. Introduce `g hg hg1`. Establish `: g = 1` using `hinj _ _ hg s1 (by rw [hg1, map_one])`.

Rewrite using `[this]`. Conclude with `one_mem _`. Consider the case `mul x y _ _ ihx ihy`. Introduce `g hg hgxy`. Take `⟨gx, sx, rfl⟩` from `hex x`.

Take `⟨gy, sy, rfl⟩` from `hex y`. Establish `: g = gx * gy` using `hinj _ _ hg (suppAt_mul sx sy) (by rw [hgxy, map_mul])`. Rewrite using `[this]`. Conclude with `mul_mem (ihx gx sx rfl) (ihy gy sy rfl)`.
-/
theorem supp_mem_closure : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal →
    ϖ ∉ P.asIdeal ^ 2 → ∀ h ∈ GfC V, Formalism.L2.Theta.SuppAt e V h →
      h ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) := by
  intro D V P e ϖ he hP hP2 h _ hs
  classical
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1.1 h2 h3 h4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨hex, hinj⟩ := comp_bij (V := V) (B := B) he.1 h1 h2
  have hK := fun g => K_iff (g := g) he.1 h2 h3 hB
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hH := hecke_iff he.1 h1 h2 h3 h4 hB (unif_facts hu).1
  have hloc := local_closure hu (unif_facts hu).2 (comp V π B h)
  have s1 : Formalism.L2.Theta.SuppAt e V 1 := by
    rw [suppAt_iff, mt_one, sub_self, smul_zero]
  suffices key : ∀ a ∈ Submonoid.closure ((GLint (Fin V.rank) (Ov D.host.F v) : Set (GL (Fin V.rank) (Fv D.host.F v))) ∪
      heckeL (π (finPart D (incA D (ϖ : D.host.E)))) ∪ {x | x⁻¹ ∈ heckeL (π (finPart D (incA D (ϖ : D.host.E))))}),
      ∀ g, Formalism.L2.Theta.SuppAt e V g → comp V π B g = a → g ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) from key _ hloc h hs rfl
  intro a ha
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    intro g hg hgx
    apply Submonoid.subset_closure
    rcases hx with (hx | ⟨k, hx⟩) | ⟨k, hx⟩
    · exact Or.inl (Or.inl ⟨(hK g hg).2 (hgx ▸ hx), hg⟩)
    · exact Or.inl (Or.inr ⟨k, (hH k g).2 ⟨hg, hgx ▸ hx⟩⟩)
    · refine Or.inr ⟨k, (hH k g⁻¹).2 ⟨suppAt_inv hg, ?_⟩⟩
      rw [map_inv, hgx]
      exact hx
  | one =>
    intro g hg hg1
    have : g = 1 := hinj _ _ hg s1 (by rw [hg1, map_one])
    rw [this]
    exact one_mem _
  | mul x y _ _ ihx ihy =>
    intro g hg hgxy
    obtain ⟨gx, sx, rfl⟩ := hex x
    obtain ⟨gy, sy, rfl⟩ := hex y
    have : g = gx * gy := hinj _ _ hg (suppAt_mul sx sy) (by rw [hgxy, map_mul])
    rw [this]
    exact mul_mem (ihx gx sx rfl) (ihy gy sy rfl)

end GlobalTheory.SplitCartanGen
