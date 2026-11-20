import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.BotBigLevel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar Formalism.L2.DIV GlobalTheory.BotFinLevel
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hi : i.val < b`. Simplify using `[topL, Matrix.mul_apply, hi]`. Simplify using `[topL, Matrix.mul_apply, hi]`.
-/
theorem topL_mul_sq {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

/- English proof (translation)
Establish `h1 : IsUnitDet e M = IsUnitDet e N`. Use function extensionality and compare the values at `x`. Unfold `IsUnitDet`. Rewrite using `[h]`. Unfold `unitChar`.

Rewrite using `[h1]`.
-/
theorem unitChar_congr (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) (e : Formalism.L2.Theta.AE D) {k : ℕ}
    {M N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (h : M.det = N.det) : unitChar ν e M = unitChar ν e N := by
  have h1 : IsUnitDet e M = IsUnitDet e N := by
    funext x
    unfold IsUnitDet
    rw [h]
  unfold unitChar
  rw [h1]

/- English proof (translation)
Use `inId_mul (K := K.transpose) (Y := Y.transpose) (j := i) (fun a b => hK b a) h j` as an intermediate fact. Rewrite `this` using `[← Matrix.transpose_mul]`. Then use the resulting hypothesis.
-/
theorem inId_mul_right {I : Ideal (𝓞 D.host.E)} {k d : ℕ} {K : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hK : IsIntM K)
    {Y : Matrix (Fin d) (Fin k) (Lev.EAf D)} {i : Fin d} (h : ∀ j, InId I (Y i j)) (j : Fin k) :
    InId I ((HMul.hMul Y K) i j) := by
  have := inId_mul (K := K.transpose) (Y := Y.transpose) (j := i) (fun a b => hK b a) h j
  rwa [← Matrix.transpose_mul] at this

/- English proof (translation)
Use `(inv_eq_of_mul_eq_one_right (Units.ext ?_)).symm` and prove the remaining obligations. Establish `h1 : (Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det = 1`. Rewrite using `[← Matrix.det_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_mul_inv, Matrix.det_one]`. Rewrite using `[Units.val_mul, detIdl_val hee, detIdl_val hee, Units.val_one]`. Take the linear combination `e * h1 + ((Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det - (Formalism.L2.Theta.mt S g).det - (Formalism.L2.Theta.mt S g⁻¹).det + 1) * hee`.
-/
theorem detIdl_inv {e : Formalism.L2.Theta.AE D} (hee : e * e = e) (S : HSp D) (g : Formalism.L2.Theta.GA D S) :
    detIdl e S g⁻¹ = (detIdl e S g)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right (Units.ext ?_)).symm
  have h1 : (Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_mul_inv, Matrix.det_one]
  rw [Units.val_mul, detIdl_val hee, detIdl_val hee, Units.val_one]
  linear_combination e * h1 + ((Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det - (Formalism.L2.Theta.mt S g).det -
    (Formalism.L2.Theta.mt S g⁻¹).det + 1) * hee

/- English proof (translation)
Establish `hee : e * e = e` using `GlobalTheory.PlaceDatum.idemSum_mul_self he`. Establish `hg' : Lev.finE S g⁻¹ ∈ St βS` using `by rw [map_inv]; exact inv_mem hg`. Establish `hK : (frG S βS g).1 * (frG S βS g⁻¹).1 = 1`. Rewrite using `[Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.mul_inv]`. Establish `hK' : (frG S βS g⁻¹).1 * (frG S βS g).1 = 1`.

Rewrite using `[Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.inv_mul]`. Establish `h1 : frG T βT 1 = 1`. Unfold `frG`. Rewrite using `[map_one, mul_one, inv_mul_cancel]`. Establish `hact : frMapO S T βS βT (actO S T g 1 y) = HMul.hMul (frMapO S T βS βT y) (frG S βS g⁻¹).1`.

Rewrite using `[Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_actO, h1, Units.val_one, Matrix.one_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv]`. Establish `hback : frMapO S T βS βT y = HMul.hMul (HMul.hMul (frMapO S T βS βT y) (frG S βS g⁻¹).1) (frG S βS g).1`. Rewrite using `[Matrix.mul_assoc, hK', Matrix.mul_one]`. Unfold `stdFst`. Rewrite using `[hact]`.

Distinguish the cases in `hc : IsHalf e y ∧ IsIntM (frMapO S T βS βT y) ∧ ∀ i j, S.rank ≤ i.1 → InId I (frMapO S T βS βT y i j)`. Rewrite using `[if_pos hc, if_pos ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).2 hc.1, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul hc.2.1 (isIntM_frG hg'), fun i j hi => inId_mul_right (isIntM_frG hg') (fun l => hc.2.2 i l hi) j⟩, topL_mul_sq, unitChar_congr ν e (Matrix.det_mul_comm …`. Rewrite using `[if_neg hc, if_neg, mul_zero]`. Introduce and unpack `⟨h1, h2, h3⟩`. Use `hc ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).1 h1, ?_, fun i j hi => ?_⟩` and prove the remaining obligations.

Rewrite using `[hback]`. Conclude with `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul h2 (isIntM_frG hg)`. Rewrite using `[hback]`. Conclude with `inId_mul_right (isIntM_frG hg) (fun l => h3 i l hi) j`.
-/
theorem stdFst_actO (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (I : Ideal (𝓞 D.host.E)) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    {g : Formalism.L2.Theta.GA D S} (hg : Lev.finE S g ∈ St βS) (y : WO S T) :
    stdFst ν e I S T βS βT (actO S T g 1 y) = ((ν (detIdl e S g) : Circle) : ℂ) * stdFst ν e I S T βS βT y := by
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hg' : Lev.finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact inv_mem hg
  have hK : (frG S βS g).1 * (frG S βS g⁻¹).1 = 1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.mul_inv]
  have hK' : (frG S βS g⁻¹).1 * (frG S βS g).1 = 1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.inv_mul]
  have h1 : frG T βT 1 = 1 := by
    unfold frG
    rw [map_one, mul_one, inv_mul_cancel]
  have hact : frMapO S T βS βT (actO S T g 1 y) = HMul.hMul (frMapO S T βS βT y) (frG S βS g⁻¹).1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_actO, h1, Units.val_one, Matrix.one_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv]
  have hback : frMapO S T βS βT y =
      HMul.hMul (HMul.hMul (frMapO S T βS βT y) (frG S βS g⁻¹).1) (frG S βS g).1 := by
    rw [Matrix.mul_assoc, hK', Matrix.mul_one]
  unfold stdFst
  rw [hact]
  by_cases hc : IsHalf e y ∧ IsIntM (frMapO S T βS βT y) ∧ ∀ i j, S.rank ≤ i.1 → InId I (frMapO S T βS βT y i j)
  · rw [if_pos hc, if_pos ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).2 hc.1,
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul hc.2.1 (isIntM_frG hg'),
      fun i j hi => inId_mul_right (isIntM_frG hg') (fun l => hc.2.2 i l hi) j⟩, topL_mul_sq,
      unitChar_congr ν e (Matrix.det_mul_comm _ _),
      unitChar_mul ν hee hK (isUnitDet_frG he hg') (isUnitDet_frG he hg), detIdl_inv hee, map_inv, inv_inv]
  · rw [if_neg hc, if_neg, mul_zero]
    rintro ⟨h1, h2, h3⟩
    refine hc ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).1 h1, ?_, fun i j hi => ?_⟩
    · rw [hback]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul h2 (isIntM_frG hg)
    · rw [hback]; exact inId_mul_right (isIntM_frG hg) (fun l => h3 i l hi) j

/- English proof (translation)
Establish `hW : IsWeilDatumO ψ (GlobalTheory.Grid.neg A) WW (β s) (β s / α s) ((X.ω s).toSgn true)` using `hX.weil s`. Establish `hA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ` using `GlobalTheory.RowTest.isSelfDualC_neg' hX.rigA.1`. Use `set k' : Formalism.L2.Theta.GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm k with hk'`. Establish `hk1' : k' ∈ GfC (GlobalTheory.Grid.neg A)` using `hk1`. Establish `hk2' : Lev.finE (GlobalTheory.Grid.neg A) k' ∈ St X.rA.β` using `hk2`.

Establish `he` using `hX.idem s`. Establish `hee : X.e s * X.e s = X.e s` using `GlobalTheory.PlaceDatum.idemSum_mul_self he`. Establish `hP : ∀ w ∈ S s, Formalism.L2.NTheta.IsIdemAt (idemAt w) w` using `fun w hw => by`. Take `⟨⟨es, hes, -⟩, -⟩` from `he`. Conclude with `Classical.epsilon_spec (p := fun e : Formalism.L2.Theta.AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩`.

Establish `h1 : Lev.finE WW 1 ∈ St X.rW.β` using `by rw [map_one]; exact one_mem _`. Establish `hv` using `GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW hA hX.rigW.1 (S s) hP (GlobalTheory.LevelPlaces.under_injOn he) (fun v hv => ⟨(hu v hv).2, by`. Rewrite using `[div_eq_mul_inv]`. Conclude with `GlobalTheory.SeeSaw.WeilLines.charUnram_mul (hu v hv).2 (GlobalTheory.SeeSaw.WeilLines.charUnram_inv (hu v hv).1)⟩)`. Use the proof step `k' hk1' 1 (one_mem _) (keeps_latHat (S := GlobalTheory.Grid.neg A) hX.rigA.2.1 hk2') (keeps_latHat hX.rigW.2.1 h1) X.vac`.

Use the proof step `hX.isVac.2.theta hX.isVac.2.lat`. Establish `hc : (∏ w ∈ S s, ((splitFacO (β s) (β s / α s) (detIdl (idemAt w) (GlobalTheory.Grid.neg A) k') (detIdl (idemAt w) WW 1) : Circle) : ℂ)) = (((α s / β s) (detIdl (X.e s) (GlobalTheory.Grid.neg A) k') : Circle) : ℂ)`. Rewrite using `[← prod_detIdl he hP, map_prod]`. Rewrite using `[show ∀ f : Pl D.host.E → Circle, ((∏ w ∈ S s, f w : Circle) : ℂ) = ∏ w ∈ S s, (f w : ℂ) from fun f => map_prod Circle.coeHom f (S s)]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[splitFacO, detIdl_one, map_one, mul_one, MonoidHom.div_apply, MonoidHom.div_apply, inv_div]`. Rewrite `hv` using `[hc]`. Establish `key` using `GlobalTheory.SchrMove.smul_om_eq D ψ (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ _ _ _ hW hA hX.rigW.1 (X.e s) hee (GlobalTheory.PlaceDatum.infPart_idemSum he) k' 1 (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW _ _ _ _ hA hX.rigW.1 hX.rigA.2.1 hX.ri …`. Conclude with `smul_right_injective _ (Circle.coe_ne_zero _) key`.
-/
theorem fix_fst_of_unram {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}
    (hX : X.Is ψ θ α β νH S) (s : T)
    (hu : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ S s, w.under (𝓞 D.host.F) ≠ v) →
      CharUnramAt D (α s) v ∧ CharUnramAt D (β s) v)
    {k : Formalism.L2.Theta.GA D A} (hk1 : k ∈ GfC A) (hk2 : Lev.finE A k ∈ St X.rA.β) : X.ω s (k, 1) (X.f s) = X.f s := by
  have hW : IsWeilDatumO ψ (GlobalTheory.Grid.neg A) WW (β s) (β s / α s) ((X.ω s).toSgn true) := hX.weil s
  have hA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.rigA.1
  set k' : Formalism.L2.Theta.GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm k with hk'
  have hk1' : k' ∈ GfC (GlobalTheory.Grid.neg A) := hk1
  have hk2' : Lev.finE (GlobalTheory.Grid.neg A) k' ∈ St X.rA.β := hk2
  have he := hX.idem s
  have hee : X.e s * X.e s = X.e s := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hP : ∀ w ∈ S s, Formalism.L2.NTheta.IsIdemAt (idemAt w) w := fun w hw => by
    obtain ⟨⟨es, hes, -⟩, -⟩ := he
    exact Classical.epsilon_spec (p := fun e : Formalism.L2.Theta.AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩
  have h1 : Lev.finE WW 1 ∈ St X.rW.β := by rw [map_one]; exact one_mem _
  have hv := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW hA hX.rigW.1 (S s) hP (GlobalTheory.LevelPlaces.under_injOn he)
    (fun v hv => ⟨(hu v hv).2, by
      rw [div_eq_mul_inv]
      exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul (hu v hv).2 (GlobalTheory.SeeSaw.WeilLines.charUnram_inv (hu v hv).1)⟩)
    k' hk1' 1 (one_mem _) (keeps_latHat (S := GlobalTheory.Grid.neg A) hX.rigA.2.1 hk2') (keeps_latHat hX.rigW.2.1 h1) X.vac
    hX.isVac.2.theta hX.isVac.2.lat
  have hc : (∏ w ∈ S s, ((splitFacO (β s) (β s / α s) (detIdl (idemAt w) (GlobalTheory.Grid.neg A) k')
      (detIdl (idemAt w) WW 1) : Circle) : ℂ)) = (((α s / β s) (detIdl (X.e s) (GlobalTheory.Grid.neg A) k') : Circle) : ℂ) := by
    rw [← prod_detIdl he hP, map_prod]
    rw [show ∀ f : Pl D.host.E → Circle, ((∏ w ∈ S s, f w : Circle) : ℂ) = ∏ w ∈ S s, (f w : ℂ) from
      fun f => map_prod Circle.coeHom f (S s)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [splitFacO, detIdl_one, map_one, mul_one, MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
  rw [hc] at hv
  have key := GlobalTheory.SchrMove.smul_om_eq D ψ (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ _ _ _ hW hA hX.rigW.1 (X.e s)
    hee (GlobalTheory.PlaceDatum.infPart_idemSum he) k' 1
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW _ _ _ _ hA hX.rigW.1 hX.rigA.2.1 hX.rigW.2.1 k' 1 hk2' h1)
    X.vac _ (X.f s) _ _ hX.isVac.2.theta (hX.fst s) (Circle.coe_ne_zero _) hv
    (stdFst_actO (α s / β s) he (X.ideal S s) (GlobalTheory.Grid.neg A) WW X.rA.β X.rW.β hk2')
  exact smul_right_injective _ (Circle.coe_ne_zero _) key

/- English proof (translation)
Take `rfl : A.rank = n` from `hk.2.choose`. Establish `hΛ : r.Λ = Formalism.L2.Col.stdLat D.host.E A.rank`. Use extensionality with `y`. Rewrite using `[hs.2.1 y]`. Conclude with `⟨fun h i _ => Submodule.mem_one.2 (h i), fun h i => Submodule.mem_one.1 (h i trivial)⟩`.

Establish `hβ : Formalism.L2.DIV.IsFrame r.β (Formalism.L2.Col.stdLat D.host.E A.rank)` using `hΛ ▸ hr.2.1`. Use `(GlobalTheory.BotClassDict.mem_level_iff A hs.1 hβ k).2 ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.BotClassDict.finStd_of_isFinPt A hs.1 hk]`. Conclude with `hx`.
-/
theorem mem_St_of_isFinPt {A : HSp D} {r : Rig A} (hr : r.Is) (hs : r.IsStd) {n : ℕ} {x : Formalism.MainNotions.StandardLatticesGL3.GA D n}
    {k : Formalism.L2.Theta.GA D A} (hx : x ∈ GlobalTheory.NormSum.intG D n) (hk : GlobalTheory.BotFormula.IsFinPt A k x) : Lev.finE A k ∈ St r.β := by
  obtain rfl : A.rank = n := hk.2.choose
  have hΛ : r.Λ = Formalism.L2.Col.stdLat D.host.E A.rank := by
    ext y
    rw [hs.2.1 y]
    exact ⟨fun h i _ => Submodule.mem_one.2 (h i), fun h i => Submodule.mem_one.1 (h i trivial)⟩
  have hβ : Formalism.L2.DIV.IsFrame r.β (Formalism.L2.Col.stdLat D.host.E A.rank) := hΛ ▸ hr.2.1
  refine (GlobalTheory.BotClassDict.mem_level_iff A hs.1 hβ k).2 ?_
  rw [GlobalTheory.BotClassDict.finStd_of_isFinPt A hs.1 hk]
  exact hx

/- English proof (translation)
Use `set pt : (WO (GlobalTheory.Grid.neg A) WW → ℂ) → (WO (GlobalTheory.Grid.neg A) WW → ℂ) := fun f => pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B f P with hpt`. Establish `e1 : ∀ f, ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm k, 1) f = X.ω t (k, 1) f` using `fun f => rfl`. Establish `move : X.ω t (k, 1) (pt (X.f t)) = pt (X.ω t (k, 1) (X.f t))`. Rewrite using `[← e1, ← e1]`. Conclude with `GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hX.weil t) θ hX.isVac.2.inf ((GlobalTheory.Grid.ofSgn true A).symm k) hk 1 (one_mem _) (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P (GlobalTheory.ConstRatio.theta_f hX t).1`.

Establish `e2 : ∀ z, X.ker ψ θ t P g z = X.ω t (z, g) (pt (X.f t)) 0` using `fun z => rfl`. Establish `e3 : ((y * k, g) : Formalism.L2.Theta.GA D A × Formalism.L2.Theta.GA D WW) = (y, g) * (k, 1)`. Rewrite using `[Prod.mk_mul_mk, mul_one]`. Rewrite using `[e2, e2, e3, map_mul, Module.End.mul_apply, move, hf]`.
-/
theorem ker_mul_of_fix {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}
    (hX : X.Is ψ θ α β νH S) (t : T) {k : Formalism.L2.Theta.GA D A} (hk : k ∈ GfC A) (hf : X.ω t (k, 1) (X.f t) = X.f t)
    (P : PolF D WW.rank A.rank) (g : Formalism.L2.Theta.GA D WW) (y : Formalism.L2.Theta.GA D A) :
    X.ker ψ θ t P g (y * k) = X.ker ψ θ t P g y := by
  set pt : (WO (GlobalTheory.Grid.neg A) WW → ℂ) → (WO (GlobalTheory.Grid.neg A) WW → ℂ) := fun f =>
    pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B f P with hpt
  have e1 : ∀ f, ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm k, 1) f = X.ω t (k, 1) f := fun f => rfl
  have move : X.ω t (k, 1) (pt (X.f t)) = pt (X.ω t (k, 1) (X.f t)) := by
    rw [← e1, ← e1]
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hX.weil t) θ hX.isVac.2.inf ((GlobalTheory.Grid.ofSgn true A).symm k) hk 1
      (one_mem _) (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P (GlobalTheory.ConstRatio.theta_f hX t).1
  have e2 : ∀ z, X.ker ψ θ t P g z = X.ω t (z, g) (pt (X.f t)) 0 := fun z => rfl
  have e3 : ((y * k, g) : Formalism.L2.Theta.GA D A × Formalism.L2.Theta.GA D WW) = (y, g) * (k, 1) := by
    rw [Prod.mk_mul_mk, mul_one]
  rw [e2, e2, e3, map_mul, Module.End.mul_apply, move, hf]

end GlobalTheory.BotBigLevel

/- English proof (translation)
Introduce `_ _ _ _ _`. Use `⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩` and prove the remaining obligations. Introduce `W _ i j A A' WW X hX t Pf g n x k hx hk y`. Conclude with `GlobalTheory.BotBigLevel.ker_mul_of_fix hX.is t hk.1 (GlobalTheory.BotBigLevel.fix_fst_of_unram hX.is t (fun v hv => GlobalTheory.BotFinLevel.unram_off G hμ t i j _ hv) hk.1 (GlobalTheory.BotBigLevel.mem_St_of_isFinPt hX.is.rigA hX.std hx hk)) Pf g y`.
-/
theorem GlobalTheory.BotBigLevel.ker_mul_level : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (Pf : PolF D WW.rank A.rank) (g : Formalism.L2.Theta.GA D WW) (n : ℕ) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n)
        (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ y, X.ker W.ψ W.θ t Pf g (y * k) = X.ker W.ψ W.θ t Pf g y := by
  intro _ _ _ _ _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W _ i j A A' WW X hX t Pf g n x k hx hk y
  exact GlobalTheory.BotBigLevel.ker_mul_of_fix hX.is t hk.1
    (GlobalTheory.BotBigLevel.fix_fst_of_unram hX.is t (fun v hv => GlobalTheory.BotFinLevel.unram_off G hμ t i j _ hv) hk.1
      (GlobalTheory.BotBigLevel.mem_St_of_isFinPt hX.is.rigA hX.std hx hk)) Pf g y

end
