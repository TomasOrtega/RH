import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameSplitPlaceEntriesOffPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVectorConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorIdentityIsotypicConjugateType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesMemPlacesOverGenerators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugateStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameSplitConjMemIntegralMatricesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualFrameConjugatePlaceIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLPullbackContinuousRingEquivStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000

section SphOffSec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

namespace GlobalTheory.RowSphOff

/- English proof (translation)
The claim follows from `GlobalTheory.T.standardFrame_split_conj_mem_integral_matrices`.
-/
theorem kO_frame_cpt : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b)) ≤ 1 := GlobalTheory.T.standardFrame_split_conj_mem_integral_matrices

/- English proof (translation)
The claim follows from `GlobalTheory.T.selfDualFrame_conjugate_place_integral`.
-/
theorem int_cP_of_inv : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b)) ≤ 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b)) ≤ 1 := GlobalTheory.T.selfDualFrame_conjugate_place_integral

/- English proof (translation)
The claim follows from `GlobalTheory.T.integralGL_pullback_continuousRingEquiv`.
-/
theorem mem_KO_of_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (c : v.adicCompletion F ≃+* w.adicCompletion E), Continuous c → ∀ {n : ℕ} (A : GL (Fin n) (v.adicCompletion F)), Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) → A ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) := GlobalTheory.T.integralGL_pullback_continuousRingEquiv

/- English proof (translation)
Introduce `L _ _ _ n π s τ hloc f hf hf0 hfix`. Take `⟨c, _, hc, hci, _⟩` from `id hloc`. Establish `hspan` using `GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent L n π s τ hloc c hc hci hf`. Set `H : Subgroup (GAf L n)` to `{ carrier := {x | TrivOutside {s.v} x} mul_mem' := fun {x y} hx hy v hv => by`. Simplify using `only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]`.

Use the proof step `one_mem' := fun v _ => by simp`. Use the proof step `inv_mem' := fun {x} hx v hv => by`. Establish `h1 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1` using `by simp`. Establish `h2` using `congrArg (fun M => Matrix.map M (compAt L v)) h1`. Simplify using `only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2`.

Conclude with `h2 }`. Set `φ : H →* GL (Fin n) (s.w.adicCompletion L)` to `(Matrix.GeneralLinearGroup.map c.toRingHom).comp ((s.loc n).comp H.subtype)`. Establish `hφ : Function.Surjective φ`. Introduce `h`. Take `⟨x, hx, e⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)`.

Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h`. Rewrite using `[e]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Set `σ' : Representation ℂ H τ.V` to `τ.ρ.comp φ`. Establish `hσ' : σ'.IsIrreducible` using `GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr φ hφ`. Set `ρ' : Representation ℂ H (GAf L n → ℂ)` to `{ toFun := fun x => NG.rt L n (x : GAf L n) map_one' := by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`.

Use function extensionality and compare the values at `a`. Simplify using `[NG.rt]`. Use the proof step `map_mul' := fun x y => by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `g`.

Use function extensionality and compare the values at `a`. Simplify using `[NG.rt, mul_assoc] }`. Rewrite `hspan` using `[iSup_subtype']`. Take `⟨t, ht⟩` from `Submodule.mem_iSup_iff_exists_finset.1 hspan`. Set `T : t → σ'.IntertwiningMap ρ'` to `fun j => LinearMap.intertwiningMap_of_isIntertwiningMap σ' ρ' j.1.1 fun g v => j.1.2.2 g.1 g.2 v`.

Establish `hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap`. Rewrite `ht` using `[iSup_subtype']`. Conclude with `ht`. Set `K : Subgroup H` to `(GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n)).comap φ`. Establish `hfixK : ∀ k ∈ K, ρ' k f = f` using `fun k hk => hfix k.1 k.2 (mem_KO_of_map c hc _ hk)`.

Establish `hne` using `GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK`. Rewrite `hne`, the goal using `[Submodule.ne_bot_iff]`. Take `⟨y, hy, hy0⟩` from `hne`. Use `⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hy0⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hφ h`.

Conclude with `GlobalTheory.Parabolic.mem_fixed.1 hy x hh`.
-/
theorem fixed_kO_ne_bot : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → s.loc n κ ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ hloc f hf hf0 hfix
  classical
  obtain ⟨c, _, hc, hci, _⟩ := id hloc
  have hspan := GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent L n π s τ hloc c hc hci hf
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun {x y} hx hy v hv => by
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]
      one_mem' := fun v _ => by simp
      inv_mem' := fun {x} hx v hv => by
        have h1 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
        have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
        simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
        exact h2 }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map c.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h
    rw [e]
    ext i j
    simp
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr φ hφ
  let ρ' : Representation ℂ H (GAf L n → ℂ) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [iSup_subtype'] at hspan
  obtain ⟨t, ht⟩ := Submodule.mem_iSup_iff_exists_finset.1 hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    LinearMap.intertwiningMap_of_isIntertwiningMap σ' ρ' j.1.1 fun g v => j.1.2.2 g.1 g.2 v
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n)).comap φ
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk =>
    hfix k.1 k.2 (mem_KO_of_map c hc _ hk)
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hy0⟩
  obtain ⟨x, rfl⟩ := hφ h
  exact GlobalTheory.Parabolic.mem_fixed.1 hy x hh

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP s hoff`. Establish `hβ` using `hP.char.base.lev.βY 0 Y.hm`. Take `⟨h, hh⟩` from `kO_frame_cpt D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) Y.stdPsi.1 s`. Establish `hPgOver : ∀ P ∈ R.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k)`. Introduce `P hP'`.

Take `⟨k, hk⟩` from `(hP.char.base.lev.Pg P).1 hP'`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `h1` using `R.C.P.pb_over k`. Rewrite `h1` using `[← hk]`. Establish `h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ P.asIdeal` using `h1`.

Simplify `h2` using `[placesOver]`. Establish `hOff : ∀ P ∈ R.Pg, P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal`. Introduce `P hP' hPv`. Take `⟨k, hk⟩` from `hPgOver P hP'`. Apply `hoff k` to reduce the goal to its premises.

Break down `GlobalTheory.T.placeOver_splitPlace_eq_chosen_or_conjugate D Y.hF s P hPv with rfl | rfl` into its components or cases. Conclude with `hk`. Simplify `hk` using `[placesOver, GlobalTheory.IdemSupport.mem_cP, map_natCast]`. Establish `hint : ∀ κ' : Formalism.AUTREP.GAf D.host.E D.R.r, TrivOutside {s.v} κ' → h⁻¹ * s.loc D.R.r κ' * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) → h⁻¹ * s.loc D.R.r κ'⁻¹ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalReal …`. Introduce `κ' hκ' hk1 hk2 Q a c`.

Distinguish the cases in `hQ : Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal`. Break down `GlobalTheory.T.placeOver_splitPlace_eq_chosen_or_conjugate D Y.hF s Q hQ with rfl | rfl` into its components or cases. Conclude with `hh κ' hκ' hk1 a c`. Use `int_cP_of_inv D (Yc D 0) (R.βY 0) _ _ hβ (Y.PY.ψ κ') s.w (fun a' c' => ?_) a c` and prove the remaining obligations. Use `hh κ'⁻¹ (GlobalTheory.RowLevelSplit.trivOutside_inv hκ') hk2 a' c'` as an intermediate fact.

Rewrite `this` using `[map_inv, map_inv]`. Then use the resulting hypothesis. Rewrite using `[GlobalTheory.T.frameComponent_eq_one_off_splitPlace_of_trivOutside D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) Y.stdPsi.1 s κ' hκ' Q hQ a c, Matrix.one_apply] split_ifs`. Rewrite using `[map_one, map_one]`. Rewrite using `[map_zero, map_zero]`. Conclude with `zero_le'`.

Use `⟨h, fun b κ hκ hk => ?_⟩` and prove the remaining obligations. Establish `hk' : h⁻¹ * s.loc D.R.r κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r)`. Use `Subgroup.inv_mem _ hk` as an intermediate fact. Rewrite `this` using `[show (h⁻¹ * s.loc D.R.r κ * h)⁻¹ = h⁻¹ * (s.loc D.R.r κ)⁻¹ * h by group, ← map_inv]`. Then use the resulting hypothesis. Establish `hk'' : h⁻¹ * s.loc D.R.r κ⁻¹⁻¹ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r)`.

Rewrite using `[inv_inv]` and apply the resulting hypothesis. Use `set x := finE (Yc D 0) (Y.PY.ψ κ) with hxdef`. Use `set β := R.βY 0 with hβdef`. Establish `i1 : ∀ a c, (β⁻¹ * x * β).val a c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `fun a c => (GlobalTheory.AdIsom.mem_OA _).2 fun Q => hint κ hκ hk hk' Q a c`. Establish `hyi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * finE (Yc D 0) (Y.PY.ψ κ⁻¹) * β`.

Rewrite using `[map_inv, map_inv, ← hxdef]`. Use `group`. Establish `i2 : ∀ a c, ((β⁻¹ * x * β)⁻¹).val a c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `fun a c => by`. Rewrite using `[hyi]`. Conclude with `(GlobalTheory.AdIsom.mem_OA _).2 fun Q => hint κ⁻¹ (GlobalTheory.RowLevelSplit.trivOutside_inv hκ) hk' hk'' Q a c`.

Take `⟨z, hz0, hzv⟩` from `GlobalTheory.RowLevelSplit.glInt_of_int (β⁻¹ * x * β) i1 i2`. Establish `hz : Formalism.L2.DIV.frGL β z = x` using `by show β * Formalism.L2.DIV.intGL D.host.F D.host.E (Yc D 0).rank z * β⁻¹ = x`. Rewrite using `[hz0]`. Use `group`. Establish `hS : x ∈ Formalism.L2.DIV.St β` using `⟨z, hz⟩`.

Establish `hred : ∀ PP ∈ R.Pg, Formalism.L2.DIV.redFn β PP x = 1`. Introduce `PP hPP`. Rewrite using `[← hz, Formalism.L2.DIV.redFn_frGL]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a c`.

Use `show Formalism.L2.DIV.resS D.host.F PP (z.val a c) = (1 : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.L2.DIV.kP PP)) a c`. Establish `h0 : Formalism.L2.DIV.resS D.host.F PP (z.val a c - (1 : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a c) = 0`. Rewrite using `[GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]`. Establish `e3 : ((z.val a c - (1 : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a c : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = (β⁻¹ * x * β).val a c - (1 : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (EAf D)) a c`. Apply the tactic sequence `rw [← hzv a c, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl`.

Rewrite using `[e3, map_sub, GlobalTheory.T.frameComponent_eq_one_off_splitPlace_of_trivOutside D (Yc D 0) D.R.r Y.hF Y.PY β Y.stdPsi.1 s κ hκ PP (hOff PP hPP) a c, sub_self, map_zero]`. Conclude with `zero_lt_one`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Apply the tactic sequence `rw [h0, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Establish `hK : x ∈ Formalism.L2.DIV.Kg D.sp.cm (Yc D 0).gram β (R.Pg ∪ ∅)` using `⟨⟨GlobalTheory.LevSplit.finE_mem_UA (Yc D 0) _, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hPP => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hred PP (by simpa using hPP)⟩⟩`.

Conclude with `GlobalTheory.RowLevelSplit.lemB_pf D (Yc D 0) β (R.dat0 (R.toRealDat.levR F.lv2 b)) (R.Pg ∪ ∅) (Y.PY.ψ κ) Finset.subset_union_left Finset.subset_union_right (Y.PY.into κ) hK`.
-/
theorem levS_of_kO_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → ∀ (s : SplitPlace D.host.E), (∀ k : Fin 2, s.w ∉ placesOver D.host.E (D.host.g k)) → ∃ h : GL (Fin D.R.r) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ (b : Bool) (κ : Formalism.AUTREP.GAf D.host.E D.R.r), TrivOutside {s.v} κ → h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) → Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧ levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP s hoff
  have hβ := hP.char.base.lev.βY 0 Y.hm
  obtain ⟨h, hh⟩ := kO_frame_cpt D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) Y.stdPsi.1 s

  have hPgOver : ∀ P ∈ R.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k) := by
    intro P hP'
    obtain ⟨k, hk⟩ := (hP.char.base.lev.Pg P).1 hP'
    refine ⟨k, ?_⟩
    have h1 := R.C.P.pb_over k
    rw [← hk] at h1
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ P.asIdeal := h1
    simpa [placesOver] using h2
  have hOff : ∀ P ∈ R.Pg, P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal := by
    intro P hP' hPv
    obtain ⟨k, hk⟩ := hPgOver P hP'
    apply hoff k
    rcases GlobalTheory.T.placeOver_splitPlace_eq_chosen_or_conjugate D Y.hF s P hPv with rfl | rfl
    · exact hk
    · simpa [placesOver, GlobalTheory.IdemSupport.mem_cP, map_natCast] using hk

  have hint : ∀ κ' : Formalism.AUTREP.GAf D.host.E D.R.r, TrivOutside {s.v} κ' →
      h⁻¹ * s.loc D.R.r κ' * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) →
      h⁻¹ * s.loc D.R.r κ'⁻¹ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) →
      ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a c : Fin (Yc D 0).rank),
        Valued.v (GlobalTheory.StdFrames.cpt Q (((R.βY 0)⁻¹ * finE (Yc D 0) (Y.PY.ψ κ') * R.βY 0).val a c)) ≤ 1 := by
    intro κ' hκ' hk1 hk2 Q a c
    by_cases hQ : Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal
    · rcases GlobalTheory.T.placeOver_splitPlace_eq_chosen_or_conjugate D Y.hF s Q hQ with rfl | rfl
      · exact hh κ' hκ' hk1 a c
      · refine int_cP_of_inv D (Yc D 0) (R.βY 0) _ _ hβ (Y.PY.ψ κ') s.w (fun a' c' => ?_) a c
        have := hh κ'⁻¹ (GlobalTheory.RowLevelSplit.trivOutside_inv hκ') hk2 a' c'
        rwa [map_inv, map_inv] at this
    · rw [GlobalTheory.T.frameComponent_eq_one_off_splitPlace_of_trivOutside D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) Y.stdPsi.1 s κ' hκ' Q hQ a c, Matrix.one_apply]
      split_ifs
      · rw [map_one, map_one]
      · rw [map_zero, map_zero]; exact zero_le'
  refine ⟨h, fun b κ hκ hk => ?_⟩
  classical
  have hk' : h⁻¹ * s.loc D.R.r κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) := by
    have := Subgroup.inv_mem _ hk
    rwa [show (h⁻¹ * s.loc D.R.r κ * h)⁻¹ = h⁻¹ * (s.loc D.R.r κ)⁻¹ * h by group, ← map_inv] at this
  have hk'' : h⁻¹ * s.loc D.R.r κ⁻¹⁻¹ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) := by
    rwa [inv_inv]
  set x := finE (Yc D 0) (Y.PY.ψ κ) with hxdef
  set β := R.βY 0 with hβdef
  have i1 : ∀ a c, (β⁻¹ * x * β).val a c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a c =>
    (GlobalTheory.AdIsom.mem_OA _).2 fun Q => hint κ hκ hk hk' Q a c
  have hyi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * finE (Yc D 0) (Y.PY.ψ κ⁻¹) * β := by
    rw [map_inv, map_inv, ← hxdef]; group
  have i2 : ∀ a c, ((β⁻¹ * x * β)⁻¹).val a c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a c => by
    rw [hyi]
    exact (GlobalTheory.AdIsom.mem_OA _).2 fun Q => hint κ⁻¹ (GlobalTheory.RowLevelSplit.trivOutside_inv hκ) hk' hk'' Q a c
  obtain ⟨z, hz0, hzv⟩ := GlobalTheory.RowLevelSplit.glInt_of_int (β⁻¹ * x * β) i1 i2
  have hz : Formalism.L2.DIV.frGL β z = x := by
    show β * Formalism.L2.DIV.intGL D.host.F D.host.E (Yc D 0).rank z * β⁻¹ = x
    rw [hz0]; group
  have hS : x ∈ Formalism.L2.DIV.St β := ⟨z, hz⟩
  have hred : ∀ PP ∈ R.Pg, Formalism.L2.DIV.redFn β PP x = 1 := by
    intro PP hPP
    rw [← hz, Formalism.L2.DIV.redFn_frGL]
    apply Units.ext
    ext a c
    show Formalism.L2.DIV.resS D.host.F PP (z.val a c) = (1 : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.L2.DIV.kP PP)) a c
    have h0 : Formalism.L2.DIV.resS D.host.F PP (z.val a c - (1 : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a c) = 0 := by
      rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
      have e3 : ((z.val a c - (1 : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a c : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
          (β⁻¹ * x * β).val a c - (1 : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (EAf D)) a c := by
        rw [← hzv a c, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      rw [e3, map_sub, GlobalTheory.T.frameComponent_eq_one_off_splitPlace_of_trivOutside D (Yc D 0) D.R.r Y.hF Y.PY β Y.stdPsi.1 s κ hκ PP (hOff PP hPP) a c, sub_self, map_zero]
      exact zero_lt_one
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have hK : x ∈ Formalism.L2.DIV.Kg D.sp.cm (Yc D 0).gram β (R.Pg ∪ ∅) :=
    ⟨⟨GlobalTheory.LevSplit.finE_mem_UA (Yc D 0) _, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hPP =>
      Formalism.L2.DIV.mem_princAt.2 ⟨hS, hred PP (by simpa using hPP)⟩⟩
  exact GlobalTheory.RowLevelSplit.lemB_pf D (Yc D 0) β (R.dat0 (R.toRealDat.levR F.lv2 b)) (R.Pg ∪ ∅) (Y.PY.ψ κ)
    Finset.subset_union_left Finset.subset_union_right (Y.PY.into κ) hK

/- English proof (translation)
Use `haveI hE : IsEmpty Empty := ⟨fun e => e.elim⟩`. Take `⟨b, hb⟩` from `principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)`. Use `set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ`. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hfixY : ∀ κ ∈ U, actM Y.PY (R.MY 0) κ y = y`. Introduce `κ hκ`. Take `⟨hJ, hχ⟩` from `hU b κ hκ`. Establish `hgen : ∀ T ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))), actM Y.PY (R.MY 0) κ T = T`.

Introduce `T hT`. Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem T hT`. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Use function extensionality and compare the values at `g`. Rewrite using `[actM_apply, hT.lev v _ hJ g, hχ, one_mul]`. Consider the case `zero => exact map_zero _`. Consider the case `add a c _ _ ha hc => rw [map_add, ha, hc]`. Consider the case `smul a c _ hc => rw [map_smul, hc]`.

Conclude with `hgen y hy.1.1`. Establish `key` using `GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum D D.R.r _ (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) π U Empty (fun _ => 0) (fun _ => 1) (fun φ hφ hfix => by`. Rewrite using `[finsum_of_isEmpty]`. Assume the negation of the conclusion as `hne`. Take `⟨κ, hκ, hκf⟩` from `hcon φ hφ (Ne.symm hne)`.

Conclude with `hκf (hfix κ hκ)) y hy.2 hfixY`. Rewrite `key` using `[finsum_of_isEmpty]`. Conclude with `hy0 key.symm`.
-/
theorem exists_fixed_of_level (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (σ : D.what₂.FT) (U : Set (Formalism.AUTREP.GAf D.host.E D.R.r)) (hU : ∀ (b : Bool), ∀ κ ∈ U, Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧ levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1) : ∃ f ∈ (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S, f ≠ 0 ∧ ∀ κ ∈ U, NG.rt D.host.E D.R.r κ f = f := by
  haveI hE : IsEmpty Empty := ⟨fun e => e.elim⟩
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  by_contra hcon
  push_neg at hcon
  have hfixY : ∀ κ ∈ U, actM Y.PY (R.MY 0) κ y = y := by
    intro κ hκ
    obtain ⟨hJ, hχ⟩ := hU b κ hκ
    have hgen : ∀ T ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))), actM Y.PY (R.MY 0) κ T = T := by
      intro T hT
      induction hT using Submodule.span_induction with
      | mem T hT =>
        apply MultilinearMap.ext
        intro v
        funext g
        rw [actM_apply, hT.lev v _ hJ g, hχ, one_mul]
      | zero => exact map_zero _
      | add a c _ _ ha hc => rw [map_add, ha, hc]
      | smul a c _ hc => rw [map_smul, hc]
    exact hgen y hy.1.1
  have key := GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum D D.R.r _ (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) π U Empty
    (fun _ => 0) (fun _ => 1) (fun φ hφ hfix => by
      rw [finsum_of_isEmpty]
      by_contra hne
      obtain ⟨κ, hκ, hκf⟩ := hcon φ hφ (Ne.symm hne)
      exact hκf (hfix κ hκ)) y hy.2 hfixY
  rw [finsum_of_isEmpty] at key
  exact hy0 key.symm

/- English proof (translation)
Take `⟨b, hb⟩` from `principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)`. Use `set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ`. Establish `hne : isotIn (D` using `D) (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) (FinTyp.conjT π) ≠ ⊥ := by`. Introduce `h`. Apply `hb` to reduce the goal to its premises.

Unfold `isotE isotL`. Rewrite using `[h, inf_bot_eq]`. Establish `hM` using `hP.char.base.models`. Establish `hθ : IsInfFam R.θ` using `hM.inf`. Establish `hSig : (Yc D 0).SigOK` using `D.sp.Y_sig 0`.

Establish `hfd : ∀ j, j < D.R.m → (R.νY A3.A.μ0 j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY A3.A.μ0 j) (R.νY A3.A.μ0 j)`. Introduce `j hj`. Distinguish the cases in `h : j + 1 < D.R.m`. Use `hM.νY A3.A.μ0 j h` as an intermediate fact. Conclude with `⟨this.1.1, this.2⟩`.

Take `rfl : j = D.R.m - 1` from `by omega`. Use `hM.νY' A3.A.μ0` as an intermediate fact. Conclude with `⟨this.1.1, this.2⟩`. Establish `hHA : HCAll D` using `fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1`. Take `⟨B, k1, k2, k3, k4⟩` from `GlobalTheory.RowSphSmall.exists_form_rowRepR hH hC D G Pl0 I0 T A3 Ks R F cG X0 Y hP σ`.

Establish `hadm : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ Minf R.θ Y.PY (R.MY 0) ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → actM Y.PY (R.MY 0) κ x = x})` using `fun N hN => GlobalTheory.FinTypesRows.minf_adm (M := R.MY 0) Y.PY hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open Y.PY Y.stdPsi.1) N hN`. Establish `hfix : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f})` using `fun N hN => GlobalTheory.RowLocalRows.fixed_fd_of_conjT π N (GlobalTheory.RowLocalRows.fixed_fd_of_isotIn _ _ hadm _ hne N hN)`. Take `⟨W, hWS, hW0, hst, hirr⟩` from `GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace D.host.E D.R.r π B k1 k2 k3 k4 hfix s`. Conclude with `GlobalTheory.RowLocal.isLocS_of_irr π s W hWS hW0 hst hirr`.
-/
theorem exists_isLocS_rows (hH : GlobalTheory.Published.HarishChandraFinite) (hC : GlobalTheory.Published.CuspRapidDecay) (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : Pins R F cG) (σ : D.what₂.FT) (s : SplitPlace D.host.E) : ∃ τ, GlobalTheory.HeightCounting.IsLocS (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).S s τ := by
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  have hne : isotIn (D := D) (actM Y.PY (R.MY 0)) (Minf R.θ Y.PY (R.MY 0)) (FinTyp.conjT π) ≠ ⊥ := by
    intro h
    apply hb
    unfold isotE isotL
    rw [h, inf_bot_eq]
  have hM := hP.char.base.models
  have hθ : IsInfFam R.θ := hM.inf
  have hSig : (Yc D 0).SigOK := D.sp.Y_sig 0
  have hfd : ∀ j, j < D.R.m → (R.νY A3.A.μ0 j).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D j)) (R.fdY A3.A.μ0 j) (R.νY A3.A.μ0 j) := by
    intro j hj
    by_cases h : j + 1 < D.R.m
    · have := hM.νY A3.A.μ0 j h
      exact ⟨this.1.1, this.2⟩
    · obtain rfl : j = D.R.m - 1 := by omega
      have := hM.νY' A3.A.μ0
      exact ⟨this.1.1, this.2⟩
  have hHA : HCAll D := fun V _ S θ M J χ =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  obtain ⟨B, k1, k2, k3, k4⟩ := GlobalTheory.RowSphSmall.exists_form_rowRepR hH hC D G Pl0 I0 T A3 Ks R F cG X0 Y hP σ
  have hadm : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ Minf R.θ Y.PY (R.MY 0) ∧
      ∀ κ, NG.Cong D.host.E D.R.r N κ → actM Y.PY (R.MY 0) κ x = x}) := fun N hN =>
    GlobalTheory.FinTypesRows.minf_adm (M := R.MY 0) Y.PY hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open Y.PY Y.stdPsi.1) N hN
  have hfix : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f}) := fun N hN =>
    GlobalTheory.RowLocalRows.fixed_fd_of_conjT π N (GlobalTheory.RowLocalRows.fixed_fd_of_isotIn _ _ hadm _ hne N hN)
  obtain ⟨W, hWS, hW0, hst, hirr⟩ := GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace D.host.E D.R.r π B k1 k2 k3 k4 hfix s
  exact GlobalTheory.RowLocal.isLocS_of_irr π s W hWS hW0 hst hirr

end GlobalTheory.RowSphOff
end SphOffSec

namespace GlobalTheory.RowSphOff

/- English proof (translation)
Introduce `hPr`. Use `evG_all fun K => lg_all K fun B f T _ => ?_` and prove the remaining obligations. Introduce `hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ s hoff`. Take `⟨h, hh⟩` from `levS_of_kO_conj _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins s hoff`. Take `⟨φ, hφS, hφ0, hφfix⟩` from `exists_fixed_of_level _ _ _ _ _ _ _ z.R z.F p0 Y σ {κ | ReciprocityTheory.Aut.TrivOutside {s.v} κ ∧ h⁻¹ * s.loc _ κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield (w.st Z).toD7.host.E)) (Fin (w.st Z).toD7.R.r)} (fun b κ hκ => hh b κ hκ.1 hκ.2)`.

Take `⟨τ, hτ⟩` from `exists_isLocS_rows hPr.hc hPr.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ s`. Use `⟨τ, hτ, ?_⟩` and prove the remaining obligations. Take `⟨x, hx, e⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq _ s h`. Establish `hmul : ∀ (a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r) (g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ), NG.rt _ _ (a * b) g = NG.rt _ _ a (NG.rt _ _ b g)`. Introduce `a b g`.

Use function extensionality and compare the values at `c`. Simplify using `[NG.rt, mul_assoc]`. Establish `hone : ∀ g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ, NG.rt _ _ 1 g = g`. Introduce `g`. Use function extensionality and compare the values at `c`.

Simplify using `[NG.rt]`. Establish `hT : ∀ a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r, ReciprocityTheory.Aut.TrivOutside {s.v} a → ReciprocityTheory.Aut.TrivOutside {s.v} b → ReciprocityTheory.Aut.TrivOutside {s.v} (a * b)` using `fun a b ha hb v hv => by`. Simplify using `only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]`. Use `fixed_kO_ne_bot _ _ (repOf Y σ) s τ hτ (NG.rt _ _ x⁻¹ φ) ((repOf Y σ).stable _ φ hφS) ?_ ?_` and prove the remaining obligations. Introduce `h0`.

Apply `hφ0` to reduce the goal to its premises. Rewrite using `[← hone φ, ← mul_inv_cancel x, hmul, h0, map_zero]`. Introduce `κ hκ hk`. Establish `h1` using `hφfix (x * κ * x⁻¹) ⟨hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx), by`. Rewrite using `[map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc _ κ * h⁻¹) * h = s.loc _ κ by group]`.

Conclude with `hk⟩`. Rewrite using `[← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]`.
-/
theorem rowSph_overRows : PrN → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (σ : (w.st Z).toD7.what₂.FT) (s : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E), (∀ k : Fin 2, s.w ∉ placesOver (w.st Z).toD7.host.E ((w.st Z).toD7.host.g k)) → ∃ τ, IsLocS (repOf Y σ).S s τ ∧ GlobalTheory.SmGL.IsSpherical τ.ρ := by
  intro hPr
  refine evG_all fun K => lg_all K fun B f T _ => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ s hoff
  obtain ⟨h, hh⟩ := levS_of_kO_conj _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins s hoff
  obtain ⟨φ, hφS, hφ0, hφfix⟩ := exists_fixed_of_level _ _ _ _ _ _ _ z.R z.F p0 Y σ
    {κ | ReciprocityTheory.Aut.TrivOutside {s.v} κ ∧ h⁻¹ * s.loc _ κ * h ∈ GlobalTheory.SplitWeil.KO (s.v.adicCompletion (maximalRealSubfield (w.st Z).toD7.host.E)) (Fin (w.st Z).toD7.R.r)}
    (fun b κ hκ => hh b κ hκ.1 hκ.2)
  obtain ⟨τ, hτ⟩ := exists_isLocS_rows hPr.hc hPr.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ s
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq _ s h
  have hmul : ∀ (a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r) (g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ),
      NG.rt _ _ (a * b) g = NG.rt _ _ a (NG.rt _ _ b g) := by
    intro a b g
    funext c
    simp [NG.rt, mul_assoc]
  have hone : ∀ g : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r → ℂ, NG.rt _ _ 1 g = g := by
    intro g
    funext c
    simp [NG.rt]
  have hT : ∀ a b : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.r, ReciprocityTheory.Aut.TrivOutside {s.v} a →
      ReciprocityTheory.Aut.TrivOutside {s.v} b → ReciprocityTheory.Aut.TrivOutside {s.v} (a * b) :=
    fun a b ha hb v hv => by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha v hv, hb v hv, mul_one]
  refine fixed_kO_ne_bot _ _ (repOf Y σ) s τ hτ (NG.rt _ _ x⁻¹ φ) ((repOf Y σ).stable _ φ hφS) ?_ ?_
  · intro h0
    apply hφ0
    rw [← hone φ, ← mul_inv_cancel x, hmul, h0, map_zero]
  · intro κ hκ hk
    have h1 := hφfix (x * κ * x⁻¹) ⟨hT _ _ (hT _ _ hx hκ) (GlobalTheory.RowLevelSplit.trivOutside_inv hx), by
      rw [map_mul, map_mul, map_inv, e, show h⁻¹ * (h * s.loc _ κ * h⁻¹) * h = s.loc _ κ by group]
      exact hk⟩
    rw [← hmul, show κ * x⁻¹ = x⁻¹ * (x * κ * x⁻¹) by group, hmul, h1]

end GlobalTheory.RowSphOff
