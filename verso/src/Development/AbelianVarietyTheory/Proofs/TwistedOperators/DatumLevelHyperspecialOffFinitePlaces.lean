import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OToSAlgebraMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.LevelOff

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.rTensor_tmul]`. Rewrite using `[← TensorProduct.sum_tmul]`.

Use `congr 1`. Use `GlobalTheory.AdelicU.af_ext fun u => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_sum]`. Distinguish the cases in `hu : u ∈ Sb`. Rewrite using `[Finset.sum_eq_single u (fun v _ hv => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hu h), GlobalTheory.AdelicU.evalV_singleFin_self] show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _`.

Rewrite using `[if_pos hu, one_mul]`. Rewrite using `[Finset.sum_eq_zero (fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne (fun e : u = v => hu (e ▸ hv)) _)] show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _`. Rewrite using `[if_neg hu, zero_mul]`. Consider the case `add x y hx hy => rw [mul_add, hx, hy, ← Finset.sum_add_distrib]`. Simplify using `only [map_add]`.
-/
theorem ind_tmul_mul (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E) :
    (GlobalTheory.AdeleIdem.ind Sb ⊗ₜ[F] (1 : E)) * z =
      ∑ v ∈ Sb, (GlobalTheory.AdelicU.singleFin v).rTensor E
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      LinearMap.rTensor_tmul]
    rw [← TensorProduct.sum_tmul]
    congr 1
    refine GlobalTheory.AdelicU.af_ext fun u => ?_
    rw [map_mul, map_sum]
    by_cases hu : u ∈ Sb
    · rw [Finset.sum_eq_single u (fun v _ hv => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hv) _)
        (fun h => absurd hu h), GlobalTheory.AdelicU.evalV_singleFin_self]
      show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _
      rw [if_pos hu, one_mul]
    · rw [Finset.sum_eq_zero (fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne (fun e : u = v => hu (e ▸ hv)) _)]
      show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _
      rw [if_neg hu, zero_mul]
  | add x y hx hy => rw [mul_add, hx, hy, ← Finset.sum_add_distrib]; simp only [map_add]

/- English proof (translation)
Rewrite using `[ind_tmul_mul]`. Conclude with `Finset.sum_eq_zero fun v hv => by rw [h v hv, map_zero]`.
-/
theorem ind_tmul_mul_eq_zero (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E)
    (h : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z = 0) :
    (GlobalTheory.AdeleIdem.ind Sb ⊗ₜ[F] (1 : E)) * z = 0 := by
  rw [ind_tmul_mul]
  exact Finset.sum_eq_zero fun v hv => by rw [h v hv, map_zero]

/- English proof (translation)
Rewrite using `[TensorProduct.sub_tmul, sub_mul, ← Algebra.TensorProduct.one_def, one_mul, ind_tmul_mul_eq_zero Sb z h, sub_zero]`.
-/
theorem one_sub_ind_tmul_mul (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E)
    (h : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z = 0) :
    ((1 - GlobalTheory.AdeleIdem.ind Sb) ⊗ₜ[F] (1 : E)) * z = z := by
  rw [TensorProduct.sub_tmul, sub_mul, ← Algebra.TensorProduct.one_def, one_mul, ind_tmul_mul_eq_zero Sb z h, sub_zero]

open Filter GlobalTheory.AdelicU

variable {D : D7}

/- English proof (translation)
Establish `e : g ∈ KsphC V ∅ ↔ g ∈ ((levelOff D.sp.cm.sig V.gram (frameLat V) ∅ : Subgroup _) : Set (GA D V))`. Rewrite using `[KsphC_eq]`. Rewrite using `[e, SetLike.mem_coe, mem_levelOff, GfC_eq]`. Simplify using the standard rewrite rules.
-/
theorem mem_KsphC_iff (V : HSp D) (g : GA D V) : g ∈ KsphC V ∅ ↔ g ∈ GfC V ∧ ∀ v, projV V v g ∈ Kv V v := by
  have e : g ∈ KsphC V ∅ ↔ g ∈ ((levelOff D.sp.cm.sig V.gram (frameLat V) ∅ : Subgroup _) : Set (GA D V)) := by
    rw [KsphC_eq]
  rw [e, SetLike.mem_coe, mem_levelOff, GfC_eq]
  simp

/- English proof (translation)
Take `⟨-, -, -, h01, h10⟩` from `hB`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx show x ∈ L0c D V`. Simplify using `using h10 x hx`.

Introduce `hx`. Simplify using `using h01 x hx`.
-/
theorem eq_L0sub {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) : Λ = GlobalTheory.LevSplit.L0sub V := by
  obtain ⟨-, -, -, h01, h10⟩ := hB
  ext x
  constructor
  · intro hx
    show x ∈ L0c D V
    simpa using h10 x hx
  · intro hx
    simpa using h01 x hx

/- English proof (translation)
Establish `hfr : Formalism.L2.DIV.IsFrame β (GlobalTheory.LevSplit.L0sub V)` using `eq_L0sub hB ▸ hB.1`. Establish `e1` using `GlobalTheory.LevSplit.mem_St_iff β _ hfr (Formalism.IndefR.Lev.finE V g)`. Establish `e2` using `GlobalTheory.LevSplit.ksph_iff V g`. Conclude with `e1.trans ⟨fun h => e2.2 ⟨hg, h⟩, fun h => (e2.1 h).2⟩`.
-/
theorem finE_mem_St_iff {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) {g : GA D V} (hg : g ∈ GfC V) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ g ∈ KsphC V ∅ := by
  have hfr : Formalism.L2.DIV.IsFrame β (GlobalTheory.LevSplit.L0sub V) := eq_L0sub hB ▸ hB.1
  have e1 := GlobalTheory.LevSplit.mem_St_iff β _ hfr (Formalism.IndefR.Lev.finE V g)
  have e2 := GlobalTheory.LevSplit.ksph_iff V g
  exact e1.trans ⟨fun h => e2.2 ⟨hg, h⟩, fun h => (e2.1 h).2⟩

/- English proof (translation)
The claim follows from `Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hg.2)`.
-/
theorem finE_mem_St_of_mem_levG {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Lv : LevDat D.host.E ℂ V.rank}
    {g : GA D V} (hg : g ∈ levG V β Lv) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β :=
  Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hg.2)

open Filter GlobalTheory.AdelicU

variable {D : D7}

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, _root_.map_zero, RingHom.map_zero]`. Consider the case `tmul a e => rfl`. Consider the case `add x y hx hy => rw [RingHom.map_add, _root_.map_add, RingHom.map_add, hx, hy]`.
-/
theorem evalV_finPart (v : HeightOneSpectrum (𝓞 D.host.F)) (w : AE D) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (Formalism.L2.Theta.finPart D w) =
      compFin D.host.F D.host.E v w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, _root_.map_zero, RingHom.map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add, _root_.map_add, RingHom.map_add, hx, hy]

/- English proof (translation)
Use `set b : FiniteAdeleRing (𝓞 D.host.F) D.host.F := 1 - GlobalTheory.AdeleIdem.ind Sb with hbdef`. Establish `hb : b ∈ Formalism.UG.intAd D.host.F` using `sub_mem (one_mem _) (GlobalTheory.AdeleIdem.ind_mem Sb)`. Use `GlobalTheory.LevSplit.redFn_eq_one β PP _ hS ⟨_, GlobalTheory.AdeleIdem.one_tmul_mem hb⟩ ?_ ?_` and prove the remaining obligations. Use `GlobalTheory.AdeleIdem.resS_eq_zero PP (PP.under (𝓞 D.host.F)) rfl hb ?_` and prove the remaining obligations. Simplify using `[hbdef, GlobalTheory.AdeleIdem.ind_apply, hPP]`.

Use extensionality with `i j set w : AE D := (Formalism.L2.Theta.mt V h - 1) i j with hw`. Establish `e0 : ((Formalism.L2.Theta.mt V h) - 1).map (GlobalTheory.LevSplit.finSw D) = (Formalism.L2.Theta.mt V h).map (GlobalTheory.LevSplit.finSw D) - 1`. Rewrite using `[Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]`. Establish `ex : ((Formalism.IndefR.Lev.finE V h).1 - 1) i j = Formalism.IndefR.Lev.swapAE D (Formalism.L2.Theta.finPart D w)`. Rewrite using `[GlobalTheory.LevSplit.finE_val, ← e0]`.

Both sides reduce to the same expression. Establish `hz : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (Formalism.L2.Theta.finPart D w) = 0`. Introduce `v hv`. Rewrite using `[evalV_finPart]`. Establish `e1 : (Formalism.L2.Theta.mt V h).map (compFin D.host.F D.host.E v) = 1`.

Establish `e2 : (matHom _ D.sp.cm.sig V.gram (projV V v h)).1 = 1`. Rewrite using `[h1 v hv, MonoidHom.map_one, Units.val_one]`. Conclude with `e2`. Establish `e3 : ((Formalism.L2.Theta.mt V h) - 1).map (compFin D.host.F D.host.E v) = 0`. Rewrite using `[Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), e1, sub_self]`.

Conclude with `congrFun (congrFun e3 i) j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ex]`. Use `show Formalism.IndefR.Lev.swapAE D (b ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _`. Rewrite using `[← RingHom.map_mul]`. Use `congrArg (Formalism.IndefR.Lev.swapAE D) ?_` and prove the remaining obligations.

Conclude with `one_sub_ind_tmul_mul Sb _ hz`.
-/
theorem redFn_eq_one_of_proj {V : HSp D} (β : GL (Fin V.rank) (EAf D)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    {h : GA D V} (hS : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.St β) (h1 : ∀ v ∈ Sb, projV V v h = 1)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP.under (𝓞 D.host.F) ∈ Sb) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V h) = 1 := by
  classical
  set b : FiniteAdeleRing (𝓞 D.host.F) D.host.F := 1 - GlobalTheory.AdeleIdem.ind Sb with hbdef
  have hb : b ∈ Formalism.UG.intAd D.host.F := sub_mem (one_mem _) (GlobalTheory.AdeleIdem.ind_mem Sb)
  refine GlobalTheory.LevSplit.redFn_eq_one β PP _ hS ⟨_, GlobalTheory.AdeleIdem.one_tmul_mem hb⟩ ?_ ?_
  · refine GlobalTheory.AdeleIdem.resS_eq_zero PP (PP.under (𝓞 D.host.F)) rfl hb ?_
    simp [hbdef, GlobalTheory.AdeleIdem.ind_apply, hPP]
  · ext i j
    set w : AE D := (Formalism.L2.Theta.mt V h - 1) i j with hw
    have e0 : ((Formalism.L2.Theta.mt V h) - 1).map (GlobalTheory.LevSplit.finSw D) = (Formalism.L2.Theta.mt V h).map (GlobalTheory.LevSplit.finSw D) - 1 := by
      rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
    have ex : ((Formalism.IndefR.Lev.finE V h).1 - 1) i j = Formalism.IndefR.Lev.swapAE D (Formalism.L2.Theta.finPart D w) := by
      rw [GlobalTheory.LevSplit.finE_val, ← e0]
      rfl
    have hz : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Formalism.L2.Theta.finPart D w) = 0 := by
      intro v hv
      rw [evalV_finPart]
      have e1 : (Formalism.L2.Theta.mt V h).map (compFin D.host.F D.host.E v) = 1 := by
        have e2 : (matHom _ D.sp.cm.sig V.gram (projV V v h)).1 = 1 := by
          rw [h1 v hv, MonoidHom.map_one, Units.val_one]
        exact e2
      have e3 : ((Formalism.L2.Theta.mt V h) - 1).map (compFin D.host.F D.host.E v) = 0 := by
        rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), e1, sub_self]
      exact congrFun (congrFun e3 i) j
    rw [Matrix.smul_apply, smul_eq_mul, ex]
    show Formalism.IndefR.Lev.swapAE D (b ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [← RingHom.map_mul]
    refine congrArg (Formalism.IndefR.Lev.swapAE D) ?_
    exact one_sub_ind_tmul_mul Sb _ hz

open GlobalTheory.AdelicU

/- English proof (translation)
Introduce `D V β Λ Lv Sb hB hPl`. Establish `hsplit` using `GlobalTheory.LevSplit.lev_split V β Λ 1 Lv hB`. Establish `hK : ∀ k ∈ levG V β Lv, ∀ v, projV V v k ∈ Kv V v` using `fun k hk => ((mem_KsphC_iff V k).1 ((finE_mem_St_iff hB hk.1).1 (finE_mem_St_of_mem_levG hk))).2`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP`.

Rewrite `hP` using `[GlobalTheory.GoodPrimes.offS_iff]`. Take `⟨e, f, hpe⟩` from `(GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P`. Establish `h1P : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Rewrite using `[Nat.cast_one]`. Conclude with `fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`.

Take `⟨h1, h2, -⟩` from `hsplit.2 P e f hpe h1P fun PP hPP => ⟨fun e => by subst e; exact hP (hPl _ hPP), fun hc => hP (by rw [← GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc]; exact hPl PP hPP)⟩`. Conclude with `⟨e, f, hpe, h1, h2⟩`. Introduce `g hg`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨⟨g, h, fun _ _ => rfl⟩, fun v _ => hK g h v⟩`. Introduce and unpack `⟨⟨k, hk, heq⟩, hoff⟩`. Establish `hxf : g * k⁻¹ ∈ GfC V` using `mul_mem hg (inv_mem hk.1)`. Establish `hx1 : ∀ v ∈ Sb, projV V v (g * k⁻¹) = 1` using `fun v hv => by`. Rewrite using `[MonoidHom.map_mul, MonoidHom.map_inv, heq v hv, mul_inv_cancel]`.

Establish `hxK : g * k⁻¹ ∈ KsphC V ∅` using `(mem_KsphC_iff V _).2 ⟨hxf, fun v => by`. Distinguish the cases in `hv : v ∈ Sb`. Rewrite using `[hx1 v hv]`. Conclude with `one_mem _`. Rewrite using `[MonoidHom.map_mul, MonoidHom.map_inv]`.

Conclude with `mul_mem (hoff v hv) (inv_mem (hK k hk v))⟩`. Establish `hxS` using `(finE_mem_St_iff hB hxf).2 hxK`. Establish `hxl : g * k⁻¹ ∈ levG V β Lv` using `⟨hxf, GlobalTheory.LevSplit.mem_lev_of_red _ _ β Lv _ (GlobalTheory.LevSplit.finE_mem_UA V _) hxS fun PP hPP => redFn_eq_one_of_proj β Sb hxS hx1 (hPl PP hPP)⟩`. Establish `e : g = g * k⁻¹ * k` using `by rw [inv_mul_cancel_right]`. Rewrite using `[e]`.

Conclude with `mul_mem hxl hk`. Introduce `g haveI := SelfDual.isLattice_frameLat V`. Conclude with `Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V) g)`. Introduce `k hk`. Take `⟨n, hn, h⟩` from `hsplit.1 k hk`.

Conclude with `Complex.norm_eq_one_of_pow_eq_one h hn.ne'`.
-/
theorem level_offS : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Lv : LevDat D.host.E ℂ V.rank) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBaseFrame V β Λ 1 → (∀ PP, PP ∈ Lv.Pg ∨ PP ∈ Lv.Q → PP.under (𝓞 D.host.F) ∈ Sb) → SphOff (levG V β Lv : Set (GA D V)) (levChi V β Lv) Sb ∧ (∀ g ∈ GfC V, g ∈ levG V β Lv ↔ (∃ k ∈ levG V β Lv, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v) ∧ (∀ g : GA D V, {v | projV V v g ∉ Kv V v}.Finite) ∧ ∀ k ∈ levG V β Lv, ‖levChi V β Lv k‖ = 1 := by
  intro D V β Λ Lv Sb hB hPl
  have hsplit := GlobalTheory.LevSplit.lev_split V β Λ 1 Lv hB
  have hK : ∀ k ∈ levG V β Lv, ∀ v, projV V v k ∈ Kv V v := fun k hk =>
    ((mem_KsphC_iff V k).1 ((finE_mem_St_iff hB hk.1).1 (finE_mem_St_of_mem_levG hk))).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    rw [GlobalTheory.GoodPrimes.offS_iff] at hP
    obtain ⟨e, f, hpe⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
    have h1P : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [Nat.cast_one]
      exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    obtain ⟨h1, h2, -⟩ := hsplit.2 P e f hpe h1P fun PP hPP =>
      ⟨fun e => by subst e; exact hP (hPl _ hPP),
       fun hc => hP (by rw [← GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc]; exact hPl PP hPP)⟩
    exact ⟨e, f, hpe, h1, h2⟩
  · intro g hg
    constructor
    · intro h
      exact ⟨⟨g, h, fun _ _ => rfl⟩, fun v _ => hK g h v⟩
    · rintro ⟨⟨k, hk, heq⟩, hoff⟩
      have hxf : g * k⁻¹ ∈ GfC V := mul_mem hg (inv_mem hk.1)
      have hx1 : ∀ v ∈ Sb, projV V v (g * k⁻¹) = 1 := fun v hv => by
        rw [MonoidHom.map_mul, MonoidHom.map_inv, heq v hv, mul_inv_cancel]
      have hxK : g * k⁻¹ ∈ KsphC V ∅ := (mem_KsphC_iff V _).2 ⟨hxf, fun v => by
        by_cases hv : v ∈ Sb
        · rw [hx1 v hv]; exact one_mem _
        · rw [MonoidHom.map_mul, MonoidHom.map_inv]; exact mul_mem (hoff v hv) (inv_mem (hK k hk v))⟩
      have hxS := (finE_mem_St_iff hB hxf).2 hxK
      have hxl : g * k⁻¹ ∈ levG V β Lv := ⟨hxf, GlobalTheory.LevSplit.mem_lev_of_red _ _ β Lv _
        (GlobalTheory.LevSplit.finE_mem_UA V _) hxS fun PP hPP => redFn_eq_one_of_proj β Sb hxS hx1 (hPl PP hPP)⟩
      have e : g = g * k⁻¹ * k := by rw [inv_mul_cancel_right]
      rw [e]
      exact mul_mem hxl hk
  · intro g
    haveI := SelfDual.isLattice_frameLat V
    exact Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V) g)
  · intro k hk
    obtain ⟨n, hn, h⟩ := hsplit.1 k hk
    exact Complex.norm_eq_one_of_pow_eq_one h hn.ne'

end GlobalTheory.FinZeta.LevelOff

end
