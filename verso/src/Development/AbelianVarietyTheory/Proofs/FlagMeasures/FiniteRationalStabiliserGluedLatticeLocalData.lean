import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometriesFixingBothFramesStabilizingLatti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUnitaryAndFixesFramesOfMemComplementUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetNeOfTotPos
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabYFin

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt

/- English proof (translation)
Introduce `x hx hx0`. Establish `hdet0 : (ZhatL F F').det ≠ 0` using `Formalism.L2.SG.Pf.Cnt.R1.det_ne_of_totPos D (ZhatL F F') hTP`. Establish `hdet : (ZhatOM (Zhat F.fl F'.fl)).det ≠ 0`. Establish `e : ZhatOM (Zhat F.fl F'.fl) = Zhat F.fl F'.fl * Matrix.diagonal (fun b : Fin (D.R.rS + 1) => ((-1 : D.host.E) ^ (D.R.rS - b.val)))`. Use extensionality with `a b`.

Simplify using `[ZhatOM, Matrix.mul_diagonal, mul_comm]`. Rewrite using `[e, Matrix.det_mul, Matrix.det_diagonal]`. Conclude with `mul_ne_zero hdet0 (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (by norm_num))`. Distinguish the cases in `hxX : x ∈ Xsp F`. Conclude with `absurd (GlobalTheory.ComplPos.eq_zero_of_mem_X F.fl F'.fl hdet hxX (GlobalTheory.ComplPos.mem_orth_right hx)) hx0`.

Establish `hT : 0 < Tu D u` using `(D.mem u).A.T_prime.pos`. Conclude with `GlobalTheory.LoopC.PerpPos.trace_pos_perp D (Tu D u) F hT x (GlobalTheory.ComplPos.mem_orth_left hx) hxX`.
-/
theorem pos_compl (D : D7) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hTP : TotPos (Gval F F')) :
    ∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x) := by
  intro x hx hx0
  have hdet0 : (ZhatL F F').det ≠ 0 := Formalism.L2.SG.Pf.Cnt.R1.det_ne_of_totPos D (ZhatL F F') hTP
  have hdet : (ZhatOM (Zhat F.fl F'.fl)).det ≠ 0 := by
    have e : ZhatOM (Zhat F.fl F'.fl) = Zhat F.fl F'.fl *
        Matrix.diagonal (fun b : Fin (D.R.rS + 1) => ((-1 : D.host.E) ^ (D.R.rS - b.val))) := by
      ext a b
      simp [ZhatOM, Matrix.mul_diagonal, mul_comm]
    rw [e, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero hdet0 (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (by norm_num))
  by_cases hxX : x ∈ Xsp F
  · exact absurd (GlobalTheory.ComplPos.eq_zero_of_mem_X F.fl F'.fl hdet hxX (GlobalTheory.ComplPos.mem_orth_right hx)) hx0
  · have hT : 0 < Tu D u := (D.mem u).A.T_prime.pos
    exact GlobalTheory.LoopC.PerpPos.trace_pos_perp D (Tu D u) F hT x (GlobalTheory.ComplPos.mem_orth_left hx) hxX

/- English proof (translation)
Introduce `x hx`. Establish `hU : ∀ a : Fin D.R.rS, (VS D).hT (frame F a.castSucc) w = 0`. Introduce `a`. Establish `hmem : frame F a.castSucc ∈ Xplus F ⊔ Xplus F'`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises.

Use `show F.fl.fvec a.castSucc ∈ F.fl.X ⊔ _`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Use `(Submodule.mem_iInf _).1 hw (frame F a.castSucc)` as an intermediate fact.

Conclude with `(Submodule.mem_iInf _).1 this hmem`. Establish `hX : (locH Z p).X (FP p).A.f = Submodule.span (D.s.atP p).Ep (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (frame F a.castSucc))`. Rewrite using `[show (locH Z p).X (FP p).A.f = Submodule.span (D.s.atP p).Ep (Set.range fun a : Fin D.R.rS => (FP p).A.f a.castSucc) from rfl, (hB p).1]`. Rewrite `hx` using `[hX]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Use `show LocFacts₂ Z.M p (baseChange₂ D p w) (frFac Z.δ p a.castSucc • baseChange₂ D p (frame F a.castSucc)) = 0`. Rewrite using `[LocFacts.localForm_smul_right, baseChangeAt_form Z.M p (Z.hcj p), brS, hU a, map_zero, mul_zero]`. Consider the case `zero => show LocFacts₂ Z.M p (baseChange₂ D p w) 0 = 0`.

Use `LocFacts.localForm_smul_right Z p 0 (baseChange₂ D p w) 0` as an intermediate fact. Rewrite `this` using `[zero_smul]`. Rewrite using `[this, map_zero, zero_mul]`. Consider the case `add x y _ _ hx hy => show LocFacts₂ Z.M p (baseChange₂ D p w) (x + y) = 0`. Rewrite using `[LocFacts.localForm_add_right]`.

Conclude with `(congrArg₂ (· + ·) hx hy).trans (add_zero 0)`. Consider the case `smul c x _ hx => show LocFacts₂ Z.M p (baseChange₂ D p w) (c • x) = 0`. Rewrite using `[LocFacts.localForm_smul_right]`. Conclude with `(congrArg _ hx).trans (mul_zero _)`.
-/
theorem baseChange_mem_perp_sup (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (p : PlF D) (w : (VS D).V) (hw : w ∈ orth (VS D) (Xplus F ⊔ Xplus F')) :
    baseChange₂ D p w ∈ (locH Z p).perp ((locH Z p).X (FP p).A.f) := by
  intro x hx
  have hU : ∀ a : Fin D.R.rS, (VS D).hT (frame F a.castSucc) w = 0 := by
    intro a
    have hmem : frame F a.castSucc ∈ Xplus F ⊔ Xplus F' := by
      apply Submodule.mem_sup_left
      show F.fl.fvec a.castSucc ∈ F.fl.X ⊔ _
      apply Submodule.mem_sup_left
      simp only [FlagG.fvec, Fin.snoc_castSucc]
      exact Submodule.subset_span ⟨a, rfl⟩
    have := (Submodule.mem_iInf _).1 hw (frame F a.castSucc)
    exact (Submodule.mem_iInf _).1 this hmem
  have hX : (locH Z p).X (FP p).A.f = Submodule.span (D.s.atP p).Ep
      (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (frame F a.castSucc)) := by
    rw [show (locH Z p).X (FP p).A.f = Submodule.span (D.s.atP p).Ep (Set.range fun a : Fin D.R.rS => (FP p).A.f a.castSucc) from rfl,
      (hB p).1]
  rw [hX] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    show LocFacts₂ Z.M p (baseChange₂ D p w) (frFac Z.δ p a.castSucc • baseChange₂ D p (frame F a.castSucc)) = 0
    rw [LocFacts.localForm_smul_right, baseChangeAt_form Z.M p (Z.hcj p), brS, hU a, map_zero, mul_zero]
  | zero =>
    show LocFacts₂ Z.M p (baseChange₂ D p w) 0 = 0
    have := LocFacts.localForm_smul_right Z p 0 (baseChange₂ D p w) 0
    rw [zero_smul] at this
    rw [this, map_zero, zero_mul]
  | add x y _ _ hx hy =>
    show LocFacts₂ Z.M p (baseChange₂ D p w) (x + y) = 0
    rw [LocFacts.localForm_add_right]
    exact (congrArg₂ (· + ·) hx hy).trans (add_zero 0)
  | smul c x _ hx =>
    show LocFacts₂ Z.M p (baseChange₂ D p w) (c • x) = 0
    rw [LocFacts.localForm_smul_right]
    exact (congrArg _ hx).trans (mul_zero _)

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `v _`. Take `⟨d, hd0, hd⟩` from `h v`. Use `Submodule.smul_mem (Submodule.span E (N : Set V)) (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span hd)` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul E d v, inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)]`. Then use the resulting hypothesis.
-/
theorem span_top_of_mul {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V)
    (h : ∀ v : V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ N) : Submodule.span E (N : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨d, hd0, hd⟩ := h v
  have := Submodule.smul_mem (Submodule.span E (N : Set V)) (algebraMap (𝓞 E) E d)⁻¹
    (Submodule.subset_span hd)
  rwa [← algebraMap_smul E d v, inv_smul_smul₀
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at this

/- English proof (translation)
Set `Φ : V →ₗ[𝓞 E] (s → E)` to `LinearMap.pi fun l => ((hT l.1).restrictScalars (𝓞 E))`. Establish `hΦ : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Apply `hnd.2 y` to reduce the goal to its premises.

Introduce `v`. Establish `hv : v ∈ Submodule.span E (s : Set V)` using `by rw [hs]; trivial`. Use `Submodule.span_induction (p := fun v _ => hT v y = 0) ?_ ?_ ?_ ?_ hv` and prove the remaining obligations. Introduce `l hl`. Conclude with `congrFun hy ⟨l, hl⟩`.

Simplify using the standard rewrite rules. Introduce `a c _ _ ha hc`. Rewrite using `[map_add, LinearMap.add_apply, ha, hc, add_zero]`. Introduce `e a _ ha`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]`.

Apply `Submodule.fg_of_fg_map_injective Φ hΦ` to reduce the goal to its premises. Set `P : Submodule (𝓞 E) (s → E)` to `LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft s)`. Establish `hP : P.FG` using `Module.Finite.iff_fg.mp inferInstance`. Use `hP.of_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Establish `h1 : ∀ l : s, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = hT l.1 w` using `fun l => Submodule.mem_one.1 (hΘ w hw l.1 l.2)`. Use `choose o ho using h1`. Conclude with `⟨o, funext fun l => ho l⟩`.
-/
theorem fg_of_int {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (hT : V →ₗ⋆[E] V →ₗ[E] E) (hnd : hT.Nondegenerate)
    (s : Finset V) (hs : Submodule.span E (s : Set V) = ⊤) (Θ : Submodule (𝓞 E) V)
    (hΘ : ∀ w ∈ Θ, ∀ l ∈ s, hT l w ∈ (1 : Submodule (𝓞 E) E)) : Θ.FG := by
  let Φ : V →ₗ[𝓞 E] (s → E) := LinearMap.pi fun l => ((hT l.1).restrictScalars (𝓞 E))
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd.2 y
    intro v
    have hv : v ∈ Submodule.span E (s : Set V) := by rw [hs]; trivial
    refine Submodule.span_induction (p := fun v _ => hT v y = 0) ?_ ?_ ?_ ?_ hv
    · intro l hl
      exact congrFun hy ⟨l, hl⟩
    · simp
    · intro a c _ _ ha hc
      rw [map_add, LinearMap.add_apply, ha, hc, add_zero]
    · intro e a _ ha
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
  apply Submodule.fg_of_fg_map_injective Φ hΦ
  let P : Submodule (𝓞 E) (s → E) := LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft s)
  have hP : P.FG := Module.Finite.iff_fg.mp inferInstance
  refine hP.of_le ?_
  rintro _ ⟨w, hw, rfl⟩
  have h1 : ∀ l : s, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = hT l.1 w := fun l =>
    Submodule.mem_one.1 (hΘ w hw l.1 l.2)
  choose o ho using h1
  exact ⟨o, funext fun l => ho l⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D Z FP u u' F G F' G' P d0 _hk hB _hS hTP Λ y _hGl hΛ`. Establish `hBased : Based Z FP (Tu D u) (Tu D u') F F'` using `hB.1`. Use `set U : Submodule D.host.E (VS D).V := Xplus F ⊔ Xplus F' with hUdef`. Use `set W : Submodule D.host.E (VS D).V := orth (VS D) U with hWdef`. Establish `hpos : ∀ x ∈ W, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)` using `pos_compl D u u' F F' hTP`.

Establish `memW : ∀ v, v ∈ W ↔ ∀ x ∈ U, (VS D).hT x v = 0` using `fun v => by`. Simplify using `[hWdef, orth, Submodule.mem_iInf]`. Establish `hdisj : U ⊓ W = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨hxU, hxW⟩`.

Assume the negation of the conclusion as `hx0`. Use `hpos x hxW hx0` as an intermediate fact. Rewrite `this` using `[(memW x).1 hxW x hxU]`. Simplify using `at this`. Establish `hsup : U ⊔ W = ⊤`.

Set `b` to `Module.finBasis D.host.E U`. Set `φ : (VS D).V →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E)` to `LinearMap.pi fun i => (VS D).hT (b i : (VS D).V)`. Establish `hker : LinearMap.ker φ ≤ W`. Introduce `y hy`. Rewrite using `[memW]`.

Introduce `x hx`. Establish `hy' : ∀ i, (VS D).hT (b i : (VS D).V) y = 0` using `fun i => congrFun (LinearMap.mem_ker.1 hy) i`. Establish `hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : (VS D).V)`. Use `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`.

Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Rewrite using `[hx', map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy' i, smul_zero]`.

Establish `h1` using `LinearMap.finrank_range_add_finrank_ker φ`. Establish `h2 : Module.finrank D.host.E (LinearMap.range φ) ≤ Module.finrank D.host.E U`. Use `(Submodule.finrank_le _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h3` using `Submodule.finrank_mono hker`.

Establish `h4` using `Submodule.finrank_sup_add_finrank_inf_eq U W`. Rewrite `h4` using `[hdisj, finrank_bot]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Establish `h5` using `Submodule.finrank_le (U ⊔ W)`. Use linear arithmetic over natural numbers and integers.

Establish `hΛlat : Submodule.IsLattice D.host.E Λ` using `hΛ.1`. Establish `hmul : ∀ v : (VS D).V, ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ d • v ∈ Λ` using `fun v => by`. Establish `hv : v ∈ Submodule.span D.host.E (Λ : Set (VS D).V)` using `by rw [hΛlat.span_eq_top]; trivial`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E _ v hv`. Rewrite `ht` using `[Submodule.span_eq]`.

Conclude with `⟨t, nonZeroDivisors.ne_zero t.2, ht⟩`. Set `ΛW : LV D` to `Λ ⊓ W.restrictScalars (𝓞 D.host.E)`. Set `ΛU : LV D` to `Λ ⊓ U.restrictScalars (𝓞 D.host.E)`. Establish `hmul2 : ∀ v : (VS D).V, ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ d • v ∈ ΛW ⊔ ΛU`. Introduce `v`.

Establish `hv : v ∈ U ⊔ W` using `by rw [hsup]; trivial`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hv`. Take `⟨d1, hd1, ha1⟩` from `hmul a`. Take `⟨d2, hd2, hb2⟩` from `hmul b`. Use `⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `add_mem (Submodule.mem_sup_right ⟨?_, ?_⟩) (Submodule.mem_sup_left ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `Λ.smul_mem d2 ha1`. Conclude with `U.smul_of_tower_mem _ ha`.

Rewrite using `[mul_smul]`. Conclude with `Λ.smul_mem d1 hb2`. Conclude with `W.smul_of_tower_mem _ hb`. Set `Θs : Set (VS D).V` to `{w | ∃ hw : w ∈ W, ∀ p, (locH Z p).mkW (FP p).A.f ⟨baseChange₂ D p w, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p w hw⟩ ∈ (y p).L}`. Establish `hΛW : ∀ w ∈ Λ, w ∈ W → w ∈ Θs`.

Introduce `w hwΛ hw`. Use `⟨hw, fun p => ?_⟩` and prove the remaining obligations. Use `((Formalism.L2.SG.GoodFamilyMass.lset_term (hΛ.2 p).1).1 _).2 ?_` and prove the remaining obligations. Conclude with `⟨⟨baseChange₂ D p w, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p w hw⟩, Submodule.subset_span ⟨w, hwΛ, rfl⟩, rfl⟩`. Establish `hint : ∀ w ∈ Θs, ∀ l ∈ Λ, l ∈ W → (VS D).hT l w ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)`.

Introduce and unpack `w ⟨hw, hwL⟩ l hlΛ hl`. Establish `hlL` using `(hΛW l hlΛ hl).2`. Use `DualityBasisChange.locGlobIntE D _ fun p => ?_` and prove the remaining obligations. Establish `hf` using `baseChangeAt_form Z.M p (Z.hcj p) w l`. Rewrite `hf` using `[brS]`.

Rewrite using `[← hf, ← (Z.agree p).2.2.2.1]`. Conclude with `(((y p).hL.2.1 ⟨baseChange₂ D p w, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p w hw⟩).1 (hwL p)) ⟨baseChange₂ D p l, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p l hl⟩ (hlL p)`. Set `Θ : LV D` to `Submodule.span (𝓞 D.host.E) Θs`. Establish `hΛ1fg : (ΛW ⊔ ΛU).FG` using `(hΛlat.fg.of_le inf_le_left).sup (hΛlat.fg.of_le inf_le_left)`. Take `⟨s, hs⟩` from `hΛ1fg`.

Establish `hsE : Submodule.span D.host.E (s : Set (VS D).V) = ⊤`. Rewrite using `[← Submodule.span_span_of_tower (𝓞 D.host.E) D.host.E, hs]`. Conclude with `span_top_of_mul _ hmul2`. Establish `hΘfg : Θ.FG`. Use `fg_of_int (VS D).hT (VS D).nondeg s hsE Θ fun w hwΘ l hl => ?_` and prove the remaining obligations.

Establish `hl1 : l ∈ ΛW ⊔ ΛU` using `hs ▸ Submodule.subset_span hl`. Proceed by induction on `hwΘ using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hl1`. Rewrite using `[map_add, LinearMap.add_apply]`.

Use `add_mem (hint w hw a ha.1 ha.2) ?_` and prove the remaining obligations. Rewrite using `[(memW w).1 hw.1 b hb.2]`. Conclude with `zero_mem _`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add a c _ _ ha hc => rw [map_add]`. Conclude with `add_mem ha hc`. Consider the case `smul o a _ ha`. Rewrite using `[← algebraMap_smul D.host.E o a, map_smul, smul_eq_mul]`. Conclude with `Submodule.mul_mem_mul (Submodule.mem_one.2 ⟨o, rfl⟩) ha |> fun h => by simpa using h`.

Set `Λ₀ : LV D` to `Θ ⊔ ΛU`. Establish `hΛ₀ : Submodule.IsLattice D.host.E Λ₀`. Use `⟨hΘfg.sup (hΛlat.fg.of_le inf_le_left), span_top_of_mul _ fun v => ?_⟩` and prove the remaining obligations. Take `⟨d, hd0, hd⟩` from `hmul2 v`. Establish `hle : ΛW ⊔ ΛU ≤ Λ₀` using `sup_le (fun x hx => Submodule.mem_sup_left (Submodule.subset_span (hΛW x hx.1 hx.2))) le_sup_right`.

Conclude with `⟨d, hd0, hle hd⟩`. Use `(GlobalTheory.StabFin.finite_of_fix (VS D).hT U hpos Λ₀ hΛ₀).subset ?_` and prove the remaining obligations. Introduce and unpack `h ⟨hh, hm⟩`. Establish `hfixU : ∀ x ∈ U, h x = x`. Establish `key : ∀ {T0 : D.host.E} (G0 : LFlag (VS D) D.R.rS T0), (∀ a, h (frame G0 a) = frame G0 a) → Xplus G0 ≤ LinearMap.ker ((h : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id)`.

Introduce `T0 G0 hG`. Establish `he : ∀ i, h (G0.fl.e i) = G0.fl.e i` using `fun i => by`. Use `hG (Fin.castSucc i)` as an intermediate fact. Simplify `this` using `[frame, FlagG.fvec]`. Establish `hz : h G0.fl.z = G0.fl.z`.

Use `hG (Fin.last _)` as an intermediate fact. Simplify `this` using `[frame, FlagG.fvec]`. Use `show Submodule.span D.host.E (Set.range G0.fl.e) ⊔ Submodule.span D.host.E {G0.fl.z} ≤ _`. Use `sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Simplify using `[he i]`. Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Simplify using `[hz]`.

Introduce `x hx`. Use `(sup_le (key F hh.2.1) (key F' hh.2.2)) hx` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Conclude with `this`. Establish `hWiff : ∀ v, h v ∈ W ↔ v ∈ W`.

Introduce `v`. Rewrite using `[memW, memW]`. Use `forall₂_congr fun x hx => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← hfixU x hx]`. Rewrite using `[hh.1 x v]`.

Establish `hΘiff : ∀ v, h v ∈ Θs ↔ v ∈ Θs`. Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hw', hL'⟩`. Establish `hw` using `(hWiff v).1 hw'`.

Use `⟨hw, fun p => ?_⟩` and prove the remaining obligations. Take `⟨g', hE, hMv⟩` from `hm p`. Conclude with `(hMv.1 ⟨baseChange₂ D p v, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p v hw⟩ ⟨baseChange₂ D p (h v), baseChange_mem_perp_sup D Z FP _ _ F F' hBased p (h v) hw'⟩ (hE v).symm).2 (hL' p)`. Introduce and unpack `⟨hw, hL⟩`. Establish `hw'` using `(hWiff v).2 hw`.

Use `⟨hw', fun p => ?_⟩` and prove the remaining obligations. Take `⟨g', hE, hMv⟩` from `hm p`. Conclude with `(hMv.1 ⟨baseChange₂ D p v, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p v hw⟩ ⟨baseChange₂ D p (h v), baseChange_mem_perp_sup D Z FP _ _ F F' hBased p (h v) hw'⟩ (hE v).symm).1 (hL p)`. Establish `himg : (h : (VS D).V → (VS D).V) '' Θs = Θs`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(hΘiff x).2 hx`. Introduce `hv`. Use `⟨h.symm v, (hΘiff _).1 ?_, h.apply_symm_apply v⟩` and prove the remaining obligations.

Rewrite using `[h.apply_symm_apply]` and apply the resulting hypothesis. Establish `hU' : Submodule.map ((h : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) ΛU = ΛU`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩ show h x ∈ ΛU`. Rewrite using `[hfixU x hx.2]`.

Conclude with `hx`. Introduce `x hx`. Conclude with `⟨x, hx, hfixU x hx.2⟩`. Use `⟨hh.1, hfixU, ?_⟩` and prove the remaining obligations. Use `show Submodule.map ((h : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) (Θ ⊔ ΛU) = Θ ⊔ ΛU`.

Rewrite using `[Submodule.map_sup, hU', Submodule.map_span]`. Use `congr 2`.
-/
theorem stabY_finite : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → TotPos (Gval F F') → ∀ (Λ : LV D) (y : Dat Z FP), Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') → Λ ∈ globSet G G' y → (stabY F F' y).Finite := by
  intro D Z FP u u' F G F' G' P d0 _hk hB _hS hTP Λ y _hGl hΛ
  have hBased : Based Z FP (Tu D u) (Tu D u') F F' := hB.1
  set U : Submodule D.host.E (VS D).V := Xplus F ⊔ Xplus F' with hUdef
  set W : Submodule D.host.E (VS D).V := orth (VS D) U with hWdef
  have hpos : ∀ x ∈ W, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x) := pos_compl D u u' F F' hTP
  have memW : ∀ v, v ∈ W ↔ ∀ x ∈ U, (VS D).hT x v = 0 := fun v => by
    simp [hWdef, orth, Submodule.mem_iInf]

  have hdisj : U ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxW⟩
    by_contra hx0
    have := hpos x hxW hx0
    rw [(memW x).1 hxW x hxU] at this
    simp at this
  have hsup : U ⊔ W = ⊤ := by
    let b := Module.finBasis D.host.E U
    let φ : (VS D).V →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E) :=
      LinearMap.pi fun i => (VS D).hT (b i : (VS D).V)
    have hker : LinearMap.ker φ ≤ W := by
      intro y hy
      rw [memW]
      intro x hx
      have hy' : ∀ i, (VS D).hT (b i : (VS D).V) y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : (VS D).V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hx', map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy' i, smul_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank D.host.E (LinearMap.range φ) ≤ Module.finrank D.host.E U := by
      refine (Submodule.finrank_le _).trans ?_
      simp
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hdisj, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    have h5 := Submodule.finrank_le (U ⊔ W)
    omega
  have hΛlat : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hmul : ∀ v : (VS D).V, ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ d • v ∈ Λ := fun v => by
    have hv : v ∈ Submodule.span D.host.E (Λ : Set (VS D).V) := by rw [hΛlat.span_eq_top]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 D.host.E)) D.host.E _ v hv
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

  let ΛW : LV D := Λ ⊓ W.restrictScalars (𝓞 D.host.E)
  let ΛU : LV D := Λ ⊓ U.restrictScalars (𝓞 D.host.E)
  have hmul2 : ∀ v : (VS D).V, ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ d • v ∈ ΛW ⊔ ΛU := by
    intro v
    have hv : v ∈ U ⊔ W := by rw [hsup]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨d1, hd1, ha1⟩ := hmul a
    obtain ⟨d2, hd2, hb2⟩ := hmul b
    refine ⟨d1 * d2, mul_ne_zero hd1 hd2, ?_⟩
    rw [smul_add]
    refine add_mem (Submodule.mem_sup_right ⟨?_, ?_⟩) (Submodule.mem_sup_left ⟨?_, ?_⟩)
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem d2 ha1
    · exact U.smul_of_tower_mem _ ha
    · rw [mul_smul]; exact Λ.smul_mem d1 hb2
    · exact W.smul_of_tower_mem _ hb

  let Θs : Set (VS D).V := {w | ∃ hw : w ∈ W, ∀ p, (locH Z p).mkW (FP p).A.f
    ⟨baseChange₂ D p w, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p w hw⟩ ∈ (y p).L}
  have hΛW : ∀ w ∈ Λ, w ∈ W → w ∈ Θs := by
    intro w hwΛ hw
    refine ⟨hw, fun p => ?_⟩
    refine ((Formalism.L2.SG.GoodFamilyMass.lset_term (hΛ.2 p).1).1 _).2 ?_
    exact ⟨⟨baseChange₂ D p w, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p w hw⟩, Submodule.subset_span ⟨w, hwΛ, rfl⟩, rfl⟩
  have hint : ∀ w ∈ Θs, ∀ l ∈ Λ, l ∈ W → (VS D).hT l w ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rintro w ⟨hw, hwL⟩ l hlΛ hl
    have hlL := (hΛW l hlΛ hl).2
    refine DualityBasisChange.locGlobIntE D _ fun p => ?_
    have hf := baseChangeAt_form Z.M p (Z.hcj p) w l
    rw [brS] at hf
    rw [← hf, ← (Z.agree p).2.2.2.1]
    exact (((y p).hL.2.1 ⟨baseChange₂ D p w, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p w hw⟩).1 (hwL p))
      ⟨baseChange₂ D p l, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p l hl⟩ (hlL p)
  let Θ : LV D := Submodule.span (𝓞 D.host.E) Θs

  have hΛ1fg : (ΛW ⊔ ΛU).FG := (hΛlat.fg.of_le inf_le_left).sup (hΛlat.fg.of_le inf_le_left)
  obtain ⟨s, hs⟩ := hΛ1fg
  have hsE : Submodule.span D.host.E (s : Set (VS D).V) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 D.host.E) D.host.E, hs]
    exact span_top_of_mul _ hmul2
  have hΘfg : Θ.FG := by
    refine fg_of_int (VS D).hT (VS D).nondeg s hsE Θ fun w hwΘ l hl => ?_
    have hl1 : l ∈ ΛW ⊔ ΛU := hs ▸ Submodule.subset_span hl
    induction hwΘ using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hl1
      rw [map_add, LinearMap.add_apply]
      refine add_mem (hint w hw a ha.1 ha.2) ?_
      rw [(memW w).1 hw.1 b hb.2]
      exact zero_mem _
    | zero => rw [map_zero]; exact zero_mem _
    | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
    | smul o a _ ha =>
      rw [← algebraMap_smul D.host.E o a, map_smul, smul_eq_mul]
      exact Submodule.mul_mem_mul (Submodule.mem_one.2 ⟨o, rfl⟩) ha |> fun h => by simpa using h

  let Λ₀ : LV D := Θ ⊔ ΛU
  have hΛ₀ : Submodule.IsLattice D.host.E Λ₀ := by
    refine ⟨hΘfg.sup (hΛlat.fg.of_le inf_le_left), span_top_of_mul _ fun v => ?_⟩
    obtain ⟨d, hd0, hd⟩ := hmul2 v
    have hle : ΛW ⊔ ΛU ≤ Λ₀ :=
      sup_le (fun x hx => Submodule.mem_sup_left (Submodule.subset_span (hΛW x hx.1 hx.2))) le_sup_right
    exact ⟨d, hd0, hle hd⟩
  refine (GlobalTheory.StabFin.finite_of_fix (VS D).hT U hpos Λ₀ hΛ₀).subset ?_
  rintro h ⟨hh, hm⟩

  have hfixU : ∀ x ∈ U, h x = x := by
    have key : ∀ {T0 : D.host.E} (G0 : LFlag (VS D) D.R.rS T0), (∀ a, h (frame G0 a) = frame G0 a) →
        Xplus G0 ≤ LinearMap.ker ((h : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id) := by
      intro T0 G0 hG
      have he : ∀ i, h (G0.fl.e i) = G0.fl.e i := fun i => by
        have := hG (Fin.castSucc i)
        simpa [frame, FlagG.fvec] using this
      have hz : h G0.fl.z = G0.fl.z := by
        have := hG (Fin.last _)
        simpa [frame, FlagG.fvec] using this
      show Submodule.span D.host.E (Set.range G0.fl.e) ⊔ Submodule.span D.host.E {G0.fl.z} ≤ _
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨i, rfl⟩
        simp [he i]
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp [hz]
    intro x hx
    have := (sup_le (key F hh.2.1) (key F' hh.2.2)) hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have hWiff : ∀ v, h v ∈ W ↔ v ∈ W := by
    intro v
    rw [memW, memW]
    refine forall₂_congr fun x hx => ?_
    conv_lhs => rw [← hfixU x hx]
    rw [hh.1 x v]
  have hΘiff : ∀ v, h v ∈ Θs ↔ v ∈ Θs := by
    intro v
    constructor
    · rintro ⟨hw', hL'⟩
      have hw := (hWiff v).1 hw'
      refine ⟨hw, fun p => ?_⟩
      obtain ⟨g', hE, hMv⟩ := hm p
      exact (hMv.1 ⟨baseChange₂ D p v, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p v hw⟩
        ⟨baseChange₂ D p (h v), baseChange_mem_perp_sup D Z FP _ _ F F' hBased p (h v) hw'⟩ (hE v).symm).2 (hL' p)
    · rintro ⟨hw, hL⟩
      have hw' := (hWiff v).2 hw
      refine ⟨hw', fun p => ?_⟩
      obtain ⟨g', hE, hMv⟩ := hm p
      exact (hMv.1 ⟨baseChange₂ D p v, baseChange_mem_perp_sup D Z FP _ _ F F' hBased p v hw⟩
        ⟨baseChange₂ D p (h v), baseChange_mem_perp_sup D Z FP _ _ F F' hBased p (h v) hw'⟩ (hE v).symm).1 (hL p)
  have himg : (h : (VS D).V → (VS D).V) '' Θs = Θs := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hΘiff x).2 hx
    · intro hv
      refine ⟨h.symm v, (hΘiff _).1 ?_, h.apply_symm_apply v⟩
      rwa [h.apply_symm_apply]
  have hU' : Submodule.map ((h : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) ΛU = ΛU := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show h x ∈ ΛU
      rw [hfixU x hx.2]
      exact hx
    · intro x hx
      exact ⟨x, hx, hfixU x hx.2⟩
  refine ⟨hh.1, hfixU, ?_⟩
  show Submodule.map ((h : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) (Θ ⊔ ΛU) = Θ ⊔ ΛU
  rw [Submodule.map_sup, hU', Submodule.map_span]
  congr 2

end GlobalTheory.StabYFin
