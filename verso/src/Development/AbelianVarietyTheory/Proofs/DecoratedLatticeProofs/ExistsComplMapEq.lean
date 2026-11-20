import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSphGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousComplEquivSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

noncomputable section

namespace GlobalTheory.Core.Rk.SWQ.LatHalf

open scoped TensorProduct
open GlobalTheory.FinPl (latMul latV latA idAt MxAt)
open GlobalTheory.LFun (latAt IsFrameAt complMap)

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

/- English proof (translation)
Take `⟨s, hs⟩ : (I : Submodule (𝓞 E) E).FG` from `FractionalIdeal.fg_of_isNoetherianRing le_rfl I`. Establish `hne : s.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce and unpack `rfl`. Apply `hI` to reduce the goal to its premises.

Rewrite using `[← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]`. Simplify using the standard rewrite rules. Take `⟨a₀, ha₀, hmax⟩` from `s.exists_max_image (fun a => Valued.v (algebraMap E (w.adicCompletion E) a)) hne`. Establish `hle : ∀ a ∈ (I : Submodule (𝓞 E) E), Valued.v (algebraMap E (w.adicCompletion E) a) ≤ Valued.v (algebraMap E (w.adicCompletion E) a₀)`. Introduce `a ha`.

Rewrite `ha` using `[← hs]`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact hmax x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `(Valuation.map_add _ _ _).trans (max_le hx hy)`. Consider the case `smul r x _ hx`. Rewrite using `[Algebra.smul_def, map_mul, map_mul]`. Establish `hr : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1` using `GlobalTheory.AdeleBaseChange.algebraMap_int_mem r w`. Conclude with `(mul_le_mul_left hr _).trans (by rw [one_mul]; exact hx)`.

Establish `h0 : a₀ ≠ 0`. Introduce and unpack `rfl`. Apply `hI` to reduce the goal to its premises. Rewrite using `[← FractionalIdeal.coeToSubmodule_eq_bot, eq_bot_iff]`. Introduce `a ha`.

Use `hle a ha` as an intermediate fact. Simplify using `using this`. Establish `h0' : algebraMap E (w.adicCompletion E) a₀ ≠ 0` using `(map_ne_zero _).2 h0`. Use `⟨a₀, show a₀ ∈ (I : Submodule (𝓞 E) E) from hs ▸ Submodule.subset_span ha₀, h0, fun a ha => ⟨algebraMap E _ a / algebraMap E _ a₀, ?_, by field_simp⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Valued.v (algebraMap E (w.adicCompletion E) a / algebraMap E (w.adicCompletion E) a₀) ≤ 1`.

Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ (hle a ha) zero_le'`.
-/
theorem exists_gen {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ a₀ ∈ I, a₀ ≠ 0 ∧ ∀ a ∈ I, ∃ c ∈ Ov E w,
      algebraMap E (w.adicCompletion E) a = algebraMap E (w.adicCompletion E) a₀ * c := by
  obtain ⟨s, hs⟩ : (I : Submodule (𝓞 E) E).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]
    simp
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (algebraMap E (w.adicCompletion E) a)) hne
  have hle : ∀ a ∈ (I : Submodule (𝓞 E) E),
      Valued.v (algebraMap E (w.adicCompletion E) a) ≤ Valued.v (algebraMap E (w.adicCompletion E) a₀) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hmax x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul]
      have hr : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 :=
        GlobalTheory.AdeleBaseChange.algebraMap_int_mem r w
      exact (mul_le_mul_left hr _).trans (by rw [one_mul]; exact hx)
  have h0 : a₀ ≠ 0 := by
    rintro rfl
    apply hI
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, eq_bot_iff]
    intro a ha
    have := hle a ha
    simpa using this
  have h0' : algebraMap E (w.adicCompletion E) a₀ ≠ 0 := (map_ne_zero _).2 h0
  refine ⟨a₀, show a₀ ∈ (I : Submodule (𝓞 E) E) from hs ▸ Submodule.subset_span ha₀, h0, fun a ha =>
    ⟨algebraMap E _ a / algebraMap E _ a₀, ?_, by field_simp⟩⟩
  change Valued.v (algebraMap E (w.adicCompletion E) a / algebraMap E (w.adicCompletion E) a₀) ≤ 1
  rw [map_div₀]
  exact div_le_one_of_le₀ (hle a ha) zero_le'

/- English proof (translation)
Set `Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D)` to `AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (a * x i)))) fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add]; rfl`. Establish `hle : intAE D ≤ (latMul S 𝔞 L P).comap Φ`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, hγ, o, rfl⟩`. Use `AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v), fun v hv => by rw [map_mul, hβ v hv, mul_zero], a, ha, o • x, L.smul_mem o hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (a * x i))) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def, show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `e : (fun i => z * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i))) = Φ (finPart D z)`. Use function extensionality and compare the values at `fun i => GlobalTheory.LatticeStable.mul_pair_tmul D z β _`. Rewrite using `[e]`. Conclude with `hle hz`.
-/
theorem mul_mem_gen {S : HSp D} {𝔞 : Set D.host.E} {L : Lat S} {P : FinPl D → Prop} {z : AE D}
    (hz : finPart D z ∈ intAE D) {β : Af D.host.F} (hβi : β ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F)
    (hβ : ∀ v, ¬ P v → evalV D.host.F v β = 0) {a : D.host.E} (ha : a ∈ 𝔞) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    (fun i => z * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i))) ∈ latMul S 𝔞 L P := by
  let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (a * x i))))
      fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add]; rfl
  have hle : intAE D ≤ (latMul S 𝔞 L P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, o, rfl⟩
    refine AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v),
      fun v hv => by rw [map_mul, hβ v hv, mul_zero], a, ha, o • x, L.smul_mem o hx, ?_⟩
    funext i
    change GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (a * x i))) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
      show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]
    congr 1
    ring
  have e : (fun i => z * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i))) = Φ (finPart D z) :=
    funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D z β _
  rw [e]
  exact hle hz

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cw_tmul (h : w.under (𝓞 D.host.F) = q) (α : Af D.host.F) (x : D.host.E) :
    cw h (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = complMap h (evalV D.host.F q α) * algebraMap D.host.E _ x := rfl

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hαi, -, a, ha, x, hx, rfl⟩` from `hy`. Take `⟨c, hc, e⟩` from `h𝔞 a ha`. Use `⟨_, (latAt w L).smul_mem ⟨complMap h (evalV D.host.F q α) * c, mul_mem (GlobalTheory.LFun.complMap_mem h (hαi q)) hc⟩ (Submodule.subset_span ⟨x, hx, rfl⟩), fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[cw_tmul, map_mul, e]`. Express the relevant statement in the definitionally equal form `_ = a₀ * (complMap h (evalV D.host.F q α) * c * algebraMap D.host.E _ (x i))`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, zero_mem _, fun i => by simp⟩`. Consider the case `add y y' _ _ hy hy'`.

Take `⟨z, hz, e⟩` from `hy`. Take `⟨z', hz', e'⟩` from `hy'`. Conclude with `⟨z + z', add_mem hz hz', fun i => by simp [e, e', mul_add]⟩`. Consider the case `neg y _ hy`. Take `⟨z, hz, e⟩` from `hy`.

Conclude with `⟨-z, neg_mem hz, fun i => by simp [e]⟩`.
-/
theorem cw_mem (h : w.under (𝓞 D.host.F) = q) {S : HSp D} {𝔞 : Set D.host.E} {L : Lat S} {P : FinPl D → Prop}
    {a₀ : w.adicCompletion D.host.E} (h𝔞 : ∀ a ∈ 𝔞, ∃ c ∈ Ov D.host.E w, algebraMap D.host.E _ a = a₀ * c)
    {y : Fin S.rank → AE D} (hy : y ∈ latMul S 𝔞 L P) : ∃ z ∈ latAt w L, ∀ i, cw h (y i) = a₀ * z i := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
    obtain ⟨c, hc, e⟩ := h𝔞 a ha
    refine ⟨_, (latAt w L).smul_mem ⟨complMap h (evalV D.host.F q α) * c,
      mul_mem (GlobalTheory.LFun.complMap_mem h (hαi q)) hc⟩ (Submodule.subset_span ⟨x, hx, rfl⟩), fun i => ?_⟩
    rw [cw_tmul, map_mul, e]
    change _ = a₀ * (complMap h (evalV D.host.F q α) * c * algebraMap D.host.E _ (x i))
    ring
  | zero => exact ⟨0, zero_mem _, fun i => by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨z, hz, e⟩ := hy
    obtain ⟨z', hz', e'⟩ := hy'
    exact ⟨z + z', add_mem hz hz', fun i => by simp [e, e', mul_add]⟩
  | neg y _ hy =>
    obtain ⟨z, hz, e⟩ := hy
    exact ⟨-z, neg_mem hz, fun i => by simp [e]⟩

/- English proof (translation)
Take `⟨τ, rfl⟩` from `GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (isCMExt_host D) hs h`. Take `⟨ψ, h1, -, h3, -⟩` from `GlobalTheory.LFun.SplitChart.exists_equiv_complMap τ h`. Take `⟨α, rfl⟩` from `ψ.surjective c`. Conclude with `⟨α, (GlobalTheory.LFun.SplitChart.map_mem_Ov_iff h3).1 hc, (h1 α).symm⟩`.
-/
theorem exists_complMap_eq (h : w.under (𝓞 D.host.F) = q) (hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q)
    {c : w.adicCompletion D.host.E} (hc : c ∈ Ov D.host.E w) :
    ∃ α ∈ q.adicCompletionIntegers D.host.F, complMap h α = c := by
  obtain ⟨τ, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (isCMExt_host D) hs h
  obtain ⟨ψ, h1, -, h3, -⟩ := GlobalTheory.LFun.SplitChart.exists_equiv_complMap τ h
  obtain ⟨α, rfl⟩ := ψ.surjective c
  exact ⟨α, (GlobalTheory.LFun.SplitChart.map_mem_Ov_iff h3).1 hc, (h1 α).symm⟩

/- English proof (translation)
Introduce `_ hv` and use `evalV_singleFin_ne hv α`.
-/
theorem singleFin_supp (α : Fv D.host.F q) : ∀ v, ¬ v = q → evalV D.host.F v (singleFin q α) = 0 :=
  fun _ hv => evalV_singleFin_ne hv α

/- English proof (translation)
Establish `hint : finPart D (ι 1) ∈ intAE D` using `GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h4, h1, one_mul])`. Establish `key : ∀ c ∈ Ov D.host.E w, (fun i => ι (algebraMap D.host.E _ a₀ * (c * z i))) ∈ latMul S 𝔞 L (fun v => v = q)`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, hx, rfl⟩` from `hz`.

Introduce `c hc`. Take `⟨α, hα, rfl⟩` from `exists_complMap_eq h hs hc`. Establish `hαi : singleFin q α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F` using `fun v => by`. Distinguish the cases in `hv : v = q`. Rewrite using `[hv, evalV_singleFin_self]`.

Conclude with `hα`. Rewrite using `[singleFin_supp α v hv]`. Conclude with `zero_mem _`. Use `mul_mem_gen (P := fun v => v = q) hint hαi (singleFin_supp α) ha₀ hx using 2 with i` and compare the differences between its conclusion and the goal. Rewrite using `[mul_comm (ι 1), h4, cw_tmul, evalV_singleFin_self, (algebraMap D.host.E (w.adicCompletion D.host.E)).map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Introduce `c _`. Use `zero_mem (latMul S 𝔞 L (fun v => v = q)) using 2 with i` and compare the differences between its conclusion and the goal.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Introduce `c hc`. Use `add_mem (hx c hc) (hy c hc) using 2 with i` and compare the differences between its conclusion and the goal. Simplify using `[mul_add]`.

Consider the case `smul r x _ hx`. Introduce `c hc`. Use `hx (c * r) (mul_mem hc r.2) using 3 with i` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ * (c * ((r : w.adicCompletion D.host.E) * x i)) = _`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `using key 1 (one_mem _)`.
-/
theorem iota_mem (h : w.under (𝓞 D.host.F) = q) (hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q)
    {ι : w.adicCompletion D.host.E →+ AE D} (h1 : ∀ x, cw h (ι x) = x) (h4 : ∀ a x, a * ι x = ι (cw h a * x))
    {S : HSp D} {𝔞 : Set D.host.E} {L : Lat S} {a₀ : D.host.E} (ha₀ : a₀ ∈ 𝔞)
    {z : Fin S.rank → w.adicCompletion D.host.E} (hz : z ∈ latAt w L) :
    (fun i => ι (algebraMap D.host.E _ a₀ * z i)) ∈ latMul S 𝔞 L (fun v => v = q) := by
  have hint : finPart D (ι 1) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h4, h1, one_mul])
  have key : ∀ c ∈ Ov D.host.E w,
      (fun i => ι (algebraMap D.host.E _ a₀ * (c * z i))) ∈ latMul S 𝔞 L (fun v => v = q) := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      intro c hc
      obtain ⟨α, hα, rfl⟩ := exists_complMap_eq h hs hc
      have hαi : singleFin q α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := fun v => by
        by_cases hv : v = q
        · rw [hv, evalV_singleFin_self]; exact hα
        · rw [singleFin_supp α v hv]; exact zero_mem _
      convert mul_mem_gen (P := fun v => v = q) hint hαi (singleFin_supp α) ha₀ hx using 2 with i
      rw [mul_comm (ι 1), h4, cw_tmul, evalV_singleFin_self, (algebraMap D.host.E (w.adicCompletion D.host.E)).map_mul]
      congr 1
      ring
    | zero =>
      intro c _
      convert zero_mem (latMul S 𝔞 L (fun v => v = q)) using 2 with i
      simp
    | add x y _ _ hx hy =>
      intro c hc
      convert add_mem (hx c hc) (hy c hc) using 2 with i
      simp [mul_add]
    | smul r x _ hx =>
      intro c hc
      convert hx (c * r) (mul_mem hc r.2) using 3 with i
      change _ * (c * ((r : w.adicCompletion D.host.E) * x i)) = _
      ring
  simpa using key 1 (one_mem _)

end GlobalTheory.Core.Rk.SWQ.LatHalf

open GlobalTheory.Core.Rk.SWQ.LatHalf in

/- English proof (translation)
Introduce `D q w h hs S T LS LT hS hT a ha`. Take `⟨ι, -, h1, -, -, h4, h5, -, -⟩` from `GlobalTheory.Core.Rk.SplitIota.exists_iota D q w h hs`. Take `⟨e, ⟨⟨b₀, hb₀, -⟩, -⟩, -, -⟩` from `GlobalTheory.LFun.SplitChart.exists_isSplitChart (isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram T) hT.1.fg hT.1.span_eq_top h hs (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hT q)`. Use `clear e`. Take `⟨a₀, ha₀, h0, hgen⟩` from `exists_gen w D.host.AA (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)`.

Use `set π : w.adicCompletion D.host.E := algebraMap D.host.E _ a₀ with hπ`. Establish `hπ0 : π ≠ 0` using `(map_ne_zero _).2 h0`. Set `b : GL (Fin T.rank) (w.adicCompletion D.host.E)` to `⟨π • b₀.1, π⁻¹ • (b₀⁻¹).1, by`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hπ0, one_smul, Units.mul_inv], by`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hπ0, one_smul, Units.inv_mul]⟩`.

Establish `hb : (b⁻¹).1 = π⁻¹ • (b₀⁻¹).1` using `rfl`. Establish `hone : ∀ x ∈ ({1} : Set D.host.E), ∃ c ∈ Ov D.host.E w, algebraMap D.host.E (w.adicCompletion D.host.E) x = 1 * c`. Introduce and unpack `_ rfl`. Conclude with `⟨1, one_mem _, by simp⟩`. Use `⟨b, fun u hoff hc => ?_⟩` and prove the remaining obligations.

Establish `hu1 : ∀ i j, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * u i j = u i j` using `fun i j => (sub_eq_zero.1 (congrFun (congrFun hoff i) j)).symm`. Establish `hu : ∀ i j, u i j = ι (cw h (u i j))` using `fun i j => by conv_lhs => rw [← hu1, h5, hc, map_zero, map_zero, add_zero]`. Establish `hmv : ∀ (y : Fin S.rank → AE D) i, cw h ((u *ᵥ y) i) = (u.map (cw h) *ᵥ fun j => cw h (y j)) i` using `fun y i => RingHom.map_mulVec (cw h) u y i`. Rewrite using `[GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, hb]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, H⟩ i j`. Establish `hj : a.1 *ᵥ (Pi.single j 1) ∈ GlobalTheory.LFun.latAt w LS` using `(ha _).1 fun k => by`. Distinguish the cases in `e : k = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[e]`. Establish `hy` using `iota_mem h hs h1 h4 (𝔞 := {1}) rfl hj`. Take `⟨z, hz, e⟩` from `cw_mem h (a₀ := π) hgen (H _ hy)`. Establish `e' : u.map (cw h) *ᵥ (a.1 *ᵥ (Pi.single j 1)) = π • z`. Use function extensionality and compare the values at `k`.

Use `e k` as an intermediate fact. Rewrite `this` using `[hmv]`. Simplify using `only [h1, map_one, one_mul] at this`. Conclude with `this`. Establish `hz'` using `(hb₀ ((b₀⁻¹).1 *ᵥ z)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) i`.

Establish `: (π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ (Pi.single j 1) = (b₀⁻¹).1 *ᵥ z`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e', Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hπ0, one_smul]`. Rewrite `hz'` using `[← this, Matrix.mulVec_single_one]`. Conclude with `hz'`. Introduce `H`.

Use `⟨fun i j => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← hu1]`. Conclude with `Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.LatMem.tmul_mem_idAt (singleFin_supp 1) 1)`. Take `⟨z, hz, e⟩` from `cw_mem h hone hy`. Establish `hx` using `(ha ((a⁻¹).1 *ᵥ z)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])`.

Establish `hM` using `(hb₀ ((π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ ((a⁻¹).1 *ᵥ z))).1 fun i => sum_mem fun k _ => mul_mem (H i k) (hx k)`. Establish `e2 : b₀.1 *ᵥ ((π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ ((a⁻¹).1 *ᵥ z)) = π⁻¹ • (u.map (cw h) *ᵥ z)`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, Units.mul_inv, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite `hM` using `[e2]`. Use `(congrArg (· ∈ GlobalTheory.FinPl.latA T LT (fun v => v = q)) ?_).mpr (iota_mem h hs h1 h4 (𝔞 := {x | x ∈ D.host.AA}) ha₀ hM)` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Rewrite using `[← hπ, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hπ0]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [hu, mul_comm, h4, e, one_mul, mul_comm]`.
-/
theorem GlobalTheory.Core.Rk.SWQ.LatHalf.mem_latO_iff_intM : ∀ (D : D7) (q : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = q), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ a : GL (Fin S.rank) (w.adicCompletion D.host.E), GlobalTheory.LFun.IsFrameAt w LS a → ∃ b : GL (Fin T.rank) (w.adicCompletion D.host.E), ∀ u : WO S T, offM q u = 0 → (∀ i j, cw h (cA D (u i j)) = 0) → (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun v => v = q) ↔ IntM ((b⁻¹).1 * u.map (cw h) * a.1)) := by
  intro D q w h hs S T LS LT hS hT a ha
  obtain ⟨ι, -, h1, -, -, h4, h5, -, -⟩ := GlobalTheory.Core.Rk.SplitIota.exists_iota D q w h hs
  obtain ⟨e, ⟨⟨b₀, hb₀, -⟩, -⟩, -, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart (isCMExt_host D)
    (GlobalTheory.Doubling.isHermND_gram T) hT.1.fg hT.1.span_eq_top h hs
    (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hT q)
  clear e
  obtain ⟨a₀, ha₀, h0, hgen⟩ := exists_gen w D.host.AA (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)
  set π : w.adicCompletion D.host.E := algebraMap D.host.E _ a₀ with hπ
  have hπ0 : π ≠ 0 := (map_ne_zero _).2 h0
  let b : GL (Fin T.rank) (w.adicCompletion D.host.E) :=
    ⟨π • b₀.1, π⁻¹ • (b₀⁻¹).1, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hπ0, one_smul, Units.mul_inv], by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hπ0, one_smul, Units.inv_mul]⟩
  have hb : (b⁻¹).1 = π⁻¹ • (b₀⁻¹).1 := rfl
  have hone : ∀ x ∈ ({1} : Set D.host.E), ∃ c ∈ Ov D.host.E w,
      algebraMap D.host.E (w.adicCompletion D.host.E) x = 1 * c := by
    rintro _ rfl
    exact ⟨1, one_mem _, by simp⟩
  refine ⟨b, fun u hoff hc => ?_⟩
  have hu1 : ∀ i j, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) * u i j = u i j := fun i j =>
    (sub_eq_zero.1 (congrFun (congrFun hoff i) j)).symm
  have hu : ∀ i j, u i j = ι (cw h (u i j)) := fun i j => by
    conv_lhs => rw [← hu1, h5, hc, map_zero, map_zero, add_zero]
  have hmv : ∀ (y : Fin S.rank → AE D) i, cw h ((u *ᵥ y) i) = (u.map (cw h) *ᵥ fun j => cw h (y j)) i :=
    fun y i => RingHom.map_mulVec (cw h) u y i
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, hb]
  constructor
  · rintro ⟨-, H⟩ i j
    have hj : a.1 *ᵥ (Pi.single j 1) ∈ GlobalTheory.LFun.latAt w LS := (ha _).1 fun k => by
      by_cases e : k = j
      · subst e; simp
      · simp [e]
    have hy := iota_mem h hs h1 h4 (𝔞 := {1}) rfl hj
    obtain ⟨z, hz, e⟩ := cw_mem h (a₀ := π) hgen (H _ hy)
    have e' : u.map (cw h) *ᵥ (a.1 *ᵥ (Pi.single j 1)) = π • z := by
      funext k
      have := e k
      rw [hmv] at this
      simp only [h1, map_one, one_mul] at this
      exact this
    have hz' := (hb₀ ((b₀⁻¹).1 *ᵥ z)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) i
    have : (π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ (Pi.single j 1) = (b₀⁻¹).1 *ᵥ z := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e', Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
        inv_mul_cancel₀ hπ0, one_smul]
    rw [← this, Matrix.mulVec_single_one] at hz'
    exact hz'
  · intro H
    refine ⟨fun i j => ?_, fun y hy => ?_⟩
    · rw [← hu1]
      exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.LatMem.tmul_mem_idAt (singleFin_supp 1) 1)
    · obtain ⟨z, hz, e⟩ := cw_mem h hone hy
      have hx := (ha ((a⁻¹).1 *ᵥ z)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
      have hM := (hb₀ ((π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ ((a⁻¹).1 *ᵥ z))).1 fun i =>
        sum_mem fun k _ => mul_mem (H i k) (hx k)
      have e2 : b₀.1 *ᵥ ((π⁻¹ • (b₀⁻¹).1 * u.map (cw h) * a.1) *ᵥ ((a⁻¹).1 *ᵥ z)) = π⁻¹ • (u.map (cw h) *ᵥ z) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z, Units.mul_inv, Matrix.one_mulVec,
          Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e2] at hM
      refine (congrArg (· ∈ GlobalTheory.FinPl.latA T LT (fun v => v = q)) ?_).mpr
        (iota_mem h hs h1 h4 (𝔞 := {x | x ∈ D.host.AA}) ha₀ hM)
      funext i
      rw [← hπ, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hπ0]
      simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [hu, mul_comm, h4, e, one_mul, mul_comm]

end
