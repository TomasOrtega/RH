import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitSupportedRepFiniteUnitaryClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.ClassSumRat

variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)

/- English proof (translation)
Take `⟨x, rfl⟩` from `hx`. Take `⟨y, rfl⟩` from `hy`. Conclude with `⟨x + y, map_add _ _ _⟩`.
-/
theorem add_mem_range {k : ℕ} {x y : GA D (Wc D j) → ℂ} (hx : x ∈ Set.range (rdK rd hρ k)) (hy : y ∈ Set.range (rdK rd hρ k)) :
    x + y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact ⟨x + y, map_add _ _ _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, map_zero _⟩`.
-/
theorem zero_mem_range {k : ℕ} : (0 : GA D (Wc D j) → ℂ) ∈ Set.range (rdK rd hρ k) := ⟨0, map_zero _⟩

/- English proof (translation)
Take `⟨x, rfl⟩` from `hy`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, smul_zero]`. Conclude with `zero_mem_range hρ rd`. Consider the case `add x y hx hy => rw [map_add, smul_add]`.

Conclude with `add_mem_range hρ rd hx hy`. Consider the case `tmul a f => exact ⟨a ⊗ₜ (c • f), by rw [rdK_tmul, rdK_tmul, LinearMap.map_smulₛₗ, smul_comm]⟩`.
-/
theorem e_smul_mem_range {k : ℕ} (c : FractionRing (D.ntw.O i)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.e i b c • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem_range hρ rd
  | add x y hx hy => rw [map_add, smul_add]; exact add_mem_range hρ rd hx hy
  | tmul a f => exact ⟨a ⊗ₜ (c • f), by rw [rdK_tmul, rdK_tmul, LinearMap.map_smulₛₗ, smul_comm]⟩

/- English proof (translation)
Take `⟨p, d, hd, e⟩` from `D.ntw.Ok_gen i k a`. Generalize the expression as in `Polynomial.aeval (D.ntw.zk i k : D.ntw.Ok i k) p = u at e`. Establish `h1 : ρ.ek i b k a * ρ.eO i b d = ρ.eOk i b k u`. Rewrite using `[← hρ.ek_e i b k d]`. Conclude with `(map_mul (ρ.ek i b k) _ _).symm.trans (congrArg (ρ.ek i b k) e)`.

Establish `hd0 : ρ.eO i b d ≠ 0` using `fun h => hd (ρ.eO_injective i b (h.trans (map_zero _).symm))`. Establish `h2 : ρ.ek i b k a = ρ.e i b (algebraMap (D.ntw.O i) _ d)⁻¹ * ρ.eOk i b k u`. Rewrite using `[map_inv₀, ← h1, mul_comm (ρ.ek i b k a)]`. Conclude with `(inv_mul_cancel_left₀ hd0 _).symm`. Take `⟨x, rfl⟩` from `hy`.

Rewrite using `[h2, mul_smul]`. Conclude with `e_smul_mem_range hρ rd _ ⟨u • x, LinearMap.map_smulₛₗ _ _ _⟩`.
-/
theorem ek_smul_mem_range {k : ℕ} (a : FractionRing (D.ntw.Ok i k)) {y : GA D (Wc D j) → ℂ} (hy : y ∈ Set.range (rdK rd hρ k)) :
    ρ.ek i b k a • y ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨p, d, hd, e⟩ := D.ntw.Ok_gen i k a
  generalize Polynomial.aeval (D.ntw.zk i k : D.ntw.Ok i k) p = u at e
  have h1 : ρ.ek i b k a * ρ.eO i b d = ρ.eOk i b k u := by
    rw [← hρ.ek_e i b k d]
    exact (map_mul (ρ.ek i b k) _ _).symm.trans (congrArg (ρ.ek i b k) e)
  have hd0 : ρ.eO i b d ≠ 0 := fun h => hd (ρ.eO_injective i b (h.trans (map_zero _).symm))
  have h2 : ρ.ek i b k a = ρ.e i b (algebraMap (D.ntw.O i) _ d)⁻¹ * ρ.eOk i b k u := by
    rw [map_inv₀, ← h1, mul_comm (ρ.ek i b k a)]
    exact (inv_mul_cancel_left₀ hd0 _).symm
  obtain ⟨x, rfl⟩ := hy
  rw [h2, mul_smul]
  exact e_smul_mem_range hρ rd _ ⟨u • x, LinearMap.map_smulₛₗ _ _ _⟩

include hρ in

/- English proof (translation)
Take `⟨N₀, hN₀, hK⟩` from `GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS ((ρ.B i j b).levS t)`. Establish `hbad : 0 < ρ.bad i` using `Nat.pos_of_ne_zero (hρ.bad_ne i)`. Establish `hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ t` using `fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1`. Take `⟨h', ⟨hh', hs⟩, γ, k, e⟩` from `GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)`. Take `⟨-, e', P, hP, hoff, hsupp⟩` from `GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs`.

Use `⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩` and prove the remaining obligations. Rewrite using `[idem_eq hP]`. Conclude with `hsupp`.
-/
theorem exists_rep (t : Twist D Circle) (h : GA D (Vc D j)) : ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j))
    (κ : (ρ.B i j b).levJ t), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧
      SuppAt (idem s) (Vc D j) h' ∧
      finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (κ : Bridge.Gf (Vc D j)) := by
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS ((ρ.B i j b).levS t)
  have hbad : 0 < ρ.bad i := Nat.pos_of_ne_zero (hρ.bad_ne i)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ t :=
    fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1
  obtain ⟨h', ⟨hh', hs⟩, γ, k, e⟩ := GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  refine ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩
  rw [idem_eq hP]
  exact hsupp

/- English proof (translation)
Take `⟨ht, hadm, hval⟩` from `GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ`. Establish `h1` using `hR k Q ψ hψ hQ s h P hd ⟨1, GlobalTheory.SplitLinear.suppAt_one _ _, rfl⟩`. Rewrite `h1` using `[mul_one, GlobalTheory.TwTraceCx.gen_eq_smul (hρ.base i j b) ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)]`. Take `⟨u, hu⟩` from `hval (detRoot (Vc D j) h)`. Establish `hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi h : Circle) : ℂ) = ρ.ek i b k (algebraMap (D.ntw.Ok i k) _ u)` using `hu`.

Establish `h2` using `ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u)⁻¹ h1`. Rewrite `h2` using `[map_inv₀, ← hc, inv_smul_smul₀ (Circle.coe_ne_zero _)]`. Then use the resulting hypothesis.
-/
theorem series_datum (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {s h P}
    (hd : ρ.IsDatum i j b s h P) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h P ∈ Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have h1 := hR k Q ψ hψ hQ s h P hd ⟨1, GlobalTheory.SplitLinear.suppAt_one _ _, rfl⟩
  rw [mul_one, GlobalTheory.TwTraceCx.gen_eq_smul (hρ.base i j b) ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)] at h1
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) h)
  have hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi h : Circle) : ℂ) = ρ.ek i b k (algebraMap (D.ntw.Ok i k) _ u) := hu
  have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u)⁻¹ h1
  rwa [map_inv₀, ← hc, inv_smul_smul₀ (Circle.coe_ne_zero _)] at h2

/- English proof (translation)
Take `⟨ht, hadm, -⟩` from `GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ`. Establish `hB` using `hρ.base i j b`. Take `⟨hF1, hF2⟩` from `((ρ.B i j b).mem_mtLat _ _ _).1 hF`. Take `⟨γ, s, h', κ, hs, hoff, hh', hsupp, e⟩` from `exists_rep hρ (i := i) (b := b) (ρ.tw i b k Q ψ) h`. Establish `hlaw` using `((ρ.B i j b).mem_formsC.1 hF1).2 γ (finPt _ h') κ`.

Establish `hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) = F (finPt _ h')`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]`. Rewrite using `[e, hlaw, LinearMap.map_smul, GlobalTheory.BaseClassSum.series_move hB (D.sp.V_sig _) ht hadm (hρ.weil i j b _ ht) hh hh' γ κ e, hinv, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]`. Establish `hspan : F (finPt _ h') ∈ Submodule.span (ρ.eOk i b k).range (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank))` using `GlobalTheory.SmallSpan.harmLat_le_span (RingHom.id _) (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.eOk i b k).range (hρ.isCoefRing_k i b k).int _ _ hB.wt (GlobalTheory.CoefLatConj.pq_le hB) (GlobalTheory.SmallSpan.isLattice_latAt hB.frame _) (hF2 _)`. Generalize the expression as in `F (finPt _ h') = P at hspan`.

Proceed by induction on `hspan using Submodule.span_induction with`. Consider the case `mem P hP => exact series_datum hρ rd hR hψ hQ ⟨hs, hoff, hh', hsupp, hP⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem_range hρ rd`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem_range hρ rd hx hy`. Consider the case `smul a x _ hx`. Take `⟨_, u, rfl⟩` from `a`. Establish `h2` using `ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u) hx`. Rewrite `h2` using `[← map_smul]`.

Conclude with `h2`.
-/
theorem term_mem (hR : RatTwist hρ rd) {k Q ψ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q) {F} (hF : F ∈ ρ.mt i j b k Q ψ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b k Q ψ).chi) ((ρ.B i j b).vecFlat (ρ.tw i b k Q ψ)) h (F (finPt _ h)) ∈
      Set.range (rdK rd hρ k) := by
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hB := hρ.base i j b
  obtain ⟨hF1, hF2⟩ := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
  obtain ⟨γ, s, h', κ, hs, hoff, hh', hsupp, e⟩ := exists_rep hρ (i := i) (b := b) (ρ.tw i b k Q ψ) h
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF1).2 γ (finPt _ h') κ
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e, hlaw, LinearMap.map_smul, GlobalTheory.BaseClassSum.series_move hB (D.sp.V_sig _) ht hadm (hρ.weil i j b _ ht) hh hh' γ κ e, hinv,
    smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hspan : F (finPt _ h') ∈ Submodule.span (ρ.eOk i b k).range
      (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) :=
    GlobalTheory.SmallSpan.harmLat_le_span (RingHom.id _) (embLL0 D) (labLL0 D) (ρ.eO i b).range (ρ.eOk i b k).range
      (hρ.isCoefRing_k i b k).int _ _ hB.wt (GlobalTheory.CoefLatConj.pq_le hB) (GlobalTheory.SmallSpan.isLattice_latAt hB.frame _) (hF2 _)
  generalize F (finPt _ h') = P at hspan
  induction hspan using Submodule.span_induction with
  | mem P hP => exact series_datum hρ rd hR hψ hQ ⟨hs, hoff, hh', hsupp, hP⟩
  | zero => rw [map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx =>
    obtain ⟨_, u, rfl⟩ := a
    have h2 := ek_smul_mem_range hρ rd (algebraMap (D.ntw.Ok i k) _ u) hx
    rw [← map_smul] at h2
    exact h2

/- English proof (translation)
Introduce `D ρ hρ i j b rd T hR _ k Q ψ hψ hQ f`. Take `⟨ht, hadm, -⟩` from `GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ`. Establish `hc` using `hρ.classes i j b _ ht hadm`. Establish `hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok i k)) (D.nexp.MtLat i ((j : ℕ) + 1) b k Q ψ : Set (D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ))`. Rewrite using `[D.nexp.MtLat_span]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Establish `hF` using `(T.mtLat_iff k Q ψ hψ _).2 ⟨f, hf, rfl⟩`. Rewrite using `[Setup.sum, Base.classSum_apply]`.

Use `Finset.sum_induction _ (· ∈ Set.range (rdK rd hρ k)) (fun _ _ => add_mem_range hρ rd) (zero_mem_range hρ rd) fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (ρ.ek i b k), ← map_inv₀]`. Conclude with `ek_smul_mem_range hρ rd _ (term_mem hρ rd hR hψ hQ hF (hc.fin c))`. Consider the case `zero => rw [map_zero, map_zero]`. Conclude with `zero_mem_range hρ rd`.

Consider the case `add x y _ _ hx hy => rw [map_add, map_add]`. Conclude with `add_mem_range hρ rd hx hy`. Consider the case `smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul]`. Conclude with `ek_smul_mem_range hρ rd a hx`.
-/
theorem sum_mem_range : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (rd : Rd ρ D.nexp i j b) (T : CellTie hρ D.nexp rd), RatTwist hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  ∀ k Q ψ, TwOK i k Q ψ → ClsQ (D := D) Q → ∀ f, ρ.sum i j b k Q ψ (T.rdV k Q ψ f) ∈ Set.range (rdK rd hρ k) := by
  intro D ρ hρ i j b rd T hR _ k Q ψ hψ hQ f
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hψ
  have hc := hρ.classes i j b _ ht hadm
  have hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok i k)) (D.nexp.MtLat i ((j : ℕ) + 1) b k Q ψ : Set (D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ)) := by
    rw [D.nexp.MtLat_span]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    have hF := (T.mtLat_iff k Q ψ hψ _).2 ⟨f, hf, rfl⟩
    rw [Setup.sum, Base.classSum_apply]
    refine Finset.sum_induction _ (· ∈ Set.range (rdK rd hρ k)) (fun _ _ => add_mem_range hρ rd) (zero_mem_range hρ rd) fun c _ => ?_
    rw [← map_natCast (ρ.ek i b k), ← map_inv₀]
    exact ek_smul_mem_range hρ rd _ (term_mem hρ rd hR hψ hQ hF (hc.fin c))
  | zero => rw [map_zero, map_zero]; exact zero_mem_range hρ rd
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem_range hρ rd hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul]; exact ek_smul_mem_range hρ rd a hx

end GlobalTheory.ClassSumRat

end
