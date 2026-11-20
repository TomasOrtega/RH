import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrHOUpIncAdj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMemLatVIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLastPt

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `only [Matrix.vecMul, dotProduct]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `congr 1`. Use `show q.pr (incA D _) = q.pr (incA D _)`.

Use `congr 2`. Simplify using `only [Matrix.mulVec, dotProduct, star_sum, star_mul, Pi.star_apply, GlobalTheory.LatVac.gram_star]`.
-/
theorem sum_frame_star (q : SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y)
    (u : Fin S.rank → D.host.E) (m : Y) :
    ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) =
      ((fun l => q.pr (incA D ((star u ᵥ* S.gram) l))) ᵥ* F.β) m := by
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_comm]
  congr 1
  show q.pr (incA D _) = q.pr (incA D _)
  congr 2
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul, Pi.star_apply, GlobalTheory.LatVac.gram_star]

/- English proof (translation)
Establish `h` using `congrArg q.pr (FrameLat.cAe_mul_e q)`. Rewrite `h` using `[map_mul, GlobalTheory.LastPrimSplit.pr_e, mul_one, map_zero]`. Then use the resulting hypothesis.
-/
theorem pr_cA_e (q : SplitPt D k) : q.pr (cA D q.e) = 0 := by
  have h := congrArg q.pr (FrameLat.cAe_mul_e q)
  rwa [map_mul, GlobalTheory.LastPrimSplit.pr_e, mul_one, map_zero] at h

/- English proof (translation)
Rewrite `ha`, the goal using `[FrameLat.idem_iff]`. Use `conv_rhs => rw [← ha]`. Rewrite using `[RingHom.map_mul, RingHom.map_add, GlobalTheory.LocSympl.conj_conj, add_comm]`.
-/
theorem cA_mem_idAt (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) : cA D a ∈ idAt D (· = q.v) := by
  rw [FrameLat.idem_iff] at ha ⊢
  conv_rhs => rw [← ha]
  rw [RingHom.map_mul, RingHom.map_add, GlobalTheory.LocSympl.conj_conj, add_comm]

/- English proof (translation)
Establish `h1 : a ∈ idAt D (· = q.v)` using `ha.1`. Rewrite `ha` using `[GlobalTheory.SplitLine.mem_intAt_iff_pr q h1]`. Rewrite using `[GlobalTheory.SplitLine.mem_intAt_iff_pr q (cA_mem_idAt q h1), GlobalTheory.LocSympl.conj_conj]`. Conclude with `⟨ha.2, ha.1⟩`.
-/
theorem cA_mem_intAt (q : SplitPt D k) {a : AE D} (ha : a ∈ intAt D (· = q.v)) : cA D a ∈ intAt D (· = q.v) := by
  have h1 : a ∈ idAt D (· = q.v) := ha.1
  rw [GlobalTheory.SplitLine.mem_intAt_iff_pr q h1] at ha
  rw [GlobalTheory.SplitLine.mem_intAt_iff_pr q (cA_mem_idAt q h1), GlobalTheory.LocSympl.conj_conj]
  exact ⟨ha.2, ha.1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩`.
-/
theorem mul_mem_intAt {a b : AE D} {v : Pl D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

/- English proof (translation)
Use `GlobalTheory.SplitLine.line_mem_latV_iff D k q S L Y F u c m₀ hL hI hc hcol (fun m => ?_) ⟨m₁, ?_⟩` and prove the remaining obligations. Rewrite using `[sum_frame_star, hrow, Pi.single_apply] split_ifs`. Conclude with `(Valuation.mem_integer_iff _ _).2 (le_of_eq hc₁)`. Conclude with `zero_mem _`. Rewrite using `[sum_frame_star, hrow, Pi.single_eq_same, hc₁]`.
-/
theorem line_iff (q : SplitPt D k) (S : HSp D) (L : Lat S) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y)
    (u : Fin S.rank → D.host.E) (c : k) (m₀ m₁ : Y) (c₁ : k) (hL : IsSelfDualC S L) (hI : IntIn q S F L)
    (hc : valuation k c = 1) (hcol : ∀ r, c * (ofSplit q).pr (u r) = F.β r m₀)
    (hrow : (fun l => q.pr (incA D ((star u ᵥ* S.gram) l))) ᵥ* F.β = Pi.single m₁ c₁) (hc₁ : valuation k c₁ = 1) :
    ∀ a ∈ idAt D (· = q.v), (fun r => a * incA D (u r)) ∈ latV S L (· = q.v) ↔ a ∈ intAt D (· = q.v) := by
  refine GlobalTheory.SplitLine.line_mem_latV_iff D k q S L Y F u c m₀ hL hI hc hcol (fun m => ?_) ⟨m₁, ?_⟩
  · rw [sum_frame_star, hrow, Pi.single_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 (le_of_eq hc₁)
    · exact zero_mem _
  · rw [sum_frame_star, hrow, Pi.single_eq_same, hc₁]

/- English proof (translation)
Establish `h` using `congrFun (GlobalTheory.LastPrimSplit.row_core q B sc FA F₀ hF₀) (Sum.inr ())`. Rewrite `h` using `[Pi.single_eq_same]`. Use `mul_left_cancel₀ hsc ?_` and prove the remaining obligations. Rewrite using `[← h, Matrix.vecMul, dotProduct]`. Simplify using `only [hF₀.2]`.

Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Use `show sc * (q.pr (incA D (FrameLat.row B.V₀ (vecB B.o B.ζ) b)) * q.pr (incA D (vecB B.o B.ζ b))) = q.pr (incA D (FrameLat.row B.V₀ (vecB B.o B.ζ) b)) * (sc * q.pr (incA D (vecB B.o B.ζ b)))`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pr_hzz (q : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k) (hsc : sc ≠ 0)
    (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) :
    q.pr (incA D (∑ b, FrameLat.row B.V₀ (vecB B.o B.ζ) b * vecB B.o B.ζ b)) = (ofSplit q).hz B := by
  have h := congrFun (GlobalTheory.LastPrimSplit.row_core q B sc FA F₀ hF₀) (Sum.inr ())
  rw [Pi.single_eq_same] at h
  refine mul_left_cancel₀ hsc ?_
  rw [← h, Matrix.vecMul, dotProduct]
  simp only [hF₀.2]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_mul]
  show sc * (q.pr (incA D (FrameLat.row B.V₀ (vecB B.o B.ζ) b)) * q.pr (incA D (vecB B.o B.ζ b))) =
    q.pr (incA D (FrameLat.row B.V₀ (vecB B.o B.ζ) b)) * (sc * q.pr (incA D (vecB B.o B.ζ b)))
  ring

end GlobalTheory.SplitLastPt

namespace GlobalTheory.SplitLastPt

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hsc0 : sc ≠ 0` using `fun h0 => by simp [h0] at hsc`. Establish `hid : FrameLat.pairing B.V₀ (vecB B.o B.ζ) yv ∈ idAt D (· = q.v)` using `sum_mem fun b _ => Ideal.mul_mem_left _ _ (FrameLat.latV_supp hyv b)`. Rewrite using `[GlobalTheory.SplitLine.mem_intAt_iff_pr q hid]`. Prove the components needed by the constructor for the conclusion. Establish `hu : (fun b => q.sec (q.pr (yv b))) ∈ latV B.V₀ M (· = q.v)`.

Establish `h` using `GlobalTheory.FinPl.LatIndHalf.mul_mem_latV (GlobalTheory.UpMem.finPart_e_int q) hyv`. Use `h using 2 with b` and compare the differences between its conclusion and the goal. Conclude with `q.sec_pr _`. Establish `hw` using `(hI (F₀.γ *ᵥ fun b => q.pr (yv b))).2 (by`. Rewrite using `[Matrix.mulVec_mulVec, F₀.βγ, Matrix.one_mulVec])` and apply the resulting hypothesis.

Establish `e : q.pr (FrameLat.pairing B.V₀ (vecB B.o B.ζ) yv) = ((fun l => q.pr (incA D ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l))) ᵥ* F₀.β) ⬝ᵥ (F₀.γ *ᵥ fun b => q.pr (yv b))`. Rewrite using `[← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, F₀.βγ, Matrix.one_mulVec]`. Simplify using `only [FrameLat.pairing, map_sum, map_mul, dotProduct]`. Both sides reduce to the same expression. Rewrite using `[e, GlobalTheory.LastPrimSplit.row_core q B sc FA F₀ hF₀, single_dotProduct]`.

Use `mul_mem ?_ (hw _)` and prove the remaining obligations. Conclude with `(Valuation.mem_integer_iff _ _).2 (by rw [map_mul, hsc, hhz, one_mul])`. Establish `hx : (fun b => cA D (q.sec (q.pr (cA D (yv b))))) ∈ latV B.V₀ M (· = q.v)`. Establish `h` using `GlobalTheory.FinPl.LatIndHalf.mul_mem_latV ((GlobalTheory.FinPl.FrameLat.cA_int_iff q.e).2 (GlobalTheory.UpMem.finPart_e_int q)) hyv`. Use `h using 2 with b` and compare the differences between its conclusion and the goal.

Rewrite using `[q.sec_pr, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj]`. Establish `hz : (fun i => q.sec (q.pr (incA D (vecB B.o B.ζ i)))) ∈ latV B.V₀ M (· = q.v)`. Establish `h` using `(hI (Pi.single (Sum.inr ()) sc⁻¹)).1 (fun i => by`. Distinguish the cases in `hi : i = Sum.inr ()`. Substitute `hi` using the available equality.

Rewrite using `[Pi.single_eq_same]`. Conclude with `(Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hsc, inv_one])`. Rewrite using `[Pi.single_eq_of_ne hi]`. Conclude with `zero_mem _)`. Use `h using 2 with i` and compare the differences between its conclusion and the goal.

Use `congr 1`. Rewrite using `[Matrix.mulVec_single]`. Express the relevant statement in the definitionally equal form `_ = F₀.β i (Sum.inr ()) * sc⁻¹`. Rewrite using `[hF₀.2]`. Use `show q.pr (incA D _) = sc * q.pr (incA D _) * sc⁻¹`.

Clear the denominators using the available nonvanishing facts. Establish `h` using `(FrameLat.csec_mem_iff hM _).1 hx _ hz`. Use `h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [FrameLat.pairing, FrameLat.row, map_sum, map_mul, FrameLat.cA_incA, star_sum, star_mul, Pi.star_apply, star_star]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.
-/
theorem pairing_mem_intAt (q : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k)
    (hsc : valuation k sc = 1) (hhz : valuation k ((ofSplit q).hz B) = 1) (FA : Frame k B.A.rank n)
    (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) (M : Lat B.V₀)
    (hM : IsSelfDualC B.V₀ M) (hI : IntIn q B.V₀ F₀ M) (yv : Fin B.V₀.rank → AE D)
    (hyv : yv ∈ latV B.V₀ M (· = q.v)) : FrameLat.pairing B.V₀ (vecB B.o B.ζ) yv ∈ intAt D (· = q.v) := by
  have hsc0 : sc ≠ 0 := fun h0 => by simp [h0] at hsc
  have hid : FrameLat.pairing B.V₀ (vecB B.o B.ζ) yv ∈ idAt D (· = q.v) :=
    sum_mem fun b _ => Ideal.mul_mem_left _ _ (FrameLat.latV_supp hyv b)
  rw [GlobalTheory.SplitLine.mem_intAt_iff_pr q hid]
  constructor
  · have hu : (fun b => q.sec (q.pr (yv b))) ∈ latV B.V₀ M (· = q.v) := by
      have h := GlobalTheory.FinPl.LatIndHalf.mul_mem_latV (GlobalTheory.UpMem.finPart_e_int q) hyv
      convert h using 2 with b
      exact q.sec_pr _
    have hw := (hI (F₀.γ *ᵥ fun b => q.pr (yv b))).2 (by
      rwa [Matrix.mulVec_mulVec, F₀.βγ, Matrix.one_mulVec])
    have e : q.pr (FrameLat.pairing B.V₀ (vecB B.o B.ζ) yv) =
        ((fun l => q.pr (incA D ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l))) ᵥ* F₀.β) ⬝ᵥ
          (F₀.γ *ᵥ fun b => q.pr (yv b)) := by
      rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, F₀.βγ, Matrix.one_mulVec]
      simp only [FrameLat.pairing, map_sum, map_mul, dotProduct]
      rfl
    rw [e, GlobalTheory.LastPrimSplit.row_core q B sc FA F₀ hF₀, single_dotProduct]
    refine mul_mem ?_ (hw _)
    exact (Valuation.mem_integer_iff _ _).2 (by rw [map_mul, hsc, hhz, one_mul])
  · have hx : (fun b => cA D (q.sec (q.pr (cA D (yv b))))) ∈ latV B.V₀ M (· = q.v) := by
      have h := GlobalTheory.FinPl.LatIndHalf.mul_mem_latV
        ((GlobalTheory.FinPl.FrameLat.cA_int_iff q.e).2 (GlobalTheory.UpMem.finPart_e_int q)) hyv
      convert h using 2 with b
      rw [q.sec_pr, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj]
    have hz : (fun i => q.sec (q.pr (incA D (vecB B.o B.ζ i)))) ∈ latV B.V₀ M (· = q.v) := by
      have h := (hI (Pi.single (Sum.inr ()) sc⁻¹)).1 (fun i => by
        by_cases hi : i = Sum.inr ()
        · subst hi
          rw [Pi.single_eq_same]
          exact (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hsc, inv_one])
        · rw [Pi.single_eq_of_ne hi]; exact zero_mem _)
      convert h using 2 with i
      congr 1
      rw [Matrix.mulVec_single]
      change _ = F₀.β i (Sum.inr ()) * sc⁻¹
      rw [hF₀.2]
      show q.pr (incA D _) = sc * q.pr (incA D _) * sc⁻¹
      field_simp
    have h := (FrameLat.csec_mem_iff hM _).1 hx _ hz
    convert h using 1
    simp only [FrameLat.pairing, FrameLat.row, map_sum, map_mul, FrameLat.cA_incA, star_sum, star_mul,
      Pi.star_apply, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]

end GlobalTheory.SplitLastPt

namespace GlobalTheory.SplitLastPt

open GlobalTheory.FinPl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ hψ a y βT PP l FY sc hNF hIs N M hN hNI hM hMI j ρ h hρ t ht`. Rewrite `ht`, the goal using `[← l.under]`. Take `⟨hsc, hstep, hhz, -, hjac, -⟩` from `hNF`. Establish `hsc0 : ∀ j, sc j ≠ 0` using `fun j h0 => by simpa [h0] using hsc j`. Establish `hxi1 : valuation l.k (ofSplit l.q).xi = 1`.

Establish `h2` using `hsc (0 + 1 + 1)`. Rewrite `h2` using `[hstep, map_mul, hsc 0, one_mul]`. Then use the resulting hypothesis. Establish `hxi0 : (ofSplit l.q).xi ≠ 0` using `fun h0 => by simp [h0] at hxi1`. Establish `hjs : j ≤ l.s + 1` using `by have := l.hs; omega`. Establish `hd : j + 1 + 2 * ρ = l.s + 1` using `by have := l.hs; omega`.

Establish `hjm : j + 1 < D.R.m` using `by omega`. Establish `hhz1` using `hhz j ρ h`. Take `⟨F₀, hF₀⟩` from `(ofSplit l.q).exists_isCoreFrame (hsc0 j) ((y.bes j ρ h).lev (a.x j).vol) (l.FX j hjs)`. Establish `hMI0` using `hMI j ρ h hjs F₀ hF₀`. Establish `hNI0` using `hNI (j + 1) (2 * ρ) hd`.

Establish `hJF` using `hjac j ρ h (2 * ρ) hd`. Establish `hLineN : ∀ s ∈ idAt D (· = l.q.v), (fun r => s * incA D (((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e' r ⟨ρ - 1, by omega⟩)) ∈ latV ((y.jac j ρ h).lev (a.x (j + 1)).vol).W (N (j + 1)) (· = l.q.v) ↔ s ∈ intAt D (· = l.q.v)` using `line_iff l.q _ (N (j + 1)) (FY (j + 1) (2 * ρ) hd) _ (sc j * ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi)) (Sum.inr ⟨ρ, by omega⟩) (Sum.inr ⟨ρ - 1, by omega⟩) (sc j * (ofSplit l.q).xi) (hN (j + 1) hjm) hNI0 (by rw [map_mul, map_div₀, hsc, hhz1, hxi1]; sim …`. Rewrite using `[hJF.2.2.2 ⟨ρ - 1, by omega⟩ ⟨ρ, by omega⟩ (by show ρ + (ρ - 1) + 1 = 2 * ρ; omega) r]`. Use the proof step `simp)`. Use the proof step `(by rw [← GlobalTheory.LastPrimSplit.row_jac l.q hρ _ (sc j) _ _ _ hJF]; rfl)`.

Use the proof step `(by rw [map_mul, hsc, hxi1, one_mul])`. Establish `hLineM : ∀ s ∈ idAt D (· = l.q.v), (fun r => s * incA D (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ r)) ∈ latV ((y.bes j ρ h).lev (a.x j).vol).V₀ (M j ρ h) (· = l.q.v) ↔ s ∈ intAt D (· = l.q.v)` using `line_iff l.q _ (M j ρ h) F₀ _ (sc j) (Sum.inr ()) (Sum.inr ()) (sc j * (ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (hM j ρ h) hMI0 (hsc j) (fun r => (hF₀.2 r).symm) (GlobalTheory.LastPrimSplit.row_core l.q _ (sc j) _ F₀ hF₀) (by rw [map_mul, hsc, hhz1, one_mul])`. Establish `hca : cA D t ∈ idAt D (· = l.q.v)` using `cA_mem_idAt l.q ht`. Establish `hT : ∀ yv : Fin ((y.bes j ρ h).lev (a.x j).vol).V₀.rank → AE D, Matrix.mulVec (((y.jac j ρ h).lev (a.x (j + 1)).vol).d.incAdj ((y.bes j ρ h).lev (a.x j).vol).V₀ (t • yZero ((y.bes j ρ h).lev (a.x j).vol).V₀ ρ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol) …`. Introduce `yv`.

Use function extensionality and compare the values at `r`. Establish `e1 : ∀ b, (star (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) ᵥ* ((y.bes j ρ h).lev (a.x j).vol).V₀.gram) b = FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b` using `fun b => rfl`. Simplify using `only [Matrix.mulVec, dotProduct, GlobalTheory.LastPrimSplit.incAdj_yZero_apply hρ, FrameLat.pairing, Finset.mul_sum, Finset.sum_mul, e1]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpid : ∀ yv ∈ latV ((y.bes j ρ h).lev (a.x j).vol).V₀ (M j ρ h) (· = l.q.v), cA D t * incA D D.host.xi0⁻¹ * FrameLat.pairing ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) yv ∈ idAt D (· = l.q.v)` using `fun yv hyv => Ideal.mul_mem_left _ _ (sum_mem fun b _ => Ideal.mul_mem_left _ _ (FrameLat.latV_supp hyv b))`. Rewrite using `[GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ (M j ρ h) (N (j + 1)) (hM j ρ h) (hN (j + 1) hjm)]`. Establish `hpinv : ∀ x : D.host.E, l.q.pr (incA D x⁻¹) = (l.q.pr (incA D x))⁻¹` using `fun x => map_inv₀ (l.q.pr.comp (incA D)) x`. Establish `hxiv : valuation l.k (l.q.pr (incA D D.host.xi0⁻¹)) = 1`.

Rewrite using `[hpinv, map_inv₀]`. Express the relevant statement in the definitionally equal form `(valuation l.k (ofSplit l.q).xi)⁻¹ = 1`. Rewrite using `[hxi1, inv_one]`. Establish `hxiv' : valuation l.k (l.q.pr (incA D (star D.host.xi0⁻¹))) = 1`. Rewrite using `[star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, hpinv, map_inv₀, map_neg, map_neg, Valuation.map_neg]`.

Express the relevant statement in the definitionally equal form `(valuation l.k (ofSplit l.q).xi)⁻¹ = 1`. Rewrite using `[hxi1, inv_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hmap⟩`. Establish `hε : l.q.e + cA D l.q.e ∈ intAt D (· = l.q.v)`.

Rewrite using `[GlobalTheory.SplitLine.mem_intAt_iff_pr l.q (FrameLat.sum_mem_idAt l.q)]`. Simplify using `only [map_add, GlobalTheory.LastPrimSplit.pr_e, pr_cA_e, GlobalTheory.LocSympl.conj_conj, add_zero, zero_add]`. Conclude with `⟨one_mem _, one_mem _⟩`. Establish `hy₀` using `(hLineM _ (FrameLat.sum_mem_idAt l.q)).2 hε`. Establish `h1` using `hmap _ hy₀`.

Simplify using `only at h1`. Rewrite `h1` using `[l.unit.2, hT]`. Establish `h2` using `(hLineN _ (hpid _ hy₀)).1 h1`. Establish `e : FrameLat.pairing ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) (fun r => (l.q.e + cA D l.q.e) * incA D ((vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) r)) = (l.q.e + cA D l.q.e) * incA …`. Simplify using `only [FrameLat.pairing, map_sum, map_mul, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun b _ => by ring`. Establish `hid2` using `hpid _ hy₀`. Rewrite `h2`, `hid2` using `[e]`. Rewrite `h2` using `[GlobalTheory.SplitLine.mem_intAt_iff_pr l.q hid2]`. Take `⟨h3, h4⟩` from `h2`.

Establish `hpz` using `pr_hzz l.q ((y.bes j ρ h).lev (a.x j).vol) (sc j) (hsc0 j) _ F₀ hF₀`. Establish `hzz : star (∑ b, FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b * (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b) = ∑ b, FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (ve …`. Simplify using `only [FrameLat.row, star_sum, star_mul, star_star, GlobalTheory.LatVac.gram_star, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring`.

Simplify using `only [map_mul, map_add, GlobalTheory.LastPrimSplit.pr_e, pr_cA_e, GlobalTheory.LocSympl.conj_conj, FrameLat.cA_incA, hzz, hpz, add_zero, zero_add, mul_one, one_mul] at h3 h4`. Rewrite using `[GlobalTheory.SplitLine.mem_intAt_iff_pr l.q ht]`. Rewrite `h3`, `h4` using `[Valuation.mem_integer_iff]`. Rewrite `h3` using `[map_mul, map_mul, hxiv, hhz1, mul_one, mul_one]`. Rewrite `h4` using `[map_mul, map_mul, hxiv', hhz1, mul_one, mul_one]`.

Conclude with `⟨(Valuation.mem_integer_iff _ _).2 h4, (Valuation.mem_integer_iff _ _).2 h3⟩`. Introduce `hti`. Use `⟨fun i l' => ?_, fun yv hyv => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LastPrimSplit.incAdj_yZero_apply hρ]`. Conclude with `Ideal.mul_mem_right _ _ hca`.

Simplify using `only`. Rewrite using `[l.unit.2, hT]`. Use `(hLineN _ (hpid _ hyv)).2 (mul_mem_intAt ?_ ?_)` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(l.unit.1 _ (cA_mem_intAt l.q hti)).2`.

Conclude with `pairing_mem_intAt l.q ((y.bes j ρ h).lev (a.x j).vol) (sc j) (hsc j) hhz1 _ F₀ hF₀ (M j ρ h) (hM j ρ h) hMI0 yv hyv`.
-/
theorem normalFr_incAdj_yZero_mem_latO_iff : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), 0 < ρ → ∀ t ∈ GlobalTheory.FinPl.idAt D (· = (PP.under (𝓞 D.host.F))), ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.incAdj ((y.bes j ρ h).lev (a.x j).vol).V₀ (t • yZero ((y.bes j ρ h).lev (a.x j).vol).V₀ ρ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ)) ∈ latO ((y.bes j ρ h).lev (a.x j).vol).V₀ ((y.jac j ρ h).lev (a.x (j + 1)).vol).W (M j ρ h : Set _) (N (j + 1) : Set _) (· = (PP.under (𝓞 D.host.F))) ↔ t ∈ GlobalTheory.FinPl.intAt D (· = (PP.under (𝓞 D.host.F))) := by
  intro D ψ hψ a y βT PP l FY sc hNF hIs N M hN hNI hM hMI j ρ h hρ t ht
  rw [← l.under] at ht ⊢
  obtain ⟨hsc, hstep, hhz, -, hjac, -⟩ := hNF
  have hsc0 : ∀ j, sc j ≠ 0 := fun j h0 => by simpa [h0] using hsc j
  have hxi1 : valuation l.k (ofSplit l.q).xi = 1 := by
    have h2 := hsc (0 + 1 + 1)
    rwa [hstep, map_mul, hsc 0, one_mul] at h2
  have hxi0 : (ofSplit l.q).xi ≠ 0 := fun h0 => by simp [h0] at hxi1
  have hjs : j ≤ l.s + 1 := by have := l.hs; omega
  have hd : j + 1 + 2 * ρ = l.s + 1 := by have := l.hs; omega
  have hjm : j + 1 < D.R.m := by omega
  have hhz1 := hhz j ρ h
  obtain ⟨F₀, hF₀⟩ := (ofSplit l.q).exists_isCoreFrame (hsc0 j) ((y.bes j ρ h).lev (a.x j).vol) (l.FX j hjs)
  have hMI0 := hMI j ρ h hjs F₀ hF₀
  have hNI0 := hNI (j + 1) (2 * ρ) hd
  have hJF := hjac j ρ h (2 * ρ) hd
  have hLineN : ∀ s ∈ idAt D (· = l.q.v),
      (fun r => s * incA D (((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e' r ⟨ρ - 1, by omega⟩)) ∈
        latV ((y.jac j ρ h).lev (a.x (j + 1)).vol).W (N (j + 1)) (· = l.q.v) ↔ s ∈ intAt D (· = l.q.v) :=
    line_iff l.q _ (N (j + 1)) (FY (j + 1) (2 * ρ) hd) _
      (sc j * ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi))
      (Sum.inr ⟨ρ, by omega⟩) (Sum.inr ⟨ρ - 1, by omega⟩) (sc j * (ofSplit l.q).xi) (hN (j + 1) hjm) hNI0
      (by rw [map_mul, map_div₀, hsc, hhz1, hxi1]; simp)
      (fun r => by
        rw [hJF.2.2.2 ⟨ρ - 1, by omega⟩ ⟨ρ, by omega⟩ (by show ρ + (ρ - 1) + 1 = 2 * ρ; omega) r]
        simp)
      (by rw [← GlobalTheory.LastPrimSplit.row_jac l.q hρ _ (sc j) _ _ _ hJF]; rfl)
      (by rw [map_mul, hsc, hxi1, one_mul])
  have hLineM : ∀ s ∈ idAt D (· = l.q.v),
      (fun r => s * incA D (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ r)) ∈
        latV ((y.bes j ρ h).lev (a.x j).vol).V₀ (M j ρ h) (· = l.q.v) ↔ s ∈ intAt D (· = l.q.v) :=
    line_iff l.q _ (M j ρ h) F₀ _ (sc j) (Sum.inr ()) (Sum.inr ())
      (sc j * (ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (hM j ρ h) hMI0 (hsc j) (fun r => (hF₀.2 r).symm)
      (GlobalTheory.LastPrimSplit.row_core l.q _ (sc j) _ F₀ hF₀) (by rw [map_mul, hsc, hhz1, one_mul])
  have hca : cA D t ∈ idAt D (· = l.q.v) := cA_mem_idAt l.q ht
  have hT : ∀ yv : Fin ((y.bes j ρ h).lev (a.x j).vol).V₀.rank → AE D, Matrix.mulVec (((y.jac j ρ h).lev (a.x (j + 1)).vol).d.incAdj ((y.bes j ρ h).lev (a.x j).vol).V₀ (t • yZero ((y.bes j ρ h).lev (a.x j).vol).V₀ ρ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ))) yv =
      fun r => (cA D t * incA D D.host.xi0⁻¹ * FrameLat.pairing ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) yv) * incA D (((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e' r ⟨ρ - 1, by omega⟩) := by
    intro yv
    funext r
    have e1 : ∀ b, (star (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) ᵥ* ((y.bes j ρ h).lev (a.x j).vol).V₀.gram) b = FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b := fun b => rfl
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.LastPrimSplit.incAdj_yZero_apply hρ, FrameLat.pairing, Finset.mul_sum,
      Finset.sum_mul, e1]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul]
    ring
  have hpid : ∀ yv ∈ latV ((y.bes j ρ h).lev (a.x j).vol).V₀ (M j ρ h) (· = l.q.v),
      cA D t * incA D D.host.xi0⁻¹ * FrameLat.pairing ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) yv ∈ idAt D (· = l.q.v) :=
    fun yv hyv => Ideal.mul_mem_left _ _ (sum_mem fun b _ => Ideal.mul_mem_left _ _ (FrameLat.latV_supp hyv b))
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ (M j ρ h) (N (j + 1)) (hM j ρ h) (hN (j + 1) hjm)]
  have hpinv : ∀ x : D.host.E, l.q.pr (incA D x⁻¹) = (l.q.pr (incA D x))⁻¹ := fun x =>
    map_inv₀ (l.q.pr.comp (incA D)) x
  have hxiv : valuation l.k (l.q.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [hpinv, map_inv₀]
    change (valuation l.k (ofSplit l.q).xi)⁻¹ = 1
    rw [hxi1, inv_one]
  have hxiv' : valuation l.k (l.q.pr (incA D (star D.host.xi0⁻¹))) = 1 := by
    rw [star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, hpinv, map_inv₀, map_neg, map_neg, Valuation.map_neg]
    change (valuation l.k (ofSplit l.q).xi)⁻¹ = 1
    rw [hxi1, inv_one]
  constructor
  · rintro ⟨-, hmap⟩
    have hε : l.q.e + cA D l.q.e ∈ intAt D (· = l.q.v) := by
      rw [GlobalTheory.SplitLine.mem_intAt_iff_pr l.q (FrameLat.sum_mem_idAt l.q)]
      simp only [map_add, GlobalTheory.LastPrimSplit.pr_e, pr_cA_e, GlobalTheory.LocSympl.conj_conj, add_zero, zero_add]
      exact ⟨one_mem _, one_mem _⟩
    have hy₀ := (hLineM _ (FrameLat.sum_mem_idAt l.q)).2 hε
    have h1 := hmap _ hy₀
    dsimp only at h1
    rw [l.unit.2, hT] at h1
    have h2 := (hLineN _ (hpid _ hy₀)).1 h1
    have e : FrameLat.pairing ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) (fun r => (l.q.e + cA D l.q.e) * incA D ((vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) r)) =
        (l.q.e + cA D l.q.e) * incA D (∑ b, FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b * (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b) := by
      simp only [FrameLat.pairing, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hid2 := hpid _ hy₀
    rw [e] at h2 hid2
    rw [GlobalTheory.SplitLine.mem_intAt_iff_pr l.q hid2] at h2
    obtain ⟨h3, h4⟩ := h2
    have hpz := pr_hzz l.q ((y.bes j ρ h).lev (a.x j).vol) (sc j) (hsc0 j) _ F₀ hF₀
    have hzz : star (∑ b, FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b * (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b) = ∑ b, FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b * (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b := by
      simp only [FrameLat.row, star_sum, star_mul, star_star, GlobalTheory.LatVac.gram_star, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
    simp only [map_mul, map_add, GlobalTheory.LastPrimSplit.pr_e, pr_cA_e, GlobalTheory.LocSympl.conj_conj, FrameLat.cA_incA, hzz, hpz,
      add_zero, zero_add, mul_one, one_mul] at h3 h4
    rw [GlobalTheory.SplitLine.mem_intAt_iff_pr l.q ht]
    rw [Valuation.mem_integer_iff] at h3 h4
    rw [map_mul, map_mul, hxiv, hhz1, mul_one, mul_one] at h3
    rw [map_mul, map_mul, hxiv', hhz1, mul_one, mul_one] at h4
    exact ⟨(Valuation.mem_integer_iff _ _).2 h4, (Valuation.mem_integer_iff _ _).2 h3⟩
  · intro hti
    refine ⟨fun i l' => ?_, fun yv hyv => ?_⟩
    · rw [GlobalTheory.LastPrimSplit.incAdj_yZero_apply hρ]
      exact Ideal.mul_mem_right _ _ hca
    · dsimp only
      rw [l.unit.2, hT]
      refine (hLineN _ (hpid _ hyv)).2 (mul_mem_intAt ?_ ?_)
      · rw [mul_comm]
        exact (l.unit.1 _ (cA_mem_intAt l.q hti)).2
      · exact pairing_mem_intAt l.q ((y.bes j ρ h).lev (a.x j).vol) (sc j) (hsc j) hhz1 _ F₀ hF₀ (M j ρ h) (hM j ρ h) hMI0 yv hyv

end GlobalTheory.SplitLastPt
