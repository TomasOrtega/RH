import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanSingletonMulIdealCompletionIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatLine

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, h0, c, hc, rfl⟩` from `hy`. Establish `e` using `incA_mul_tmul (D := D) c (pairA D.host.F 0 α) 1`. Rewrite `e` using `[mul_one]`.

Rewrite using `[← e, mul_comm (incA D c), mul_assoc]`. Conclude with `intAt_mul (tmul_one_mem_intAt hα h0) (h c hc)`. Consider the case `zero => rw [zero_mul]`. Conclude with `intAt_zero`. Consider the case `add x y _ _ hx hy => rw [add_mul]`.

Conclude with `intAt_add hx hy`. Consider the case `neg x _ hx => rw [neg_mul]`. Conclude with `intAt_neg hx`.
-/
theorem mul_idV_int {𝔠 : FI D} {v : GlobalTheory.FinPl.Pl D} {a : AE D}
    (h : ∀ c ∈ 𝔠, incA D c * a ∈ intAt D (· = v)) {y : AE D} (hy : y ∈ idV 𝔠 v) : y * a ∈ intAt D (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hy
    have e := incA_mul_tmul (D := D) c (pairA D.host.F 0 α) 1
    rw [mul_one] at e
    rw [← e, mul_comm (incA D c), mul_assoc]
    exact intAt_mul (tmul_one_mem_intAt hα h0) (h c hc)
  | zero => rw [zero_mul]; exact intAt_zero
  | add x y _ _ hx hy => rw [add_mul]; exact intAt_add hx hy
  | neg x _ hx => rw [neg_mul]; exact intAt_neg hx

/- English proof (translation)
Take `⟨b, hb0, hb⟩` from `GlobalTheory.IdVGen.idV_gen D v 𝔠⁻¹ (inv_ne_zero h𝔠)`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.IdVGen.idV_gen D v 𝔠 h𝔠`. Establish `hm` using `idV_mul_gen D v 𝔠⁻¹ 𝔠 b c hb0 hc0 hb hc (GlobalTheory.FinPlLoc.idem D (· = v))`. Rewrite `hm` using `[inv_mul_cancel₀ h𝔠, GlobalTheory.SeeSaw.idV_one_eq_intAt]`. Take `⟨h1, h2⟩` from `hm.1 (GlobalTheory.FinPlLoc.idem_mem_intAt _)`.

Establish `h3 : incA D b⁻¹ * GlobalTheory.FinPlLoc.idem D (· = v) ∈ idV 𝔠 v`. Use `(hc _).2 ⟨?_, Ideal.mul_mem_left _ _ h2⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← map_mul, ← mul_inv, mul_comm c b]`. Conclude with `h1`. Establish `h4` using `mul_idV_int h h3`.

Rewrite `h4` using `[mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha]`. Conclude with `(hb a).2 ⟨h4, ha⟩`.
-/
theorem mem_idV_inv {𝔠 : FI D} (h𝔠 : 𝔠 ≠ 0) {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ idAt D (· = v))
    (h : ∀ c ∈ 𝔠, incA D c * a ∈ intAt D (· = v)) : a ∈ idV 𝔠⁻¹ v := by
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠⁻¹ (inv_ne_zero h𝔠)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠 h𝔠
  have hm := idV_mul_gen D v 𝔠⁻¹ 𝔠 b c hb0 hc0 hb hc (GlobalTheory.FinPlLoc.idem D (· = v))
  rw [inv_mul_cancel₀ h𝔠, GlobalTheory.SeeSaw.idV_one_eq_intAt] at hm
  obtain ⟨h1, h2⟩ := hm.1 (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have h3 : incA D b⁻¹ * GlobalTheory.FinPlLoc.idem D (· = v) ∈ idV 𝔠 v := by
    refine (hc _).2 ⟨?_, Ideal.mul_mem_left _ _ h2⟩
    rw [← mul_assoc, ← map_mul, ← mul_inv, mul_comm c b]
    exact h1
  have h4 := mul_idV_int h h3
  rw [mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha] at h4
  exact (hb a).2 ⟨h4, ha⟩

/- English proof (translation)
Simplify using `only [pairing, ratV, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem pairing_smul_ratV (S : HSp D) (s x : Fin S.rank → D.host.E) (a : AE D) :
    pairing S s (a • ratV x) = incA D (∑ b, row S s b * x b) * a := by
  simp only [pairing, ratV, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
The claim follows from `GlobalTheory.MixModel.incA_injective`.
-/
theorem incA_inj : Function.Injective (incA D) := GlobalTheory.MixModel.incA_injective

/- English proof (translation)
Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, h0, t, ht, rfl⟩` from `hy`. Establish `e` using `incA_mul_tmul (D := D) t (pairA D.host.F 0 α) 1`. Rewrite `e` using `[mul_one]`.

Use `int_mul_mem (tmul_one_mem_intAt hα h0) (h t ht)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[← e]`. Simplify using `only [ratV, Pi.smul_apply, smul_eq_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [zero_smul]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_smul]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [neg_smul]`. Conclude with `neg_mem hx`.
-/
theorem smul_mem_latV {S : HSp D} {L : Lat S} {x : Fin S.rank → D.host.E} {𝔞 : FI D} (h : ∀ t ∈ 𝔞, t • x ∈ L)
    {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ idV 𝔞 v) : a • ratV x ∈ latV S L (· = v) := by
  induction ha using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, t, ht, rfl⟩ := hy
    have e := incA_mul_tmul (D := D) t (pairA D.host.F 0 α) 1
    rw [mul_one] at e
    have := int_mul_mem (tmul_one_mem_intAt hα h0) (h t ht)
    convert this using 1
    funext i
    rw [← e]
    simp only [ratV, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

/- English proof (translation)
Introduce `D S L x hL hx`. Take `⟨m, s, s', hs, hs', hexp⟩` from `exists_expansion hL`. Use `set c : Fin m → D.host.E := fun l => ∑ b, row S (s' l) b * x b with hc`. Establish `hx' : ∀ i, x i = ∑ l, c l * s l i`. Introduce `i`.

Apply `incA_inj (D := D)` to reduce the goal to its premises. Use `hexp ((1 : AE D) • ratV x) i` as an intermediate fact. Simplify using `only [pairing_smul_ratV, mul_one] at this`. Rewrite using `[map_sum]`. Simplify `this` using `only [one_smul, ratV, map_mul]`.

Use `set 𝔠 : FI D := FractionalIdeal.spanFinset (𝓞 D.host.E) Finset.univ c with h𝔠def`. Establish `hmem : ∀ y, y ∈ 𝔠 ↔ y ∈ Submodule.span (𝓞 D.host.E) (Set.range c)`. Introduce `y`. Rewrite using `[← FractionalIdeal.mem_coe, h𝔠def, FractionalIdeal.spanFinset_coe, Finset.coe_univ, Set.image_univ]`. Establish `h𝔠 : 𝔠 ≠ 0`.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Rewrite using `[hx' i]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Establish `: c l ∈ 𝔠` using `(hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)`. Rewrite `this` using `[h0, FractionalIdeal.mem_zero_iff]`. Rewrite using `[this, zero_mul]`. Establish `hglob : ∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔠⁻¹`. Introduce `t`.

Rewrite using `[FractionalIdeal.mem_inv_iff h𝔠]`. Prove the components needed by the constructor for the conclusion. Introduce `ht y hy`. Rewrite `hy` using `[hmem]`. Rewrite using `[← FractionalIdeal.mem_coe]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, rfl⟩` from `hy`. Take `⟨o, ho⟩` from `(hL.2 _).1 ht (s' l) (hs' l)`. Rewrite using `[FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]`.

Use `⟨o, ho.trans ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Simplify using `only [hc, GlobalTheory.FinPl.FrameLat.row, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Consider the case `zero => rw [mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul o y _ hy => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ hy`.

Introduce `ht`. Establish `ho : ∀ l, ∃ o : 𝓞 D.host.E, algebraMap _ D.host.E o = t * c l` using `fun l => (FractionalIdeal.mem_one_iff _).1 (ht _ ((hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)))`. Use `choose o ho using ho`. Establish `: t • x = ∑ l, o l • s l`. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, hx' i, Finset.mul_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Algebra.smul_def, ho, mul_assoc]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun l _ => L.smul_mem _ (hs l)`.

Use `⟨𝔠⁻¹, inv_ne_zero h𝔠, hglob, fun v a ha => ⟨fun h => ?_, smul_mem_latV fun t ht => (hglob t).2 ht⟩⟩` and prove the remaining obligations. Use `mem_idV_inv h𝔠 ha fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[hmem]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨l, rfl⟩` from `hy`. Use `⟨Ideal.mul_mem_left _ _ ha, ?_⟩` and prove the remaining obligations. Use `pairing_int hL (hs' l) h` as an intermediate fact. Rewrite `this` using `[pairing_smul_ratV]`. Then use the resulting hypothesis. Consider the case `zero => rw [map_zero, zero_mul]`.

Conclude with `intAt_zero`. Consider the case `add y z _ _ hy hz => rw [map_add, add_mul]`. Conclude with `intAt_add hy hz`. Consider the case `smul o y hy' hy`. Establish `h1` using `GlobalTheory.IdVGen.gen_mem_intAt (v := v) (GlobalTheory.FinPlLoc.ePl_int (· = v)) (fun w hw => by rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]) o`.

Establish `e` using `incA_mul_tmul (D := D) (algebraMap (𝓞 D.host.E) D.host.E o) (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v))) 1`. Rewrite `e` using `[mul_one]`. Establish `h2` using `intAt_mul h1 hy`. Rewrite `h2` using `[← e]`. Establish `h3 : GlobalTheory.FinPlLoc.idem D (· = v) * a = a` using `(GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Algebra.smul_def, map_mul]`. Use `conv_lhs => rw [← h3]`. Simplify using `only [GlobalTheory.FinPlLoc.idem]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem line_trace : ∀ (D : D7) (S : HSp D) (L : Lat S) (x : Fin S.rank → D.host.E), IsSelfDualC S L → x ≠ 0 → ∃ 𝔞 : FI D, 𝔞 ≠ 0 ∧ (∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔞) ∧ ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ a ∈ idV 𝔞 v := by
  intro D S L x hL hx
  obtain ⟨m, s, s', hs, hs', hexp⟩ := exists_expansion hL
  set c : Fin m → D.host.E := fun l => ∑ b, row S (s' l) b * x b with hc
  have hx' : ∀ i, x i = ∑ l, c l * s l i := by
    intro i
    apply incA_inj (D := D)
    have := hexp ((1 : AE D) • ratV x) i
    simp only [pairing_smul_ratV, mul_one] at this
    rw [map_sum]
    simpa only [one_smul, ratV, map_mul] using this
  set 𝔠 : FI D := FractionalIdeal.spanFinset (𝓞 D.host.E) Finset.univ c with h𝔠def
  have hmem : ∀ y, y ∈ 𝔠 ↔ y ∈ Submodule.span (𝓞 D.host.E) (Set.range c) := by
    intro y
    rw [← FractionalIdeal.mem_coe, h𝔠def, FractionalIdeal.spanFinset_coe, Finset.coe_univ, Set.image_univ]
  have h𝔠 : 𝔠 ≠ 0 := by
    intro h0
    apply hx
    funext i
    rw [hx' i]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : c l ∈ 𝔠 := (hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)
    rw [h0, FractionalIdeal.mem_zero_iff] at this
    rw [this, zero_mul]
  have hglob : ∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔠⁻¹ := by
    intro t
    rw [FractionalIdeal.mem_inv_iff h𝔠]
    constructor
    · intro ht y hy
      rw [hmem] at hy
      rw [← FractionalIdeal.mem_coe]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        obtain ⟨o, ho⟩ := (hL.2 _).1 ht (s' l) (hs' l)
        rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
        refine ⟨o, ho.trans ?_⟩
        rw [Finset.sum_comm]
        simp only [hc, GlobalTheory.FinPl.FrameLat.row, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      | zero => rw [mul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul o y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    · intro ht
      have ho : ∀ l, ∃ o : 𝓞 D.host.E, algebraMap _ D.host.E o = t * c l := fun l =>
        (FractionalIdeal.mem_one_iff _).1 (ht _ ((hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)))
      choose o ho using ho
      have : t • x = ∑ l, o l • s l := by
        funext i
        rw [Pi.smul_apply, smul_eq_mul, hx' i, Finset.mul_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, ho, mul_assoc]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => L.smul_mem _ (hs l)
  refine ⟨𝔠⁻¹, inv_ne_zero h𝔠, hglob, fun v a ha => ⟨fun h => ?_, smul_mem_latV fun t ht => (hglob t).2 ht⟩⟩
  refine mem_idV_inv h𝔠 ha fun y hy => ?_
  rw [hmem] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
    have := pairing_int hL (hs' l) h
    rwa [pairing_smul_ratV] at this
  | zero => rw [map_zero, zero_mul]; exact intAt_zero
  | add y z _ _ hy hz => rw [map_add, add_mul]; exact intAt_add hy hz
  | smul o y hy' hy =>
    have h1 := GlobalTheory.IdVGen.gen_mem_intAt (v := v) (GlobalTheory.FinPlLoc.ePl_int (· = v))
      (fun w hw => by rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]) o
    have e := incA_mul_tmul (D := D) (algebraMap (𝓞 D.host.E) D.host.E o) (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v))) 1
    rw [mul_one] at e
    have h2 := intAt_mul h1 hy
    rw [← e] at h2
    have h3 : GlobalTheory.FinPlLoc.idem D (· = v) * a = a := (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha
    convert h2 using 1
    rw [Algebra.smul_def, map_mul]
    conv_lhs => rw [← h3]
    simp only [GlobalTheory.FinPlLoc.idem]
    ring

end GlobalTheory.Core.Mi.LatLine

end
