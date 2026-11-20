import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (0 : Ainf D.host.F) * 0 = 0`. Rewrite using `[zero_mul]`. Both sides reduce to the same expression.
-/
theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  refine Prod.ext ?_ ?_
  · show (0 : Ainf D.host.F) * 0 = 0
    rw [zero_mul]
  · rfl

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, pairA_mul]`.
-/
theorem pair_tmul_mul (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul]

def Good (v : Pl D) (α : Af D.host.F) : Prop :=
  α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w α = 0

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w => by rw [map_mul]; exact mul_mem (hα.1 w) (hβ.1 w), fun w hw => by rw [map_mul, hα.2 w hw, zero_mul]⟩`.
-/
theorem Good.mul {v : Pl D} {α β : Af D.host.F} (hα : Good v α) (hβ : Good v β) : Good v (α * β) :=
  ⟨fun w => by rw [map_mul]; exact mul_mem (hα.1 w) (hβ.1 w), fun w hw => by rw [map_mul, hα.2 w hw, zero_mul]⟩

/- English proof (translation)
Use `⟨fun w => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.SelfDualAt.evalV_indP] split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Rewrite using `[GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]`.
-/
theorem good_indP (v : Pl D) : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]

/- English proof (translation)
Use `FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_` and prove the remaining obligations. Establish `h1 : evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D` using `D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v)) = evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by`. Rewrite using `[map_mul, GlobalTheory.SelfDualAt.evalV_indP]`. Apply the tactic sequence `split_ifs <;> simp`. Conclude with `h1`.
-/
theorem indicatorAdele_mul_self (v : Pl D) :
    GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v) = GlobalTheory.SelfDualAt.indP (D := D) (· = v) := by
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  have h1 : evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v)) =
      evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
    rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs <;> simp
  exact h1

/- English proof (translation)
Use `Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0`. Conclude with `TensorProduct.zero_tmul _ _`. Express the relevant statement in the definitionally equal form `(evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0`. Rewrite using `[hα _ w.2, TensorProduct.zero_tmul]`.
-/
theorem gen_mem_idAt (v : Pl D) (α : Af D.host.F) (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hα _ w.2, TensorProduct.zero_tmul]

/- English proof (translation)
The claim follows from `(GlobalTheory.SeeSaw.LiftModel.AA_ne (D := D) Formalism.IndefR.Fin.factPrincipalDatum).1`.
-/
theorem AA_ne_zero : D.host.AA ≠ 0 :=
  (GlobalTheory.SeeSaw.LiftModel.AA_ne (D := D) Formalism.IndefR.Fin.factPrincipalDatum).1

/- English proof (translation)
Establish `h : d * c ∈ D.host.AA⁻¹ * D.host.AA` using `FractionalIdeal.mul_mem_mul hd hc`. Rewrite `h` using `[inv_mul_cancel₀ AA_ne_zero]`. Take `⟨o, ho⟩` from `(FractionalIdeal.mem_one_iff _).1 h`. Conclude with `⟨o, ho⟩`.
-/
theorem int_of_mem {c d : D.host.E} (hc : c ∈ D.host.AA) (hd : d ∈ D.host.AA⁻¹) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = d * c := by
  have h : d * c ∈ D.host.AA⁻¹ * D.host.AA := FractionalIdeal.mul_mem_mul hd hc
  rw [inv_mul_cancel₀ AA_ne_zero] at h
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨o, ho⟩

/- English proof (translation)
Unfold `GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hz`. Unfold `GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨β, hβ1, hβ2, a, ha, x, hx, rfl⟩` from `hz`.

Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Establish `g` using `hε.mul ⟨hβ1, hβ2⟩`. Use `⟨ε * β, g.1, g.2, c, hc, x, hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [smul_add]`.

Conclude with `add_mem h1 h2`. Consider the case `neg x _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
theorem smul_latV_mem_latA (S : HSp D) (L : Lat S) (v : Pl D) {ε : Af D.host.F} (hε : Good v ε) {c : D.host.E}
    (hc : c ∈ D.host.AA) {z : Fin S.rank → AE D} (hz : z ∈ latV S L (· = v)) :
    ((pairA D.host.F 0 ε) ⊗ₜ[D.host.F] c : AE D) • z ∈ latA S L (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hz
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβ1, hβ2, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    apply AddSubgroup.subset_closure
    have g := hε.mul ⟨hβ1, hβ2⟩
    refine ⟨ε * β, g.1, g.2, c, hc, x, hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.SeeSaw.LatAt

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

/- English proof (translation)
Unfold `GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul at hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα1, hα2, c, hc, x, hx, rfl⟩` from `hy`. Use `⟨fun i => gen_mem_idAt v α hα2 _, fun s hs => ?_⟩` and prove the remaining obligations.

Unfold `idV at hs`. Proceed by induction on `hs using AddSubgroup.closure_induction with`. Consider the case `mem s hs`. Take `⟨β, hβ1, hβ2, d, hd, rfl⟩` from `hs`. Take `⟨o, ho⟩` from `int_of_mem hc hd`.

Unfold `GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Establish `g` using `Good.mul (v := v) ⟨hβ1, hβ2⟩ ⟨hα1, hα2⟩`. Use `⟨β * α, g.1, g.2, 1, rfl, o • x, L.smul_mem o hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul, Pi.smul_apply, Algebra.smul_def, ← mul_assoc]`. Use `congr 2`. Conclude with `ho.symm`. Consider the case `zero => rw [zero_smul]`. Conclude with `zero_mem _`.

Consider the case `add s t _ _ h1 h2 => rw [add_smul]`. Conclude with `add_mem h1 h2`. Consider the case `neg s _ h => rw [neg_smul]`. Conclude with `neg_mem h`. Consider the case `zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩`.

Consider the case `add y z _ _ h1 h2`. Conclude with `⟨fun i => add_mem (h1.1 i) (h2.1 i), fun s hs => by rw [smul_add]; exact add_mem (h1.2 s hs) (h2.2 s hs)⟩`. Consider the case `neg y _ h => exact ⟨fun i => neg_mem (h.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (h.2 s hs)⟩`.
-/
theorem mem_latA_fwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hy : y ∈ latA S L (· = v)) :
    (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα1, hα2, c, hc, x, hx, rfl⟩ := hy
    refine ⟨fun i => gen_mem_idAt v α hα2 _, fun s hs => ?_⟩
    unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨β, hβ1, hβ2, d, hd, rfl⟩ := hs
      obtain ⟨o, ho⟩ := int_of_mem hc hd
      unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
      apply AddSubgroup.subset_closure
      have g := Good.mul (v := v) ⟨hβ1, hβ2⟩ ⟨hα1, hα2⟩
      refine ⟨β * α, g.1, g.2, 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul, Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
      congr 2
      exact ho.symm
    | zero => rw [zero_smul]; exact zero_mem _
    | add s t _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
    | neg s _ h => rw [neg_smul]; exact neg_mem h
  | zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ h1 h2 =>
    exact ⟨fun i => add_mem (h1.1 i) (h2.1 i), fun s hs => by rw [smul_add]; exact add_mem (h1.2 s hs) (h2.2 s hs)⟩
  | neg y _ h => exact ⟨fun i => neg_mem (h.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (h.2 s hs)⟩

/- English proof (translation)
Establish `hε : Good v (GlobalTheory.SelfDualAt.indP (D` using `D) (· = v)) := good_indP v`. Establish `key : ∀ t ∈ D.host.AA * D.host.AA⁻¹, ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D` using `D) (· = v))) ⊗ₜ[D.host.F] t : AE D) • y ∈ latA S L (· = v) := by`. Introduce `t ht`. Use `FractionalIdeal.mul_induction_on ht ?_ ?_` and prove the remaining obligations. Introduce `c hc d hd`.

Establish `e : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D` using `D) (· = v))) ⊗ₜ[D.host.F] (c * d) : AE D) = ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] c) * ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] d) := by`. Rewrite using `[pair_tmul_mul, indicatorAdele_mul_self]`. Rewrite using `[e, mul_smul]`. Use `smul_latV_mem_latA S L v hε hc (h _ ?_)` and prove the remaining obligations. Unfold `idV`.

Conclude with `AddSubgroup.subset_closure ⟨_, hε.1, hε.2, d, hd, rfl⟩`. Introduce `a b ha hb`. Rewrite using `[TensorProduct.tmul_add, add_smul]`. Conclude with `add_mem ha hb`. Establish `h1` using `key 1 (by rw [mul_inv_cancel₀ AA_ne_zero]; exact FractionalIdeal.one_mem_one _)`.

Establish `e1 : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D` using `D) (· = v))) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • y = y := by`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Conclude with `GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) (y i) (hsupp i)`. Rewrite `h1` using `[e1]`. Then use the resulting hypothesis.
-/
theorem mem_latA_bwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hsupp : ∀ i, y i ∈ idAt D (· = v))
    (h : ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v)) : y ∈ latA S L (· = v) := by
  have hε : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := good_indP v
  have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹,
      ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] t : AE D) • y ∈ latA S L (· = v) := by
    intro t ht
    refine FractionalIdeal.mul_induction_on ht ?_ ?_
    · intro c hc d hd
      have e : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (c * d) : AE D) =
          ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] c) *
            ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] d) := by
        rw [pair_tmul_mul, indicatorAdele_mul_self]
      rw [e, mul_smul]
      refine smul_latV_mem_latA S L v hε hc (h _ ?_)
      unfold idV
      exact AddSubgroup.subset_closure ⟨_, hε.1, hε.2, d, hd, rfl⟩
    · intro a b ha hb
      rw [TensorProduct.tmul_add, add_smul]
      exact add_mem ha hb
  have h1 := key 1 (by rw [mul_inv_cancel₀ AA_ne_zero]; exact FractionalIdeal.one_mem_one _)
  have e1 : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) (y i) (hsupp i)
  rwa [e1] at h1

end GlobalTheory.SeeSaw.LatAt

/- English proof (translation)
Introduce `_ v S L y` and use `⟨GlobalTheory.SeeSaw.LatAt.mem_latA_fwd S L v y, fun h => GlobalTheory.SeeSaw.LatAt.mem_latA_bwd S L v y h.1 h.2⟩`.
-/
theorem GlobalTheory.SeeSaw.mem_latA_iff_mul_inv : ∀ (D : D7) (v : Pl D) (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) :=
  fun _ v S L y => ⟨GlobalTheory.SeeSaw.LatAt.mem_latA_fwd S L v y, fun h => GlobalTheory.SeeSaw.LatAt.mem_latA_bwd S L v y h.1 h.2⟩

end
