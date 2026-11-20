import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsSumFrame
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoprimeScalingIdealValuationLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.CoreGlue

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.LiftModel

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, hα', c, hc, x, hx, rfl⟩` from `hy`. Rewrite `hc` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality.

Use `AddSubgroup.subset_closure ⟨α, hα, hα', 1, rfl, m *ᵥ x, h x hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((1 : AF D.host.F) ⊗ₜ[D.host.F] m i j) * _ = _`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero => rw [mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mulVec_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [mulVec_neg]`. Conclude with `neg_mem hx`.
-/
theorem rat_mulVec_mem {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latV T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα', 1, rfl, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] m i j) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]`.
-/
theorem dsum_eq {S : HSp D} (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

/- English proof (translation)
Establish `h : A.gram * o.qA = o.iAᴴ * S.gram`. Rewrite using `[OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]`. Rewrite using `[mulVec_mulVec, h, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star a)]`.
-/
theorem pair_iA {S A B : HSp D} (o : OrthDec S A B) (a : Fin A.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (o.iA *ᵥ a) ⬝ᵥ S.gram *ᵥ y = star a ⬝ᵥ A.gram *ᵥ (o.qA *ᵥ y) := by
  have h : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  rw [mulVec_mulVec, h, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star a)]

/- English proof (translation)
Set `fA` to `(mulVecLin o.iA).restrictScalars (𝓞 D.host.E)`. Set `fB` to `(mulVecLin o.iB).restrictScalars (𝓞 D.host.E)`. Establish `hsum : ∀ y : Fin S.rank → D.host.E, y = o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y)` using `fun y => by`. Rewrite using `[mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.iA_qA_add, one_mulVec]`. Establish `hiA : ∀ x ∈ LA, o.iA *ᵥ x ∈ LA.map fA ⊔ LB.map fB` using `fun x hx => Submodule.mem_sup_left ⟨x, hx, rfl⟩`.

Establish `hiB : ∀ x ∈ LB, o.iB *ᵥ x ∈ LA.map fA ⊔ LB.map fB` using `fun x hx => Submodule.mem_sup_right ⟨x, hx, rfl⟩`. Establish `hmem : ∀ y, y ∈ LA.map fA ⊔ LB.map fB ↔ o.qA *ᵥ y ∈ LA ∧ o.qB *ᵥ y ∈ LB` using `fun y => by`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Take `⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 h`. Express the relevant statement in the definitionally equal form `o.qA *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LA ∧ o.qB *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LB`.

Simplify using `only [mulVec_add, mulVec_mulVec, o.qA_iA, o.qA_iB, o.qB_iA, o.qB_iB, one_mulVec, zero_mulVec, add_zero, zero_add]`. Conclude with `⟨ha, hb⟩`. Rewrite using `[hsum y]`. Conclude with `add_mem (hiA _ h.1) (hiB _ h.2)`. Use `⟨LA.map fA ⊔ LB.map fB, ⟨⟨(hA.1.fg.map _).sup (hB.1.fg.map _), ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩, fun v y => ⟨fun hy => ⟨rat_mulVec_mem _ (fun x hx => ((hmem x).1 hx).1) hy, rat_mulVec_mem _ (fun x hx => ((hmem x).1 hx).2) hy⟩, fun h => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `y _`. Establish `key : ∀ {C : HSp D} (m : Matrix (Fin S.rank) (Fin C.rank) D.host.E) (LC : Lat C), IsSelfDualC C LC → (∀ x ∈ LC, m *ᵥ x ∈ LA.map fA ⊔ LB.map fB) → ∀ z, m *ᵥ z ∈ Submodule.span D.host.E ((LA.map fA ⊔ LB.map fB : Lat S) : Set (Fin S.rank → D.host.E))`. Introduce `C m LC hC hm z`. Establish `hz : z ∈ Submodule.span D.host.E (LC : Set (Fin C.rank → D.host.E))` using `by rw [hC.1.span_eq_top]; trivial`.

Establish `: Submodule.span D.host.E (LC : Set (Fin C.rank → D.host.E)) ≤ Submodule.comap (mulVecLin m) (Submodule.span D.host.E ((LA.map fA ⊔ LB.map fB : Lat S) : Set (Fin S.rank → D.host.E)))` using `Submodule.span_le.2 fun x hx => Submodule.subset_span (hm x hx)`. Conclude with `this hz`. Rewrite using `[hsum y]`. Conclude with `add_mem (key _ LA hA hiA _) (key _ LB hB hiB _)`. Take `⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hx`.

Take `⟨c, hc⟩` from `(hA.2 _).1 ((hmem y).1 hy).1 a ha`. Take `⟨d, hd⟩` from `(hB.2 _).1 ((hmem y).1 hy).2 b hb`. Use `⟨c + d, ?_⟩` and prove the remaining obligations. Rewrite `hc`, `hd`, the goal using `[dsum_eq]`. Express the relevant statement in the definitionally equal form `_ = star (o.iA *ᵥ a + o.iB *ᵥ b) ⬝ᵥ _`.

Establish `e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y)` using `pair_iA o.symm b y`. Rewrite using `[star_add, add_dotProduct, pair_iA, e2, ← hc, ← hd]`. Both sides reduce to the same expression. Use `(hmem y).2 ⟨(hA.2 _).2 fun a ha => ?_, (hB.2 _).2 fun b hb => ?_⟩` and prove the remaining obligations. Use `h _ (hiA a ha)` as an intermediate fact.

Rewrite `this` using `[dsum_eq, pair_iA, ← dsum_eq]`. Then use the resulting hypothesis. Use `h _ (hiB b hb)` as an intermediate fact. Establish `e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y)` using `pair_iA o.symm b y`. Rewrite `this` using `[dsum_eq, e2, ← dsum_eq]`. Then use the resulting hypothesis. Establish `e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y)`.

Rewrite using `[mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.sum_eq_one, one_mulVec]`. Rewrite using `[e]`. Conclude with `add_mem (rat_mulVec_mem _ hiA h.1) (rat_mulVec_mem _ hiB h.2)`.
-/
theorem exists_orthSum {S A B : HSp D} (o : OrthDec S A B) {LA : Lat A} {LB : Lat B} (hA : IsSelfDualC A LA)
    (hB : IsSelfDualC B LB) : ∃ L : Lat S, IsSelfDualC S L ∧ ∀ v, OrthAt o L LA LB v := by
  let fA := (mulVecLin o.iA).restrictScalars (𝓞 D.host.E)
  let fB := (mulVecLin o.iB).restrictScalars (𝓞 D.host.E)
  have hsum : ∀ y : Fin S.rank → D.host.E, y = o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) := fun y => by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.iA_qA_add, one_mulVec]
  have hiA : ∀ x ∈ LA, o.iA *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_left ⟨x, hx, rfl⟩
  have hiB : ∀ x ∈ LB, o.iB *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_right ⟨x, hx, rfl⟩
  have hmem : ∀ y, y ∈ LA.map fA ⊔ LB.map fB ↔ o.qA *ᵥ y ∈ LA ∧ o.qB *ᵥ y ∈ LB := fun y => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
      change o.qA *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LA ∧ o.qB *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LB
      simp only [mulVec_add, mulVec_mulVec, o.qA_iA, o.qA_iB, o.qB_iA, o.qB_iB, one_mulVec, zero_mulVec, add_zero, zero_add]
      exact ⟨ha, hb⟩
    · rw [hsum y]; exact add_mem (hiA _ h.1) (hiB _ h.2)
  refine ⟨LA.map fA ⊔ LB.map fB, ⟨⟨(hA.1.fg.map _).sup (hB.1.fg.map _), ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩,
    fun v y => ⟨fun hy => ⟨rat_mulVec_mem _ (fun x hx => ((hmem x).1 hx).1) hy,
      rat_mulVec_mem _ (fun x hx => ((hmem x).1 hx).2) hy⟩, fun h => ?_⟩⟩
  · rw [eq_top_iff]
    intro y _
    have key : ∀ {C : HSp D} (m : Matrix (Fin S.rank) (Fin C.rank) D.host.E) (LC : Lat C), IsSelfDualC C LC →
        (∀ x ∈ LC, m *ᵥ x ∈ LA.map fA ⊔ LB.map fB) → ∀ z, m *ᵥ z ∈ Submodule.span D.host.E
          ((LA.map fA ⊔ LB.map fB : Lat S) : Set (Fin S.rank → D.host.E)) := by
      intro C m LC hC hm z
      have hz : z ∈ Submodule.span D.host.E (LC : Set (Fin C.rank → D.host.E)) := by rw [hC.1.span_eq_top]; trivial
      have : Submodule.span D.host.E (LC : Set (Fin C.rank → D.host.E)) ≤ Submodule.comap (mulVecLin m)
          (Submodule.span D.host.E ((LA.map fA ⊔ LB.map fB : Lat S) : Set (Fin S.rank → D.host.E))) :=
        Submodule.span_le.2 fun x hx => Submodule.subset_span (hm x hx)
      exact this hz
    rw [hsum y]
    exact add_mem (key _ LA hA hiA _) (key _ LB hB hiB _)
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hA.2 _).1 ((hmem y).1 hy).1 a ha
    obtain ⟨d, hd⟩ := (hB.2 _).1 ((hmem y).1 hy).2 b hb
    refine ⟨c + d, ?_⟩
    rw [dsum_eq] at hc hd ⊢
    change _ = star (o.iA *ᵥ a + o.iB *ᵥ b) ⬝ᵥ _
    have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA o.symm b y
    rw [star_add, add_dotProduct, pair_iA, e2, ← hc, ← hd]
    rfl
  · refine (hmem y).2 ⟨(hA.2 _).2 fun a ha => ?_, (hB.2 _).2 fun b hb => ?_⟩
    · have := h _ (hiA a ha)
      rwa [dsum_eq, pair_iA, ← dsum_eq] at this
    · have := h _ (hiB b hb)
      have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA o.symm b y
      rwa [dsum_eq, e2, ← dsum_eq] at this
  · have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.sum_eq_one, one_mulVec]
    rw [e]
    exact add_mem (rat_mulVec_mem _ hiA h.1) (rat_mulVec_mem _ hiB h.2)

/- English proof (translation)
Use `⟨fun h => ⟨AddSubgroup.closure_mono ?_ h, latV_supp h⟩, fun h => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨α, h1, h2, r⟩`. Conclude with `⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), r⟩`. Establish `key : ∀ y ∈ latV S L P, (fun i => y i * (pairA D.host.F 0 (LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E))) ∈ latV S L (· = v)`. Introduce `y hy`.

Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, -, c, hc, x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨α * LatMem.indP D.host.F (· = v), LatMem.intAf_mul' hα (LatMem.indicatorAdele_mem_integralAdeles' _ _), fun w hw => ?_, c, hc, x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, LatMem.indicatorAdele_supported _ _ w hw, mul_zero]`.

Use function extensionality and compare the values at `i`. Establish `hp : pairA D.host.F 0 α * pairA D.host.F 0 (LatMem.indP D.host.F (· = v)) = pairA D.host.F 0 (α * LatMem.indP D.host.F (· = v))` using `Prod.ext (zero_mul _) rfl`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, hp, mul_one]`. Consider the case `zero => simp only [Pi.zero_apply, zero_mul]`. Conclude with `zero_mem _`.

Consider the case `add a b _ _ ha hb => simp only [Pi.add_apply, add_mul]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => simp only [Pi.neg_apply, neg_mul]`. Conclude with `neg_mem ha`. Use `key y h.1` as an intermediate fact.

Simplify using `only [LatMem.mul_indP (h.2 _)] at this`. Conclude with `this`.
-/
theorem mem_latV_one {S : HSp D} (L : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v) (y : Fin S.rank → AE D) :
    y ∈ latV S L (· = v) ↔ y ∈ latV S L P ∧ ∀ i, y i ∈ idAt D (· = v) := by
  refine ⟨fun h => ⟨AddSubgroup.closure_mono ?_ h, latV_supp h⟩, fun h => ?_⟩
  · rintro _ ⟨α, h1, h2, r⟩
    exact ⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), r⟩
  · have key : ∀ y ∈ latV S L P, (fun i => y i * (pairA D.host.F 0 (LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E))) ∈
        latV S L (· = v) := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨α * LatMem.indP D.host.F (· = v),
          LatMem.intAf_mul' hα (LatMem.indicatorAdele_mem_integralAdeles' _ _), fun w hw => ?_, c, hc, x, hx, ?_⟩
        · rw [map_mul, LatMem.indicatorAdele_supported _ _ w hw, mul_zero]
        · funext i
          have hp : pairA D.host.F 0 α * pairA D.host.F 0 (LatMem.indP D.host.F (· = v)) =
            pairA D.host.F 0 (α * LatMem.indP D.host.F (· = v)) := Prod.ext (zero_mul _) rfl
          rw [Algebra.TensorProduct.tmul_mul_tmul, hp, mul_one]
      | zero => simp only [Pi.zero_apply, zero_mul]; exact zero_mem _
      | add a b _ _ ha hb => simp only [Pi.add_apply, add_mul]; exact add_mem ha hb
      | neg a _ ha => simp only [Pi.neg_apply, neg_mul]; exact neg_mem ha
    have := key y h.1
    simp only [LatMem.mul_indP (h.2 _)] at this
    exact this

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_latV_one M hv, mem_latV_one L hv, h]`.
-/
theorem latV_eq_at {S : HSp D} {L M : Lat S} {P : Pl D → Prop} (h : latV S M P = latV S L P) {v : Pl D} (hv : P v) :
    latV S M (· = v) = latV S L (· = v) := by
  ext y
  rw [mem_latV_one M hv, mem_latV_one L hv, h]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩`. Consider the case `cons i l ih`. Take `⟨M, hM, h1, h2⟩` from `ih`. Take `⟨M', hM', h3, h4⟩` from `(GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).2.2.2.2.1 M (Λ i) hM (hΛ i)`.

Use `⟨M', hM', fun i' hi' => ?_, fun v hv => (latV_eq_at h4 (hv i)).trans (h2 v hv)⟩` and prove the remaining obligations. Distinguish the cases in `e : i' = i`. Substitute `e` using the available equality. Conclude with `h3`. Introduce `x`.

Rewrite using `[latV_eq_at h4 (fun e' => e (hp e'))]`. Conclude with `h1 i' ((List.mem_cons.1 hi').resolve_left e) x`.
-/
theorem exists_modify {ι : Type} {p : ι → SplitPt D k} (hp : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Λ : ι → Submodule 𝒪[k] (n → k)) (hΛ : ∀ i, (Λ i).IsLattice k)
    {L : Lat S} (hL : IsSelfDualC S L) (l : List ι) : ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i ∈ l, (β i).IsLat M (Λ i)) ∧
      ∀ v, (∀ i, v ≠ (p i).v) → latV S M (· = v) = latV S L (· = v) := by
  induction l with
  | nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨M', hM', h3, h4⟩ := (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).2.2.2.2.1 M (Λ i) hM (hΛ i)
    refine ⟨M', hM', fun i' hi' => ?_, fun v hv => (latV_eq_at h4 (hv i)).trans (h2 v hv)⟩
    by_cases e : i' = i
    · subst e; exact h3
    · intro x
      rw [latV_eq_at h4 (fun e' => e (hp e'))]
      exact h1 i' ((List.mem_cons.1 hi').resolve_left e) x

/- English proof (translation)
Rewrite using `[p.int_iff, p.sec_pr, RingHom.map_mul]`. Conclude with `mul_mem_intAE (e_mem_intAt p).2 ha`.
-/
theorem pr_mem_of_intAt (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

/- English proof (translation)
Rewrite using `[p.sec_pr, p.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff p a).1 ha]`.
-/
theorem eq_sec_add (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a = p.sec (p.pr a) + cA D (p.sec (p.pr (cA D a))) := by
  rw [p.sec_pr, p.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff p a).1 ha]

/- English proof (translation)
Use `⟨fun h => ⟨pr_mem_of_intAt p h.2, pr_mem_of_intAt p ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_sec_add p ha, RingHom.map_add]`. Conclude with `add_mem ((p.int_iff _).1 h.1) ((cA_int_iff _).2 ((p.int_iff _).1 h.2))`.
-/
theorem mem_intAt_iff (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a ∈ intAt D (· = p.v) ↔ p.pr a ∈ 𝒪[k] ∧ p.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_intAt p h.2, pr_mem_of_intAt p ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add p ha, RingHom.map_add]
  exact add_mem ((p.int_iff _).1 h.1) ((cA_int_iff _).2 ((p.int_iff _).1 h.2))

/- English proof (translation)
Take `⟨h1, h2⟩` from `hp.1 _ (e_mem_intAt p)`. Establish `he : p.pr p.e = 1` using `by rw [← sec_one, p.pr_sec]`. Establish `h3` using `pr_mem_of_intAt p h1.2`. Establish `h4` using `pr_mem_of_intAt p h2.2`. Rewrite `h3`, `h4` using `[RingHom.map_mul, he, mul_one, Valuation.mem_integer_iff]`.

Establish `h5 : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1`. Rewrite using `[← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one, RingHom.map_one, map_one]`. Use `le_antisymm h3 ?_` and prove the remaining obligations. Rewrite using `[← h5]`. Conclude with `mul_le_of_le_one_right' h4`.
-/
theorem valuation_xi_zero_eq_one (p : SplitPt D k) (hp : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  obtain ⟨h1, h2⟩ := hp.1 _ (e_mem_intAt p)
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h3 := pr_mem_of_intAt p h1.2
  have h4 := pr_mem_of_intAt p h2.2
  rw [RingHom.map_mul, he, mul_one, Valuation.mem_integer_iff] at h3 h4
  have h5 : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
      RingHom.map_one, map_one]
  refine le_antisymm h3 ?_
  rw [← h5]
  exact mul_le_of_le_one_right' h4

/- English proof (translation)
Establish `h0 : (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∘ Sum.inl = 0`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[GlobalTheory.LevelUnfold.mem_gluedS, h0]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, h1, h2⟩`. Establish `h3` using `(h2 0).1 rfl`. Rewrite `h3` using `[Pi.single_eq_same]`. Rewrite `h1` using `[zero_sub, neg_mem_iff, Pair.mem_ker]`. Establish `h4` using `(P.hasVal_vec.smul s).unique h1`.

Rewrite `h4` using `[mul_one, IsLocalRing.residue_eq_zero_iff, q.mem_max_iff]`. Take `⟨c, rfl⟩` from `h4`. Rewrite using `[h3, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]`. Conclude with `c.2`. Introduce `ht`.

Use `⟨q.1 * ⟨t, ht⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩` and prove the remaining obligations. Rewrite using `[zero_sub]`. Conclude with `neg_mem (Pair.smul_mem_ker (Ideal.mul_mem_right _ _ q.mem_max) P.hasVal_vec.mem)`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Rewrite using `[Pi.single_eq_same, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]`.
-/
theorem single_mem_glued_iff {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) (t : k) :
    (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec ↔ t ∈ 𝒪[k] := by
  have h0 : (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j
    simp
  rw [GlobalTheory.LevelUnfold.mem_gluedS, h0]
  constructor
  · rintro ⟨s, h1, h2⟩
    have h3 := (h2 0).1 rfl
    rw [Pi.single_eq_same] at h3
    rw [zero_sub, neg_mem_iff, Pair.mem_ker] at h1
    have h4 := (P.hasVal_vec.smul s).unique h1
    rw [mul_one, IsLocalRing.residue_eq_zero_iff, q.mem_max_iff] at h4
    obtain ⟨c, rfl⟩ := h4
    rw [h3, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]
    exact c.2
  · intro ht
    refine ⟨q.1 * ⟨t, ht⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · rw [zero_sub]
      exact neg_mem (Pair.smul_mem_ker (Ideal.mul_mem_right _ _ q.mem_max) P.hasVal_vec.mem)
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [Pi.single_eq_same, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]

/- English proof (translation)
Set `f : D.host.E →+* k` to `p.pr.comp (incA D)`. Set `r : Fin S.rank → D.host.E` to `star (vecB o ζ) ᵥ* S.gram`. Establish `hr : ∀ i, r i = ∑ j, star (S.gram i j) * star (vecB o ζ j)` using `fun i => by`. Simplify using `only [r, vecMul, dotProduct, Pi.star_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, ← conjTranspose_apply, gram_conjTranspose]`. Establish `h1 : ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) = t * ((f ∘ r) ⬝ᵥ β₀.b *ᵥ x)`. Simplify using `only [dotProduct, Function.comp_apply, hr, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ * f (star (S.gram i j)) * (t * f (star (vecB o ζ j))) = _`.

Expand and normalize the polynomial expressions, which then agree. Establish `hA : r ᵥ* o.iA = 0`. Simplify using `only [r, vecB, star_mulVec, vecMul_vecMul, o.orth, vecMul_zero]`. Establish `hB : r ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ`. Rewrite using `[← o.isoB]`.

Simplify using `only [r, vecB, star_mulVec, vecMul_vecMul, dotProduct_mulVec]`. Establish `hA' : (f ∘ r) ᵥ* o.jA.map p.pr = 0`. Use function extensionality and compare the values at `i`. Use `RingHom.map_vecMul f o.iA r i` as an intermediate fact. Rewrite `this` using `[hA, Pi.zero_apply, map_zero]`.

Conclude with `this.symm`. Establish `hB' : (f ∘ r) ⬝ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ))`. Rewrite using `[← hB]`. Conclude with `(RingHom.map_dotProduct f r (vecB o ζ)).symm`. Rewrite using `[h1, hs, dotProduct_mulVec, vecMul_fromCols, ← vecMul_vecMul, hA', zero_vecMul, ← hB']`.

Use `congr 1`. Simplify using `[dotProduct, vecMul, Fintype.sum_sum_type]`.
-/
theorem pair_sumFrame {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : Frame p A n} {β₀ : Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀) (x : n ⊕ Fin 1 → k) (t : k) :
    ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin S.rank → D.host.E := star (vecB o ζ) ᵥ* S.gram
  have hr : ∀ i, r i = ∑ j, star (S.gram i j) * star (vecB o ζ j) := fun i => by
    simp only [r, vecMul, dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← conjTranspose_apply, gram_conjTranspose]
  have h1 : ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * ((f ∘ r) ⬝ᵥ β₀.b *ᵥ x) := by
    simp only [dotProduct, Function.comp_apply, hr, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change _ * f (star (S.gram i j)) * (t * f (star (vecB o ζ j))) = _
    ring
  have hA : r ᵥ* o.iA = 0 := by
    simp only [r, vecB, star_mulVec, vecMul_vecMul, o.orth, vecMul_zero]
  have hB : r ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
    rw [← o.isoB]
    simp only [r, vecB, star_mulVec, vecMul_vecMul, dotProduct_mulVec]
  have hA' : (f ∘ r) ᵥ* o.jA.map p.pr = 0 := by
    funext i
    have := RingHom.map_vecMul f o.iA r i
    rw [hA, Pi.zero_apply, map_zero] at this
    exact this.symm
  have hB' : (f ∘ r) ⬝ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) := by
    rw [← hB]
    exact (RingHom.map_dotProduct f r (vecB o ζ)).symm
  rw [h1, hs, dotProduct_mulVec, vecMul_fromCols, ← vecMul_vecMul, hA', zero_vecMul, ← hB']
  congr 1
  simp [dotProduct, vecMul, Fintype.sum_sum_type]

/- English proof (translation)
Establish `hdec : a • ratV (vecB B.o B.ζ) = (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) (p.pr a) : n ⊕ Fin 1 → k)) i)) + fun i => cA D (p.sec (p.pr (cA D a) * p.pr (incA D (star (vecB B.o B.ζ i)))))`. Use function extensionality and compare the values at `i`. Establish `e` using `eq_sec_add p (Ideal.mul_mem_right (incA D (vecB B.o B.ζ i)) _ ha)`. Rewrite `e` using `[RingHom.map_mul, RingHom.map_mul (cA D), RingHom.map_mul, cA_incA]`. Use `e.trans ?_` and prove the remaining obligations.

Rewrite using `[Pi.add_apply, mulVec_single, hg.sum]`. Use `congr 2`. Conclude with `mul_comm _ _`. Establish `hq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0` using `by simpa using q.ne_zero`. Establish `hu : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * q.inv) = 1`.

Rewrite using `[map_mul, hg.norm, Unif.inv, map_inv₀, mul_inv_cancel₀ hq]`. Rewrite using `[hdec, decomp hM, ← hg.lat, single_mem_glued_iff, mem_intAt_iff p ha, csec_mem_iff hM]`. Use `and_congr_right fun _ => ⟨fun h => ?_, fun h x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `h _ ((hg.lat _).1 (GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨1, (by simp : Sum.elim P.vec (fun _ => q.inv) ∘ Sum.inl - (1 : 𝒪[k]) • P.vec ∈ P.ker), fun i => ⟨fun _ => by simp, fun hi => absurd hi (by omega)⟩⟩))`. Rewrite `h1` using `[pair_sumFrame B.o B.ζ hg.sum, Sum.elim_inr, Valuation.mem_integer_iff, map_mul, hu, mul_one]`.

Conclude with `h1`. Establish `hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x)` using `by rw [mulVec_mulVec, β₀.bb', one_mulVec]`. Rewrite `hx` using `[hx']`. Take `⟨s, -, hs⟩` from `GlobalTheory.LevelUnfold.mem_gluedS.1 ((hg.lat _).2 hx)`. Rewrite using `[hx', pair_sumFrame B.o B.ζ hg.sum, (hs 0).1 rfl, ← mul_assoc _ q.inv]`.

Conclude with `mul_mem h (mul_mem ((Valuation.mem_integer_iff _ _).2 hu.le) s.2)`.
-/
theorem line_of_glued {p : SplitPt D k} {ρ : ℕ} {B : BesLev D ρ} {M : Lat B.V₀} {q : Unif k} {n : Type} [Fintype n] [DecidableEq n]
    {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n} (hM : IsSelfDualC B.V₀ M) (hg : GluedCore B M q β β₀ P)
    {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = p.v) ↔ a ∈ intAt D (· = p.v) := by
  have hdec : a • ratV (vecB B.o B.ζ) = (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) (p.pr a) : n ⊕ Fin 1 → k)) i)) +
      fun i => cA D (p.sec (p.pr (cA D a) * p.pr (incA D (star (vecB B.o B.ζ i))))) := by
    funext i
    have e := eq_sec_add p (Ideal.mul_mem_right (incA D (vecB B.o B.ζ i)) _ ha)
    rw [RingHom.map_mul, RingHom.map_mul (cA D), RingHom.map_mul, cA_incA] at e
    refine e.trans ?_
    rw [Pi.add_apply, mulVec_single, hg.sum]
    congr 2
    exact mul_comm _ _
  have hq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using q.ne_zero
  have hu : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * q.inv) = 1 := by
    rw [map_mul, hg.norm, Unif.inv, map_inv₀, mul_inv_cancel₀ hq]
  rw [hdec, decomp hM, ← hg.lat, single_mem_glued_iff, mem_intAt_iff p ha, csec_mem_iff hM]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h x hx => ?_⟩
  · have h1 := h _ ((hg.lat _).1 (GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨1, (by simp : Sum.elim P.vec (fun _ => q.inv) ∘ Sum.inl - (1 : 𝒪[k]) • P.vec ∈ P.ker),
      fun i => ⟨fun _ => by simp, fun hi => absurd hi (by omega)⟩⟩))
    rw [pair_sumFrame B.o B.ζ hg.sum, Sum.elim_inr, Valuation.mem_integer_iff, map_mul, hu, mul_one] at h1
    exact h1
  · have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
    rw [hx'] at hx
    obtain ⟨s, -, hs⟩ := GlobalTheory.LevelUnfold.mem_gluedS.1 ((hg.lat _).2 hx)
    rw [hx', pair_sumFrame B.o B.ζ hg.sum, (hs 0).1 rfl, ← mul_assoc _ q.inv]
    exact mul_mem h (mul_mem ((Valuation.mem_integer_iff _ _).2 hu.le) s.2)

end GlobalTheory.SeeSaw.CoreGlue

end
