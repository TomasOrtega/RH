import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped ENNReal

namespace GlobalTheory.HaarIdx

open MeasureTheory

/- English proof (translation)
Establish `hμ : μ ≠ 0`. Introduce `h`. Rewrite `hK` using `[h]`. Simplify using `at hK`. Establish `hmeas : ∀ g : Γ, AEMeasurable (fun x => g * x) μ`.

Introduce `g`. Assume the negation of the conclusion as `hg`. Establish `h1` using `Measure.map_of_not_aemeasurable hg`. Rewrite `h1` using `[map_mul_left_eq_self μ g]`. Conclude with `hμ h1`.

Establish `hpre : ∀ g : Γ, μ ((fun x => g * x) ⁻¹' (H : Set Γ)) = μ H`. Introduce `g`. Rewrite using `[← Measure.map_apply_of_aemeasurable (hmeas g) hH, map_mul_left_eq_self μ g]`. Use `set L := H.subgroupOf K`. Use `haveI : L.FiniteIndex := ⟨hn⟩`.

Use `haveI : Fintype (K ⧸ L) := Fintype.ofFinite _`. Set `C : (K ⧸ L) → Set Γ` to `fun q => (fun x => ((q.out : K) : Γ)⁻¹ * x) ⁻¹' (H : Set Γ)`. Establish `hcov : (K : Set Γ) = ⋃ q, C q`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, C]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨(QuotientGroup.mk (⟨x, hx⟩ : K) : K ⧸ L), ?_⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul L (⟨x, hx⟩ : K)`. Rewrite using `[hh]`.

Establish `: (((⟨x, hx⟩ : K) * (h : K) : K) : Γ)⁻¹ * x = ((h : K) : Γ)⁻¹`. Simplify using `[_root_.mul_inv_rev, mul_assoc]`. Rewrite using `[this]`. Conclude with `H.inv_mem (Subgroup.mem_subgroupOf.mp h.2)`. Introduce and unpack `⟨q, hq⟩`.

Establish `h1 : ((q.out : K) : Γ)⁻¹ * x ∈ K` using `hHK hq`. Establish `h2 : ((q.out : K) : Γ) ∈ K` using `(q.out : K).2`. Use `K.mul_mem h2 h1` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `hdisj : Pairwise (Function.onFun (AEDisjoint μ) C)`.

Introduce `q q' hqq'`. Apply `Disjoint.aedisjoint` to reduce the goal to its premises. Rewrite using `[Set.disjoint_left]`. Introduce `y hy hy'`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, C] at hy hy'`.

Apply `hqq'` to reduce the goal to its premises. Rewrite using `[← Quotient.out_eq q, ← Quotient.out_eq q']`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk q.out : K ⧸ L) = QuotientGroup.mk q'.out`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Use `H.mul_mem hy (H.inv_mem hy')` as an intermediate fact.

Simplify `this` using `[_root_.mul_inv_rev, mul_assoc]`. Establish `hnull : ∀ q, NullMeasurableSet (C q) μ` using `fun q => (hmeas _).nullMeasurableSet_preimage hH`. Establish `hsum : μ (K : Set Γ) = (Fintype.card (K ⧸ L) : ℝ≥0∞) * μ H`. Rewrite using `[hcov, measure_iUnion₀ hdisj hnull, tsum_fintype]`. Simplify using `[C, hpre, Finset.sum_const, nsmul_eq_mul]`.

Establish `hcard : (Fintype.card (K ⧸ L) : ℕ) = H.relIndex K`. Rewrite using `[Fintype.card_eq_nat_card]`. Both sides reduce to the same expression. Rewrite `hsum` using `[hK, hcard]`. Establish `hne : μ (H : Set Γ) ≠ ⊤`.

Introduce `h; rw [h, ENNReal.mul_top (by exact_mod_cast hn)] at hsum; exact ENNReal.one_ne_top hsum`. Establish `hr` using `congrArg ENNReal.toReal hsum`. Rewrite `hr` using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one]`. Establish `hpos : (μ (H : Set Γ)).toReal ≠ 0`. Introduce `h`.

Rewrite `hr` using `[h, mul_zero]`. Conclude with `one_ne_zero hr`. Clear the denominators using the available nonvanishing facts. Combine the linear relations using `[hr]`.
-/
theorem inv_toReal_eq_relIndex {Γ : Type*} [Group Γ] [MeasurableSpace Γ] (μ : Measure Γ) [μ.IsMulLeftInvariant]
    (K H : Subgroup Γ) (hHK : H ≤ K) (hH : MeasurableSet (H : Set Γ)) (hK : μ (K : Set Γ) = 1)
    (hn : H.relIndex K ≠ 0) : ((μ (H : Set Γ)).toReal)⁻¹ = (H.relIndex K : ℝ) := by
  have hμ : μ ≠ 0 := by
    intro h; rw [h] at hK; simp at hK
  have hmeas : ∀ g : Γ, AEMeasurable (fun x => g * x) μ := by
    intro g
    by_contra hg
    have h1 := Measure.map_of_not_aemeasurable hg
    rw [map_mul_left_eq_self μ g] at h1
    exact hμ h1
  have hpre : ∀ g : Γ, μ ((fun x => g * x) ⁻¹' (H : Set Γ)) = μ H := by
    intro g
    rw [← Measure.map_apply_of_aemeasurable (hmeas g) hH, map_mul_left_eq_self μ g]
  set L := H.subgroupOf K
  haveI : L.FiniteIndex := ⟨hn⟩
  haveI : Fintype (K ⧸ L) := Fintype.ofFinite _
  let C : (K ⧸ L) → Set Γ := fun q => (fun x => ((q.out : K) : Γ)⁻¹ * x) ⁻¹' (H : Set Γ)
  have hcov : (K : Set Γ) = ⋃ q, C q := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, C]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : K) : K ⧸ L), ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L (⟨x, hx⟩ : K)
      rw [hh]
      have : (((⟨x, hx⟩ : K) * (h : K) : K) : Γ)⁻¹ * x = ((h : K) : Γ)⁻¹ := by
        simp [_root_.mul_inv_rev, mul_assoc]
      rw [this]
      exact H.inv_mem (Subgroup.mem_subgroupOf.mp h.2)
    · rintro ⟨q, hq⟩
      have h1 : ((q.out : K) : Γ)⁻¹ * x ∈ K := hHK hq
      have h2 : ((q.out : K) : Γ) ∈ K := (q.out : K).2
      have := K.mul_mem h2 h1
      simpa [mul_assoc] using this
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) C) := by
    intro q q' hqq'
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro y hy hy'
    simp only [Set.mem_preimage, SetLike.mem_coe, C] at hy hy'
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change (QuotientGroup.mk q.out : K ⧸ L) = QuotientGroup.mk q'.out
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := H.mul_mem hy (H.inv_mem hy')
    simpa [_root_.mul_inv_rev, mul_assoc] using this
  have hnull : ∀ q, NullMeasurableSet (C q) μ := fun q =>
    (hmeas _).nullMeasurableSet_preimage hH
  have hsum : μ (K : Set Γ) = (Fintype.card (K ⧸ L) : ℝ≥0∞) * μ H := by
    rw [hcov, measure_iUnion₀ hdisj hnull, tsum_fintype]
    simp [C, hpre, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ L) : ℕ) = H.relIndex K := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hK, hcard] at hsum
  have hne : μ (H : Set Γ) ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by exact_mod_cast hn)] at hsum; exact ENNReal.one_ne_top hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hr
  have hpos : (μ (H : Set Γ)).toReal ≠ 0 := by
    intro h; rw [h, mul_zero] at hr; exact one_ne_zero hr
  field_simp
  linarith [hr]

end GlobalTheory.HaarIdx

namespace GlobalTheory

/- English proof (translation)
Introduce `D c v B PP G χ E j H hHK hH hn`. Use `haveI := (E.haar j).1`. Rewrite using `[HaarIdx.inv_toReal_eq_relIndex (E.m j) _ H hHK hH (E.haar j).2 hn]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem QTw.QExt.m_inv_toReal_eq_relIndex : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GlobalTheory.QTw.QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : GlobalTheory.QTw.QExt G χ) (j : ℕ) (H : Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)), H ≤ KO G.k _ → MeasurableSet (H : Set (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)) → H.relIndex (KO G.k _) ≠ 0 → ((((E.m j H).toReal)⁻¹ : ℝ) : ℂ) = (H.relIndex (KO G.k _) : ℂ) := by
  intro D c v B PP G χ E j H hHK hH hn
  haveI := (E.haar j).1
  rw [HaarIdx.inv_toReal_eq_relIndex (E.m j) _ H hHK hH (E.haar j).2 hn]
  push_cast
  rfl

end GlobalTheory
