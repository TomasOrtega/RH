import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulOfSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocFlat.ContrSum

open GlobalTheory.LocFlat.CFac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h : Matrix.GeneralLinearGroup.det (colE c p β) = 1`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[colE, upU, Matrix.GeneralLinearGroup.val_det_apply]`. Use function extensionality and compare the values at `x`. Simplify using `only [om, h, map_one]`.
-/
theorem om_colE_indep {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ)
    (μ : kˣ →* ℂˣ) (β : n → k) (Φ : Matrix (n ⊕ Fin c) n' k → ℂ) :
    om μ 1 (colE c p β) Φ = om 1 1 (colE c p β) Φ := by
  have h : Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
    apply Units.ext
    simp [colE, upU, Matrix.GeneralLinearGroup.val_det_apply]
  funext x
  simp only [om, h, map_one]

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Use `Function.LeftInverse.isClosedEmbedding (f := fun z : Matrix n (n' ⊕ Unit) k => (z.toCols₁, fun r => -z r (Sum.inr ()))) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨x, β⟩`. Simplify using the standard rewrite rules. Conclude with `(continuous_matrix fun r s => continuous_id.matrix_elem _ _).prodMk (continuous_pi fun r => (continuous_id.matrix_elem _ _).neg)`.

Use `continuous_matrix fun r s => ?_` and prove the remaining obligations. Break down `s with s | s` into its components or cases. Conclude with `continuous_fst.matrix_elem _ _`. Conclude with `((continuous_apply r).comp continuous_snd).neg`.
-/
theorem isClosedEmbedding_negCol (n n' : Type) :
    Topology.IsClosedEmbedding fun q : Matrix n n' k × (n → k) =>
      (fromCols q.1 (Matrix.of fun r (_ : Unit) => (-q.2) r) : Matrix n (n' ⊕ Unit) k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z : Matrix n (n' ⊕ Unit) k => (z.toCols₁, fun r => -z r (Sum.inr ()))) ?_ ?_ ?_
  · rintro ⟨x, β⟩
    simp
  · exact (continuous_matrix fun r s => continuous_id.matrix_elem _ _).prodMk
      (continuous_pi fun r => (continuous_id.matrix_elem _ _).neg)
  · refine continuous_matrix fun r s => ?_
    rcases s with s | s
    · exact continuous_fst.matrix_elem _ _
    · exact ((continuous_apply r).comp continuous_snd).neg

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Use `Function.LeftInverse.isClosedEmbedding (f := fun z : Matrix (n ⊕ Unit) n' k => (z.toRows₁, z (Sum.inr ()))) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨x, u⟩`. Both sides reduce to the same expression. Conclude with `(continuous_matrix fun r s => continuous_id.matrix_elem _ _).prodMk (continuous_pi fun s => continuous_id.matrix_elem _ _)`.

Use `continuous_matrix fun r s => ?_` and prove the remaining obligations. Break down `r with r | r` into its components or cases. Conclude with `continuous_fst.matrix_elem _ _`. Conclude with `(continuous_apply s).comp continuous_snd`.
-/
theorem isClosedEmbedding_row (n n' : Type) :
    Topology.IsClosedEmbedding fun q : Matrix n n' k × (n' → k) =>
      (fromRows q.1 (Matrix.of fun (_ : Unit) => q.2) : Matrix (n ⊕ Unit) n' k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z : Matrix (n ⊕ Unit) n' k => (z.toRows₁, z (Sum.inr ()))) ?_ ?_ ?_
  · rintro ⟨x, u⟩
    rfl
  · exact (continuous_matrix fun r s => continuous_id.matrix_elem _ _).prodMk
      (continuous_pi fun s => continuous_id.matrix_elem _ _)
  · refine continuous_matrix fun r s => ?_
    rcases r with r | r
    · exact continuous_fst.matrix_elem _ _
    · exact (continuous_apply s).comp continuous_snd

/- English proof (translation)
Use `haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k`. Use `haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by`. Take `⟨s, hs⟩` from `GlobalTheory.SplitWeil.exists_cball_subset hV`. Conclude with `⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩, GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩`. Use `haveI : TotallyDisconnectedSpace k := inferInstance`.

Use `haveI : TotallyDisconnectedSpace (Matrix n n' k) := inferInstanceAs (TotallyDisconnectedSpace (n → n' → k))`. Use `haveI : LocallyCompactSpace (Matrix n n' k) := inferInstanceAs (LocallyCompactSpace (n → n' → k))`. Use `haveI : T2Space (Matrix n n' k) := inferInstanceAs (T2Space (n → n' → k))`. Establish `hmem : F ∈ Submodule.span ℂ (Set.range fun q : SB (Matrix n n' k) × SB (m' → k) => prodSB q.1 q.2)`. Rewrite using `[Span.span_prodSB_eq_top]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨N, f, q, hq⟩` from `Submodule.mem_span_set'.mp hmem`. Use `choose p hp using fun i => (q i).2`. Use `⟨N, fun i => f i • (p i).1, fun i => (p i).2, fun x β => ?_⟩` and prove the remaining obligations. Rewrite using `[← hq, Submodule.coe_sum, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hp i]`. Simplify using `only [prodSB_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem exists_sum_prod (n n' m' : Type) [Fintype n] [Fintype n'] [Fintype m']
    (F : SB (Matrix n n' k × (m' → k))) :
    ∃ (m : ℕ) (Ψ : Fin m → SB (Matrix n n' k)) (Φ₀ : Fin m → SB (m' → k)),
      ∀ x β, F.1 (x, β) = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix n n' k) := inferInstanceAs (TotallyDisconnectedSpace (n → n' → k))
  haveI : LocallyCompactSpace (Matrix n n' k) := inferInstanceAs (LocallyCompactSpace (n → n' → k))
  haveI : T2Space (Matrix n n' k) := inferInstanceAs (T2Space (n → n' → k))
  have hmem : F ∈ Submodule.span ℂ
      (Set.range fun q : SB (Matrix n n' k) × SB (m' → k) => prodSB q.1 q.2) := by
    rw [Span.span_prodSB_eq_top]; trivial
  obtain ⟨N, f, q, hq⟩ := Submodule.mem_span_set'.mp hmem
  choose p hp using fun i => (q i).2
  refine ⟨N, fun i => f i • (p i).1, fun i => (p i).2, fun x β => ?_⟩
  rw [← hq, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hp i]
  simp only [prodSB_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Establish `h` using `(((GlobalTheory.RootEx.FourierJacobi.fourierJacobiBessel k).2.2.2.1 n n' c ρ h1 hc).2.2.2 ψ ν hψ hne hν).1 1 continuous_const Φ β`. Establish `h2` using `h.2 x`. Unfold `fl at h2 ⊢`. Rewrite using `[om_colE_indep, h2]`. Both sides reduce to the same expression.
-/
theorem fl_eq_flCol (ψ : AddChar k Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1) (ν : Measure k) (hν : IsSelfDual ψ ν)
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (h1 : 1 ≤ ρ) (hc : c = 2 * ρ)
    (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x : Matrix n n' k) (β : n → k) :
    fl ψ ν μ ρ Φ.1 x β = flCol ψ ν (ρ + 1) Φ.1 (fromCols x (Matrix.of fun r (_ : Unit) => (-β) r)) := by
  have h := (((GlobalTheory.RootEx.FourierJacobi.fourierJacobiBessel k).2.2.2.1 n n' c ρ h1 hc).2.2.2 ψ ν hψ hne hν).1
    1 continuous_const Φ β
  have h2 := h.2 x
  unfold fl at h2 ⊢
  rw [om_colE_indep, h2]
  rfl

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ψ hψ hne ν hν n₀ _ _ n₁ _ _ n₂ _ _ c ρ hc μ Φ₁ Φ₂`. Use `haveI := hν.1`. Use `haveI := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Use `haveI : T2Space (Matrix n₂ n₁ k) := inferInstanceAs (T2Space (n₂ → n₁ → k))`.

Use `haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular ν`. Establish `h1 : 1 ≤ ρ` using `by omega`. Establish `hA` using `((flat_SB_onto k ψ ν hψ hν.1 n₁ n₀ (c + 1) (ρ + 1) (by omega)).1 (by omega)).1 _ Φ₁.2`. Establish `hB` using `((flat_SB_onto k ψ ν hψ hν.1 n₂ n₁ c ρ h1).2 (by omega)).1 _ Φ₂.2`. Establish `hfl` using `fl_eq_flCol ψ hψ hne ν hν (c + 1) ρ h1 hc μ Φ₁`.

Establish `hG : (fun q : Matrix n₂ n₁ k × (n₁ → k) => flRow ψ ν ρ Φ₂.1 (fromRows q.1 (Matrix.of fun (_ : Unit) => q.2))) ∈ SB _` using `⟨hB.1.comp_continuous (isClosedEmbedding_row n₂ n₁).continuous, hB.2.comp_isClosedEmbedding (isClosedEmbedding_row n₂ n₁)⟩`. Establish `hE : ∀ (Φ₀ : (n₁ → k) → ℂ) (x : Matrix n₂ n₁ k), opEFJ ψ ν ρ Φ₀ Φ₂.1 x = ∫ u, flRow ψ ν ρ Φ₂.1 (fromRows x (Matrix.of fun (_ : Unit) => u)) * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀ u ∂(Measure.pi fun _ => ν)`. Introduce `Φ₀ x`. Unfold `opEFJ`. Use `congr 1`.

Use function extensionality and compare the values at `u`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Use `⟨hA, hB, fun Φ₀ => ?_, ?_, fun m Ψ Φ₀ hd x => ?_⟩` and prove the remaining obligations. Rewrite using `[funext (hE Φ₀.1)]`.

Conclude with `integral_mul_mem_SB _ _ hG _`. Take `⟨m, Ψ, Φ₀, h⟩` from `exists_sum_prod n₁ n₀ n₁ ⟨_, hA.1.comp_continuous (isClosedEmbedding_negCol n₁ n₀).continuous, hA.2.comp_isClosedEmbedding (isClosedEmbedding_negCol n₁ n₀)⟩`. Conclude with `⟨m, Ψ, Φ₀, fun x β => (hfl x β).trans (h x β)⟩`. Take `⟨c₀, hc₀⟩` from `(conductor_exists k).1 ψ hψ hne`. Establish `hhat : ∀ u, GlobalTheory.StepData.hat ψ ν (-1) (fun y => flCol ψ ν (ρ + 1) Φ₁.1 (fromCols x.1 (Matrix.of fun r (_ : Unit) => y r))) u = ∑ i, (Ψ i).1 x.1 * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 u`.

Introduce `u`. Unfold `GlobalTheory.StepData.hat GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat`. Rewrite using `[← integral_neg_eq_self]`. Simplify using `only [← hfl, hd, dotProduct_neg, neg_mul_neg, one_mul, Finset.sum_mul, mul_assoc]`. Rewrite using `[integral_finset_sum]`.

Simplify using `only [integral_const_mul]`. Introduce `i _`. Use `GlobalTheory.StepData.integrable_hat ψ ν 1 hψ (Φ₀ i).2 u` as an intermediate fact. Simplify using `only [one_mul] at this`. Conclude with `this.const_mul _`.

Unfold `contr`. Simplify using `only [hhat, hE, Finset.mul_sum]`. Rewrite using `[integral_finset_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `u`. Expand and normalize the polynomial expressions, which then agree. Introduce `i _`. Establish `hF` using `FourierPi.fourier_mem_SB (Measure.pi fun _ : n₁ => ν) hc₀ (Φ₀ i).2`.

Establish `hF' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 ∈ SB (n₁ → k)`. Use `hF using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm]`. Use `Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.mul_left hF'.2.mul_left)` and prove the remaining obligations.

Conclude with `(hG.1.continuous.comp (Continuous.prodMk_right x.2)).mul (continuous_const.mul hF'.1.continuous)`.
-/
theorem contr_flat_eq_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Measure k, IsSelfDual ψ ν → ∀ (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ), c + 1 = 2 * ρ → ∀ (μ : kˣ →* ℂˣ) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁.1 ∈ SB (Matrix n₁ (n₀ ⊕ Unit) k) ∧ GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂.1 ∈ SB (Matrix (n₂ ⊕ Unit) n₁ k) ∧ (∀ Φ₀ : SB (n₁ → k), opEFJ ψ ν ρ Φ₀.1 Φ₂.1 ∈ SB (Matrix n₂ n₁ k)) ∧ (∃ (m : ℕ) (Ψ : Fin m → SB (Matrix n₁ n₀ k)) (Φ₀ : Fin m → SB (n₁ → k)), ∀ x β, fl ψ ν μ ρ Φ₁.1 x β = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β) ∧ ∀ (m : ℕ) (Ψ : Fin m → SB (Matrix n₁ n₀ k)) (Φ₀ : Fin m → SB (n₁ → k)), (∀ x β, fl ψ ν μ ρ Φ₁.1 x β = ∑ i, (Ψ i).1 x * (Φ₀ i).1 β) → ∀ x, GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂.1) x = ∑ i, (Ψ i).1 x.1 * opEFJ ψ ν ρ (Φ₀ i).1 Φ₂.1 x.2 := by
  intro k _ _ _ _ _ _ ψ hψ hne ν hν n₀ _ _ n₁ _ _ n₂ _ _ c ρ hc μ Φ₁ Φ₂
  haveI := hν.1
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : T2Space (Matrix n₂ n₁ k) := inferInstanceAs (T2Space (n₂ → n₁ → k))
  haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular ν
  have h1 : 1 ≤ ρ := by omega
  have hA := ((flat_SB_onto k ψ ν hψ hν.1 n₁ n₀ (c + 1) (ρ + 1) (by omega)).1 (by omega)).1 _ Φ₁.2
  have hB := ((flat_SB_onto k ψ ν hψ hν.1 n₂ n₁ c ρ h1).2 (by omega)).1 _ Φ₂.2
  have hfl := fl_eq_flCol ψ hψ hne ν hν (c + 1) ρ h1 hc μ Φ₁
  have hG : (fun q : Matrix n₂ n₁ k × (n₁ → k) =>
      flRow ψ ν ρ Φ₂.1 (fromRows q.1 (Matrix.of fun (_ : Unit) => q.2))) ∈ SB _ :=
    ⟨hB.1.comp_continuous (isClosedEmbedding_row n₂ n₁).continuous,
      hB.2.comp_isClosedEmbedding (isClosedEmbedding_row n₂ n₁)⟩
  have hE : ∀ (Φ₀ : (n₁ → k) → ℂ) (x : Matrix n₂ n₁ k), opEFJ ψ ν ρ Φ₀ Φ₂.1 x =
      ∫ u, flRow ψ ν ρ Φ₂.1 (fromRows x (Matrix.of fun (_ : Unit) => u)) * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀ u
        ∂(Measure.pi fun _ => ν) := by
    intro Φ₀ x
    unfold opEFJ
    congr 1
    funext u
    rw [mul_comm]
    rfl
  refine ⟨hA, hB, fun Φ₀ => ?_, ?_, fun m Ψ Φ₀ hd x => ?_⟩
  · rw [funext (hE Φ₀.1)]
    exact integral_mul_mem_SB _ _ hG _
  · obtain ⟨m, Ψ, Φ₀, h⟩ := exists_sum_prod n₁ n₀ n₁
      ⟨_, hA.1.comp_continuous (isClosedEmbedding_negCol n₁ n₀).continuous,
        hA.2.comp_isClosedEmbedding (isClosedEmbedding_negCol n₁ n₀)⟩
    exact ⟨m, Ψ, Φ₀, fun x β => (hfl x β).trans (h x β)⟩
  · obtain ⟨c₀, hc₀⟩ := (conductor_exists k).1 ψ hψ hne
    have hhat : ∀ u, GlobalTheory.StepData.hat ψ ν (-1)
        (fun y => flCol ψ ν (ρ + 1) Φ₁.1 (fromCols x.1 (Matrix.of fun r (_ : Unit) => y r))) u =
        ∑ i, (Ψ i).1 x.1 * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 u := by
      intro u
      unfold GlobalTheory.StepData.hat GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat
      rw [← integral_neg_eq_self]
      simp only [← hfl, hd, dotProduct_neg, neg_mul_neg, one_mul, Finset.sum_mul, mul_assoc]
      rw [integral_finset_sum]
      · simp only [integral_const_mul]
      · intro i _
        have := GlobalTheory.StepData.integrable_hat ψ ν 1 hψ (Φ₀ i).2 u
        simp only [one_mul] at this
        exact this.const_mul _
    unfold contr
    simp only [hhat, hE, Finset.mul_sum]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      congr 1
      funext u
      ring
    · intro i _
      have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n₁ => ν) hc₀ (Φ₀ i).2
      have hF' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 ∈ SB (n₁ → k) := by
        convert hF using 1
        funext u
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm]
      refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.mul_left hF'.2.mul_left)
      exact (hG.1.continuous.comp (Continuous.prodMk_right x.2)).mul (continuous_const.mul hF'.1.continuous)

end GlobalTheory.LocFlat.ContrSum
