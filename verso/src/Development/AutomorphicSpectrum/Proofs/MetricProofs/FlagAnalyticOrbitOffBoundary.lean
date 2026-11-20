import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `ho`. Establish `hP : (∏ k, ‖c k‖ ^ A.a k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))`. Rewrite using `[A.smul c z' hc, B.smul c z' hc, ← hab, Real.log_mul hP (A.pos z' hz').ne', Real.log_mul hP (B.pos z' hz').ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_h_sub_eq_of_sameOrbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (ho : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  have hP : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A.smul c z' hc, B.smul c z' hc, ← hab, Real.log_mul hP (A.pos z' hz').ne',
    Real.log_mul hP (B.pos z' hz').ne']
  ring

/- English proof (translation)
Introduce `hz`. Simplify using `only [mcPts, Set.mem_ofPred_eq] at hz`. Establish `h1` using `hz.2 1 Submodule.mem_top`. Simplify using `at h1`.
-/
theorem exactLine_not_mem_mcPts_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz
  have h1 := hz.2 1 Submodule.mem_top
  simp at h1

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `ho`. Conclude with `⟨fun k => c k.1, fun k => hc k.1, rfl⟩`.
-/
theorem exactLine_basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l x₀ z₀ b p hm hb hx hbase hex hbd hdet`. Establish `hsymm : ∀ {K' : Type} {ι' : K' → Type} {u v : (Σ k, ι' k) → ℂ}, SameOrbit u v → SameOrbit v u`. Introduce `K' ι' u v h`. Take `⟨c, hc, rfl⟩` from `h`. Conclude with `⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k),`.

Use function extensionality and compare the values at `fun q => (inv_mul_cancel_left₀ (hc q.1) (v q)).symm⟩`. Establish `htrans : ∀ {K' : Type} {ι' : K' → Type} {u v w : (Σ k, ι' k) → ℂ}, SameOrbit u v → SameOrbit v w → SameOrbit u w`. Introduce `K' ι' u v w h h'`. Take `⟨c, hc, rfl⟩` from `h`. Take `⟨e, he, rfl⟩` from `h'`.

Conclude with `⟨fun k => c k * e k, fun k => mul_ne_zero (hc k) (he k),`. Use function extensionality and compare the values at `fun q => (mul_assoc _ _ _).symm⟩`. Establish `hmemx : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y)` using `FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)`. Establish `hmem : z₀ ∈ mcPts (mCoordIdeal y)` using `ReciprocityTheory.ChartRestriction.G.Geo.mem_mcPts_of_sameOrbit (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) (hsymm hx) hmemx`. Establish `hpr : FA.pr (FA.Re.π x₀) = b`.

Apply `BM.Rb.inj` to reduce the goal to its premises. Conclude with `exactLine_not_mem_mcPts_top _`. Conclude with `htrans (hsymm (FA.pr_eq x₀)) (htrans (exactLine_basePart_orbit M.blk hx) hbase)`. Establish `hopen : FA.Re.π x₀ ∈ FA.S.open'` using `by show FA.Re.π x₀ ∈ (bdry FA.S.s)ᶜ`. Rewrite using `[Set.mem_compl_iff]`.

Introduce `h`. Apply `hb.2` to reduce the goal to its premises. Establish `h' : FA.S.s (FA.Re.π x₀) (FA.Re.π x₀) = 0` using `h`. Simplify using `only [FA.s_eq, hpr] at h'`. Use `show BM.s b b = 0`.

Conclude with `h'`. Establish `hhom` using `FA.hom_eq p x₀ hopen`. Rewrite `hhom` using `[FA.ref_some p]`. Establish `hz0 : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0` using `hmem.1`. Establish `hsub` using `log_h_sub_eq_of_sameOrbit (BM.hom p) (fsHerm ι (M.dy p)) (BM.hom_deg p) hz0 hx`.

Establish `hind` using `BM.induced l b hb p z₀ hmem hbase hex.1 hm hbd hdet`. Establish `hval : valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b) = valAt M.x ((BM.F l).υ p) (basePart M.blk z₀)` using `valAt_eq_of_sameOrbit _ _ _ M.x _ _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) (hsymm hbase)`. Unfold `potAt upsLogAt upsVal`. Distinguish the cases in `hblk : M.blk p = none`. Establish `h1` using `hind.2 hblk`.

Rewrite using `[if_pos hblk, hval]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨k, hk⟩` from `Option.ne_none_iff_exists'.mp hblk`. Establish `h1` using `hind.1 k hk (hex.2 k hk)`. Rewrite using `[if_neg hblk, sub_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_fsHerm_add_ph_eq_potAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x₀ : FA.Re.R.X) (z₀ : (Σ k, ι k) → ℂ) (b : BM.Rb.X) (p : Ψ × Fin N) (hm : Matrix (Fin N) (Fin N) ℂ), b ∈ BM.O l \ bdry BM.s → SameOrbit (FA.Re.R.lift x₀ x₀) z₀ → SameOrbit (basePart M.blk z₀) (BM.Rb.lift b b) → M.ExactAt (BM.F l) p z₀ hm → IsBlockDiag j hm → hm.det ≠ 0 → Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (FA.Re.π x₀) = potAt BM l p b hm := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l x₀ z₀ b p hm hb hx hbase hex hbd hdet
  have hsymm : ∀ {K' : Type} {ι' : K' → Type} {u v : (Σ k, ι' k) → ℂ}, SameOrbit u v → SameOrbit v u := by
    intro K' ι' u v h
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k),
      funext fun q => (inv_mul_cancel_left₀ (hc q.1) (v q)).symm⟩
  have htrans : ∀ {K' : Type} {ι' : K' → Type} {u v w : (Σ k, ι' k) → ℂ},
      SameOrbit u v → SameOrbit v w → SameOrbit u w := by
    intro K' ι' u v w h h'
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨e, he, rfl⟩ := h'
    exact ⟨fun k => c k * e k, fun k => mul_ne_zero (hc k) (he k),
      funext fun q => (mul_assoc _ _ _).symm⟩
  have hmemx : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)
  have hmem : z₀ ∈ mcPts (mCoordIdeal y) :=
    ReciprocityTheory.ChartRestriction.G.Geo.mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) (hsymm hx) hmemx
  have hpr : FA.pr (FA.Re.π x₀) = b := by
    apply BM.Rb.inj
    · exact exactLine_not_mem_mcPts_top _
    · exact htrans (hsymm (FA.pr_eq x₀)) (htrans (exactLine_basePart_orbit M.blk hx) hbase)
  have hopen : FA.Re.π x₀ ∈ FA.S.open' := by
    show FA.Re.π x₀ ∈ (bdry FA.S.s)ᶜ
    rw [Set.mem_compl_iff]
    intro h
    apply hb.2
    have h' : FA.S.s (FA.Re.π x₀) (FA.Re.π x₀) = 0 := h
    simp only [FA.s_eq, hpr] at h'
    show BM.s b b = 0
    exact h'
  have hhom := FA.hom_eq p x₀ hopen
  rw [FA.ref_some p] at hhom
  have hz0 : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0 := hmem.1
  have hsub := log_h_sub_eq_of_sameOrbit (BM.hom p) (fsHerm ι (M.dy p)) (BM.hom_deg p) hz0 hx
  have hind := BM.induced l b hb p z₀ hmem hbase hex.1 hm hbd hdet
  have hval : valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b) = valAt M.x ((BM.F l).υ p) (basePart M.blk z₀) :=
    valAt_eq_of_sameOrbit _ _ _ M.x _ _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) (hsymm hbase)
  unfold potAt upsLogAt upsVal
  by_cases hblk : M.blk p = none
  · have h1 := hind.2 hblk
    rw [if_pos hblk, hval]
    linarith
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hblk
    have h1 := hind.1 k hk (hex.2 k hk)
    rw [if_neg hblk, sub_zero]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
