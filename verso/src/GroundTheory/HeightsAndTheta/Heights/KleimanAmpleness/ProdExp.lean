import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistModNatMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

section Model

variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

/- English proof (translation)
Establish `h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)`. Rewrite using `[Finset.prod_eq_single k₀]`. Simplify using `[IndefiniteRowSideFullHecke.Kleiman2.baseDeg]`. Introduce `k _ hk`. Simplify using `[IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[h0, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]`.

Use `congr 1`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem TensorRealises.prod_exp (y : (Σ k, ι k) → Ω) (k₀ : K) (β β' : K → ℤ) (c d : ℤ)
    (cc : ∀ k, ι k) (hc : ∀ k, y ⟨k, cc k⟩ ≠ 0) :
    y ⟨k₀, cc k₀⟩ ^ (-d) * ((∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) *
        ∏ k, y ⟨k, cc k⟩ ^ (-(β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) =
      ∏ k, y ⟨k, cc k⟩ ^ (-(β + β' + (2 * c + d) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
  have h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    rw [Finset.prod_eq_single k₀]
    · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    · intro k _ hk
      simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Model

/- English proof (translation)
Introduce `F _ K _ _ ι _ Ω _ _ y k₀ N e hmod L L' β β' hL hL' ct`. Take `⟨a₀, ha₀⟩` from `Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L`. Take `⟨a₁, ha₁⟩` from `Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L'`. Take `⟨b₀, hb₀⟩` from `hG F K ι Ω y k₀ hmod β`. Take `⟨b₁, hb₁⟩` from `hG F K ι Ω y k₀ hmod β'`.

Take `⟨c, h0, h1, h2, h3⟩ : ∃ c, a₀ ≤ c ∧ a₁ ≤ c ∧ b₀ ≤ c ∧ b₁ ≤ c` from `⟨max (max a₀ a₁) (max b₀ b₁), by omega, by omega, by omega, by omega⟩`. Establish `hgL` using `ha₀ c h0`. Establish `hgL'` using `ha₁ c h1`. Establish `hgY` using `hb₀ c h2`. Establish `hgY'` using `hb₁ c h3`.

Take `⟨d, rfl⟩ : ∃ d, ct = 2 * c + d` from `⟨ct - 2 * c, by ring⟩`. Establish `hchart : ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm), ((L.tensor L').toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).sub I = Submodule.span (Kleiman.chartRing F (IndefiniteRowSid …`. Introduce `I`. Establish `e1 : (L.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I = Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.bas …`. Rewrite using `[← hgL I, hL c]`.

Establish `e2 : (L'.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I = Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.b …`. Rewrite using `[← hgL' I, hL' c]`. Rewrite `e1`, `e2` using `[PowRealises.twist_sub, PowRealises.twistSys_sub]`. Use `show ((L.toSubSystem.twist L'.toSubSystem).twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).sub I = _`. Rewrite using `[PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.twist_sub, ← Submodule.span_mul_span, ← e1, ← e2, two_mul, ← PowRealises.twistMod_mul, ← PowRealises.twistMod_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsecs : ((L.tensor L').toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).secs = ⨅ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm), (Submodule.span (Kleiman.chartRing F (IndefiniteRowSide …`. Simplify using `only [Kleiman.SubSystem.secs, hchart]`. Use extensionality with `s`. Rewrite using `[hsecs, hS F K ι Ω y k₀ N e _ rfl hmod _ d s, PowRealises.mem_secOver]`.

Use `forall_congr' fun cc => forall_congr' fun hc => ?_` and prove the remaining obligations. Establish `hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`. Establish `hu' : (∏ k, y ⟨k, cc k⟩ ^ (-(β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`. Rewrite using `[← Submodule.span_mul_span, PowRealises.span_secOver_eq y _ hgY cc hc, PowRealises.span_secOver_eq y _ hgY' cc hc, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_inv, PowRealises.mem_span_inv_iff _ (mul_ne_zero hu hu'), mul_assoc, TensorRealises.prod_exp y k₀ β β' c …`.
-/
theorem TensorRealises.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement) :
    TensorRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod L L' β β' hL hL' ct
  obtain ⟨a₀, ha₀⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L
  obtain ⟨a₁, ha₁⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L'
  obtain ⟨b₀, hb₀⟩ := hG F K ι Ω y k₀ hmod β
  obtain ⟨b₁, hb₁⟩ := hG F K ι Ω y k₀ hmod β'
  obtain ⟨c, h0, h1, h2, h3⟩ : ∃ c, a₀ ≤ c ∧ a₁ ≤ c ∧ b₀ ≤ c ∧ b₁ ≤ c :=
    ⟨max (max a₀ a₁) (max b₀ b₁), by omega, by omega, by omega, by omega⟩
  have hgL := ha₀ c h0
  have hgL' := ha₁ c h1
  have hgY := hb₀ c h2
  have hgY' := hb₁ c h3
  obtain ⟨d, rfl⟩ : ∃ d, ct = 2 * c + d := ⟨ct - 2 * c, by ring⟩
  have hchart : ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
      ((L.tensor L').toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
            ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) *
              (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) * Kleiman.twistMod F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) d I := by
    intro I
    have e1 : (L.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgL I, hL c]
    have e2 : (L'.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgL' I, hL' c]
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub] at e1 e2
    show ((L.toSubSystem.twist L'.toSubSystem).twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).sub I = _
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.twist_sub, ← Submodule.span_mul_span, ← e1,
      ← e2, two_mul, ← PowRealises.twistMod_mul, ← PowRealises.twistMod_mul]
    ring
  have hsecs : ((L.tensor L').toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).secs =
      ⨅ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm), (Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) *
            (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) *
          Kleiman.twistMod F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) d I).restrictScalars F := by
    simp only [Kleiman.SubSystem.secs, hchart]
  ext s
  rw [hsecs, hS F K ι Ω y k₀ N e _ rfl hmod _ d s, PowRealises.mem_secOver]
  refine forall_congr' fun cc => forall_congr' fun hc => ?_
  have hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hu' : (∏ k, y ⟨k, cc k⟩ ^ (-(β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  rw [← Submodule.span_mul_span, PowRealises.span_secOver_eq y _ hgY cc hc,
    PowRealises.span_secOver_eq y _ hgY' cc hc, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_inv,
    PowRealises.mem_span_inv_iff _ (mul_ne_zero hu hu'), mul_assoc, TensorRealises.prod_exp y k₀ β β' c d cc hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
