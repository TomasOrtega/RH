import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace VeryAmpleZChartSpan

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chart_smul {I : Chart x} (a : chartRing S x I) (e : E) : a • e = (a : Ω) • e := rfl

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact one_mem_twistMod_zero I`. Consider the case `insert l T hl ih`. Rewrite using `[Finset.prod_insert hl, Finset.card_insert_of_notMem hl]`. Conclude with `Submodule.subset_span ⟨h l, (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp (hh l) I), _, ih, rfl⟩`.
-/
theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    exact Submodule.subset_span
      ⟨h l, (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp (hh l) I), _, ih, rfl⟩

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ∈ Submodule.span _ _ at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨q, hq, y', hy', rfl⟩` from `hz`. Take `⟨a, -, ha⟩` from `Submodule.mem_span_finset.mp (hg hy')`.

Use `⟨fun y => (a y : Ω) * q, fun y _ => ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem (Q.sub I) (a y) hq` as an intermediate fact. Rewrite `this` using `[chartRing_smul_def]`. Then use the resulting hypothesis. Rewrite using `[← ha, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations.

Rewrite using `[chart_smul, smul_smul, mul_comm]`. Consider the case `zero => exact ⟨0, fun _ _ => Submodule.zero_mem _, by simp⟩`. Consider the case `add z z' _ _ ih ih'`. Take `⟨γ, hγ, rfl⟩` from `ih`. Take `⟨γ', hγ', rfl⟩` from `ih'`.

Use `⟨γ + γ', fun y hy => Submodule.add_mem _ (hγ y hy) (hγ' y hy), ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]`. Consider the case `smul a z _ ih`. Take `⟨γ, hγ, rfl⟩` from `ih`.

Use `⟨fun y => (a : Ω) * γ y, fun y hy => ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem (Q.sub I) a (hγ y hy)` as an intermediate fact. Rewrite `this` using `[chartRing_smul_def]`. Then use the resulting hypothesis. Rewrite using `[chart_smul, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => by rw [smul_smul]`.
-/
theorem exists_coeff_of_mem_twist (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x) (g : Finset E)
    (hg : F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E)) {z : E} (hz : z ∈ (F.twist Q).sub I) :
    ∃ γ : E → Ω, (∀ y ∈ g, γ y ∈ Q.sub I) ∧ z = ∑ y ∈ g, γ y • y := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, y', hy', rfl⟩ := hz
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.mp (hg hy')
    refine ⟨fun y => (a y : Ω) * q, fun y _ => ?_, ?_⟩
    · have := Submodule.smul_mem (Q.sub I) (a y) hq
      rwa [chartRing_smul_def] at this
    · rw [← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [chart_smul, smul_smul, mul_comm]
  | zero => exact ⟨0, fun _ _ => Submodule.zero_mem _, by simp⟩
  | add z z' _ _ ih ih' =>
    obtain ⟨γ, hγ, rfl⟩ := ih
    obtain ⟨γ', hγ', rfl⟩ := ih'
    refine ⟨γ + γ', fun y hy => Submodule.add_mem _ (hγ y hy) (hγ' y hy), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]
  | smul a z _ ih =>
    obtain ⟨γ, hγ, rfl⟩ := ih
    refine ⟨fun y => (a : Ω) * γ y, fun y hy => ?_, ?_⟩
    · have := Submodule.smul_mem (Q.sub I) a (hγ y hy)
      rwa [chartRing_smul_def] at this
    · rw [chart_smul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [smul_smul]

/- English proof (translation)
Introduce `S _ Ω _ _ N x E _ _ _ _ F H r h hh I J g hg e he`. Establish `hJ : xProd J ∈ (H.pow J.1.card).sub I` using `prod_mem_pow H I hh J.1`. Establish `h0 : xProd J ≠ 0` using `AmpleAffineGen.xProd_ne_zero J`. Establish `memB : ∀ {a : Ω}, a ∈ ampleChart H J.1.card (xProd J) I → a ∈ AmpleAffineGen.ampleSubalg H J.1.card (xProd J) I hJ` using `fun ha => ha`. Express the relevant statement in the definitionally equal form `e ∈ Submodule.span S _ at he`.

Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem e he`. Take `⟨n, hn⟩` from `he`. Take `⟨γ, hγ, hz⟩` from `exists_coeff_of_mem_twist F _ I g hg hn`. Establish `hp : xProd J ^ n ≠ 0` using `pow_ne_zero n h0`.

Use `⟨fun y => γ y / xProd J ^ n, fun y hy => ⟨n, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_cancel₀ _ hp]`. Conclude with `hγ y hy`. Establish `he' : e = (xProd J ^ n)⁻¹ • (xProd J ^ n • e)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hp, one_smul]`.

Rewrite using `[he', hz, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => by show _ = (γ y / xProd J ^ n) • y`. Rewrite using `[smul_smul, div_eq_inv_mul]`. Consider the case `zero`. Use `⟨0, fun _ _ => ⟨0, ?_⟩, by simp⟩` and prove the remaining obligations.

Rewrite using `[Pi.zero_apply, zero_mul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add e e' _ _ ih ih'`. Take `⟨β, hβ, rfl⟩` from `ih`. Take `⟨β', hβ', rfl⟩` from `ih'`.

Use `⟨β + β', fun y hy => Subalgebra.add_mem _ (memB (hβ y hy)) (memB (hβ' y hy)), ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]`. Consider the case `smul s e _ ih`. Take `⟨β, hβ, rfl⟩` from `ih`.

Use `⟨fun y => algebraMap S Ω s * β y, fun y hy => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ s) (memB (hβ y hy)), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => by rw [← smul_assoc, Algebra.smul_def]`.
-/
theorem proof : VeryAmpleZChartSpan.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh I J g hg e he
  have hJ : xProd J ∈ (H.pow J.1.card).sub I := prod_mem_pow H I hh J.1
  have h0 : xProd J ≠ 0 := AmpleAffineGen.xProd_ne_zero J
  have memB : ∀ {a : Ω}, a ∈ ampleChart H J.1.card (xProd J) I →
      a ∈ AmpleAffineGen.ampleSubalg H J.1.card (xProd J) I hJ := fun ha => ha
  change e ∈ Submodule.span S _ at he
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨n, hn⟩ := he
    obtain ⟨γ, hγ, hz⟩ := exists_coeff_of_mem_twist F _ I g hg hn
    have hp : xProd J ^ n ≠ 0 := pow_ne_zero n h0
    refine ⟨fun y => γ y / xProd J ^ n, fun y hy => ⟨n, ?_⟩, ?_⟩
    · rw [div_mul_cancel₀ _ hp]; exact hγ y hy
    · have he' : e = (xProd J ^ n)⁻¹ • (xProd J ^ n • e) := by
        rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
      rw [he', hz, Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => by
        show _ = (γ y / xProd J ^ n) • y
        rw [smul_smul, div_eq_inv_mul]
  | zero =>
    refine ⟨0, fun _ _ => ⟨0, ?_⟩, by simp⟩
    rw [Pi.zero_apply, zero_mul]; exact Submodule.zero_mem _
  | add e e' _ _ ih ih' =>
    obtain ⟨β, hβ, rfl⟩ := ih
    obtain ⟨β', hβ', rfl⟩ := ih'
    refine ⟨β + β', fun y hy => Subalgebra.add_mem _ (memB (hβ y hy)) (memB (hβ' y hy)), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]
  | smul s e _ ih =>
    obtain ⟨β, hβ, rfl⟩ := ih
    refine ⟨fun y => algebraMap S Ω s * β y,
      fun y hy => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ s) (memB (hβ y hy)), ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [← smul_assoc, Algebra.smul_def]

end VeryAmpleZChartSpan

end

end GroundTheory.Heights₂.Heights.Kleiman
