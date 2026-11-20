import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.ZeroLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.LevProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.SliceRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨e, he, -⟩` from `adMeas a b t`. Conclude with `⟨e.symm X, by rw [he, e.apply_symm_apply]⟩`.
-/
theorem lv_nn (a b : G1 K 2) (t : ℝ) (X : UPos (2 + 2) 2 → 𝔸[K]) : ∃ Y, lv a b t * nn X = nn Y * lv a b t := by
  obtain ⟨e, he, -⟩ := adMeas a b t
  exact ⟨e.symm X, by rw [he, e.apply_symm_apply]⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `h.decay 0`. Conclude with `⟨C, fun m => by simpa using hC m⟩`.
-/
theorem rd_bdd {μ₂ : Measure (G1 K 2)} {τ : Submodule ℂ (L2 μ₂)} {φ : G1 K 2 → ℂ} (h : Rd τ φ) : ∃ C : ℝ, ∀ m, ‖φ m‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.decay 0
  exact ⟨C, fun m => by simpa using hC m⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Measure.haarMeasure ⊤, ⟨by simpa using Measure.haarMeasure_self (G := U) (K₀ := ⊤)⟩, inferInstance⟩`.
-/
theorem ex_prob {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (U : Subgroup G)
    [CompactSpace U] : ∃ lam : Measure U, IsProbabilityMeasure lam ∧ lam.IsHaarMeasure :=
  ⟨Measure.haarMeasure ⊤, ⟨by simpa using Measure.haarMeasure_self (G := U) (K₀ := ⊤)⟩, inferInstance⟩

set_option maxHeartbeats 400000 in
/- English proof (translation)
Take `⟨S, π, hS, hπ, hmem, hval⟩` from `levProj (K := K)`. Establish `hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2)))` using `((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1`. Establish `hmul` using `(blkLaws (K := K)).2.1`. Use `haveI hc : CompactSpace (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) := isCompact_iff_compactSpace.1 (hK.inter_left hS)`. Use `haveI : SecondCountableTopology (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) := TopologicalSpace.Subtype.secondCountableTopology _`.

Take `⟨lam, hp, hl⟩` from `ex_prob (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2)))`. Establish `c₁` using `r₁.cont`. Establish `c₂` using `r₂.cont`. Take `⟨f, hf, hv⟩` from `indSec S (KG K (2 + 2)) hS hK (fun g => by`. Take `⟨X, a, b, t, k, hk, rfl⟩` from `iwa g`.

Conclude with `⟨_, (hmem _).2 ⟨X, a, b, t, rfl⟩, k, hk, rfl⟩) π hπ (fun m => φ₁ m.1 * φ₂ m.2) (by fun_prop) ψ hψ lam`. Use `set x : (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) → G1 K 2 × G1 K 2 := fun u => π ⟨u, u.2.1⟩ with hx`. Establish `hxc : Continuous x` using `hπ.comp (continuous_subtype_val.subtype_mk _)`. Establish `hv' : ∀ X a b t, ∀ k ∈ KG K (2 + 2), f (nn X * lv a b t * k) = ∫ u, φ₁ (a * (x u).1) * φ₂ (b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k) ∂lam`. Introduce `X a b t k hk`.

Use `hv ⟨_, (hmem _).2 ⟨X, a, b, t, rfl⟩⟩ k hk` as an intermediate fact. Rewrite `this` using `[hval X a b t _ rfl]`. Conclude with `this`. Establish `hF : D.Fix f`. Introduce `g`.

Take `⟨X, a, b, t, k, hk, rfl⟩` from `iwa g`. Take `⟨hU, hle, -⟩` from `typeFin D`. Use `haveI := D.prob`. Establish `hH : Continuous fun z : G1 K (2 + 2) × (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) => φ₁ (a * (x z.2).1) * φ₂ (b * (x z.2).2) * ψ ((z.2 : G1 K (2 + 2))⁻¹ * z.1)` using `((c₁.comp (continuous_const.mul (hxc.comp continuous_snd).fst)).mul (c₂.comp (continuous_const.mul (hxc.comp continuous_snd).snd))).mul (hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst))`. Use `fix_swap D.ν _ hU D.supp D.e D.cont lam _ hH (fun C hC => by` as an intermediate fact.

Take `⟨B, hB⟩` from `(hC.prod isCompact_univ).exists_bound_of_continuousOn hH.continuousOn`. Conclude with `⟨B, ae_of_all _ fun y z hz => hB (z, y) ⟨hz, trivial⟩⟩) k fun u => by`. Simplify using `only [← hfix ((u : G1 K (2 + 2))⁻¹ * k), ← integral_const_mul, mul_assoc]`. Conclude with `integral_congr_ae (ae_of_all _ fun h => by ring)`. Rewrite using `[hv' X a b t k hk, ← this]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [D.supp] with h hh`. Rewrite using `[mul_assoc, hv' X a b t _ (mul_mem hk (hle hh))]`. Take `⟨C₁, b₁⟩` from `rd_bdd r₁`. Take `⟨C₂, b₂⟩` from `rd_bdd r₂`.

Establish `hsl : ∀ m₁ m₂ X a b t, ∀ k ∈ KG K (2 + 2), f (lv m₁ m₂ 0 * (nn X * lv a b t * k)) = ∫ u, φ₁ (m₁ * a * (x u).1) * φ₂ (m₂ * b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k) ∂lam`. Introduce `m₁ m₂ X a b t k hk`. Take `⟨Y, hY⟩` from `lv_nn m₁ m₂ 0 X`. Rewrite using `[← mul_assoc, ← mul_assoc, hY, mul_assoc (nn Y), hmul, hv' _ _ _ _ k hk]`. Use `⟨_, hc, lam, hp, x, f, inf_le_right, hxc, fun u => ?_, (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hF).2 ⟨hf, ?_, fun Y g => ?_, fun s g => ?_, fun g => ?_⟩, hF, hv'⟩` and prove the remaining obligations.

Take `⟨X, a, b, t, e⟩` from `(hmem _).1 u.2.1`. Establish `h0` using `(hpSpec (K := K)).1 X a b t 1`. Rewrite `h0` using `[mul_one, ← e, ((hpSpec (K := K)).2.1 _ u.2.2).1, ((hpSpec (K := K)).2.1 _ (one_mem _)).1, add_zero]`. Substitute `h0` using the available equality. Establish `e2 : x u = (a, b)` using `hval X a b 0 _ e`.

Conclude with `⟨X, by rw [e2]; exact e⟩`. Take `⟨B, hB⟩` from `hK.exists_bound_of_continuousOn hψ.continuousOn`. Use `⟨C₁ * C₂ * B * lam.real univ, fun g => ?_⟩` and prove the remaining obligations. Take `⟨X, a, b, t, k, hk, rfl⟩` from `iwa g`. Rewrite using `[hv' X a b t k hk]`.

Use `norm_integral_le_of_norm_le_const (ae_of_all _ fun u => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`. Establish `h1` using `(norm_nonneg _).trans (b₁ 1)`. Conclude with `mul_le_mul (mul_le_mul (b₁ _) (b₂ _) (norm_nonneg _) h1) (hB _ (mul_mem (inv_mem u.2.2) hk)) (norm_nonneg _) (mul_nonneg h1 ((norm_nonneg _).trans (b₂ 1)))`. Take `⟨X, a, b, t, k, hk, rfl⟩` from `iwa g`.

Rewrite using `[← mul_assoc, ← mul_assoc, ← unipOne_add, hv' _ a b t k hk, hv' _ a b t k hk]`. Take `⟨X, a, b, t, k, hk, rfl⟩` from `iwa g`. Take `⟨Y, hY⟩` from `lv_nn 1 1 s X`. Rewrite using `[← mul_assoc, ← mul_assoc, hY, mul_assoc (nn Y), hmul, one_mul, one_mul, hv' _ _ _ _ k hk, hv' _ _ _ _ k hk]`. Take `⟨X, a, b, t, k, hk, rfl⟩` from `iwa g`.

Use `⟨fun m₂ => ?_, fun m₁ => ?_⟩` and prove the remaining obligations. Take `⟨v, hv, hr⟩` from `sliceRep μ₂ τ₁ h₁ φ₁ c₁ ⟨C₁, b₁⟩ r₁.rat r₁.rep _ lam (fun u => φ₂ (m₂ * b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k)) (fun u => a * (x u).1) ((c₂.comp (continuous_const.mul hxc.snd)).mul (hψ.comp (continuous_subtype_val.inv.mul continuous_const))) (continuous_const.mul hxc.fst)`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Simplify using `only [hsl _ _ X a b t k hk]`. Conclude with `hr.mono fun y hy => hy.trans (integral_congr_ae (ae_of_all _ fun u => by simp only [mul_assoc]; ring))`.

Take `⟨v, hv, hr⟩` from `sliceRep μ₂ τ₂ h₂ φ₂ c₂ ⟨C₂, b₂⟩ r₂.rat r₂.rep _ lam (fun u => φ₁ (m₁ * a * (x u).1) * ψ ((u : G1 K (2 + 2))⁻¹ * k)) (fun u => b * (x u).2) ((c₁.comp (continuous_const.mul hxc.fst)).mul (hψ.comp (continuous_subtype_val.inv.mul continuous_const))) (continuous_const.mul hxc.snd)`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Simplify using `only [hsl _ _ X a b t k hk]`. Conclude with `hr.mono fun y hy => hy.trans (integral_congr_ae (ae_of_all _ fun u => by simp only [mul_assoc]; ring))`.
-/
theorem secEx [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2))
    (h₁ : CuspIrr μ₂ τ₁) (h₂ : CuspIrr μ₂ τ₂) (φ₁ φ₂ : G1 K 2 → ℂ) (r₁ : Rd τ₁ φ₁) (r₂ : Rd τ₂ φ₂)
    (ψ : G1 K (2 + 2) → ℂ) (hψ : Continuous ψ) (hfix : D.Fix ψ) :
    ∃ (U : Subgroup (G1 K (2 + 2))) (_ : CompactSpace U) (lam : Measure U) (_ : IsProbabilityMeasure lam)
      (x : U → G1 K 2 × G1 K 2) (f : G1 K (2 + 2) → ℂ), U ≤ KG K (2 + 2) ∧ Continuous x ∧
      (∀ u : U, ∃ X, (u : G1 K (2 + 2)) = nn X * lv (x u).1 (x u).2 0) ∧ IsSec τ₁ τ₂ f ∧ D.Fix f ∧
      ∀ X a b t, ∀ k ∈ KG K (2 + 2),
        f (nn X * lv a b t * k) = ∫ u : U, φ₁ (a * (x u).1) * φ₂ (b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k) ∂lam := by
  obtain ⟨S, π, hS, hπ, hmem, hval⟩ := levProj (K := K)
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1
  have hmul := (blkLaws (K := K)).2.1
  haveI hc : CompactSpace (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) := isCompact_iff_compactSpace.1 (hK.inter_left hS)
  haveI : SecondCountableTopology (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨lam, hp, hl⟩ := ex_prob (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2)))
  have c₁ := r₁.cont
  have c₂ := r₂.cont
  obtain ⟨f, hf, hv⟩ := indSec S (KG K (2 + 2)) hS hK (fun g => by
    obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    exact ⟨_, (hmem _).2 ⟨X, a, b, t, rfl⟩, k, hk, rfl⟩) π hπ (fun m => φ₁ m.1 * φ₂ m.2) (by fun_prop) ψ hψ lam
  set x : (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) → G1 K 2 × G1 K 2 := fun u => π ⟨u, u.2.1⟩ with hx
  have hxc : Continuous x := hπ.comp (continuous_subtype_val.subtype_mk _)
  have hv' : ∀ X a b t, ∀ k ∈ KG K (2 + 2), f (nn X * lv a b t * k) =
      ∫ u, φ₁ (a * (x u).1) * φ₂ (b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k) ∂lam := by
    intro X a b t k hk
    have := hv ⟨_, (hmem _).2 ⟨X, a, b, t, rfl⟩⟩ k hk
    rw [hval X a b t _ rfl] at this
    exact this
  have hF : D.Fix f := by
    intro g
    obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    obtain ⟨hU, hle, -⟩ := typeFin D
    haveI := D.prob
    have hH : Continuous fun z : G1 K (2 + 2) × (S ⊓ KG K (2 + 2) : Subgroup (G1 K (2 + 2))) =>
        φ₁ (a * (x z.2).1) * φ₂ (b * (x z.2).2) * ψ ((z.2 : G1 K (2 + 2))⁻¹ * z.1) :=
      ((c₁.comp (continuous_const.mul (hxc.comp continuous_snd).fst)).mul (c₂.comp (continuous_const.mul (hxc.comp continuous_snd).snd))).mul
        (hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst))
    have := fix_swap D.ν _ hU D.supp D.e D.cont lam _ hH (fun C hC => by
      obtain ⟨B, hB⟩ := (hC.prod isCompact_univ).exists_bound_of_continuousOn hH.continuousOn
      exact ⟨B, ae_of_all _ fun y z hz => hB (z, y) ⟨hz, trivial⟩⟩) k fun u => by
        simp only [← hfix ((u : G1 K (2 + 2))⁻¹ * k), ← integral_const_mul, mul_assoc]
        exact integral_congr_ae (ae_of_all _ fun h => by ring)
    rw [hv' X a b t k hk, ← this]
    refine integral_congr_ae ?_
    filter_upwards [D.supp] with h hh
    rw [mul_assoc, hv' X a b t _ (mul_mem hk (hle hh))]
  obtain ⟨C₁, b₁⟩ := rd_bdd r₁
  obtain ⟨C₂, b₂⟩ := rd_bdd r₂
  have hsl : ∀ m₁ m₂ X a b t, ∀ k ∈ KG K (2 + 2), f (lv m₁ m₂ 0 * (nn X * lv a b t * k)) =
      ∫ u, φ₁ (m₁ * a * (x u).1) * φ₂ (m₂ * b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k) ∂lam := by
    intro m₁ m₂ X a b t k hk
    obtain ⟨Y, hY⟩ := lv_nn m₁ m₂ 0 X
    rw [← mul_assoc, ← mul_assoc, hY, mul_assoc (nn Y), hmul, hv' _ _ _ _ k hk]
  refine ⟨_, hc, lam, hp, x, f, inf_le_right, hxc, fun u => ?_,
    (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hF).2 ⟨hf, ?_, fun Y g => ?_, fun s g => ?_, fun g => ?_⟩, hF, hv'⟩
  · obtain ⟨X, a, b, t, e⟩ := (hmem _).1 u.2.1
    have h0 := (hpSpec (K := K)).1 X a b t 1
    rw [mul_one, ← e, ((hpSpec (K := K)).2.1 _ u.2.2).1, ((hpSpec (K := K)).2.1 _ (one_mem _)).1, add_zero] at h0
    subst h0
    have e2 : x u = (a, b) := hval X a b 0 _ e
    exact ⟨X, by rw [e2]; exact e⟩
  · obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hψ.continuousOn
    refine ⟨C₁ * C₂ * B * lam.real univ, fun g => ?_⟩
    obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    rw [hv' X a b t k hk]
    refine norm_integral_le_of_norm_le_const (ae_of_all _ fun u => ?_)
    rw [norm_mul, norm_mul]
    have h1 := (norm_nonneg _).trans (b₁ 1)
    exact mul_le_mul (mul_le_mul (b₁ _) (b₂ _) (norm_nonneg _) h1) (hB _ (mul_mem (inv_mem u.2.2) hk)) (norm_nonneg _)
      (mul_nonneg h1 ((norm_nonneg _).trans (b₂ 1)))
  · obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    rw [← mul_assoc, ← mul_assoc, ← unipOne_add, hv' _ a b t k hk, hv' _ a b t k hk]
  · obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    obtain ⟨Y, hY⟩ := lv_nn 1 1 s X
    rw [← mul_assoc, ← mul_assoc, hY, mul_assoc (nn Y), hmul, one_mul, one_mul, hv' _ _ _ _ k hk, hv' _ _ _ _ k hk]
  · obtain ⟨X, a, b, t, k, hk, rfl⟩ := iwa g
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨v, hv, hr⟩ := sliceRep μ₂ τ₁ h₁ φ₁ c₁ ⟨C₁, b₁⟩ r₁.rat r₁.rep _ lam
        (fun u => φ₂ (m₂ * b * (x u).2) * ψ ((u : G1 K (2 + 2))⁻¹ * k)) (fun u => a * (x u).1)
        ((c₂.comp (continuous_const.mul hxc.snd)).mul (hψ.comp (continuous_subtype_val.inv.mul continuous_const)))
        (continuous_const.mul hxc.fst)
      refine ⟨v, hv, ?_⟩
      simp only [hsl _ _ X a b t k hk]
      exact hr.mono fun y hy => hy.trans (integral_congr_ae (ae_of_all _ fun u => by simp only [mul_assoc]; ring))
    · obtain ⟨v, hv, hr⟩ := sliceRep μ₂ τ₂ h₂ φ₂ c₂ ⟨C₂, b₂⟩ r₂.rat r₂.rep _ lam
        (fun u => φ₁ (m₁ * a * (x u).1) * ψ ((u : G1 K (2 + 2))⁻¹ * k)) (fun u => b * (x u).2)
        ((c₁.comp (continuous_const.mul hxc.fst)).mul (hψ.comp (continuous_subtype_val.inv.mul continuous_const)))
        (continuous_const.mul hxc.snd)
      refine ⟨v, hv, ?_⟩
      simp only [hsl _ _ X a b t k hk]
      exact hr.mono fun y hy => hy.trans (integral_congr_ae (ae_of_all _ fun u => by simp only [mul_assoc]; ring))

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX
