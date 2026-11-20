import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

/- English proof (translation)
Take `⟨s, hs, -⟩` from `P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by`. Rewrite using `[map_zpow₀, hσ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])`. Conclude with `⟨s, hs⟩`.
-/
theorem exists_diag_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L}
    (hσ : σ ϖ = ϖ) (h0 : ϖ ≠ 0) {r : ℕ} (b : Fin r → ℤ) (hb : ∀ i, b i.rev = -b i) :
    ∃ s : GU σ r, mat s = Matrix.diagonal (fun i => ϖ ^ b i) := by
  obtain ⟨s, hs, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  exact ⟨s, hs⟩

/- English proof (translation)
Introduce `L _ _ ϖ σ q n r e β γ b B B' Q d t t' h hU hD hb hbd hB hB' hBB hd ht ht' hQ hidx hcar hh`. Establish `hv` using `hU.2.1`. Establish `hϖ : σ ϖ = ϖ` using `hU.2.2.1`. Establish `h0 : ϖ ≠ 0`. Introduce `h0`.

Use `hU.2.2.2.1` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe this`. Establish `hinj : Function.Injective e` using `hD.1.injective`. Take `⟨ι, hι⟩` from `hE L σ n r e hinj hD.2.1`.

Take `⟨s₀, hs₀⟩` from `exists_diag_zpow hϖ h0 b hb`. Take `⟨s, hs⟩` from `exists_diag_zpow hϖ h0 (fun i => B (e i)) (fun i => by rw [hD.2.1, hB])`. Take `⟨s', hs'⟩` from `exists_diag_zpow hϖ h0 (fun i => B' (e i)) (fun i => by rw [hD.2.1, hB'])`. Take `⟨z, hz, hz', hzc⟩` from `hT L σ n r e ι hinj hι (fun a => ϖ ^ B a) (fun a => ϖ ^ B' a) t t' s s' ht ht' hs hs' (fun a ha => by simp only [hBB a ha])`. Establish `hMem` using `hM L σ n r e β γ ι hv hD hι`.

Establish `hCon` using `fun g hg => hC L ϖ σ q r γ b s₀ g hU hbd hs₀ hg`. Establish `hnorm : s₀ ∈ Subgroup.normalizer ((rootU σ γ : Subgroup (GU σ r)) : Set (GU σ r))`. Rewrite using `[Subgroup.mem_normalizer_iff]`. Introduce `g`. Use `⟨fun hg => (hCon g hg).1, fun hg => ?_⟩` and prove the remaining obligations.

Use `(hCon _ hg).2.1` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Use `set c : MulAut (rootU σ γ) := (rootU σ γ).normalizerMonoidHom ⟨s₀, hnorm⟩ with hc`. Establish `hc1 : ∀ a, ((c a : rootU σ γ) : GU σ r) = s₀ * a * s₀⁻¹` using `fun a => rfl`. Establish `hcz : ∀ (j : ℤ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹` using `fun j a => by`.

Rewrite using `[hc, ← map_zpow, Subgroup.normalizerMonoidHom_apply_apply_coe]`. Simplify using the standard rewrite rules. Establish `hcn : ∀ (j : ℕ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹` using `fun j a => by`. Rewrite using `[hc, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe]`. Simplify using the standard rewrite rules.

Establish `hcomap : (KU σ n).comap (ι.comp (rootU σ γ).subtype) = (KU σ r ⊓ rootU σ γ).subgroupOf (rootU σ γ)`. Use extensionality with `a`. Rewrite using `[Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]`. Conclude with `⟨fun ha => ⟨(hMem a).1.1 ha, a.2⟩, fun ha => (hMem a).1.2 ha.1⟩`. Establish `hLR` using `hL L σ n β hv`.

Use `hR (GU σ n) (rootU σ γ) (KU σ n) (radU σ Fin.val) (radU σ β) (ι.comp (rootU σ γ).subtype) c Q d h t t' hh.1 (P.finite_supp (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) h hh) ?_ ?_ ?_ ?_ ?_ ?_ hQ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `u hu i j hij`. Conclude with `hu i j (hD.2.2.1 hij)`. Introduce `a`. Conclude with `(hMem a).2.2 a.2.1`.

Introduce `u hu`. Take `⟨a, ha, u', hu', e1⟩` from `hS L σ n r e β γ ι hD hι u hu`. Conclude with `⟨⟨a, ha⟩, u', hu', e1⟩`. Introduce `a u' hu'`. Conclude with `(hLR _ ((hMem a).2.1 a.2.2) u' hu').2`.

Introduce `a u' hu'`. Conclude with `(hLR _ ((hMem a).2.1 a.2.2) u' hu').1`. Introduce `a ha`. Conclude with `(hMem _).1.2 ((hCon a a.2).2.2.1 ((hMem a).1.1 ha))`. Rewrite using `[hcomap, ← Subgroup.relIndex_map_map_of_injective _ _ (rootU σ γ).subtype_injective, Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← hidx s₀ hs₀, Subgroup.map_map]`.

Use `congr 1`. Use `conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : KU σ r ⊓ rootU σ γ ≤ _), Subgroup.map_map]`. Both sides reduce to the same expression. Introduce `a`. Take `⟨j, hj⟩` from `(hCon a a.2).2.2.2`.

Use `⟨j, (hMem _).1.2 ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[← hcn]`. Conclude with `hj`. Introduce `a`. Establish `e1` using `hJ L ϖ σ r γ b (fun i => B' (e i)) d s₀ s' a h0 hd hs₀ hs' a.2.2`.

Use `show t' * ι a * t'⁻¹ = ι ((c ^ d) a : rootU σ γ)`. Rewrite using `[hcz, ← e1, hz', map_mul, map_mul, map_inv, mul_assoc (ι s'), (hzc a).eq]`. Use `group`. Introduce `a`. Take `⟨k₁, hk₁, k₂, hk₂, e1⟩` from `hcar s s' hs hs' a a.2`.

Establish `hk : ι k₂ ∈ leviU σ β` using `(hMem _).2.1 hk₂.2`. Use `⟨ι k₁, (hMem _).1.2 hk₁, ι k₂, (hMem _).1.2 hk₂.1, fun u hu => (hLR _ hk u hu).1, fun u hu => ?_, ?_⟩` and prove the remaining obligations. Simplify using `using (hLR _ (inv_mem hk) u hu).1`. Use `show (ι a)⁻¹ * t' = ι k₁ * (t * ι a) * ι k₂`. Establish `e2` using `congrArg ι e1`.

Simplify using `only [map_mul, map_inv] at e2`. Rewrite using `[hz, hz', ← mul_assoc, e2, mul_assoc (ι s), (hzc a).eq]`. Simplify using `only [mul_assoc]`. Rewrite using `[(hzc k₂).eq]`.
-/
theorem leviStep_of_steps (hR : RankOne) (hE : EmbExists) (hM : EmbMem) (hT : EmbTorus) (hL : LeviRad)
    (hS : UnipSplit) (hC : Contract) (hJ : TorusConj) : LeviStep := by
  intro L _ _ ϖ σ q n r e β γ b B B' Q d t t' h hU hD hb hbd hB hB' hBB hd ht ht' hQ hidx hcar hh
  have hv := hU.2.1
  have hϖ : σ ϖ = ϖ := hU.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h0
    have := hU.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hinj : Function.Injective e := hD.1.injective
  obtain ⟨ι, hι⟩ := hE L σ n r e hinj hD.2.1
  obtain ⟨s₀, hs₀⟩ := exists_diag_zpow hϖ h0 b hb
  obtain ⟨s, hs⟩ := exists_diag_zpow hϖ h0 (fun i => B (e i)) (fun i => by rw [hD.2.1, hB])
  obtain ⟨s', hs'⟩ := exists_diag_zpow hϖ h0 (fun i => B' (e i)) (fun i => by rw [hD.2.1, hB'])
  obtain ⟨z, hz, hz', hzc⟩ := hT L σ n r e ι hinj hι (fun a => ϖ ^ B a) (fun a => ϖ ^ B' a) t t' s s' ht ht' hs hs'
    (fun a ha => by simp only [hBB a ha])
  have hMem := hM L σ n r e β γ ι hv hD hι
  have hCon := fun g hg => hC L ϖ σ q r γ b s₀ g hU hbd hs₀ hg
  have hnorm : s₀ ∈ Subgroup.normalizer ((rootU σ γ : Subgroup (GU σ r)) : Set (GU σ r)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => (hCon g hg).1, fun hg => ?_⟩
    have := (hCon _ hg).2.1
    simpa [mul_assoc] using this
  set c : MulAut (rootU σ γ) := (rootU σ γ).normalizerMonoidHom ⟨s₀, hnorm⟩ with hc
  have hc1 : ∀ a, ((c a : rootU σ γ) : GU σ r) = s₀ * a * s₀⁻¹ := fun a => rfl
  have hcz : ∀ (j : ℤ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹ := fun j a => by
    rw [hc, ← map_zpow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcn : ∀ (j : ℕ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹ := fun j a => by
    rw [hc, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcomap : (KU σ n).comap (ι.comp (rootU σ γ).subtype) = (KU σ r ⊓ rootU σ γ).subgroupOf (rootU σ γ) := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun ha => ⟨(hMem a).1.1 ha, a.2⟩, fun ha => (hMem a).1.2 ha.1⟩
  have hLR := hL L σ n β hv
  refine hR (GU σ n) (rootU σ γ) (KU σ n) (radU σ Fin.val) (radU σ β) (ι.comp (rootU σ γ).subtype) c Q d h t t'
    hh.1 (P.finite_supp (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) h hh) ?_ ?_ ?_ ?_ ?_ ?_ hQ ?_ ?_ ?_ ?_
  · intro u hu i j hij
    exact hu i j (hD.2.2.1 hij)
  · intro a
    exact (hMem a).2.2 a.2.1
  · intro u hu
    obtain ⟨a, ha, u', hu', e1⟩ := hS L σ n r e β γ ι hD hι u hu
    exact ⟨⟨a, ha⟩, u', hu', e1⟩
  · intro a u' hu'
    exact (hLR _ ((hMem a).2.1 a.2.2) u' hu').2
  · intro a u' hu'
    exact (hLR _ ((hMem a).2.1 a.2.2) u' hu').1
  · intro a ha
    exact (hMem _).1.2 ((hCon a a.2).2.2.1 ((hMem a).1.1 ha))
  · rw [hcomap, ← Subgroup.relIndex_map_map_of_injective _ _ (rootU σ γ).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← hidx s₀ hs₀, Subgroup.map_map]
    congr 1
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : KU σ r ⊓ rootU σ γ ≤ _), Subgroup.map_map]
    rfl
  · intro a
    obtain ⟨j, hj⟩ := (hCon a a.2).2.2.2
    refine ⟨j, (hMem _).1.2 ?_⟩
    rw [← hcn] at hj
    exact hj
  · intro a
    have e1 := hJ L ϖ σ r γ b (fun i => B' (e i)) d s₀ s' a h0 hd hs₀ hs' a.2.2
    show t' * ι a * t'⁻¹ = ι ((c ^ d) a : rootU σ γ)
    rw [hcz, ← e1, hz', map_mul, map_mul, map_inv, mul_assoc (ι s'), (hzc a).eq]
    group
  · intro a
    obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hcar s s' hs hs' a a.2
    have hk : ι k₂ ∈ leviU σ β := (hMem _).2.1 hk₂.2
    refine ⟨ι k₁, (hMem _).1.2 hk₁, ι k₂, (hMem _).1.2 hk₂.1, fun u hu => (hLR _ hk u hu).1, fun u hu => ?_, ?_⟩
    · simpa using (hLR _ (inv_mem hk) u hu).1
    · show (ι a)⁻¹ * t' = ι k₁ * (t * ι a) * ι k₂
      have e2 := congrArg ι e1
      simp only [map_mul, map_inv] at e2
      rw [hz, hz', ← mul_assoc, e2, mul_assoc (ι s), (hzc a).eq]
      simp only [mul_assoc]
      rw [(hzc k₂).eq]

end GlobalTheory.SatakeWeyl
