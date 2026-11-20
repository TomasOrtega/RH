import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinset
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne

open Filter Topology

namespace GlobalTheory.CompanionTheory.TailProd

/- English proof (translation)
Introduce `S₁ S₂ h12`. Establish `hU : S ∪ S₁ ⊆ S ∪ S₂` using `Finset.union_subset_union_right h12`. Simplify using `only`. Rewrite using `[GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι τ (S ∪ S₁) (S ∪ S₂) hτ hU, GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι p (S ∪ S₁) (S ∪ S₂) hp hU]`. Establish `hX : ∏ v ∈ (S ∪ S₂) \ S, Mv v = (∏ v ∈ (S ∪ S₁) \ S, Mv v) * ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v`.

Establish `hD : ((S ∪ S₂) \ S) \ ((S ∪ S₁) \ S) = (S ∪ S₂) \ (S ∪ S₁)`. Use extensionality with `x`. Simplify using `only [Finset.mem_sdiff, Finset.mem_union]`. The claim follows by propositional logic. Rewrite using `[← Finset.prod_sdiff (Finset.sdiff_subset_sdiff hU (Finset.Subset.refl S)), hD, mul_comm]`.

Establish `hΔ : (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), τ v) * (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), p v) ≤ ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_le_prod (fun v _ => mul_nonneg (hτ0 v) (hp0 v)) (fun v hv => hle v (fun hvS => (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ hvS)))`. Establish `hX1 : 0 ≤ ∏ v ∈ (S ∪ S₁) \ S, Mv v` using `Finset.prod_nonneg fun v _ => hM0 v`. Establish `hT : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, τ v.1` using `(GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => τ v.1) (hτ.comp_injective Subtype.val_injective)).2.2.2 fun v => hτ0 v.1`.

Establish `hP : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, p v.1` using `(GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => p v.1) (hp.comp_injective Subtype.val_injective)).2.2.2 fun v => hp0 v.1`. Rewrite using `[hX]`. Use `set X := ∏ v ∈ (S ∪ S₁) \ S, Mv v`. Use `set D := (S ∪ S₂) \ (S ∪ S₁)`. Use `set T := ∏' v : {v // v ∉ S ∪ S₂}, τ v.1`.

Use `set P := ∏' v : {v // v ∉ S ∪ S₂}, p v.1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem term_mono {ι : Type} [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι)
    (hτ : Summable (fun v => |τ v - 1|)) (hp : Summable (fun v => |p v - 1|))
    (hM0 : ∀ v, 0 ≤ Mv v) (hτ0 : ∀ v, 0 ≤ τ v) (hp0 : ∀ v, 0 ≤ p v)
    (hle : ∀ v, v ∉ S → τ v * p v ≤ Mv v) :
    Monotone (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) := by
  intro S₁ S₂ h12
  have hU : S ∪ S₁ ⊆ S ∪ S₂ := Finset.union_subset_union_right h12
  dsimp only
  rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι τ (S ∪ S₁) (S ∪ S₂) hτ hU,
    GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι p (S ∪ S₁) (S ∪ S₂) hp hU]
  have hX : ∏ v ∈ (S ∪ S₂) \ S, Mv v =
      (∏ v ∈ (S ∪ S₁) \ S, Mv v) * ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    have hD : ((S ∪ S₂) \ S) \ ((S ∪ S₁) \ S) = (S ∪ S₂) \ (S ∪ S₁) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [← Finset.prod_sdiff (Finset.sdiff_subset_sdiff hU (Finset.Subset.refl S)), hD, mul_comm]
  have hΔ : (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), τ v) * (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), p v) ≤
      ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun v _ => mul_nonneg (hτ0 v) (hp0 v))
      (fun v hv => hle v (fun hvS => (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ hvS)))
  have hX1 : 0 ≤ ∏ v ∈ (S ∪ S₁) \ S, Mv v := Finset.prod_nonneg fun v _ => hM0 v
  have hT : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, τ v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => τ v.1)
      (hτ.comp_injective Subtype.val_injective)).2.2.2 fun v => hτ0 v.1
  have hP : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, p v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => p v.1)
      (hp.comp_injective Subtype.val_injective)).2.2.2 fun v => hp0 v.1
  rw [hX]
  set X := ∏ v ∈ (S ∪ S₁) \ S, Mv v
  set D := (S ∪ S₂) \ (S ∪ S₁)
  set T := ∏' v : {v // v ∉ S ∪ S₂}, τ v.1
  set P := ∏' v : {v // v ∉ S ∪ S₂}, p v.1
  calc X * ((∏ v ∈ D, τ v) * T * ((∏ v ∈ D, p v) * P))
      = X * ((∏ v ∈ D, τ v) * (∏ v ∈ D, p v)) * (T * P) := by ring
    _ ≤ X * (∏ v ∈ D, Mv v) * (T * P) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ hX1) (mul_nonneg hT hP)

/- English proof (translation)
Introduce `ι _ Mv τ p S hMs hτs hps hM0 hτ0 hp0 hle`. Establish `hmono` using `GlobalTheory.CompanionTheory.TailProd.term_mono Mv τ p S hτs hps hM0 hτ0 hp0 hle`. Establish `hg : Tendsto (fun S' : Finset ι => S ∪ S') atTop atTop` using `tendsto_atTop_mono (fun S' => (Finset.subset_union_right : S' ⊆ S ∪ S')) tendsto_id`. Establish `hM` using `(GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one Mv hMs).comp hg`. Establish `hT` using `(GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one τ hτs).comp hg`.

Establish `hP` using `(GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one p hps).comp hg`. Establish `hlim : Tendsto (fun S' : Finset ι => (∏' v : {v // v ∉ S}, Mv v.1) * ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * (∏' v : {v // v ∉ S ∪ S'}, p v.1) / ∏' v : {v // v ∉ S ∪ S'}, Mv v.1)) atTop (𝓝 (∏' v : {v // v ∉ S}, Mv v.1))`. Use `(tendsto_const_nhds (x := ∏' v : {v // v ∉ S}, Mv v.1)).mul ((hT.mul hP).div hM one_ne_zero)` as an intermediate fact. Simplify `this` using `only [Function.comp_def, Pi.div_apply, mul_one, div_one]`. Establish `hA : Tendsto (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) * ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) atTop (𝓝 (∏' v : {v // v ∉ S}, Mv v.1))`.

Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hM.eventually_ne one_ne_zero] with S' hS'`. Simplify using `only [Function.comp] at hS' ⊢`. Rewrite using `[GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι Mv S (S ∪ S') hMs Finset.subset_union_left, mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hS']`. Conclude with `iSup_eq_of_tendsto (fun a b h => ENNReal.ofReal_le_ofReal (hmono h)) ((ENNReal.continuous_ofReal.tendsto _).comp hA)`.
-/
theorem iSup_partial_mul_tails : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι),
    Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) →
    (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) →
    ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) =
      ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  intro ι _ Mv τ p S hMs hτs hps hM0 hτ0 hp0 hle
  have hmono := GlobalTheory.CompanionTheory.TailProd.term_mono Mv τ p S hτs hps hM0 hτ0 hp0 hle
  have hg : Tendsto (fun S' : Finset ι => S ∪ S') atTop atTop :=
    tendsto_atTop_mono (fun S' => (Finset.subset_union_right : S' ⊆ S ∪ S')) tendsto_id
  have hM := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one Mv hMs).comp hg
  have hT := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one τ hτs).comp hg
  have hP := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one p hps).comp hg
  have hlim : Tendsto (fun S' : Finset ι => (∏' v : {v // v ∉ S}, Mv v.1) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * (∏' v : {v // v ∉ S ∪ S'}, p v.1) /
        ∏' v : {v // v ∉ S ∪ S'}, Mv v.1)) atTop (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    have := (tendsto_const_nhds (x := ∏' v : {v // v ∉ S}, Mv v.1)).mul
      ((hT.mul hP).div hM one_ne_zero)
    simpa only [Function.comp_def, Pi.div_apply, mul_one, div_one] using this
  have hA : Tendsto (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) atTop
      (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    refine hlim.congr' ?_
    filter_upwards [hM.eventually_ne one_ne_zero] with S' hS'
    dsimp only [Function.comp] at hS' ⊢
    rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι Mv S (S ∪ S') hMs Finset.subset_union_left,
      mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hS']
  exact iSup_eq_of_tendsto (fun a b h => ENNReal.ofReal_le_ofReal (hmono h))
    ((ENNReal.continuous_ofReal.tendsto _).comp hA)

end GlobalTheory.CompanionTheory.TailProd
