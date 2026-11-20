import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasConstTermConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.RankRed

/- English proof (translation)
Introduce `F E _ _ _ _ _ ψ hψ κ₁ κ _ _ j hj d q hq0 hsurj hrat Φ hΦ`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Establish `hqc : Continuous q` using `IsModuleTopology.continuous_of_linearMap q`. Use `haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable`.

Set `emb : (κ₁ → F) → (κ → F)` to `fun y => Function.extend j y 0`. Establish `hemb : Function.Injective emb` using `fun a b h => by`. Use function extensionality and compare the values at `i`. Use `congrFun h (j i)` as an intermediate fact. Simplify `this` using `[emb, hj.extend_apply]`.

Set `S : Set (κ → F)` to `Set.range emb`. Set `cst : (κ → F) → (κ → AF F)` to `fun ξ i => algebraMap F (AF F) (ξ i)`. Set `lin : (κ → F) → (Fin d → AE F E) →+ AF F` to `fun ξ => AddMonoidHom.mk' (fun z => cst ξ ⬝ᵥ q z) (fun a b => by simp [map_add, dotProduct_add])`. Set `χ : ↥Sᶜ → AddChar (Fin d → AE F E) ℂ` to `fun ξ => ψ.compAddMonoidHom (lin ξ.1)`. Establish `hχ : ∀ ξ z, χ ξ z = ψ (cst ξ.1 ⬝ᵥ q z)` using `fun _ _ => rfl`.

Set `a : ↥Sᶜ → ℂ` to `fun ξ => Φ (cst ξ.1)`. Establish `hext : ∀ y : κ₁ → F, cst (emb y) = Function.extend j (fun i => algebraMap F (AF F) (y i)) 0` using `fun y => by`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : ∃ i, j i = k`. Take `⟨i, rfl⟩` from `hk`.

Simplify using `[cst, emb, hj.extend_apply]`. Simplify using `[cst, emb, Function.extend_apply' _ _ _ hk]`. Establish `hdot : ∀ (v : κ₁ → AF F) (w : κ → AF F), (∀ k, w (j k) = 0) → Function.extend j v 0 ⬝ᵥ w = 0`. Introduce `v w hw`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : ∃ i, j i = k`. Take `⟨i, rfl⟩` from `hk`. Simplify using `[hw]`. Simplify using `[Function.extend_apply' _ _ _ hk]`. Use `⟨↥Sᶜ, a, χ, inferInstance, (summable_norm_of_mem_schA F hΦ).subtype Sᶜ, fun ξ => ⟨?_, ?_, ?_, ?_⟩, fun z => ?_⟩` and prove the remaining obligations.

Conclude with `hψ.1.comp (continuous_const.dotProduct hqc)`. Introduce `z`. Rewrite using `[hχ]`. Conclude with `GlobalTheory.StdCharFromIsStd.norm_psi hψ _`. Introduce and unpack `z ⟨w, rfl⟩`.

Take `⟨y, hy⟩` from `hrat w`. Rewrite using `[hχ, hy]`. Establish `: cst ξ.1 ⬝ᵥ (fun k => algebraMap F (AF F) (y k)) = algebraMap F (AF F) (ξ.1 ⬝ᵥ y)`. Simplify using `[dotProduct, cst, map_sum, map_mul]`. Rewrite using `[this]`.

Conclude with `hψ.2.1 _`. Introduce `h`. Choose the witnesses or unpack the hypotheses as in `⟨k₀, hk₀, hξk₀⟩ : ∃ k₀, (¬∃ i, j i = k₀) ∧ ξ.1 k₀ ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Apply `ξ.2` to reduce the goal to its premises. Use `⟨ξ.1 ∘ j, funext fun k => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : ∃ i, j i = k`. Take `⟨i, rfl⟩` from `hk`. Simplify using `[emb, hj.extend_apply]`.

Simplify using `only [emb, Function.extend_apply' _ _ _ hk]`. Conclude with `(hc k (not_exists.mp hk)).symm`. Take `⟨t, ht⟩` from `GlobalTheory.StdCharFromIsStd.exists_ne_one hψ`. Set `η : κ → AF F` to `Pi.single k₀ (algebraMap F (AF F) (ξ.1 k₀)⁻¹ * t)`. Establish `hη : ∀ k, η (j k) = 0` using `fun k => by`.

Simplify using `only [η]`. Rewrite using `[Pi.single_apply, if_neg (fun h' => hk₀ ⟨k, h'⟩)]`. Take `⟨z, hz⟩` from `hsurj η hη`. Establish `h1` using `DFunLike.congr_fun h z`. Rewrite `h1` using `[hχ, hz, AddChar.one_apply]`.

Apply `ht` to reduce the goal to its premises. Rewrite using `[← h1]`. Simplify using `only [η, dotProduct_single, cst]`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hξk₀, map_one, one_mul]`. Set `g : (κ → F) → ℂ` to `fun ξ => schr ψ (0, q z) Φ (cst ξ)`.

Establish `hg : ∀ ξ, g ξ = ψ (cst ξ ⬝ᵥ q z) * Φ (cst ξ)` using `fun ξ => by`. Simplify using `[g, schr]`. Establish `hsg : Summable g`. Use `Summable.of_norm ((summable_norm_of_mem_schA F hΦ).congr fun ξ => ?_)` and prove the remaining obligations. Rewrite using `[hg, norm_mul, GlobalTheory.StdCharFromIsStd.norm_psi hψ, one_mul]`.

Use `show ∑' ξ : κ → F, g ξ = _`. Rewrite using `[← hsg.tsum_subtype_add_tsum_subtype_compl S]`. Use `congr 1`. Rewrite using `[tsum_range g hemb]`. Unfold `thetaSum`.

Use `tsum_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[hg, hext, hdot _ _ (hq0 z), AddChar.map_zero_eq_one, one_mul]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[hg, hχ, mul_comm]`.
-/
theorem hasConstTerm_thetaSum_schr_lin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ₁ κ : Type) [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ (d : ℕ) (q : (Fin d → AE F E) →ₗ[AF F] (κ → AF F)), (∀ z k, q z (j k) = 0) →
    (∀ η : κ → AF F, (∀ k, η (j k) = 0) → ∃ z, q z = η) →
    (∀ z : Fin d → E, ∃ y : κ → F, q (incV F z) = fun k => algebraMap F (AF F) (y k)) →
    ∀ Φ ∈ schA F κ, GlobalTheory.ThK.RankRed.HasConstTerm (Set.range (incV F : (Fin d → E) → Fin d → AE F E))
      (fun z => thetaSum F (schr ψ (0, q z) Φ)) (thetaSum F (fun y : κ₁ → AF F => Φ (Function.extend j y 0))) := by
  intro F E _ _ _ _ _ ψ hψ κ₁ κ _ _ j hj d q hq0 hsurj hrat Φ hΦ
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hqc : Continuous q := IsModuleTopology.continuous_of_linearMap q
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let emb : (κ₁ → F) → (κ → F) := fun y => Function.extend j y 0
  have hemb : Function.Injective emb := fun a b h => by
    funext i
    have := congrFun h (j i)
    simpa [emb, hj.extend_apply] using this
  let S : Set (κ → F) := Set.range emb
  let cst : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i)
  let lin : (κ → F) → (Fin d → AE F E) →+ AF F := fun ξ =>
    AddMonoidHom.mk' (fun z => cst ξ ⬝ᵥ q z) (fun a b => by simp [map_add, dotProduct_add])
  let χ : ↥Sᶜ → AddChar (Fin d → AE F E) ℂ := fun ξ => ψ.compAddMonoidHom (lin ξ.1)
  have hχ : ∀ ξ z, χ ξ z = ψ (cst ξ.1 ⬝ᵥ q z) := fun _ _ => rfl
  let a : ↥Sᶜ → ℂ := fun ξ => Φ (cst ξ.1)
  have hext : ∀ y : κ₁ → F, cst (emb y) = Function.extend j (fun i => algebraMap F (AF F) (y i)) 0 := fun y => by
    funext k
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simp [cst, emb, hj.extend_apply]
    · simp [cst, emb, Function.extend_apply' _ _ _ hk]
  have hdot : ∀ (v : κ₁ → AF F) (w : κ → AF F), (∀ k, w (j k) = 0) → Function.extend j v 0 ⬝ᵥ w = 0 := by
    intro v w hw
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simp [hw]
    · simp [Function.extend_apply' _ _ _ hk]
  refine ⟨↥Sᶜ, a, χ, inferInstance, (summable_norm_of_mem_schA F hΦ).subtype Sᶜ, fun ξ => ⟨?_, ?_, ?_, ?_⟩, fun z => ?_⟩
  · exact hψ.1.comp (continuous_const.dotProduct hqc)
  · intro z
    rw [hχ]
    exact GlobalTheory.StdCharFromIsStd.norm_psi hψ _
  · rintro z ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := hrat w
    rw [hχ, hy]
    have : cst ξ.1 ⬝ᵥ (fun k => algebraMap F (AF F) (y k)) = algebraMap F (AF F) (ξ.1 ⬝ᵥ y) := by
      simp [dotProduct, cst, map_sum, map_mul]
    rw [this]
    exact hψ.2.1 _
  · intro h
    obtain ⟨k₀, hk₀, hξk₀⟩ : ∃ k₀, (¬∃ i, j i = k₀) ∧ ξ.1 k₀ ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply ξ.2
      refine ⟨ξ.1 ∘ j, funext fun k => ?_⟩
      by_cases hk : ∃ i, j i = k
      · obtain ⟨i, rfl⟩ := hk
        simp [emb, hj.extend_apply]
      · simp only [emb, Function.extend_apply' _ _ _ hk]
        exact (hc k (not_exists.mp hk)).symm
    obtain ⟨t, ht⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
    let η : κ → AF F := Pi.single k₀ (algebraMap F (AF F) (ξ.1 k₀)⁻¹ * t)
    have hη : ∀ k, η (j k) = 0 := fun k => by
      simp only [η]
      rw [Pi.single_apply, if_neg (fun h' => hk₀ ⟨k, h'⟩)]
    obtain ⟨z, hz⟩ := hsurj η hη
    have h1 := DFunLike.congr_fun h z
    rw [hχ, hz, AddChar.one_apply] at h1
    apply ht
    rw [← h1]
    simp only [η, dotProduct_single, cst]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hξk₀, map_one, one_mul]
  · let g : (κ → F) → ℂ := fun ξ => schr ψ (0, q z) Φ (cst ξ)
    have hg : ∀ ξ, g ξ = ψ (cst ξ ⬝ᵥ q z) * Φ (cst ξ) := fun ξ => by
      simp [g, schr]
    have hsg : Summable g := by
      refine Summable.of_norm ((summable_norm_of_mem_schA F hΦ).congr fun ξ => ?_)
      rw [hg, norm_mul, GlobalTheory.StdCharFromIsStd.norm_psi hψ, one_mul]
    show ∑' ξ : κ → F, g ξ = _
    rw [← hsg.tsum_subtype_add_tsum_subtype_compl S]
    congr 1
    · rw [tsum_range g hemb]
      unfold thetaSum
      refine tsum_congr fun y => ?_
      rw [hg, hext, hdot _ _ (hq0 z), AddChar.map_zero_eq_one, one_mul]
    · refine tsum_congr fun ξ => ?_
      rw [hg, hχ, mul_comm]

end GlobalTheory.ThK.RankRed
