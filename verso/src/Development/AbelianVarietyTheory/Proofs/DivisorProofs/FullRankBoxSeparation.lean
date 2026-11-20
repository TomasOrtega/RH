import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.RankCoinv.OffDiagAssemble

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `⟨GlobalTheory.RankCoinv.boxFn_mem_SB ϖ c _, fun Y hY => ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.RankCoinv.boxFn`. Use `Set.indicator_of_notMem (fun hmem => hc ?_) _` and prove the remaining obligations. Rewrite using `[← hval Y hmem]`. Conclude with `hΨ.2 Y hY`.
-/
theorem boxFn_mem_fullRk {n d : ℕ} (ϖ : kˣ) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d) {c : Matrix (Fin n) (Fin d) k} {m : ℕ} (hc : Ψ c ≠ 0)
    (hval : ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Ψ X = Ψ c) :
    GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
  refine ⟨GlobalTheory.RankCoinv.boxFn_mem_SB ϖ c _, fun Y hY => ?_⟩
  unfold GlobalTheory.RankCoinv.boxFn
  refine Set.indicator_of_notMem (fun hmem => hc ?_) _
  rw [← hval Y hmem]
  exact hΨ.2 Y hY

/- English proof (translation)
Take `⟨m₁, hm₁⟩` from `GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn k (Fin n) (Fin d) ϖ hϖ Ψ.1 Ψ.2.1`. Use `⟨m₁, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨s, hsum, hval⟩` from `hm₁ m hm`. Set `g : Matrix (Fin n) (Fin d) k → GlobalTheory.FullRankCoinv.fullRk k n d` to `fun c => if h : Ψ.1 c ≠ 0 ∧ ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Ψ.1 X = Ψ.1 c then ⟨_, boxFn_mem_fullRk ϖ Ψ.2 h.1 h.2⟩ else 0`. Use `⟨s, g, ?_, fun c hc => ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Use `conv_lhs => rw [hsum]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul]`.

Distinguish the cases in `h0 : Ψ.1 c = 0`. Simplify using `[h0]`. Establish `h : Ψ.1 c ≠ 0 ∧ ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Ψ.1 X = Ψ.1 c` using `⟨h0, hval c hc⟩`. Simplify using `only [g, dif_pos h]`. Distinguish the cases in `h : Ψ.1 c ≠ 0 ∧ ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Ψ.1 X = Ψ.1 c`.

Conclude with `Or.inr ⟨h.1, by simp only [g, dif_pos h]⟩`. Conclude with `Or.inl (by simp only [g, dif_neg h])`.
-/
theorem exists_sum_fullRk {n d : ℕ} {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (Ψ : GlobalTheory.FullRankCoinv.fullRk k n d) :
    ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ (s : Finset (Matrix (Fin n) (Fin d) k))
      (g : Matrix (Fin n) (Fin d) k → GlobalTheory.FullRankCoinv.fullRk k n d),
      Ψ = ∑ c ∈ s, Ψ.1 c • g c ∧
      ∀ c ∈ s, g c = 0 ∨ (Ψ.1 c ≠ 0 ∧ (g c).1 = GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m)) := by
  classical
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.RankCoinv.Decomp.exists_sum_boxFn k (Fin n) (Fin d) ϖ hϖ Ψ.1 Ψ.2.1
  refine ⟨m₁, fun m hm => ?_⟩
  obtain ⟨s, hsum, hval⟩ := hm₁ m hm
  let g : Matrix (Fin n) (Fin d) k → GlobalTheory.FullRankCoinv.fullRk k n d := fun c =>
    if h : Ψ.1 c ≠ 0 ∧ ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Ψ.1 X = Ψ.1 c then
      ⟨_, boxFn_mem_fullRk ϖ Ψ.2 h.1 h.2⟩ else 0
  refine ⟨s, g, ?_, fun c hc => ?_⟩
  · apply Subtype.ext
    rw [Submodule.coe_sum]
    conv_lhs => rw [hsum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Submodule.coe_smul]
    by_cases h0 : Ψ.1 c = 0
    · simp [h0]
    · have h : Ψ.1 c ≠ 0 ∧ ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Ψ.1 X = Ψ.1 c := ⟨h0, hval c hc⟩
      simp only [g, dif_pos h]
  · by_cases h : Ψ.1 c ≠ 0 ∧ ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Ψ.1 X = Ψ.1 c
    · exact Or.inr ⟨h.1, by simp only [g, dif_pos h]⟩
    · exact Or.inl (by simp only [g, dif_neg h])

/- English proof (translation)
Introduce `k _ _ _ _ n d ϖ hϖ Bf hloc Ψ₁ Ψ₂ hsep`. Establish `hsuppc : ∀ Ψ : GlobalTheory.FullRankCoinv.fullRk k n d, IsCompact (Function.support Ψ.1)`. Introduce `Ψ`. Take `⟨hlc, hcs⟩` from `Ψ.2.1`. Establish `hcl : IsClosed (Function.support Ψ.1)`.

Use `(hlc.isOpen_fiber 0).isClosed_compl` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `Y`. Simplify using the standard rewrite rules. Conclude with `hcs.of_isClosed_subset hcl (subset_tsupport _)`.

Establish `hrank : ∀ Ψ : GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y, Ψ.1 Y ≠ 0 → Y.rank = n`. Introduce `Ψ Y hY`. Assume the negation of the conclusion as `h`. Conclude with `hY (Ψ.2.2 Y h)`. Establish `hN : ∀ p ∈ Function.support Ψ₁.1 ×ˢ Function.support Ψ₂.1, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Z₁ ∈ GlobalTheory.RankCoinv.box ϖ p.1 (fun _ => N₀), ∀ Z₂ ∈ GlobalTheory.RankCoinv.box ϖ p.2 (fun _ => N₀), ∀ Φ₁ Φ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, Φ₁.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₁ …`.

Introduce and unpack `⟨Y₁, Y₂⟩ ⟨h₁, h₂⟩`. Conclude with `hloc Y₁ Y₂ (hrank Ψ₁ Y₁ h₁) (hrank Ψ₂ Y₂ h₂) (hsep Y₁ Y₂ h₁ h₂)`. Use `choose! N hN using hN`. Take `⟨b, hbS, hbfin, hcov⟩` from `((hsuppc Ψ₁).prod (hsuppc Ψ₂)).elim_finite_subcover_image (b := Function.support Ψ₁.1 ×ˢ Function.support Ψ₂.1) (c := fun p => GlobalTheory.RankCoinv.box ϖ p.1 (fun _ => N p) ×ˢ GlobalTheory.RankCoinv.box ϖ p.2 (fun _ => N p)) (fun p _ => (GlobalTheory.RankCoinv.isClopen_box ϖ _ …`. Take `⟨m₁, hm₁⟩` from `exists_sum_fullRk hϖ Ψ₁`.

Take `⟨m₂, hm₂⟩` from `exists_sum_fullRk hϖ Ψ₂`. Take `⟨s₁, g₁, hsum₁, hg₁⟩` from `hm₁ (max (max m₁ m₂) (hbfin.toFinset.sup N)) (by omega)`. Take `⟨s₂, g₂, hsum₂, hg₂⟩` from `hm₂ (max (max m₁ m₂) (hbfin.toFinset.sup N)) (by omega)`. Establish `key : ∀ c ∈ s₁, ∀ c' ∈ s₂, Bf (g₁ c) (g₂ c') = 0`. Introduce `c hc c' hc'`.

Break down `hg₁ c hc with h | ⟨hc0, hgc⟩` into its components or cases. Simplify using `[h]`. Break down `hg₂ c' hc' with h' | ⟨hc0', hgc'⟩` into its components or cases. Simplify using `[h']`. Take `⟨p, hpb, hcp⟩` from `Set.mem_iUnion₂.1 (hcov (Set.mk_mem_prod hc0 hc0'))`.

Conclude with `hN p (hbS hpb) _ ((Finset.le_sup (hbfin.mem_toFinset.2 hpb)).trans (le_max_right _ _)) c hcp.1 c' hcp.2 _ _ hgc hgc'`. Rewrite using `[hsum₁, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun c hc => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, hsum₂, map_sum, Finset.sum_eq_zero fun c' hc' => by rw [map_smulₛₗ, key c hc c' hc', smul_zero], smul_zero]`.
-/
theorem bf_eq_zero_of_local : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (Bf : GlobalTheory.FullRankCoinv.fullRk k n d →ₗ[ℂ] GlobalTheory.FullRankCoinv.fullRk k n d →ₗ⋆[ℂ] ℂ),
    (∀ Y₁ Y₂ : Matrix (Fin n) (Fin d) k, Y₁.rank = n → Y₂.rank = n → (∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Z₁ ∈ GlobalTheory.RankCoinv.box ϖ Y₁ (fun _ => N₀), ∀ Z₂ ∈ GlobalTheory.RankCoinv.box ϖ Y₂ (fun _ => N₀),
      ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, Ψ₁.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₁ (fun _ => N) →
        Ψ₂.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₂ (fun _ => N) → Bf Ψ₁ Ψ₂ = 0) →
    ∀ Ψ₁ Ψ₂ : GlobalTheory.FullRankCoinv.fullRk k n d,
      (∀ (Y₁ Y₂ : Matrix (Fin n) (Fin d) k), Ψ₁.1 Y₁ ≠ 0 → Ψ₂.1 Y₂ ≠ 0 → ∀ a : GL (Fin n) k, Y₁ ≠ a.1 * Y₂) →
      Bf Ψ₁ Ψ₂ = 0 := by
  classical
  intro k _ _ _ _ n d ϖ hϖ Bf hloc Ψ₁ Ψ₂ hsep
  have hsuppc : ∀ Ψ : GlobalTheory.FullRankCoinv.fullRk k n d, IsCompact (Function.support Ψ.1) := by
    intro Ψ
    obtain ⟨hlc, hcs⟩ := Ψ.2.1
    have hcl : IsClosed (Function.support Ψ.1) := by
      have := (hlc.isOpen_fiber 0).isClosed_compl
      convert this using 1
      ext Y
      simp
    exact hcs.of_isClosed_subset hcl (subset_tsupport _)
  have hrank : ∀ Ψ : GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y, Ψ.1 Y ≠ 0 → Y.rank = n := by
    intro Ψ Y hY
    by_contra h
    exact hY (Ψ.2.2 Y h)
  have hN : ∀ p ∈ Function.support Ψ₁.1 ×ˢ Function.support Ψ₂.1, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ Z₁ ∈ GlobalTheory.RankCoinv.box ϖ p.1 (fun _ => N₀), ∀ Z₂ ∈ GlobalTheory.RankCoinv.box ϖ p.2 (fun _ => N₀),
      ∀ Φ₁ Φ₂ : GlobalTheory.FullRankCoinv.fullRk k n d, Φ₁.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₁ (fun _ => N) →
        Φ₂.1 = GlobalTheory.RankCoinv.boxFn ϖ Z₂ (fun _ => N) → Bf Φ₁ Φ₂ = 0 := by
    rintro ⟨Y₁, Y₂⟩ ⟨h₁, h₂⟩
    exact hloc Y₁ Y₂ (hrank Ψ₁ Y₁ h₁) (hrank Ψ₂ Y₂ h₂) (hsep Y₁ Y₂ h₁ h₂)
  choose! N hN using hN
  obtain ⟨b, hbS, hbfin, hcov⟩ := ((hsuppc Ψ₁).prod (hsuppc Ψ₂)).elim_finite_subcover_image
    (b := Function.support Ψ₁.1 ×ˢ Function.support Ψ₂.1)
    (c := fun p => GlobalTheory.RankCoinv.box ϖ p.1 (fun _ => N p) ×ˢ GlobalTheory.RankCoinv.box ϖ p.2 (fun _ => N p))
    (fun p _ => (GlobalTheory.RankCoinv.isClopen_box ϖ _ _).isOpen.prod (GlobalTheory.RankCoinv.isClopen_box ϖ _ _).isOpen)
    (fun p hp => Set.mem_biUnion hp
      ⟨GlobalTheory.RankCoinv.Decomp.mem_box_self ϖ _ _, GlobalTheory.RankCoinv.Decomp.mem_box_self ϖ _ _⟩)
  obtain ⟨m₁, hm₁⟩ := exists_sum_fullRk hϖ Ψ₁
  obtain ⟨m₂, hm₂⟩ := exists_sum_fullRk hϖ Ψ₂
  obtain ⟨s₁, g₁, hsum₁, hg₁⟩ := hm₁ (max (max m₁ m₂) (hbfin.toFinset.sup N)) (by omega)
  obtain ⟨s₂, g₂, hsum₂, hg₂⟩ := hm₂ (max (max m₁ m₂) (hbfin.toFinset.sup N)) (by omega)
  have key : ∀ c ∈ s₁, ∀ c' ∈ s₂, Bf (g₁ c) (g₂ c') = 0 := by
    intro c hc c' hc'
    rcases hg₁ c hc with h | ⟨hc0, hgc⟩
    · simp [h]
    rcases hg₂ c' hc' with h' | ⟨hc0', hgc'⟩
    · simp [h']
    obtain ⟨p, hpb, hcp⟩ := Set.mem_iUnion₂.1 (hcov (Set.mk_mem_prod hc0 hc0'))
    exact hN p (hbS hpb) _ ((Finset.le_sup (hbfin.mem_toFinset.2 hpb)).trans (le_max_right _ _))
      c hcp.1 c' hcp.2 _ _ hgc hgc'
  rw [hsum₁, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [map_smul, LinearMap.smul_apply, hsum₂, map_sum,
    Finset.sum_eq_zero fun c' hc' => by rw [map_smulₛₗ, key c hc c' hc', smul_zero], smul_zero]

end GlobalTheory.RankCoinv.OffDiagAssemble
