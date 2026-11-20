import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.AdaptedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1 : valuation k (ϖ : k) < 1` using `(h _).2 le_rfl`. Establish `hs : valuation k (s : k) ≠ 0` using `by simp`. Take `⟨m, hm⟩` from `exists_pow_lt₀ h1 (Units.mk0 _ hs)`. Use `filter_upwards [Filter.eventually_ge_atTop m] with e he`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow]`.

Conclude with `(pow_le_pow_right_of_le_one' h1.le he).trans hm.le`.
-/
theorem eventually_pow_le {ϖ : kˣ} (h : IsUnif ϖ) (s : kˣ) :
    ∀ᶠ e : ℕ in Filter.atTop, valuation k ((ϖ ^ e : kˣ) : k) ≤ valuation k (s : k) := by
  have h1 : valuation k (ϖ : k) < 1 := (h _).2 le_rfl
  have hs : valuation k (s : k) ≠ 0 := by simp
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hs)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le he).trans hm.le

/- English proof (translation)
Establish `key : ∀ s : kˣ, ∀ᶠ e : ℕ in Filter.atTop, cball s ⊆ cball (ϖ ^ e)⁻¹`. Introduce `s`. Use `filter_upwards [eventually_pow_le h s⁻¹] with e he x hx`. Establish `hs : 0 < valuation k (s : k)` using `by simp [pos_iff_ne_zero]`. Establish `he0 : 0 < valuation k ((ϖ ^ e : kˣ) : k)`.

Rewrite using `[pos_iff_ne_zero]`. Simplify using the standard rewrite rules. Simplify using `only [cball, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx he ⊢`. Conclude with `hx.trans ((le_inv_comm₀ he0 hs).1 he)`. Use `hK.induction_on (p := fun K => ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹) (by simp) ?_ ?_ ?_` and prove the remaining obligations.

Introduce `s t hst ht`. Conclude with `ht.mono fun e he => hst.trans he`. Introduce `s t hs ht filter_upwards [hs, ht] with e h1 h2 using Set.union_subset h1 h2`. Introduce `x _`. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Conclude with `⟨cball 1, mem_nhdsWithin_of_mem_nhds (cball_mem_nhds 1), key 1⟩`. Conclude with `⟨cball (Units.mk0 x hx), mem_nhdsWithin_of_mem_nhds ((isOpen_cball _).mem_nhds (by simp [cball])), key _⟩`.
-/
theorem eventually_subset_cball {ϖ : kˣ} (h : IsUnif ϖ) {K : Set k} (hK : IsCompact K) :
    ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹ := by
  have key : ∀ s : kˣ, ∀ᶠ e : ℕ in Filter.atTop, cball s ⊆ cball (ϖ ^ e)⁻¹ := by
    intro s
    filter_upwards [eventually_pow_le h s⁻¹] with e he x hx
    have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
    have he0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := by
      rw [pos_iff_ne_zero]; simp
    simp only [cball, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx he ⊢
    exact hx.trans ((le_inv_comm₀ he0 hs).1 he)
  refine hK.induction_on (p := fun K => ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹)
    (by simp) ?_ ?_ ?_
  · intro s t hst ht
    exact ht.mono fun e he => hst.trans he
  · intro s t hs ht
    filter_upwards [hs, ht] with e h1 h2 using Set.union_subset h1 h2
  · intro x _
    by_cases hx : x = 0
    · subst hx
      exact ⟨cball 1, mem_nhdsWithin_of_mem_nhds (cball_mem_nhds 1), key 1⟩
    · exact ⟨cball (Units.mk0 x hx), mem_nhdsWithin_of_mem_nhds
        ((isOpen_cball _).mem_nhds (by simp [cball])), key _⟩

variable {n n' : Type}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [withCol]`.
-/
theorem withCol_add (x₀ : Matrix n n' k) (y z : n → k) :
    withCol x₀ (y + z) = withCol x₀ y + withCol (0 : Matrix n n' k) z := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [withCol]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp only [withCol, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop`.
-/
theorem continuous_withCol_zero :
    Continuous fun z : n → k => withCol (0 : Matrix n n' k) z := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simp only [withCol, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

/- English proof (translation)
Rewrite `hU` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hU`. Use `choose s hs using fun i => exists_cball_subset (ht i)`. Use `filter_upwards [Filter.eventually_all.2 fun i => eventually_pow_le h (s i)] with e he z hz`. Conclude with `hsub fun i _ => hs i (le_trans (hz i) (he i))`.
-/
theorem eventually_box_subset [Fintype n] {ϖ : kˣ} (h : IsUnif ϖ) {U : Set (n → k)}
    (hU : U ∈ 𝓝 (0 : n → k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ z ∈ box n (ϖ ^ e), z ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose s hs using fun i => exists_cball_subset (ht i)
  filter_upwards [Filter.eventually_all.2 fun i => eventually_pow_le h (s i)] with e he z hz
  exact hsub fun i _ => hs i (le_trans (hz i) (he i))

/- English proof (translation)
Take `⟨Λ, hΛ, hinv⟩` from `sb_matrix_exists_isOpen_addSubgroup k _ _ Ψ hΨ`. Establish `hc : IsCompact (tsupport Ψ)` using `hΨ.2`. Establish `h1 : ∀ r : n, ∀ᶠ e : ℕ in Filter.atTop, (fun x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k => x (Sum.inl r) (Sum.inr 0)) '' tsupport Ψ ⊆ cball (ϖ ^ e)⁻¹` using `fun r => eventually_subset_cball h (hc.image (by fun_prop))`. Establish `h0 : withCol (0 : Matrix n n' k) (0 : n → k) = 0`. Use extensionality with `i j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [withCol]`. Establish `h2 : (fun z : n → k => withCol (0 : Matrix n n' k) z) ⁻¹' (Λ : Set _) ∈ 𝓝 (0 : n → k)` using `(hΛ.preimage continuous_withCol_zero).mem_nhds (by`. Simplify using `only [Set.mem_preimage, h0]`. Conclude with `Λ.zero_mem)`. Use `filter_upwards [Filter.eventually_all.2 h1, eventually_box_subset h h2] with e he1 he2 x₀ y`.

Use `⟨fun hne r => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `he1 r ⟨withCol x₀ y, subset_tsupport _ hne, rfl⟩`. Rewrite using `[withCol_add]`. Conclude with `hinv _ _ (he2 z hz)`.
-/
theorem eventually_adapted [Fintype n] [Fintype n'] {ϖ : kˣ} (h : IsUnif ϖ)
    {Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ (x₀ : Matrix n n' k) (y : n → k),
      (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧
        ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  obtain ⟨Λ, hΛ, hinv⟩ := sb_matrix_exists_isOpen_addSubgroup k _ _ Ψ hΨ
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ r : n, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k => x (Sum.inl r) (Sum.inr 0)) ''
        tsupport Ψ ⊆ cball (ϖ ^ e)⁻¹ := fun r =>
    eventually_subset_cball h (hc.image (by fun_prop))
  have h0 : withCol (0 : Matrix n n' k) (0 : n → k) = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [withCol]
  have h2 : (fun z : n → k => withCol (0 : Matrix n n' k) z) ⁻¹' (Λ : Set _) ∈ 𝓝 (0 : n → k) :=
    (hΛ.preimage continuous_withCol_zero).mem_nhds (by
      simp only [Set.mem_preimage, h0]; exact Λ.zero_mem)
  filter_upwards [Filter.eventually_all.2 h1, eventually_box_subset h h2] with e he1 he2 x₀ y
  refine ⟨fun hne r => ?_, fun z hz => ?_⟩
  · exact he1 r ⟨withCol x₀ y, subset_tsupport _ hne, rfl⟩
  · rw [withCol_add]
    exact hinv _ _ (he2 z hz)

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ n' _ _ S hS hSB ϖ h`. Conclude with `((Filter.eventually_ge_atTop 1).and ((Filter.eventually_all_finite hS).2 fun Ψ hΨ => eventually_adapted h (hSB Ψ hΨ))).exists`.
-/
theorem exists_adapted_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  intro k _ _ _ _ n _ _ n' _ _ S hS hSB ϖ h
  exact ((Filter.eventually_ge_atTop 1).and ((Filter.eventually_all_finite hS).2
    fun Ψ hΨ => eventually_adapted h (hSB Ψ hΨ))).exists

end GlobalTheory.AdaptedExp
