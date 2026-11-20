import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

noncomputable section
namespace GlobalTheory.SchwartzBox

/- English proof (translation)
Establish `hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl))` using `(f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff`. Establish `hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr))` using `(f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff`. Establish `hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k`. Establish `h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k` using `pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k`. Use `h0.trans ?_` and prove the remaining obligations.

Establish `p1` using `pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k`. Establish `p2` using `pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k`. Break down `le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h` into its components or cases. Rewrite using `[max_eq_right h]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[max_eq_left h]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL` using `norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)` and prove the remaining obligations.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `norm_iteratedFDeriv_restr_le Sum.inl f₁ i x`. Conclude with `norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x`. Use `_ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ + ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by`.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring`. Use `_ ≤ _ := by`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `SchwartzMap.le_seminorm ℂ k i f₁ _`.

Conclude with `SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₂ _ _`. Conclude with `SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₁ _ _`. Conclude with `SchwartzMap.le_seminorm ℂ k (n - i) f₂ _`.
-/
theorem box_pow_mul_iteratedFDeriv_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ) (f₂ : SchwartzMap (κ' → V) ℂ) (k n : ℕ)
    (x : κ ⊕ κ' → V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i f₁ * SchwartzMap.seminorm ℂ 0 (n - i) f₂ +
          SchwartzMap.seminorm ℂ 0 i f₁ * SchwartzMap.seminorm ℂ k (n - i) f₂) := by
  have hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl)) :=
    (f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff
  have hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr)) :=
    (f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff
  have hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k := by
    have h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k
    refine h0.trans ?_
    have p1 := pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k
    have p2 := pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k
    rcases le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖
      ≤ (‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_restr_le Sum.inl f₁ i x
        · exact norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) *
              ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ +
           ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ *
              (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℂ k i f₁ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₂ _ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₁ _ _
        · exact SchwartzMap.le_seminorm ℂ k (n - i) f₂ _

/- English proof (translation)
Introduce `V _ _ κ κ' _ _ f₁`. Use `⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun (f : SchwartzMap (κ' → V) ℂ) (x : κ ⊕ κ' → V) => f₁ (x ∘ Sum.inl) * f (x ∘ Sum.inr)) (fun f g x => by simp [mul_add]) (fun a f x => by simp; ring) (fun f => ?_) ?_, fun _ _ => rfl⟩` and prove the remaining obligations. Conclude with `((f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff).mul ((f.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff)`. Introduce and unpack `⟨k, n⟩`. Use `⟨Finset.range (k + 1) ×ˢ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (SchwartzMap.seminorm ℂ k i f₁ + SchwartzMap.seminorm ℂ 0 i f₁), by positivity, fun f x => ?_⟩` and prove the remaining obligations.

Use `(box_pow_mul_iteratedFDeriv_le f₁ f k n x).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `hb : ∀ a, a ≤ k → SchwartzMap.seminorm ℂ a (n - i) f ≤ (Finset.range (k + 1) ×ˢ Finset.range (n + 1)).sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) f`. Introduce `a ha`.

Establish `hm : (a, n - i) ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1)`. Simplify using `only [Finset.mem_product, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Conclude with `Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ' → V) ℂ) hm`. Rewrite using `[mul_assoc, add_mul]`.

Use `gcongr`. Conclude with `hb 0 (Nat.zero_le _)`. Conclude with `hb k le_rfl`.
-/
theorem exists_boxCLM : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ κ' : Type) [Fintype κ]
    [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ),
    ∃ T : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ' → V) ℂ,
      ∀ f x, T f x = f₁ (x ∘ Sum.inl) * f (x ∘ Sum.inr) := by
  intro V _ _ κ κ' _ _ f₁
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ)
    (fun (f : SchwartzMap (κ' → V) ℂ) (x : κ ⊕ κ' → V) => f₁ (x ∘ Sum.inl) * f (x ∘ Sum.inr))
    (fun f g x => by simp [mul_add]) (fun a f x => by simp; ring) (fun f => ?_) ?_, fun _ _ => rfl⟩
  · exact ((f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff).mul
      ((f.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (k + 1) ×ˢ Finset.range (n + 1),
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (SchwartzMap.seminorm ℂ k i f₁ + SchwartzMap.seminorm ℂ 0 i f₁), by positivity, fun f x => ?_⟩
    refine (box_pow_mul_iteratedFDeriv_le f₁ f k n x).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hb : ∀ a, a ≤ k → SchwartzMap.seminorm ℂ a (n - i) f ≤
        (Finset.range (k + 1) ×ˢ Finset.range (n + 1)).sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) f := by
      intro a ha
      have hm : (a, n - i) ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1) := by
        simp only [Finset.mem_product, Finset.mem_range]; omega
      exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ' → V) ℂ) hm
    rw [mul_assoc, add_mul]
    gcongr
    · exact hb 0 (Nat.zero_le _)
    · exact hb k le_rfl

end GlobalTheory.SchwartzBox
