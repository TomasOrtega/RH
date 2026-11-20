import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Core2

variable {n : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]

/- English proof (translation)
Use `set post := vcIter A θ (j + 1) (m - j - 1) with hpost`. Use `set c' : ℂ := ∏ i ∈ range (m - j - 1), (θ j - θ (j + 1 + i)) with hc'`. Establish `hc'0 : c' ≠ 0`. Rewrite using `[hc', Finset.prod_ne_zero_iff]`. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_range]`. Conclude with `sub_ne_zero.mpr (hθ (j + 1 + i) (by omega) (by omega)).symm`. Establish `hpostT : ∀ a b, Commute post (T a b)` using `fun a b => vcIter_comm A θ _ (hA a b) _`. Establish `hred : ∀ x, A x = θ j • x → ∃ y ∈ Submodule.span ℂ (vcMonAll T v), post y = c' • x`. Introduce `x hx`.

Establish `hxj : x ∈ F j`. Establish `h1` using `vcIter_maps A θ F hstep 0 j x (by rw [h0]; exact Submodule.mem_top)`. Rewrite `h1` using `[vcIter_eig A θ 0 hx j, Nat.zero_add]`. Establish `hc : (∏ i' ∈ range j, (θ j - θ (0 + i'))) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Conclude with `sub_ne_zero.mpr (hθ (0 + i) (by omega) (by omega)).symm`. Use `(F j).smul_mem (∏ i' ∈ range j, (θ j - θ (0 + i')))⁻¹ h1` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.

Establish `hx2 : x ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F (j + 1)`. Establish `h3` using `vc_genSub_le_mon T hT v (F (j + 1)) (hF (j + 1)) hlow (fun a => ⟨_, hdiag a⟩)`. Conclude with `(sup_le h3 le_sup_right) (hFj hxj)`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hx2`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Establish `hpz : post z = 0`. Use `vcIter_maps A θ F hstep (j + 1) (m - j - 1) z hz` as an intermediate fact. Rewrite `this` using `[show j + 1 + (m - j - 1) = m by omega, hm]`. Conclude with `(Submodule.mem_bot ℂ).mp this`. Establish `hpx : post x = c' • x` using `vcIter_eig A θ (j + 1) hx _`.

Rewrite using `[← hpx, ← hyz, map_add, hpz, add_zero]`. Establish `hpostGood : ∀ (P : (Fin n → ℝ) → Prop) (w : U), w ∈ vcGood T P → post w ∈ vcGood T P`. Introduce `P w ⟨ν, hP, hν⟩`. Use `⟨ν, hP, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hν a, map_smul]`.

Establish `hspanGood : ∀ (P : (Fin n → ℝ) → Prop) (G : Set U), G ⊆ vcGood T P → ∀ y ∈ Submodule.span ℂ G, post y ∈ Submodule.span ℂ (vcGood T P)`. Introduce `P G hG y hy`. Establish `: Submodule.span ℂ G ≤ (Submodule.span ℂ (vcGood T P)).comap post` using `Submodule.span_le.mpr (fun w hw => Submodule.subset_span (hpostGood P w (hG hw)))`. Conclude with `this hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `μ x hx hx0 hμ`. Assume the negation of the conclusion as `hcone`. Take `⟨y, hy, hyx⟩` from `hred x hx`. Establish `hmon : vcMonAll T v ⊆ vcGood T (fun ν => InRootCone (ν - base))`. Introduce `w hw`.

Take `⟨k, hk⟩` from `Set.mem_iUnion.mp hw`. Take `⟨ν, hν, hc, _⟩` from `vcMon_weight T hT hdiag k w hk`. Conclude with `⟨ν, hc, hν⟩`. Establish `hs` using `hspanGood _ _ hmon y hy`. Rewrite `hs` using `[hyx]`.

Establish `hz` using `vc_eq_zero_of_mem_span T (fun ν => InRootCone (ν - base)) hcone (x := c' • x) (fun a => by rw [map_smul, hμ a, smul_comm]) hs`. Conclude with `hx0 ((smul_eq_zero.mp hz).resolve_left hc'0)`. Establish `hpv : ∀ a, T a a (post v) = ((base a : ℝ) : ℂ) • post v`. Introduce `a`. Rewrite using `[← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hdiag a, map_smul]`.

Establish `hvert : ∀ x, A x = θ j • x → (∀ a, T a a x = ((base a : ℝ) : ℂ) • x) → ∃ β : ℂ, x = β • post v`. Introduce `x hx hxw`. Take `⟨y, hy, hyx⟩` from `hred x hx`. Establish `hmon : vcMonAll T v ⊆ (Submodule.span ℂ {v} ⊔ Submodule.span ℂ (vcGood T (fun ν => ν ≠ base)) : Submodule ℂ U)`. Introduce `w hw`.

Take `⟨k, hk⟩` from `Set.mem_iUnion.mp hw`. Break down `k with _ | k` into its components or cases. Establish `hwv : w = v` using `hk`. Substitute `hwv` using the available equality. Conclude with `Submodule.mem_sup_left (Submodule.mem_span_singleton_self w)`.

Take `⟨ν, hν, _, hht⟩` from `vcMon_weight T hT hdiag (k + 1) w hk`. Use `Submodule.mem_sup_right (Submodule.subset_span ⟨ν, ?_, hν⟩)` and prove the remaining obligations. Introduce `hνb`. Rewrite `hht` using `[hνb, sub_self, vcHt_zero]`. Move the coercions through the operations in `at hht`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy2` using `(Submodule.span_le.mpr hmon) hy`. Take `⟨y1, hy1, r, hr, hyr⟩` from `Submodule.mem_sup.mp hy2`. Take `⟨α, rfl⟩` from `Submodule.mem_span_singleton.mp hy1`. Establish `hpr` using `hspanGood (fun ν => ν ≠ base) _ (Set.Subset.refl _) r hr`.

Establish `hd : c' • x - α • post v = post r`. Rewrite using `[← hyx, ← hyr, map_add, map_smul]`. Normalize the expressions using the abelian group laws. Establish `hdw : ∀ a, T a a (c' • x - α • post v) = ((base a : ℝ) : ℂ) • (c' • x - α • post v)`. Introduce `a`.

Rewrite using `[map_sub, map_smul, map_smul, hxw a, hpv a, smul_sub, smul_comm c', smul_comm α]`. Establish `hd0` using `vc_eq_zero_of_mem_span T (fun ν => ν ≠ base) (μ := base) (by simp) hdw (by rw [hd]; exact hpr)`. Use `⟨c'⁻¹ * α, ?_⟩` and prove the remaining obligations. Rewrite `hd0` using `[sub_eq_zero]`. Rewrite using `[mul_smul, ← hd0, smul_smul, inv_mul_cancel₀ hc'0, one_smul]`.

Introduce `x₁ x₂ h1 h2 hw1 hw2`. Take `⟨β₁, rfl⟩` from `hvert x₁ h1 hw1`. Take `⟨β₂, rfl⟩` from `hvert x₂ h2 hw2`. Distinguish the cases in `hb : β₁ = 0`. Conclude with `⟨1, 0, Or.inl one_ne_zero, by simp [hb]⟩`.

Use `⟨β₂, -β₁, Or.inr (neg_ne_zero.mpr hb), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, mul_comm β₂ β₁, neg_mul, neg_smul, add_neg_cancel]`.
-/
theorem vc_cone_core (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) (A : Module.End ℂ U)
    (hA : ∀ a b, Commute A (T a b)) (F : ℕ → Submodule ℂ U) (θ : ℕ → ℂ)
    (hF : ∀ k a b, ∀ x ∈ F k, T a b x ∈ F k)
    (hstep : ∀ k, ∀ x ∈ F k, A x - θ k • x ∈ F (k + 1))
    (m j : ℕ) (h0 : F 0 = ⊤) (hm : F m = ⊥) (hj : j < m) (hθ : ∀ k < m, k ≠ j → θ k ≠ θ j)
    (v : U) (base : Fin n → ℝ) (hFj : F j ≤ genSub T (Submodule.span ℂ {v}) ⊔ F (j + 1))
    (hlow : ∀ a b, b < a → T a b v ∈ F (j + 1)) (hdiag : ∀ a, T a a v = ((base a : ℝ) : ℂ) • v) :
    (∀ (μ : Fin n → ℝ) (x : U), A x = θ j • x → x ≠ 0 → (∀ a, T a a x = ((μ a : ℝ) : ℂ) • x) →
        InRootCone (μ - base)) ∧
    ∀ x₁ x₂ : U, A x₁ = θ j • x₁ → A x₂ = θ j • x₂ →
      (∀ a, T a a x₁ = ((base a : ℝ) : ℂ) • x₁) → (∀ a, T a a x₂ = ((base a : ℝ) : ℂ) • x₂) →
      ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • x₁ + c₂ • x₂ = 0 := by
  set post := vcIter A θ (j + 1) (m - j - 1) with hpost
  set c' : ℂ := ∏ i ∈ range (m - j - 1), (θ j - θ (j + 1 + i)) with hc'
  have hc'0 : c' ≠ 0 := by
    rw [hc', Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    exact sub_ne_zero.mpr (hθ (j + 1 + i) (by omega) (by omega)).symm
  have hpostT : ∀ a b, Commute post (T a b) := fun a b => vcIter_comm A θ _ (hA a b) _
  have hred : ∀ x, A x = θ j • x → ∃ y ∈ Submodule.span ℂ (vcMonAll T v), post y = c' • x := by
    intro x hx
    have hxj : x ∈ F j := by
      have h1 := vcIter_maps A θ F hstep 0 j x (by rw [h0]; exact Submodule.mem_top)
      rw [vcIter_eig A θ 0 hx j, Nat.zero_add] at h1
      have hc : (∏ i' ∈ range j, (θ j - θ (0 + i'))) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        exact sub_ne_zero.mpr (hθ (0 + i) (by omega) (by omega)).symm
      have := (F j).smul_mem (∏ i' ∈ range j, (θ j - θ (0 + i')))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have hx2 : x ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F (j + 1) := by
      have h3 := vc_genSub_le_mon T hT v (F (j + 1)) (hF (j + 1)) hlow (fun a => ⟨_, hdiag a⟩)
      exact (sup_le h3 le_sup_right) (hFj hxj)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
    refine ⟨y, hy, ?_⟩
    have hpz : post z = 0 := by
      have := vcIter_maps A θ F hstep (j + 1) (m - j - 1) z hz
      rw [show j + 1 + (m - j - 1) = m by omega, hm] at this
      exact (Submodule.mem_bot ℂ).mp this
    have hpx : post x = c' • x := vcIter_eig A θ (j + 1) hx _
    rw [← hpx, ← hyz, map_add, hpz, add_zero]
  have hpostGood : ∀ (P : (Fin n → ℝ) → Prop) (w : U), w ∈ vcGood T P → post w ∈ vcGood T P := by
    intro P w ⟨ν, hP, hν⟩
    refine ⟨ν, hP, fun a => ?_⟩
    rw [← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hν a, map_smul]
  have hspanGood : ∀ (P : (Fin n → ℝ) → Prop) (G : Set U), G ⊆ vcGood T P →
      ∀ y ∈ Submodule.span ℂ G, post y ∈ Submodule.span ℂ (vcGood T P) := by
    intro P G hG y hy
    have : Submodule.span ℂ G ≤ (Submodule.span ℂ (vcGood T P)).comap post :=
      Submodule.span_le.mpr (fun w hw => Submodule.subset_span (hpostGood P w (hG hw)))
    exact this hy
  refine ⟨?_, ?_⟩
  · intro μ x hx hx0 hμ
    by_contra hcone
    obtain ⟨y, hy, hyx⟩ := hred x hx
    have hmon : vcMonAll T v ⊆ vcGood T (fun ν => InRootCone (ν - base)) := by
      intro w hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
      obtain ⟨ν, hν, hc, _⟩ := vcMon_weight T hT hdiag k w hk
      exact ⟨ν, hc, hν⟩
    have hs := hspanGood _ _ hmon y hy
    rw [hyx] at hs
    have hz := vc_eq_zero_of_mem_span T (fun ν => InRootCone (ν - base)) hcone
      (x := c' • x) (fun a => by rw [map_smul, hμ a, smul_comm]) hs
    exact hx0 ((smul_eq_zero.mp hz).resolve_left hc'0)
  · have hpv : ∀ a, T a a (post v) = ((base a : ℝ) : ℂ) • post v := by
      intro a
      rw [← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hdiag a, map_smul]
    have hvert : ∀ x, A x = θ j • x → (∀ a, T a a x = ((base a : ℝ) : ℂ) • x) →
        ∃ β : ℂ, x = β • post v := by
      intro x hx hxw
      obtain ⟨y, hy, hyx⟩ := hred x hx
      have hmon : vcMonAll T v ⊆
          (Submodule.span ℂ {v} ⊔ Submodule.span ℂ (vcGood T (fun ν => ν ≠ base)) : Submodule ℂ U) := by
        intro w hw
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
        rcases k with _ | k
        · have hwv : w = v := hk
          subst hwv
          exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self w)
        · obtain ⟨ν, hν, _, hht⟩ := vcMon_weight T hT hdiag (k + 1) w hk
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨ν, ?_, hν⟩)
          intro hνb
          rw [hνb, sub_self, vcHt_zero] at hht
          push_cast at hht
          linarith
      have hy2 := (Submodule.span_le.mpr hmon) hy
      obtain ⟨y1, hy1, r, hr, hyr⟩ := Submodule.mem_sup.mp hy2
      obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hy1
      have hpr := hspanGood (fun ν => ν ≠ base) _ (Set.Subset.refl _) r hr
      have hd : c' • x - α • post v = post r := by
        rw [← hyx, ← hyr, map_add, map_smul]
        abel
      have hdw : ∀ a, T a a (c' • x - α • post v) = ((base a : ℝ) : ℂ) • (c' • x - α • post v) := by
        intro a
        rw [map_sub, map_smul, map_smul, hxw a, hpv a, smul_sub, smul_comm c', smul_comm α]
      have hd0 := vc_eq_zero_of_mem_span T (fun ν => ν ≠ base) (μ := base) (by simp) hdw
        (by rw [hd]; exact hpr)
      refine ⟨c'⁻¹ * α, ?_⟩
      rw [sub_eq_zero] at hd0
      rw [mul_smul, ← hd0, smul_smul, inv_mul_cancel₀ hc'0, one_smul]
    intro x₁ x₂ h1 h2 hw1 hw2
    obtain ⟨β₁, rfl⟩ := hvert x₁ h1 hw1
    obtain ⟨β₂, rfl⟩ := hvert x₂ h2 hw2
    by_cases hb : β₁ = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hb]⟩
    · refine ⟨β₂, -β₁, Or.inr (neg_ne_zero.mpr hb), ?_⟩
      rw [smul_smul, smul_smul, mul_comm β₂ β₁, neg_mul, neg_smul, add_neg_cancel]

def vcFlag (T : Fin n → Fin n → Module.End ℂ U) (g : Fin n → U) (r : Fin n → ℕ) (k : ℕ) : Submodule ℂ U :=
  genSub T (Submodule.span ℂ (g '' {t | k ≤ r t}))

variable (T : Fin n → Fin n → Module.End ℂ U) (g : Fin n → U) (r : Fin n → ℕ)

/- English proof (translation)
Introduce `_ hx` and use `vc_genSub_stable T _ a b hx`.
-/
theorem vcFlag_stable (k : ℕ) (a b : Fin n) : ∀ x ∈ vcFlag T g r k, T a b x ∈ vcFlag T g r k :=
  fun _ hx => vc_genSub_stable T _ a b hx

/- English proof (translation)
The claim follows from `vc_le_genSub T _ (Submodule.subset_span ⟨t, h, rfl⟩)`.
-/
theorem vcFlag_gen {t : Fin n} {k : ℕ} (h : k ≤ r t) : g t ∈ vcFlag T g r k :=
  vc_le_genSub T _ (Submodule.subset_span ⟨t, h, rfl⟩)

/- English proof (translation)
The claim follows from `vc_genSub_le T _ _ (Submodule.span_le.mpr (by rintro _ ⟨t, ht, rfl⟩ exact vcFlag_gen T g r (le_trans h ht))) (vcFlag_stable T g r k)`.
-/
theorem vcFlag_anti {k l : ℕ} (h : k ≤ l) : vcFlag T g r l ≤ vcFlag T g r k :=
  vc_genSub_le T _ _ (Submodule.span_le.mpr (by
    rintro _ ⟨t, ht, rfl⟩
    exact vcFlag_gen T g r (le_trans h ht))) (vcFlag_stable T g r k)

/- English proof (translation)
Use `le_bot_iff.mp (vc_genSub_le T _ ⊥ ?_ (fun a b v hv => by` and prove the remaining obligations. Rewrite using `[(Submodule.mem_bot ℂ).mp hv, map_zero]`. Conclude with `Submodule.zero_mem _))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨t, ht, rfl⟩`.

Conclude with `absurd ht (not_le.mpr (hm t))`.
-/
theorem vcFlag_eq_bot {m : ℕ} (hm : ∀ t, r t < m) : vcFlag T g r m = ⊥ := by
  refine le_bot_iff.mp (vc_genSub_le T _ ⊥ ?_ (fun a b v hv => by
    rw [(Submodule.mem_bot ℂ).mp hv, map_zero]; exact Submodule.zero_mem _))
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  exact absurd ht (not_le.mpr (hm t))

/- English proof (translation)
Establish `hAst : ∀ k, ∀ x ∈ vcFlag T g r k, A x ∈ vcFlag T g r k`. Introduce `k`. Set `S : Submodule ℂ U` to `vcFlag T g r k ⊓ (vcFlag T g r k).comap A`. Establish `hle : vcFlag T g r k ≤ S`. Use `vc_genSub_le T _ S ?_ ?_` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Use `⟨vcFlag_gen T g r ht, ?_⟩` and prove the remaining obligations. Use `show A (g t) ∈ vcFlag T g r k`. Establish `h1` using `vcFlag_anti T g r (show k ≤ r t + 1 by simp at ht; omega) (hgen t)`.

Establish `h2` using `(vcFlag T g r k).smul_mem (θ (r t)) (vcFlag_gen T g r ht)`. Simplify using `using (vcFlag T g r k).add_mem h1 h2`. Introduce `a b x hx`. Use `⟨vcFlag_stable T g r k a b x hx.1, ?_⟩` and prove the remaining obligations. Use `show A (T a b x) ∈ vcFlag T g r k`.

Rewrite using `[← Module.End.mul_apply, (hA a b).eq, Module.End.mul_apply]`. Conclude with `vcFlag_stable T g r k a b _ hx.2`. Conclude with `fun x hx => (hle hx).2`. Introduce `k`. Set `S : Submodule ℂ U` to `vcFlag T g r k ⊓ (vcFlag T g r (k + 1)).comap (A - θ k • 1)`.

Establish `hle : vcFlag T g r k ≤ S`. Use `vc_genSub_le T _ S ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Use `⟨vcFlag_gen T g r ht, ?_⟩` and prove the remaining obligations.

Use `show (A - θ k • 1) (g t) ∈ vcFlag T g r (k + 1)`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Establish `ht' : k ≤ r t` using `ht`. Break down `eq_or_lt_of_le ht' with h | h` into its components or cases. Rewrite using `[h]`.

Conclude with `hgen t`. Establish `hg : g t ∈ vcFlag T g r (k + 1)` using `vcFlag_gen T g r h`. Conclude with `Submodule.sub_mem _ (hAst (k + 1) _ hg) (Submodule.smul_mem _ _ hg)`. Introduce `a b x hx`. Use `⟨vcFlag_stable T g r k a b x hx.1, ?_⟩` and prove the remaining obligations.

Use `show (A - θ k • 1) (T a b x) ∈ vcFlag T g r (k + 1)`. Establish `hc : Commute (A - θ k • 1) (T a b)` using `(hA a b).sub_left ((Commute.one_left _).smul_left _)`. Rewrite using `[← Module.End.mul_apply, hc.eq, Module.End.mul_apply]`. Conclude with `vcFlag_stable T g r (k + 1) a b _ hx.2`. Introduce `x hx`.

Use `(hle hx).2` as an intermediate fact. Simplify using `using this`.
-/
theorem vcFlag_step (A : Module.End ℂ U) (hA : ∀ a b, Commute A (T a b)) (θ : ℕ → ℂ)
    (hgen : ∀ t, A (g t) - θ (r t) • g t ∈ vcFlag T g r (r t + 1)) :
    ∀ k, ∀ x ∈ vcFlag T g r k, A x - θ k • x ∈ vcFlag T g r (k + 1) := by
  have hAst : ∀ k, ∀ x ∈ vcFlag T g r k, A x ∈ vcFlag T g r k := by
    intro k
    let S : Submodule ℂ U := vcFlag T g r k ⊓ (vcFlag T g r k).comap A
    have hle : vcFlag T g r k ≤ S := by
      refine vc_genSub_le T _ S ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨vcFlag_gen T g r ht, ?_⟩
        show A (g t) ∈ vcFlag T g r k
        have h1 := vcFlag_anti T g r (show k ≤ r t + 1 by simp at ht; omega) (hgen t)
        have h2 := (vcFlag T g r k).smul_mem (θ (r t)) (vcFlag_gen T g r ht)
        simpa using (vcFlag T g r k).add_mem h1 h2
      · intro a b x hx
        refine ⟨vcFlag_stable T g r k a b x hx.1, ?_⟩
        show A (T a b x) ∈ vcFlag T g r k
        rw [← Module.End.mul_apply, (hA a b).eq, Module.End.mul_apply]
        exact vcFlag_stable T g r k a b _ hx.2
    exact fun x hx => (hle hx).2
  intro k
  let S : Submodule ℂ U := vcFlag T g r k ⊓ (vcFlag T g r (k + 1)).comap (A - θ k • 1)
  have hle : vcFlag T g r k ≤ S := by
    refine vc_genSub_le T _ S ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨vcFlag_gen T g r ht, ?_⟩
      show (A - θ k • 1) (g t) ∈ vcFlag T g r (k + 1)
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      have ht' : k ≤ r t := ht
      rcases eq_or_lt_of_le ht' with h | h
      · rw [h]; exact hgen t
      · have hg : g t ∈ vcFlag T g r (k + 1) := vcFlag_gen T g r h
        exact Submodule.sub_mem _ (hAst (k + 1) _ hg) (Submodule.smul_mem _ _ hg)
    · intro a b x hx
      refine ⟨vcFlag_stable T g r k a b x hx.1, ?_⟩
      show (A - θ k • 1) (T a b x) ∈ vcFlag T g r (k + 1)
      have hc : Commute (A - θ k • 1) (T a b) := (hA a b).sub_left ((Commute.one_left _).smul_left _)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      exact vcFlag_stable T g r (k + 1) a b _ hx.2
  intro x hx
  have := (hle hx).2
  simpa using this

/- English proof (translation)
Use `vc_genSub_le T _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Establish `ht' : j ≤ r t` using `ht`. Break down `eq_or_lt_of_le ht' with h | h` into its components or cases.

Establish `hts : t = s` using `hr (by omega)`. Substitute `hts` using the available equality. Conclude with `Submodule.mem_sup_left (vc_le_genSub T _ (Submodule.mem_span_singleton_self _))`. Conclude with `Submodule.mem_sup_right (vcFlag_gen T g r h)`. Introduce `a b x hx`.

Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (vc_genSub_stable T _ a b hy) (vcFlag_stable T g r _ a b z hz)`.
-/
theorem vcFlag_top_le {j : ℕ} {s : Fin n} (hr : Function.Injective r) (hj : r s = j) :
    vcFlag T g r j ≤ genSub T (Submodule.span ℂ {g s}) ⊔ vcFlag T g r (j + 1) := by
  refine vc_genSub_le T _ _ ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : j ≤ r t := ht
    rcases eq_or_lt_of_le ht' with h | h
    · have hts : t = s := hr (by omega)
      subst hts
      exact Submodule.mem_sup_left (vc_le_genSub T _ (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (vcFlag_gen T g r h)
  · intro a b x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (vc_genSub_stable T _ a b hy) (vcFlag_stable T g r _ a b z hz)

end Core2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
