import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VkGenSubStable

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section VKMain

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Use `c.isLt` as an intermediate fact. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vk_natCast_Ioi (c : Fin n) : (((n - 1 - (c : ℕ) : ℕ) : ℝ) : ℂ) = ((n : ℂ) - 1 - (c : ℕ)) := by
  have := c.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, vk_eeV_apply, Finset.sum_apply, vk_tensV_apply, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]`. Rewrite using `[Pi.single_eq_same]`. Break down `lt_trichotomy c t with h | h | h` into its components or cases.

Rewrite using `[hlow t c h, Pi.single_eq_of_ne (ne_of_lt h)]`. Establish `h1 : ∀ d ∈ Ioi t, E t d ((Pi.single d φ : Fin n → M) c) = 0` using `fun d hd => by`. Rewrite using `[Pi.single_eq_of_ne (ne_of_lt (h.trans (mem_Ioi.1 hd))), map_zero]`. Rewrite using `[Finset.sum_eq_zero h1]`. Simplify using `[ne_of_lt h]`.

Substitute `h` using the available equality. Establish `h1 : ∀ d ∈ Ioi c, E c d ((Pi.single d φ : Fin n → M) c) = 0` using `fun d hd => by`. Rewrite using `[Pi.single_eq_of_ne (ne_of_lt (mem_Ioi.1 hd)), map_zero]`. Rewrite using `[Finset.sum_eq_zero h1, hdiag]`. Simplify using `only [Pi.single_eq_same, if_true, Finset.sum_const, Fin.card_Ioi, zero_add]`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]`. Use `congr 1`. Use `vk_natCast_Ioi c` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Rewrite using `[this]`.

Simplify using `only [rho, thV]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_eq_single c (fun b hb hbc => by rw [Pi.single_eq_of_ne (Ne.symm hbc), map_zero]) (fun hc => absurd (mem_Ioi.2 h) hc)]`. Simplify using `[ne_of_gt h]`.
-/
theorem vk_stepV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hdiag : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ)
    (t : Fin n) :
    (eeV E - ((thV lam t : ℝ) : ℂ) • 1) (Pi.single t φ) =
      ∑ d ∈ Ioi t, tensV E t d (Pi.single d φ) := by
  funext c
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, vk_eeV_apply, Finset.sum_apply, vk_tensV_apply, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
  rw [Pi.single_eq_same]
  rcases lt_trichotomy c t with h | h | h
  · rw [hlow t c h, Pi.single_eq_of_ne (ne_of_lt h)]
    have h1 : ∀ d ∈ Ioi t, E t d ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_lt (h.trans (mem_Ioi.1 hd))), map_zero]
    rw [Finset.sum_eq_zero h1]
    simp [ne_of_lt h]
  · subst h
    have h1 : ∀ d ∈ Ioi c, E c d ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_lt (mem_Ioi.1 hd)), map_zero]
    rw [Finset.sum_eq_zero h1, hdiag]
    simp only [Pi.single_eq_same, if_true, Finset.sum_const, Fin.card_Ioi, zero_add]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have := vk_natCast_Ioi c
    push_cast at this ⊢
    rw [this]
    simp only [rho, thV]
    push_cast
    ring
  · rw [Finset.sum_eq_single c (fun b hb hbc => by rw [Pi.single_eq_of_ne (Ne.symm hbc), map_zero])
      (fun hc => absurd (mem_Ioi.2 h) hc)]
    simp [ne_of_gt h]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, vk_eeVd_apply, Finset.sum_apply, vk_tensVd_apply, Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]`. Rewrite using `[Pi.single_eq_same]`. Break down `lt_trichotomy c s with h | h | h` into its components or cases.

Rewrite using `[Finset.sum_eq_single c (fun b hb hbc => by rw [Pi.single_eq_of_ne (Ne.symm hbc), map_zero]) (fun hc => absurd (mem_Iio.2 h) hc)]`. Simplify using `[ne_of_lt h]`. Substitute `h` using the available equality. Establish `h1 : ∀ d ∈ Iio c, E d c ((Pi.single d φ : Fin n → M) c) = 0` using `fun d hd => by`. Rewrite using `[Pi.single_eq_of_ne (ne_of_gt (mem_Iio.1 hd)), map_zero]`.

Rewrite using `[Finset.sum_eq_zero h1, hdiag]`. Simplify using `only [Pi.single_eq_same, if_true, Finset.sum_const, Fin.card_Iio, zero_sub, neg_neg]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]`. Use `congr 1`. Simplify using `only [rho, thVd]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hlow c s h, Pi.single_eq_of_ne (ne_of_gt h)]`. Establish `h1 : ∀ d ∈ Iio s, E d s ((Pi.single d φ : Fin n → M) c) = 0` using `fun d hd => by`. Rewrite using `[Pi.single_eq_of_ne (ne_of_gt ((mem_Iio.1 hd).trans h)), map_zero]`.

Rewrite using `[Finset.sum_eq_zero h1]`. Simplify using `[ne_of_gt h]`.
-/
theorem vk_stepVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hdiag : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ)
    (s : Fin n) :
    (eeVd E - ((thVd lam s : ℝ) : ℂ) • 1) (Pi.single s φ) =
      -∑ d ∈ Iio s, tensVd E d s (Pi.single d φ) := by
  funext c
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, vk_eeVd_apply, Finset.sum_apply, vk_tensVd_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (by simp)]
  rw [Pi.single_eq_same]
  rcases lt_trichotomy c s with h | h | h
  · rw [Finset.sum_eq_single c (fun b hb hbc => by rw [Pi.single_eq_of_ne (Ne.symm hbc), map_zero])
      (fun hc => absurd (mem_Iio.2 h) hc)]
    simp [ne_of_lt h]
  · subst h
    have h1 : ∀ d ∈ Iio c, E d c ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_gt (mem_Iio.1 hd)), map_zero]
    rw [Finset.sum_eq_zero h1, hdiag]
    simp only [Pi.single_eq_same, if_true, Finset.sum_const, Fin.card_Iio, zero_sub, neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · rw [hlow c s h, Pi.single_eq_of_ne (ne_of_gt h)]
    have h1 : ∀ d ∈ Iio s, E d s ((Pi.single d φ : Fin n → M) c) = 0 := fun d hd => by
      rw [Pi.single_eq_of_ne (ne_of_gt ((mem_Iio.1 hd).trans h)), map_zero]
    rw [Finset.sum_eq_zero h1]
    simp [ne_of_gt h]

/- English proof (translation)
Use extensionality with `d`. Distinguish the cases in `h : d = c`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem vk_single_smul (c : Fin n) (r : ℂ) (x : M) :
    (Pi.single c (r • x) : Fin n → M) = r • Pi.single c x := by
  ext d
  by_cases h : d = c
  · subst h; simp
  · simp [h]

/- English proof (translation)
Use `set G := genSub T (Submodule.span ℂ (Set.range fun t : Fin n => (Pi.single t φ : Fin n → M)))`. Set `S : Submodule ℂ M` to `{ carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G} add_mem' := by`. Introduce `x y hx hy c`. Rewrite using `[Pi.single_add]`. Conclude with `G.add_mem (hx c) (hy c)`.

Use the proof step `zero_mem' := by`. Introduce `c`. Rewrite using `[Pi.single_zero]`. Conclude with `G.zero_mem`. Use the proof step `smul_mem' := by`.

Introduce `r x hx c`. Rewrite using `[vk_single_smul]`. Conclude with `G.smul_mem r (hx c) }`. Establish `hφ : Submodule.span ℂ {φ} ≤ S`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`.

Introduce `c`. Conclude with `vk_le_genSub T _ (Submodule.subset_span ⟨c, rfl⟩)`. Establish `hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S`. Introduce `a b m hm c`. Establish `h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G` using `Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)`.

Establish `h2` using `G.add_mem (h1 (hT a b c m)) (vk_genSub_stable T _ a b _ (hm c))`. Simplify using `using h2`. Establish `hle : genSub E (Submodule.span ℂ {φ}) ≤ S` using `sInf_le ⟨hφ, hSS⟩`. Rewrite `hle` using `[hgen]`. Rewrite using `[← Finset.univ_sum_single f]`.

Conclude with `G.sum_mem fun c _ => hle Submodule.mem_top c`.
-/
theorem vk_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (f : Fin n → M) :
    f ∈ genSub T (Submodule.span ℂ (Set.range fun t : Fin n => (Pi.single t φ : Fin n → M))) := by
  set G := genSub T (Submodule.span ℂ (Set.range fun t : Fin n => (Pi.single t φ : Fin n → M)))
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]
        exact G.add_mem (hx c) (hy c)
      zero_mem' := by
        intro c
        rw [Pi.single_zero]
        exact G.zero_mem
      smul_mem' := by
        intro r x hx c
        rw [vk_single_smul]
        exact G.smul_mem r (hx c) }
  have hφ : Submodule.span ℂ {φ} ≤ S := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    intro c
    exact vk_le_genSub T _ (Submodule.subset_span ⟨c, rfl⟩)
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (vk_genSub_stable T _ a b _ (hm c))
    simpa using h2
  have hle : genSub E (Submodule.span ℂ {φ}) ≤ S := sInf_le ⟨hφ, hSS⟩
  rw [hgen] at hle
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[vk_tensV_apply]`. Apply the tactic sequence `by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;> simp_all`.
-/
theorem vk_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  rw [vk_tensV_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;> simp_all

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[vk_tensVd_apply]`. Apply the tactic sequence `by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;> simp_all`.
-/
theorem vk_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  rw [vk_tensVd_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;> simp_all

/- English proof (translation)
Rewrite using `[vk_tensV_single]`. Use `split_ifs`. Establish `hx : (Pi.single a m : Fin n → M) ∈ Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M))` using `Submodule.subset_span ⟨a, rfl⟩`. Simplify using `using Submodule.neg_mem _ hx`. Simplify using the standard rewrite rules.
-/
theorem vk_hT_V (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    Pi.single c (E a b m) - tensV E a b (Pi.single c m) ∈
      Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) := by
  rw [vk_tensV_single]
  split_ifs
  · have hx : (Pi.single a m : Fin n → M) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
      Submodule.subset_span ⟨a, rfl⟩
    simpa using Submodule.neg_mem _ hx
  · simp

/- English proof (translation)
Rewrite using `[vk_tensVd_single]`. Use `split_ifs`. Establish `hx : (Pi.single b m : Fin n → M) ∈ Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M))` using `Submodule.subset_span ⟨b, rfl⟩`. Simplify using `using hx`. Simplify using the standard rewrite rules.
-/
theorem vk_hT_Vd (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    Pi.single c (E a b m) - tensVd E a b (Pi.single c m) ∈
      Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) := by
  rw [vk_tensVd_single]
  split_ifs
  · have hx : (Pi.single b m : Fin n → M) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
      Submodule.subset_span ⟨b, rfl⟩
    simpa using hx
  · simp

end VKMain

/- English proof (translation)
Introduce `M _ _ E lam φ hE hlow hdiag hgen`. Prove the components needed by the constructor for the conclusion. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Rewrite using `[vk_prodShift_eq, LinearMap.zero_apply]`. Use `vk_kill (tensV E) (eeV E) (fun a b => vk_eeV_comm E hE a b) (fun t => ((thV lam t : ℝ) : ℂ)) (fun t => (Pi.single t φ : Fin n → M)) (fun t => ?_) f (vk_gen_top E φ hgen _ (vk_hT_V E) f)` and prove the remaining obligations.

Rewrite using `[vk_stepV E lam φ hlow hdiag t]`. Conclude with `Submodule.sum_mem _ fun d hd => vk_genSub_stable _ _ _ _ _ (vk_le_genSub _ _ (Submodule.subset_span ⟨d, mem_Ioi.1 hd, rfl⟩))`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Rewrite using `[vk_prodShift_eq, LinearMap.zero_apply]`. Establish `hprod : ∏ t : Fin n, (X - C (((thVd lam t : ℝ) : ℂ))) = ∏ t : Fin n, (X - C (((thVd lam (Fin.rev t) : ℝ) : ℂ)))` using `(Fintype.prod_equiv Fin.revPerm _ _ (fun t => by simp)).symm`.

Establish `hrange : Set.range (fun t : Fin n => (Pi.single (Fin.rev t) φ : Fin n → M)) = Set.range (fun t : Fin n => (Pi.single t φ : Fin n → M))` using `Fin.rev_surjective.range_comp (fun t : Fin n => (Pi.single t φ : Fin n → M))`. Rewrite using `[hprod]`. Use `vk_kill (tensVd E) (eeVd E) (fun a b => vk_eeVd_comm E hE a b) (fun t => ((thVd lam (Fin.rev t) : ℝ) : ℂ)) (fun t => (Pi.single (Fin.rev t) φ : Fin n → M)) (fun t => ?_) f (by rw [hrange]; exact vk_gen_top E φ hgen _ (vk_hT_Vd E) f)` and prove the remaining obligations. Rewrite using `[vk_stepVd E lam φ hlow hdiag (Fin.rev t)]`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => vk_genSub_stable _ _ _ _ _ (vk_le_genSub _ _ (Submodule.subset_span ⟨Fin.rev d, ?_, by simp⟩)))` and prove the remaining obligations.

Simplify using `only [Set.mem_ofPred_eq]`. Conclude with `Fin.lt_rev_iff.2 (mem_Iio.1 hd)`.
-/
theorem verma_product_identity (n : ℕ) : VermaProductIdentity n := by
  intro M _ _ E lam φ hE hlow hdiag hgen
  constructor
  · refine LinearMap.ext fun f => ?_
    rw [vk_prodShift_eq, LinearMap.zero_apply]
    refine vk_kill (tensV E) (eeV E) (fun a b => vk_eeV_comm E hE a b) (fun t => ((thV lam t : ℝ) : ℂ))
      (fun t => (Pi.single t φ : Fin n → M)) (fun t => ?_) f (vk_gen_top E φ hgen _ (vk_hT_V E) f)
    rw [vk_stepV E lam φ hlow hdiag t]
    exact Submodule.sum_mem _ fun d hd => vk_genSub_stable _ _ _ _ _
      (vk_le_genSub _ _ (Submodule.subset_span ⟨d, mem_Ioi.1 hd, rfl⟩))
  · refine LinearMap.ext fun f => ?_
    rw [vk_prodShift_eq, LinearMap.zero_apply]
    have hprod : ∏ t : Fin n, (X - C (((thVd lam t : ℝ) : ℂ))) =
        ∏ t : Fin n, (X - C (((thVd lam (Fin.rev t) : ℝ) : ℂ))) :=
      (Fintype.prod_equiv Fin.revPerm _ _ (fun t => by simp)).symm
    have hrange : Set.range (fun t : Fin n => (Pi.single (Fin.rev t) φ : Fin n → M)) =
        Set.range (fun t : Fin n => (Pi.single t φ : Fin n → M)) :=
      Fin.rev_surjective.range_comp (fun t : Fin n => (Pi.single t φ : Fin n → M))
    rw [hprod]
    refine vk_kill (tensVd E) (eeVd E) (fun a b => vk_eeVd_comm E hE a b)
      (fun t => ((thVd lam (Fin.rev t) : ℝ) : ℂ))
      (fun t => (Pi.single (Fin.rev t) φ : Fin n → M)) (fun t => ?_) f
      (by rw [hrange]; exact vk_gen_top E φ hgen _ (vk_hT_Vd E) f)
    rw [vk_stepVd E lam φ hlow hdiag (Fin.rev t)]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => vk_genSub_stable _ _ _ _ _
      (vk_le_genSub _ _ (Submodule.subset_span ⟨Fin.rev d, ?_, by simp⟩)))
    simp only [Set.mem_ofPred_eq]
    exact Fin.lt_rev_iff.2 (mem_Iio.1 hd)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
