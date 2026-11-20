import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sg_sq (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sg_ne (ε : Fin n → Bool) (a : Fin n) : sg ε a ≠ 0 := by
  unfold sg
  split_ifs <;> norm_num

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sg_comp (ε : Fin n → Bool) (a : Fin n) : sg (ε ∘ Fin.rev) a = sg ε (Fin.rev a) := rfl

/- English proof (translation)
The claim follows from `Equiv.sum_comp Fin.revPerm f`.
-/
theorem sum_rev {X : Type*} [AddCommMonoid X] (f : Fin n → X) : ∑ a, f (Fin.rev a) = ∑ a, f a :=
  Equiv.sum_comp Fin.revPerm f

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => (-(sg ε (Fin.rev a) * sg ε (Fin.rev b))) • E (Fin.rev b) (Fin.rev a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twE_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (v : M) :
    twE ε E a b v = (-(sg ε (Fin.rev a) * sg ε (Fin.rev b))) • E (Fin.rev b) (Fin.rev a) v := rfl

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[Fin.rev_rev]`.
-/
theorem comp_rev_rev (ε : Fin n → Bool) : (ε ∘ Fin.rev) ∘ Fin.rev = ε := by
  funext a
  simp [Fin.rev_rev]

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Simplify using `only [twE, sg_comp, Fin.rev_rev, smul_smul]`. Use `one_smul ℂ (E a b) using 2` and compare the differences between its conclusion and the goal. Take the linear combination `(sg ε b * sg ε b) * sg_sq ε a + sg_sq ε b`.
-/
theorem twE_twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    twE (ε ∘ Fin.rev) (twE ε E) = E := by
  funext a b
  simp only [twE, sg_comp, Fin.rev_rev, smul_smul]
  convert one_smul ℂ (E a b) using 2
  linear_combination (sg ε b * sg ε b) * sg_sq ε a + sg_sq ε b

/- English proof (translation)
Introduce `a b c d`. Establish `h` using `hE (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c)`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Simplify using `only [twE, smul_mul_smul_comm, h, Fin.rev_inj]`. Simplify using `only [@eq_comm (Fin n) b c, @eq_comm (Fin n) d a]`.

Apply the tactic sequence `split_ifs <;> subst_vars <;> simp only [sg] <;> split_ifs <;> module`.
-/
theorem twE_gl {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    IsGlRep (twE ε E) := by
  intro a b c d
  have h := hE (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c)
  rw [sub_eq_iff_eq_add] at h
  simp only [twE, smul_mul_smul_comm, h, Fin.rev_inj]
  simp only [@eq_comm (Fin n) b c, @eq_comm (Fin n) d a]
  split_ifs <;> subst_vars <;> simp only [sg] <;> split_ifs <;> module

/- English proof (translation)
Unfold `casimir`. Simplify using `only [twE, smul_mul_smul_comm]`. Establish `hs : ∀ a b : Fin n, (-(sg ε (Fin.rev a) * sg ε (Fin.rev b)) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a))) = 1`. Introduce `a b`. Take the linear combination `(sg ε (Fin.rev b) * sg ε (Fin.rev b)) * sg_sq ε (Fin.rev a) + sg_sq ε (Fin.rev b)`.

Simplify using `only [hs, one_smul]`. Establish `h1 : ∀ a : Fin n, ∑ b, E (Fin.rev b) (Fin.rev a) * E (Fin.rev a) (Fin.rev b) = ∑ b, E b (Fin.rev a) * E (Fin.rev a) b` using `fun a => sum_rev (fun b => E b (Fin.rev a) * E (Fin.rev a) b)`. Simplify using `only [h1]`. Conclude with `(sum_rev (fun a => ∑ b, E b a * E a b)).trans Finset.sum_comm`.
-/
theorem casimir_twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    casimir (twE ε E) = casimir E := by
  unfold casimir
  simp only [twE, smul_mul_smul_comm]
  have hs : ∀ a b : Fin n,
      (-(sg ε (Fin.rev a) * sg ε (Fin.rev b)) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a))) = 1 := by
    intro a b
    linear_combination (sg ε (Fin.rev b) * sg ε (Fin.rev b)) * sg_sq ε (Fin.rev a) + sg_sq ε (Fin.rev b)
  simp only [hs, one_smul]
  have h1 : ∀ a : Fin n, ∑ b, E (Fin.rev b) (Fin.rev a) * E (Fin.rev a) (Fin.rev b) =
      ∑ b, E b (Fin.rev a) * E (Fin.rev a) b :=
    fun a => sum_rev (fun b => E b (Fin.rev a) * E (Fin.rev a) b)
  simp only [h1]
  exact (sum_rev (fun a => ∑ b, E b a * E a b)).trans Finset.sum_comm

/- English proof (translation)
Introduce `a b hab v hv`. Rewrite using `[twE_apply]`. Conclude with `S.smul_mem _ (h _ _ hab.symm v hv)`.
-/
theorem kst_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (h : IsKStableSub ε E S) : IsKStableSub (ε ∘ Fin.rev) (twE ε E) S := by
  intro a b hab v hv
  rw [twE_apply]
  exact S.smul_mem _ (h _ _ hab.symm v hv)

/- English proof (translation)
Use `⟨fun h => ?_, kst_tw⟩` and prove the remaining obligations. Establish `h'` using `kst_tw (ε := ε ∘ Fin.rev) h`. Rewrite `h'` using `[twE_twE, comp_rev_rev]`. Then use the resulting hypothesis.
-/
theorem kst_tw_iff {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} :
    IsKStableSub (ε ∘ Fin.rev) (twE ε E) S ↔ IsKStableSub ε E S := by
  refine ⟨fun h => ?_, kst_tw⟩
  have h' := kst_tw (ε := ε ∘ Fin.rev) h
  rwa [twE_twE, comp_rev_rev] at h'

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `⟨fun a => ?_, fun a b hab he => ?_⟩` and prove the remaining obligations. Rewrite using `[twE_apply, h1, sg_sq, smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[twE_apply, h2 _ _ (Fin.rev_lt_rev.2 hab) he.symm, smul_zero]`.
-/
theorem khw_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {v : M}
    (h : IsKHWVec ε E μ v) : IsKHWVec (ε ∘ Fin.rev) (twE ε E) (fun a => -μ (Fin.rev a)) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [twE_apply, h1, sg_sq, smul_smul]
    congr 1
    push_cast
    ring
  · rw [twE_apply, h2 _ _ (Fin.rev_lt_rev.2 hab) he.symm, smul_zero]

/- English proof (translation)
Unfold `genSub`. Use `congr 1`. Use extensionality with `T`. Simplify using `only [Set.mem_setOf_eq]`. Use `and_congr_right fun _ => ⟨fun hT a b v hv => ?_, fun hT a b v hv => ?_⟩` and prove the remaining obligations.

Rewrite using `[← twE_twE ε E, twE_apply]`. Conclude with `T.smul_mem _ (hT _ _ v hv)`. Rewrite using `[twE_apply]`. Conclude with `T.smul_mem _ (hT _ _ v hv)`.
-/
theorem genSub_tw (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) :
    genSub (twE ε E) S = genSub E S := by
  unfold genSub
  congr 1
  ext T
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun hT a b v hv => ?_, fun hT a b v hv => ?_⟩
  · rw [← twE_twE ε E, twE_apply]
    exact T.smul_mem _ (hT _ _ v hv)
  · rw [twE_apply]
    exact T.smul_mem _ (hT _ _ v hv)

/- English proof (translation)
Take `⟨h1, h2, h3, w, hw, hw0, hw1⟩` from `h`. Conclude with `⟨h1, kst_tw h2, fun S' hS' hk => h3 S' hS' (kst_tw_iff.1 hk), w, hw, hw0, khw_tw hw1⟩`.
-/
theorem kirr_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {Λ : Fin n → ℝ}
    {S : Submodule ℂ M} (h : IsKIrrHW ε E Λ S) :
    IsKIrrHW (ε ∘ Fin.rev) (twE ε E) (fun a => -Λ (Fin.rev a)) S := by
  obtain ⟨h1, h2, h3, w, hw, hw0, hw1⟩ := h
  exact ⟨h1, kst_tw h2, fun S' hS' hk => h3 S' hS' (kst_tw_iff.1 hk), w, hw, hw0, khw_tw hw1⟩

end Alg

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
