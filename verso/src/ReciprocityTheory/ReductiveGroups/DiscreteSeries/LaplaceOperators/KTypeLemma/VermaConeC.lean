import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Use extensionality with `d`. Simplify using `only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.add_apply]`. Apply the tactic sequence `by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>`. Simplify the hypotheses and the goal together.
-/
theorem vc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  simp only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.add_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp_all

/- English proof (translation)
Use extensionality with `d`. Simplify using `only [tensVd, prj, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.sub_apply]`. Apply the tactic sequence `by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>`. Simplify the hypotheses and the goal together.
-/
theorem vc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  simp only [tensVd, prj, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.sub_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp_all

/- English proof (translation)
Apply the tactic sequence `by_cases h : c = a <;> simp [tensV, prj, h]`.
-/
theorem vc_tensV_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

/- English proof (translation)
Apply the tactic sequence `by_cases h : c = b <;> simp [tensVd, prj, h]`.
-/
theorem vc_tensVd_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

/- English proof (translation)
Simplify using `[eeV, prj, Pi.single_apply, apply_ite]`.
-/
theorem vc_eeV_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeV E (Pi.single t m) e = E t e m := by
  simp [eeV, prj, Pi.single_apply, apply_ite]

/- English proof (translation)
Simplify using `[eeVd, prj, Pi.single_apply, apply_ite]`.
-/
theorem vc_eeVd_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeVd E (Pi.single t m) e = -E e t m := by
  simp [eeVd, prj, Pi.single_apply, apply_ite]

/- English proof (translation)
Take `⟨hT, -, hcas, -⟩` from `tens_statement n M E hE`. Establish `key : ∀ g : Fin n → M, (2 : ℂ) • eeV E g = casimir (tensV E) g - (fun c => casimir E (g c)) - (n : ℂ) • g`. Introduce `g`. Rewrite using `[hcas g]`. Normalize the expressions using the abelian group laws.

Establish `hpi : ∀ g : Fin n → M, (fun c => casimir E (tensV E a b g c)) = tensV E a b (fun c => casimir E (g c))`. Introduce `g`. Use function extensionality and compare the values at `c`. Rewrite using `[vc_tensV_apply, vc_tensV_apply, map_add]`. Use `congr 1`.

Rewrite using `[← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `show eeV E * tensV E a b = tensV E a b * eeV E`. Use `LinearMap.ext fun g => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply]`.

Establish `h2 : (2 : ℂ) • eeV E (tensV E a b g) = (2 : ℂ) • tensV E a b (eeV E g)`. Rewrite using `[← map_smul (tensV E a b) (2 : ℂ) (eeV E g), key, key, map_sub, map_sub, map_smul, ← hpi, ← Module.End.mul_apply (casimir (tensV E)), casimir_comm hT a b, Module.End.mul_apply]`. Conclude with `smul_right_injective (Fin n → M) two_ne_zero h2`.
-/
theorem vc_commV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeV E) (tensV E a b) := by
  obtain ⟨hT, -, hcas, -⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeV E g =
      casimir (tensV E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensV E a b g c)) = tensV E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensV_apply, vc_tensV_apply, map_add]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeV E * tensV E a b = tensV E a b * eeV E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeV E (tensV E a b g) = (2 : ℂ) • tensV E a b (eeV E g) := by
    rw [← map_smul (tensV E a b) (2 : ℂ) (eeV E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensV E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

/- English proof (translation)
Take `⟨-, hT, -, hcas⟩` from `tens_statement n M E hE`. Establish `key : ∀ g : Fin n → M, (2 : ℂ) • eeVd E g = casimir (tensVd E) g - (fun c => casimir E (g c)) - (n : ℂ) • g`. Introduce `g`. Rewrite using `[hcas g]`. Normalize the expressions using the abelian group laws.

Establish `hpi : ∀ g : Fin n → M, (fun c => casimir E (tensVd E a b g c)) = tensVd E a b (fun c => casimir E (g c))`. Introduce `g`. Use function extensionality and compare the values at `c`. Rewrite using `[vc_tensVd_apply, vc_tensVd_apply, map_sub]`. Use `congr 1`.

Rewrite using `[← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `show eeVd E * tensVd E a b = tensVd E a b * eeVd E`. Use `LinearMap.ext fun g => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply]`.

Establish `h2 : (2 : ℂ) • eeVd E (tensVd E a b g) = (2 : ℂ) • tensVd E a b (eeVd E g)`. Rewrite using `[← map_smul (tensVd E a b) (2 : ℂ) (eeVd E g), key, key, map_sub, map_sub, map_smul, ← hpi, ← Module.End.mul_apply (casimir (tensVd E)), casimir_comm hT a b, Module.End.mul_apply]`. Conclude with `smul_right_injective (Fin n → M) two_ne_zero h2`.
-/
theorem vc_commVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeVd E) (tensVd E a b) := by
  obtain ⟨-, hT, -, hcas⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeVd E g =
      casimir (tensVd E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensVd E a b g c)) = tensVd E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensVd_apply, vc_tensVd_apply, map_sub]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeVd E * tensVd E a b = tensVd E a b * eeVd E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeVd E (tensVd E a b g) = (2 : ℂ) • tensVd E a b (eeVd E g) := by
    rw [← map_smul (tensVd E a b) (2 : ℂ) (eeVd E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensVd E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

/- English proof (translation)
Set `S : Submodule ℂ M` to `{ carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G} add_mem' := by`. Introduce `x y hx hy c`. Rewrite using `[Pi.single_add]`. Conclude with `G.add_mem (hx c) (hy c)`. Use the proof step `zero_mem' := by`.

Introduce `c`. Rewrite using `[Pi.single_zero]`. Conclude with `G.zero_mem`. Use the proof step `smul_mem' := by`. Introduce `r x hx c`.

Rewrite using `[Pi.single_smul']`. Conclude with `G.smul_mem r (hx c) }`. Establish `hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S`. Introduce `a b m hm c`. Establish `h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G` using `Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)`.

Establish `h2` using `G.add_mem (h1 (hT a b c m)) (hG a b _ (hm c))`. Simplify using `using h2`. Establish `hle` using `vc_genSub_le E _ S (by`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `hφ) hSS`.

Rewrite `hle` using `[hgen]`. Use `eq_top_iff.mpr fun f _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.univ_sum_single f]`. Conclude with `G.sum_mem fun c _ => hle Submodule.mem_top c`.
-/
theorem vc_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (G : Submodule ℂ (Fin n → M)) (hG : ∀ a b, ∀ x ∈ G, T a b x ∈ G)
    (hφ : ∀ c, (Pi.single c φ : Fin n → M) ∈ G) : G = ⊤ := by
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
        rw [Pi.single_smul']
        exact G.smul_mem r (hx c) }
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (hG a b _ (hm c))
    simpa using h2
  have hle := vc_genSub_le E _ S (by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hφ) hSS
  rw [hgen] at hle
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

end Inst

section Inst2

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Use function extensionality and compare the values at `e`. Rewrite using `[Pi.sub_apply, vc_eeV_single, Finset.sum_apply]`. Simplify using `only [vc_tensV_single, Pi.add_apply, if_true, Pi.smul_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]`. Break down `lt_trichotomy e t with h | rfl | h` into its components or cases.

Simplify using `[h.ne, hlow t e h, not_lt.mpr h.le]`. Establish `hc : (univ.filter fun d : Fin n => e < d).card = n - 1 - e`. Rewrite using `[filter_lt_eq_Ioi, Fin.card_Ioi]`. Simplify using `only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_add, hc, hd]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]`.

Use `congr 1`. Establish `he : 1 + (e : ℕ) ≤ n` using `by have := e.isLt; omega`. Rewrite using `[Nat.sub_sub, Nat.cast_sub he]`. Simplify using `only [rho, thV]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[h.ne', h]`.
-/
theorem vc_genV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      ∑ d ∈ univ.filter (fun d => t < d), tensV E t d (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeV_single, Finset.sum_apply]
  simp only [vc_tensV_single, Pi.add_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, hlow t e h, not_lt.mpr h.le]
  · have hc : (univ.filter fun d : Fin n => e < d).card = n - 1 - e := by
      rw [filter_lt_eq_Ioi, Fin.card_Ioi]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_add, hc, hd]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have he : 1 + (e : ℕ) ≤ n := by have := e.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub he]
    simp only [rho, thV]
    push_cast
    ring
  · simp [h.ne', h]

/- English proof (translation)
Use function extensionality and compare the values at `e`. Rewrite using `[Pi.sub_apply, vc_eeVd_single, Pi.neg_apply, Finset.sum_apply]`. Simplify using `only [vc_tensVd_single, Pi.sub_apply, if_true, Pi.smul_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]`. Break down `lt_trichotomy e t with h | rfl | h` into its components or cases.

Simplify using `[h.ne, h]`. Establish `hc : (univ.filter fun d : Fin n => d < e).card = e`. Rewrite using `[filter_gt_eq_Iio, Fin.card_Iio]`. Simplify using `only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_sub, hc, hd, neg_neg]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]`.

Use `congr 1`. Simplify using `only [rho, thVd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h.ne', hlow e t h, not_lt.mpr h.le]`.
-/
theorem vc_genVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      -∑ d ∈ univ.filter (fun d => d < t), tensVd E d t (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeVd_single, Pi.neg_apply, Finset.sum_apply]
  simp only [vc_tensVd_single, Pi.sub_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, h]
  · have hc : (univ.filter fun d : Fin n => d < e).card = e := by
      rw [filter_gt_eq_Iio, Fin.card_Iio]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_sub, hc, hd,
      neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · simp [h.ne', hlow e t h, not_lt.mpr h.le]

end Inst2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
