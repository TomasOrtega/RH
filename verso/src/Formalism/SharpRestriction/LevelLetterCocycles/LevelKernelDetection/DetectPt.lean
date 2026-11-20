import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.KerEqOfSpan

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.ExponentWindows

/- English proof (translation)
Establish `hanti : Antitone F` using `hF.1`. Establish `hli : LinearIndependent LL (fun j => (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F))`. Take `⟨_, hrk⟩` from `finrank_grQ F hF`. Conclude with `linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by rw [Fintype.card_fin, hrk, hr])`. Establish `key : ∀ m, m < e → ∀ j, PowerSeries.coeff m (a j) = 0`.

Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `hm`. Establish `hcl : ∀ k' : ℤ, (∑ j, PowerSeries.coeff m (a j) • g j k') ∈ F (1 - k')`.

Introduce `k'`. Establish `hS` using `h (k' + m)`. Establish `hle : F ((e : ℤ) - (k' + m)) ≤ F (1 - k')` using `hanti (by omega)`. Establish `hS'` using `hle hS`. Establish `hR : ∀ j, (∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k' + m - i)) - PowerSeries.coeff m (a j) • g j k' ∈ F (1 - k')`.

Introduce `j`. Take `⟨mj, hmj⟩` from `hsupp j`. Take `⟨N, hN1, hN2⟩ : ∃ N : ℕ, m < N ∧ ∀ i : ℕ, N ≤ i → k' + m - i < mj` from `⟨(k' + m - mj).toNat + m + 1, by omega, fun i hi => by`. Use `Int.self_le_toNat (k' + m - mj)` as an intermediate fact. Use the proof step `omega⟩`.

Establish `hsub : (Function.support fun i : ℕ => PowerSeries.coeff i (a j) • g j (k' + m - i)) ⊆ ↑(Finset.range N)`. Introduce `i hi`. Rewrite `hi` using `[Function.mem_support]`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `hne`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[hmj _ (hN2 i (not_lt.mp hne)), smul_zero]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hN1)]`. Simplify using `only [add_sub_cancel_right, add_sub_cancel_left]`. Use `sum_mem fun i hi => ?_` and prove the remaining obligations.

Take `⟨hne, -⟩` from `Finset.mem_erase.mp hi`. Break down `lt_or_gt_of_ne hne with hlt | hgt` into its components or cases. Rewrite using `[ih i hlt (by omega) j, zero_smul]`. Conclude with `zero_mem _`. Conclude with `Submodule.smul_mem _ _ (hanti (by omega) (hg j (k' + m - i)))`.

Establish `hsum` using `sub_mem hS' (sum_mem (t := Finset.univ) fun j _ => hR j)`. Rewrite `hsum` using `[Finset.sum_sub_distrib, sub_sub_cancel]`. Conclude with `hsum`. Establish `hz : ∑ j, PowerSeries.coeff m (a j) • (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) = 0`. Establish `hmk : ∑ j, PowerSeries.coeff m (a j) • (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) = (Submodule.mkQ _) (∑ j, PowerSeries.coeff m (a j) • (⟨g j, fun k _ => hg j k⟩ : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k))))`.

Simplify using `[map_sum]`. Rewrite using `[hmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_pi]`. Introduce `k _`. Simplify using `using hcl k`. Conclude with `fun j => Fintype.linearIndependent_iff.mp hli _ hz j`.

Introduce `j`. Conclude with `PowerSeries.X_pow_dvd_iff.mpr fun m hm => key m hm j`.
-/
theorem detect_pt {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (F : ℤ → Submodule LL D) (hF : IsFilt F) {r : ℕ} (hr : r = Module.finrank LL D)
    (g : Fin r → ℤ → D) (hsupp : ∀ j, ∃ m : ℤ, ∀ k < m, g j k = 0) (hg : ∀ j k, g j k ∈ F (-k))
    (hspan : Submodule.span LL (Set.range fun j =>
      (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F)) = ⊤)
    (a : Fin r → PowerSeries LL) (e : ℕ)
    (h : ∀ k : ℤ, (∑ j, ∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k - i)) ∈ F ((e : ℤ) - k)) :
    ∀ j, PowerSeries.X ^ e ∣ a j := by
  classical
  have hanti : Antitone F := hF.1
  have hli : LinearIndependent LL
      (fun j => (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F)) := by
    obtain ⟨_, hrk⟩ := finrank_grQ F hF
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
      (by rw [Fintype.card_fin, hrk, hr])
  have key : ∀ m, m < e → ∀ j, PowerSeries.coeff m (a j) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hcl : ∀ k' : ℤ, (∑ j, PowerSeries.coeff m (a j) • g j k') ∈ F (1 - k') := by
        intro k'
        have hS := h (k' + m)
        have hle : F ((e : ℤ) - (k' + m)) ≤ F (1 - k') := hanti (by omega)
        have hS' := hle hS
        have hR : ∀ j, (∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k' + m - i)) -
            PowerSeries.coeff m (a j) • g j k' ∈ F (1 - k') := by
          intro j
          obtain ⟨mj, hmj⟩ := hsupp j
          obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, m < N ∧ ∀ i : ℕ, N ≤ i → k' + m - i < mj :=
            ⟨(k' + m - mj).toNat + m + 1, by omega, fun i hi => by
              have := Int.self_le_toNat (k' + m - mj); omega⟩
          have hsub : (Function.support fun i : ℕ => PowerSeries.coeff i (a j) • g j (k' + m - i)) ⊆
              ↑(Finset.range N) := by
            intro i hi
            rw [Function.mem_support] at hi
            simp only [Finset.coe_range, Set.mem_Iio]
            by_contra hne
            apply hi
            rw [hmj _ (hN2 i (not_lt.mp hne)), smul_zero]
          rw [finsum_eq_sum_of_support_subset _ hsub,
            ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hN1)]
          simp only [add_sub_cancel_right, add_sub_cancel_left]
          refine sum_mem fun i hi => ?_
          obtain ⟨hne, -⟩ := Finset.mem_erase.mp hi
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [ih i hlt (by omega) j, zero_smul]
            exact zero_mem _
          · exact Submodule.smul_mem _ _ (hanti (by omega) (hg j (k' + m - i)))
        have hsum := sub_mem hS' (sum_mem (t := Finset.univ) fun j _ => hR j)
        rw [Finset.sum_sub_distrib, sub_sub_cancel] at hsum
        exact hsum
      have hz : ∑ j, PowerSeries.coeff m (a j) •
          (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) = 0 := by
        have hmk : ∑ j, PowerSeries.coeff m (a j) •
            (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) =
            (Submodule.mkQ _) (∑ j, PowerSeries.coeff m (a j) •
              (⟨g j, fun k _ => hg j k⟩ : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)))) := by
          simp [map_sum]
        rw [hmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.mem_pi]
        intro k _
        simpa using hcl k
      exact fun j => Fintype.linearIndependent_iff.mp hli _ hz j
  intro j
  exact PowerSeries.X_pow_dvd_iff.mpr fun m hm => key m hm j

end Formalism.MainNotions.N.Ln03.K8
