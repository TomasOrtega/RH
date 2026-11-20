import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassDegTypeLeCycleTypeStatement

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

/- English proof (translation)
Use `(GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun _ => True)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.filter_true, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]`. Establish `hN : (N.factorial : ℝ) ≠ 0` using `by positivity`. Conclude with `div_self hN`.
-/
theorem mass_true_le_one (g : ℕ) [Fact g.Prime] (N : ℕ) : (mass g N fun _ => True) ≤ 1 := by
  refine (GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun _ => True)).trans (le_of_eq ?_)
  rw [Finset.filter_true, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  exact div_self hN

/- English proof (translation)
Take `⟨hmon, hdeg, -, -⟩` from `mem_sqSet.1 hh`. Establish `hh0 : h ≠ 0` using `hmon.ne_zero`. Unfold `mass`. Use `set S := (sqSet g N).filter fun f => h ∣ f with hS`. Establish `hfac : ∀ f ∈ S, h * (f /ₘ h) = f`.

Introduce `f hf`. Establish `hd : h ∣ f` using `(Finset.mem_filter.1 hf).2`. Establish `e` using `Polynomial.modByMonic_add_div f h`. Rewrite `e` using `[(Polynomial.modByMonic_eq_zero_iff_dvd hmon).2 hd, zero_add]`. Then use the resulting hypothesis. Establish `hmem : ∀ f ∈ S, f /ₘ h ∈ sqSet g (N - a)`.

Introduce `f hf`. Take `⟨fmon, fdeg, fsq, fc0⟩` from `mem_sqSet.1 (Finset.mem_filter.1 hf).1`. Establish `e` using `hfac f hf`. Establish `umon : (f /ₘ h).Monic` using `hmon.of_mul_monic_left (by rw [e]; exact fmon)`. Use `mem_sqSet.2 ⟨umon, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hd` using `hmon.natDegree_mul umon`. Rewrite `hd` using `[e, fdeg, hdeg]`. Use linear arithmetic over natural numbers and integers. Conclude with `Squarefree.of_mul_right (by rw [e]; exact fsq)`. Introduce `hz`.

Apply `fc0` to reduce the goal to its premises. Rewrite using `[← e, Polynomial.mul_coeff_zero, hz, mul_zero]`. Establish `hinj : Set.InjOn (fun f => f /ₘ h) (S : Set (ZMod g)[X])`. Introduce `f hf f' hf' hq`. Rewrite using `[← hfac f hf, ← hfac f' hf']`.

Conclude with `congrArg (h * ·) hq`. Establish `hterm : ∀ f ∈ S, ((torusCard g f : ℝ))⁻¹ = ((torusCard g h : ℝ))⁻¹ * ((torusCard g (f /ₘ h) : ℝ))⁻¹`. Introduce `f hf`. Establish `e` using `hfac f hf`. Establish `hu0 : f /ₘ h ≠ 0`.

Introduce `hz`. Rewrite `e` using `[hz, mul_zero]`. Conclude with `(mem_sqSet.1 (Finset.mem_filter.1 hf).1).1.ne_zero e.symm`. Use `conv_lhs => rw [← e]`. Rewrite using `[torusCard_mul hh0 hu0, Nat.cast_mul, mul_inv]`.

Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.mul_sum]`. Use `mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))` and prove the remaining obligations. Rewrite using `[← Finset.sum_image (f := fun u => ((torusCard g u : ℝ))⁻¹) hinj, Finset.filter_true]`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _))` and prove the remaining obligations. Introduce `u hu`.

Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hu`. Conclude with `hmem f hf`.
-/
theorem mass_dvd_le (g : ℕ) [Fact g.Prime] (N a : ℕ) (h : (ZMod g)[X]) (hh : h ∈ sqSet g a) :
    (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ * mass g (N - a) fun _ => True := by
  obtain ⟨hmon, hdeg, -, -⟩ := mem_sqSet.1 hh
  have hh0 : h ≠ 0 := hmon.ne_zero
  unfold mass
  set S := (sqSet g N).filter fun f => h ∣ f with hS
  have hfac : ∀ f ∈ S, h * (f /ₘ h) = f := by
    intro f hf
    have hd : h ∣ f := (Finset.mem_filter.1 hf).2
    have e := Polynomial.modByMonic_add_div f h
    rwa [(Polynomial.modByMonic_eq_zero_iff_dvd hmon).2 hd, zero_add] at e
  have hmem : ∀ f ∈ S, f /ₘ h ∈ sqSet g (N - a) := by
    intro f hf
    obtain ⟨fmon, fdeg, fsq, fc0⟩ := mem_sqSet.1 (Finset.mem_filter.1 hf).1
    have e := hfac f hf
    have umon : (f /ₘ h).Monic := hmon.of_mul_monic_left (by rw [e]; exact fmon)
    refine mem_sqSet.2 ⟨umon, ?_, ?_, ?_⟩
    · have hd := hmon.natDegree_mul umon
      rw [e, fdeg, hdeg] at hd
      omega
    · exact Squarefree.of_mul_right (by rw [e]; exact fsq)
    · intro hz
      apply fc0
      rw [← e, Polynomial.mul_coeff_zero, hz, mul_zero]
  have hinj : Set.InjOn (fun f => f /ₘ h) (S : Set (ZMod g)[X]) := by
    intro f hf f' hf' hq
    rw [← hfac f hf, ← hfac f' hf']
    exact congrArg (h * ·) hq
  have hterm : ∀ f ∈ S, ((torusCard g f : ℝ))⁻¹ =
      ((torusCard g h : ℝ))⁻¹ * ((torusCard g (f /ₘ h) : ℝ))⁻¹ := by
    intro f hf
    have e := hfac f hf
    have hu0 : f /ₘ h ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at e
      exact (mem_sqSet.1 (Finset.mem_filter.1 hf).1).1.ne_zero e.symm
    conv_lhs => rw [← e]
    rw [torusCard_mul hh0 hu0, Nat.cast_mul, mul_inv]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [← Finset.sum_image (f := fun u => ((torusCard g u : ℝ))⁻¹) hinj, Finset.filter_true]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
  intro u hu
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hu
  exact hmem f hf

/- English proof (translation)
Introduce `g _`. Use `⟨mass_true_le_one g, fun N a h hh => ?_⟩` and prove the remaining obligations. Use `(mass_dvd_le g N a h hh).trans ?_` and prove the remaining obligations. Conclude with `mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (mass_true_le_one g _)`.
-/
theorem divisor_bound : ∀ (g : ℕ) [Fact g.Prime], (∀ N : ℕ, (mass g N fun _ => True) ≤ 1) ∧
    ∀ (N a : ℕ), ∀ h ∈ sqSet g a, (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ := by
  intro g _
  refine ⟨mass_true_le_one g, fun N a h hh => ?_⟩
  refine (mass_dvd_le g N a h hh).trans ?_
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (mass_true_le_one g _)

end GlobalTheory.BadShare
