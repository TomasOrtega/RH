import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolIn

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Establish `hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n ≤ I ^ m`. Use `FractionalIdeal.mul_le.2 fun a ha b hb => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 ha`. Rewrite using `[smul_mul_assoc, mul_comm]`. Conclude with `(FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h b hb)))`.

Establish `h2 : I ^ (-n) * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n) ≤ I ^ (-n) * I ^ m` using `mul_right_mono hle`. Rewrite `h2` using `[mul_comm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y), ← mul_assoc, ← zpow_add₀ hI, neg_add_cancel, zpow_zero, one_mul, ← zpow_add₀ hI, neg_add_eq_sub]`. Conclude with `h2 (FractionalIdeal.mem_spanSingleton_self _ y)`.
-/
theorem mem_of_mul (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hI : I ≠ 0) (m n : ℤ) (y : D.host.E)
    (h : ∀ x ∈ I ^ n, x * y ∈ I ^ m) : y ∈ I ^ (m - n) := by
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n ≤ I ^ m := by
    refine FractionalIdeal.mul_le.2 fun a ha b hb => ?_
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
    rw [smul_mul_assoc, mul_comm]
    exact (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h b hb)))
  have h2 : I ^ (-n) * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n) ≤ I ^ (-n) * I ^ m :=
    mul_right_mono hle
  rw [mul_comm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y), ← mul_assoc, ← zpow_add₀ hI,
    neg_add_cancel, zpow_zero, one_mul, ← zpow_add₀ hI, neg_add_eq_sub] at h2
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ y)

/- English proof (translation)
Establish `key : ∃ y' : Fin D.R.rS → D.host.E, (∀ a : Fin D.R.rS, y' a ∈ (ddS D ^ (-((D.R.rS : ℤ) - ((a : Fin D.R.rS) : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ v = ∑ a, y' a • F0.e a` using `by clear hy`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, x, hx, rfl⟩` from `hx`. Use `⟨Pi.single a x, fun b => ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Simplify using `using hx`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `FractionalIdeal.zero_mem _`.

Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp), Pi.single_eq_same]`. Consider the case `zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩`. Consider the case `add x w _ _ hx hw`. Take `⟨y1, h1, rfl⟩` from `hx`. Take `⟨y2, h2, rfl⟩` from `hw`.

Conclude with `⟨y1 + y2, fun a => (FractionalIdeal.mem_coe).1 (Submodule.add_mem _ ((FractionalIdeal.mem_coe).2 (h1 a)) ((FractionalIdeal.mem_coe).2 (h2 a))), by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul c x _ hx`. Take `⟨y1, h1, rfl⟩` from `hx`. Use `⟨fun a => (c : D.host.E) * y1 a, fun a => ?_, ?_⟩` and prove the remaining obligations. Use `(FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h1 a)))` as an intermediate fact.

Rewrite `this` using `[Algebra.smul_def]`. Then use the resulting hypothesis. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_assoc, Algebra.smul_def]`. Take `⟨y', hy', hv'⟩` from `key`.

Establish `hyy : y = y'`. Establish `h` using `F0.e_indep`. Rewrite `h` using `[Fintype.linearIndependent_iff]`. Use function extensionality and compare the values at `b`. Use `h (y - y') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, ← hv', sub_self]) b` as an intermediate fact.

Conclude with `sub_eq_zero.1 this`. Rewrite using `[hyy]`. Conclude with `hy' a`.
-/
theorem coef_XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V} (hv : v ∈ XS D F0)
    (y : Fin D.R.rS → D.host.E) (hy : v = ∑ a, y a • F0.e a) (a : Fin D.R.rS) :
    y a ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have key : ∃ y' : Fin D.R.rS → D.host.E, (∀ a : Fin D.R.rS, y' a ∈ (ddS D ^ (-((D.R.rS : ℤ) - ((a : Fin D.R.rS) : ℕ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ v = ∑ a, y' a • F0.e a := by
    clear hy
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, x, hx, rfl⟩ := hx
      refine ⟨Pi.single a x, fun b => ?_, ?_⟩
      · by_cases h : b = a
        · subst h
          simpa using hx
        · rw [Pi.single_eq_of_ne h]
          exact FractionalIdeal.zero_mem _
      · rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
          Pi.single_eq_same]
    | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
    | add x w _ _ hx hw =>
      obtain ⟨y1, h1, rfl⟩ := hx
      obtain ⟨y2, h2, rfl⟩ := hw
      exact ⟨y1 + y2, fun a => (FractionalIdeal.mem_coe).1 (Submodule.add_mem _ ((FractionalIdeal.mem_coe).2 (h1 a))
        ((FractionalIdeal.mem_coe).2 (h2 a))), by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨y1, h1, rfl⟩ := hx
      refine ⟨fun a => (c : D.host.E) * y1 a, fun a => ?_, ?_⟩
      · have := (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h1 a)))
        rwa [Algebra.smul_def] at this
      · rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← smul_assoc, Algebra.smul_def]
  obtain ⟨y', hy', hv'⟩ := key
  have hyy : y = y' := by
    have h := F0.e_indep
    rw [Fintype.linearIndependent_iff] at h
    funext b
    have := h (y - y') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, ← hv', sub_self]) b
    exact sub_eq_zero.1 this
  rw [hyy]
  exact hy' a

end Formalism.L2.SG.Pf.ZsVolLat

end
