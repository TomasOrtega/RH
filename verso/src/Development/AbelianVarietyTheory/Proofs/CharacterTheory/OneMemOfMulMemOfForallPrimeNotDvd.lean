import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ∀ x : X, ∃ f ∈ S, f x = 1`. Introduce `x`. Take `⟨d, hd⟩` from `Int.subgroup_cyclic (S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x))`. Rewrite `hd` using `[← AddSubgroup.zmultiples_eq_closure]`. Establish `hd1 : d.natAbs = 1`.

Rewrite using `[Nat.eq_one_iff_not_exists_prime_dvd]`. Introduce `p pp hpd`. Take `⟨f, hf, hnd⟩` from `hp x p pp`. Apply `hnd` to reduce the goal to its premises. Establish `hmem : f x ∈ AddSubgroup.zmultiples d`.

Rewrite using `[← hd]`. Conclude with `⟨f, hf, rfl⟩`. Conclude with `(Int.natCast_dvd.mpr hpd).trans (Int.mem_zmultiples_iff.mp hmem)`. Establish `: (1 : ℤ) ∈ AddSubgroup.zmultiples d`. Rewrite using `[Int.mem_zmultiples_iff]`.

Conclude with `isUnit_iff_dvd_one.mp (Int.isUnit_iff_natAbs_eq.mpr hd1)`. Rewrite `this` using `[← hd]`. Take `⟨f, hf, hfx⟩` from `this`. Conclude with `⟨f, hf, hfx⟩`. Use `choose f hfS hf1 using h1`.

Establish `key : ∀ s : Finset X, 1 - ∏ x ∈ s, (1 - f x) ∈ S`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.prod_insert ha]`. Establish `e : 1 - (1 - f a) * ∏ x ∈ s, (1 - f x) = f a + (1 - ∏ x ∈ s, (1 - f x)) - f a * (1 - ∏ x ∈ s, (1 - f x))` using `by ring`. Rewrite using `[e]`. Conclude with `S.sub_mem (S.add_mem (hfS a) ih) (hmul _ (hfS a) _ ih)`. Use `haveI := Fintype.ofFinite X`.

Establish `h0 : ∏ x : X, (1 - f x) = 0`. Use function extensionality and compare the values at `y`. Rewrite using `[Finset.prod_apply]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ y) (by simp [hf1])`. Simplify `key Finset.univ` using `[h0]`.
-/
theorem one_mem_of_mul_mem_of_forall_prime_not_dvd (X : Type) [Finite X]
    (S : AddSubgroup (X → ℤ)) (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hp : ∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) : (1 : X → ℤ) ∈ S := by
  classical
  have h1 : ∀ x : X, ∃ f ∈ S, f x = 1 := by
    intro x
    obtain ⟨d, hd⟩ := Int.subgroup_cyclic (S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x))
    rw [← AddSubgroup.zmultiples_eq_closure] at hd
    have hd1 : d.natAbs = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p pp hpd
      obtain ⟨f, hf, hnd⟩ := hp x p pp
      apply hnd
      have hmem : f x ∈ AddSubgroup.zmultiples d := by
        rw [← hd]
        exact ⟨f, hf, rfl⟩
      exact (Int.natCast_dvd.mpr hpd).trans (Int.mem_zmultiples_iff.mp hmem)
    have : (1 : ℤ) ∈ AddSubgroup.zmultiples d := by
      rw [Int.mem_zmultiples_iff]
      exact isUnit_iff_dvd_one.mp (Int.isUnit_iff_natAbs_eq.mpr hd1)
    rw [← hd] at this
    obtain ⟨f, hf, hfx⟩ := this
    exact ⟨f, hf, hfx⟩
  choose f hfS hf1 using h1
  have key : ∀ s : Finset X, 1 - ∏ x ∈ s, (1 - f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have e : 1 - (1 - f a) * ∏ x ∈ s, (1 - f x)
          = f a + (1 - ∏ x ∈ s, (1 - f x)) - f a * (1 - ∏ x ∈ s, (1 - f x)) := by ring
      rw [e]
      exact S.sub_mem (S.add_mem (hfS a) ih) (hmul _ (hfS a) _ ih)
  haveI := Fintype.ofFinite X
  have h0 : ∏ x : X, (1 - f x) = 0 := by
    funext y
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [hf1])
  simpa [h0] using key Finset.univ

end GlobalTheory
