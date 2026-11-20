import Mathlib

namespace GlobalTheory.ThetaReal

/- English proof (translation)
Use `haveI : NeZero (n ^ J) := ⟨pow_ne_zero _ (by omega)⟩`. Take `⟨k, rfl⟩` from `ZMod.natCast_zmod_surjective y`. Rewrite `hy` using `[nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]`. Take `⟨j, rfl⟩ : ∃ j, J = j + 2` from `⟨J - 2, by omega⟩`. Establish `h1 : n * (n * n ^ j) ∣ n * k`.

Establish `: n * (n * n ^ j) = n ^ (j + 2)` using `by ring`. Rewrite using `[this]`. Conclude with `hy`. Establish `h2 : n * n ^ j ∣ k` using `Nat.dvd_of_mul_dvd_mul_left (by omega) h1`. Take `⟨c, rfl⟩` from `(Dvd.intro _ rfl : n ∣ n * n ^ j).trans h2`.

Conclude with `⟨(c : ZMod (n ^ (j + 2))), by rw [nsmul_eq_mul, Nat.cast_mul]⟩`.
-/
theorem zmod_pow_exists_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : 1 ≤ n) (hJ : 2 ≤ J)
    (y : ZMod (n ^ J)) (hy : n • y = 0) : ∃ w : ZMod (n ^ J), y = n • w := by
  haveI : NeZero (n ^ J) := ⟨pow_ne_zero _ (by omega)⟩
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hy
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 2 := ⟨J - 2, by omega⟩
  have h1 : n * (n * n ^ j) ∣ n * k := by
    have : n * (n * n ^ j) = n ^ (j + 2) := by ring
    rw [this]; exact hy
  have h2 : n * n ^ j ∣ k := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
  obtain ⟨c, rfl⟩ := (Dvd.intro _ rfl : n ∣ n * n ^ j).trans h2
  exact ⟨(c : ZMod (n ^ (j + 2))), by rw [nsmul_eq_mul, Nat.cast_mul]⟩

/- English proof (translation)
Introduce `κ n J M hn hJ hM X hX`. Substitute `hM` using the available equality. Establish `step : ∀ a : κ → ZMod (n ^ J), ∃ w : κ → ZMod (n ^ J), a + n • w ∈ AddSubgroup.closure X`. Introduce `a`. Take `⟨y, hy, hay⟩` from `hX a`.

Establish `: ∀ i, ∃ w : ZMod (n ^ J), y i = n • w` using `fun i => zmod_pow_exists_nsmul_of_nsmul_eq_zero n J hn hJ (y i) (congrFun hy i)`. Use `choose w hw using this`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `: n • w = y` using `funext fun i => (hw i).symm`. Rewrite using `[this]`.

Conclude with `AddSubgroup.subset_closure hay`. Establish `ind : ∀ (i : ℕ) (a : κ → ZMod (n ^ J)), ∃ w : κ → ZMod (n ^ J), a + n ^ i • w ∈ AddSubgroup.closure X`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro a; exact ⟨-a, by simp⟩`.

Consider the case `succ i ih`. Introduce `a`. Take `⟨w, hw⟩` from `ih a`. Take `⟨v, hv⟩` from `step (-w)`. Use `⟨v, ?_⟩` and prove the remaining obligations.

Establish `h` using `(AddSubgroup.closure X).add_mem hw ((AddSubgroup.closure X).nsmul_mem hv (n ^ i))`. Establish `e : a + n ^ i • w + n ^ i • (-w + n • v) = a + n ^ (i + 1) • v`. Rewrite using `[smul_add, smul_neg, smul_smul, pow_succ]`. Normalize the expressions using the abelian group laws. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Rewrite using `[eq_top_iff]`. Introduce `a _`. Take `⟨w, hw⟩` from `ind J a`. Establish `: n ^ J • w = 0`. Use function extensionality and compare the values at `i`.

Use `show n ^ J • w i = 0`. Rewrite using `[nsmul_eq_mul, ZMod.natCast_self, zero_mul]`. Rewrite `hw` using `[this, add_zero]`. Then use the resulting hypothesis.
-/
theorem closure_eq_top_of_meets_torsion_cosets :
    ∀ (κ : Type) (n J M : ℕ), 1 ≤ n → 2 ≤ J → M = n ^ J → ∀ X : Set (κ → ZMod M),
      (∀ a : κ → ZMod M, ∃ y : κ → ZMod M, n • y = 0 ∧ a + y ∈ X) →
      AddSubgroup.closure X = ⊤ := by
  intro κ n J M hn hJ hM X hX
  subst hM
  have step : ∀ a : κ → ZMod (n ^ J), ∃ w : κ → ZMod (n ^ J),
      a + n • w ∈ AddSubgroup.closure X := by
    intro a
    obtain ⟨y, hy, hay⟩ := hX a
    have : ∀ i, ∃ w : ZMod (n ^ J), y i = n • w := fun i =>
      zmod_pow_exists_nsmul_of_nsmul_eq_zero n J hn hJ (y i) (congrFun hy i)
    choose w hw using this
    refine ⟨w, ?_⟩
    have : n • w = y := funext fun i => (hw i).symm
    rw [this]
    exact AddSubgroup.subset_closure hay
  have ind : ∀ (i : ℕ) (a : κ → ZMod (n ^ J)), ∃ w : κ → ZMod (n ^ J),
      a + n ^ i • w ∈ AddSubgroup.closure X := by
    intro i
    induction i with
    | zero => intro a; exact ⟨-a, by simp⟩
    | succ i ih =>
      intro a
      obtain ⟨w, hw⟩ := ih a
      obtain ⟨v, hv⟩ := step (-w)
      refine ⟨v, ?_⟩
      have h := (AddSubgroup.closure X).add_mem hw ((AddSubgroup.closure X).nsmul_mem hv (n ^ i))
      have e : a + n ^ i • w + n ^ i • (-w + n • v) = a + n ^ (i + 1) • v := by
        rw [smul_add, smul_neg, smul_smul, pow_succ]; abel
      rwa [e] at h
  rw [eq_top_iff]
  intro a _
  obtain ⟨w, hw⟩ := ind J a
  have : n ^ J • w = 0 := by
    funext i
    show n ^ J • w i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rwa [this, add_zero] at hw

end GlobalTheory.ThetaReal
