import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatPrime

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

/- English proof (translation)
Rewrite using `[Lat.IB]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem f_mem_IB : f ξ ∈ Lat.IB f ξ := by
  rw [Lat.IB]
  exact Ideal.mem_span_singleton_self _

/- English proof (translation)
Rewrite using `[Lat.η, Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (f_mem_IB f ξ)`.
-/
theorem eta_mem_IB : Lat.η f ξ l M ∈ Lat.IB f ξ := by
  rw [Lat.η, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (f_mem_IB f ξ)

/- English proof (translation)
Rewrite using `[Lat.dpE, Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (eta_mem_IB f ξ l M) _ (Nat.succ_pos i))`.
-/
theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  rw [Lat.dpE, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (eta_mem_IB f ξ l M) _ (Nat.succ_pos i))

/- English proof (translation)
Simplify using `[Lat.dpE]`.
-/
theorem dpE_zero : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]

/- English proof (translation)
Unfold `Lat.sub at hx`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨w, rfl⟩ | ⟨i, rfl⟩` into its components or cases. Conclude with `⟨w, by rw [sub_self]; exact zero_mem _⟩`.

Consider the cases of `i with`. Consider the case `zero => exact ⟨1, by rw [dpE_zero, map_one, sub_self]; exact zero_mem _⟩`. Consider the case `succ i => exact ⟨0, by rw [map_zero, sub_zero]; exact dpE_succ_mem_IB f ξ l M i⟩`. Consider the case `zero => exact ⟨0, by rw [map_zero, sub_zero]; exact zero_mem _⟩`. Consider the case `one => exact ⟨1, by rw [map_one, sub_self]; exact zero_mem _⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Establish `e : x + y - f (a + b) = (x - f a) + (y - f b)` using `by rw [map_add]; ring`.

Rewrite using `[e]`. Conclude with `add_mem ha hb`. Consider the case `neg x _ hx`. Take `⟨a, ha⟩` from `hx`. Use `⟨-a, ?_⟩` and prove the remaining obligations.

Establish `e : -x - f (-a) = -(x - f a)` using `by rw [map_neg]; ring`. Rewrite using `[e]`. Conclude with `neg_mem ha`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Use `⟨a * b, ?_⟩` and prove the remaining obligations. Establish `e : x * y - f (a * b) = (x - f a) * y + f a * (y - f b)` using `by rw [map_mul]; ring`. Rewrite using `[e]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)`.
-/
theorem exists_sub_mem_IB {x : B} (hx : x ∈ Lat.sub f ξ l M) :
    ∃ a : W, x - f a ∈ Lat.IB f ξ := by
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨w, by rw [sub_self]; exact zero_mem _⟩
    · cases i with
      | zero => exact ⟨1, by rw [dpE_zero, map_one, sub_self]; exact zero_mem _⟩
      | succ i => exact ⟨0, by rw [map_zero, sub_zero]; exact dpE_succ_mem_IB f ξ l M i⟩
  | zero => exact ⟨0, by rw [map_zero, sub_zero]; exact zero_mem _⟩
  | one => exact ⟨1, by rw [map_one, sub_self]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have e : x + y - f (a + b) = (x - f a) + (y - f b) := by rw [map_add]; ring
    rw [e]
    exact add_mem ha hb
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a, ?_⟩
    have e : -x - f (-a) = -(x - f a) := by rw [map_neg]; ring
    rw [e]
    exact neg_mem ha
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    have e : x * y - f (a * b) = (x - f a) * y + f a * (y - f b) := by rw [map_mul]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)

/- English proof (translation)
Conclude with `(show ↥(Lat.sub f ξ l M) from x).2`.
-/
theorem ι_mem_sub (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := by
  exact (show ↥(Lat.sub f ξ l M) from x).2

/- English proof (translation)
Rewrite `ha` using `[Lat.IB, Ideal.mem_span_singleton]`. Take `⟨b, hb⟩` from `ha`. Establish `hm : 0 < m` using `hyp.one_le`. Use `hyp.gr 0 hm a b ?_` and prove the remaining obligations. Rewrite using `[pow_zero, mul_one, zero_add, pow_one]`.

Conclude with `hb`.
-/
theorem dvd_of_mem_IB {m : ℕ} (hyp : Lat.Hyp f ξ l m) {a : W} (ha : f a ∈ Lat.IB f ξ) : ξ ∣ a := by
  rw [Lat.IB, Ideal.mem_span_singleton] at ha
  obtain ⟨b, hb⟩ := ha
  have hm : 0 < m := hyp.one_le
  refine hyp.gr 0 hm a b ?_
  rw [pow_zero, mul_one, zero_add, pow_one]
  exact hb

end

/- English proof (translation)
Introduce `W B _ _ _ f ξ l M m hyp`. Use `haveI := hyp.dom`. Establish `key : ∀ a : W, f a ∈ Lat.IB f ξ ↔ ξ ∣ a`. Introduce `a`. Use `⟨fun ha => dvd_of_mem_IB f ξ l hyp ha, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_right _ _ (f_mem_IB f ξ)`. Establish `hq : ∀ a : W, ξ ∣ a ↔ Ideal.Quotient.mk (Ideal.span {ξ}) a = 0`. Introduce `a`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `htop`. Rewrite `htop` using `[Ideal.eq_top_iff_one]`. Simplify using `only [Lat.I, Ideal.mem_comap] at htop`.

Establish `h2 : f 1 ∈ Lat.IB f ξ` using `by rwa [map_one, ← map_one f] at htop`. Establish `h3` using `(hq 1).1 ((key 1).1 h2)`. Rewrite `h3` using `[map_one]`. Conclude with `one_ne_zero h3`. Introduce `x y hxy`.

Simplify using `only [Lat.I, Ideal.mem_comap, map_mul] at hxy ⊢`. Take `⟨a, ha⟩` from `exists_sub_mem_IB f ξ l M (ι_mem_sub f ξ l M x)`. Take `⟨b, hb⟩` from `exists_sub_mem_IB f ξ l M (ι_mem_sub f ξ l M y)`. Establish `hab : f (a * b) ∈ Lat.IB f ξ`. Establish `e : f (a * b) = Lat.ι f ξ l M x * Lat.ι f ξ l M y - ((Lat.ι f ξ l M x - f a) * Lat.ι f ξ l M y + f a * (Lat.ι f ξ l M y - f b))`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `sub_mem hxy (add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb))`. Establish `h` using `(hq (a * b)).1 ((key _).1 hab)`.

Rewrite `h` using `[map_mul, mul_eq_zero]`. Break down `h with h | h` into its components or cases. Use `left`. Establish `hfa : f a ∈ Lat.IB f ξ` using `(key a).2 ((hq a).2 h)`. Establish `e : Lat.ι f ξ l M x = (Lat.ι f ξ l M x - f a) + f a` using `by ring`.

Rewrite using `[e]`. Conclude with `add_mem ha hfa`. Use `right`. Establish `hfb : f b ∈ Lat.IB f ξ` using `(key b).2 ((hq b).2 h)`. Establish `e : Lat.ι f ξ l M y = (Lat.ι f ξ l M y - f b) + f b` using `by ring`.

Rewrite using `[e]`. Conclude with `add_mem hb hfb`.
-/
theorem I_isPrime : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → (Lat.I f ξ l M).IsPrime := by
  intro W B _ _ _ f ξ l M m hyp
  haveI := hyp.dom
  have key : ∀ a : W, f a ∈ Lat.IB f ξ ↔ ξ ∣ a := by
    intro a
    refine ⟨fun ha => dvd_of_mem_IB f ξ l hyp ha, ?_⟩
    rintro ⟨c, rfl⟩
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ (f_mem_IB f ξ)
  have hq : ∀ a : W, ξ ∣ a ↔ Ideal.Quotient.mk (Ideal.span {ξ}) a = 0 := by
    intro a
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨?_, ?_⟩
  · intro htop
    rw [Ideal.eq_top_iff_one] at htop
    simp only [Lat.I, Ideal.mem_comap] at htop
    have h2 : f 1 ∈ Lat.IB f ξ := by rwa [map_one, ← map_one f] at htop
    have h3 := (hq 1).1 ((key 1).1 h2)
    rw [map_one] at h3
    exact one_ne_zero h3
  · intro x y hxy
    simp only [Lat.I, Ideal.mem_comap, map_mul] at hxy ⊢
    obtain ⟨a, ha⟩ := exists_sub_mem_IB f ξ l M (ι_mem_sub f ξ l M x)
    obtain ⟨b, hb⟩ := exists_sub_mem_IB f ξ l M (ι_mem_sub f ξ l M y)
    have hab : f (a * b) ∈ Lat.IB f ξ := by
      have e : f (a * b) = Lat.ι f ξ l M x * Lat.ι f ξ l M y
          - ((Lat.ι f ξ l M x - f a) * Lat.ι f ξ l M y + f a * (Lat.ι f ξ l M y - f b)) := by
        rw [map_mul]; ring
      rw [e]
      exact sub_mem hxy (add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb))
    have h := (hq (a * b)).1 ((key _).1 hab)
    rw [map_mul, mul_eq_zero] at h
    rcases h with h | h
    · left
      have hfa : f a ∈ Lat.IB f ξ := (key a).2 ((hq a).2 h)
      have e : Lat.ι f ξ l M x = (Lat.ι f ξ l M x - f a) + f a := by ring
      rw [e]
      exact add_mem ha hfa
    · right
      have hfb : f b ∈ Lat.IB f ξ := (key b).2 ((hq b).2 h)
      have e : Lat.ι f ξ l M y = (Lat.ι f ξ l M y - f b) + f b := by ring
      rw [e]
      exact add_mem hb hfb

end GlobalTheory.CompanionTheory.LatPrime
