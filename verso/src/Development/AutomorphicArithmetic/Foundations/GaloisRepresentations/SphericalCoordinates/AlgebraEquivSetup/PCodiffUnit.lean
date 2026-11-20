import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `hU E _ _ M hMpos y t hy ht hloc`. Take `⟨_, e, he, hye⟩` from `hy`. Distinguish the cases in `hM1 : M = 1`. Use `⟨ht, 0, by simp [hM1], fun z _ => ⟨0, by simp⟩⟩` and prove the remaining obligations. Set `A : Ideal (𝓞 E)` to `{ carrier := {a | ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x} add_mem' := by`.

Introduce `a b ha hb z hz`. Take `⟨x1, h1⟩` from `ha z hz`. Take `⟨x2, h2⟩` from `hb z hz`. Conclude with `⟨x1 + x2, by push_cast; rw [add_mul, h1, h2, mul_add]⟩`. Use the proof step `zero_mem' := by`.

Introduce `z _`. Conclude with `⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce `c a ha z hz`. Take `⟨x, hx⟩` from `ha z hz`.

Use `⟨c * x, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Use `push_cast`. Rewrite using `[mul_assoc, hx]`. Use `ring }`.

Establish `hA : ∀ a : 𝓞 E, a ∈ A → ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x` using `fun a ha => ha`. Establish `htop : A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hPmax, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hMP : ((M : ℕ) : 𝓞 E) ∈ P` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`.

Take `⟨s, u, _, huP, hsu⟩` from `hloc P hPmax hMP`. Establish `heP : ((e : ℕ) : 𝓞 E) ∉ P`. Introduce `heP`. Take `⟨p, q, hpq⟩` from `Nat.isCoprime_iff_coprime.mpr he`. Establish `h1 : ((p : 𝓞 E) * ((e : ℕ) : 𝓞 E) + (q : 𝓞 E) * ((M : ℕ) : 𝓞 E)) = 1`.

Use `congrArg (fun n : ℤ => (n : 𝓞 E)) hpq` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Apply `hPmax.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← h1]`.

Conclude with `P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)`. Establish `hue : u * ((e : ℕ) : 𝓞 E) ∉ P`. Introduce `hmem`. Break down `hPmax.isPrime.mem_or_mem hmem with h | h` into its components or cases. Conclude with `huP h`.

Conclude with `heP h`. Apply `hue` to reduce the goal to its premises. Apply `hle` to reduce the goal to its premises. Apply `Ideal.mem_sup_left` to reduce the goal to its premises. Introduce `z hz`.

Take `⟨x, hx⟩` from `hye z hz`. Use `⟨s * x, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[mul_assoc, hx, ← mul_assoc, ← hsu]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hone : (1 : 𝓞 E) ∈ A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)}`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Take `⟨a, haA, m, hm, ham⟩` from `Submodule.mem_sup.mp hone`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp hm`.

Distinguish the cases in `ha0 : a = 0`. It suffices to derive a contradiction. Apply `hM1` to reduce the goal to its premises. Establish `hunit : IsUnit ((M : ℕ) : 𝓞 E)` using `isUnit_iff_exists_inv.mpr ⟨b, by rw [ha0, zero_add] at ham; rw [mul_comm]; exact ham⟩`. Establish `hspan : Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤` using `Ideal.span_singleton_eq_top.mpr hunit`.

Establish `hn` using `Ideal.absNorm_span_natCast (S := 𝓞 E) M`. Rewrite `hn` using `[hspan, Ideal.absNorm_top]`. Establish `hpos : Module.finrank ℤ (𝓞 E) ≠ 0` using `Module.finrank_pos.ne'`. Break down `Nat.pow_eq_one.mp hn.symm with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h hpos`. Take `⟨e', he', c', hc'⟩` from `hU E M a (-b) ha0 (by linear_combination ham)`. Use `⟨ht, e', he', fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hA a haA z hz`. Use `⟨c' * x, ?_⟩` and prove the remaining obligations.

Establish `hcoe : ((e' : ℕ) : E) = (a : E) * (c' : E)`. Use `congrArg (fun w : 𝓞 E => (w : E)) hc'` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this.symm`. Rewrite using `[hcoe, mul_comm (a : E), mul_assoc, hx]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.W2.Seed.pCodiffUnit :
    UnitMod → CodiffUnit := by
  intro hU E _ _ M hMpos y t hy ht hloc
  obtain ⟨_, e, he, hye⟩ := hy
  by_cases hM1 : M = 1
  · refine ⟨ht, 0, by simp [hM1], fun z _ => ⟨0, by simp⟩⟩
  let A : Ideal (𝓞 E) :=
    { carrier := {a | ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x}
      add_mem' := by
        intro a b ha hb z hz
        obtain ⟨x1, h1⟩ := ha z hz
        obtain ⟨x2, h2⟩ := hb z hz
        exact ⟨x1 + x2, by push_cast; rw [add_mul, h1, h2, mul_add]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro c a ha z hz
        obtain ⟨x, hx⟩ := ha z hz
        refine ⟨c * x, ?_⟩
        simp only [smul_eq_mul]
        push_cast
        rw [mul_assoc, hx]
        ring }
  have hA : ∀ a : 𝓞 E, a ∈ A → ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x :=
    fun a ha => ha
  have htop : A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMP : ((M : ℕ) : 𝓞 E) ∈ P :=
      hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨s, u, _, huP, hsu⟩ := hloc P hPmax hMP
    have heP : ((e : ℕ) : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr he
      have h1 : ((p : 𝓞 E) * ((e : ℕ) : 𝓞 E) + (q : 𝓞 E) * ((M : ℕ) : 𝓞 E)) = 1 := by
        have := congrArg (fun n : ℤ => (n : 𝓞 E)) hpq
        push_cast at this
        exact this
      apply hPmax.ne_top
      rw [Ideal.eq_top_iff_one, ← h1]
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hue : u * ((e : ℕ) : 𝓞 E) ∉ P := by
      intro hmem
      rcases hPmax.isPrime.mem_or_mem hmem with h | h
      · exact huP h
      · exact heP h
    apply hue
    apply hle
    apply Ideal.mem_sup_left
    intro z hz
    obtain ⟨x, hx⟩ := hye z hz
    refine ⟨s * x, ?_⟩
    push_cast
    rw [mul_assoc, hx, ← mul_assoc, ← hsu]
    ring
  have hone : (1 : 𝓞 E) ∈ A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, haA, m, hm, ham⟩ := Submodule.mem_sup.mp hone
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hm
  by_cases ha0 : a = 0
  · exfalso
    apply hM1
    have hunit : IsUnit ((M : ℕ) : 𝓞 E) :=
      isUnit_iff_exists_inv.mpr ⟨b, by rw [ha0, zero_add] at ham; rw [mul_comm]; exact ham⟩
    have hspan : Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have hn := Ideal.absNorm_span_natCast (S := 𝓞 E) M
    rw [hspan, Ideal.absNorm_top] at hn
    have hpos : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
    rcases Nat.pow_eq_one.mp hn.symm with h | h
    · exact h
    · exact absurd h hpos
  obtain ⟨e', he', c', hc'⟩ := hU E M a (-b) ha0 (by linear_combination ham)
  refine ⟨ht, e', he', fun z hz => ?_⟩
  obtain ⟨x, hx⟩ := hA a haA z hz
  refine ⟨c' * x, ?_⟩
  have hcoe : ((e' : ℕ) : E) = (a : E) * (c' : E) := by
    have := congrArg (fun w : 𝓞 E => (w : E)) hc'
    push_cast at this
    exact this.symm
  rw [hcoe, mul_comm (a : E), mul_assoc, hx]
  push_cast
  ring
