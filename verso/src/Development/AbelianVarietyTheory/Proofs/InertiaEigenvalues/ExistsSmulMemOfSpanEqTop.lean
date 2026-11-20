import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

namespace GlobalTheory.DenominatorOfSpan

open GlobalTheory.UnitLemma

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (L : Set A)` using `by rw [hL]; exact Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem b hay`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem a hbz`. Consider the case `smul e y _ hy`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨⟨n, s⟩, hs⟩` from `IsLocalization.surj (nonZeroDivisors O) e`. Establish `hs' : e * algebraMap O E (s : O) = algebraMap O E n` using `hs`. Use `⟨a * (s : O), mul_ne_zero ha (nonZeroDivisors.ne_zero s.2), ?_⟩` and prove the remaining obligations. Establish `h1 : (s : O) • e • y = n • y`.

Rewrite using `[← algebraMap_smul E (s : O), ← mul_smul, mul_comm, hs', algebraMap_smul]`. Rewrite using `[mul_smul, h1, smul_comm]`. Conclude with `L.smul_mem n hay`.
-/
theorem exists_smul_mem_of_span_eq_top {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (L : Submodule O A) (hL : Submodule.span E (L : Set A) = ⊤) (x : A) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set A) := by rw [hL]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul e y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have hs' : e * algebraMap O E (s : O) = algebraMap O E n := hs
    refine ⟨a * (s : O), mul_ne_zero ha (nonZeroDivisors.ne_zero s.2), ?_⟩
    have h1 : (s : O) • e • y = n • y := by
      rw [← algebraMap_smul E (s : O), ← mul_smul, mul_comm, hs', algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.smul_mem n hay

/- English proof (translation)
The claim follows from `exists_smul_mem_of_span_eq_top L hL x`.
-/
theorem exists_denominator {K : UQ} (B : InvAlg K) (L : Submodule K.O B.A)
    (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L :=
  exists_smul_mem_of_span_eq_top L hL x

end GlobalTheory.DenominatorOfSpan
