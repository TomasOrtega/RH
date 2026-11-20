import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.LocWLemmas

namespace GlobalTheory.SmulMemOfIsLattice

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (B : Set (Formalism.L2.Col.Sp E n))`. Rewrite using `[hB.span_eq_top]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩`.

Consider the case `zero => exact ⟨1, one_mem _, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨r, hr, hry⟩` from `hy`. Take `⟨s, hs, hsz⟩` from `hz`. Use `⟨r * s, mul_mem hr hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `B.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `B.smul_mem _ hry`. Rewrite using `[mul_smul]`.

Conclude with `B.smul_mem _ hsz`. Consider the case `smul c y _ hy`. Take `⟨r, hr, hry⟩` from `hy`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c`. Use `⟨r * b, mul_mem hr hb, ?_⟩` and prove the remaining obligations.

Establish `hb0 : algebraMap (NumberField.RingOfIntegers E) E b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Establish `h : (r * b) • ((algebraMap (NumberField.RingOfIntegers E) E a / algebraMap (NumberField.RingOfIntegers E) E b) • y) = a • (r • y)`. Rewrite using `[← algebraMap_smul E (r * b), ← algebraMap_smul E a, ← algebraMap_smul E r y, smul_smul, smul_smul, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h]`. Conclude with `B.smul_mem _ hry`.
-/
theorem exists_smul_mem_of_isLattice {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (B : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n))
    (hB : Submodule.IsLattice E B) (x : Formalism.L2.Col.Sp E n) :
    ∃ r ∈ nonZeroDivisors (NumberField.RingOfIntegers E), r • x ∈ B := by
  have hx : x ∈ Submodule.span E (B : Set (Formalism.L2.Col.Sp E n)) := by
    rw [hB.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_mem hr hs, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ hry
    · rw [mul_smul]; exact B.smul_mem _ hsz
  | smul c y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    refine ⟨r * b, mul_mem hr hb, ?_⟩
    have hb0 : algebraMap (NumberField.RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h : (r * b) • ((algebraMap (NumberField.RingOfIntegers E) E a / algebraMap (NumberField.RingOfIntegers E) E b) • y) = a • (r • y) := by
      rw [← algebraMap_smul E (r * b), ← algebraMap_smul E a, ← algebraMap_smul E r y, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h]
    exact B.smul_mem _ hry

end GlobalTheory.SmulMemOfIsLattice
