import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsLZBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint

namespace GlobalTheory.SubmoduleScalarClosure

open NumberField

/- English proof (translation)
Establish `h` using `L.smul_mem (m : 𝓞 E) hx`. Rewrite `h` using `[← algebraMap_smul E (m : 𝓞 E) x, map_intCast]`. Then use the resulting hypothesis.
-/
theorem int_smul_mem_submodule {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (𝓞 E) (Fin r → E)) {x : Fin r → E} (hx : x ∈ L) (m : ℤ) :
    (m : E) • x ∈ L := by
  have h := L.smul_mem (m : 𝓞 E) hx
  rwa [← algebraMap_smul E (m : 𝓞 E) x, map_intCast] at h

/- English proof (translation)
Establish `h` using `L.smul_mem a hx`. Rewrite `h` using `[← algebraMap_smul E a x]`. Then use the resulting hypothesis.
-/
theorem integer_ring_smul_mem_submodule {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (𝓞 E) (Fin r → E)) {x : Fin r → E} (hx : x ∈ L) (a : 𝓞 E) :
    (a : E) • x ∈ L := by
  have h := L.smul_mem a hx
  rwa [← algebraMap_smul E a x] at h

/- English proof (translation)
Set `S : Submodule E (Fin r → E)` to `{ carrier := {w | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • w ∈ X.Λ} add_mem' := by`. Introduce and unpack `a b ⟨n, hn, ha⟩ ⟨k, hk, hb⟩`. Use `⟨n * k, mul_ne_zero hn hk, ?_⟩` and prove the remaining obligations. Establish `h` using `X.Λ.add_mem (int_smul_mem_submodule X.Λ ha k) (int_smul_mem_submodule X.Λ hb n)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (k : E) (n : E)]`. Use the proof step `zero_mem' := ⟨1, one_ne_zero, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c w ⟨n, hn, hw⟩`. Establish `hc : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)`.

Take `⟨d, hd, hint⟩` from `hc.exists_integral_multiple`. Use `⟨d * n, mul_ne_zero hd hn, ?_⟩` and prove the remaining obligations. Establish `h` using `integer_ring_smul_mem_submodule X.Λ hw ⟨d • c, hint⟩`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `show _ = (d • c) • ((n : E) • w)`.

Rewrite using `[smul_smul, smul_smul, zsmul_eq_mul]`. Use `congr 1`. Use `push_cast`. Use `ring }`. Establish `hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ S` using `Submodule.span_le.mpr fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩`.

Rewrite `hle` using `[X.Λ_span]`. Take `⟨n, hn, h⟩` from `hle (Submodule.mem_top : v ∈ ⊤)`. Conclude with `⟨n, hn, h⟩`.
-/
theorem main {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E) :
    ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ (↑n : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by

  let S : Submodule E (Fin r → E) :=
    { carrier := {w | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • w ∈ X.Λ}
      add_mem' := by
        rintro a b ⟨n, hn, ha⟩ ⟨k, hk, hb⟩
        refine ⟨n * k, mul_ne_zero hn hk, ?_⟩
        have h := X.Λ.add_mem (int_smul_mem_submodule X.Λ ha k) (int_smul_mem_submodule X.Λ hb n)
        convert h using 1
        rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (k : E) (n : E)]
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c w ⟨n, hn, hw⟩

        have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
        obtain ⟨d, hd, hint⟩ := hc.exists_integral_multiple
        refine ⟨d * n, mul_ne_zero hd hn, ?_⟩
        have h := integer_ring_smul_mem_submodule X.Λ hw ⟨d • c, hint⟩
        convert h using 1
        show _ = (d • c) • ((n : E) • w)
        rw [smul_smul, smul_smul, zsmul_eq_mul]
        congr 1
        push_cast
        ring }
  have hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ S :=
    Submodule.span_le.mpr fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  rw [X.Λ_span] at hle
  obtain ⟨n, hn, h⟩ := hle (Submodule.mem_top : v ∈ ⊤)
  exact ⟨n, hn, h⟩

end GlobalTheory.SubmoduleScalarClosure
