import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`.

Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Establish `e : (a * b) • (x + y) = b • (a • x) + a • (b • y)`. Rewrite using `[smul_add, mul_smul, mul_comm, mul_smul]`. Rewrite using `[smul_comm a b x, smul_comm b a y]`.

Rewrite using `[e]`. Conclude with `L.add_mem (L.smul_mem _ hax) (L.smul_mem _ hby)`. Consider the case `smul k x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨n, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) k`.

Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Establish `hdK : algebraMap (𝓞 K) K d ≠ 0`. Simplify using `using hd0`. Use `⟨d * a, mul_ne_zero hd0 ha, ?_⟩` and prove the remaining obligations. Establish `e : (d * a) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) • x) = n • (a • x)`.

Use extensionality with `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Simplify using `only [Algebra.smul_def, map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `L.smul_mem _ hax`.
-/
theorem exists_ne_zero_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K)) {v : Fin m → K}
    (hv : v ∈ Submodule.span K (L : Set (Fin m → K))) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, mul_comm, mul_smul]
      rw [smul_comm a b x, smul_comm b a y]
    rw [e]
    exact L.add_mem (L.smul_mem _ hax) (L.smul_mem _ hby)
  | smul k x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      simpa using hd0
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have e : (d * a) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) • x) = n • (a • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [e]
    exact L.smul_mem _ hax

/- English proof (translation)
Introduce `K _ _ m L hL x h`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective L x`. Take `⟨a, ha, hav⟩` from `exists_ne_zero_smul_mem_of_mem_span L (show v ∈ Submodule.span K (L : Set (Fin m → K)) by rw [hL.2]; trivial)`. Establish `hmem : a ∈ Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) (Submodule.Quotient.mk v)`. Rewrite using `[Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul]`.

Conclude with `(Submodule.Quotient.mk_eq_zero L).2 hav`. Rewrite `hmem` using `[h]`. Conclude with `ha ((Submodule.mem_bot _).1 hmem)`.
-/
theorem torsionOf_quot_lat_ne_bot : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L →
    ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  intro K _ _ m L hL x h
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_smul_mem_of_mem_span L
    (show v ∈ Submodule.span K (L : Set (Fin m → K)) by rw [hL.2]; trivial)
  have hmem : a ∈ Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) (Submodule.Quotient.mk v) := by
    rw [Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero L).2 hav
  rw [h] at hmem
  exact ha ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
