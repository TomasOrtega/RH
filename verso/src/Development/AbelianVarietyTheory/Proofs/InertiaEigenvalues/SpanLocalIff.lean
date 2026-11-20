import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open IsDedekindDomain NumberField

namespace GlobalTheory.LocalSpanCriterion

/- English proof (translation)
Establish `hmem : ∀ y : V, y ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w) (Submodule.span (RingOfIntegers K) T) ↔ ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ Submodule.span (RingOfIntegers K) T` using `fun y => Iff.rfl`. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using Submodule.subset_span hy⟩`. Consider the case `zero => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨s, hs, hsy⟩` from `hy`. Take `⟨t, ht, htz⟩` from `hz`.

Use `⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩` and prove the remaining obligations. Establish `e : (s * t) • (y + z) = t • (s • y) + s • (t • z)`. Rewrite using `[smul_add, mul_smul, smul_comm s t y, mul_smul]`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ t hsy) (Submodule.smul_mem _ s htz)`.

Consider the case `smul a y _ hy`. Take `⟨s, hs, hsy⟩` from `hy`. Take `⟨⟨r, t⟩, hrt⟩` from `IsLocalization.mk'_surjective w.asIdeal.primeCompl a`. Use `⟨s * t, w.asIdeal.primeCompl.mul_mem hs t.2, ?_⟩` and prove the remaining obligations. Establish `hspec : (IsLocalization.mk' (Formalism.L2.Col.Ow w) r t) * algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) = algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) r` using `IsLocalization.mk'_spec _ r t`.

Simplify using `only at hrt`. Rewrite `hspec` using `[hrt]`. Establish `e : (s * (t : RingOfIntegers K)) • (a • y) = r • (s • y)`. Establish `ht : (t : RingOfIntegers K) • (a • y) = r • y`. Rewrite using `[← algebraMap_smul (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) (a • y), smul_smul, mul_comm, hspec, algebraMap_smul]`.

Rewrite using `[mul_comm, mul_smul, smul_comm (t : RingOfIntegers K) s, ht, smul_comm s r]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ r hsy`. Introduce and unpack `⟨s, hs, hsx⟩`. Establish `hu : IsUnit (algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) s)` using `IsLocalization.map_units (Formalism.L2.Col.Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)`.

Establish `h1 : s • x ∈ Submodule.span (Formalism.L2.Col.Ow w) T`. Use `Submodule.span_le_restrictScalars (RingOfIntegers K) (Formalism.L2.Col.Ow w) T hsx` as an intermediate fact. Conclude with `this`. Rewrite `h1` using `[← algebraMap_smul (Formalism.L2.Col.Ow w) s x]`. Take `⟨u, hu'⟩` from `hu`.

Establish `h2` using `Submodule.smul_mem _ (↑u⁻¹ : Formalism.L2.Col.Ow w) h1`. Rewrite `h2` using `[← hu', smul_smul, Units.inv_mul, one_smul]`. Then use the resulting hypothesis.
-/
theorem span_local_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module (RingOfIntegers K) V] (w : HeightOneSpectrum (RingOfIntegers K))
    [Module (Formalism.L2.Col.Ow w) V] [IsScalarTower (RingOfIntegers K) (Formalism.L2.Col.Ow w) V]
    (T : Set V) (x : V) :
    x ∈ Submodule.span (Formalism.L2.Col.Ow w) T ↔
      x ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) := by
  have hmem : ∀ y : V, y ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) ↔
      ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ Submodule.span (RingOfIntegers K) T := fun y => Iff.rfl
  rw [hmem]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using Submodule.subset_span hy⟩
    | zero => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨t, ht, htz⟩ := hz
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
      have e : (s * t) • (y + z) = t • (s • y) + s • (t • z) := by
        rw [smul_add, mul_smul, smul_comm s t y, mul_smul]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ t hsy) (Submodule.smul_mem _ s htz)
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl a
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs t.2, ?_⟩
      have hspec : (IsLocalization.mk' (Formalism.L2.Col.Ow w) r t) *
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) =
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) r := IsLocalization.mk'_spec _ r t
      simp only at hrt
      rw [hrt] at hspec
      have e : (s * (t : RingOfIntegers K)) • (a • y) = r • (s • y) := by
        have ht : (t : RingOfIntegers K) • (a • y) = r • y := by
          rw [← algebraMap_smul (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) (a • y), smul_smul,
            mul_comm, hspec, algebraMap_smul]
        rw [mul_comm, mul_smul, smul_comm (t : RingOfIntegers K) s, ht, smul_comm s r]
      rw [e]
      exact Submodule.smul_mem _ r hsy
  · rintro ⟨s, hs, hsx⟩
    have hu : IsUnit (algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) s) :=
      IsLocalization.map_units (Formalism.L2.Col.Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)
    have h1 : s • x ∈ Submodule.span (Formalism.L2.Col.Ow w) T := by
      have := Submodule.span_le_restrictScalars (RingOfIntegers K) (Formalism.L2.Col.Ow w) T hsx
      exact this
    rw [← algebraMap_smul (Formalism.L2.Col.Ow w) s x] at h1
    obtain ⟨u, hu'⟩ := hu
    have h2 := Submodule.smul_mem _ (↑u⁻¹ : Formalism.L2.Col.Ow w) h1
    rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

end GlobalTheory.LocalSpanCriterion
