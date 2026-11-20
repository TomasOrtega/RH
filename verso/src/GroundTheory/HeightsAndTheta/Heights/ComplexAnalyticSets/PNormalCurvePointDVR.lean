import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurvePointDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `σ _ I w hI hic hdim hw`. Establish `: I.IsPrime` using `hI`. Set `m : Ideal (MvPolynomial σ ℂ)` to `RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)`. Set `S` to `Localization.AtPrime m`. Set `T` to `S ⧸ I.map (algebraMap (MvPolynomial σ ℂ) S)`.

Set `A` to `MvPolynomial σ ℂ ⧸ I`. Establish `hIm : I ≤ m` using `fun f hf ↦ RingHom.mem_ker.2 (hw f hf)`. Set `P : Ideal A` to `m.map (Ideal.Quotient.mk I)`. Establish `hmem : ∀ f, Ideal.Quotient.mk I f ∈ P ↔ f ∈ m` using `fun f ↦ Ideal.mem_quotient_iff_mem hIm`. Establish `hP : P.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIm)`.

Establish `: Ring.KrullDimLE 1 A` using `Ring.krullDimLE_iff.2 (by rw [hdim])`. Establish `: Ring.DimensionLEOne A` using `⟨fun hp0 hp ↦ hp.isMaximal_of_ne_bot hp0⟩`. Establish `: IsDedekindRing A` using `{ toIsIntegralClosure := hic }`. Establish `hP0 : P ≠ ⊥`. Introduce `h0`.

Establish `hmI : m ≤ I` using `fun f hf ↦ by`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0]`. Conclude with `(hmem f).2 hf`. Establish `hmax : m.IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ (fun z ↦ ⟨C z, by simp⟩)`. Establish `hfield : IsField A` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 (le_antisymm hIm hmI ▸ hmax)`.

Use `ringKrullDim_eq_zero_of_isField hfield` as an intermediate fact. Rewrite `this` using `[hdim]`. Conclude with `this` after adjusting the coercions. Establish `hsub : Algebra.algebraMapSubmonoid A m.primeCompl = P.primeCompl`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `fun h ↦ hf ((hmem f).1 h)`. Introduce `hx`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Conclude with `⟨f, fun h ↦ hx ((hmem f).2 h), rfl⟩`. Establish `hloc : IsLocalization (Algebra.algebraMapSubmonoid A m.primeCompl) T` using `inferInstance`. Establish `hlocP : IsLocalization.AtPrime T P`. Express the relevant statement in the definitionally equal form `IsLocalization P.primeCompl T`. Rewrite using `[← hsub]`.

Conclude with `hloc`. Establish `hdom : IsDomain T` using `IsLocalization.isDomain_of_le_nonZeroDivisors T (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors`. Conclude with `⟨hdom, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 T⟩`.
-/
theorem NormalCurvePointDVR.proof : NormalCurvePointDVR.Statement := by
  intro σ _ I w hI hic hdim hw
  have : I.IsPrime := hI
  let m : Ideal (MvPolynomial σ ℂ) := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  let S := Localization.AtPrime m
  let T := S ⧸ I.map (algebraMap (MvPolynomial σ ℂ) S)
  let A := MvPolynomial σ ℂ ⧸ I
  have hIm : I ≤ m := fun f hf ↦ RingHom.mem_ker.2 (hw f hf)
  let P : Ideal A := m.map (Ideal.Quotient.mk I)
  have hmem : ∀ f, Ideal.Quotient.mk I f ∈ P ↔ f ∈ m := fun f ↦ Ideal.mem_quotient_iff_mem hIm
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIm)

  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by rw [hdim])
  have : Ring.DimensionLEOne A := ⟨fun hp0 hp ↦ hp.isMaximal_of_ne_bot hp0⟩
  have : IsDedekindRing A := { toIsIntegralClosure := hic }

  have hP0 : P ≠ ⊥ := by
    intro h0
    have hmI : m ≤ I := fun f hf ↦ by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0]
      exact (hmem f).2 hf
    have hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun z ↦ ⟨C z, by simp⟩)
    have hfield : IsField A := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 (le_antisymm hIm hmI ▸ hmax)
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at this
    exact_mod_cast this

  have hsub : Algebra.algebraMapSubmonoid A m.primeCompl = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact fun h ↦ hf ((hmem f).1 h)
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨f, fun h ↦ hx ((hmem f).2 h), rfl⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid A m.primeCompl) T := inferInstance
  have hlocP : IsLocalization.AtPrime T P := by
    change IsLocalization P.primeCompl T
    rw [← hsub]
    exact hloc
  have hdom : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  exact ⟨hdom, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 T⟩

end

end GroundTheory.Heights₂.Heights
