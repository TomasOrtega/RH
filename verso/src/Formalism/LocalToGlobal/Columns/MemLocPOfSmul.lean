import Mathlib
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.AdjointFrobeniusPreservesRamified
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV

section L3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Take `⟨s', hs', h'⟩` from `(mem_locP P N _).1 h`. Use `(mem_locP P N w).2 ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs' hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]` and apply the resulting hypothesis.
-/
theorem mem_localization_of_smul_mem'₂ (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) {s : 𝓞 E}
    (hs : s ∉ P.asIdeal) {w : Sp E n} (h : s • w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  obtain ⟨s', hs', h'⟩ := (mem_locP P N _).1 h
  refine (mem_locP P N w).2 ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs' hs, ?_⟩
  rwa [mul_smul]

/- English proof (translation)
Take `⟨β, hβN, hβI⟩` from `exists_locBasis P hN`. Use `⟨β.equivFun.symm, fun z => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mem_localization_standardLattice]`. Introduce `i`. Use `hβI _ h i` as an intermediate fact.

Rewrite `this` using `[Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self]`. Then use the resulting hypothesis. Rewrite `h` using `[mem_localization_standardLattice]`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨r, s, hs, hrs⟩` from `h i`.

Apply `mem_localization_of_smul_mem'₂ P N hs` to reduce the goal to its premises. Establish `e : s • (z i • β i) = r • β i`. Rewrite using `[← algebraMap_smul E s, ← algebraMap_smul E r, smul_smul, hrs]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ r (hβN i)`.
-/
theorem frame_exists (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) := by
  obtain ⟨β, hβN, hβI⟩ := exists_locBasis P hN
  refine ⟨β.equivFun.symm, fun z => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [mem_localization_standardLattice]
    intro i
    have := hβI _ h i
    rwa [Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self] at this
  · rw [mem_localization_standardLattice] at h
    rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, hrs⟩ := h i
    apply mem_localization_of_smul_mem'₂ P N hs
    have e : s • (z i • β i) = r • β i := by
      rw [← algebraMap_smul E s, ← algebraMap_smul E r, smul_smul, hrs]
    rw [e]
    exact Submodule.smul_mem _ r (hβN i)

end L3

section Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

def matA (f : Sp E n ≃ₗ[E] Sp E n) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
  (iA F E).mapMatrix (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n))

end Mat

section Unit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Unit

section Bwd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Bwd

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Cong

end DetChrL

end Formalism.L2.Col
