import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
open GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Introduce `T _ _ _ hA O _ _ _ _ _ _ hind P hP hne`. Use `haveI : IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := (locIndEtale_isDomain_isIntegrallyClosed T O 1 ⟨inferInstance, hA⟩ (by simp) one_pos hind).1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨y, hyP, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`.

Take `⟨⟨o, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) y`. Establish `ho : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o = IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s` using `(IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s).symm`. Establish `hoP : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ∈ P` using `ho ▸ P.mul_mem_right _ hyP`. Establish `ho0 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ≠ 0`. Rewrite using `[ho]`.

Conclude with `mul_ne_zero hy0 (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s).ne_zero`. Take `⟨ι, _, _, _, Si, -, hcov, hloc⟩` from `hind`. Take `⟨i, hoi⟩` from `hcov o`. Take `⟨E, _, _, _, p, _, ⟨e⟩⟩` from `hloc i`. Use `haveI : Algebra.QuasiFinite (Polynomial T) (Localization.AtPrime p) := inferInstance`.

Use `haveI : Algebra.QuasiFinite (Polynomial T) (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).1 this`. Set `φ : Si i →+* (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))` to `(algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comp (Si i).val.toRingHom`. Establish `hφ : ∀ g : Polynomial T, φ (algebraMap (Polynomial T) (Si i) g) = algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g` using `fun g => by`. Simplify using `[φ, IsScalarTower.algebraMap_apply (Polynomial T) O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))]`. Use `haveI h1 : (P.comap φ).IsPrime := Ideal.comap_isPrime φ P`.

Use `haveI h0 : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).IsPrime := Ideal.comap_isPrime φ ⊥`. Establish `hunder : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).under (Polynomial T) = (P.comap φ).under (Polynomial T)`. Use extensionality with `g`. Simplify using `only [Ideal.under, Ideal.mem_comap, hφ, Ideal.mem_bot]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[h]`. Conclude with `P.zero_mem`. Introduce `h`. Distinguish the cases in `hg : g = 0`.

Rewrite using `[hg, map_zero]`. Conclude with `absurd h (hcon g hg)`. Establish `heq` using `Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Polynomial T) _ _ (Ideal.comap_mono bot_le) hunder`. Establish `hmem : (⟨o, hoi⟩ : Si i) ∈ P.comap φ` using `hoP`. Rewrite `hmem` using `[← heq, Ideal.mem_comap, Ideal.mem_bot]`.

Conclude with `ho0 hmem`.
-/
theorem genFibre_prime_meets_polynomial :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → P ≠ ⊥ → ∃ g : Polynomial T, g ≠ 0 ∧ algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P := by
  intro T _ _ _ hA O _ _ _ _ _ _ hind P hP hne
  haveI : IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) :=
    (locIndEtale_isDomain_isIntegrallyClosed T O 1 ⟨inferInstance, hA⟩ (by simp) one_pos hind).1
  by_contra hcon
  push_neg at hcon

  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨⟨o, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) y
  have ho : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o = IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s :=
    (IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o s).symm
  have hoP : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ∈ P := ho ▸ P.mul_mem_right _ hyP
  have ho0 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) o ≠ 0 := by
    rw [ho]
    exact mul_ne_zero hy0 (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s).ne_zero
  obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := hind
  obtain ⟨i, hoi⟩ := hcov o
  obtain ⟨E, _, _, _, p, _, ⟨e⟩⟩ := hloc i
  haveI : Algebra.QuasiFinite (Polynomial T) (Localization.AtPrime p) := inferInstance
  haveI : Algebra.QuasiFinite (Polynomial T) (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).1 this
  let φ : Si i →+* (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := (algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comp (Si i).val.toRingHom
  have hφ : ∀ g : Polynomial T, φ (algebraMap (Polynomial T) (Si i) g) =
      algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g := fun g => by
    simp [φ, IsScalarTower.algebraMap_apply (Polynomial T) O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))]
  haveI h1 : (P.comap φ).IsPrime := Ideal.comap_isPrime φ P
  haveI h0 : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).IsPrime := Ideal.comap_isPrime φ ⊥
  have hunder : ((⊥ : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).comap φ).under (Polynomial T) = (P.comap φ).under (Polynomial T) := by
    ext g
    simp only [Ideal.under, Ideal.mem_comap, hφ, Ideal.mem_bot]
    constructor
    · intro h; rw [h]; exact P.zero_mem
    · intro h
      by_cases hg : g = 0
      · rw [hg, map_zero]
      · exact absurd h (hcon g hg)
  have heq := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Polynomial T) _ _
    (Ideal.comap_mono bot_le) hunder
  have hmem : (⟨o, hoi⟩ : Si i) ∈ P.comap φ := hoP
  rw [← heq, Ideal.mem_comap, Ideal.mem_bot] at hmem
  exact ho0 hmem

end GlobalTheory
