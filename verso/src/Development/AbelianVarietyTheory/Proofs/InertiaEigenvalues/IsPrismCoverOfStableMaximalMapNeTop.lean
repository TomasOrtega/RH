import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `htop`. Take `⟨x, hx, hx1⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ((Ideal.eq_top_iff_one _).1 htop)`. Establish `h1 : 1 - x ∈ 𝔟`. Rewrite using `[← Ideal.Quotient.eq, map_one, hx1]`. Establish `hu` using `Ideal.mem_jacobson_bot.1 (hJ h1) (-1)`.

Establish `hx' : (1 - x) * -1 + 1 = x` using `by ring`. Rewrite `hu` using `[hx']`. Conclude with `h (Ideal.eq_top_of_isUnit_mem _ hx hu)`.
-/
private lemma map_quotient_mk_proper_of_le_jacobson {B : Type} [CommRing B] (J 𝔟 : Ideal B) (hJ : 𝔟 ≤ Ideal.jacobson ⊥)
    (h : J ≠ ⊤) : J.map (Ideal.Quotient.mk 𝔟) ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    ((Ideal.eq_top_iff_one _).1 htop)
  have h1 : 1 - x ∈ 𝔟 := by
    rw [← Ideal.Quotient.eq, map_one, hx1]
  have hu := Ideal.mem_jacobson_bot.1 (hJ h1) (-1)
  have hx' : (1 - x) * -1 + 1 = x := by ring
  rw [hx'] at hu
  exact h (Ideal.eq_top_of_isUnit_mem _ hx hu)

/- English proof (translation)
Use `letI : Algebra (A ⧸ 𝔞) (B ⧸ 𝔟) := (Ideal.quotientMap 𝔟 f hle).toAlgebra`. Establish `hfl' : Module.Flat (A ⧸ 𝔞) (B ⧸ 𝔟)` using `hfl`. Use `show Module.FaithfullyFlat (A ⧸ 𝔞) (B ⧸ 𝔟)`. Use `{ toFlat := hfl', submodule_ne_top := fun 𝔫 h𝔫 htop => ?_ }` and prove the remaining obligations. Rewrite `htop` using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff]`.

Use `set 𝔪 := 𝔫.comap (Ideal.Quotient.mk 𝔞)`. Establish `hmax : 𝔪.IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `key : (𝔪.map f).map (Ideal.Quotient.mk 𝔟) = ⊤`. Rewrite using `[Ideal.map_map, ← Ideal.quotientMap_comp_mk hle, ← Ideal.map_map, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Conclude with `htop`.

Conclude with `map_quotient_mk_proper_of_le_jacobson _ _ hJ (hm 𝔪 hmax) key`.
-/
theorem faithfullyFlat_quotientMap_of_map_ne_top {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (𝔞 : Ideal A) (𝔟 : Ideal B) (hle : 𝔞 ≤ 𝔟.comap f) (hJ : 𝔟 ≤ Ideal.jacobson ⊥)
    (hfl : (Ideal.quotientMap 𝔟 f hle).Flat) (hm : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪.map f ≠ ⊤) :
    (Ideal.quotientMap 𝔟 f hle).FaithfullyFlat := by
  letI : Algebra (A ⧸ 𝔞) (B ⧸ 𝔟) := (Ideal.quotientMap 𝔟 f hle).toAlgebra
  have hfl' : Module.Flat (A ⧸ 𝔞) (B ⧸ 𝔟) := hfl
  show Module.FaithfullyFlat (A ⧸ 𝔞) (B ⧸ 𝔟)
  refine { toFlat := hfl', submodule_ne_top := fun 𝔫 h𝔫 htop => ?_ }
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop

  set 𝔪 := 𝔫.comap (Ideal.Quotient.mk 𝔞)
  have hmax : 𝔪.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have key : (𝔪.map f).map (Ideal.Quotient.mk 𝔟) = ⊤ := by
    rw [Ideal.map_map, ← Ideal.quotientMap_comp_mk hle, ← Ideal.map_map,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact htop
  exact map_quotient_mk_proper_of_le_jacobson _ _ hJ (hm 𝔪 hmax) key

/- English proof (translation)
Introduce `l _ R _ B C h hs hm`. Use `⟨hs, fun m => ?_⟩` and prove the remaining obligations. Break down `m with _ | m` into its components or cases. Use `haveI : Subsingleton (B.A ⧸ adI B ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)`. Rewrite using `[RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]`.

Conclude with `⟨hs.flat 0, fun p => isEmptyElim p⟩`. Use `haveI := C.complete`. Establish `hJ : adI C ^ (m + 1) ≤ Ideal.jacobson ⊥` using `(Ideal.pow_le_self (Nat.succ_ne_zero m)).trans (IsAdicComplete.le_jacobson_bot (adI C))`. Conclude with `faithfullyFlat_quotientMap_of_map_ne_top h.f _ _ (adI_pow_le h (m + 1)) hJ (hs.flat (m + 1)) hm`.
-/
theorem cover_of_stable_of_map_ne_top : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R)
    (h : Hom B C), Stable h → (∀ 𝔪 : Ideal B.A, 𝔪.IsMaximal → 𝔪.map h.f ≠ ⊤) → Cover h := by
  intro l _ R _ B C h hs hm
  refine ⟨hs, fun m => ?_⟩
  rcases m with _ | m
  ·
    haveI : Subsingleton (B.A ⧸ adI B ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨hs.flat 0, fun p => isEmptyElim p⟩
  · haveI := C.complete
    have hJ : adI C ^ (m + 1) ≤ Ideal.jacobson ⊥ :=
      (Ideal.pow_le_self (Nat.succ_ne_zero m)).trans (IsAdicComplete.le_jacobson_bot (adI C))
    exact faithfullyFlat_quotientMap_of_map_ne_top h.f _ _ (adI_pow_le h (m + 1)) hJ (hs.flat (m + 1)) hm

end GlobalTheory.BSP
