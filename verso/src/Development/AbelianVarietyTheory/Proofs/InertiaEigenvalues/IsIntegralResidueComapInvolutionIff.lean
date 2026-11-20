import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.SwapInt

/- English proof (translation)
Take `⟨p, hm, hp⟩` from `h`. Use `⟨p.map κ, hm.map κ, ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_map]`. Establish `e : (algebraMap O S').comp κ = ψ.comp (algebraMap O S)`. Use extensionality with `o`.

Simplify using `[hψ]`. Rewrite using `[e, ← hom_eval₂, hp, map_zero]`.
-/
theorem isIntegral_map_semilinear {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] [Algebra O S]
    [Algebra O S'] (κ : O →+* O) (ψ : S →+* S')
    (hψ : ∀ o, ψ (algebraMap O S o) = algebraMap O S' (κ o)) {y : S} (h : IsIntegral O y) :
    IsIntegral O (ψ y) := by
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map κ, hm.map κ, ?_⟩
  rw [eval₂_map]
  have e : (algebraMap O S').comp κ = ψ.comp (algebraMap O S) := by
    ext o; simp [hψ]
  rw [e, ← hom_eval₂, hp, map_zero]

noncomputable def conjO (K : UQ) : K.O →+* K.O where
  toFun o := Classical.choose (K.c_int o)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a * b)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a + b)), map_add, map_add, map_add,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]

/- English proof (translation)
The claim follows from `(Classical.choose_spec (K.c_int o)).symm`.
-/
theorem conjO_spec (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← conjO_spec, ← IsScalarTower.algebraMap_apply K.O K.E B.A]`.
-/
theorem sigma_algebraMap {K : UQ} (B : InvAlg K) (o : K.O) :
    B.σ (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← conjO_spec,
    ← IsScalarTower.algebraMap_apply K.O K.E B.A]

end GlobalTheory.UnitLemma.SwapInt

open GlobalTheory.UnitLemma.SwapInt in

/- English proof (translation)
Introduce `K B m x`. Set `σr : B.A →+* B.A` to `B.σ`. Set `ψ` to `Ideal.quotientMap m.asIdeal σr (le_refl (m.asIdeal.comap σr))`. Establish `hm : m.asIdeal ≤ (m.asIdeal.comap σr).comap σr`. Introduce `y hy`.

Simplify using `only [Ideal.mem_comap]`. Use `show B.σ (B.σ y) ∈ m.asIdeal`. Rewrite using `[B.σ_σ]`. Conclude with `hy`. Set `φ` to `Ideal.quotientMap (m.asIdeal.comap σr) σr hm`.

Establish `key : ∀ o : K.O, σr (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o)` using `sigma_algebraMap B`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap σr) x)` using `h`. Use `isIntegral_map_semilinear (conjO K) ψ (fun o => by` as an intermediate fact.

Rewrite using `[← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]`. Simplify using `only [ψ]`. Rewrite using `[Ideal.quotientMap_mk, key]) h'`. Establish `e2 : ψ (Ideal.Quotient.mk (m.asIdeal.comap σr) x) = Ideal.Quotient.mk m.asIdeal (σr x)` using `Ideal.quotientMap_mk`. Rewrite `this` using `[e2]`.

Conclude with `this`. Introduce `h`. Establish `h' : IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (σr x))` using `h`. Use `isIntegral_map_semilinear (conjO K) φ (fun o => by` as an intermediate fact. Rewrite using `[← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]`.

Simplify using `only [φ]`. Rewrite using `[Ideal.quotientMap_mk, key]) h'`. Establish `e2 : φ (Ideal.Quotient.mk m.asIdeal (σr x)) = Ideal.Quotient.mk (m.asIdeal.comap σr) (σr (σr x))` using `Ideal.quotientMap_mk`. Establish `e : σr (σr x) = x` using `B.σ_σ x`. Rewrite `this` using `[e2, e]`.

Conclude with `this`.
-/
theorem GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff :
    ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A),
      IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔
        IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  intro K B m x
  let σr : B.A →+* B.A := B.σ
  let ψ := Ideal.quotientMap m.asIdeal σr (le_refl (m.asIdeal.comap σr))
  have hm : m.asIdeal ≤ (m.asIdeal.comap σr).comap σr := by
    intro y hy
    simp only [Ideal.mem_comap]
    show B.σ (B.σ y) ∈ m.asIdeal
    rw [B.σ_σ]; exact hy
  let φ := Ideal.quotientMap (m.asIdeal.comap σr) σr hm
  have key : ∀ o : K.O, σr (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) :=
    sigma_algebraMap B
  constructor
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap σr) x) := h
    have := isIntegral_map_semilinear (conjO K) ψ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [ψ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : ψ (Ideal.Quotient.mk (m.asIdeal.comap σr) x) = Ideal.Quotient.mk m.asIdeal (σr x) :=
      Ideal.quotientMap_mk
    rw [e2] at this
    exact this
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (σr x)) := h
    have := isIntegral_map_semilinear (conjO K) φ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [φ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : φ (Ideal.Quotient.mk m.asIdeal (σr x)) = Ideal.Quotient.mk (m.asIdeal.comap σr) (σr (σr x)) :=
      Ideal.quotientMap_mk
    have e : σr (σr x) = x := B.σ_σ x
    rw [e2, e] at this
    exact this
