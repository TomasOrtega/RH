import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOrderLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Rewrite using `[Module.length_eq_coheight, Module.length_eq_coheight]`. Use `Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥` as an intermediate fact. Establish `hb : Ideal.comap (e : S →+* T) ⊥ = ⊥` using `Ideal.comap_bot_of_injective _ e.injective`. Rewrite `this` using `[hb]`. Conclude with `this`.
-/
private theorem length_self_eq_of_ringEquiv' {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

/- English proof (translation)
Set `S` to `Localization.AtPrime W`. Establish `hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) = J.map (algebraMap R S)`. Rewrite using `[Submodule.localized'_eq_span, Ideal.map]`. Both sides reduce to the same expression. Set `e` to `(IsLocalizedModule.linearEquiv W.primeCompl ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S)) (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S`.

Rewrite using `[← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]`. Conclude with `Module.length_eq_of_surjective Ideal.Quotient.mk_surjective`.
-/
private theorem length_localizedModule_quot' {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

/- English proof (translation)
Introduce `S _ P W₀ _ z`. Use `set W := W₀.comap (Ideal.Quotient.mk P) with hWdef`. Use `set A := Localization.AtPrime W₀`. Use `set J := P ⊔ Ideal.span {z} with hJdef`. Set `ψ : Localization.AtPrime W →+* A` to `Localization.localRingHom W W₀ (Ideal.Quotient.mk P) rfl`.

Establish `hψ : Function.Surjective ψ`. Introduce `x`. Take `⟨⟨a, t⟩, rfl⟩` from `IsLocalization.mk'_surjective W₀.primeCompl x`. Take `⟨a', rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨t', ht'⟩` from `Ideal.Quotient.mk_surjective (t : S ⧸ P)`.

Establish `hs : t' ∈ W.primeCompl`. Introduce `h`. Apply `t.2` to reduce the goal to its premises. Rewrite using `[← ht']`. Conclude with `h`.

Use `⟨IsLocalization.mk' _ a' ⟨t', hs⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Localization.localRingHom_mk']`. Use `congr 1`. Conclude with `Subtype.ext ht'`. Establish `hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap S (Localization.AtPrime W))`.

Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot]`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective W.primeCompl x`. Rewrite `hx` using `[Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff]`. Take `⟨⟨t, ht⟩, htr⟩` from `hx`.

Take `⟨t', rfl⟩` from `Ideal.Quotient.mk_surjective t`. Establish `ht'W : t' ∈ W.primeCompl` using `ht`. Establish `hmemP : t' * r ∈ P`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_mul]`. Conclude with `htr`.

Establish `hrJ : algebraMap S (Localization.AtPrime W) r ∈ J.map (algebraMap S (Localization.AtPrime W))`. Rewrite using `[← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, ht'W⟩), ← map_mul]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hmemP)`. Use `show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one]`.

Conclude with `Ideal.mul_mem_right _ _ hrJ`. Establish `hcomp : ψ.comp (algebraMap S (Localization.AtPrime W)) = (algebraMap (S ⧸ P) A).comp (Ideal.Quotient.mk P)` using `RingHom.ext fun x => Localization.localRingHom_to_map W W₀ (Ideal.Quotient.mk P) rfl x`. Establish `hJmk : J.map (Ideal.Quotient.mk P) = Ideal.span {Ideal.Quotient.mk P z}`. Rewrite using `[hJdef, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]`. Establish `hI : (J.map (algebraMap S (Localization.AtPrime W))).map ψ = Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)}`.

Rewrite using `[Ideal.map_map, hcomp, ← Ideal.map_map, hJmk, Ideal.map_span, Set.image_singleton]`. Set `: CommRing A` to `inferInstance`. Set `g` to `(Ideal.Quotient.mk (Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)})).comp ψ`. Establish `hg : Function.Surjective g` using `Ideal.Quotient.mk_surjective.comp hψ`. Establish `hgk : J.map (algebraMap S (Localization.AtPrime W)) = RingHom.ker g`.

Rewrite using `[← RingHom.comap_ker, Ideal.mk_ker, ← hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]`. Establish `key` using `length_self_eq_of_ringEquiv' ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))`. Rewrite using `[length_localizedModule_quot', key]`. Conclude with `(Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm`.
-/
theorem LocalizedQuotLength.proof : LocalizedQuotLength.Statement.{u} := by
  intro S _ P W₀ _ z
  set W := W₀.comap (Ideal.Quotient.mk P) with hWdef
  set A := Localization.AtPrime W₀
  set J := P ⊔ Ideal.span {z} with hJdef
  let ψ : Localization.AtPrime W →+* A := Localization.localRingHom W W₀ (Ideal.Quotient.mk P) rfl

  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective W₀.primeCompl x
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t', ht'⟩ := Ideal.Quotient.mk_surjective (t : S ⧸ P)
    have hs : t' ∈ W.primeCompl := by
      intro h
      apply t.2
      rw [← ht']
      exact h
    refine ⟨IsLocalization.mk' _ a' ⟨t', hs⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap S (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    have ht'W : t' ∈ W.primeCompl := ht
    have hmemP : t' * r ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact htr
    have hrJ : algebraMap S (Localization.AtPrime W) r ∈ J.map (algebraMap S (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, ht'W⟩),
        ← map_mul]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  have hcomp : ψ.comp (algebraMap S (Localization.AtPrime W)) =
      (algebraMap (S ⧸ P) A).comp (Ideal.Quotient.mk P) :=
    RingHom.ext fun x => Localization.localRingHom_to_map W W₀ (Ideal.Quotient.mk P) rfl x
  have hJmk : J.map (Ideal.Quotient.mk P) = Ideal.span {Ideal.Quotient.mk P z} := by
    rw [hJdef, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have hI : (J.map (algebraMap S (Localization.AtPrime W))).map ψ =
      Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)} := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hJmk, Ideal.map_span, Set.image_singleton]
  let : CommRing A := inferInstance
  let g := (Ideal.Quotient.mk (Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)})).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap S (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv'
    ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [length_localizedModule_quot', key]
  exact (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
