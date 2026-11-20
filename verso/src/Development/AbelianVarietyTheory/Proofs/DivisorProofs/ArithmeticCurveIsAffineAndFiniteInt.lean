import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.ArithCurve

/- English proof (translation)
Take `⟨m, i, hi, rfl⟩` from `h`. Use `isProper_str R m` as an intermediate fact. Use `infer_instance`.
-/
theorem isProper_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

/- English proof (translation)
Introduce `hc`. Establish `hu : ∀ x : Sp ℤ, x = genericPoint (Sp ℤ)` using `fun x => by`. Establish `hx : x ∈ closure ({genericPoint (Sp ℤ)} : Set (Sp ℤ))` using `(genericPoint_spec (Sp ℤ)).def ▸ Set.mem_univ x`. Rewrite `hx` using `[hc.closure_eq]`. Then use the resulting hypothesis. Set `a : PrimeSpectrum ℤ` to `⟨⊥, Ideal.bot_prime⟩`.

Set `b : PrimeSpectrum ℤ` to `⟨Ideal.span {(2 : ℤ)}, (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two⟩`. Establish `hab : a = b` using `(hu (show Sp ℤ from a)).trans (hu (show Sp ℤ from b)).symm`. Establish `h2 : (2 : ℤ) ∈ b.asIdeal` using `Ideal.subset_span rfl`. Rewrite `h2` using `[← hab]`. Conclude with `absurd ((Submodule.mem_bot ℤ).1 h2) (by norm_num)`.
-/
theorem not_isClosed_genericPoint_int : ¬ IsClosed ({genericPoint (Sp ℤ)} : Set (Sp ℤ)) := by
  intro hc
  have hu : ∀ x : Sp ℤ, x = genericPoint (Sp ℤ) := fun x => by
    have hx : x ∈ closure ({genericPoint (Sp ℤ)} : Set (Sp ℤ)) :=
      (genericPoint_spec (Sp ℤ)).def ▸ Set.mem_univ x
    rwa [hc.closure_eq] at hx
  let a : PrimeSpectrum ℤ := ⟨⊥, Ideal.bot_prime⟩
  let b : PrimeSpectrum ℤ := ⟨Ideal.span {(2 : ℤ)},
    (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two⟩
  have hab : a = b := (hu (show Sp ℤ from a)).trans (hu (show Sp ℤ from b)).symm
  have h2 : (2 : ℤ) ∈ b.asIdeal := Ideal.subset_span rfl
  rw [← hab] at h2
  exact absurd ((Submodule.mem_bot ℤ).1 h2) (by norm_num)

/- English proof (translation)
Introduce `k _ Y q h`. Use `h.isIntegral` as an intermediate fact. Use `h.isNoetherian` as an intermediate fact. Establish `hd : topologicalKrullDim Y = 1` using `by simpa using h.dim_eq`. Establish `: IsProper q` using `isProper_of_projOver h.isProjOver`.

Establish `: IsFinite (spMap (Int.castRingHom k))`. Use `h.finite` as an intermediate fact. Rewrite using `[IsFinite.SpecMap_iff]`. Express the relevant statement in the definitionally equal form `(Int.castRingHom k).Finite`. Rewrite using `[← algebraMap_int_eq]`.

Conclude with `RingHom.finite_algebraMap.2 ‹_›`. Use `set f : Y ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom k) with hf`. Establish `: Flat f` using `h.flat`. Establish `: IsProper f` using `inferInstance`. Establish `hη : f (genericPoint Y) = genericPoint (Sp ℤ)`.

Take `⟨y, hy, e⟩` from `Flat.generalizingMap f (genericPoint_specializes (f (genericPoint Y)))`. Rewrite `e` using `[(hy.antisymm (genericPoint_specializes y)).eq]`. Then use the resulting hypothesis. Establish `hfib : ∀ z, (f ⁻¹' {z}).Finite`. Introduce `z`. Distinguish the cases in `hz : z = genericPoint (Sp ℤ)`.

Use `(Set.finite_singleton (genericPoint Y)).subset fun y hy => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hc` using `f.isClosedMap _ (ProperCurve.isClosed_singleton hd hne)`. Rewrite `hc` using `[Set.image_singleton, show f y = z from hy, hz]`. Conclude with `not_isClosed_genericPoint_int hc`.

Use `(ProperCurve.finite_of_isClosed hd (isClosed_closure.preimage f.continuous) ?_).subset (Set.preimage_mono subset_closure)` and prove the remaining obligations. Introduce `hmem`. Rewrite `hmem` using `[Set.mem_preimage, hη, ← specializes_iff_mem_closure]`. Conclude with `hz (hmem.antisymm (genericPoint_specializes z)).eq`. Establish `: LocallyQuasiFinite f` using `.of_finite_preimage_singleton f hfib`.

Establish `: IsFinite f` using `.of_isProper_of_locallyQuasiFinite f`. Establish `: IsAffine Y` using `isAffine_of_isAffineHom f`. Use `⟨this, ?_⟩` and prove the remaining obligations. Establish `h1` using `IsFinite.finite_app f ⊤ (isAffineOpen_top _)`. Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.Finite` using `RingHom.Finite.of_surjective _ fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom x, by simp⟩`.

Establish `e : (f.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom = algebraMap ℤ Γ(Y, ⊤)` using `RingHom.ext_int _ _`. Conclude with `RingHom.finite_algebraMap.1 (e ▸ h1.comp h2)`.
-/
theorem isAffine_and_finite : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsArithVar q 0 → IsAffine Y ∧ Module.Finite ℤ Γ(Y, ⊤) := by
  intro k _ Y q h
  have := h.isIntegral
  have := h.isNoetherian
  have hd : topologicalKrullDim Y = 1 := by simpa using h.dim_eq
  have : IsProper q := isProper_of_projOver h.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    have := h.finite
    rw [IsFinite.SpecMap_iff]
    change (Int.castRingHom k).Finite
    rw [← algebraMap_int_eq]
    exact RingHom.finite_algebraMap.2 ‹_›
  set f : Y ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom k) with hf
  have : Flat f := h.flat
  have : IsProper f := inferInstance
  have hη : f (genericPoint Y) = genericPoint (Sp ℤ) := by
    obtain ⟨y, hy, e⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint Y)))
    rwa [(hy.antisymm (genericPoint_specializes y)).eq] at e
  have hfib : ∀ z, (f ⁻¹' {z}).Finite := by
    intro z
    by_cases hz : z = genericPoint (Sp ℤ)
    · refine (Set.finite_singleton (genericPoint Y)).subset fun y hy => ?_
      by_contra hne
      have hc := f.isClosedMap _ (ProperCurve.isClosed_singleton hd hne)
      rw [Set.image_singleton, show f y = z from hy, hz] at hc
      exact not_isClosed_genericPoint_int hc
    · refine (ProperCurve.finite_of_isClosed hd (isClosed_closure.preimage f.continuous) ?_).subset
        (Set.preimage_mono subset_closure)
      intro hmem
      rw [Set.mem_preimage, hη, ← specializes_iff_mem_closure] at hmem
      exact hz (hmem.antisymm (genericPoint_specializes z)).eq
  have : LocallyQuasiFinite f := .of_finite_preimage_singleton f hfib
  have : IsFinite f := .of_isProper_of_locallyQuasiFinite f
  have : IsAffine Y := isAffine_of_isAffineHom f
  refine ⟨this, ?_⟩
  have h1 := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom x, by simp⟩
  have e : (f.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom =
      algebraMap ℤ Γ(Y, ⊤) := RingHom.ext_int _ _
  exact RingHom.finite_algebraMap.1 (e ▸ h1.comp h2)

end GlobalTheory.ArithCurve
