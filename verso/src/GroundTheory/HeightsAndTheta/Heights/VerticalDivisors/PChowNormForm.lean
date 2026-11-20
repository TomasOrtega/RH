import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Unfold `specRest`. Rewrite using `[eval₂_comp_left]`. Use `congr 1`. Conclude with `RingHom.ext fun a => by simp`. Use function extensionality and compare the values at `ij`.

Take `⟨i, j⟩` from `ij`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> simp`.
-/
theorem specRest_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {n e : ℕ}
    (φ : R →+* S) (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext ij
    obtain ⟨i, j⟩ := ij
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

/- English proof (translation)
Introduce `k E _ _ _ _ n e Q g y hy hQ hg`. Establish `hinj : Function.Injective ((MvPolynomial.aeval y : MvPolynomial (Par e n) k →ₐ[k] E) : MvPolynomial (Par e n) k →+* E)` using `hy`. Use `set φ : GenParField k e n →+* E := IsFractionRing.lift hinj with hφ`. Establish `hφC : φ.comp (algebraMap k (GenParField k e n)) = algebraMap k E`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k), hφ, IsFractionRing.lift_algebraMap]`. Simplify using the standard rewrite rules. Establish `hy' : y = φ ∘ genPar k e n`. Use function extensionality and compare the values at `p`. Simplify using `[hφ, genPar, IsFractionRing.lift_algebraMap]`.

Establish `hQ' : Q.map (MvPolynomial.map (algebraMap k E)) = (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))).map (MvPolynomial.map φ)`. Rewrite using `[Ideal.map_map]`. Use `congr 1`. Conclude with `RingHom.ext fun p => by rw [RingHom.comp_apply, map_map, hφC]`. Take `⟨hfin₀, c, hc, heq⟩` from `h₁ k n e Q g hQ hg`.

Take `⟨hfin, hnorm⟩` from `h₂ (GenParField k e n) E φ n e _ (genPar k e n) hfin₀`. Rewrite using `[hQ', hy']`. Use `⟨hfin, φ c, (map_ne_zero φ).mpr hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← hnorm, ← hφC, ← specRest_map, heq, _root_.map_mul, map_C]`.
-/
theorem ChowNormForm.proof (h₁ : ChowNormFormGeneric.Statement)
    (h₂ : SecAlgFieldChange.Statement) : ChowNormForm.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  have hinj : Function.Injective
      ((MvPolynomial.aeval y : MvPolynomial (Par e n) k →ₐ[k] E) : MvPolynomial (Par e n) k →+* E) :=
    hy
  set φ : GenParField k e n →+* E := IsFractionRing.lift hinj with hφ
  have hφC : φ.comp (algebraMap k (GenParField k e n)) = algebraMap k E := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k),
      hφ, IsFractionRing.lift_algebraMap]
    simp
  have hy' : y = φ ∘ genPar k e n := by
    funext p
    simp [hφ, genPar, IsFractionRing.lift_algebraMap]
  have hQ' : Q.map (MvPolynomial.map (algebraMap k E)) =
      (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))).map (MvPolynomial.map φ) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun p => by rw [RingHom.comp_apply, map_map, hφC]
  obtain ⟨hfin₀, c, hc, heq⟩ := h₁ k n e Q g hQ hg
  obtain ⟨hfin, hnorm⟩ := h₂ (GenParField k e n) E φ n e _ (genPar k e n) hfin₀
  rw [hQ', hy']
  refine ⟨hfin, φ c, (map_ne_zero φ).mpr hc, ?_⟩
  rw [← hnorm, ← hφC, ← specRest_map, heq, _root_.map_mul, map_C]

end

end GroundTheory.Heights₂.Heights.Vertical
