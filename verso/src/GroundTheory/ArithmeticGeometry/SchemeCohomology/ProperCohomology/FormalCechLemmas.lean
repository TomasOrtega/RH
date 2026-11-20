import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalDegreeCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)
  {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) (p : ℕ)

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Rewrite using `[← CechFamily.ofHom_cechH, ← CechFamily.comp_cechH]`. Use `CechFamily.cechH_congr (fun t y => ?_) p x` and prove the remaining obligations. Conclude with `(idealPowι_reesDeg I hF (isAffineOpen_inter 𝔘 hU t) n y).symm`.
-/
lemma reesCoefFam_cechH (n : ℕ) (x : cechH (reesPre I F) 𝔘 p) :
    (reesCoefFam I hF 𝔘 hU n).cechH p x =
      cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p ((reesDegFam I hF 𝔘 hU n).cechH p x) := by
  rw [← CechFamily.ofHom_cechH, ← CechFamily.comp_cechH]
  refine CechFamily.cechH_congr (fun t y => ?_) p x
  exact (idealPowι_reesDeg I hF (isAffineOpen_inter 𝔘 hU t) n y).symm

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Rewrite using `[← CechFamily.comp_cechH]`. Take `⟨σ, hσ, rfl⟩` from `exists_cls x`. Rewrite using `[CechFamily.cechH_cls]`. Conclude with `cls_congr 𝔘 (by funext t; exact reesDeg_reesInc I hF _ n (σ t)) _ _`.
-/
lemma reesDegFam_reesIncFam (n : ℕ) (x : cechH (modulesAb (idealPow I F n)).obj 𝔘 p) :
    (reesDegFam I hF 𝔘 hU n).cechH p ((reesIncFam I hF 𝔘 hU n).cechH p x) = x := by
  rw [← CechFamily.comp_cechH]
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [CechFamily.cechH_cls]
  exact cls_congr 𝔘 (by funext t; exact reesDeg_reesInc I hF _ n (σ t)) _ _

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Rewrite using `[← CechFamily.comp_cechH]`. Take `⟨σ, hσ, rfl⟩` from `exists_cls x`. Rewrite using `[CechFamily.cechH_cls]`. Use `(cls_congr 𝔘 (by funext t; exact reesDeg_reesInc_of_ne I hF _ h (σ t)) _ (map_zero _)).trans cls_zero` and prove the remaining obligations.
-/
lemma reesDegFam_reesIncFam_of_ne {n k : ℕ} (h : n ≠ k)
    (x : cechH (modulesAb (idealPow I F n)).obj 𝔘 p) :
    (reesDegFam I hF 𝔘 hU k).cechH p ((reesIncFam I hF 𝔘 hU n).cechH p x) = 0 := by
  rw [← CechFamily.comp_cechH]
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [CechFamily.cechH_cls]
  refine (cls_congr 𝔘 (by funext t; exact reesDeg_reesInc_of_ne I hF _ h (σ t)) _
    (map_zero _)).trans cls_zero

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Rewrite using `[reesCoefFam_cechH]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[reesDegFam_reesIncFam]`. Rewrite using `[reesDegFam_reesIncFam_of_ne I hF 𝔘 hU p h, map_zero]`.
-/
lemma reesCoefFam_reesIncFam (n k : ℕ) (x : cechH (modulesAb (idealPow I F n)).obj 𝔘 p) :
    (reesCoefFam I hF 𝔘 hU k).cechH p ((reesIncFam I hF 𝔘 hU n).cechH p x) =
      if n = k then cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p x else 0 := by
  rw [reesCoefFam_cechH]
  split_ifs with h
  · subst h
    rw [reesDegFam_reesIncFam]
  · rw [reesDegFam_reesIncFam_of_ne I hF 𝔘 hU p h, map_zero]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Take `⟨σ, hσ, rfl⟩` from `exists_cls x`. Use `⟨σ, hσ, Finset.univ.sup fun t : Fin (p + 1) → ι => (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id, rfl, ?_⟩` and prove the remaining obligations. Introduce `n hn t`. Express the relevant statement in the definitionally equal form `(reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff n = 0`.

Assume the negation of the conclusion as `h`. Establish `h1 : n ≤ (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id` using `Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)`. Establish `h2` using `Finset.le_sup (f := fun t : Fin (p + 1) → ι => (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id) (Finset.mem_univ t)`. Use linear arithmetic over natural numbers and integers.
-/
lemma exists_cls_coef_eq_zero [Finite ι] (x : cechH (reesPre I F) 𝔘 p) :
    ∃ (σ : Cochain (reesPre I F) 𝔘 p) (hσ : d (reesPre I F) 𝔘 p σ = 0) (N : ℕ),
      cls σ hσ = x ∧ ∀ n, N < n → ∀ t, reesCoef I hF (isAffineOpen_inter 𝔘 hU t) n (σ t) = 0 := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  refine ⟨σ, hσ, Finset.univ.sup fun t : Fin (p + 1) → ι =>
    (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id, rfl, ?_⟩
  intro n hn t
  change (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff n = 0
  by_contra h
  have h1 : n ≤ (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id :=
    Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)
  have h2 := Finset.le_sup (f := fun t : Fin (p + 1) → ι =>
    (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id)
    (Finset.mem_univ t)
  omega

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Take `⟨σ, hσ, N, rfl, hN⟩` from `exists_cls_coef_eq_zero I hF 𝔘 hU p x`. Use `⟨N, fun n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[CechFamily.cechH_cls]`. Conclude with `(cls_congr 𝔘 (by funext t; exact hN n hn t) _ (map_zero _)).trans cls_zero`.
-/
lemma reesCoefFam_eq_zero_of_lt [Finite ι] (x : cechH (reesPre I F) 𝔘 p) :
    ∃ N : ℕ, ∀ n, N < n → (reesCoefFam I hF 𝔘 hU n).cechH p x = 0 := by
  obtain ⟨σ, hσ, N, rfl, hN⟩ := exists_cls_coef_eq_zero I hF 𝔘 hU p x
  refine ⟨N, fun n hn => ?_⟩
  rw [CechFamily.cechH_cls]
  exact (cls_congr 𝔘 (by funext t; exact hN n hn t) _ (map_zero _)).trans cls_zero

end

end GroundTheory.Arith.SchemeCoh
