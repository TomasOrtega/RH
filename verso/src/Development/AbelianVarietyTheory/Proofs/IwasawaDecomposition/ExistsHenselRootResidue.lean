import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[eval_map, eval_map, hom_eval₂]`.
-/
theorem residue_eval_map_comm {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (q : A[X]) (f : A →+* B) (h : B →+* C) (x : B) :
    h ((q.map f).eval x) = (q.map (h.comp f)).eval (h x) := by
  rw [eval_map, eval_map, hom_eval₂]

/- English proof (translation)
Introduce `A R V _ _ _ _ _ _ _ φ α σ hσ θ q hq h0 hu`. Take `⟨η₀, hη₀⟩` from `residue_surjective (σ (residue R θ))`. Establish `hcomp : (residue V).comp α = σ.comp ((residue R).comp φ)`. Use extensionality with `a`. Simplify using `[hσ]`.

Establish `key : ∀ p : A[X], residue V ((p.map α).eval η₀) = σ (residue R ((p.map φ).eval θ))`. Introduce `p`. Rewrite using `[residue_eval_map_comm, hcomp, hη₀, residue_eval_map_comm p φ (residue R), residue_eval_map_comm _ _ σ]`. Establish `hm : (q.map α).Monic` using `hq.map α`. Establish `h1 : (q.map α).eval η₀ ∈ maximalIdeal V`.

Rewrite using `[← residue_eq_zero_iff, key, h0, map_zero, map_zero]`. Establish `h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal V) ((q.map α).derivative.eval η₀))`. Establish `: (Ideal.Quotient.mk (maximalIdeal V) ((q.map α).derivative.eval η₀)) = σ (residue R ((q.derivative.map φ).eval θ))`. Rewrite using `[derivative_map]`. Conclude with `key _`.

Rewrite using `[this]`. Conclude with `(hu.map (residue R)).map σ`. Take `⟨η, hη, hηm⟩` from `HenselianRing.is_henselian (I := maximalIdeal V) _ hm η₀ h1 h2`. Use `⟨η, hη, ?_⟩` and prove the remaining obligations. Rewrite using `[← hη₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`.

Conclude with `hηm`.
-/
theorem exists_root_lift_of_residue_map :
    ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V]
      [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V)
      (σ : ResidueField R →+* ResidueField V),
      (∀ a, σ (residue R (φ a)) = residue V (α a)) → ∀ (θ : R) (q : Polynomial A), q.Monic →
      (q.map φ).eval θ = 0 → IsUnit ((q.derivative.map φ).eval θ) →
      ∃ η : V, (q.map α).eval η = 0 ∧ residue V η = σ (residue R θ) := by
  intro A R V _ _ _ _ _ _ _ φ α σ hσ θ q hq h0 hu
  obtain ⟨η₀, hη₀⟩ := residue_surjective (σ (residue R θ))
  have hcomp : (residue V).comp α = σ.comp ((residue R).comp φ) := by
    ext a; simp [hσ]
  have key : ∀ p : A[X], residue V ((p.map α).eval η₀) = σ (residue R ((p.map φ).eval θ)) := by
    intro p
    rw [residue_eval_map_comm, hcomp, hη₀, residue_eval_map_comm p φ (residue R),
      residue_eval_map_comm _ _ σ]
  have hm : (q.map α).Monic := hq.map α
  have h1 : (q.map α).eval η₀ ∈ maximalIdeal V := by
    rw [← residue_eq_zero_iff, key, h0, map_zero, map_zero]
  have h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal V) ((q.map α).derivative.eval η₀)) := by
    have : (Ideal.Quotient.mk (maximalIdeal V) ((q.map α).derivative.eval η₀)) =
        σ (residue R ((q.derivative.map φ).eval θ)) := by
      rw [derivative_map]; exact key _
    rw [this]
    exact (hu.map (residue R)).map σ
  obtain ⟨η, hη, hηm⟩ := HenselianRing.is_henselian (I := maximalIdeal V) _ hm η₀ h1 h2
  refine ⟨η, hη, ?_⟩
  rw [← hη₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hηm

end GlobalTheory
