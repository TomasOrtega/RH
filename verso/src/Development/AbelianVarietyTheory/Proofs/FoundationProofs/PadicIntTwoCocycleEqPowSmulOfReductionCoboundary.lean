import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ Γ _ _ _ ρ hρ r ρr hc z hz hB`. Take `⟨c, hcc, hcd⟩` from `(separated_dvr_second_cohomology_mem _ _).1 hB`. Establish `hsurj : Function.Surjective (PadicInt.toZModPow (p` using `l) r) := ZMod.ringHom_surjective _`. Use `choose s hs using hsurj`. Establish `hsc : Continuous s` using `continuous_of_discreteTopology`.

Establish `hb : d1 ρ (s ∘ c) ∈ B2 ρ` using `(separated_dvr_second_cohomology_mem _ _).2 ⟨s ∘ c, hsc.comp hcc, rfl⟩`. Establish `hy : z - d1 ρ (s ∘ c) ∈ Z2 ρ` using `(Z2 ρ).sub_mem hz (coboundaries2_le_cocycles2 ρ hρ hb)`. Establish `hdiv : ∀ p, ∃ a : ℤ_[l], (l : ℤ_[l]) ^ r * a = (z - d1 ρ (s ∘ c)) p`. Introduce and unpack `⟨g, h⟩`. Establish `h1 : (z - d1 ρ (s ∘ c)) (g, h) ∈ RingHom.ker (PadicInt.toZModPow (p` using `l) r) := by`.

Establish `h2` using `congrFun hcd (g, h)`. Rewrite `h2` using `[d1_apply]`. Rewrite using `[RingHom.mem_ker, Pi.sub_apply, d1_apply, map_sub, map_add, map_sub, hc]`. Simplify using `only [Function.comp_apply, hs]`. Rewrite using `[h2, sub_self]`.

Rewrite `h1` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`. Take `⟨a, ha⟩` from `h1`. Conclude with `⟨a, ha.symm⟩`. Use `choose w hw using hdiv`. Establish `hne : (l : ℤ_[l]) ^ r ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`.

Establish `hemb : Topology.IsClosedEmbedding (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x)` using `Continuous.isClosedEmbedding (continuous_const.mul continuous_id) (mul_right_injective₀ hne)`. Establish `hw' : (l : ℤ_[l]) ^ r • w = z - d1 ρ (s ∘ c)` using `funext hw`. Use `⟨w, (mem_cocycles2 _ _).2 ⟨?_, fun g h k => ?_⟩, ?_⟩` and prove the remaining obligations. Use `hemb.isInducing.continuous_iff.2 ?_` and prove the remaining obligations. Establish `: (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) ∘ w = z - d1 ρ (s ∘ c)` using `funext hw`.

Rewrite using `[this]`. Conclude with `hy.1`. Establish `e` using `((mem_cocycles2 _ _).1 hy).2 g h k`. Rewrite `e` using `[← hw']`. Simplify using `only [Pi.smul_apply, map_smul] at e`.

Rewrite `e` using `[← smul_sub, ← smul_add, ← smul_sub, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 e).resolve_left hne`. Rewrite using `[hw', sub_sub_cancel]`. Conclude with `hb`.
-/
theorem padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ z ∈ Z2 ρ, (fun p => PadicInt.toZModPow r (z p)) ∈ B2 ρr → ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ := by
  intro l _ Γ _ _ _ ρ hρ r ρr hc z hz hB
  obtain ⟨c, hcc, hcd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hB
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) r) := ZMod.ringHom_surjective _
  choose s hs using hsurj
  have hsc : Continuous s := continuous_of_discreteTopology
  have hb : d1 ρ (s ∘ c) ∈ B2 ρ := (separated_dvr_second_cohomology_mem _ _).2 ⟨s ∘ c, hsc.comp hcc, rfl⟩
  have hy : z - d1 ρ (s ∘ c) ∈ Z2 ρ := (Z2 ρ).sub_mem hz (coboundaries2_le_cocycles2 ρ hρ hb)
  have hdiv : ∀ p, ∃ a : ℤ_[l], (l : ℤ_[l]) ^ r * a = (z - d1 ρ (s ∘ c)) p := by
    rintro ⟨g, h⟩
    have h1 : (z - d1 ρ (s ∘ c)) (g, h) ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      have h2 := congrFun hcd (g, h)
      rw [d1_apply] at h2
      rw [RingHom.mem_ker, Pi.sub_apply, d1_apply, map_sub, map_add, map_sub, hc]
      simp only [Function.comp_apply, hs]
      rw [h2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha.symm⟩
  choose w hw using hdiv
  have hne : (l : ℤ_[l]) ^ r ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hemb : Topology.IsClosedEmbedding (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) :=
    Continuous.isClosedEmbedding (continuous_const.mul continuous_id)
      (mul_right_injective₀ hne)
  have hw' : (l : ℤ_[l]) ^ r • w = z - d1 ρ (s ∘ c) := funext hw
  refine ⟨w, (mem_cocycles2 _ _).2 ⟨?_, fun g h k => ?_⟩, ?_⟩
  · refine hemb.isInducing.continuous_iff.2 ?_
    have : (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) ∘ w = z - d1 ρ (s ∘ c) := funext hw
    rw [this]
    exact hy.1
  · have e := ((mem_cocycles2 _ _).1 hy).2 g h k
    rw [← hw'] at e
    simp only [Pi.smul_apply, map_smul] at e
    rw [← smul_sub, ← smul_add, ← smul_sub, smul_eq_mul] at e
    exact (mul_eq_zero.1 e).resolve_left hne
  · rw [hw', sub_sub_cancel]
    exact hb

end GlobalTheory
