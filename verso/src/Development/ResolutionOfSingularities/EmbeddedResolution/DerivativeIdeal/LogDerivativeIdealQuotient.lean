import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivationOfSurjective

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k] {S T : Type*} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

/- English proof (authored)
The images of the elements of J belong to the ordinary derivative ideal of its extension. A derivation preserving the kernel of f descends through the surjection. Thus the image of its derivative of an element of J is the derivative of the corresponding image under the descended derivation. It belongs to the target derivative ideal as well. This gives the containment on all generators.
-/
theorem map_logDerivIdeal_ker_le_derivIdeal_map (f : S →ₐ[k] T)
    (hf : Function.Surjective f) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdeal k (RingHom.ker f.toRingHom) J)
      ≤ derivIdeal k (Ideal.map f.toRingHom J) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_derivIdeal k (Ideal.map f.toRingHom J) (Ideal.mem_map_of_mem f.toRingHom hx)
  · intro D hD x hx
    have hD' : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom :=
      (mem_tangentDerivations k (RingHom.ker f.toRingHom) D).mp hD
    have hmem : f x ∈ Ideal.map f.toRingHom J := Ideal.mem_map_of_mem f.toRingHom hx
    have h2 := derivation_apply_mem_derivIdeal k (Ideal.map f.toRingHom J)
      (derivationOfSurjective f hf D hD') hmem
    rw [derivationOfSurjective_apply] at h2
    rw [Ideal.mem_comap]
    exact h2

/- English proof (authored)
At the zero-th iterate both sides give the extended J. At a successor apply the one-step quotient containment to the preceding logarithmic iterate. The induction hypothesis and monotonicity of the target derivative ideal bound the result by the next ordinary iterate of the extended J.
-/
theorem map_logDerivIdealIterate_ker_le_derivIdealIterate_map (f : S →ₐ[k] T)
    (hf : Function.Surjective f) (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k (RingHom.ker f.toRingHom) r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ]
      exact (map_logDerivIdeal_ker_le_derivIdeal_map k f hf _).trans (derivIdeal_mono k ih)

/- English proof (authored)
Replace P by the kernel of f using the assumed equality. The iterative quotient containment then gives exactly the stated result.
-/
theorem map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker (f : S →ₐ[k] T)
    (hf : Function.Surjective f) {P : Ideal S} (hP : P = RingHom.ker f.toRingHom)
    (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k P r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  subst hP
  exact map_logDerivIdealIterate_ker_le_derivIdealIterate_map k f hf r J

end FunctorialResolution.EmbeddedResolution
