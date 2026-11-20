import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.SkewUnit

/- English proof (translation)
Establish `hfin : {P : Ideal R | P.IsMaximal ∧ p ∈ P}.Finite`. Establish `h1` using `(Ideal.finite_factors (I := Ideal.span {p}) (by simpa using hp)).image (fun v => v.asIdeal)`. Use `h1.subset ?_` and prove the remaining obligations. Introduce and unpack `P ⟨hP, hpP⟩`. Establish `hne : P ≠ ⊥` using `fun h0 => hp (by simpa [h0] using hpP)`.

Conclude with `⟨⟨P, hP.isPrime, hne⟩, by`. Simplify `hpP, rfl⟩` using `[Ideal.dvd_span_singleton]`. Establish `: Finite {P : Ideal R // P.IsMaximal ∧ p ∈ P}` using `hfin.to_subtype`. Set `x : Ideal R → R` to `fun P => Classical.epsilon (fun θ => θ - σ θ ∉ P)`. Take `⟨r, hr⟩` from `Ideal.exists_forall_sub_mem_ideal (ι := {P : Ideal R // P.IsMaximal ∧ p ∈ P}) (I := fun P => P.1) (fun P Q hPQ => by`.

Use `P.2.1` as an intermediate fact. Use `Q.2.1` as an intermediate fact. Conclude with `Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne P.2.1 Q.2.1 (fun e => hPQ (Subtype.ext e))))`. Use the proof step `(fun P => x P.1)`. Use `⟨r, fun P hP hpP hmem => ?_⟩` and prove the remaining obligations.

Establish `hsurj : Function.Surjective σ` using `fun y => ⟨σ y, hσ y⟩`. Use `hP` as an intermediate fact. Establish `hQ : (P.comap σ).IsMaximal` using `Ideal.comap_isMaximal_of_surjective σ hsurj`. Establish `hpQ : p ∈ P.comap σ` using `by rw [Ideal.mem_comap, hσp]; exact hpP`. Establish `hx : x (P.comap σ) = x P`.

Establish `: (fun θ => θ - σ θ ∉ P.comap σ) = (fun θ => θ - σ θ ∉ P)`. Use function extensionality and compare the values at `θ`. Rewrite using `[Ideal.mem_comap, map_sub, hσ, ← neg_sub, Ideal.neg_mem_iff]`. Simplify using `only [x, this]`. Establish `h1 : r - x P ∈ P` using `hr ⟨P, hP, hpP⟩`.

Establish `h2 : r - x (P.comap σ) ∈ P.comap σ` using `hr ⟨_, hQ, hpQ⟩`. Rewrite `h2` using `[hx, Ideal.mem_comap, map_sub]`. Establish `h3 : x P - σ (x P) ∉ P` using `Classical.epsilon_spec (h P hP)`. Apply `h3` to reduce the goal to its premises. Establish `: x P - σ (x P) = (r - σ r) - (r - x P) + (σ r - σ (x P))` using `by ring`.

Rewrite using `[this]`. Conclude with `add_mem (sub_mem hmem h1) h2`.
-/
theorem exists_sub_notMem {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (hσ : ∀ x, σ (σ x) = x) {p : R} (hp : p ≠ 0) (hσp : σ p = p)
    (h : ∀ P : Ideal R, P.IsMaximal → ∃ θ, θ - σ θ ∉ P) :
    ∃ θ, ∀ P : Ideal R, P.IsMaximal → p ∈ P → θ - σ θ ∉ P := by
  classical
  have hfin : {P : Ideal R | P.IsMaximal ∧ p ∈ P}.Finite := by
    have h1 := (Ideal.finite_factors (I := Ideal.span {p}) (by simpa using hp)).image
      (fun v => v.asIdeal)
    refine h1.subset ?_
    rintro P ⟨hP, hpP⟩
    have hne : P ≠ ⊥ := fun h0 => hp (by simpa [h0] using hpP)
    exact ⟨⟨P, hP.isPrime, hne⟩, by
      simpa [Ideal.dvd_span_singleton] using hpP, rfl⟩
  have : Finite {P : Ideal R // P.IsMaximal ∧ p ∈ P} := hfin.to_subtype
  let x : Ideal R → R := fun P => Classical.epsilon (fun θ => θ - σ θ ∉ P)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal
    (ι := {P : Ideal R // P.IsMaximal ∧ p ∈ P}) (I := fun P => P.1)
    (fun P Q hPQ => by
      have := P.2.1
      have := Q.2.1
      exact Ideal.isCoprime_iff_sup_eq.2
        (Ideal.IsMaximal.coprime_of_ne P.2.1 Q.2.1 (fun e => hPQ (Subtype.ext e))))
    (fun P => x P.1)
  refine ⟨r, fun P hP hpP hmem => ?_⟩
  have hsurj : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩
  have := hP
  have hQ : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hpQ : p ∈ P.comap σ := by rw [Ideal.mem_comap, hσp]; exact hpP
  have hx : x (P.comap σ) = x P := by
    have : (fun θ => θ - σ θ ∉ P.comap σ) = (fun θ => θ - σ θ ∉ P) := by
      funext θ
      rw [Ideal.mem_comap, map_sub, hσ, ← neg_sub, Ideal.neg_mem_iff]
    simp only [x, this]
  have h1 : r - x P ∈ P := hr ⟨P, hP, hpP⟩
  have h2 : r - x (P.comap σ) ∈ P.comap σ := hr ⟨_, hQ, hpQ⟩
  rw [hx, Ideal.mem_comap, map_sub] at h2
  have h3 : x P - σ (x P) ∉ P := Classical.epsilon_spec (h P hP)
  apply h3
  have : x P - σ (x P) = (r - σ r) - (r - x P) + (σ r - σ (x P)) := by ring
  rw [this]
  exact add_mem (sub_mem hmem h1) h2

/- English proof (translation)
Establish `h1` using `InfinitePlace.prod_eq_abs_norm (δ : E)`. Rewrite `h1` using `[← hφ.prod_comp (fun w => w (δ : E) ^ w.mult)]`. Simplify using `only [IsTotallyComplex.mult_eq, InfinitePlace.apply] at h1`. Rewrite using `[h1, ← Algebra.coe_norm_int, Nat.cast_natAbs]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem prod_norm_sq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {ι : Type} [Fintype ι]
    (φ : ι → E →+* ℂ) (hφ : Function.Bijective (fun v => InfinitePlace.mk (φ v))) (δ : 𝓞 E) :
    ∏ v, ‖φ v (δ : E)‖ ^ 2 = ((Algebra.norm ℤ δ).natAbs : ℝ) := by
  have h1 := InfinitePlace.prod_eq_abs_norm (δ : E)
  rw [← hφ.prod_comp (fun w => w (δ : E) ^ w.mult)] at h1
  simp only [IsTotallyComplex.mult_eq, InfinitePlace.apply] at h1
  rw [h1, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

/- English proof (translation)
Introduce `E _ _ _ hE ι _ φ hφ p hp`. Use `hE.1` as an intermediate fact. Set `σ : 𝓞 E →+* 𝓞 E` to `RingOfIntegers.mapRingHom (starRingEnd E)`. Establish `hσ : ∀ x, ((σ x : 𝓞 E) : E) = star (x : E)` using `fun x => rfl`. Establish `hσσ : ∀ x, σ (σ x) = x` using `fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])`.

Take `⟨θ, hθ⟩` from `exists_sub_notMem σ hσσ (p := (p : 𝓞 E)) (by exact_mod_cast hp.ne_zero) (map_natCast σ p) (fun P hP => by`. Take `⟨θ, t, ht, hm⟩` from `hE.2.2 P hP`. Establish `: σ θ = t` using `RingOfIntegers.ext (by rw [hσ]; exact ht.symm)`. Conclude with `⟨θ, by rwa [this]⟩)`. Use `⟨θ - σ θ, (Algebra.norm ℤ (θ - σ θ)).natAbs, ?_, ?_, prod_norm_sq φ hφ _⟩` and prove the remaining obligations.

Rewrite using `[← hσ, map_sub σ, hσσ, ← neg_sub θ]`. Conclude with `map_neg (algebraMap (𝓞 E) E) _`. Introduce `hd`. Rewrite `hd` using `[← Ideal.absNorm_span_singleton]`. Take `⟨P, hP, hu, hdv⟩` from `Ideal.exists_isMaximal_dvd_of_dvd_absNorm (Nat.prime_iff_prime_int.1 hp) _ (Int.natCast_dvd_natCast.2 hd)`.

Use `hθ P hP ?_ (Ideal.dvd_span_singleton.1 hdv)` and prove the remaining obligations. Establish `: (p : ℤ) ∈ Ideal.under ℤ P` using `hu ▸ Ideal.mem_span_singleton_self _`. Simplify `this` using `[Ideal.mem_comap]`.
-/
theorem exists_skew_norm_coprime : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ p : ℕ, p.Prime → ∃ (δ : 𝓞 E) (N : ℕ), star (δ : E) = -(δ : E) ∧ ¬ p ∣ N ∧ ∏ v, ‖φ v (δ : E)‖ ^ 2 = N := by
  intro E _ _ _ hE ι _ φ hφ p hp
  have := hE.1
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ x, ((σ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])
  obtain ⟨θ, hθ⟩ := exists_sub_notMem σ hσσ (p := (p : 𝓞 E)) (by exact_mod_cast hp.ne_zero)
    (map_natCast σ p) (fun P hP => by
      obtain ⟨θ, t, ht, hm⟩ := hE.2.2 P hP
      have : σ θ = t := RingOfIntegers.ext (by rw [hσ]; exact ht.symm)
      exact ⟨θ, by rwa [this]⟩)
  refine ⟨θ - σ θ, (Algebra.norm ℤ (θ - σ θ)).natAbs, ?_, ?_, prod_norm_sq φ hφ _⟩
  · rw [← hσ, map_sub σ, hσσ, ← neg_sub θ]
    exact map_neg (algebraMap (𝓞 E) E) _
  · intro hd
    rw [← Ideal.absNorm_span_singleton] at hd
    obtain ⟨P, hP, hu, hdv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm
      (Nat.prime_iff_prime_int.1 hp) _ (Int.natCast_dvd_natCast.2 hd)
    refine hθ P hP ?_ (Ideal.dvd_span_singleton.1 hdv)
    have : (p : ℤ) ∈ Ideal.under ℤ P := hu ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this

end GlobalTheory.RadCov.SkewUnit
