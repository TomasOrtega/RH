import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ n η t P hgen ht hdvd`. Apply `h₃ K (AlgebraicClosure K) (Fin n)` to reduce the goal to its premises. Rewrite using `[h₁ K L (AlgebraicClosure K) n η]`. Use `set θ : (L →ₐ[K] AlgebraicClosure K) → MvPolynomial (Fin n) (AlgebraicClosure K) := fun σ => ∑ m, X m * C (σ (η m)) with hθ`. Establish `hev : ∀ σ, eval (fun m => algebraMap K (AlgebraicClosure K) (t m)) (θ σ) = 1`.

Introduce `σ`. Establish `h` using `congrArg σ ht`. Simplify using `only [map_sum, map_one, Algebra.smul_def, map_mul, AlgHom.commutes] at h`. Simplify `h` using `[hθ, map_sum, mul_comm]`. Establish `hcoord : ∀ σ m, eval (Pi.single m 1) (θ σ) = σ (η m)`.

Introduce `σ m`. Simplify using `[hθ, Pi.single_apply]`. Establish `hprime : ∀ σ, Prime (θ σ)`. Introduce `σ`. Use `h₂ (AlgebraicClosure K) n (fun m => σ (η m)) ?_` and prove the remaining obligations.

Introduce `h0`. Establish `h` using `hev σ`. Establish `hz : θ σ = 0` using `by simp only [hθ]; simp [funext_iff] at h0; simp [h0]`. Rewrite `h` using `[hz, map_zero]`. Conclude with `zero_ne_one h`.

Establish `hdiv : ∀ σ, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P`. Introduce `σ`. Take `⟨Q, hQ⟩` from `hdvd`. Use `⟨map (σ : L →+* AlgebraicClosure K) Q, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (map (σ : L →+* AlgebraicClosure K)) hQ`.

Rewrite `h` using `[map_map, AlgHom.comp_algebraMap, map_mul]`. Rewrite using `[h]`. Use `congr 1`. Simplify using `[hθ, map_sum]`. Establish `hinj : ∀ a b, θ a ∣ θ b → a = b`.

Introduce `a b hab`. Take `⟨u, hu⟩` from `(hprime a).associated_of_dvd (hprime b) hab`. Take `⟨c, -, hc⟩` from `isUnit_iff_eq_C_of_isReduced.1 u.isUnit`. Rewrite `hu` using `[hc]`. Establish `h1` using `congrArg (eval (fun m => algebraMap K (AlgebraicClosure K) (t m))) hu`.

Rewrite `h1` using `[eval_mul, hev, hev, eval_C, one_mul]`. Rewrite `hu` using `[h1, C_1, mul_one]`. Use `AlgHom.ext_of_adjoin_eq_top hgen ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, rfl⟩`. Rewrite using `[← hcoord a m, ← hcoord b m, hu]`.

Establish `key : ∀ s : Finset (L →ₐ[K] AlgebraicClosure K), ∏ σ ∈ s, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.prod_insert ha]`. Take `⟨R, hR⟩` from `ih`. Establish `h` using `hdiv a`. Rewrite `h` using `[hR]`. Break down `(hprime a).dvd_or_dvd h with h' | h'` into its components or cases.

It suffices to derive a contradiction. Take `⟨b, hb, hab⟩` from `((hprime a).dvd_finsetProd_iff _).1 h'`. Conclude with `ha (by rw [hinj a b hab]; exact hb)`. Take `⟨S, hS⟩` from `h'`. Conclude with `⟨S, by rw [hR, hS]; ring⟩`.

Conclude with `key Finset.univ`.
-/
theorem NormFormDvd.proof (h₁ : NormFormEmbeddings.Statement) (h₂ : LinearFormPrime.Statement)
    (h₃ : MapDvdDescent.Statement) : NormFormDvd.Statement := by
  intro K L _ _ _ _ _ _ n η t P hgen ht hdvd
  classical
  apply h₃ K (AlgebraicClosure K) (Fin n)
  rw [h₁ K L (AlgebraicClosure K) n η]
  set θ : (L →ₐ[K] AlgebraicClosure K) → MvPolynomial (Fin n) (AlgebraicClosure K) :=
    fun σ => ∑ m, X m * C (σ (η m)) with hθ

  have hev : ∀ σ, eval (fun m => algebraMap K (AlgebraicClosure K) (t m)) (θ σ) = 1 := by
    intro σ
    have h := congrArg σ ht
    simp only [map_sum, map_one, Algebra.smul_def, map_mul, AlgHom.commutes] at h
    simpa [hθ, map_sum, mul_comm] using h

  have hcoord : ∀ σ m, eval (Pi.single m 1) (θ σ) = σ (η m) := by
    intro σ m
    simp [hθ, Pi.single_apply]
  have hprime : ∀ σ, Prime (θ σ) := by
    intro σ
    refine h₂ (AlgebraicClosure K) n (fun m => σ (η m)) ?_
    intro h0
    have h := hev σ
    have hz : θ σ = 0 := by simp only [hθ]; simp [funext_iff] at h0; simp [h0]
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hdiv : ∀ σ, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro σ
    obtain ⟨Q, hQ⟩ := hdvd
    refine ⟨map (σ : L →+* AlgebraicClosure K) Q, ?_⟩
    have h := congrArg (map (σ : L →+* AlgebraicClosure K)) hQ
    rw [map_map, AlgHom.comp_algebraMap, map_mul] at h
    rw [h]
    congr 1
    simp [hθ, map_sum]
  have hinj : ∀ a b, θ a ∣ θ b → a = b := by
    intro a b hab
    obtain ⟨u, hu⟩ := (hprime a).associated_of_dvd (hprime b) hab
    obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    rw [hc] at hu
    have h1 := congrArg (eval (fun m => algebraMap K (AlgebraicClosure K) (t m))) hu
    rw [eval_mul, hev, hev, eval_C, one_mul] at h1
    rw [h1, C_1, mul_one] at hu
    refine AlgHom.ext_of_adjoin_eq_top hgen ?_
    rintro _ ⟨m, rfl⟩
    rw [← hcoord a m, ← hcoord b m, hu]
  have key : ∀ s : Finset (L →ₐ[K] AlgebraicClosure K),
      ∏ σ ∈ s, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      obtain ⟨R, hR⟩ := ih
      have h := hdiv a
      rw [hR] at h
      rcases (hprime a).dvd_or_dvd h with h' | h'
      · exfalso
        obtain ⟨b, hb, hab⟩ := ((hprime a).dvd_finsetProd_iff _).1 h'
        exact ha (by rw [hinj a b hab]; exact hb)
      · obtain ⟨S, hS⟩ := h'
        exact ⟨S, by rw [hR, hS]; ring⟩
  exact key Finset.univ

end GroundTheory.Heights₂.Heights
