import Mathlib

namespace GlobalTheory.CompanionTheory.SplitQuadratic

/- English proof (translation)
Introduce `R O _ _ _ _ ι δ e hδ hspan _ he h2`. Take `⟨e', he'⟩` from `he.exists_right_inv`. Take `⟨h, hh⟩` from `h2.exists_right_inv`. Establish `hee' : ι e * ι e' = 1` using `by rw [← map_mul, he', map_one]`. Establish `h2' : 2 * ι h = 1`.

Use `congrArg ι hh` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, map_ofNat]`. Then use the resulting hypothesis. Establish `hδ' : δ * δ = ι e * ι e` using `by rw [hδ, map_mul]`. Establish `hu2 : (ι e' * δ) * (ι e' * δ) = 1`. Take the linear combination `(ι e' * ι e') * hδ' + (ι e * ι e' + 1) * hee'`.

Use `set ε₁ : O := ι h * (1 + ι e' * δ) with hε₁`. Use `set ε₂ : O := ι h * (1 - ι e' * δ) with hε₂`. Establish `h11 : ε₁ * ε₁ = ε₁`. Rewrite using `[hε₁]`. Take the linear combination `(ι h * (1 + ι e' * δ)) * h2' + (ι h * ι h) * hu2`.

Establish `h22 : ε₂ * ε₂ = ε₂`. Rewrite using `[hε₂]`. Take the linear combination `(ι h * (1 - ι e' * δ)) * h2' + (ι h * ι h) * hu2`. Establish `h12 : ε₁ * ε₂ = 0`. Rewrite using `[hε₁, hε₂]`.

Take the linear combination `(-(ι h * ι h)) * hu2`. Establish `hsum : ε₁ + ε₂ = 1`. Rewrite using `[hε₁, hε₂]`. Take the linear combination `h2'`. Set `φ : R × R →+* O` to `{ toFun := fun x => ι x.1 * ε₁ + ι x.2 * ε₂ map_one' := by`.

Simplify using `only [Prod.fst_one, Prod.snd_one, map_one, one_mul]`. Conclude with `hsum`. Use the proof step `map_mul' := fun x y => by`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, map_mul]`. Take the linear combination `(-(ι x.1 * ι y.1)) * h11 + (-(ι x.2 * ι y.2)) * h22 + (-(ι x.1 * ι y.2 + ι x.2 * ι y.1)) * h12`.

Use the proof step `map_zero' := by simp`. Use the proof step `map_add' := fun x y => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, map_add]`. Use `ring }`. Establish `hsurj : Function.Surjective φ`.

Introduce `y`. Take `⟨p, q, rfl⟩` from `hspan y`. Use `⟨(p + q * e, p - q * e), ?_⟩` and prove the remaining obligations. Use `show ι (p + q * e) * ε₁ + ι (p - q * e) * ε₂ = ι p + ι q * δ`. Rewrite using `[hε₁, hε₂]`.

Simplify using `only [map_add, map_sub, map_mul]`. Take the linear combination `(ι p + ι q * ι e * ι e' * δ) * h2' + (ι q * δ) * hee'`. Conclude with `IsPrincipalIdealRing.of_surjective φ hsurj`.
-/
theorem isPrincipalIdealRing_of_sq_eq_sq :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
      (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) →
      (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ ι δ e hδ hspan _ he h2
  obtain ⟨e', he'⟩ := he.exists_right_inv
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hee' : ι e * ι e' = 1 := by rw [← map_mul, he', map_one]
  have h2' : 2 * ι h = 1 := by
    have := congrArg ι hh
    rwa [map_mul, map_one, map_ofNat] at this
  have hδ' : δ * δ = ι e * ι e := by rw [hδ, map_mul]

  have hu2 : (ι e' * δ) * (ι e' * δ) = 1 := by
    linear_combination (ι e' * ι e') * hδ' + (ι e * ι e' + 1) * hee'

  set ε₁ : O := ι h * (1 + ι e' * δ) with hε₁
  set ε₂ : O := ι h * (1 - ι e' * δ) with hε₂
  have h11 : ε₁ * ε₁ = ε₁ := by
    rw [hε₁]
    linear_combination (ι h * (1 + ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h22 : ε₂ * ε₂ = ε₂ := by
    rw [hε₂]
    linear_combination (ι h * (1 - ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h12 : ε₁ * ε₂ = 0 := by
    rw [hε₁, hε₂]
    linear_combination (-(ι h * ι h)) * hu2
  have hsum : ε₁ + ε₂ = 1 := by
    rw [hε₁, hε₂]
    linear_combination h2'

  let φ : R × R →+* O :=
    { toFun := fun x => ι x.1 * ε₁ + ι x.2 * ε₂
      map_one' := by
        simp only [Prod.fst_one, Prod.snd_one, map_one, one_mul]
        exact hsum
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination (-(ι x.1 * ι y.1)) * h11 + (-(ι x.2 * ι y.2)) * h22 +
          (-(ι x.1 * ι y.2 + ι x.2 * ι y.1)) * h12
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring }
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p, q, rfl⟩ := hspan y
    refine ⟨(p + q * e, p - q * e), ?_⟩
    show ι (p + q * e) * ε₁ + ι (p - q * e) * ε₂ = ι p + ι q * δ
    rw [hε₁, hε₂]
    simp only [map_add, map_sub, map_mul]
    linear_combination (ι p + ι q * ι e * ι e' * δ) * h2' + (ι q * δ) * hee'
  exact IsPrincipalIdealRing.of_surjective φ hsurj

end GlobalTheory.CompanionTheory.SplitQuadratic
