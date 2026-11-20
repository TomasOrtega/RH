import Development.EtaleCohomology.CohomologicalPurity.LeafRootPf

noncomputable section
open Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

/- English proof (translation)
Take `⟨y, hy⟩` from `(Ideal.Quotient.mk_surjective (hx.unit⁻¹ : (B ⧸ J)ˣ).1)`. Establish `h1 : Ideal.Quotient.mk J (x * y) = Ideal.Quotient.mk J 1`. Rewrite using `[map_mul, hy, map_one]`. Conclude with `hx.mul_val_inv`. Establish `h2 : x * y - 1 ∈ J` using `Ideal.Quotient.eq.mp h1`.

Establish `h3 : IsUnit (x * y)` using `Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ h2)`. Conclude with `isUnit_of_mul_isUnit_left h3`.
-/
theorem hens_isUnit_of_mk {B : Type} [CommRing B] (J : Ideal B) (hJ : J ≤ Ideal.jacobson ⊥) (x : B)
    (hx : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := (Ideal.Quotient.mk_surjective (hx.unit⁻¹ : (B ⧸ J)ˣ).1)
  have h1 : Ideal.Quotient.mk J (x * y) = Ideal.Quotient.mk J 1 := by
    rw [map_mul, hy, map_one]; exact hx.mul_val_inv
  have h2 : x * y - 1 ∈ J := Ideal.Quotient.eq.mp h1
  have h3 : IsUnit (x * y) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hJ h2)
  exact isUnit_of_mul_isUnit_left h3

/- English proof (translation)
Apply `hens_isUnit_of_mk J hJ` to reduce the goal to its premises. Establish `: Ideal.Quotient.mk J x = Ideal.Quotient.mk J y` using `Ideal.Quotient.eq.mpr hxy`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem hens_isUnit_of_sub {B : Type} [CommRing B] (J : Ideal B) (hJ : J ≤ Ideal.jacobson ⊥) (x y : B)
    (hxy : x - y ∈ J) (hy : IsUnit (Ideal.Quotient.mk J y)) : IsUnit x := by
  apply hens_isUnit_of_mk J hJ
  have : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := Ideal.Quotient.eq.mpr hxy
  rwa [this]

/- English proof (translation)
Take `⟨k, hk⟩` from `Polynomial.sub_dvd_eval_sub x y p`. Rewrite using `[hk]`. Conclude with `J.mul_mem_right k h`.
-/
theorem hens_eval_sub_mem {B : Type} [CommRing B] (J : Ideal B) (p : B[X]) (x y : B) (h : x - y ∈ J) :
    p.eval x - p.eval y ∈ J := by
  obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub x y p
  rw [hk]; exact J.mul_mem_right k h

/- English proof (translation)
Establish `h : C (f.eval a) + (X - C a) * (f /ₘ (X - C a)) = f`. Rewrite using `[← Polynomial.modByMonic_X_sub_C_eq_C_eval]`. Conclude with `Polynomial.modByMonic_add_div f _`. Use `conv_rhs => rw [← h]`. Simplify using `[derivative_mul]`.
-/
theorem hens_q_eval {A : Type} [CommRing A] (f : A[X]) (a : A) (hf : f.Monic) :
    (f /ₘ (X - C a)).eval a = f.derivative.eval a := by
  have h : C (f.eval a) + (X - C a) * (f /ₘ (X - C a)) = f := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval]; exact Polynomial.modByMonic_add_div f _
  conv_rhs => rw [← h]
  simp [derivative_mul]

/- English proof (translation)
Introduce `A B _ _ I J hJ ψ hIJ f a hf hfa hu`. Establish `hjac` using `hJ.jac`. Establish `hmk : ∀ x : A, IsUnit (Ideal.Quotient.mk I x) → IsUnit (Ideal.Quotient.mk J (ψ x))`. Introduce `x hx`. Use `hx.map (Ideal.quotientMap J ψ hIJ)` as an intermediate fact.

Simplify `this` using `[Ideal.quotientMap_mk]`. Establish `hder : ∀ z : B, (f.map ψ).derivative.eval z = (f.derivative.map ψ).eval z`. Introduce `z`. Rewrite using `[Polynomial.derivative_map]`. Establish `e0 : ∀ (p : A[X]), (p.map ψ).eval (ψ a) = ψ (p.eval a)`.

Introduce `p`. Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_at_apply]`. Establish `hev0 : (f.map ψ).eval (ψ a) ∈ J` using `by rw [e0]; exact hIJ hfa`. Establish `hu0 : IsUnit (Ideal.Quotient.mk J ((f.map ψ).derivative.eval (ψ a)))`. Rewrite using `[hder, e0]`.

Conclude with `hmk _ hu`. Take `⟨c, hc, hca⟩` from `hJ.is_henselian (f.map ψ) (hf.map ψ) (ψ a) hev0 hu0`. Establish `hc1 : IsUnit ((f.derivative.map ψ).eval c)`. Apply `hens_isUnit_of_sub J hjac _ (ψ (f.derivative.eval a)) _ (hmk _ hu)` to reduce the goal to its premises. Rewrite using `[← e0]`.

Conclude with `hens_eval_sub_mem J _ c (ψ a) hca`. Establish `hc2 : IsUnit (((f /ₘ (X - C a)).map ψ).eval c)`. Apply `hens_isUnit_of_sub J hjac _ (ψ (f.derivative.eval a)) _ (hmk _ hu)` to reduce the goal to its premises. Rewrite using `[← hens_q_eval f a hf, ← e0]`. Conclude with `hens_eval_sub_mem J _ c (ψ a) hca`.

Use `⟨c, hc, hca, hc1, hc2, ?_⟩` and prove the remaining obligations. Introduce `c' hc' hc'a`. Establish `hd : c' - c ∈ J`. Use `J.sub_mem hc'a hca` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.

Take `⟨k, hk⟩` from `Polynomial.binomExpansion (f.map ψ) c (c' - c)`. Rewrite `hk` using `[add_sub_cancel, hc'.eq_zero, hc.eq_zero, zero_add]`. Establish `hfac : (c' - c) * ((f.map ψ).derivative.eval c + k * (c' - c)) = 0`. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hunit : IsUnit ((f.map ψ).derivative.eval c + k * (c' - c))`. Apply `hens_isUnit_of_sub J hjac _ ((f.map ψ).derivative.eval c)` to reduce the goal to its premises. Rewrite using `[add_sub_cancel_left]`. Conclude with `J.mul_mem_left k hd`. Rewrite using `[hder]`.

Conclude with `hc1.map _`. Establish `: c' - c = 0` using `(hunit.mul_left_eq_zero).mp hfac`. Conclude with `sub_eq_zero.mp this`.
-/
theorem LeafRootHens_of : LeafRootHens := by
  intro A B _ _ I J hJ ψ hIJ f a hf hfa hu
  have hjac := hJ.jac
  have hmk : ∀ x : A, IsUnit (Ideal.Quotient.mk I x) → IsUnit (Ideal.Quotient.mk J (ψ x)) := by
    intro x hx
    have := hx.map (Ideal.quotientMap J ψ hIJ)
    simpa [Ideal.quotientMap_mk] using this
  have hder : ∀ z : B, (f.map ψ).derivative.eval z = (f.derivative.map ψ).eval z := by
    intro z; rw [Polynomial.derivative_map]
  have e0 : ∀ (p : A[X]), (p.map ψ).eval (ψ a) = ψ (p.eval a) := by
    intro p; rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hev0 : (f.map ψ).eval (ψ a) ∈ J := by rw [e0]; exact hIJ hfa
  have hu0 : IsUnit (Ideal.Quotient.mk J ((f.map ψ).derivative.eval (ψ a))) := by
    rw [hder, e0]; exact hmk _ hu
  obtain ⟨c, hc, hca⟩ := hJ.is_henselian (f.map ψ) (hf.map ψ) (ψ a) hev0 hu0
  have hc1 : IsUnit ((f.derivative.map ψ).eval c) := by
    apply hens_isUnit_of_sub J hjac _ (ψ (f.derivative.eval a)) _ (hmk _ hu)
    rw [← e0]; exact hens_eval_sub_mem J _ c (ψ a) hca
  have hc2 : IsUnit (((f /ₘ (X - C a)).map ψ).eval c) := by
    apply hens_isUnit_of_sub J hjac _ (ψ (f.derivative.eval a)) _ (hmk _ hu)
    rw [← hens_q_eval f a hf, ← e0]; exact hens_eval_sub_mem J _ c (ψ a) hca
  refine ⟨c, hc, hca, hc1, hc2, ?_⟩
  intro c' hc' hc'a
  have hd : c' - c ∈ J := by
    have := J.sub_mem hc'a hca
    rwa [sub_sub_sub_cancel_right] at this
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map ψ) c (c' - c)
  rw [add_sub_cancel, hc'.eq_zero, hc.eq_zero, zero_add] at hk
  have hfac : (c' - c) * ((f.map ψ).derivative.eval c + k * (c' - c)) = 0 := by
    rw [hk]; ring
  have hunit : IsUnit ((f.map ψ).derivative.eval c + k * (c' - c)) := by
    apply hens_isUnit_of_sub J hjac _ ((f.map ψ).derivative.eval c)
    · rw [add_sub_cancel_left]; exact J.mul_mem_left k hd
    · rw [hder]; exact hc1.map _
  have : c' - c = 0 := (hunit.mul_left_eq_zero).mp hfac
  exact sub_eq_zero.mp this

end LateralTheory.CohomologicalPurity.Hz
