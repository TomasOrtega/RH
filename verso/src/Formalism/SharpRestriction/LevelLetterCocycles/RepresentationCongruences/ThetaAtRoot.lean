import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGLLatBasisOfIsSplitEquiv
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ThetaAtRootAlt

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/- English proof (translation)
Take `⟨f', hf'⟩` from `(PowerSeries.X_dvd_iff).mpr (show constantCoeff (f - C (constantCoeff f)) = 0 by simp)`. Conclude with `⟨f', by linear_combination hf'⟩`.
-/
private theorem exists_eq_C_constantCoeff_add_X_mul {A : Type*} [CommRing A] (f : A⟦X⟧) :
    ∃ f' : A⟦X⟧, f = C (constantCoeff f) + X * f' := by
  obtain ⟨f', hf'⟩ :=
    (PowerSeries.X_dvd_iff).mpr (show constantCoeff (f - C (constantCoeff f)) = 0 by simp)
  exact ⟨f', by linear_combination hf'⟩

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∀ g : A⟦X⟧, ψ₁ X ^ n ∣ ψ₁ g - ψ₂ g`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro g`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `g`. Take `⟨g', hg'⟩` from `exists_eq_C_constantCoeff_add_X_mul g`. Take `⟨r, hr⟩` from `ih g'`. Establish `e1 : ψ₁ g = ψ₁ (C (constantCoeff g)) + ψ₁ X * ψ₁ g'`.

Combine the equalities or inequalities in the displayed calculation. Establish `e2 : ψ₂ g = ψ₂ (C (constantCoeff g)) + ψ₂ X * ψ₂ g'`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨r, by linear_combination e1 - e2 + hC (constantCoeff g) + ψ₂ g' * hX + ψ₁ X * hr⟩`. Conclude with `sub_eq_zero.mp (hsep _ (fun n => key n f))`.
-/
private theorem ringHom_eq_of_eq_on_C_X_of_pow_dvd_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    (ψ₁ ψ₂ : A⟦X⟧ →+* B) (hC : ∀ a, ψ₁ (C a) = ψ₂ (C a)) (hX : ψ₁ X = ψ₂ X)
    (hsep : ∀ d : B, (∀ n : ℕ, ψ₁ X ^ n ∣ d) → d = 0) (f : A⟦X⟧) : ψ₁ f = ψ₂ f := by
  have key : ∀ n : ℕ, ∀ g : A⟦X⟧, ψ₁ X ^ n ∣ ψ₁ g - ψ₂ g := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      obtain ⟨g', hg'⟩ := exists_eq_C_constantCoeff_add_X_mul g
      obtain ⟨r, hr⟩ := ih g'
      have e1 : ψ₁ g = ψ₁ (C (constantCoeff g)) + ψ₁ X * ψ₁ g' := by
        calc ψ₁ g = ψ₁ (C (constantCoeff g) + X * g') := by rw [← hg']
          _ = _ := by rw [map_add, map_mul]
      have e2 : ψ₂ g = ψ₂ (C (constantCoeff g)) + ψ₂ X * ψ₂ g' := by
        calc ψ₂ g = ψ₂ (C (constantCoeff g) + X * g') := by rw [← hg']
          _ = _ := by rw [map_add, map_mul]
      exact ⟨r, by linear_combination e1 - e2 + hC (constantCoeff g) + ψ₂ g' * hX + ψ₁ X * hr⟩
  exact sub_eq_zero.mp (hsep _ (fun n => key n f))

/- English proof (translation)
Establish `hxm : x₀ ∈ IsLocalRing.maximalIdeal O` using `Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.mem_max l hl hroot`. Take `⟨I, hI⟩ : ∃ I : Ideal O⟦X⟧, I = Ideal.span {X - C x₀}` from `⟨_, rfl⟩`. Rewrite using `[← hI]`. Establish `hXI : X - C x₀ ∈ I` using `by rw [hI]; exact Ideal.mem_span_singleton_self _`. Establish `hπX : Ideal.Quotient.mk I X = Ideal.Quotient.mk I (C x₀)` using `Ideal.Quotient.eq.mpr hXI`.

Establish `hinj : ∀ a b : O, Ideal.Quotient.mk I (C a) = Ideal.Quotient.mk I (C b) → a = b`. Introduce `a b hab`. Establish `h' : C (a - b) ∈ Ideal.span {X - C x₀}`. Rewrite using `[map_sub, ← hI]`. Conclude with `Ideal.Quotient.eq.mp hab`.

Conclude with `sub_eq_zero.mp (Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hxm h')`. Establish `hsurj : ∀ p : O⟦X⟧, ∃ c : O, Ideal.Quotient.mk I p = Ideal.Quotient.mk I (C c)`. Introduce `p`. Take `⟨c, q, hpq⟩` from `Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.decomp hxm p`. Use `⟨c, Ideal.Quotient.eq.mpr ?_⟩` and prove the remaining obligations.

Rewrite using `[hpq, add_sub_cancel_right]`. Conclude with `I.mul_mem_right q hXI`. Establish `hsep : ∀ d : O⟦X⟧ ⧸ I, (∀ n : ℕ, Ideal.Quotient.mk I X ^ n ∣ d) → d = 0`. Introduce `d hd`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective d`.

Take `⟨c, hc'⟩` from `hsurj p`. Rewrite `hd`, the goal using `[hc']`. Establish `hmem : ∀ n : ℕ, c ∈ Ideal.span {x₀} ^ n`. Introduce `n`. Take `⟨r, hr⟩` from `hd n`.

Take `⟨p', rfl⟩` from `Ideal.Quotient.mk_surjective r`. Take `⟨e, he⟩` from `hsurj p'`. Establish `h2 : Ideal.Quotient.mk I (C c) = Ideal.Quotient.mk I (C (x₀ ^ n * e))`. Rewrite using `[hr, hπX, he]`. Simplify using `only [map_mul, map_pow]`.

Rewrite using `[hinj _ _ h2, Ideal.span_singleton_pow]`. Conclude with `(Ideal.span {x₀ ^ n}).mul_mem_right e (Ideal.mem_span_singleton_self _)`. Establish `hne : Ideal.span {x₀} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Conclude with `mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x₀).mp hxm)`.

Establish `hc0 : c ∈ ⨅ n : ℕ, Ideal.span {x₀} ^ n` using `Ideal.mem_iInf.mpr hmem`. Rewrite `hc0` using `[Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {x₀}) hne, Ideal.mem_bot]`. Rewrite using `[hc0, map_zero, map_zero]`. Establish `hπφX : Ideal.Quotient.mk I (φ₀ X) = 0`. Establish `h3 : Ideal.Quotient.mk I (φ₀ X) = Ideal.Quotient.mk I (C ((1 + x₀) ^ l - 1))`.

Rewrite using `[hφ₀]`. Simplify using `only [map_sub, map_pow, map_add, map_one, hπX]`. Rewrite using `[h3, hroot, sub_self, map_zero, map_zero]`. Establish `hφπ : ∀ f, Ideal.Quotient.mk I (φ₀ f) = Ideal.Quotient.mk I (C (constantCoeff f))`. Introduce `f`.

Take `⟨f', hf'⟩` from `exists_eq_C_constantCoeff_add_X_mul f`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_add, map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.alg_C, hπφX, zero_mul, add_zero]`. Take `⟨g1, hg1⟩` from `(PowerSeries.X_dvd_iff).mpr h0`. Establish `hg1χ : constantCoeff g1 = χ`.

Rewrite using `[← h1, hg1]`. Use `show constantCoeff g1 = coeff (0 + 1) (X * g1)`. Rewrite using `[PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Take `⟨t, ht⟩` from `exists_eq_C_constantCoeff_add_X_mul g1`. Take `⟨e, he⟩` from `hsurj t`.

Establish `hπg1 : Ideal.Quotient.mk I g1 = Ideal.Quotient.mk I (C (χ + x₀ * e))`. Rewrite using `[ht, hg1χ]`. Simplify using `only [map_add, map_mul, hπX, he]`. Establish `hπg : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I (C (x₀ * (χ + x₀ * e)))`. Rewrite using `[hg1, map_mul, hπg1, hπX]`.

Simplify using `only [map_mul]`. Establish `hry : (1 + x₀ * (χ + x₀ * e)) ^ l = 1`. Establish `h4 : Ideal.Quotient.mk I (γ (φ₀ X)) = 0`. Rewrite using `[← hc X, hφπ, h0, map_zero, map_zero]`. Establish `h5 : Ideal.Quotient.mk I (γ (φ₀ X)) = Ideal.Quotient.mk I (C ((1 + x₀ * (χ + x₀ * e)) ^ l - 1))`.

Rewrite using `[hφ₀]`. Simplify using `only [map_sub, map_pow, map_add, map_one, hπg]`. Establish `h6` using `hinj ((1 + x₀ * (χ + x₀ * e)) ^ l - 1) 0 (by rw [← h5, h4, map_zero, map_zero])`. Conclude with `sub_eq_zero.mp h6`. Establish `hχm : χ - 1 ∈ IsLocalRing.maximalIdeal O` using `(Ideal.span_singleton_le_iff_mem _).mpr hl hχ`.

Establish `hw : χ - 1 + x₀ * e ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.maximalIdeal O).add_mem hχm ((IsLocalRing.maximalIdeal O).mul_mem_right e hxm)`. Establish `hyx : x₀ * (χ + x₀ * e) = x₀` using `Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.root_eq l hx₀ hroot hry hw (by ring)`. Establish `hχe : χ + x₀ * e = 1` using `mul_left_cancel₀ hx₀ (by rw [hyx, mul_one])`. Establish `hπg1' : Ideal.Quotient.mk I g1 = 1` using `by rw [hπg1, hχe, map_one, map_one]`. Establish `hπgX : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I X`.

Rewrite using `[hπg, hyx, hπX]`. Establish `hγπ : ∀ f, Ideal.Quotient.mk I (γ f) = Ideal.Quotient.mk I f`. Introduce `f`. Conclude with `(ringHom_eq_of_eq_on_C_X_of_pow_dvd_eq_zero (Ideal.Quotient.mk I) ((Ideal.Quotient.mk I).comp γ.toRingHom) (fun a => by show _ = Ideal.Quotient.mk I (γ (C a))`. Rewrite using `[Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.alg_C])`.

Use the proof step `hπgX.symm hsep f).symm`. Take `⟨Q0, hQ0c, hQ0⟩` from `Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.exists_GL_latBasis_of_isSplitEquiv (O := O) l`. Establish `hQQ0 : Q = Q0` using `mul_left_cancel₀ PowerSeries.X_ne_zero (hQ.trans hQ0)`. Establish `hQne : Q ≠ 0`. Introduce `hQz`.

Establish `hl0 : ((l : ℕ) : O) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero`. Apply `hl0` to reduce the goal to its premises. Rewrite using `[← hQ0c, ← hQQ0, hQz, map_zero]`. Establish `hγQ : γ (X * Q) = X * g1 * γ Q` using `by rw [map_mul, hg1]`. Establish `hγQ' : γ (X * Q) = X * Q * φ₀ g1`.

Rewrite using `[hQ, ← hφ₀, ← hc X, hg1, map_mul]`. Establish `hg1Q : g1 * γ Q = Q * φ₀ g1` using `mul_left_cancel₀ PowerSeries.X_ne_zero (by linear_combination hγQ' - hγQ)`. Establish `hkey : Q * (g1 * u * θ) = Q * (γ u * φ₀ g1)`. Establish `e3 : γ (u * Q) = γ u * γ Q` using `map_mul _ _ _`. Take the linear combination `(-g1) * hθ + g1 * e3 + γ u * hg1Q`.

Establish `hkey' : g1 * u * θ = γ u * φ₀ g1` using `mul_left_cancel₀ hQne hkey`. Establish `hk : Ideal.Quotient.mk I (g1 * u * θ) = Ideal.Quotient.mk I (γ u * φ₀ g1)`. Rewrite using `[hkey']`. Simplify using `only [map_mul] at hk`. Rewrite `hk` using `[hγπ, hφπ, hg1χ, hπg1', one_mul]`.

Conclude with `Ideal.Quotient.eq.mp ((hu.map (Ideal.Quotient.mk I)).mul_left_cancel hk)`.
-/
theorem theta_at_root (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (φ₀ γ : O⟦X⟧ →ₐ[O] O⟦X⟧) (hφ₀ : φ₀ X = (1 + X) ^ l - 1) (hc : ∀ f, φ₀ (γ f) = γ (φ₀ f))
    (χ : O) (h0 : constantCoeff (γ X) = 0) (h1 : coeff 1 (γ X) = χ)
    (hχ : χ - 1 ∈ Ideal.span {((l : ℕ) : O)})
    (x₀ : O) (hx₀ : x₀ ≠ 0) (hroot : (1 + x₀) ^ l = 1)
    (Q : O⟦X⟧) (hQ : X * Q = (1 + X) ^ l - 1) (u : O⟦X⟧) (hu : IsUnit u) (θ : O⟦X⟧)
    (hθ : γ (u * Q) = u * Q * θ) :
    θ - C χ ∈ Ideal.span {X - C x₀} := by
  have hxm : x₀ ∈ IsLocalRing.maximalIdeal O :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.mem_max l hl hroot
  obtain ⟨I, hI⟩ : ∃ I : Ideal O⟦X⟧, I = Ideal.span {X - C x₀} := ⟨_, rfl⟩
  rw [← hI]
  have hXI : X - C x₀ ∈ I := by rw [hI]; exact Ideal.mem_span_singleton_self _
  have hπX : Ideal.Quotient.mk I X = Ideal.Quotient.mk I (C x₀) := Ideal.Quotient.eq.mpr hXI
  have hinj : ∀ a b : O, Ideal.Quotient.mk I (C a) = Ideal.Quotient.mk I (C b) → a = b := by
    intro a b hab
    have h' : C (a - b) ∈ Ideal.span {X - C x₀} := by
      rw [map_sub, ← hI]; exact Ideal.Quotient.eq.mp hab
    exact sub_eq_zero.mp (Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hxm h')
  have hsurj : ∀ p : O⟦X⟧, ∃ c : O, Ideal.Quotient.mk I p = Ideal.Quotient.mk I (C c) := by
    intro p
    obtain ⟨c, q, hpq⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.decomp hxm p
    refine ⟨c, Ideal.Quotient.eq.mpr ?_⟩
    rw [hpq, add_sub_cancel_right]
    exact I.mul_mem_right q hXI
  have hsep : ∀ d : O⟦X⟧ ⧸ I, (∀ n : ℕ, Ideal.Quotient.mk I X ^ n ∣ d) → d = 0 := by
    intro d hd
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨c, hc'⟩ := hsurj p
    rw [hc'] at hd ⊢
    have hmem : ∀ n : ℕ, c ∈ Ideal.span {x₀} ^ n := by
      intro n
      obtain ⟨r, hr⟩ := hd n
      obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨e, he⟩ := hsurj p'
      have h2 : Ideal.Quotient.mk I (C c) = Ideal.Quotient.mk I (C (x₀ ^ n * e)) := by
        rw [hr, hπX, he]; simp only [map_mul, map_pow]
      rw [hinj _ _ h2, Ideal.span_singleton_pow]
      exact (Ideal.span {x₀ ^ n}).mul_mem_right e (Ideal.mem_span_singleton_self _)
    have hne : Ideal.span {x₀} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x₀).mp hxm)
    have hc0 : c ∈ ⨅ n : ℕ, Ideal.span {x₀} ^ n := Ideal.mem_iInf.mpr hmem
    rw [Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {x₀}) hne, Ideal.mem_bot] at hc0
    rw [hc0, map_zero, map_zero]
  have hπφX : Ideal.Quotient.mk I (φ₀ X) = 0 := by
    have h3 : Ideal.Quotient.mk I (φ₀ X) = Ideal.Quotient.mk I (C ((1 + x₀) ^ l - 1)) := by
      rw [hφ₀]; simp only [map_sub, map_pow, map_add, map_one, hπX]
    rw [h3, hroot, sub_self, map_zero, map_zero]
  have hφπ : ∀ f, Ideal.Quotient.mk I (φ₀ f) = Ideal.Quotient.mk I (C (constantCoeff f)) := by
    intro f
    obtain ⟨f', hf'⟩ := exists_eq_C_constantCoeff_add_X_mul f
    calc Ideal.Quotient.mk I (φ₀ f)
        = Ideal.Quotient.mk I (φ₀ (C (constantCoeff f) + X * f')) := by rw [← hf']
      _ = _ := by
        simp only [map_add, map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.alg_C, hπφX, zero_mul, add_zero]
  obtain ⟨g1, hg1⟩ := (PowerSeries.X_dvd_iff).mpr h0
  have hg1χ : constantCoeff g1 = χ := by
    rw [← h1, hg1]
    show constantCoeff g1 = coeff (0 + 1) (X * g1)
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  obtain ⟨t, ht⟩ := exists_eq_C_constantCoeff_add_X_mul g1
  obtain ⟨e, he⟩ := hsurj t
  have hπg1 : Ideal.Quotient.mk I g1 = Ideal.Quotient.mk I (C (χ + x₀ * e)) := by
    rw [ht, hg1χ]; simp only [map_add, map_mul, hπX, he]
  have hπg : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I (C (x₀ * (χ + x₀ * e))) := by
    rw [hg1, map_mul, hπg1, hπX]; simp only [map_mul]
  have hry : (1 + x₀ * (χ + x₀ * e)) ^ l = 1 := by
    have h4 : Ideal.Quotient.mk I (γ (φ₀ X)) = 0 := by
      rw [← hc X, hφπ, h0, map_zero, map_zero]
    have h5 : Ideal.Quotient.mk I (γ (φ₀ X))
        = Ideal.Quotient.mk I (C ((1 + x₀ * (χ + x₀ * e)) ^ l - 1)) := by
      rw [hφ₀]; simp only [map_sub, map_pow, map_add, map_one, hπg]
    have h6 := hinj ((1 + x₀ * (χ + x₀ * e)) ^ l - 1) 0 (by rw [← h5, h4, map_zero, map_zero])
    exact sub_eq_zero.mp h6
  have hχm : χ - 1 ∈ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hl hχ
  have hw : χ - 1 + x₀ * e ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.maximalIdeal O).add_mem hχm ((IsLocalRing.maximalIdeal O).mul_mem_right e hxm)
  have hyx : x₀ * (χ + x₀ * e) = x₀ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.root_eq l hx₀ hroot hry hw (by ring)
  have hχe : χ + x₀ * e = 1 := mul_left_cancel₀ hx₀ (by rw [hyx, mul_one])
  have hπg1' : Ideal.Quotient.mk I g1 = 1 := by rw [hπg1, hχe, map_one, map_one]
  have hπgX : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I X := by
    rw [hπg, hyx, hπX]
  have hγπ : ∀ f, Ideal.Quotient.mk I (γ f) = Ideal.Quotient.mk I f := by
    intro f
    exact (ringHom_eq_of_eq_on_C_X_of_pow_dvd_eq_zero (Ideal.Quotient.mk I) ((Ideal.Quotient.mk I).comp γ.toRingHom)
      (fun a => by
        show _ = Ideal.Quotient.mk I (γ (C a))
        rw [Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.alg_C])
      hπgX.symm hsep f).symm
  obtain ⟨Q0, hQ0c, hQ0⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.exists_GL_latBasis_of_isSplitEquiv (O := O) l
  have hQQ0 : Q = Q0 := mul_left_cancel₀ PowerSeries.X_ne_zero (hQ.trans hQ0)
  have hQne : Q ≠ 0 := by
    intro hQz
    have hl0 : ((l : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    apply hl0
    rw [← hQ0c, ← hQQ0, hQz, map_zero]
  have hγQ : γ (X * Q) = X * g1 * γ Q := by rw [map_mul, hg1]
  have hγQ' : γ (X * Q) = X * Q * φ₀ g1 := by
    rw [hQ, ← hφ₀, ← hc X, hg1, map_mul]
  have hg1Q : g1 * γ Q = Q * φ₀ g1 :=
    mul_left_cancel₀ PowerSeries.X_ne_zero (by linear_combination hγQ' - hγQ)
  have hkey : Q * (g1 * u * θ) = Q * (γ u * φ₀ g1) := by
    have e3 : γ (u * Q) = γ u * γ Q := map_mul _ _ _
    linear_combination (-g1) * hθ + g1 * e3 + γ u * hg1Q
  have hkey' : g1 * u * θ = γ u * φ₀ g1 := mul_left_cancel₀ hQne hkey
  have hk : Ideal.Quotient.mk I (g1 * u * θ) = Ideal.Quotient.mk I (γ u * φ₀ g1) := by
    rw [hkey']
  simp only [map_mul] at hk
  rw [hγπ, hφπ, hg1χ, hπg1', one_mul] at hk
  exact Ideal.Quotient.eq.mp ((hu.map (Ideal.Quotient.mk I)).mul_left_cancel hk)

end Formalism.MainNotions.N.FrobeniusPowerSeries
