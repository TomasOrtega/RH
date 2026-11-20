import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import GroundTheory.AutomorphicForms.HermitianBinaryValues
set_option maxSynthPendingDepth 1

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open GroundTheory.Automorphic GroundTheory.Global
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace

/- English proof (translation)
Establish `hd : ∀ r : K, r ^ 2 ≠ d`. Introduce `r hr`. Establish `hr0 : r ≠ 0` using `by rintro rfl; exact hd0 (by rw [← hr]; ring)`. Conclude with `h (sqNorm_of_eq_sq h2 hr.symm hr0 β)`. Establish `hN : ∀ x y : K, x ^ 2 - d * y ^ 2 = 0 → x = 0 ∧ y = 0`.

Introduce `x y hxy`. Establish `hy : y = 0`. Assume the negation of the conclusion as `hy`. Use `hd (x / y) ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Take the linear combination `hxy`. Substitute `hy` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Establish `: x ^ 2 = 0` using `by linear_combination hxy`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.1 this`.

Distinguish the cases in `hn : c ^ 2 - d * e ^ 2 = 0`. Take `⟨rfl, rfl⟩` from `hN c e hn`. Take `⟨rfl, rfl⟩` from `hN a b (by linear_combination hz)`. Conclude with `⟨rfl, rfl, rfl, rfl⟩`. It suffices to derive a contradiction.

Apply `h` to reduce the goal to its premises. Establish `hA : SqNorm d (a ^ 2 - d * b ^ 2)` using `⟨a, b, rfl⟩`. Establish `hB : SqNorm d (c ^ 2 - d * e ^ 2)` using `⟨c, e, rfl⟩`. Use `hA.mul hB.inv` as an intermediate fact. Establish `he : (a ^ 2 - d * b ^ 2) * (c ^ 2 - d * e ^ 2)⁻¹ = β`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hz`. Rewrite `this` using `[he]`. Then use the resulting hypothesis.
-/
theorem eq_zero_of_not_sqNorm {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {d β : K} (hd0 : d ≠ 0)
    (h : ¬ SqNorm d β) {a b c e : K}
    (hz : (a ^ 2 - d * b ^ 2) - β * (c ^ 2 - d * e ^ 2) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have hd : ∀ r : K, r ^ 2 ≠ d := by
    intro r hr
    have hr0 : r ≠ 0 := by rintro rfl; exact hd0 (by rw [← hr]; ring)
    exact h (sqNorm_of_eq_sq h2 hr.symm hr0 β)
  have hN : ∀ x y : K, x ^ 2 - d * y ^ 2 = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have hy : y = 0 := by
      by_contra hy
      refine hd (x / y) ?_
      field_simp
      linear_combination hxy
    subst hy
    refine ⟨?_, rfl⟩
    have : x ^ 2 = 0 := by linear_combination hxy
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  by_cases hn : c ^ 2 - d * e ^ 2 = 0
  · obtain ⟨rfl, rfl⟩ := hN c e hn
    obtain ⟨rfl, rfl⟩ := hN a b (by linear_combination hz)
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exfalso
    apply h
    have hA : SqNorm d (a ^ 2 - d * b ^ 2) := ⟨a, b, rfl⟩
    have hB : SqNorm d (c ^ 2 - d * e ^ 2) := ⟨c, e, rfl⟩
    have := hA.mul hB.inv
    have he : (a ^ 2 - d * b ^ 2) * (c ^ 2 - d * e ^ 2)⁻¹ = β := by
      field_simp
      linear_combination hz
    rwa [he] at this

/- English proof (translation)
Establish `h2 : (2 : K) ≠ 0`. Establish `: algebraMap F K 2 ≠ 0` using `(map_ne_zero _).2 two_ne_zero`. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Introduce `x hx`. Take `⟨h1, h3, h4, h5⟩` from `eq_zero_of_not_sqNorm h2 ((map_ne_zero (algebraMap F K)).2 hd0) h (a := x.re) (b := x.imI) (c := x.imJ) (e := x.imK) (by unfold qn at hx; linear_combination hx)`.

Apply the tactic sequence `ext <;> simp [h1, h3, h4, h5]`.
-/
theorem aniso_of_not_sqNorm {F : Type} [Field F] [CharZero F] {K : Type} [Field K] [Algebra F K]
    {d β : F} (hd0 : d ≠ 0) (h : ¬ SqNorm (algebraMap F K d) (algebraMap F K β)) :
    ∀ x : Q d β K, qn x = 0 → x = 0 := by
  have h2 : (2 : K) ≠ 0 := by
    have : algebraMap F K 2 ≠ 0 := (map_ne_zero _).2 two_ne_zero
    rwa [map_ofNat] at this
  intro x hx
  obtain ⟨h1, h3, h4, h5⟩ := eq_zero_of_not_sqNorm h2 ((map_ne_zero (algebraMap F K)).2 hd0) h
    (a := x.re) (b := x.imI) (c := x.imJ) (e := x.imK) (by unfold qn at hx; linear_combination hx)
  ext <;> simp [h1, h3, h4, h5]

/- English proof (translation)
Establish `hre` using `congrArg QuadraticAlgebra.re hxy`. Establish `him` using `congrArg QuadraticAlgebra.im hxy`. Simplify using `only [sq, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im] at hre him`. Use `set x0 := x.re`. Use `set x1 := x.im`.

Use `set y0 := y.re`. Use `set y1 := y.im`. Establish `hn : x1 ^ 2 - d * y1 ^ 2 ≠ 0`. Introduce `hn`. Conclude with `hβ ⟨x0, y0, by linear_combination hre + hn⟩`.

Use `set n := x1 ^ 2 - d * y1 ^ 2 with hndef`. Use `⟨⟨-(x0 * x1 - d * y0 * y1) / n, -(y0 * x1 - x0 * y1) / n, x1 / n, -y1 / n⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [qn, Algebra.algebraMap_self, RingHom.id_apply]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hndef]`.

Take the linear combination `(x1 ^ 2 - d * y1 ^ 2) * hre`. Simplify using `only`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hndef]`. Take the linear combination `-him`.
-/
theorem exists_qn_of_quadraticAlgebra {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {d β t : K}
    (hβ : ¬ SqNorm d β) {x y : QuadraticAlgebra K (-1) t}
    (hxy : x ^ 2 - algebraMap K _ d * y ^ 2 = algebraMap K _ β) :
    ∃ q : Q d β K, qn q = 1 ∧ 2 * q.re = t := by
  have hre := congrArg QuadraticAlgebra.re hxy
  have him := congrArg QuadraticAlgebra.im hxy
  simp only [sq, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
    at hre him
  set x0 := x.re
  set x1 := x.im
  set y0 := y.re
  set y1 := y.im
  have hn : x1 ^ 2 - d * y1 ^ 2 ≠ 0 := by
    intro hn
    exact hβ ⟨x0, y0, by linear_combination hre + hn⟩
  set n := x1 ^ 2 - d * y1 ^ 2 with hndef
  refine ⟨⟨-(x0 * x1 - d * y0 * y1) / n, -(y0 * x1 - x0 * y1) / n, x1 / n, -y1 / n⟩, ?_, ?_⟩
  · simp only [qn, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
    rw [hndef]
    linear_combination (x1 ^ 2 - d * y1 ^ 2) * hre
  · simp only
    field_simp
    rw [hndef]
    linear_combination -him

/- English proof (translation)
Establish `key : ∀ a b c e : F, a ^ 2 - d * b ^ 2 - β * c ^ 2 + d * β * e ^ 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0`. Introduce `a b c e h`. Use `hF ⟨a, b, c, e⟩ (by simpa [qn] using h)` as an intermediate fact. Conclude with `⟨congrArg QuaternionAlgebra.re this, congrArg QuaternionAlgebra.imI this, congrArg QuaternionAlgebra.imJ this, congrArg QuaternionAlgebra.imK this⟩`. Establish `hd0 : d ≠ 0` using `fun h => one_ne_zero (key 0 1 0 0 (by simp [h])).2.1`.

Establish `hβ0 : β ≠ 0` using `fun h => one_ne_zero (key 0 0 1 0 (by simp [h])).2.2.1`. Establish `hd : ∀ r : F, r ^ 2 ≠ d` using `fun r h => one_ne_zero (key r 1 0 0 (by rw [← h]; ring)).2.1`. Establish `hβd : ¬ SqNorm d β`. Introduce and unpack `⟨a, b, h⟩`. Conclude with `one_ne_zero (key a b 1 0 (by rw [← h]; ring)).2.2.1`.

Establish `ht1 : ∀ v : HeightOneSpectrum (𝓞 F), ¬ SqNorm (algebraMap F (v.adicCompletion F) d) (algebraMap F _ β) → ∀ r : v.adicCompletion F, r ^ 2 ≠ algebraMap F _ (t ^ 2 - 4 * 1)`. Introduce `v hv r`. Rewrite using `[mul_one]`. Conclude with `hl (Sum.inr v) (aniso_of_not_sqNorm (K := Kp (Sum.inr v : Pl F)) hd0 hv) r`. Establish `ht2 : ∀ w : InfinitePlace F, ¬ SqNorm (algebraMap F w.Completion d) (algebraMap F _ β) → ∀ r : w.Completion, r ^ 2 ≠ algebraMap F _ (t ^ 2 - 4 * 1)`.

Introduce `w hw r`. Rewrite using `[mul_one]`. Conclude with `hl (Sum.inl w) (aniso_of_not_sqNorm (K := Kp (Sum.inl w : Pl F)) hd0 hw) r`. Establish `hbad : (∃ v : HeightOneSpectrum (𝓞 F), ¬ SqNorm (algebraMap F (v.adicCompletion F) d) (algebraMap F _ β)) ∨ ∃ w : InfinitePlace F, ¬ SqNorm (algebraMap F w.Completion d) (algebraMap F _ β)`. Assume the negation of the conclusion as `H`.

Use `push Not at H`. Conclude with `hβd ((exists_sq_sub_mul_sq_iff_forall_local hd hβ0).2 ⟨H.1, H.2⟩)`. Establish `hnsq : ∀ r : F, r ^ 2 ≠ t ^ 2 - 4 * 1`. Introduce `r hr`. Break down `hbad with ⟨v, hv⟩ | ⟨w, hw⟩` into its components or cases.

Conclude with `ht1 v hv (algebraMap F _ r) (by rw [← map_pow, hr])`. Conclude with `ht2 w hw (algebraMap F _ r) (by rw [← map_pow, hr])`. Establish `hL : Fact (∀ r : F, r ^ 2 ≠ -1 + t * r)` using `⟨fun r hr => hnsq (2 * r - t) (by linear_combination 4 * hr)⟩`. Establish `hex : ∃ x y : QuadraticAlgebra F (-1) t, x ^ 2 - algebraMap F _ d * y ^ 2 = algebraMap F _ β`. Distinguish the cases in `hdL : ∃ r : QuadraticAlgebra F (-1) t, r ^ 2 = algebraMap F _ d`.

Take `⟨r, hr⟩` from `hdL`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Conclude with `(map_ne_zero (algebraMap F (QuadraticAlgebra F (-1) t))).2 hd0 (by rw [← hr]; ring)`. Conclude with `sqNorm_of_eq_sq two_ne_zero hr.symm hr0 _`.

Use `push Not at hdL`. Establish `hβL : algebraMap F (QuadraticAlgebra F (-1) t) β ≠ 0` using `(map_ne_zero _).2 hβ0`. Use `(exists_sq_sub_mul_sq_iff_forall_local hdL hβL).2 ⟨fun w => ?_, fun w => ?_⟩` and prove the remaining obligations. Use `sqNorm_finite_quadraticAlgebra (γ := 1) hd0 hβ0 w ?_` and prove the remaining obligations. Conclude with `(Classical.em _).imp_right (ht1 _)`.

Use `sqNorm_infinite_quadraticAlgebra (γ := 1) hd0 hβ0 w ?_` and prove the remaining obligations. Conclude with `(Classical.em _).imp_right (ht2 _)`. Take `⟨x, y, hxy⟩` from `hex`. Conclude with `exists_qn_of_quadraticAlgebra two_ne_zero hβd hxy`.
-/
theorem exists_qn_eq_one_two_mul_re {F : Type} [Field F] [NumberField F] (d β t : F)
    (hF : ∀ x : Q d β F, qn x = 0 → x = 0)
    (hl : ∀ u : Pl F, (∀ x : Q d β (Kp u), qn x = 0 → x = 0) →
      ∀ r : Kp u, r ^ 2 ≠ algebraMap F (Kp u) (t ^ 2 - 4)) :
    ∃ x : Q d β F, qn x = 1 ∧ 2 * x.re = t := by
  have key : ∀ a b c e : F, a ^ 2 - d * b ^ 2 - β * c ^ 2 + d * β * e ^ 2 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
    intro a b c e h
    have := hF ⟨a, b, c, e⟩ (by simpa [qn] using h)
    exact ⟨congrArg QuaternionAlgebra.re this, congrArg QuaternionAlgebra.imI this,
      congrArg QuaternionAlgebra.imJ this, congrArg QuaternionAlgebra.imK this⟩
  have hd0 : d ≠ 0 := fun h => one_ne_zero (key 0 1 0 0 (by simp [h])).2.1
  have hβ0 : β ≠ 0 := fun h => one_ne_zero (key 0 0 1 0 (by simp [h])).2.2.1
  have hd : ∀ r : F, r ^ 2 ≠ d := fun r h =>
    one_ne_zero (key r 1 0 0 (by rw [← h]; ring)).2.1
  have hβd : ¬ SqNorm d β := by
    rintro ⟨a, b, h⟩
    exact one_ne_zero (key a b 1 0 (by rw [← h]; ring)).2.2.1
  have ht1 : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ SqNorm (algebraMap F (v.adicCompletion F) d) (algebraMap F _ β) →
      ∀ r : v.adicCompletion F, r ^ 2 ≠ algebraMap F _ (t ^ 2 - 4 * 1) := by
    intro v hv r
    rw [mul_one]
    exact hl (Sum.inr v) (aniso_of_not_sqNorm (K := Kp (Sum.inr v : Pl F)) hd0 hv) r
  have ht2 : ∀ w : InfinitePlace F,
      ¬ SqNorm (algebraMap F w.Completion d) (algebraMap F _ β) →
      ∀ r : w.Completion, r ^ 2 ≠ algebraMap F _ (t ^ 2 - 4 * 1) := by
    intro w hw r
    rw [mul_one]
    exact hl (Sum.inl w) (aniso_of_not_sqNorm (K := Kp (Sum.inl w : Pl F)) hd0 hw) r
  have hbad : (∃ v : HeightOneSpectrum (𝓞 F),
        ¬ SqNorm (algebraMap F (v.adicCompletion F) d) (algebraMap F _ β)) ∨
      ∃ w : InfinitePlace F, ¬ SqNorm (algebraMap F w.Completion d) (algebraMap F _ β) := by
    by_contra H
    push Not at H
    exact hβd ((exists_sq_sub_mul_sq_iff_forall_local hd hβ0).2 ⟨H.1, H.2⟩)
  have hnsq : ∀ r : F, r ^ 2 ≠ t ^ 2 - 4 * 1 := by
    intro r hr
    rcases hbad with ⟨v, hv⟩ | ⟨w, hw⟩
    · exact ht1 v hv (algebraMap F _ r) (by rw [← map_pow, hr])
    · exact ht2 w hw (algebraMap F _ r) (by rw [← map_pow, hr])
  have hL : Fact (∀ r : F, r ^ 2 ≠ -1 + t * r) :=
    ⟨fun r hr => hnsq (2 * r - t) (by linear_combination 4 * hr)⟩
  have hex : ∃ x y : QuadraticAlgebra F (-1) t,
      x ^ 2 - algebraMap F _ d * y ^ 2 = algebraMap F _ β := by
    by_cases hdL : ∃ r : QuadraticAlgebra F (-1) t, r ^ 2 = algebraMap F _ d
    · obtain ⟨r, hr⟩ := hdL
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact (map_ne_zero (algebraMap F (QuadraticAlgebra F (-1) t))).2 hd0 (by rw [← hr]; ring)
      exact sqNorm_of_eq_sq two_ne_zero hr.symm hr0 _
    push Not at hdL
    have hβL : algebraMap F (QuadraticAlgebra F (-1) t) β ≠ 0 := (map_ne_zero _).2 hβ0
    refine (exists_sq_sub_mul_sq_iff_forall_local hdL hβL).2 ⟨fun w => ?_, fun w => ?_⟩
    · refine sqNorm_finite_quadraticAlgebra (γ := 1) hd0 hβ0 w ?_
      exact (Classical.em _).imp_right (ht1 _)
    · refine sqNorm_infinite_quadraticAlgebra (γ := 1) hd0 hβ0 w ?_
      exact (Classical.em _).imp_right (ht2 _)
  obtain ⟨x, y, hxy⟩ := hex
  exact exists_qn_of_quadraticAlgebra two_ne_zero hβd hxy

end GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace
