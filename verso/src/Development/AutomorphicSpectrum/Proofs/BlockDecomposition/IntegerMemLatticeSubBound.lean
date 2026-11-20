import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
open Polynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.LatOKElem

section Newton
variable {R : Type*} [CommRing R]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, e, by simp [hE]⟩`. Consider the case `succ n ih`. Take `⟨z, r, h⟩` from `ih`. Take `⟨z', hz'⟩` from `Polynomial.evalSubFactor E.derivative (a + T * y * z) a`.

Use `set h' := -(T * v * y ^ (n + 1) * r) with hh'`. Take `⟨k, hk⟩` from `Polynomial.binomExpansion E (a + T * y * z) h'`. Use `⟨z - v * y ^ n * r, -(z' * z * v * r) + k * v ^ 2 * y ^ n * r ^ 2, ?_⟩` and prove the remaining obligations. Establish `e1 : a + T * y * (z - v * y ^ n * r) = a + T * y * z + h'` using `by rw [hh']; ring`. Establish `e2 : E.derivative.eval (a + T * y * z) = E.derivative.eval a + z' * (T * y * z)`.

Take the linear combination `hz'`. Rewrite using `[e1, hk, h, e2, hh']`. Take the linear combination `(-(T * y ^ (n + 1) * r)) * hv`.
-/
theorem newton_step (E : R[X]) (a T y v e : R) (hv : E.derivative.eval a * v = T)
    (hE : E.eval a = T ^ 2 * y * e) (n : ℕ) :
    ∃ z r : R, E.eval (a + T * y * z) = T ^ 2 * y ^ (n + 1) * r := by
  induction n with
  | zero => exact ⟨0, e, by simp [hE]⟩
  | succ n ih =>
    obtain ⟨z, r, h⟩ := ih
    obtain ⟨z', hz'⟩ := Polynomial.evalSubFactor E.derivative (a + T * y * z) a
    set h' := -(T * v * y ^ (n + 1) * r) with hh'
    obtain ⟨k, hk⟩ := Polynomial.binomExpansion E (a + T * y * z) h'
    refine ⟨z - v * y ^ n * r, -(z' * z * v * r) + k * v ^ 2 * y ^ n * r ^ 2, ?_⟩
    have e1 : a + T * y * (z - v * y ^ n * r) = a + T * y * z + h' := by rw [hh']; ring
    have e2 : E.derivative.eval (a + T * y * z) = E.derivative.eval a + z' * (T * y * z) := by
      linear_combination hz'
    rw [e1, hk, h, e2, hh']
    linear_combination (-(T * y ^ (n + 1) * r)) * hv

/- English proof (translation)
Establish `hn : IsNilpotent (T * y * w)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, mul_pow, hy]`. Simplify using the standard rewrite rules. Take `⟨g, hg⟩` from `hn.isUnit_one_add.exists_right_inv`.

Take `⟨z, r, h⟩` from `newton_step E a T y (v * g) e (by rw [← mul_assoc, hv, mul_assoc, hg, mul_one]) hE m`. Establish `h0 : y ^ (m + 1) = 0` using `by rw [pow_succ, hy, zero_mul]`. Conclude with `⟨z, by rw [h, h0]; simp⟩`.
-/
theorem exists_root (E : R[X]) (a T y v e w : R) (m : ℕ) (hy : y ^ m = 0)
    (hv : E.derivative.eval a * v = T * (1 + T * y * w))
    (hE : E.eval a = T ^ 2 * y * e) :
    ∃ z : R, E.eval (a + T * y * z) = 0 := by
  have hn : IsNilpotent (T * y * w) := by
    refine ⟨m, ?_⟩
    rw [mul_pow, mul_pow, hy]; simp
  obtain ⟨g, hg⟩ := hn.isUnit_one_add.exists_right_inv
  obtain ⟨z, r, h⟩ := newton_step E a T y (v * g) e
    (by rw [← mul_assoc, hv, mul_assoc, hg, mul_one]) hE m
  have h0 : y ^ (m + 1) = 0 := by rw [pow_succ, hy, zero_mul]
  exact ⟨z, by rw [h, h0]; simp⟩

/- English proof (translation)
Establish `hδ : IsNilpotent (α - β)`. Use `(Commute.all (α - a) (-(β - a))).isNilpotent_add hαa hβa.neg` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, hk⟩` from `Polynomial.binomExpansion E β (α - β)`.

Take `⟨z, hz⟩` from `Polynomial.evalSubFactor E.derivative β a`. Establish `h0 : (α - β) * (E.derivative.eval a + (z * (β - a) + k * (α - β))) = 0`. Establish `e : β + (α - β) = α` using `by ring`. Rewrite `hk` using `[e, hα, hβ]`. Establish `e2 : E.derivative.eval β = E.derivative.eval a + z * (β - a)` using `by rw [← hz]; ring`.

Rewrite `hk` using `[e2]`. Take the linear combination `-hk`. Establish `hn : IsNilpotent (z * (β - a) + k * (α - β))` using `(Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_mul_left hβa) ((Commute.all _ _).isNilpotent_mul_left hδ)`. Establish `hU : IsUnit (E.derivative.eval a + (z * (β - a) + k * (α - β)))` using `hn.isUnit_add_left_of_commute hu (Commute.all _ _)`. Conclude with `sub_eq_zero.1 ((hU.mul_left_eq_zero).1 h0)`.
-/
theorem root_unique (E : R[X]) (a α β : R) (hα : E.eval α = 0) (hβ : E.eval β = 0)
    (hu : IsUnit (E.derivative.eval a)) (hαa : IsNilpotent (α - a)) (hβa : IsNilpotent (β - a)) :
    α = β := by
  have hδ : IsNilpotent (α - β) := by
    have := (Commute.all (α - a) (-(β - a))).isNilpotent_add hαa hβa.neg
    convert this using 1; ring
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion E β (α - β)
  obtain ⟨z, hz⟩ := Polynomial.evalSubFactor E.derivative β a
  have h0 : (α - β) * (E.derivative.eval a + (z * (β - a) + k * (α - β))) = 0 := by
    have e : β + (α - β) = α := by ring
    rw [e, hα, hβ] at hk
    have e2 : E.derivative.eval β = E.derivative.eval a + z * (β - a) := by rw [← hz]; ring
    rw [e2] at hk
    linear_combination -hk
  have hn : IsNilpotent (z * (β - a) + k * (α - β)) :=
    (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_mul_left hβa)
      ((Commute.all _ _).isNilpotent_mul_left hδ)
  have hU : IsUnit (E.derivative.eval a + (z * (β - a) + k * (α - β))) :=
    hn.isUnit_add_left_of_commute hu (Commute.all _ _)
  exact sub_eq_zero.1 ((hU.mul_left_eq_zero).1 h0)

end Newton

section Lattice
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)

/- English proof (translation)
Establish `hlq : (l : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hl`. Establish `e : ((l : ℚ) ^ (2 * c))⁻¹ • f ξ = (l : B) ^ (M - 2 * c) * dpE f ξ l M 1`. Establish `h1 : (l : B) = algebraMap ℚ B (l : ℚ)` using `(map_natCast _ l).symm`. Rewrite using `[dpE, η, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one, h1, ← map_pow, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]`. Use `congr 2`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hM`. Rewrite using `[Nat.add_sub_cancel_left, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `(sub f ξ l M).mul_mem ((sub f ξ l M).pow_mem (natCast_mem _ l) _) (Subring.subset_closure (Or.inr ⟨1, rfl⟩))`.
-/
theorem div_mem_sub (l M c : ℕ) (hl : l ≠ 0) (hM : 2 * c ≤ M) :
    ((l : ℚ) ^ (2 * c))⁻¹ • f ξ ∈ sub f ξ l M := by
  have hlq : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl
  have e : ((l : ℚ) ^ (2 * c))⁻¹ • f ξ = (l : B) ^ (M - 2 * c) * dpE f ξ l M 1 := by
    have h1 : (l : B) = algebraMap ℚ B (l : ℚ) := (map_natCast _ l).symm
    rw [dpE, η, Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one, h1, ← map_pow,
      Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
    congr 2
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  rw [e]
  exact (sub f ξ l M).mul_mem ((sub f ξ l M).pow_mem (natCast_mem _ l) _)
    (Subring.subset_closure (Or.inr ⟨1, rfl⟩))

/- English proof (translation)
Establish `hlq : (l : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hl`. Establish `hlB : IsUnit (l : B)`. Establish `h1 : (l : B) = algebraMap ℚ B (l : ℚ)` using `(map_natCast _ l).symm`. Rewrite using `[h1]`. Conclude with `(IsUnit.mk0 _ hlq).map _`.

Use `set y0 : B := ((l : ℚ) ^ (2 * c))⁻¹ • f ξ with hy0`. Establish `hTy : (l : B) ^ (2 * c) * y0 = f ξ`. Establish `h1 : (l : B) = algebraMap ℚ B (l : ℚ)` using `(map_natCast _ l).symm`. Rewrite using `[hy0, Algebra.smul_def, h1, ← map_pow, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hlq), map_one, one_mul]`. Establish `hym : y0 ^ m = 0` using `by rw [hy0, _root_.smul_pow, hnil, smul_zero]`.

Set `g : W →+* A f ξ l M` to `ofW f ξ l M`. Set `i : A f ξ l M →+* B` to `ι f ξ l M`. Establish `hi : Function.Injective i` using `ι_injective f ξ l M`. Establish `hig : ∀ x, i (g x) = f x` using `fun _ => rfl`. Set `yR : A f ξ l M` to `⟨y0, div_mem_sub f ξ l M c hl hM⟩`.

Establish `hiy : i yR = y0` using `rfl`. Establish `hξ' : g ξ = ((l : A f ξ l M) ^ c) ^ 2 * yR`. Apply `hi` to reduce the goal to its premises. Simplify using `only [map_mul, map_pow, map_natCast, hig, hiy]`. Rewrite using `[← pow_mul, mul_comm c 2, hTy]`.

Establish `heval : ∀ (P : W[X]) (x : W), (P.map g).eval (g x) = g (P.eval x)` using `fun P x => by`. Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_at_apply]`. Take `⟨z, hz⟩` from `exists_root (E.map g) (g a) ((l : A f ξ l M) ^ c) yR (g v) (g e) (g w) m (hi (by rw [map_pow, hiy, hym, map_zero])) (by`. Rewrite using `[Polynomial.derivative_map, heval, ← map_mul, huv, map_add, map_mul, map_pow, map_natCast, hξ']`. Use the proof step `ring)`.

Use the proof step `(by rw [heval, hEa, map_mul, hξ'])`. Use `set b : A f ξ l M := g a + (l : A f ξ l M) ^ c * yR * z with hb`. Establish `hmap : E.map f = (E.map g).map i` using `by rw [Polynomial.map_map]; rfl`. Establish `hβ : (E.map f).eval (i b) = 0`. Rewrite using `[hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hz, map_zero]`.

Establish `hu : IsUnit ((E.map f).derivative.eval (f a))`. Rewrite using `[Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]`. Establish `h1 : f (E.derivative.eval a) * f v = (l : B) ^ c + f ξ * f w`. Rewrite using `[← map_mul, huv, map_add, map_mul, map_pow, map_natCast]`. Establish `hn : IsNilpotent (f ξ * f w)` using `⟨m, by rw [mul_pow, hnil, zero_mul]⟩`.

Establish `h2 : IsUnit (f (E.derivative.eval a) * f v)`. Rewrite using `[h1]`. Conclude with `hn.isUnit_add_left_of_commute (hlB.pow c) (Commute.all _ _)`. Conclude with `isUnit_of_mul_isUnit_left h2`. Establish `hn1 : IsNilpotent (α - f a)`.

Take `⟨r, hr⟩` from `Ideal.mem_span_singleton.1 hαa`. Conclude with `⟨m, by rw [hr, mul_pow, hnil, zero_mul]⟩`. Establish `hn2 : IsNilpotent (i b - f a)`. Establish `e1 : i b - f a = y0 * ((l : B) ^ c * i z)`. Rewrite using `[hb, map_add, map_mul, map_mul, map_pow, map_natCast, hig, hiy]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨m, by rw [e1, mul_pow, hym, zero_mul]⟩`. Establish `hαb` using `root_unique (E.map f) (f a) α (i b) hα hβ hu hn1 hn2`. Rewrite using `[hαb]`. Conclude with `b.2`.
-/
theorem mem_sub_of_root (l M c m : ℕ) (hl : l ≠ 0) (hM : 2 * c ≤ M) (hnil : f ξ ^ m = 0)
    (E : W[X]) (a v w e : W) (α : B) (hα : (E.map f).eval α = 0)
    (hαa : α - f a ∈ Ideal.span {f ξ}) (hEa : E.eval a = ξ * e)
    (huv : E.derivative.eval a * v = (l : W) ^ c + ξ * w) : α ∈ sub f ξ l M := by
  have hlq : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hlB : IsUnit (l : B) := by
    have h1 : (l : B) = algebraMap ℚ B (l : ℚ) := (map_natCast _ l).symm
    rw [h1]; exact (IsUnit.mk0 _ hlq).map _
  set y0 : B := ((l : ℚ) ^ (2 * c))⁻¹ • f ξ with hy0
  have hTy : (l : B) ^ (2 * c) * y0 = f ξ := by
    have h1 : (l : B) = algebraMap ℚ B (l : ℚ) := (map_natCast _ l).symm
    rw [hy0, Algebra.smul_def, h1, ← map_pow, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ (pow_ne_zero _ hlq), map_one, one_mul]
  have hym : y0 ^ m = 0 := by rw [hy0, _root_.smul_pow, hnil, smul_zero]
  let g : W →+* A f ξ l M := ofW f ξ l M
  let i : A f ξ l M →+* B := ι f ξ l M
  have hi : Function.Injective i := ι_injective f ξ l M
  have hig : ∀ x, i (g x) = f x := fun _ => rfl
  let yR : A f ξ l M := ⟨y0, div_mem_sub f ξ l M c hl hM⟩
  have hiy : i yR = y0 := rfl
  have hξ' : g ξ = ((l : A f ξ l M) ^ c) ^ 2 * yR := by
    apply hi
    simp only [map_mul, map_pow, map_natCast, hig, hiy]
    rw [← pow_mul, mul_comm c 2, hTy]
  have heval : ∀ (P : W[X]) (x : W), (P.map g).eval (g x) = g (P.eval x) := fun P x => by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  obtain ⟨z, hz⟩ := exists_root (E.map g) (g a) ((l : A f ξ l M) ^ c) yR (g v) (g e) (g w) m
    (hi (by rw [map_pow, hiy, hym, map_zero]))
    (by
      rw [Polynomial.derivative_map, heval, ← map_mul, huv, map_add, map_mul, map_pow, map_natCast,
        hξ']
      ring)
    (by rw [heval, hEa, map_mul, hξ'])
  set b : A f ξ l M := g a + (l : A f ξ l M) ^ c * yR * z with hb
  have hmap : E.map f = (E.map g).map i := by rw [Polynomial.map_map]; rfl
  have hβ : (E.map f).eval (i b) = 0 := by
    rw [hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hz, map_zero]
  have hu : IsUnit ((E.map f).derivative.eval (f a)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    have h1 : f (E.derivative.eval a) * f v = (l : B) ^ c + f ξ * f w := by
      rw [← map_mul, huv, map_add, map_mul, map_pow, map_natCast]
    have hn : IsNilpotent (f ξ * f w) := ⟨m, by rw [mul_pow, hnil, zero_mul]⟩
    have h2 : IsUnit (f (E.derivative.eval a) * f v) := by
      rw [h1]; exact hn.isUnit_add_left_of_commute (hlB.pow c) (Commute.all _ _)
    exact isUnit_of_mul_isUnit_left h2
  have hn1 : IsNilpotent (α - f a) := by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 hαa
    exact ⟨m, by rw [hr, mul_pow, hnil, zero_mul]⟩
  have hn2 : IsNilpotent (i b - f a) := by
    have e1 : i b - f a = y0 * ((l : B) ^ c * i z) := by
      rw [hb, map_add, map_mul, map_mul, map_pow, map_natCast, hig, hiy]; ring
    exact ⟨m, by rw [e1, mul_pow, hym, zero_mul]⟩
  have hαb := root_unique (E.map f) (f a) α (i b) hα hβ hu hn1 hn2
  rw [hαb]
  exact b.2

end Lattice

section Concrete
variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] xa` using `Algebra.IsIntegral.isIntegral xa`. Establish `h` using `hx`. Rewrite `h` using `[← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)]`. Establish `hl : minpoly ℚ_[l] xa ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p` using `l)) := by`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`.

Introduce `n`. Conclude with `⟨⟨_, h n⟩, rfl⟩`. Take `⟨E₀, hE⟩` from `(Polynomial.mem_lifts _).1 hl`. Use `⟨E₀, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hE]`.

Conclude with `minpoly.aeval _ _`. Rewrite using `[hE]`. Conclude with `Polynomial.Separable.aeval_derivative_ne_zero (minpoly.irreducible hi).separable (minpoly.aeval _ _)`.
-/
theorem exists_poly (xa : PadicAlgCl l) (hx : ‖xa‖ ≤ 1) :
    ∃ E₀ : ℤ_[l][X], aeval xa (E₀.map (PadicInt.Coe.ringHom (p := l))) = 0 ∧
      aeval xa (E₀.map (PadicInt.Coe.ringHom (p := l))).derivative ≠ 0 := by
  have hi : IsIntegral ℚ_[l] xa := Algebra.IsIntegral.isIntegral xa
  have h := hx
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] xa ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := l)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨E₀, hE⟩ := (Polynomial.mem_lifts _).1 hl
  refine ⟨E₀, ?_, ?_⟩
  · rw [hE]; exact minpoly.aeval _ _
  · rw [hE]
    exact Polynomial.Separable.aeval_derivative_ne_zero (minpoly.irreducible hi).separable
      (minpoly.aeval _ _)

/- English proof (translation)
Set `ρ : Ainf l →+* ℂ_[l]` to `(normInteger ℂ_[l]).subtype.comp (theta0 l)`. Establish `ha' : ρ a = algebraMap (PadicAlgCl l) ℂ_[l] xa` using `ha`. Establish `hA : aeval xa (E₀.map (PadicInt.Coe.ringHom (p` using `l))) = eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (PadicInt.Coe.ringHom (p := l))) xa E₀ := by`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`. Rewrite using `[hA]`.

Express the relevant statement in the definitionally equal form `ρ _ = algebraMap (PadicAlgCl l) ℂ_[l] _`. Rewrite using `[Polynomial.eval_map, Polynomial.hom_eval₂, ha', Polynomial.hom_eval₂]`. Use `congr 1`. Use extensionality with `q`. Conclude with `fontaineTheta_padicIntToWitt l q`.
-/
theorem theta_eval (E₀ : ℤ_[l][X]) (a : Ainf l) (xa : PadicAlgCl l)
    (ha : ((theta0 l a : OC l) : ℂ_[l]) = (xa : ℂ_[l])) :
    ((theta0 l ((E₀.map (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l)).eval a) : OC l) : ℂ_[l]) =
      ((aeval xa (E₀.map (PadicInt.Coe.ringHom (p := l))) : PadicAlgCl l) : ℂ_[l]) := by
  let ρ : Ainf l →+* ℂ_[l] := (normInteger ℂ_[l]).subtype.comp (theta0 l)
  have ha' : ρ a = algebraMap (PadicAlgCl l) ℂ_[l] xa := ha
  have hA : aeval xa (E₀.map (PadicInt.Coe.ringHom (p := l))) =
      eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (PadicInt.Coe.ringHom (p := l))) xa E₀ := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [hA]
  change ρ _ = algebraMap (PadicAlgCl l) ℂ_[l] _
  rw [Polynomial.eval_map, Polynomial.hom_eval₂, ha', Polynomial.hom_eval₂]
  congr 1
  ext q
  exact fontaineTheta_padicIntToWitt l q

/- English proof (translation)
Rewrite using `[← Polynomial.aeval_algHom_apply, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.map_map, Polynomial.eval_map]`. Use `congr 1`. Use extensionality with `q`. Conclude with `(IsPerfectoidField.algebraMap_padic_coe l q).symm`.
-/
theorem bdr_eval (E₀ : ℤ_[l][X]) (xa : PadicAlgCl l) :
    ((E₀.map (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l)).map
      (wittToBDeRhamPlus (normInteger ℂ_[l]) l)).eval (algClToBdR l xa) =
      algClToBdR l (aeval xa (E₀.map (PadicInt.Coe.ringHom (p := l)))) := by
  rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def, Polynomial.eval₂_map,
    Polynomial.map_map, Polynomial.eval_map]
  congr 1
  ext q
  exact (IsPerfectoidField.algebraMap_padic_coe l q).symm

/- English proof (translation)
Take `⟨E₀, h0, h1⟩` from `exists_poly l xa hx`. Establish `hmem : (xa : ℂ_[l]) ∈ normInteger ℂ_[l]`. Rewrite using `[mem_normInteger, PadicComplex.norm_extends]`. Conclude with `hx`. Take `⟨a, ha⟩` from `IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l ⟨_, hmem⟩`.

Establish `ha' : ((theta0 l a : OC l) : ℂ_[l]) = (xa : ℂ_[l])` using `congrArg Subtype.val ha`. Use `set E := E₀.map (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l) with hE`. Establish `hker : E.eval a ∈ RingHom.ker (theta0 l)`. Rewrite using `[RingHom.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hE, theta_eval l E₀ a xa ha', h0]`. Both sides reduce to the same expression. Rewrite `hker` using `[ker_theta0]`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton.1 hker`. Establish `hd : ((theta0 l (E.derivative.eval a) : OC l) : ℂ_[l]) = ((aeval xa (E₀.map (PadicInt.Coe.ringHom (p` using `l))).derivative : PadicAlgCl l) : ℂ_[l]) := by`.

Rewrite using `[hE, Polynomial.derivative_map, theta_eval l _ a xa ha', Polynomial.derivative_map]`. Establish `hs : ((theta0 l (E.derivative.eval a) : OC l) : ℂ_[l]) ≠ 0`. Rewrite using `[hd]`. Introduce `h`. Apply `h1` to reduce the goal to its premises.

Establish `h2` using `congrArg norm h`. Rewrite `h2` using `[PadicComplex.norm_extends, norm_zero]`. Conclude with `norm_eq_zero.1 h2`. Establish `hl1 : ‖(l : ℂ_[l])‖ < 1`. Establish `h2 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l])` using `(map_natCast _ l).symm`.

Rewrite using `[h2, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`. Take `⟨c, hc⟩` from `exists_pow_lt_of_lt_one (norm_pos_iff.2 hs) hl1`. Use `set s : ℂ_[l] := ((theta0 l (E.derivative.eval a) : OC l) : ℂ_[l]) with hsdef`. Establish `hmem2 : (l : ℂ_[l]) ^ c / s ∈ normInteger ℂ_[l]`.

Rewrite using `[mem_normInteger, norm_div, norm_pow]`. Conclude with `(div_lt_one (norm_pos_iff.2 hs)).2 hc |>.le`. Take `⟨v, hv⟩` from `IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l ⟨_, hmem2⟩`. Establish `hv' : ((theta0 l v : OC l) : ℂ_[l]) = (l : ℂ_[l]) ^ c / s` using `congrArg Subtype.val hv`. Establish `hker2 : E.derivative.eval a * v - (l : Ainf l) ^ c ∈ RingHom.ker (theta0 l)`.

Rewrite using `[RingHom.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h3 : ((theta0 l (E.derivative.eval a * v - (l : Ainf l) ^ c) : OC l) : ℂ_[l]) = s * ((theta0 l v : OC l) : ℂ_[l]) - (l : ℂ_[l]) ^ c`. Rewrite using `[map_sub, map_mul, map_pow, map_natCast]`. Simplify using `[hsdef]`.

Rewrite using `[h3, hv', mul_div_cancel₀ _ hs, sub_self]`. Both sides reduce to the same expression. Rewrite `hker2` using `[ker_theta0]`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton.1 hker2`. Conclude with `⟨E₀, a, v, w, e, c, h0, ha', he, by rw [← hw]; ring⟩`.
-/
theorem exists_data (xa : PadicAlgCl l) (hx : ‖xa‖ ≤ 1) :
    ∃ (E₀ : ℤ_[l][X]) (a v w e : Ainf l) (c : ℕ),
      aeval xa (E₀.map (PadicInt.Coe.ringHom (p := l))) = 0 ∧
      ((theta0 l a : OC l) : ℂ_[l]) = (xa : ℂ_[l]) ∧
      (E₀.map (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l)).eval a = xi0 l * e ∧
      (E₀.map (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l)).derivative.eval a * v =
        (l : Ainf l) ^ c + xi0 l * w := by
  obtain ⟨E₀, h0, h1⟩ := exists_poly l xa hx
  have hmem : (xa : ℂ_[l]) ∈ normInteger ℂ_[l] := by
    rw [mem_normInteger, PadicComplex.norm_extends]; exact hx
  obtain ⟨a, ha⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l ⟨_, hmem⟩
  have ha' : ((theta0 l a : OC l) : ℂ_[l]) = (xa : ℂ_[l]) := congrArg Subtype.val ha
  set E := E₀.map (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l) with hE

  have hker : E.eval a ∈ RingHom.ker (theta0 l) := by
    rw [RingHom.mem_ker]
    apply Subtype.ext
    rw [hE, theta_eval l E₀ a xa ha', h0]
    rfl
  rw [ker_theta0] at hker
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.1 hker

  have hd : ((theta0 l (E.derivative.eval a) : OC l) : ℂ_[l]) =
      ((aeval xa (E₀.map (PadicInt.Coe.ringHom (p := l))).derivative : PadicAlgCl l) : ℂ_[l]) := by
    rw [hE, Polynomial.derivative_map, theta_eval l _ a xa ha', Polynomial.derivative_map]
  have hs : ((theta0 l (E.derivative.eval a) : OC l) : ℂ_[l]) ≠ 0 := by
    rw [hd]
    intro h
    apply h1
    have h2 := congrArg norm h
    rw [PadicComplex.norm_extends, norm_zero] at h2
    exact norm_eq_zero.1 h2
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have h2 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := (map_natCast _ l).symm
    rw [h2, norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨c, hc⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hs) hl1
  set s : ℂ_[l] := ((theta0 l (E.derivative.eval a) : OC l) : ℂ_[l]) with hsdef
  have hmem2 : (l : ℂ_[l]) ^ c / s ∈ normInteger ℂ_[l] := by
    rw [mem_normInteger, norm_div, norm_pow]
    exact (div_lt_one (norm_pos_iff.2 hs)).2 hc |>.le
  obtain ⟨v, hv⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l ⟨_, hmem2⟩
  have hv' : ((theta0 l v : OC l) : ℂ_[l]) = (l : ℂ_[l]) ^ c / s := congrArg Subtype.val hv
  have hker2 : E.derivative.eval a * v - (l : Ainf l) ^ c ∈ RingHom.ker (theta0 l) := by
    rw [RingHom.mem_ker]
    apply Subtype.ext
    have h3 : ((theta0 l (E.derivative.eval a * v - (l : Ainf l) ^ c) : OC l) : ℂ_[l]) =
        s * ((theta0 l v : OC l) : ℂ_[l]) - (l : ℂ_[l]) ^ c := by
      rw [map_sub, map_mul, map_pow, map_natCast]
      simp [hsdef]
    rw [h3, hv', mul_div_cancel₀ _ hs, sub_self]
    rfl
  rw [ker_theta0] at hker2
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 hker2
  exact ⟨E₀, a, v, w, e, c, h0, ha', he, by rw [← hw]; ring⟩

/- English proof (translation)
Establish `hξ` using `IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (ker_theta0 (l := l))`. Establish `h1 : wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l) ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l)`. Rewrite using `[hξ]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `h1` using `[maximalIdeal_eq_span_tBdR]`.

Take `⟨r, hr⟩` from `Ideal.mem_span_singleton.1 h1`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ _ ^ k = 0`. Rewrite using `[hr, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, mul_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem fk_xi_pow (k : ℕ) : fk l k (xi0 l) ^ k = 0 := by
  have hξ := IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (ker_theta0 (l := l))
  have h1 : wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l) ∈
      IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) := by
    rw [hξ]; exact Ideal.mem_span_singleton_self _
  rw [maximalIdeal_eq_span_tBdR] at h1
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 h1
  change Ideal.Quotient.mk _ _ ^ k = 0
  rw [hr, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, mul_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Establish `hξ` using `IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (ker_theta0 (l := l))`. Establish `h1 : algClToBdR l xa - wittToBDeRhamPlus (normInteger ℂ_[l]) l a ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l)`. Rewrite using `[IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker, map_sub, IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, ← thetaAlgHom_apply, thetaAlgHom_algClToBdR, ha, sub_self]`. Rewrite `h1` using `[hξ]`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton.1 h1`.

Use `Ideal.mem_span_singleton.2 ⟨pk l k r, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (pk l k) hr`. Rewrite `h2` using `[map_sub, map_mul]`. Then use the resulting hypothesis.
-/
theorem sub_mem_span (k : ℕ) (xa : PadicAlgCl l) (a : Ainf l)
    (ha : ((theta0 l a : OC l) : ℂ_[l]) = (xa : ℂ_[l])) :
    pk l k (algClToBdR l xa) - fk l k a ∈ Ideal.span {fk l k (xi0 l)} := by
  have hξ := IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (ker_theta0 (l := l))
  have h1 : algClToBdR l xa - wittToBDeRhamPlus (normInteger ℂ_[l]) l a ∈
      IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker, map_sub,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, ← thetaAlgHom_apply,
      thetaAlgHom_algClToBdR, ha, sub_self]
  rw [hξ] at h1
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 h1
  refine Ideal.mem_span_singleton.2 ⟨pk l k r, ?_⟩
  have h2 := congrArg (pk l k) hr
  rwa [map_sub, map_mul] at h2

end Concrete

/- English proof (translation)
Introduce `l _ K _ x`. Establish `hx : ‖((x : K) : PadicAlgCl l)‖ ≤ 1` using `mem_normInteger.1 x.2`. Take `⟨E₀, a, v, w, e, c, h0, ha, he, huv⟩` from `exists_data l _ hx`. Use `⟨c, fun M k hM => ?_⟩` and prove the remaining obligations. Use `mem_sub_of_root (fk l k) (xi0 l) l M c k (Fact.out : l.Prime).ne_zero hM (fk_xi_pow l k) _ a v w e _ ?_ (sub_mem_span l k _ a ha) he huv` and prove the remaining obligations.

Establish `h1 : kP l K (x : K) = algClToBdR l ((x : K) : PadicAlgCl l)` using `rfl`. Establish `h2 : fk l k = (pk l k).comp (wittToBDeRhamPlus (normInteger ℂ_[l]) l)` using `rfl`. Rewrite using `[h1, h2, ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply, bdr_eval, h0, map_zero, map_zero]`.
-/
theorem ok_mem_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] K], ∀ x : OK l K, ∃ c : ℕ, ∀ M k : ℕ, 2 * c ≤ M →
      Lat.pk l k (Lat.kP l K x) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K _ x
  have hx : ‖((x : K) : PadicAlgCl l)‖ ≤ 1 := mem_normInteger.1 x.2
  obtain ⟨E₀, a, v, w, e, c, h0, ha, he, huv⟩ := exists_data l _ hx
  refine ⟨c, fun M k hM => ?_⟩
  refine mem_sub_of_root (fk l k) (xi0 l) l M c k (Fact.out : l.Prime).ne_zero hM (fk_xi_pow l k)
    _ a v w e _ ?_ (sub_mem_span l k _ a ha) he huv
  have h1 : kP l K (x : K) = algClToBdR l ((x : K) : PadicAlgCl l) := rfl
  have h2 : fk l k = (pk l k).comp (wittToBDeRhamPlus (normInteger ℂ_[l]) l) := rfl
  rw [h1, h2, ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply, bdr_eval, h0,
    map_zero, map_zero]

end GlobalTheory.CompanionTheory.LatOKElem
