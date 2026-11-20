import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.IsUnitaryK

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Use `first`. Consider the case `exact norm_algebraMap' ℂ_[l] x`. Consider the case `(rw [← PadicAlgCl.norm_extends l x, ← PadicComplex.norm_extends l]; rfl)`. Consider the case `(rw [IsScalarTower.algebraMap_apply ℚ_[l] (PadicAlgCl l) ℂ_[l], ← PadicAlgCl.norm_extends l x, ← PadicComplex.norm_extends l]; rfl)`.
-/
private theorem norm_alg_lemma (x : ℚ_[l]) : ‖algebraMap ℚ_[l] ℂ_[l] x‖ = ‖x‖ := by
  first
  | exact norm_algebraMap' ℂ_[l] x
  | (rw [← PadicAlgCl.norm_extends l x, ← PadicComplex.norm_extends l]; rfl)
  | (rw [IsScalarTower.algebraMap_apply ℚ_[l] (PadicAlgCl l) ℂ_[l], ← PadicAlgCl.norm_extends l x,
        ← PadicComplex.norm_extends l]; rfl)

/- English proof (translation)
The claim follows from `(AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] ℂ_[l]) (norm_alg_lemma l)).continuous`.
-/
private theorem cont_alg_lemma_2 : Continuous (algebraMap ℚ_[l] ℂ_[l]) :=
  (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] ℂ_[l]) (norm_alg_lemma l)).continuous

/- English proof (translation)
Rewrite using `[← hS.closure_eq, Metric.mem_closure_iff]`. Introduce `ε hε`. Take `⟨r, hr⟩` from `Padic.rat_dense l x hε`. Conclude with `⟨r, hq r, by rw [dist_eq_norm]; exact hr⟩`.
-/
private theorem closed_rat_lemma_3 (S : Set ℚ_[l]) (hS : IsClosed S) (hq : ∀ r : ℚ, (r : ℚ_[l]) ∈ S)
    (x : ℚ_[l]) : x ∈ S := by
  rw [← hS.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := Padic.rat_dense l x hε
  exact ⟨r, hq r, by rw [dist_eq_norm]; exact hr⟩

/- English proof (translation)
Establish `hK : IsClosed (MaximalUnramifiedExtension l : Set ℂ_[l])` using `by first`. Consider the case `exact Subfield.isClosed_topologicalClosure _`. Consider the case `exact isClosed_closure`. Use `closed_rat_lemma_3 l {y | algebraMap ℚ_[l] ℂ_[l] y ∈ MaximalUnramifiedExtension l} (hK.preimage (cont_alg_lemma_2 l)) ?_ x` and prove the remaining obligations. Introduce `r`.

Use `show algebraMap ℚ_[l] ℂ_[l] (r : ℚ_[l]) ∈ MaximalUnramifiedExtension l`. Rewrite using `[map_ratCast]`. Use `first`. Consider the case `exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) r`. Consider the case `exact (MaximalUnramifiedExtension l).ratCast_mem r`.
-/
theorem algebraMap_mem_Kur (x : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] x ∈ MaximalUnramifiedExtension l := by
  have hK : IsClosed (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    first
    | exact Subfield.isClosed_topologicalClosure _
    | exact isClosed_closure
  refine closed_rat_lemma_3 l {y | algebraMap ℚ_[l] ℂ_[l] y ∈ MaximalUnramifiedExtension l} (hK.preimage (cont_alg_lemma_2 l)) ?_ x
  intro r
  show algebraMap ℚ_[l] ℂ_[l] (r : ℚ_[l]) ∈ MaximalUnramifiedExtension l
  rw [map_ratCast]
  first
  | exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) r
  | exact (MaximalUnramifiedExtension l).ratCast_mem r

def φ : ℚ_[l] →+* MaximalUnramifiedExtension l := (algebraMap ℚ_[l] ℂ_[l]).codRestrict (MaximalUnramifiedExtension l) (algebraMap_mem_Kur l)

def ψ : ℤ_[l] →+* MaximalUnramifiedExtension l := (φ l).comp PadicInt.Coe.ringHom

/- English proof (translation)
Conclude with `norm_alg_lemma l x`.
-/
theorem norm_φ (x : ℚ_[l]) : ‖φ l x‖ = ‖x‖ := by
  exact norm_alg_lemma l x

/- English proof (translation)
Conclude with `norm_φ l (x : ℚ_[l])`.
-/
theorem norm_ψ (x : ℤ_[l]) : ‖ψ l x‖ = ‖x‖ := by
  exact norm_φ l (x : ℚ_[l])

/- English proof (translation)
Rewrite using `[norm_ψ]`. Conclude with `x.norm_le_one`.
-/
theorem norm_ψ_le (x : ℤ_[l]) : ‖ψ l x‖ ≤ 1 := by
  rw [norm_ψ]
  exact x.norm_le_one

/- English proof (translation)
Conclude with `(AddMonoidHomClass.isometry_of_norm (φ l) (norm_φ l)).continuous`.
-/
theorem continuous_φ : Continuous (φ l) := by
  exact (AddMonoidHomClass.isometry_of_norm (φ l) (norm_φ l)).continuous

/- English proof (translation)
Establish `hσc : Continuous σ` using `(AddMonoidHomClass.isometry_of_norm σ hσ).continuous`. Use `closed_rat_lemma_3 l {y | σ (φ l y) = φ l y} (isClosed_eq (hσc.comp (continuous_φ l)) (continuous_φ l)) ?_ x` and prove the remaining obligations. Introduce `r`. Use `show σ (φ l (r : ℚ_[l])) = φ l (r : ℚ_[l])`. Rewrite using `[map_ratCast, map_ratCast]`.
-/
theorem σ_φ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : ℚ_[l]) : σ (φ l x) = φ l x := by
  have hσc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
  refine closed_rat_lemma_3 l {y | σ (φ l y) = φ l y}
    (isClosed_eq (hσc.comp (continuous_φ l)) (continuous_φ l)) ?_ x
  intro r
  show σ (φ l (r : ℚ_[l])) = φ l (r : ℚ_[l])
  rw [map_ratCast, map_ratCast]

/- English proof (translation)
Conclude with `σ_φ l σ hσ (x : ℚ_[l])`.
-/
theorem σ_ψ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : ℤ_[l]) : σ (ψ l x) = ψ l x := by
  exact σ_φ l σ hσ (x : ℚ_[l])

/- English proof (translation)
Rewrite using `[← map_natCast (φ l) k, norm_φ]`.
-/
theorem norm_natCast_Kur (k : ℕ) : ‖(k : MaximalUnramifiedExtension l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [← map_natCast (φ l) k, norm_φ]

/- English proof (translation)
Rewrite using `[norm_natCast_Kur, Padic.norm_p]`.
-/
theorem norm_l_Kur : ‖(l : MaximalUnramifiedExtension l)‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Kur, Padic.norm_p]

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod]`. Use `first`. Consider the case `rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]`. Consider the case `rw [LocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]`.
-/
theorem toZMod_eq_zero_iff (z : ℤ_[l]) : PadicInt.toZMod z = 0 ↔ ‖z‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  first
  | rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  | rw [LocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

/- English proof (translation)
Rewrite using `[Ne, toZMod_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h h'`. Rewrite `h'` using `[h]`. Conclude with `lt_irrefl _ h'`.

Introduce `h`. Conclude with `le_antisymm z.norm_le_one (not_lt.1 h)`.
-/
theorem norm_eq_one_iff (z : ℤ_[l]) : ‖z‖ = 1 ↔ PadicInt.toZMod z ≠ 0 := by
  rw [Ne, toZMod_eq_zero_iff]
  constructor
  · intro h h'
    rw [h] at h'
    exact lt_irrefl _ h'
  · intro h
    exact le_antisymm z.norm_le_one (not_lt.1 h)

/- English proof (translation)
Conclude with `map_natCast PadicInt.toZMod k`.
-/
theorem toZMod_natCast (k : ℕ) : PadicInt.toZMod (k : ℤ_[l]) = (k : ZMod l) := by
  exact map_natCast PadicInt.toZMod k

/- English proof (translation)
Introduce `h`. Establish `h2 : ((2 : ℕ) : ZMod l) = 0` using `by exact_mod_cast h`. Rewrite `h2` using `[CharP.cast_eq_zero_iff (ZMod l) l]`. Use `Nat.le_of_dvd (by norm_num) h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem odd_l (h5 : 5 ≤ l) : (2 : ZMod l) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod l) l] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/- English proof (translation)
Use `haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩`. Take `⟨a, ha⟩ : ∃ a : ℤ_[l], PadicInt.toZMod a = s` from `⟨(s.val : ℤ_[l]), by rw [toZMod_natCast, ZMod.natCast_zmod_val]⟩`. Use `set F : Polynomial ℤ_[l] := Polynomial.X ^ 2 - Polynomial.C t with hF`. Establish `h1 : Polynomial.aeval a F = a ^ 2 - t` using `by simp [hF]`. Establish `h2 : Polynomial.aeval a (Polynomial.derivative F) = 2 * a` using `by first`.

Consider the case `(norm_num [hF]; done)`. Consider the case `(simp [hF]; left; norm_num; done)`. Consider the case `(simp [hF]; left; rfl)`. Consider the case `(simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X, map_natCast]; norm_num)`. Establish `n1 : ‖a ^ 2 - t‖ < 1`.

Rewrite using `[← toZMod_eq_zero_iff l, map_sub, map_pow, ha, ht, sub_self]`. Establish `n2 : ‖(2 : ℤ_[l]) * a‖ = 1`. Rewrite using `[norm_eq_one_iff l, map_mul, map_ofNat, ha]`. Conclude with `mul_ne_zero (odd_l l h5) hs`. Take `⟨z, hz, -⟩` from `hensels_lemma (F := F) (a := a) (by rw [h1, h2, n2, one_pow]; exact n1)`.

Establish `hz2 : z ^ 2 = t`. Establish `: z ^ 2 - t = 0` using `by simpa [hF] using hz`. Conclude with `sub_eq_zero.1 this`. Conclude with `⟨z, by rw [← sq]; exact hz2⟩`.
-/
theorem exists_sqrt (h5 : 5 ≤ l) (t : ℤ_[l]) (s : ZMod l) (hs : s ≠ 0) (ht : PadicInt.toZMod t = s ^ 2) :
    ∃ z : ℤ_[l], z * z = t := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], PadicInt.toZMod a = s :=
    ⟨(s.val : ℤ_[l]), by rw [toZMod_natCast, ZMod.natCast_zmod_val]⟩
  set F : Polynomial ℤ_[l] := Polynomial.X ^ 2 - Polynomial.C t with hF
  have h1 : Polynomial.aeval a F = a ^ 2 - t := by simp [hF]
  have h2 : Polynomial.aeval a (Polynomial.derivative F) = 2 * a := by
    first
    | (norm_num [hF]; done)
    | (simp [hF]; left; norm_num; done)
    | (simp [hF]; left; rfl)
    | (simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        sub_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X, map_natCast]; norm_num)
  have n1 : ‖a ^ 2 - t‖ < 1 := by
    rw [← toZMod_eq_zero_iff l, map_sub, map_pow, ha, ht, sub_self]
  have n2 : ‖(2 : ℤ_[l]) * a‖ = 1 := by
    rw [norm_eq_one_iff l, map_mul, map_ofNat, ha]
    exact mul_ne_zero (odd_l l h5) hs
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h1, h2, n2, one_pow]; exact n1)
  have hz2 : z ^ 2 = t := by
    have : z ^ 2 - t = 0 := by simpa [hF] using hz
    exact sub_eq_zero.1 this
  exact ⟨z, by rw [← sq]; exact hz2⟩

/- English proof (translation)
Use `haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩`. Establish `hd : ((dK : ℕ) : ZMod l) ≠ 0`. Rewrite using `[Ne, CharP.cast_eq_zero_iff (ZMod l) l]` and apply the resulting hypothesis. Establish `hA : PadicInt.toZMod a ≠ 0` using `(norm_eq_one_iff l a).1 ha`. Choose the witnesses or unpack the hypotheses as in `⟨x0, y0, hxy⟩ : ∃ x0 y0 : ZMod l, x0 ^ 2 + (dK : ZMod l) * y0 ^ 2 = PadicInt.toZMod a := by`.

Establish `hR : Fintype.card (ZMod l) % 2 = 1`. Rewrite using `[ZMod.card]`. Conclude with `Nat.odd_iff.1 ((Fact.out : l.Prime).odd_of_ne_two (by omega))`. Establish `h2 : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2).degree = 2` using `Polynomial.degree_C_mul_X_pow 2 hd`. Establish `hg : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2 - Polynomial.C (PadicInt.toZMod a)).degree = 2`.

Apply the tactic sequence `rw [Polynomial.degree_sub_C (by rw [h2]; first | decide | norm_num | exact WithBot.coe_lt_coe.2 (by norm_num)), h2]`. Take `⟨x0, y0, h⟩` from `FiniteField.exists_root_sum_quadratic (f := Polynomial.X ^ 2) (g := Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2 - Polynomial.C (PadicInt.toZMod a)) (Polynomial.degree_X_pow 2) hg hR`. Use `⟨x0, y0, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at h`. Take the linear combination `h`.

Distinguish the cases in `hx0 : x0 = 0`. Substitute `hx0` using the available equality. Establish `hy0 : y0 ≠ 0`. Introduce and unpack `rfl`. Apply `hA` to reduce the goal to its premises.

Rewrite using `[← hxy]`. Simplify using the standard rewrite rules. Take `⟨w, hw⟩` from `exists_sqrt l h5 ((dK : ℤ_[l]) * a) ((dK : ZMod l) * y0) (mul_ne_zero hd hy0) (by`. Rewrite using `[map_mul, toZMod_natCast]`. Take the linear combination `(-(dK : ZMod l)) * hxy)`.

Establish `hdu : IsUnit (dK : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, norm_eq_one_iff l, toZMod_natCast]`. Conclude with `hd`. Take `⟨u, hu⟩` from `hdu`. Establish `key : (u : ℤ_[l]) * ↑u⁻¹ = 1` using `u.mul_inv`.

Rewrite `hw` using `[← hu]`. Use `⟨0, ↑u⁻¹ * w, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu]`. Take the linear combination `((u : ℤ_[l]) * ↑u⁻¹ * ↑u⁻¹) * hw + ((u : ℤ_[l]) * ↑u⁻¹ + 1) * a * key`. Take `⟨x, hx⟩` from `exists_sqrt l h5 (a - dK * ((y0.val : ℤ_[l]) * (y0.val : ℤ_[l]))) x0 hx0 (by`.

Rewrite using `[map_sub, map_mul, map_mul, toZMod_natCast, toZMod_natCast, ZMod.natCast_zmod_val]`. Take the linear combination `-hxy)`. Conclude with `⟨x, y0.val, by rw [hx]; ring⟩`.
-/
theorem exists_norm (h5 : 5 ≤ l) (dK : ℕ) (hld : ¬ l ∣ dK) (a : ℤ_[l]) (ha : ‖a‖ = 1) :
    ∃ x y : ℤ_[l], x * x + dK * (y * y) = a := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hd : ((dK : ℕ) : ZMod l) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff (ZMod l) l]
  have hA : PadicInt.toZMod a ≠ 0 := (norm_eq_one_iff l a).1 ha
  obtain ⟨x0, y0, hxy⟩ : ∃ x0 y0 : ZMod l, x0 ^ 2 + (dK : ZMod l) * y0 ^ 2 = PadicInt.toZMod a := by
    have hR : Fintype.card (ZMod l) % 2 = 1 := by
      rw [ZMod.card]
      exact Nat.odd_iff.1 ((Fact.out : l.Prime).odd_of_ne_two (by omega))
    have h2 : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2).degree = 2 :=
      Polynomial.degree_C_mul_X_pow 2 hd
    have hg : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2
        - Polynomial.C (PadicInt.toZMod a)).degree = 2 := by
      rw [Polynomial.degree_sub_C (by rw [h2]; first | decide | norm_num | exact WithBot.coe_lt_coe.2 (by norm_num)), h2]
    obtain ⟨x0, y0, h⟩ := FiniteField.exists_root_sum_quadratic (f := Polynomial.X ^ 2)
      (g := Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2 - Polynomial.C (PadicInt.toZMod a))
      (Polynomial.degree_X_pow 2) hg hR
    refine ⟨x0, y0, ?_⟩
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at h
    linear_combination h
  by_cases hx0 : x0 = 0
  · subst hx0
    have hy0 : y0 ≠ 0 := by
      rintro rfl
      apply hA
      rw [← hxy]
      simp

    obtain ⟨w, hw⟩ := exists_sqrt l h5 ((dK : ℤ_[l]) * a) ((dK : ZMod l) * y0) (mul_ne_zero hd hy0)
      (by
        rw [map_mul, toZMod_natCast]
        linear_combination (-(dK : ZMod l)) * hxy)
    have hdu : IsUnit (dK : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, norm_eq_one_iff l, toZMod_natCast]
      exact hd
    obtain ⟨u, hu⟩ := hdu
    have key : (u : ℤ_[l]) * ↑u⁻¹ = 1 := u.mul_inv
    rw [← hu] at hw
    refine ⟨0, ↑u⁻¹ * w, ?_⟩
    rw [← hu]
    linear_combination ((u : ℤ_[l]) * ↑u⁻¹ * ↑u⁻¹) * hw + ((u : ℤ_[l]) * ↑u⁻¹ + 1) * a * key
  ·
    obtain ⟨x, hx⟩ := exists_sqrt l h5 (a - dK * ((y0.val : ℤ_[l]) * (y0.val : ℤ_[l]))) x0 hx0
      (by
        rw [map_sub, map_mul, map_mul, toZMod_natCast, toZMod_natCast, ZMod.natCast_zmod_val]
        linear_combination -hxy)
    exact ⟨x, y0.val, by rw [hx]; ring⟩

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
