import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter fwdDiff
open scoped Pointwise

noncomputable section

namespace VeroneseGenDeg

/- English proof (translation)
Establish `hs : {d : Fin (D + 1) →₀ ℕ | d.degree = n} = ((Finset.univ.finsuppAntidiag n : Finset (Fin (D + 1) →₀ ℕ)) : Set (Fin (D + 1) →₀ ℕ))`. Use extensionality with `d`. Simplify using `[Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]`. Rewrite using `[MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hs, (AddMonoidAlgebra.supportedEquivFinsupp _).finrank_eq, Module.finrank_finsupp_self]`. Simplify using `only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]`.

Rewrite using `[show D + 1 + n - 1 = n + D by omega]`. Conclude with `Nat.choose_symm_add`.
-/
theorem finrank_homog (D n : ℕ) :
    Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ n) = (n + D).choose D := by
  have hs : {d : Fin (D + 1) →₀ ℕ | d.degree = n} =
      ((Finset.univ.finsuppAntidiag n : Finset (Fin (D + 1) →₀ ℕ)) : Set (Fin (D + 1) →₀ ℕ)) := by
    ext d; simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hs,
    (AddMonoidAlgebra.supportedEquivFinsupp _).finrank_eq, Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show D + 1 + n - 1 = n + D by omega]
  exact Nat.choose_symm_add

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[pow_two, Set.mem_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩`. Conclude with `⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩`.

Introduce and unpack `⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩`. Break down `le_total i j with hij | hij` into its components or cases. Conclude with `⟨⟨(), ⟨(i, j), hij⟩⟩, rfl⟩`. Conclude with `⟨⟨(), ⟨(j, i), hij⟩⟩, mul_comm _ _⟩`.
-/
theorem range_alt (D : ℕ) : Set.range (Veronese.x D) = Set.range (Veronese.t D) ^ 2 := by
  ext y
  rw [pow_two, Set.mem_mul]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    rcases le_total i j with hij | hij
    · exact ⟨⟨(), ⟨(i, j), hij⟩⟩, rfl⟩
    · exact ⟨⟨(), ⟨(j, i), hij⟩⟩, mul_comm _ _⟩

/- English proof (translation)
Establish `h : (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D).toRingHom = (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp (MvPolynomial.map (Int.castRingHom ℚ))`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[Veronese.t]`. Establish `hinj : Function.Injective ((algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp (MvPolynomial.map (Int.castRingHom ℚ)))` using `(IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp (MvPolynomial.map_injective _ (RingHom.injective_int _))`.

Rewrite `hinj` using `[← h]`. Conclude with `hinj`.
-/
theorem aeval_t_injective (D : ℕ) :
    Function.Injective (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D) := by
  have h : (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D).toRingHom =
      (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
        (MvPolynomial.map (Int.castRingHom ℚ)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp
    · simp [Veronese.t]
  have hinj : Function.Injective ((algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) :=
    (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
      (MvPolynomial.map_injective _ (RingHom.injective_int _))
  rw [← h] at hinj
  exact hinj

/- English proof (translation)
Establish `h1 : sec ℤ (Veronese.x D) n = sec ℤ (Veronese.t D) (2 * n)`. Rewrite using `[SectionsRank.sec_eq_span, SectionsRank.sec_eq_span, range_alt, ← pow_mul]`. Rewrite using `[h1, ← finrank_homog D (2 * n)]`. Conclude with `(Submodule.equivMapOfInjective _ (aeval_t_injective D) _).finrank_eq.symm`.
-/
theorem finrank_sec (D n : ℕ) :
    Module.finrank ℤ (sec ℤ (Veronese.x D) n) = (2 * n + D).choose D := by
  have h1 : sec ℤ (Veronese.x D) n = sec ℤ (Veronese.t D) (2 * n) := by
    rw [SectionsRank.sec_eq_span, SectionsRank.sec_eq_span, range_alt, ← pow_mul]
  rw [h1, ← finrank_homog D (2 * n)]
  exact (Submodule.equivMapOfInjective _ (aeval_t_injective D) _).finrank_eq.symm

/- English proof (translation)
Unfold `GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff`. Rewrite using `[List.ofFn_const]`. Proceed by induction on `D with`. Consider the case `zero => rfl`. Consider the case `succ D ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']`.
-/
theorem mixedDiff_const {K : Type*} (D : ℕ) (b : K → ℤ) (h : (K → ℤ) → ℤ) :
    GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => b) h =
      (GroundTheory.Heights₂.Heights.NumbersDVR.diffStep b)^[D] h := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_const]
  induction D with
  | zero => rfl
  | succ D ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

/- English proof (translation)
Proceed by induction on `D generalizing H with`. Consider the case `zero => simp`. Consider the case `succ D ih`. Rewrite using `[Function.iterate_succ_apply, ih]`. Establish `hg : (fun j : ℤ => GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1 H (fun _ => j)) = fun j : ℤ => fwdDiff 1 (fun j : ℤ => H (fun _ => j)) (j + -1)`.

Use function extensionality and compare the values at `j`. Establish `e1 : (fun _ : Unit => j + -1 + 1) = fun _ => j` using `by funext u; ring`. Establish `e2 : ((fun _ : Unit => j) - 1) = fun _ => j + -1` using `by funext u; simp; ring`. Simplify using `only [GroundTheory.Heights₂.Heights.NumbersDVR.diffStep, fwdDiff, e1, e2]`. Rewrite using `[hg, fwdDiff_iter_comp_add, ← Function.iterate_succ_apply, show k - (D : ℤ) + -1 = k - ((D + 1 : ℕ) : ℤ) by push_cast; ring]`.
-/
theorem iterate_diffStep (D : ℕ) (H : (Unit → ℤ) → ℤ) (k : ℤ) :
    (GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1)^[D] H (fun _ => k) =
      (fwdDiff (1 : ℤ))^[D] (fun j : ℤ => H (fun _ => j)) (k - D) := by
  induction D generalizing H with
  | zero => simp
  | succ D ih =>
    rw [Function.iterate_succ_apply, ih]
    have hg : (fun j : ℤ => GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1 H (fun _ => j)) =
        fun j : ℤ => fwdDiff 1 (fun j : ℤ => H (fun _ => j)) (j + -1) := by
      funext j
      have e1 : (fun _ : Unit => j + -1 + 1) = fun _ => j := by funext u; ring
      have e2 : ((fun _ : Unit => j) - 1) = fun _ => j + -1 := by funext u; simp; ring
      simp only [GroundTheory.Heights₂.Heights.NumbersDVR.diffStep, fwdDiff, e1, e2]
    rw [hg, fwdDiff_iter_comp_add, ← Function.iterate_succ_apply,
      show k - (D : ℤ) + -1 = k - ((D + 1 : ℕ) : ℤ) by push_cast; ring]

def hilbPoly (D : ℕ) : Polynomial ℚ :=
  (Polynomial.preHilbertPoly ℚ D 0).comp (Polynomial.C 2 * Polynomial.X)

/- English proof (translation)
Rewrite using `[hilbPoly, Polynomial.eval_comp]`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]`. Use `Polynomial.preHilbertPoly_eq_choose_sub_add ℚ D (k := 0) (n := 2 * n) (Nat.zero_le _)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this, Nat.sub_zero]`.
-/
theorem hilbPoly_eval (D n : ℕ) : (hilbPoly D).eval (n : ℚ) = ((2 * n + D).choose D : ℚ) := by
  rw [hilbPoly, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have := Polynomial.preHilbertPoly_eq_choose_sub_add ℚ D (k := 0) (n := 2 * n) (Nat.zero_le _)
  push_cast at this
  rw [this, Nat.sub_zero]

/- English proof (translation)
Establish `hdeg : (hilbPoly D).natDegree = D`. Rewrite using `[hilbPoly, Polynomial.natDegree_comp, Polynomial.natDegree_preHilbertPoly, Polynomial.natDegree_C_mul_X _ two_ne_zero, mul_one]`. Establish `hlc : (hilbPoly D).leadingCoeff = (D.factorial : ℚ)⁻¹ * 2 ^ D`. Rewrite using `[hilbPoly, Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero), Polynomial.leadingCoeff_preHilbertPoly, Polynomial.leadingCoeff_C_mul_X, Polynomial.natDegree_preHilbertPoly]`. Establish `h` using `congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial (hilbPoly D)) y`.

Rewrite `h` using `[hdeg, hlc]`. Rewrite using `[h]`. Establish `hf : (D.factorial : ℚ) ≠ 0` using `by positivity`. Simplify using `only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fwdDiff_hilbPoly (D : ℕ) (y : ℚ) : (fwdDiff (1 : ℚ))^[D] (hilbPoly D).eval y = 2 ^ D := by
  have hdeg : (hilbPoly D).natDegree = D := by
    rw [hilbPoly, Polynomial.natDegree_comp, Polynomial.natDegree_preHilbertPoly,
      Polynomial.natDegree_C_mul_X _ two_ne_zero, mul_one]
  have hlc : (hilbPoly D).leadingCoeff = (D.factorial : ℚ)⁻¹ * 2 ^ D := by
    rw [hilbPoly, Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero),
      Polynomial.leadingCoeff_preHilbertPoly, Polynomial.leadingCoeff_C_mul_X,
      Polynomial.natDegree_preHilbertPoly]
  have h := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial (hilbPoly D)) y
  rw [hdeg, hlc] at h
  rw [h]
  have hf : (D.factorial : ℚ) ≠ 0 := by positivity
  simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
  field_simp

/- English proof (translation)
Unfold `GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue`. Establish `hex : ∃ c, ∀ᶠ m in atTop, F m = c` using `⟨c, h⟩`. Rewrite using `[dif_pos hex]`. Take `⟨m, h1, h2⟩` from `(hex.choose_spec.and h).exists`. Rewrite using `[← h1, h2]`.
-/
theorem eventualValue_eq {K : Type*} (F : (K → ℤ) → ℤ) (c : ℤ)
    (h : ∀ᶠ m in atTop, F m = c) : GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue F = c := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue
  have hex : ∃ c, ∀ᶠ m in atTop, F m = c := ⟨c, h⟩
  rw [dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and h).exists
  rw [← h1, h2]

end VeroneseGenDeg

open VeroneseGenDeg in

/- English proof (translation)
Introduce `D _`. Use `set q := (coordIdeal ℤ (Veronese.x D)).map (MvPolynomial.map (Int.castRingHom ℚ)) with hq`. Use `set g : ℤ → ℤ := fun j => GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q (fun _ => j) with hgdef`. Establish `hg : ∀ j : ℤ, 0 ≤ j → (g j : ℚ) = (hilbPoly D).eval (j : ℚ)`. Introduce `j hj`.

Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le hj`. Establish `h` using `SectionsRank.proof (Veronese.Fld D) (Veronese.Idx D) (Veronese.x D) n`. Rewrite `h` using `[finrank_sec]`. Simplify using `only [hgdef]`. Rewrite `h` using `[← hq]`.

Rewrite using `[h, Int.cast_natCast, Int.cast_natCast, hilbPoly_eval]`. Establish `hev : ∀ᶠ m in atTop, GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => (1 : Unit → ℤ)) (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι` using `GlobalTheory (Veronese.Idx D)) q) m = 2 ^ D := by filter_upwards [eventually_ge_atTop (fun _ : Unit => (D : ℤ))] with m hm`. Establish `hm' : m = fun _ => m ()` using `funext fun u => rfl`. Establish `hD : (D : ℤ) ≤ m ()` using `hm ()`. Rewrite using `[mixedDiff_const, hm', iterate_diffStep]`.

Establish `key : (((fwdDiff (1 : ℤ))^[D] g (m () - D) : ℤ) : ℚ) = 2 ^ D`. Rewrite using `[← fwdDiff_hilbPoly D ((m () - D : ℤ) : ℚ), fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [nsmul_eq_mul, mul_one, smul_eq_mul, zsmul_eq_mul]`.

Use `push_cast`. Rewrite using `[hg _ (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `key` after adjusting the coercions.

Unfold `genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum`. Apply `eventualValue_eq` to reduce the goal to its premises. Use `hev` and compare the differences between its conclusion and the goal.
-/
theorem VeroneseGenDeg.proof : VeroneseGenDeg.Statement := by
  intro D _
  set q := (coordIdeal ℤ (Veronese.x D)).map (MvPolynomial.map (Int.castRingHom ℚ)) with hq
  set g : ℤ → ℤ := fun j => GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q (fun _ => j)
    with hgdef

  have hg : ∀ j : ℤ, 0 ≤ j → (g j : ℚ) = (hilbPoly D).eval (j : ℚ) := by
    intro j hj
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have h := SectionsRank.proof (Veronese.Fld D) (Veronese.Idx D) (Veronese.x D) n
    rw [finrank_sec] at h
    simp only [hgdef]
    rw [← hq] at h
    rw [h, Int.cast_natCast, Int.cast_natCast, hilbPoly_eval]
  have hev : ∀ᶠ m in atTop, GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => (1 : Unit → ℤ))
      (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q) m = 2 ^ D := by
    filter_upwards [eventually_ge_atTop (fun _ : Unit => (D : ℤ))] with m hm
    have hm' : m = fun _ => m () := funext fun u => rfl
    have hD : (D : ℤ) ≤ m () := hm ()
    rw [mixedDiff_const, hm', iterate_diffStep]
    have key : (((fwdDiff (1 : ℤ))^[D] g (m () - D) : ℤ) : ℚ) = 2 ^ D := by
      rw [← fwdDiff_hilbPoly D ((m () - D : ℤ) : ℚ), fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [nsmul_eq_mul, mul_one, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [hg _ (by omega)]
      push_cast
      ring
    exact_mod_cast key
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  apply eventualValue_eq
  convert hev

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
