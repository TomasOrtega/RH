import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemPPSetCongrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGeneratStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCoeffMemDividedPowerSeriesSubringStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdPolyEvaluationOfMemDividedTwoVariableSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPolynomialApproxDividedTwoVariableSetStatement
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysEval

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O)

omit [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] in

/- English proof (translation)
Use `⟨fun x => ((x.1.factorial * (x.2 / e).factorial : ℕ) : Wq l a) * (b.coeff x.1).coeff x.2, fun r => ?_, fun τ i n => ?_⟩` and prove the remaining obligations. Use `Filter.eventually_cofinite.2 (((Set.finite_Iic b.natDegree).prod (Set.finite_Iic ((Finset.range (b.natDegree + 1)).sup fun i => (b.coeff i).natDegree))).subset fun x hx => ?_)` and prove the remaining obligations. Establish `h0 : (b.coeff x.1).coeff x.2 ≠ 0` using `fun h0 => hx (by simp [h0])`. Establish `h1 : b.coeff x.1 ≠ 0` using `fun h1 => h0 (by simp [h1])`. Establish `h2` using `Polynomial.le_natDegree_of_ne_zero h1`.

Establish `h3` using `Polynomial.le_natDegree_of_ne_zero h0`. Conclude with `⟨h2, h3.trans (Finset.le_sup (f := fun i => (b.coeff i).natDegree) (Finset.mem_range.2 (Nat.lt_succ_of_le h2)))⟩`. Rewrite using `[coeff_iotaP]`. Simplify using `[embK, map_mul, map_natCast]`.
-/
theorem iotaP_mem (b : Bp l a) : iotaP K t b ∈ PPSet t K e := by
  refine ⟨fun x => ((x.1.factorial * (x.2 / e).factorial : ℕ) : Wq l a) * (b.coeff x.1).coeff x.2,
    fun r => ?_, fun τ i n => ?_⟩
  · refine Filter.eventually_cofinite.2 (((Set.finite_Iic b.natDegree).prod (Set.finite_Iic
      ((Finset.range (b.natDegree + 1)).sup fun i => (b.coeff i).natDegree))).subset fun x hx => ?_)
    have h0 : (b.coeff x.1).coeff x.2 ≠ 0 := fun h0 => hx (by simp [h0])
    have h1 : b.coeff x.1 ≠ 0 := fun h1 => h0 (by simp [h1])
    have h2 := Polynomial.le_natDegree_of_ne_zero h1
    have h3 := Polynomial.le_natDegree_of_ne_zero h0
    exact ⟨h2, h3.trans (Finset.le_sup (f := fun i => (b.coeff i).natDegree)
      (Finset.mem_range.2 (Nat.lt_succ_of_le h2)))⟩
  · rw [coeff_iotaP]
    simp [embK, map_mul, map_natCast]

variable (K) in

def iotaD : Bp l a →+* PPd t K e :=
  (iotaP K t).codRestrict (PPd t K e) fun b => Subring.subset_closure (iotaP_mem t b)

omit [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedAlgebra ℚ_[l] K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_iotaD (b : Bp l a) : (iotaD K (e := e) t b : ZMod a → K⟦X⟧⟦X⟧) = iotaP K t b := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `PowerSeries.map (rhoK K t τ) ((Polynomial.C q : Bp l a) : (Polynomial (Wq l a))⟦X⟧) = _`. Rewrite using `[Polynomial.coe_C, map_C]`.
-/
theorem iotaP_C (q : Polynomial (Wq l a)) (τ : ZMod a) :
    iotaP K t (Polynomial.C q) τ = C (rhoK K t τ q) := by
  change PowerSeries.map (rhoK K t τ) ((Polynomial.C q : Bp l a) : (Polynomial (Wq l a))⟦X⟧) = _
  rw [Polynomial.coe_C, map_C]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `PowerSeries.map (rhoK K t τ) ((Polynomial.X : Bp l a) : (Polynomial (Wq l a))⟦X⟧) = _`. Rewrite using `[Polynomial.coe_X, map_X]`.
-/
theorem iotaP_X (τ : ZMod a) : iotaP K t (Polynomial.X : Bp l a) τ = X := by
  change PowerSeries.map (rhoK K t τ) ((Polynomial.X : Bp l a) : (Polynomial (Wq l a))⟦X⟧) = _
  rw [Polynomial.coe_X, map_X]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `PowerSeries.map (embK K t τ) ((Polynomial.C w : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = _`. Rewrite using `[Polynomial.coe_C, map_C]`.
-/
theorem rhoK_C (w : Wq l a) (τ : ZMod a) : rhoK K t τ (Polynomial.C w) = C (embK K t τ w) := by
  change PowerSeries.map (embK K t τ) ((Polynomial.C w : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = _
  rw [Polynomial.coe_C, map_C]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `PowerSeries.map (embK K t τ) ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = _`. Rewrite using `[Polynomial.coe_X, map_X]`.
-/
theorem rhoK_X (τ : ZMod a) : rhoK K t τ Polynomial.X = X := by
  change PowerSeries.map (embK K t τ) ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = _
  rw [Polynomial.coe_X, map_X]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `coeff i (PowerSeries.map (rhoK K t τ) (b : (Polynomial (Wq l a))⟦X⟧)) = _`. Rewrite using `[coeff_map, Polynomial.coeff_coe]`.
-/
theorem coeff_iotaP_X (b : Bp l a) (τ : ZMod a) (i : ℕ) : coeff i (iotaP K t b τ) = rhoK K t τ (b.coeff i) := by
  change coeff i (PowerSeries.map (rhoK K t τ) (b : (Polynomial (Wq l a))⟦X⟧)) = _
  rw [coeff_map, Polynomial.coeff_coe]

omit [NeZero e] in

/- English proof (translation)
The claim follows from `funext fun τ => by rw [iotaP_C, rhoK_eq_toAc] rfl`.
-/
theorem constP_inclS_coe (q : Polynomial (Wq l a)) :
    constP a K (inclS t K (q : (Wq l a)⟦X⟧)) = iotaP K t (Polynomial.C q) := funext fun τ => by
  rw [iotaP_C, rhoK_eq_toAc]
  rfl

omit [NeZero e] in

/- English proof (translation)
The claim follows from `(GlobalTheory.MemLoc.acris_torsionFree_complete l).2`.
-/
theorem acris_complete : IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) :=
  (GlobalTheory.MemLoc.acris_torsionFree_complete l).2

/- English proof (translation)
Take `⟨n, b, p, h, hn, hp, hh, hpb, hF⟩` from `GlobalTheory.T.exists_polynomial_approx_dividedTwoVariableSet l a e O K t F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t _ F.2) r`. Conclude with `⟨n, b, ⟨p, Subring.subset_closure hp⟩, ⟨h, Subring.subset_closure hh⟩, hn, Subtype.ext (by simpa [coe_iotaD] using hpb), Subtype.ext (by simpa using hF)⟩`.
-/
theorem denseD (F : PPd t K e) (r : ℕ) : ∃ (n : ℕ) (b : Bp l a) (p h : PPd t K e),
    n ≠ 0 ∧ (n : PPd t K e) * p = iotaD K t b ∧ F = p + (l : PPd t K e) ^ r * h := by
  obtain ⟨n, b, p, h, hn, hp, hh, hpb, hF⟩ := GlobalTheory.T.exists_polynomial_approx_dividedTwoVariableSet l a e O K t F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t _ F.2) r
  exact ⟨n, b, ⟨p, Subring.subset_closure hp⟩, ⟨h, Subring.subset_closure hh⟩, hn,
    Subtype.ext (by simpa [coe_iotaD] using hpb), Subtype.ext (by simpa using hF)⟩

variable (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a)))

/- English proof (translation)
Use `acris_complete (l := l)` as an intermediate fact. Use `exists_ringHom (fun n x hn h => acris_nat_cancel hn h) (fun n b p hn hp => ?_) hl.out.ne_zero (fun F r => ?_)` and prove the remaining obligations. Conclude with `GlobalTheory.T.dvd_polyEvaluation_of_mem_dividedTwoVariableSet l a e O K t ϖ g b p (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t _ p.2) n hn (by simpa [coe_iotaD] using congrArg Subtype.val hp)`. Conclude with `denseD t F r`.
-/
theorem exists_E : ∃ E : PPd t K e →+* Per.Acris l,
    ∀ F r y, Approx l (iotaD K t) (fP a ϖ (g : GQ l)) F r y → (l : Per.Acris l) ^ r ∣ E F - y := by
  have := acris_complete (l := l)
  refine exists_ringHom (fun n x hn h => acris_nat_cancel hn h) (fun n b p hn hp => ?_) hl.out.ne_zero
    (fun F r => ?_)
  · exact GlobalTheory.T.dvd_polyEvaluation_of_mem_dividedTwoVariableSet l a e O K t ϖ g b p (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t _ p.2) n hn
      (by simpa [coe_iotaD] using congrArg Subtype.val hp)
  · exact denseD t F r

def evE : PPd t K e →+* Per.Acris l := (exists_E t ϖ g).choose

/- English proof (translation)
The claim follows from `(exists_E t ϖ g).choose_spec F r y h`.
-/
theorem evE_approx (F : PPd t K e) (r : ℕ) (y : Per.Acris l)
    (h : Approx l (iotaD K t) (fP a ϖ (g : GQ l)) F r y) : (l : Per.Acris l) ^ r ∣ evE t ϖ g F - y :=
  (exists_E t ϖ g).choose_spec F r y h

/- English proof (translation)
Use `acris_complete (l := l)` as an intermediate fact. Conclude with `sub_eq_zero.1 (sep_l l _ fun r => evE_approx t ϖ g _ r _ (approx_ι b r))`.
-/
theorem evE_iotaD (b : Bp l a) : evE t ϖ g (iotaD K t b) = fP a ϖ (g : GQ l) b := by
  have := acris_complete (l := l)
  exact sub_eq_zero.1 (sep_l l _ fun r => evE_approx t ϖ g _ r _ (approx_ι b r))

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `evE_iotaD t ϖ g b`.
-/
theorem evE_of_eq {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPd t K e) (b : Bp l a) (h : F = iotaP K t b) :
    evE t ϖ g ⟨F, hF⟩ = fP a ϖ (g : GQ l) b := by
  subst h
  exact evE_iotaD t ϖ g b

omit [NeZero e] in
/- English proof (translation)
Simplify using `[fP, evC]`.
-/
theorem fP_C (q : Polynomial (Wq l a)) (g' : GQ l) : fP a ϖ g' (Polynomial.C q) = ainfToAcris l (ϖ.ev a q) := by
  simp [fP, evC]

omit [NeZero e] in
/- English proof (translation)
Simplify using `[fP]`.
-/
theorem fP_X (g' : GQ l) : fP a ϖ g' Polynomial.X = ainfToAcris l (ϖ.mu g' * ϖ.teich) := by
  simp [fP]

omit [NeZero a] [NeZero e] in

/- English proof (translation)
Use `acris_complete (l := l)` as an intermediate fact. Use `sep_l l x fun r => ?_` and prove the remaining obligations. Take `⟨d, hd⟩` from `ϖ.exists_dpow_teich (l ^ r)`. Take `⟨k, hk⟩` from `Nat.dvd_factorial (pow_pos hl.out.pos r) (le_refl (l ^ r))`. Use `Dvd.dvd.trans ⟨k * d, ?_⟩ (h (e * l ^ r))` and prove the remaining obligations.

Rewrite using `[← hd, hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sep_teich_acris (x : Per.Acris l) (h : ∀ n, ainfToAcris l ϖ.teich ^ n ∣ x) : x = 0 := by
  have := acris_complete (l := l)
  refine sep_l l x fun r => ?_
  obtain ⟨d, hd⟩ := ϖ.exists_dpow_teich (l ^ r)
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (pow_pos hl.out.pos r) (le_refl (l ^ r))
  refine Dvd.dvd.trans ⟨k * d, ?_⟩ (h (e * l ^ r))
  rw [← hd, hk]
  push_cast
  ring

/- English proof (translation)
The claim follows from `Subring.subset_closure (constP_mem t e (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t x))`.
-/
theorem constP_inclS_mem (x : (Wq l a)⟦X⟧) : constP a K (inclS t K x) ∈ PPd t K e :=
  Subring.subset_closure (constP_mem t e (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t x))

/- English proof (translation)
The claim follows from `(evE_of_eq t ϖ g h _ (constP_inclS_coe t q)).trans (fP_C ϖ q _)`.
-/
theorem evE_constP_coe (q : Polynomial (Wq l a)) (h : constP a K (inclS t K (q : (Wq l a)⟦X⟧)) ∈ PPd t K e) :
    evE t ϖ g ⟨_, h⟩ = ainfToAcris l (ϖ.ev a q) :=
  (evE_of_eq t ϖ g h _ (constP_inclS_coe t q)).trans (fP_C ϖ q _)

/- English proof (translation)
Set `φ : (Wq l a)⟦X⟧ →+* Per.Acris l` to `(evE t ϖ g).comp (((constP a K).comp (inclS t K)).codRestrict _ (constP_inclS_mem t))`. Establish `hφ : ∀ q : Polynomial (Wq l a), φ q = ainfToAcris l (ϖ.ev a q)` using `fun q => evE_constP_coe t ϖ g q _`. Establish `hφX : φ X = ainfToAcris l ϖ.teich`. Use `hφ Polynomial.X` as an intermediate fact. Rewrite `this` using `[Polynomial.coe_X, PiSys.ev_X]`. Then use the resulting hypothesis.

Establish `h` using `ringHom_ext_of_sep φ ((ainfToAcris l).toRingHom.comp (ϖ.ev a)) (fun w => ?_) ?_ (fun y hy => sep_teich_acris ϖ y fun n => hφX ▸ hy n)`. Conclude with `RingHom.congr_fun h x`. Use `hφ (Polynomial.C w)` as an intermediate fact. Rewrite `this` using `[Polynomial.coe_C]`. Then use the resulting hypothesis. Use `hφ Polynomial.X` as an intermediate fact.

Rewrite `this` using `[Polynomial.coe_X]`. Then use the resulting hypothesis.
-/
theorem evE_constP (x : (Wq l a)⟦X⟧) (hx : constP a K (inclS t K x) ∈ PPd t K e) :
    evE t ϖ g ⟨_, hx⟩ = ainfToAcris l (ϖ.ev a x) := by
  let φ : (Wq l a)⟦X⟧ →+* Per.Acris l :=
    (evE t ϖ g).comp (((constP a K).comp (inclS t K)).codRestrict _ (constP_inclS_mem t))
  have hφ : ∀ q : Polynomial (Wq l a), φ q = ainfToAcris l (ϖ.ev a q) := fun q =>
    evE_constP_coe t ϖ g q _
  have hφX : φ X = ainfToAcris l ϖ.teich := by
    have := hφ Polynomial.X
    rwa [Polynomial.coe_X, PiSys.ev_X] at this
  have h := ringHom_ext_of_sep φ ((ainfToAcris l).toRingHom.comp (ϖ.ev a)) (fun w => ?_) ?_
    (fun y hy => sep_teich_acris ϖ y fun n => hφX ▸ hy n)
  · exact RingHom.congr_fun h x
  · have := hφ (Polynomial.C w)
    rwa [Polynomial.coe_C] at this
  · have := hφ Polynomial.X
    rwa [Polynomial.coe_X] at this

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] in
/- English proof (translation)
Rewrite using `[PiSys.mu, add_sub_cancel, PiSys.teich, ← map_mul, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]`.
-/
theorem frobenius_teich_mul (g' : GQ l) :
    WittVector.frobenius ((1 + ϖ.mu g') * ϖ.teich) = ((1 + ϖ.mu g') * ϖ.teich) ^ l := by
  rw [PiSys.mu, add_sub_cancel, PiSys.teich, ← map_mul, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller, frobenius_def, map_pow]

section Sh

variable (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
  (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
include hsh

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] in

/- English proof (translation)
Use extensionality with `i : 1`. Break down `i with _ | i` into its components or cases. Simplify `hsh (C c) 0` using `[coeff_C]`. Establish `h` using `hsh (C c) (i + 1)`. Establish `h4 : (PowerSeries.derivative K)^[i + 1] (C c) = 0`.

Rewrite using `[Function.iterate_succ_apply, PowerSeries.derivative_C]`. Conclude with `Function.iterate_fixed (map_zero _) i`. Rewrite `h` using `[h4]`. Rewrite using `[(mul_eq_zero.1 h).resolve_left (natCast_ne_zero_ps (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))), coeff_C, if_neg (Nat.succ_ne_zero i)]`.
-/
theorem sh_C [CharZero K] (c : K) : sh (C c) = C (C c) := by
  ext i : 1
  rcases i with _ | i
  · simpa [coeff_C] using hsh (C c) 0
  · have h := hsh (C c) (i + 1)
    have h4 : (PowerSeries.derivative K)^[i + 1] (C c) = 0 := by
      rw [Function.iterate_succ_apply, PowerSeries.derivative_C]
      exact Function.iterate_fixed (map_zero _) i
    rw [h4] at h
    rw [(mul_eq_zero.1 h).resolve_left (natCast_ne_zero_ps (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))),
      coeff_C, if_neg (Nat.succ_ne_zero i)]

/- English proof (translation)
The claim follows from `Subring.subset_closure (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).1`.
-/
theorem shP_mem (x : (Wq l a)⟦X⟧) : shP a sh (inclS t K (frobS l a x)) ∈ PPd t K e :=
  Subring.subset_closure (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).1

omit [NeZero e] in
/- English proof (translation)
Use `charZero_K (l := l) (K := K)` as an intermediate fact. Use function extensionality and compare the values at `τ`. Rewrite using `[iotaP_C, rhoK_C, frobS_C]`. Express the relevant statement in the definitionally equal form `sh (toAc t K (C (sigma l a w)) τ : K⟦X⟧) = _`. Apply the tactic sequence `rw [show (toAc t K (C (sigma l a w)) τ : K⟦X⟧) = C (embK K t τ (sigma l a w)) from PowerSeries.ext fun n => by rw [coeff_toAc, coeff_C, coeff_C]; split_ifs <;> simp [embK]]`.

Conclude with `sh_C sh hsh _`.
-/
theorem shP_frobS_C (w : Wq l a) :
    shP a sh (inclS t K (frobS l a (C w))) = iotaP K t (Polynomial.C (Polynomial.C (sigma l a w))) := by
  have := charZero_K (l := l) (K := K)
  funext τ
  rw [iotaP_C, rhoK_C, frobS_C]
  change sh (toAc t K (C (sigma l a w)) τ : K⟦X⟧) = _
  rw [show (toAc t K (C (sigma l a w)) τ : K⟦X⟧) = C (embK K t τ (sigma l a w)) from
    PowerSeries.ext fun n => by rw [coeff_toAc, coeff_C, coeff_C]; split_ifs <;> simp [embK]]
  exact sh_C sh hsh _

omit [NeZero e] in
/- English proof (translation)
Use `charZero_K (l := l) (K := K)` as an intermediate fact. Use function extensionality and compare the values at `τ`. Rewrite using `[map_pow, map_add, Pi.pow_apply, Pi.add_apply, iotaP_C, rhoK_X, iotaP_X, frobS_X, map_pow, map_pow, Pi.pow_apply]`. Express the relevant statement in the definitionally equal form `sh (toAc t K X τ : K⟦X⟧) ^ l = _`. Rewrite using `[show (toAc t K X τ : K⟦X⟧) = X from PowerSeries.ext fun n => by`.

Apply the tactic sequence `rw [coeff_toAc, coeff_X, coeff_X]; split_ifs <;> simp, sh_X sh hsh]`.
-/
theorem shP_frobS_X :
    shP a sh (inclS t K (frobS l a X)) = iotaP K t ((Polynomial.C Polynomial.X + Polynomial.X) ^ l) := by
  have := charZero_K (l := l) (K := K)
  funext τ
  rw [map_pow, map_add, Pi.pow_apply, Pi.add_apply, iotaP_C, rhoK_X, iotaP_X, frobS_X, map_pow, map_pow,
    Pi.pow_apply]
  change sh (toAc t K X τ : K⟦X⟧) ^ l = _
  rw [show (toAc t K X τ : K⟦X⟧) = X from PowerSeries.ext fun n => by
    rw [coeff_toAc, coeff_X, coeff_X]; split_ifs <;> simp, sh_X sh hsh]

/- English proof (translation)
Set `φ : (Wq l a)⟦X⟧ →+* Per.Acris l` to `(evE t ϖ g).comp (((shP a sh).comp ((inclS t K).comp (frobS l a))).codRestrict _ (shP_mem t sh hsh))`. Set `ψ : (Wq l a)⟦X⟧ →+* Per.Acris l` to `(ainfToAcris l).toRingHom.comp (WittVector.frobenius.comp ((Per.σA (g : GQ l)).comp (ϖ.ev a)))`. Establish `hψX : ψ X = (ainfToAcris l ((1 + ϖ.mu g) * ϖ.teich)) ^ l`. Express the relevant statement in the definitionally equal form `ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a X))) = _`. Rewrite using `[PiSys.ev_X, PiSys.gal_teich, frobenius_teich_mul, map_pow]`.

Establish `hπ : ainfToAcris l ϖ.teich ∣ ψ X`. Rewrite using `[hψX, map_mul]`. Conclude with `(dvd_mul_left _ _).trans (dvd_pow_self _ hl.out.ne_zero)`. Establish `hg : ∀ y ∈ Kunr l a, (g : GQ l) y = y` using `fun y hy => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 y (ϖ.Kunr_le_field a hy)`. Establish `hφC : ∀ w, φ (C w) = ψ (C w)` using `fun w => by`.

Express the relevant statement in the definitionally equal form `evE t ϖ g ⟨shP a sh (inclS t K (frobS l a (C w))), shP_mem t sh hsh _⟩ = ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a (C w))))`. Rewrite using `[evE_of_eq t ϖ g _ _ (shP_frobS_C t sh hsh w), fP_C, Polynomial.coe_C, PiSys.ev_C, PiSys.ev_C, gal_wA l a hg, wA_sigma]`. Establish `hφX : φ X = ψ X`. Express the relevant statement in the definitionally equal form `evE t ϖ g ⟨shP a sh (inclS t K (frobS l a X)), shP_mem t sh hsh _⟩ = ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a X)))`. Rewrite using `[evE_of_eq t ϖ g _ _ (shP_frobS_X t sh hsh), map_pow, map_add, fP_C, fP_X, Polynomial.coe_X, PiSys.ev_X, PiSys.gal_teich, frobenius_teich_mul, map_pow, map_mul, map_mul, map_add, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `ringHom_ext_of_sep ψ φ (fun w => (hφC w).symm) hφX.symm (fun y hy => sep_teich_acris ϖ y fun n => (pow_dvd_pow_of_dvd hπ n).trans (hy n))`. Conclude with `(RingHom.congr_fun h x).symm`.
-/
theorem evE_shP (x : (Wq l a)⟦X⟧) (hx : shP a sh (inclS t K (frobS l a x)) ∈ PPd t K e) :
    evE t ϖ g ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a x))) := by
  let φ : (Wq l a)⟦X⟧ →+* Per.Acris l := (evE t ϖ g).comp
    (((shP a sh).comp ((inclS t K).comp (frobS l a))).codRestrict _ (shP_mem t sh hsh))
  let ψ : (Wq l a)⟦X⟧ →+* Per.Acris l := (ainfToAcris l).toRingHom.comp
    (WittVector.frobenius.comp ((Per.σA (g : GQ l)).comp (ϖ.ev a)))
  have hψX : ψ X = (ainfToAcris l ((1 + ϖ.mu g) * ϖ.teich)) ^ l := by
    change ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a X))) = _
    rw [PiSys.ev_X, PiSys.gal_teich, frobenius_teich_mul, map_pow]
  have hπ : ainfToAcris l ϖ.teich ∣ ψ X := by
    rw [hψX, map_mul]
    exact (dvd_mul_left _ _).trans (dvd_pow_self _ hl.out.ne_zero)
  have hg : ∀ y ∈ Kunr l a, (g : GQ l) y = y := fun y hy =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 y (ϖ.Kunr_le_field a hy)
  have hφC : ∀ w, φ (C w) = ψ (C w) := fun w => by
    change evE t ϖ g ⟨shP a sh (inclS t K (frobS l a (C w))), shP_mem t sh hsh _⟩ =
      ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a (C w))))
    rw [evE_of_eq t ϖ g _ _ (shP_frobS_C t sh hsh w), fP_C, Polynomial.coe_C, PiSys.ev_C, PiSys.ev_C,
      gal_wA l a hg, wA_sigma]
  have hφX : φ X = ψ X := by
    change evE t ϖ g ⟨shP a sh (inclS t K (frobS l a X)), shP_mem t sh hsh _⟩ =
      ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a X)))
    rw [evE_of_eq t ϖ g _ _ (shP_frobS_X t sh hsh), map_pow, map_add, fP_C, fP_X, Polynomial.coe_X, PiSys.ev_X,
      PiSys.gal_teich, frobenius_teich_mul, map_pow, map_mul, map_mul, map_add, map_one]
    ring
  have h := ringHom_ext_of_sep ψ φ (fun w => (hφC w).symm) hφX.symm (fun y hy => sep_teich_acris ϖ y fun n =>
    (pow_dvd_pow_of_dvd hπ n).trans (hy n))
  exact (RingHom.congr_fun h x).symm

end Sh

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] in
/- English proof (translation)
Rewrite using `[WittVector.frobenius_eq_map_frobenius, PiSys.teich, WittVector.map_teichmuller, frobenius_def, map_pow]`.
-/
theorem frobenius_teich : WittVector.frobenius ϖ.teich = ϖ.teich ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, PiSys.teich, WittVector.map_teichmuller, frobenius_def, map_pow]

/- English proof (translation)
Use `acris_complete (l := l)` as an intermediate fact. Conclude with `ringHom_ext_dense (ι := iotaD K t) (fun n x hn h => acris_nat_cancel hn h) hl.out.ne_zero (denseD (e := e) t) G₁ G₂ h`.
-/
theorem evE_ext (G₁ G₂ : PPd t K e →+* Per.Acris l) (h : ∀ b, G₁ (iotaD K t b) = G₂ (iotaD K t b)) : G₁ = G₂ := by
  have := acris_complete (l := l)
  exact ringHom_ext_dense (ι := iotaD K t) (fun n x hn h => acris_nat_cancel hn h) hl.out.ne_zero
    (denseD (e := e) t) G₁ G₂ h

section Frob

variable (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
  (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
  (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) (hφC : ∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f))
  (hφsh : ∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f))
include hsh hφC hφsh

/- English proof (translation)
The claim follows from `Subring.subset_closure (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t F hF)).1`.
-/
theorem bivariateFrobenius_mem_dividedSubring {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPd t K e) : frob2 φ₂ F ∈ PPd t K e :=
  Subring.subset_closure (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t F hF)).1

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
/- English proof (translation)
Use `charZero_K (l := l) (K := K)` as an intermediate fact. Establish `h : (X : K⟦X⟧⟦X⟧) = sh X - C X` using `by rw [sh_X sh hsh]; ring`. Use `conv_lhs => rw [h]`. Rewrite using `[map_sub, hφsh, hφC, frob_X, map_pow, sh_X sh hsh]`.
-/
theorem φ₂_X : φ₂ X = (C X + X) ^ l - C (X ^ l) := by
  have := charZero_K (l := l) (K := K)
  have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
  conv_lhs => rw [h]
  rw [map_sub, hφsh, hφC, frob_X, map_pow, sh_X sh hsh]

omit [NeZero e] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `φ₂ (iotaP K t (Polynomial.C (Polynomial.C w)) (τ - 1)) = _`. Rewrite using `[iotaP_C, iotaP_C, rhoK_C, rhoK_C, hφC, frob_C]`. Use `congr 2`. Simplify using `only [embK, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, emb_sigma]`.
-/
theorem bivariateFrobenius_bivariateEmbedding_CC (w : Wq l a) :
    frob2 φ₂ (iotaP K t (Polynomial.C (Polynomial.C w))) = iotaP K t (Polynomial.C (Polynomial.C (sigma l a w))) := by
  funext τ
  change φ₂ (iotaP K t (Polynomial.C (Polynomial.C w)) (τ - 1)) = _
  rw [iotaP_C, iotaP_C, rhoK_C, rhoK_C, hφC, frob_C]
  congr 2
  simp only [embK, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, emb_sigma]

omit [NeZero e] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `φ₂ (iotaP K t (Polynomial.C Polynomial.X) (τ - 1)) = _`. Rewrite using `[iotaP_C, iotaP_C, rhoK_X, map_pow, rhoK_X, hφC, frob_X]`.
-/
theorem bivariateFrobenius_bivariateEmbedding_CX :
    frob2 φ₂ (iotaP K t (Polynomial.C Polynomial.X)) = iotaP K t (Polynomial.C (Polynomial.X ^ l)) := by
  funext τ
  change φ₂ (iotaP K t (Polynomial.C Polynomial.X) (τ - 1)) = _
  rw [iotaP_C, iotaP_C, rhoK_X, map_pow, rhoK_X, hφC, frob_X]

omit [NeZero e] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `φ₂ (iotaP K t Polynomial.X (τ - 1)) = _`. Rewrite using `[iotaP_X, φ₂_X sh hsh φ₂ hφC hφsh]`. Simplify using `only [map_sub, map_pow, map_add, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, iotaP_C, iotaP_X, rhoK_X]`.
-/
theorem bivariateFrobenius_bivariateEmbedding_X : frob2 φ₂ (iotaP K t Polynomial.X) =
    iotaP K t ((Polynomial.C Polynomial.X + Polynomial.X) ^ l - (Polynomial.C Polynomial.X) ^ l) := by
  funext τ
  change φ₂ (iotaP K t Polynomial.X (τ - 1)) = _
  rw [iotaP_X, φ₂_X sh hsh φ₂ hφC hφsh]
  simp only [map_sub, map_pow, map_add, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, iotaP_C, iotaP_X, rhoK_X]

/- English proof (translation)
Use `evE_ext t _ _ fun b => ?_` and prove the remaining obligations. Establish `key : ∀ b b' : Bp l a, frob2 φ₂ (iotaP K t b) = iotaP K t b' → fP a ϖ (g : GQ l) b' = frobC l (fP a ϖ (g : GQ l) b) → ((evE t ϖ g).comp ((frob2 φ₂).restrict (PPd t K e) (PPd t K e) fun _ hF => bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh hF)) (iotaD K t b) = ((frobC …` using `fun b b' h1 h2 => by`. Establish `hm : frob2 φ₂ (iotaP K t b) ∈ PPd t K e` using `bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh (Subring.subset_closure (iotaP_mem t b))`. Express the relevant statement in the definitionally equal form `evE t ϖ g ⟨frob2 φ₂ (iotaP K t b), hm⟩ = frobC l (evE t ϖ g (iotaD K t b))`. Rewrite using `[evE_of_eq t ϖ g hm b' h1, evE_iotaD, h2]`.

Set `H₁` to `((evE t ϖ g).comp ((frob2 φ₂).restrict (PPd t K e) (PPd t K e) fun _ hF => bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh hF)).comp (iotaD K t)`. Set `H₂` to `((frobC l).toRingHom.comp (evE t ϖ g)).comp (iotaD K t)`. Establish `hC : H₁.comp Polynomial.C = H₂.comp Polynomial.C`. Use `Polynomial.ringHom_ext (fun w => ?_) ?_` and prove the remaining obligations. Use `key _ _ (bivariateFrobenius_bivariateEmbedding_CC t sh hsh φ₂ hφC hφsh w) ?_` and prove the remaining obligations.

Rewrite using `[fP_C, fP_C, Polynomial.coe_C, Polynomial.coe_C, PiSys.ev_C, PiSys.ev_C, wA_sigma, GlobalTheory.AcrisPrism.frobC_ainfToAcris]`. Use `key _ _ (bivariateFrobenius_bivariateEmbedding_CX t sh hsh φ₂ hφC hφsh) ?_` and prove the remaining obligations. Rewrite using `[fP_C, fP_C, Polynomial.coe_pow, Polynomial.coe_X, map_pow, PiSys.ev_X, GlobalTheory.AcrisPrism.frobC_ainfToAcris, frobenius_teich, map_pow]`. Establish `h` using `Polynomial.ringHom_ext (f := H₁) (g := H₂) (fun q => RingHom.congr_fun hC q) (by`. Use `key _ _ (bivariateFrobenius_bivariateEmbedding_X t sh hsh φ₂ hφC hφsh) ?_` and prove the remaining obligations.

Rewrite using `[map_sub, map_pow, map_pow, map_add, fP_C, fP_X, Polynomial.coe_X, PiSys.ev_X, GlobalTheory.AcrisPrism.frobC_ainfToAcris]`. Establish `e1 : WittVector.frobenius (ϖ.mu (g : GQ l) * ϖ.teich) = ((1 + ϖ.mu (g : GQ l)) * ϖ.teich) ^ l - ϖ.teich ^ l`. Rewrite using `[show ϖ.mu (g : GQ l) * ϖ.teich = (1 + ϖ.mu (g : GQ l)) * ϖ.teich - ϖ.teich by ring, map_sub, frobenius_teich_mul, frobenius_teich]`. Rewrite using `[e1, map_sub, map_pow, map_pow, map_mul, map_mul, map_add, map_one]`. Use the proof step `ring)`.

Conclude with `RingHom.congr_fun h b`.
-/
theorem evE_frob2 : (evE t ϖ g).comp ((frob2 φ₂).restrict (PPd t K e) (PPd t K e)
    fun _ hF => bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh hF) = (frobC l).toRingHom.comp (evE t ϖ g) := by
  refine evE_ext t _ _ fun b => ?_
  have key : ∀ b b' : Bp l a, frob2 φ₂ (iotaP K t b) = iotaP K t b' →
      fP a ϖ (g : GQ l) b' = frobC l (fP a ϖ (g : GQ l) b) →
      ((evE t ϖ g).comp ((frob2 φ₂).restrict (PPd t K e) (PPd t K e)
        fun _ hF => bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh hF)) (iotaD K t b) =
      ((frobC l).toRingHom.comp (evE t ϖ g)) (iotaD K t b) := fun b b' h1 h2 => by
    have hm : frob2 φ₂ (iotaP K t b) ∈ PPd t K e :=
      bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh (Subring.subset_closure (iotaP_mem t b))
    change evE t ϖ g ⟨frob2 φ₂ (iotaP K t b), hm⟩ = frobC l (evE t ϖ g (iotaD K t b))
    rw [evE_of_eq t ϖ g hm b' h1, evE_iotaD, h2]
  let H₁ := ((evE t ϖ g).comp ((frob2 φ₂).restrict (PPd t K e) (PPd t K e)
    fun _ hF => bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh hF)).comp (iotaD K t)
  let H₂ := ((frobC l).toRingHom.comp (evE t ϖ g)).comp (iotaD K t)
  have hC : H₁.comp Polynomial.C = H₂.comp Polynomial.C := by
    refine Polynomial.ringHom_ext (fun w => ?_) ?_
    · refine key _ _ (bivariateFrobenius_bivariateEmbedding_CC t sh hsh φ₂ hφC hφsh w) ?_
      rw [fP_C, fP_C, Polynomial.coe_C, Polynomial.coe_C, PiSys.ev_C, PiSys.ev_C, wA_sigma,
        GlobalTheory.AcrisPrism.frobC_ainfToAcris]
    · refine key _ _ (bivariateFrobenius_bivariateEmbedding_CX t sh hsh φ₂ hφC hφsh) ?_
      rw [fP_C, fP_C, Polynomial.coe_pow, Polynomial.coe_X, map_pow, PiSys.ev_X,
        GlobalTheory.AcrisPrism.frobC_ainfToAcris, frobenius_teich, map_pow]
  have h := Polynomial.ringHom_ext (f := H₁) (g := H₂) (fun q => RingHom.congr_fun hC q) (by
    refine key _ _ (bivariateFrobenius_bivariateEmbedding_X t sh hsh φ₂ hφC hφsh) ?_
    rw [map_sub, map_pow, map_pow, map_add, fP_C, fP_X, Polynomial.coe_X, PiSys.ev_X,
      GlobalTheory.AcrisPrism.frobC_ainfToAcris]
    have e1 : WittVector.frobenius (ϖ.mu (g : GQ l) * ϖ.teich) =
        ((1 + ϖ.mu (g : GQ l)) * ϖ.teich) ^ l - ϖ.teich ^ l := by
      rw [show ϖ.mu (g : GQ l) * ϖ.teich = (1 + ϖ.mu (g : GQ l)) * ϖ.teich - ϖ.teich by ring, map_sub,
        frobenius_teich_mul, frobenius_teich]
    rw [e1, map_sub, map_pow, map_pow, map_mul, map_mul, map_add, map_one]
    ring)
  exact RingHom.congr_fun h b

end Frob

/- English proof (translation)
Establish `h : (fun τ => (⟨rhoK K t τ q, hq τ⟩ : S O K e)) = fun τ => ⟨(toAc t K (q : (Wq l a)⟦X⟧) τ : K⟦X⟧), A_le_S l e (toAc t K (q : (Wq l a)⟦X⟧) τ).2⟩`. Use function extensionality and compare the values at `fun τ => Subtype.ext (rhoK_eq_toAc t q τ)`. Rewrite using `[h, PiSys.iC_of_mem, PiSys.iTot_toAc, toOCr_tmul]`.
-/
theorem iC_rhoK (q : Polynomial (Wq l a)) (hq : ∀ τ, rhoK K t τ q ∈ S O K e) :
    ϖ.iC t K (fun τ => ⟨rhoK K t τ q, hq τ⟩) = 1 ⊗ₜ ainfToAcris l (ϖ.ev a q) := by
  have h : (fun τ => (⟨rhoK K t τ q, hq τ⟩ : S O K e)) =
      fun τ => ⟨(toAc t K (q : (Wq l a)⟦X⟧) τ : K⟦X⟧), A_le_S l e (toAc t K (q : (Wq l a)⟦X⟧) τ).2⟩ :=
    funext fun τ => Subtype.ext (rhoK_eq_toAc t q τ)
  rw [h, PiSys.iC_of_mem, PiSys.iTot_toAc, toOCr_tmul]

/- English proof (translation)
Establish `hX : ∀ τ, rhoK K t τ Polynomial.X ∈ S O K e` using `fun τ => by rw [rhoK_X]; exact HasU.X_mem`. Establish `e1 : (fun _ => uIn (S O K e) : ZMod a → S O K e) = fun τ => ⟨rhoK K t τ Polynomial.X, hX τ⟩`. Use function extensionality and compare the values at `fun τ => Subtype.ext (rhoK_X t τ).symm`. Rewrite using `[e1, iC_rhoK, Polynomial.coe_X, PiSys.ev_X]`.
-/
theorem iC_u : ϖ.iC t K (fun _ => uIn (S O K e)) = 1 ⊗ₜ ainfToAcris l ϖ.teich := by
  have hX : ∀ τ, rhoK K t τ Polynomial.X ∈ S O K e := fun τ => by rw [rhoK_X]; exact HasU.X_mem
  have e1 : (fun _ => uIn (S O K e) : ZMod a → S O K e) = fun τ => ⟨rhoK K t τ Polynomial.X, hX τ⟩ :=
    funext fun τ => Subtype.ext (rhoK_X t τ).symm
  rw [e1, iC_rhoK, Polynomial.coe_X, PiSys.ev_X]

/- English proof (translation)
Set `j : Per.Acris l →ₐ[ℤ_[l]] OCr l O` to `Algebra.TensorProduct.includeRight`. Establish `hq : ∀ τ, rhoK K t τ (b.coeff i) ∈ S O K e` using `fun τ => by`. Rewrite using `[rhoK_eq_toAc]`. Conclude with `A_le_S l e (toAc t K _ τ).2`. Establish `e1 : (N : ZMod a → S O K e) * (fun τ => ⟨_, hSp τ⟩) = (fun _ => uIn (S O K e)) ^ i * (i.factorial : ZMod a → S O K e) * fun τ => ⟨rhoK K t τ (b.coeff i), hq τ⟩` using `funext fun τ => Subtype.ext (by`.

Establish `h2` using `congrArg (fun G => coeff i (G τ)) hpb`. Simplify using `only [Pi.mul_apply, Pi.natCast_apply] at h2`. Rewrite `h2` using `[← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, coeff_iotaP_X]`. Simplify using `only [Pi.mul_apply, Pi.natCast_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast, coe_uIn]`. Rewrite using `[← h2]`.

Use the proof step `ring)`. Establish `hA : (N : OCr l O) * ϖ.iC t K (fun τ => ⟨_, hSp τ⟩) = j (ainfToAcris l ϖ.teich) ^ i * (i.factorial : OCr l O) * j (ainfToAcris l (ϖ.ev a (b.coeff i)))`. Rewrite using `[← map_natCast (ϖ.iC t K), ← map_mul, e1, map_mul, map_mul, map_pow, map_natCast, iC_u, iC_rhoK]`. Both sides reduce to the same expression. Establish `h3 : (i.factorial : OCr l O) * ϖ.muDiv a O g i = j (ainfToAcris l (ϖ.mu g)) ^ i`.

Establish `h4` using `congrArg j (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)`. Rewrite `h4` using `[map_mul, map_natCast, map_pow]`. Conclude with `h4`. Rewrite using `[mul_left_comm, hA]`. Express the relevant statement in the definitionally equal form `_ = j _`.

Rewrite using `[map_mul, map_pow, map_mul, map_mul]`. Take the linear combination `(j (ainfToAcris l ϖ.teich) ^ i * j (ainfToAcris l (ϖ.ev a (b.coeff i)))) * h3`.
-/
theorem taylor_term (b : Bp l a) (p : ZMod a → K⟦X⟧⟦X⟧) (N : ℕ) (hpb : (N : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b)
    (i : ℕ) (hSp : ∀ τ, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) ∈ S O K e) :
    (N : OCr l O) * (ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSp τ⟩)) =
      1 ⊗ₜ (ainfToAcris l (ϖ.ev a (b.coeff i)) * ainfToAcris l (ϖ.mu g * ϖ.teich) ^ i) := by
  let j : Per.Acris l →ₐ[ℤ_[l]] OCr l O := Algebra.TensorProduct.includeRight
  have hq : ∀ τ, rhoK K t τ (b.coeff i) ∈ S O K e := fun τ => by
    rw [rhoK_eq_toAc]; exact A_le_S l e (toAc t K _ τ).2
  have e1 : (N : ZMod a → S O K e) * (fun τ => ⟨_, hSp τ⟩) =
      (fun _ => uIn (S O K e)) ^ i * (i.factorial : ZMod a → S O K e) *
        fun τ => ⟨rhoK K t τ (b.coeff i), hq τ⟩ := funext fun τ => Subtype.ext (by
    have h2 := congrArg (fun G => coeff i (G τ)) hpb
    simp only [Pi.mul_apply, Pi.natCast_apply] at h2
    rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, coeff_iotaP_X] at h2
    simp only [Pi.mul_apply, Pi.natCast_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
      SubringClass.coe_natCast, coe_uIn]
    rw [← h2]; ring)
  have hA : (N : OCr l O) * ϖ.iC t K (fun τ => ⟨_, hSp τ⟩) =
      j (ainfToAcris l ϖ.teich) ^ i * (i.factorial : OCr l O) * j (ainfToAcris l (ϖ.ev a (b.coeff i))) := by
    rw [← map_natCast (ϖ.iC t K), ← map_mul, e1, map_mul, map_mul, map_pow, map_natCast, iC_u, iC_rhoK]
    rfl
  have h3 : (i.factorial : OCr l O) * ϖ.muDiv a O g i = j (ainfToAcris l (ϖ.mu g)) ^ i := by
    have h4 := congrArg j (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)
    rw [map_mul, map_natCast, map_pow] at h4
    exact h4
  rw [mul_left_comm, hA]
  change _ = j _
  rw [map_mul, map_pow, map_mul, map_mul]
  linear_combination (j (ainfToAcris l ϖ.teich) ^ i * j (ainfToAcris l (ϖ.ev a (b.coeff i)))) * h3

/- English proof (translation)
Set `j : Per.Acris l →ₐ[ℤ_[l]] OCr l O` to `Algebra.TensorProduct.includeRight`. Use `nat_cancel_OCr hN ?_` and prove the remaining obligations. Establish `e1 : (N : PPd t K e) * ⟨p, hp⟩ = iotaD K t b` using `Subtype.ext (by simpa [coe_iotaD] using hpb)`. Establish `e2 : (N : Per.Acris l) * evE t ϖ g ⟨p, hp⟩ = fP a ϖ (g : GQ l) b`. Rewrite using `[← map_natCast (evE (K := K) (e := e) t ϖ g), ← map_mul, e1, evE_iotaD]`.

Establish `e3 : fP a ϖ (g : GQ l) b = ∑ i ∈ Finset.range n, ainfToAcris l (ϖ.ev a (b.coeff i)) * ainfToAcris l (ϖ.mu g * ϖ.teich) ^ i`. Rewrite using `[fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' _ hn]`. Both sides reduce to the same expression. Establish `e4 : (N : OCr l O) * (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨p, hp⟩ = j (fP a ϖ (g : GQ l) b)`. Rewrite using `[← e2, map_mul, map_natCast]`.

Both sides reduce to the same expression. Rewrite using `[mul_sub, Finset.mul_sum, e4, Finset.sum_congr rfl fun i _ => taylor_term t ϖ g b p N hpb i (fun τ => hSp τ i), e3, map_sum]`. Conclude with `sub_eq_zero.2 (Finset.sum_congr rfl fun i _ => rfl)`.
-/
theorem taylor_poly (b : Bp l a) (p : ZMod a → K⟦X⟧⟦X⟧) (hp : p ∈ PPd t K e) (N : ℕ) (hN : N ≠ 0)
    (hpb : (N : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b)
    (hSp : ∀ τ i, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) ∈ S O K e) (n : ℕ) (hn : b.natDegree < n) :
    (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨p, hp⟩ -
      ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSp τ i⟩) = 0 := by
  let j : Per.Acris l →ₐ[ℤ_[l]] OCr l O := Algebra.TensorProduct.includeRight
  refine nat_cancel_OCr hN ?_
  have e1 : (N : PPd t K e) * ⟨p, hp⟩ = iotaD K t b := Subtype.ext (by simpa [coe_iotaD] using hpb)
  have e2 : (N : Per.Acris l) * evE t ϖ g ⟨p, hp⟩ = fP a ϖ (g : GQ l) b := by
    rw [← map_natCast (evE (K := K) (e := e) t ϖ g), ← map_mul, e1, evE_iotaD]
  have e3 : fP a ϖ (g : GQ l) b = ∑ i ∈ Finset.range n,
      ainfToAcris l (ϖ.ev a (b.coeff i)) * ainfToAcris l (ϖ.mu g * ϖ.teich) ^ i := by
    rw [fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' _ hn]
    rfl
  have e4 : (N : OCr l O) * (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨p, hp⟩ = j (fP a ϖ (g : GQ l) b) := by
    rw [← e2, map_mul, map_natCast]
    rfl
  rw [mul_sub, Finset.mul_sum, e4, Finset.sum_congr rfl fun i _ => taylor_term t ϖ g b p N hpb i (fun τ => hSp τ i),
    e3, map_sum]
  exact sub_eq_zero.2 (Finset.sum_congr rfl fun i _ => rfl)

/- English proof (translation)
Set `j : Per.Acris l →ₐ[ℤ_[l]] OCr l O` to `Algebra.TensorProduct.includeRight`. Take `⟨N, b, p, h, hN, hp, hh, hpb, hFeq⟩` from `GlobalTheory.T.exists_polynomial_approx_dividedTwoVariableSet l a e O K t F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t F hF) r`. Establish `hcoef : ∀ τ i, coeff i (F τ) = coeff i (p τ) + (l : K⟦X⟧) ^ r * coeff i (h τ)` using `fun τ i => by`. Establish `h1` using `congrFun hFeq τ`. Simplify using `only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply] at h1`.

Rewrite using `[h1, map_add, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_pow, coeff_C_mul]`. Establish `hSh : ∀ τ i, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (h τ)) ∈ S O K e` using `fun τ i => mul_mem (pow_mem HasU.X_mem i) (GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring l a e O K t h hh τ i)`. Establish `hSp : ∀ τ i, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) ∈ S O K e` using `fun τ i => by`. Establish `e1 : (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) = (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) - (l : K⟦X⟧) ^ r * ((X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (h τ)))`. Rewrite using `[hcoef]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `sub_mem (hS τ i) (mul_mem (pow_mem (natCast_mem _ l) r) (hSh τ i))`. Establish `hp' : p ∈ PPd t K e` using `Subring.subset_closure hp`. Establish `hh' : h ∈ PPd t K e` using `Subring.subset_closure hh`.

Establish `hsplit : ∀ i, ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) = ϖ.iC t K (fun τ => ⟨_, hSp τ i⟩) + (l : OCr l O) ^ r * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩)` using `fun i => by`. Establish `e1 : (fun τ => (⟨_, hS τ i⟩ : S O K e)) = (fun τ => (⟨_, hSp τ i⟩ : S O K e)) + (l : ZMod a → S O K e) ^ r * fun τ => ⟨_, hSh τ i⟩`. Use function extensionality and compare the values at `fun τ => Subtype.ext (by`. Simplify using `only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast]`. Rewrite using `[hcoef]`.

Use the proof step `ring)`. Rewrite using `[e1, map_add, map_mul, map_pow, map_natCast]`. Establish `hEsplit : (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨F, hF⟩ = (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨p, hp'⟩ + (l : OCr l O) ^ r * (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨h, hh'⟩`. Establish `e1 : (⟨F, hF⟩ : PPd t K e) = ⟨p, hp'⟩ + (l : PPd t K e) ^ r * ⟨h, hh'⟩` using `Subtype.ext (by simpa using hFeq)`. Rewrite using `[e1, map_add, map_mul, map_pow, map_natCast]`.

Express the relevant statement in the definitionally equal form `j _ = j _ + _ * j _`. Rewrite using `[map_add, map_mul, map_pow, map_natCast]`. Use `⟨b.natDegree + 1, fun n hn => ⟨(1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨h, hh'⟩ - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩), ?_⟩⟩` and prove the remaining obligations. Establish `hz` using `taylor_poly t ϖ g b p hp' N hN hpb hSp n (by omega)`. Establish `e4 : ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) = ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSp τ i⟩) + (l : OCr l O) ^ r * ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩)`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hsplit]; ring`. Rewrite using `[hEsplit, e4]`. Take the linear combination `hz`.
-/
theorem evE_taylor (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e)
    (hS : ∀ (τ : ZMod a) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) ∈ S O K e) (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨F, hF⟩ -
      ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) := by
  let j : Per.Acris l →ₐ[ℤ_[l]] OCr l O := Algebra.TensorProduct.includeRight
  obtain ⟨N, b, p, h, hN, hp, hh, hpb, hFeq⟩ :=
    GlobalTheory.T.exists_polynomial_approx_dividedTwoVariableSet l a e O K t F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t F hF) r
  have hcoef : ∀ τ i, coeff i (F τ) = coeff i (p τ) + (l : K⟦X⟧) ^ r * coeff i (h τ) := fun τ i => by
    have h1 := congrFun hFeq τ
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply] at h1
    rw [h1, map_add, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_pow, coeff_C_mul]
  have hSh : ∀ τ i, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (h τ)) ∈ S O K e := fun τ i =>
    mul_mem (pow_mem HasU.X_mem i) (GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring l a e O K t h hh τ i)
  have hSp : ∀ τ i, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) ∈ S O K e := fun τ i => by
    have e1 : (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) =
        (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) -
          (l : K⟦X⟧) ^ r * ((X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (h τ))) := by
      rw [hcoef]; ring
    rw [e1]
    exact sub_mem (hS τ i) (mul_mem (pow_mem (natCast_mem _ l) r) (hSh τ i))
  have hp' : p ∈ PPd t K e := Subring.subset_closure hp
  have hh' : h ∈ PPd t K e := Subring.subset_closure hh
  have hsplit : ∀ i, ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) =
      ϖ.iC t K (fun τ => ⟨_, hSp τ i⟩) + (l : OCr l O) ^ r * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩) := fun i => by
    have e1 : (fun τ => (⟨_, hS τ i⟩ : S O K e)) =
        (fun τ => (⟨_, hSp τ i⟩ : S O K e)) + (l : ZMod a → S O K e) ^ r * fun τ => ⟨_, hSh τ i⟩ :=
      funext fun τ => Subtype.ext (by
        simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Subalgebra.coe_add,
          Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast]
        rw [hcoef]; ring)
    rw [e1, map_add, map_mul, map_pow, map_natCast]
  have hEsplit : (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨F, hF⟩ = (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨p, hp'⟩ +
      (l : OCr l O) ^ r * (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨h, hh'⟩ := by
    have e1 : (⟨F, hF⟩ : PPd t K e) = ⟨p, hp'⟩ + (l : PPd t K e) ^ r * ⟨h, hh'⟩ := Subtype.ext (by simpa using hFeq)
    rw [e1, map_add, map_mul, map_pow, map_natCast]
    change j _ = j _ + _ * j _
    rw [map_add, map_mul, map_pow, map_natCast]
  refine ⟨b.natDegree + 1, fun n hn => ⟨(1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨h, hh'⟩ -
    ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩), ?_⟩⟩
  have hz := taylor_poly t ϖ g b p hp' N hN hpb hSp n (by omega)
  have e4 : ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) =
      ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSp τ i⟩) +
        (l : OCr l O) ^ r * ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hsplit]; ring
  rw [hEsplit, e4]
  linear_combination hz

end Main

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ sh hsh φ₂ hφC hφsh g` and use `⟨evE t ϖ g, fun x hx => by rw [evE_constP, PiSys.ev_frobS], fun x hx => evE_shP t ϖ g sh hsh x hx, fun F hF hF' => RingHom.congr_fun (evE_frob2 t ϖ g sh hsh φ₂ hφC hφsh) ⟨F, hF⟩, fun F hF hS r => evE_taylor t ϖ g F hF hS r⟩`.
-/
theorem evalPP : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ g : ↥(GK (ϖ.field a)), ∃ E : ↥(PPd t K e) →+* Per.Acris l, (∀ (x : (Wq l a)⟦X⟧) (hx : constP a K (inclS t K (frobS l a x)) ∈ PPd t K e), E ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (ϖ.ev a x))) ∧ (∀ (x : (Wq l a)⟦X⟧) (hx : shP a sh (inclS t K (frobS l a x)) ∈ PPd t K e), E ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a x)))) ∧ (∀ (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e) (hF' : frob2 φ₂ F ∈ PPd t K e), E ⟨_, hF'⟩ = frobC l (E ⟨F, hF⟩)) ∧ ∀ (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e) (hS : ∀ (τ : ZMod a) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) ∈ S O K e) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] E ⟨F, hF⟩ - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) :=
  fun l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ sh hsh φ₂ hφC hφsh g =>
    ⟨evE t ϖ g, fun x hx => by rw [evE_constP, PiSys.ev_frobS], fun x hx => evE_shP t ϖ g sh hsh x hx,
      fun F hF hF' => RingHom.congr_fun (evE_frob2 t ϖ g sh hsh φ₂ hφC hφsh) ⟨F, hF⟩,
      fun F hF hS r => evE_taylor t ϖ g F hF hS r⟩

end GlobalTheory.CrysEval
