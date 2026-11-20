import Mathlib
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylRowAll

def coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R) (F : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (c (coeff m F))

/- English proof (translation)
Simplify using `only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.mp h, map_zero]`.
-/
theorem coeff_coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R)
    (F : MvPolynomial σ S) (m : σ →₀ ℕ) : coeff m (coeffMap c F) = c (coeff m F) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

/- English proof (translation)
Establish `key : ∀ s : S, coeffMap c (s • F) ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν`. Unfold `Formalism.GradedWeylDivisibility.weyl at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`.

Introduce `s`. Establish `: coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) = c s • Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)`. Use extensionality with `m`. Rewrite using `[coeff_coeffMap, ← Formalism.GradedWeylDivisibility.lclosedeq_hw_map φ, Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, coeff_smul, coeff_smul, coeff_map, smul_eq_mul, smul_eq_mul, hc]`. Use `show coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) ∈ _`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)`. Consider the case `zero`. Introduce `s`. Establish `: coeffMap c (s • (0 : MvPolynomial (Fin r × Fin n) S)) = 0`.

Use extensionality with `m`. Simplify using `[coeff_coeffMap]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`.

Introduce `s`. Establish `: coeffMap c (s • (x + y)) = coeffMap c (s • x) + coeffMap c (s • y)`. Use extensionality with `m`. Simplify using `[coeff_coeffMap, mul_add]`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ (hx s) (hy s)`. Consider the case `smul a x _ hx`. Introduce `s`. Rewrite using `[smul_smul]`. Conclude with `hx _`.

Simplify using `using key 1`.
-/
theorem coeffMap_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : S →+ R)
    (hc : ∀ (s : S) (a : R), c (s * φ a) = c s * a) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) S) (hF : F ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν) :
    coeffMap c F ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  have key : ∀ s : S, coeffMap c (s • F) ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
    unfold Formalism.GradedWeylDivisibility.weyl at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      intro s
      have : coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) =
          c s • Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) := by
        ext m
        rw [coeff_coeffMap, ← Formalism.GradedWeylDivisibility.lclosedeq_hw_map φ, Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
          coeff_smul, coeff_smul, coeff_map, smul_eq_mul, smul_eq_mul, hc]
      show coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
    | zero =>
      intro s
      have : coeffMap c (s • (0 : MvPolynomial (Fin r × Fin n) S)) = 0 := by
        ext m; simp [coeff_coeffMap]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro s
      have : coeffMap c (s • (x + y)) = coeffMap c (s • x) + coeffMap c (s • y) := by
        ext m; simp [coeff_coeffMap, mul_add]
      rw [this]; exact Submodule.add_mem _ (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [smul_smul]; exact hx _
  simpa using key 1

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.weyl at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Use `show map φ (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ∈ _`.

Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`. Conclude with `Submodule.subset_span ⟨w, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem map_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    map φ f ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    show map φ (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ∈ _
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [Formalism.GradedWeylDivisibility.rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, map_X]`.

Use `congr 1`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct]`.
-/
theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.rowAct R g f) = Formalism.GradedWeylDivisibility.rowAct S (g.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct]

def toInv (R : Type) [CommRing R] : Polynomial R →+* HahnSeries ℤ R :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℤ) (1 : R))

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial k a`. Simplify using `only [toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Polynomial.eval_monomial, HahnSeries.single_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]`. Break down `k with _ | k` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[HahnSeries.coeff_single_of_ne]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_zero_toInv (R : Type) [CommRing R] (p : Polynomial R) :
    (toInv R p).coeff 0 = p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
    simp only [toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      Polynomial.eval_monomial, HahnSeries.single_pow, HahnSeries.C_apply,
      HahnSeries.single_mul_single]
    rcases k with _ | k
    · simp
    · rw [HahnSeries.coeff_single_of_ne]
      · simp
      · simp; omega

/- English proof (translation)
Use `set A : Matrix (Fin r) (Fin r) (PowerSeries R) := 1 + (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C with hA`. Establish `h1 : IsUnit A.det`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]`. Establish `: (PowerSeries.constantCoeff (R` using `R)).mapMatrix A = 1 := by`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [hA, Matrix.one_apply, h]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `h2 : IsUnit (A.map (HahnSeries.ofPowerSeries ℤ R)).det`. Use `h1.map (HahnSeries.ofPowerSeries ℤ R)` as an intermediate fact.

Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `hT : (HahnSeries.single (-1 : ℤ) (1 : R)) * HahnSeries.single (1 : ℤ) (1 : R) = 1`. Rewrite using `[HahnSeries.single_mul_single]`. Simplify using the standard rewrite rules. Establish `h3 : ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map (toInv R)) = (HahnSeries.single (-1 : ℤ) (1 : R)) • A.map (HahnSeries.ofPowerSeries ℤ R)`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [hA, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C, mul_add, ← mul_assoc, hT, one_mul, toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X, Matrix.one_apply]`. Rewrite using `[add_comm]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, h3, Matrix.det_smul]`.

Conclude with `((IsUnit.of_mul_eq_one _ hT).pow _).mul h2`.
-/
theorem isUnit_shift (R : Type) [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    IsUnit ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) := by
  set A : Matrix (Fin r) (Fin r) (PowerSeries R) :=
    1 + (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C with hA
  have h1 : IsUnit A.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have : (PowerSeries.constantCoeff (R := R)).mapMatrix A = 1 := by
      ext i j
      by_cases h : i = j <;> simp [hA, Matrix.one_apply, h]
    rw [this]; simp
  have h2 : IsUnit (A.map (HahnSeries.ofPowerSeries ℤ R)).det := by
    have := h1.map (HahnSeries.ofPowerSeries ℤ R)
    rwa [RingHom.map_det] at this
  have hT : (HahnSeries.single (-1 : ℤ) (1 : R)) * HahnSeries.single (1 : ℤ) (1 : R) = 1 := by
    rw [HahnSeries.single_mul_single]; simp
  have h3 : ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) = (HahnSeries.single (-1 : ℤ) (1 : R)) • A.map (HahnSeries.ofPowerSeries ℤ R) := by
    refine Matrix.ext fun i j => ?_
    simp only [hA, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      map_mul, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C, mul_add, ← mul_assoc, hT,
      one_mul, toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Matrix.one_apply]
    rw [add_comm]
    split_ifs <;> simp
  rw [Matrix.isUnit_iff_isUnit_det, h3, Matrix.det_smul]
  exact ((IsUnit.of_mul_eq_one _ hT).pow _).mul h2

/- English proof (translation)
Use `set B : Matrix (Fin r) (Fin r) (Polynomial R) := M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _) with hB`. Take `⟨u, hu⟩` from `isUnit_shift R M`. Establish `h1` using `Formalism.UG.Final.WeylGLStable (HahnSeries ℤ R) r n hn ν u⁻¹ _ (map_mem_weyl (toInv R) hn ν _ (map_mem_weyl Polynomial.C hn ν f hf))`. Rewrite `h1` using `[Formalism.UG.dwAct, inv_inv, hu, ← hB, ← map_rowAct]`. Establish `h2` using `coeffMap_mem_weyl (HahnSeries.C : R →+* HahnSeries ℤ R) (HahnSeries.coeff.addMonoidHom (0 : ℤ)) (by`.

Introduce `s a`. Simplify using `[HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]) hn ν _ h1`. Establish `h3 : coeffMap (HahnSeries.coeff.addMonoidHom (0 : ℤ)) (map (toInv R) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f))) = map (Polynomial.evalRingHom (0 : R)) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f))`. Use extensionality with `m`. Rewrite using `[coeff_coeffMap, coeff_map, coeff_map]`.

Conclude with `coeff_zero_toInv R _`. Establish `h4 : B.map (Polynomial.evalRingHom (0 : R)) = M`. Use extensionality with `i j`. Simplify using `[hB]`. Establish `h5 : map (Polynomial.evalRingHom (0 : R)) (map Polynomial.C f) = f`.

Use extensionality with `m`. Simplify using `[coeff_map]`. Rewrite `h2` using `[h3, map_rowAct, h4, h5]`. Then use the resulting hypothesis.
-/
theorem rowAct_mem_weyl (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) : Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  set B : Matrix (Fin r) (Fin r) (Polynomial R) :=
    M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _) with hB
  obtain ⟨u, hu⟩ := isUnit_shift R M
  have h1 := Formalism.UG.Final.WeylGLStable (HahnSeries ℤ R) r n hn ν u⁻¹ _
    (map_mem_weyl (toInv R) hn ν _ (map_mem_weyl Polynomial.C hn ν f hf))
  rw [Formalism.UG.dwAct, inv_inv, hu, ← hB, ← map_rowAct] at h1
  have h2 := coeffMap_mem_weyl (HahnSeries.C : R →+* HahnSeries ℤ R)
    (HahnSeries.coeff.addMonoidHom (0 : ℤ)) (by
      intro s a
      simp [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]) hn ν _ h1
  have h3 : coeffMap (HahnSeries.coeff.addMonoidHom (0 : ℤ))
      (map (toInv R) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f))) =
      map (Polynomial.evalRingHom (0 : R)) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f)) := by
    ext m
    rw [coeff_coeffMap, coeff_map, coeff_map]
    exact coeff_zero_toInv R _
  have h4 : B.map (Polynomial.evalRingHom (0 : R)) = M := by
    ext i j
    simp [hB]
  have h5 : map (Polynomial.evalRingHom (0 : R)) (map Polynomial.C f) = f := by
    ext m
    simp [coeff_map]
  rwa [h3, map_rowAct, h4, h5] at h2

/- English proof (translation)
Introduce `R _ _ ν _ M f hf` and use `rowAct_mem_weyl R le_rfl ν M f hf`.
-/
theorem rowAct_mem_weyl_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν,
      Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν :=
  fun R _ _ ν _ M f hf => rowAct_mem_weyl R le_rfl ν M f hf

end GlobalTheory.WeylRowAll
