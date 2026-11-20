import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiffSmulMem

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise nonZeroDivisors

noncomputable section

namespace GlobalTheory.GaloisTwist

section General

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_gal_smul (σ : E ≃ₐ[ℚ] E) (z : 𝓞 E) :
    algebraMap (𝓞 E) E (σ • z) = σ (algebraMap (𝓞 E) E z) := rfl

/- English proof (translation)
Take `⟨r, rfl⟩` from `hx`. Conclude with `⟨σ • r, rfl⟩`.
-/
theorem map_mem_range (σ : E ≃ₐ[ℚ] E) {x : E} (hx : x ∈ (algebraMap (𝓞 E) E).range) :
    σ x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨σ • r, rfl⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp, Pi.smul_apply, Algebra.smul_def, map_mul, coe_gal_smul]`.
-/
theorem comp_int_smul (σ : E ≃ₐ[ℚ] E) {N : ℕ} (r : 𝓞 E) (v : Fin N → E) :
    (σ ∘ (r • v) : Fin N → E) = (σ • r) • (σ ∘ v) := by
  funext i
  simp only [Function.comp, Pi.smul_apply, Algebra.smul_def, map_mul, coe_gal_smul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, map_mul, coe_gal_smul]`.
-/
theorem map_int_smul (σ : E ≃ₐ[ℚ] E) {N N' : ℕ} (r : 𝓞 E) (A : Matrix (Fin N') (Fin N) E) :
    (r • A).map σ = (σ • r) • A.map σ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, map_mul, coe_gal_smul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem comp_mulVec (σ : E ≃ₐ[ℚ] E) {N N' : ℕ} (A : Matrix (Fin N') (Fin N) E) (v : Fin N → E) :
    (σ ∘ (A.mulVec v) : Fin N' → E) = (A.map σ).mulVec (σ ∘ v) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Establish `hB : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]`. Establish `hB' : ((σ • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Introduce `h`. Apply `hJ` to reduce the goal to its premises.

Rewrite using `[← inv_smul_smul σ J, h]`. Simplify using the standard rewrite rules. Rewrite `hx` using `[FractionalIdeal.mem_div_iff_of_ne_zero hB]`. Rewrite using `[FractionalIdeal.mem_div_iff_of_ne_zero hB']`. Introduce `y hy`.

Take `⟨z, hz, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hy`. Establish `hz0 : σ⁻¹ • z ∈ J` using `Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hz`. Take `⟨w, hw, hw'⟩` from `(FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hz0, rfl⟩))`. Use `(FractionalIdeal.mem_coeIdeal _).2 ⟨σ • w, Ideal.smul_mem_pointwise_smul _ _ _ hw, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_gal_smul, hw', map_mul, ← coe_gal_smul, smul_inv_smul]`.
-/
theorem map_mem_div (σ : E ≃ₐ[ℚ] E) {I J : Ideal (𝓞 E)} (hJ : J ≠ ⊥) {x : E}
    (hx : x ∈ (I : FractionalIdeal (𝓞 E)⁰ E) / (J : FractionalIdeal (𝓞 E)⁰ E)) :
    σ x ∈ ((σ • I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) /
      ((σ • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
  have hB : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  have hB' : ((σ • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    intro h
    apply hJ
    rw [← inv_smul_smul σ J, h]
    simp
  rw [FractionalIdeal.mem_div_iff_of_ne_zero hB] at hx
  rw [FractionalIdeal.mem_div_iff_of_ne_zero hB']
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have hz0 : σ⁻¹ • z ∈ J := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hz
  obtain ⟨w, hw, hw'⟩ := (FractionalIdeal.mem_coeIdeal _).1
    (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hz0, rfl⟩))
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨σ • w, Ideal.smul_mem_pointwise_smul _ _ _ hw, ?_⟩
  rw [coe_gal_smul, hw', map_mul, ← coe_gal_smul, smul_inv_smul]

variable [StarRing E]

def twist (σ : E ≃ₐ[ℚ] E) (C : Set E) {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) :
    Submodule (𝓞 E) (Fin N → E) where
  carrier := {v | ∀ c ∈ C, (σ.symm ∘ (star c • v) : Fin N → E) ∈ L}
  add_mem' := by
    intro v w hv hw c hc
    have := L.add_mem (hv c hc) (hw c hc)
    convert this using 1
    funext i
    simp [mul_add]
  zero_mem' := by
    intro c hc
    convert L.zero_mem using 1
    funext i
    simp
  smul_mem' := by
    intro r v hv c hc
    rw [smul_comm, comp_int_smul]
    exact L.smul_mem _ (hv c hc)

/- English proof (translation)
Introduce `c hc`. Take `⟨r, hr⟩` from `h1 c hc d hd`. Rewrite using `[smul_smul, ← hr, algebraMap_smul, comp_int_smul]`. Use `L.smul_mem _ ?_` and prove the remaining obligations. Use `hu using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem smul_mem_twist (σ : E ≃ₐ[ℚ] E) {C : Set E}
    (h1 : ∀ c ∈ C, ∀ d ∈ C, star c * d ∈ (algebraMap (𝓞 E) E).range) {N : ℕ}
    {L : Submodule (𝓞 E) (Fin N → E)} {d : E} (hd : d ∈ C) {u : Fin N → E} (hu : u ∈ L) :
    d • (σ ∘ u : Fin N → E) ∈ twist σ C L := by
  intro c hc
  obtain ⟨r, hr⟩ := h1 c hc d hd
  rw [smul_smul, ← hr, algebraMap_smul, comp_int_smul]
  refine L.smul_mem _ ?_
  convert hu using 1
  funext i
  simp

/- English proof (translation)
Establish `hdec : ∀ v : Fin N → E, v = ∑ i, d i • (σ ∘ (σ.symm ∘ (star (c i) • v) : Fin N → E) : Fin N → E)`. Introduce `v`. Use function extensionality and compare the values at `k`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp, AlgEquiv.apply_symm_apply, smul_eq_mul]`. Use `conv_lhs => rw [← one_mul (v k), ← h2, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `hH : ∀ (a : E) (u y : Fin N → E), stdH E N (a • (σ ∘ u : Fin N → E)) y = σ (stdH E N u (σ.symm ∘ (star a • y)))`. Introduce `a u y`. Simplify using `only [stdH, map_sum, map_mul, hs, Function.comp, Pi.smul_apply, smul_eq_mul, AlgEquiv.apply_symm_apply, star_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Take `⟨⟨s, hs'⟩, hspan, hdual⟩` from `hL`. Use `⟨?_, ?_, fun y => ⟨fun hy x hx => ?_, fun hy a ha => ?_⟩⟩` and prove the remaining obligations. Establish `hfin : (⋃ i, (fun u : Fin N → E => d i • (σ ∘ u : Fin N → E)) '' (s : Set (Fin N → E))).Finite` using `Set.finite_iUnion fun i => s.finite_toSet.image _`. Use `Submodule.FG.of_le (Submodule.fg_span hfin) fun v hv => ?_` and prove the remaining obligations. Rewrite using `[hdec v]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hu` using `hv (c i) (hc i)`. Generalize the expression as in `(σ.symm ∘ (star (c i) • v) : Fin N → E) = u at hu`. Rewrite `hu` using `[← hs']`. Proceed by induction on `hu using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy`. Use `Submodule.add_mem _ hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[mul_add]`. Consider the case `smul r x _ hx`.

Rewrite using `[comp_int_smul, smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `key : ∀ u ∈ Submodule.span E (L : Set (Fin N → E)), (σ ∘ u : Fin N → E) ∈ Submodule.span E (twist σ C L : Set (Fin N → E))`. Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`.

Consider the case `mem x hx`. Establish `: (σ ∘ x : Fin N → E) = ∑ i, star (c i) • d i • (σ ∘ x : Fin N → E)`. Simplify using `only [smul_smul]`. Rewrite using `[← Finset.sum_smul, h2, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (smul_mem_twist σ h1 (hd i) hx))`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy`. Use `Submodule.add_mem _ hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Consider the case `smul r x _ hx`.

Use `Submodule.smul_mem _ (σ r) hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Use `key (σ.symm ∘ v) (hspan ▸ Submodule.mem_top)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Establish `hsum : stdH E N x y = ∑ i, stdH E N (d i • (σ ∘ (σ.symm ∘ (star (c i) • x) : Fin N → E) : Fin N → E)) y` using `by conv_lhs => rw [hdec x]`.

Simplify using `only [stdH, Finset.sum_apply, star_sum, Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Rewrite using `[hsum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hH]`.

Conclude with `map_mem_range σ ((hdual _).1 (hy _ (hd i)) _ (hx _ (hc i)))`. Use `(hdual _).2 fun u hu => ?_` and prove the remaining obligations. Use `map_mem_range σ.symm (hy _ (smul_mem_twist σ h1 ha hu))` as an intermediate fact. Rewrite `this` using `[hH, AlgEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem isSDLat_twist (σ : E ≃ₐ[ℚ] E) (hs : ∀ x, σ (star x) = star (σ x)) {C : Set E}
    (h1 : ∀ c ∈ C, ∀ d ∈ C, star c * d ∈ (algebraMap (𝓞 E) E).range)
    {ι : Type} [Fintype ι] {c d : ι → E} (hc : ∀ i, c i ∈ C) (hd : ∀ i, d i ∈ C)
    (h2 : ∑ i, star (c i) * d i = 1) {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)}
    (hL : IsSDLat E N L) : IsSDLat E N (twist σ C L) := by
  have hdec : ∀ v : Fin N → E,
      v = ∑ i, d i • (σ ∘ (σ.symm ∘ (star (c i) • v) : Fin N → E) : Fin N → E) := by
    intro v
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, AlgEquiv.apply_symm_apply, smul_eq_mul]
    conv_lhs => rw [← one_mul (v k), ← h2, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hH : ∀ (a : E) (u y : Fin N → E), stdH E N (a • (σ ∘ u : Fin N → E)) y =
      σ (stdH E N u (σ.symm ∘ (star a • y))) := by
    intro a u y
    simp only [stdH, map_sum, map_mul, hs, Function.comp, Pi.smul_apply, smul_eq_mul,
      AlgEquiv.apply_symm_apply, star_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨⟨s, hs'⟩, hspan, hdual⟩ := hL
  refine ⟨?_, ?_, fun y => ⟨fun hy x hx => ?_, fun hy a ha => ?_⟩⟩
  · have hfin : (⋃ i, (fun u : Fin N → E => d i • (σ ∘ u : Fin N → E)) '' (s : Set (Fin N → E))).Finite :=
      Set.finite_iUnion fun i => s.finite_toSet.image _
    refine Submodule.FG.of_le (Submodule.fg_span hfin) fun v hv => ?_
    rw [hdec v]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hu := hv (c i) (hc i)
    generalize (σ.symm ∘ (star (c i) • v) : Fin N → E) = u at hu
    rw [← hs'] at hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)
    | zero =>
      convert Submodule.zero_mem _ using 1
      funext k; simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      funext k; simp [mul_add]
    | smul r x _ hx =>
      rw [comp_int_smul, smul_comm]
      exact Submodule.smul_mem _ _ hx
  · have key : ∀ u ∈ Submodule.span E (L : Set (Fin N → E)),
        (σ ∘ u : Fin N → E) ∈ Submodule.span E (twist σ C L : Set (Fin N → E)) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        have : (σ ∘ x : Fin N → E) = ∑ i, star (c i) • d i • (σ ∘ x : Fin N → E) := by
          simp only [smul_smul]
          rw [← Finset.sum_smul, h2, one_smul]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span (smul_mem_twist σ h1 (hd i) hx))
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext k; simp
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy using 1
        funext k; simp
      | smul r x _ hx =>
        convert Submodule.smul_mem _ (σ r) hx using 1
        funext k; simp
    rw [eq_top_iff]
    intro v _
    have := key (σ.symm ∘ v) (hspan ▸ Submodule.mem_top)
    convert this using 1
    funext k; simp
  · have hsum : stdH E N x y = ∑ i, stdH E N
        (d i • (σ ∘ (σ.symm ∘ (star (c i) • x) : Fin N → E) : Fin N → E)) y := by
      conv_lhs => rw [hdec x]
      simp only [stdH, Finset.sum_apply, star_sum, Finset.sum_mul]
      exact Finset.sum_comm
    rw [hsum]
    refine sum_mem fun i _ => ?_
    rw [hH]
    exact map_mem_range σ ((hdual _).1 (hy _ (hd i)) _ (hx _ (hc i)))
  · refine (hdual _).2 fun u hu => ?_
    have := map_mem_range σ.symm (hy _ (smul_mem_twist σ h1 ha hu))
    rwa [hH, AlgEquiv.symm_apply_apply] at this

end General

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA => exact hA x hx`. Consider the case `zero => simp`. Consider the case `add A B _ _ h h' => rw [Matrix.add_mulVec]`.

Conclude with `L'.add_mem h h'`. Consider the case `smul r A _ h => rw [Matrix.smul_mulVec]`. Conclude with `L'.smul_mem r h`.
-/
theorem mem_homL (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') : ∀ x ∈ L, A.mulVec x ∈ L' := by
  intro x hx
  induction hA using Submodule.span_induction with
  | mem A hA => exact hA x hx
  | zero => simp
  | add A B _ _ h h' => rw [Matrix.add_mulVec]; exact L'.add_mem h h'
  | smul r A _ h => rw [Matrix.smul_mulVec]; exact L'.smul_mem r h

/- English proof (translation)
Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem B hB`. Take `⟨a, ha, A, hA, rfl⟩` from `hB`. Conclude with `h a ha A (mem_homL D hA)`. Consider the case `zero`.

Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using the standard rewrite rules. Consider the case `add A B _ _ h h'`. Use `Submodule.add_mem _ h h' using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Consider the case `smul r A _ h`. Rewrite using `[map_int_smul]`. Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem map_mem_YYl (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) {N N' : ℕ}
    {L M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : ∀ a ∈ D.host.AA0, ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L, A.mulVec x ∈ L') →
      (a • A).map σ ∈ YYl D M M')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L') : A.map σ ∈ YYl D M M' := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact h a ha A (mem_homL D hA)
  | zero =>
    convert Submodule.zero_mem _ using 1
    ext i j; simp
  | add A B _ _ h h' =>
    convert Submodule.add_mem _ h h' using 1
    ext i j; simp
  | smul r A _ h =>
    rw [map_int_smul]
    exact Submodule.smul_mem _ _ h

/- English proof (translation)
Apply `(D.host.gal).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, mul_comm]`.
-/
theorem gal_comm (D : D7) (σ τ : D.host.E ≃ₐ[ℚ] D.host.E) : σ * τ = τ * σ := by
  apply (D.host.gal).injective
  rw [map_mul, map_mul, mul_comm]

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `h : ∀ x : D.host.E, star x = D.host.conj x` using `bridge_star_holds D.R D.host`. Use extensionality with `x`. Rewrite using `[AlgEquiv.mul_apply, ← h, ← h, star_star]`. Both sides reduce to the same expression.
-/
theorem conj_mul_conj (D : D7) : D.host.conj * D.host.conj = 1 := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  ext x
  rw [AlgEquiv.mul_apply, ← h, ← h, star_star]
  rfl

/- English proof (translation)
Use `set b : Ideal (𝓞 D.host.E) := D.host.𝔟 with hb`. Use `set k := D.host.conj with hk`. Establish `hkk : k * k = 1` using `conj_mul_conj D`. Establish `hne : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥` using `differentIdeal_ne_bot`. Establish `hspec : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = b * (k • b)` using `D.host.𝔟_spec.1`.

Establish `hfix : σ • differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)` using `Formalism.HC.Der.kc_diff_smul_eq D.host.toHostRaw σ`. Rewrite `hfix` using `[hspec, smul_mul', smul_smul, gal_comm D σ k, ← smul_smul]`. Establish `hne'` using `hne`. Rewrite `hne`, `hne'` using `[hspec]`. Rewrite `hne'` using `[← hfix]`.

Establish `n1 : b ≠ ⊥` using `left_ne_zero_of_mul hne`. Establish `n2 : k • b ≠ ⊥` using `right_ne_zero_of_mul hne`. Establish `n3 : σ • b ≠ ⊥` using `left_ne_zero_of_mul hne'`. Establish `n4 : k • σ • b ≠ ⊥` using `right_ne_zero_of_mul hne'`. Establish `hfix'` using `congrArg (fun I : Ideal (𝓞 D.host.E) => (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) hfix`.

Simplify using `only [FractionalIdeal.coeIdeal_mul] at hfix'`. Establish `g1` using `fun x => map_mem_div k (I := b) n3 (x := x)`. Establish `g2` using `fun x => map_mem_div k (I := k • b) n4 (x := x)`. Establish `g3` using `fun x => map_mem_div σ (I := ⊤) n1 (x := x)`. Establish `g4` using `fun x => map_mem_div σ⁻¹ (I := ⊤) n3 (x := x)`.

Establish `htop : ∀ s : D.host.E ≃ₐ[ℚ] D.host.E, s • (⊤ : Ideal (𝓞 D.host.E)) = ⊤` using `fun s => by`. Rewrite using `[← Ideal.one_eq_top, smul_one]`. Simplify using `only [smul_smul k k, hkk, one_smul] at g2`. Rewrite `g3` using `[htop, FractionalIdeal.coeIdeal_top, one_div, one_div]`. Rewrite `g4` using `[htop, inv_smul_smul, FractionalIdeal.coeIdeal_top, one_div, one_div]`.

Establish `hA : D.host.AA0 = ((b : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹` using `rfl`. Rewrite using `[hA]`. Rewrite `n1`, `n2`, `n3`, `n4` using `[Ne, ← FractionalIdeal.coeIdeal_eq_zero (K := D.host.E)]`. Generalize the expression as in `((k • σ • b : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = Z at *`. Generalize the expression as in `((σ • b : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = Y at *`.

Generalize the expression as in `((k • b : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = X at *`. Generalize the expression as in `((b : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = B at *`. Establish `e0 : X / Z = Y / B`. Rewrite using `[div_eq_div_iff n4 n1, hfix', mul_comm]`. Rewrite `g1`, `g2` using `[e0]`.

Establish `e1 : Y / B * (B / Y) = 1` using `by field_simp`. Establish `e2 : Y⁻¹ * (Y / B) = B⁻¹` using `by field_simp`. Establish `e3 : B⁻¹ * (B / Y) = Y⁻¹` using `by field_simp`. Use `⟨{x | x ∈ B / Y}, fun c hc d hd => ?_, ?_, fun a ha c hc => ?_, fun a ha d hd => ?_⟩` and prove the remaining obligations. Use `FractionalIdeal.mul_mem_mul (g1 c hc) hd` as an intermediate fact.

Rewrite `this` using `[e1, FractionalIdeal.mem_one_iff]`. Conclude with `this`. Establish `h1 : (1 : D.host.E) ∈ ((Y / B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) * ((B / Y : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)`. Rewrite using `[← FractionalIdeal.coe_mul, e1]`. Conclude with `FractionalIdeal.one_mem_one _`.

Generalize the expression as in `(1 : D.host.E) = t at h1`. Use `Submodule.mul_induction_on h1 (fun m hm n hn => ?_) ?_` and prove the remaining obligations. Use `⟨Unit, inferInstance, fun _ => k m, fun _ => n, fun _ => g2 m hm, fun _ => hn, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_const, ← AlgEquiv.mul_apply, hkk]`. Simplify using the standard rewrite rules.

Introduce and unpack `x y ⟨ι, _, c, d, hc, hd, rfl⟩ ⟨ι', _, c', d', hc', hd', rfl⟩`. Use `⟨ι ⊕ ι', inferInstance, Sum.elim c c', Sum.elim d d', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | i)`. Use `exacts [hc i, hc' i]`. Introduce and unpack `(i | i)`.

Use `exacts [hd i, hd' i]`. Simplify using `[Fintype.sum_sum_type]`. Rewrite using `[← e2]`. Conclude with `FractionalIdeal.mul_mem_mul (g3 a ha) (g1 c hc)`. Use `g4 _ ?_` and prove the remaining obligations.

Rewrite using `[← e3]`. Conclude with `FractionalIdeal.mul_mem_mul ha hd`.
-/
theorem exists_twisting_ideal (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) :
    ∃ C : Set D.host.E,
      (∀ c ∈ C, ∀ d ∈ C, D.host.conj c * d ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      (∃ (ι : Type) (_ : Fintype ι) (c d : ι → D.host.E), (∀ i, c i ∈ C) ∧ (∀ i, d i ∈ C) ∧
        ∑ i, D.host.conj (c i) * d i = 1) ∧
      (∀ a ∈ D.host.AA0, ∀ c ∈ C, σ a * D.host.conj c ∈ D.host.AA0) ∧
      (∀ a ∈ D.host.AA0, ∀ d ∈ C, σ.symm (a * d) ∈ D.host.AA0) := by
  set b : Ideal (𝓞 D.host.E) := D.host.𝔟 with hb
  set k := D.host.conj with hk
  have hkk : k * k = 1 := conj_mul_conj D
  have hne : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hspec : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = b * (k • b) := D.host.𝔟_spec.1
  have hfix : σ • differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) :=
    Formalism.HC.Der.kc_diff_smul_eq D.host.toHostRaw σ
  rw [hspec, smul_mul', smul_smul, gal_comm D σ k, ← smul_smul] at hfix
  have hne' := hne
  rw [hspec] at hne hne'
  rw [← hfix] at hne'
  have n1 : b ≠ ⊥ := left_ne_zero_of_mul hne
  have n2 : k • b ≠ ⊥ := right_ne_zero_of_mul hne
  have n3 : σ • b ≠ ⊥ := left_ne_zero_of_mul hne'
  have n4 : k • σ • b ≠ ⊥ := right_ne_zero_of_mul hne'
  have hfix' := congrArg (fun I : Ideal (𝓞 D.host.E) => (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) hfix
  simp only [FractionalIdeal.coeIdeal_mul] at hfix'
  have g1 := fun x => map_mem_div k (I := b) n3 (x := x)
  have g2 := fun x => map_mem_div k (I := k • b) n4 (x := x)
  have g3 := fun x => map_mem_div σ (I := ⊤) n1 (x := x)
  have g4 := fun x => map_mem_div σ⁻¹ (I := ⊤) n3 (x := x)
  have htop : ∀ s : D.host.E ≃ₐ[ℚ] D.host.E, s • (⊤ : Ideal (𝓞 D.host.E)) = ⊤ := fun s => by
    rw [← Ideal.one_eq_top, smul_one]
  simp only [smul_smul k k, hkk, one_smul] at g2
  rw [htop, FractionalIdeal.coeIdeal_top, one_div, one_div] at g3
  rw [htop, inv_smul_smul, FractionalIdeal.coeIdeal_top, one_div, one_div] at g4
  have hA : D.host.AA0 = ((b : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ := rfl
  rw [hA]
  rw [Ne, ← FractionalIdeal.coeIdeal_eq_zero (K := D.host.E)] at n1 n2 n3 n4
  generalize ((k • σ • b : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = Z at *
  generalize ((σ • b : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = Y at *
  generalize ((k • b : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = X at *
  generalize ((b : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = B at *
  have e0 : X / Z = Y / B := by
    rw [div_eq_div_iff n4 n1, hfix', mul_comm]
  rw [e0] at g1 g2
  have e1 : Y / B * (B / Y) = 1 := by field_simp
  have e2 : Y⁻¹ * (Y / B) = B⁻¹ := by field_simp
  have e3 : B⁻¹ * (B / Y) = Y⁻¹ := by field_simp
  refine ⟨{x | x ∈ B / Y}, fun c hc d hd => ?_, ?_, fun a ha c hc => ?_, fun a ha d hd => ?_⟩
  · have := FractionalIdeal.mul_mem_mul (g1 c hc) hd
    rw [e1, FractionalIdeal.mem_one_iff] at this
    exact this
  · have h1 : (1 : D.host.E) ∈ ((Y / B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) * ((B / Y : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
      rw [← FractionalIdeal.coe_mul, e1]
      exact FractionalIdeal.one_mem_one _
    generalize (1 : D.host.E) = t at h1
    refine Submodule.mul_induction_on h1 (fun m hm n hn => ?_) ?_
    · refine ⟨Unit, inferInstance, fun _ => k m, fun _ => n, fun _ => g2 m hm, fun _ => hn, ?_⟩
      rw [Finset.sum_const, ← AlgEquiv.mul_apply, hkk]
      simp
    · rintro x y ⟨ι, _, c, d, hc, hd, rfl⟩ ⟨ι', _, c', d', hc', hd', rfl⟩
      refine ⟨ι ⊕ ι', inferInstance, Sum.elim c c', Sum.elim d d', ?_, ?_, ?_⟩
      · rintro (i | i); exacts [hc i, hc' i]
      · rintro (i | i); exacts [hd i, hd' i]
      · simp [Fintype.sum_sum_type]
  · rw [← e2]
    exact FractionalIdeal.mul_mem_mul (g3 a ha) (g1 c hc)
  · refine g4 _ ?_
    rw [← e3]
    exact FractionalIdeal.mul_mem_mul ha hd

/- English proof (translation)
Introduce `D σ _ N N' L L' hL hL'`. Use `letI := D.host.cmStar`. Establish `h : ∀ x : D.host.E, star x = D.host.conj x` using `bridge_star_holds D.R D.host`. Take `⟨C, h1, ⟨ι, _, c, d, hc, hd, h2⟩, h3, h4⟩` from `exists_twisting_ideal D σ`. Simplify using `only [← h] at h1 h2 h3`.

Establish `hs : ∀ x, σ (star x) = star (σ x)` using `fun x => by`. Rewrite using `[h, h, ← AlgEquiv.mul_apply, gal_comm, AlgEquiv.mul_apply]`. Establish `h0 : ∀ c ∈ ({1} : Set D.host.E), ∀ d ∈ ({1} : Set D.host.E), star c * d ∈ (algebraMap (𝓞 D.host.E) D.host.E).range`. Introduce and unpack `_ rfl _ rfl`. Conclude with `⟨1, by simp⟩`.

Use `⟨twist σ {1} L, twist σ C L', isSDLat_twist σ hs h0 (ι := Unit) (c := fun _ => 1) (d := fun _ => 1) (fun _ => rfl) (fun _ => rfl) (by simp) hL, isSDLat_twist σ hs h1 hc hd h2 hL', fun A => ⟨fun hA => ?_, fun hA => ?_⟩⟩` and prove the remaining obligations. Use `map_mem_YYl D σ (fun a ha A hA => ?_) hA` and prove the remaining obligations. Establish `e : (a • A).map σ = ∑ i, (σ a * star (c i)) • (d i • A.map σ)`. Simplify using `only [smul_smul, mul_assoc]`. Rewrite using `[← Finset.sum_smul, ← Finset.mul_sum, h2, mul_one]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, h3 a ha _ (hc i), _, Submodule.subset_span fun x hx => ?_, rfl⟩` and prove the remaining obligations. Establish `hx'` using `hx 1 rfl`.

Rewrite `hx'` using `[star_one, one_smul]`. Use `smul_mem_twist σ h1 (hd i) (hA _ hx')` as an intermediate fact. Rewrite `this` using `[comp_mulVec]`. Rewrite using `[Matrix.smul_mulVec]`. Use `this using 3` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Establish `: (A.map σ).map σ.symm ∈ YYl D L L'`. Use `map_mem_YYl D σ.symm (fun a ha A hA => ?_) hA` and prove the remaining obligations. Establish `e : (a • A).map σ.symm = ∑ i, σ.symm (a * d i) • (star (c i) • A).map σ.symm`.

Use extensionality with `p q`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, ← map_sum]`. Use `conv_lhs => rw [← mul_one (a * A p q), ← h2, Finset.mul_sum]`. Rewrite using `[Finset.sum_congr rfl fun i _ => (by ring : a * A p q * (star (c i) * d i) = a * d i * (star (c i) * A p q))]`. Rewrite using `[e]`.

Use `Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, h4 a ha _ (hd i), _, Submodule.subset_span fun x hx => ?_, rfl⟩` and prove the remaining obligations. Establish `hx'` using `smul_mem_twist σ h0 rfl hx`. Rewrite `hx'` using `[one_smul]`. Use `hA _ hx' _ (hc i)` as an intermediate fact. Rewrite `this` using `[← Matrix.smul_mulVec, comp_mulVec]`.

Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using the standard rewrite rules.
-/
theorem exists_conjugate_pair : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L₁ ∧ SD D L₁' ∧ ∀ A : Matrix (Fin N') (Fin N) D.host.E, A ∈ YYl D L L' ↔ A.map σ ∈ YYl D L₁ L₁' := by
  intro D σ _ N N' L L' hL hL'
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨C, h1, ⟨ι, _, c, d, hc, hd, h2⟩, h3, h4⟩ := exists_twisting_ideal D σ
  simp only [← h] at h1 h2 h3
  have hs : ∀ x, σ (star x) = star (σ x) := fun x => by
    rw [h, h, ← AlgEquiv.mul_apply, gal_comm, AlgEquiv.mul_apply]
  have h0 : ∀ c ∈ ({1} : Set D.host.E), ∀ d ∈ ({1} : Set D.host.E),
      star c * d ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    rintro _ rfl _ rfl
    exact ⟨1, by simp⟩
  refine ⟨twist σ {1} L, twist σ C L',
    isSDLat_twist σ hs h0 (ι := Unit) (c := fun _ => 1) (d := fun _ => 1) (fun _ => rfl) (fun _ => rfl)
      (by simp) hL, isSDLat_twist σ hs h1 hc hd h2 hL', fun A => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · refine map_mem_YYl D σ (fun a ha A hA => ?_) hA
    have e : (a • A).map σ = ∑ i, (σ a * star (c i)) • (d i • A.map σ) := by
      simp only [smul_smul, mul_assoc]
      rw [← Finset.sum_smul, ← Finset.mul_sum, h2, mul_one]
      ext i j; simp
    rw [e]
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨_, h3 a ha _ (hc i), _, Submodule.subset_span fun x hx => ?_, rfl⟩
    have hx' := hx 1 rfl
    rw [star_one, one_smul] at hx'
    have := smul_mem_twist σ h1 (hd i) (hA _ hx')
    rw [comp_mulVec] at this
    rw [Matrix.smul_mulVec]
    convert this using 3
    funext k; simp
  · have : (A.map σ).map σ.symm ∈ YYl D L L' := by
      refine map_mem_YYl D σ.symm (fun a ha A hA => ?_) hA
      have e : (a • A).map σ.symm = ∑ i, σ.symm (a * d i) • (star (c i) • A).map σ.symm := by
        ext p q
        simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, ← map_sum]
        conv_lhs => rw [← mul_one (a * A p q), ← h2, Finset.mul_sum]
        rw [Finset.sum_congr rfl fun i _ =>
          (by ring : a * A p q * (star (c i) * d i) = a * d i * (star (c i) * A p q))]
      rw [e]
      refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
        ⟨_, h4 a ha _ (hd i), _, Submodule.subset_span fun x hx => ?_, rfl⟩
      have hx' := smul_mem_twist σ h0 rfl hx
      rw [one_smul] at hx'
      have := hA _ hx' _ (hc i)
      rw [← Matrix.smul_mulVec, comp_mulVec] at this
      convert this using 2
      funext k; simp
    convert this using 1
    ext i j; simp

end GlobalTheory.GaloisTwist
