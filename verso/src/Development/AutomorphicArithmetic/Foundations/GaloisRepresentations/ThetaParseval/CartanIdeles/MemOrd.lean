import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

/- English proof (translation)
Rewrite using `[← FractionalIdeal.finprod_heightOneSpectrum_factorization' E hJ]`. Use `finprod_induction (p := fun X : FractionalIdeal (𝓞 E)⁰ E => X ≤ 1) le_rfl ?_ ?_` and prove the remaining obligations. Introduce `a b ha hb`. Combine the equalities or inequalities in the displayed calculation. Introduce `v`.

Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le (h v)`. Rewrite using `[hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]`. Conclude with `FractionalIdeal.coeIdeal_le_one`.
-/
private theorem le_one_of_count {E : Type} [Field E] [NumberField E] (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), 0 ≤ FractionalIdeal.count E w J) : J ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' E hJ]
  refine finprod_induction (p := fun X : FractionalIdeal (𝓞 E)⁰ E => X ≤ 1) le_rfl ?_ ?_
  · intro a b ha hb
    calc a * b ≤ 1 * b := mul_le_mul_left ha b
      _ ≤ 1 * 1 := mul_le_mul_right hb 1
      _ = 1 := one_mul 1
  · intro v
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
    rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one

/- English proof (translation)
Establish `hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy`. Prove the components needed by the constructor for the conclusion. Introduce `h w`. Conclude with `FractionalIdeal.count_mono E w hs ((FractionalIdeal.spanSingleton_le_iff_mem).mpr h)`. Introduce `h`.

Establish `hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≠ 0` using `mul_ne_zero hs (inv_ne_zero hI)`. Establish `hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≤ 1`. Use `le_one_of_count _ hJ fun w => ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.count_mul E w hs (inv_ne_zero hI), FractionalIdeal.count_inv]`. Use `h w` as an intermediate fact.

Unfold `ordE at this`. Use linear arithmetic over natural numbers and integers. Establish `h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≤ I`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, inv_mul_cancel₀ hI, mul_one]`.

Use `_ ≤ 1 * I := mul_le_mul_left hle I`. Use `_ = I := one_mul I`. Conclude with `(FractionalIdeal.spanSingleton_le_iff_mem).mp h2`.
-/
private theorem mem_iff {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (y : E) (hy : y ≠ 0) : y ∈ I ↔ ∀ w, FractionalIdeal.count E w I ≤ ordE w y := by
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy
  constructor
  · intro h w
    exact FractionalIdeal.count_mono E w hs ((FractionalIdeal.spanSingleton_le_iff_mem).mpr h)
  · intro h
    have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≠ 0 := mul_ne_zero hs (inv_ne_zero hI)
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≤ 1 := by
      refine le_one_of_count _ hJ fun w => ?_
      rw [FractionalIdeal.count_mul E w hs (inv_ne_zero hI), FractionalIdeal.count_inv]
      have := h w
      unfold ordE at this
      omega
    have h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≤ I := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ y
          = (FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹) * I := by
            rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ ≤ 1 * I := mul_le_mul_left hle I
        _ = I := one_mul I
    exact (FractionalIdeal.spanSingleton_le_iff_mem).mp h2

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hP : ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `w.ne_bot`.

Establish `hPI` using `mul_ne_zero hP hI`. Establish `hle : I ≤ ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I`. Introduce `x hx`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`.

Conclude with `FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)`. Use `(mem_iff _ hPI x hx0).mpr fun v => ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.count_mul E v hP hI]`. Establish `h1` using `(mem_iff I hI x hx0).mp hx v`. Distinguish the cases in `hv : v = w`.

Substitute `hv` using the available equality. Rewrite using `[FractionalIdeal.count_self]`. Use `hcon x hx hx0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[FractionalIdeal.count_maximal_coprime E v (Ne.symm hv)]`.

Use linear arithmetic over natural numbers and integers. Establish `h3` using `FractionalIdeal.count_mono E w hI hle`. Rewrite `h3` using `[FractionalIdeal.count_mul E w hP hI, FractionalIdeal.count_self]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem attained {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 E)) : ∃ x ∈ I, x ≠ 0 ∧ ordE w x = FractionalIdeal.count E w I := by
  by_contra hcon
  push_neg at hcon
  have hP : ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact w.ne_bot
  have hPI := mul_ne_zero hP hI
  have hle : I ≤ ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    refine (mem_iff _ hPI x hx0).mpr fun v => ?_
    rw [FractionalIdeal.count_mul E v hP hI]
    have h1 := (mem_iff I hI x hx0).mp hx v
    by_cases hv : v = w
    · subst hv
      rw [FractionalIdeal.count_self]
      have := hcon x hx hx0
      omega
    · rw [FractionalIdeal.count_maximal_coprime E v (Ne.symm hv)]
      omega
  have h3 := FractionalIdeal.count_mono E w hI hle
  rw [FractionalIdeal.count_mul E w hP hI, FractionalIdeal.count_self] at h3
  omega

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hx0⟩ : ∃ x ∈ I, x ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hI` to reduce the goal to its premises. Use extensionality with `y`.

Rewrite using `[FractionalIdeal.mem_zero_iff]`. Conclude with `⟨hcon y, fun h => h ▸ FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)⟩`. Use `⟨FractionalIdeal.fg_of_isUnit I (IsUnit.mk0 I hI), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `y _`.

Establish `: y = (y / x) • x` using `by rw [smul_eq_mul, div_mul_cancel₀ y hx0]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hx)`.
-/
private theorem lattice {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) :
    (I : Submodule (𝓞 E) E).IsLattice E := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ I, x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hI
    ext y
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨hcon y, fun h => h ▸ FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)⟩
  refine ⟨FractionalIdeal.fg_of_isUnit I (IsUnit.mk0 I hI), ?_⟩
  rw [eq_top_iff]
  intro y _
  have : y = (y / x) • x := by rw [smul_eq_mul, div_mul_cancel₀ y hx0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

/- English proof (translation)
Introduce `E _ _ I hI`. Conclude with `⟨mem_iff I hI, attained I hI, lattice I hI⟩`.
-/
theorem UpperTheory.Gal.TP.Skew.memOrd :
    UpperTheory.Gal.TP.Skew.MemOrd := by
  intro E _ _ I hI
  exact ⟨mem_iff I hI, attained I hI, lattice I hI⟩
