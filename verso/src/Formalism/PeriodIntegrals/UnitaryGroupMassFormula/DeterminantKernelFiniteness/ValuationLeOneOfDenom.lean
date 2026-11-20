import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsNatMulMemFracFam

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerDetFinW

open PI.KerIso

/- English proof (translation)
Establish `hB : R.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : R)) = A`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[← hB, ← RingHom.map_det]`. Conclude with `SetLike.coe_mem _`.
-/
lemma det_mem_of_entries {K : Type} [Field K] (R : Subring K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (h : ∀ i j, A i j ∈ R) : A.det ∈ R := by
  have hB : R.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : R)) = A := by
    ext i j
    rfl
  rw [← hB, ← RingHom.map_det]
  exact SetLike.coe_mem _

/- English proof (translation)
Use `⟨∏ j, u j, Nat.Coprime.prod_left (fun j _ => hu j), ?_⟩` and prove the remaining obligations. Establish `h1 : ((∏ j, u j : ℕ) : K) * A.det = (A * Matrix.diagonal (fun j => (u j : K))).det`. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Apply `det_mem_of_entries` to reduce the goal to its premises. Introduce `i j`. Rewrite using `[Matrix.mul_diagonal, mul_comm]`. Conclude with `hA i j`.
-/
lemma det_denom {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (A : Matrix ι ι K) (u : ι → ℕ) (hu : ∀ j, Nat.Coprime (u j) p)
    (hA : ∀ i j, (u j : K) * A i j ∈ (algebraMap (𝓞 K) K).range) :
    ∃ U : ℕ, Nat.Coprime U p ∧ (U : K) * A.det ∈ (algebraMap (𝓞 K) K).range := by
  refine ⟨∏ j, u j, Nat.Coprime.prod_left (fun j _ => hu j), ?_⟩
  have h1 : ((∏ j, u j : ℕ) : K) * A.det = (A * Matrix.diagonal (fun j => (u j : K))).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    push_cast
    ring
  rw [h1]
  apply det_mem_of_entries
  intro i j
  rw [Matrix.mul_diagonal, mul_comm]
  exact hA i j

/- English proof (translation)
Establish `hU' : ((U : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal`. Introduce `hmem`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.mpr hU`. Apply `𝔭.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`.

Establish `h2 : ((a * (U : ℤ) + b * (p : ℤ) : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal`. Use `push_cast`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp𝔭)`. Rewrite `h2` using `[hab, Int.cast_one]`. Conclude with `h2`.

Establish `hK : ((U : ℕ) : K) = algebraMap (𝓞 K) K (U : 𝓞 K)` using `(map_natCast _ _).symm`. Rewrite using `[hK, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Use `le_antisymm (𝔭.intValuation_le_one _) (not_lt.mp fun hlt => hU' ?_)` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.mp ((𝔭.intValuation_lt_one_iff_dvd _).mp hlt)`.
-/
lemma valuation_natCast_eq_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p U : ℕ}
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) :
    𝔭.valuation K (U : K) = 1 := by
  have hU' : ((U : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hU
    apply 𝔭.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : ((a * (U : ℤ) + b * (p : ℤ) : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
      push_cast
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp𝔭)
    rw [hab, Int.cast_one] at h2
    exact h2
  have hK : ((U : ℕ) : K) = algebraMap (𝓞 K) K (U : 𝓞 K) := (map_natCast _ _).symm
  rw [hK, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  refine le_antisymm (𝔭.intValuation_le_one _) (not_lt.mp fun hlt => hU' ?_)
  exact Ideal.dvd_span_singleton.mp ((𝔭.intValuation_lt_one_iff_dvd _).mp hlt)

/- English proof (translation)
Take `⟨r, hr⟩` from `hx`. Establish `h1 : 𝔭.valuation K (U : K) = 1` using `valuation_natCast_eq_one 𝔭 hp𝔭 hU`. Establish `h2 : 𝔭.valuation K ((U : K) * x) ≤ 1`. Rewrite using `[← hr, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `𝔭.intValuation_le_one r`.

Rewrite `h2` using `[map_mul, h1, one_mul]`. Then use the resulting hypothesis.
-/
lemma valuation_le_one_of_denom {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p U : ℕ}
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) {x : K}
    (hx : (U : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by
  obtain ⟨r, hr⟩ := hx
  have h1 : 𝔭.valuation K (U : K) = 1 := valuation_natCast_eq_one 𝔭 hp𝔭 hU
  have h2 : 𝔭.valuation K ((U : K) * x) ≤ 1 := by
    rw [← hr, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact 𝔭.intValuation_le_one r
  rwa [map_mul, h1, one_mul] at h2

/- English proof (translation)
Take `⟨s, hs, hsM⟩` from `hg.2 v hv`. Establish `hx : ∀ a, ((s : K) • g.symm v) a ∈ M`. Introduce `a`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_natCast]`. Conclude with `hsM a`.

Take `⟨t, ht, htM⟩` from `hg'.1 ((s : K) • g.symm v) hx`. Use `⟨t * s, Nat.Coprime.mul ht hs, fun w => ?_⟩` and prove the remaining obligations. Establish `h` using `htM w`. Rewrite `h` using `[map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc]`. Rewrite using `[LinearEquiv.trans_apply, Nat.cast_mul]`.

Conclude with `h`.
-/
lemma comp_denom {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (hg : AtP M g p) (hg' : AtP M g' p) (v : Fin 4 × n → K)
    (hv : ∀ w, v w ∈ (algebraMap (𝓞 K) K).range) :
    ∃ u : ℕ, Nat.Coprime u p ∧ ∀ w, (u : K) * (g.symm.trans g') v w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨s, hs, hsM⟩ := hg.2 v hv
  have hx : ∀ a, ((s : K) • g.symm v) a ∈ M := by
    intro a
    rw [Pi.smul_apply, Algebra.smul_def, map_natCast]
    exact hsM a
  obtain ⟨t, ht, htM⟩ := hg'.1 ((s : K) • g.symm v) hx
  refine ⟨t * s, Nat.Coprime.mul ht hs, fun w => ?_⟩
  have h := htM w
  rw [map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc] at h
  rw [LinearEquiv.trans_apply, Nat.cast_mul]
  exact h

/- English proof (translation)
Use `set f := ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) with hf`. Establish `hcol : ∀ j : Fin 4 × n, ∃ u : ℕ, Nat.Coprime u p ∧ ∀ i, (u : K) * LinearMap.toMatrix' f i j ∈ (algebraMap (𝓞 K) K).range`. Introduce `j`. Establish `hv : ∀ w, (Pi.single j (1 : K) : Fin 4 × n → K) w ∈ (algebraMap (𝓞 K) K).range`. Introduce `w`.

Distinguish the cases in `hw : w = j`. Substitute `hw` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne hw]`.

Conclude with `zero_mem _`. Take `⟨u, hu, hu'⟩` from `comp_denom hg hg' (Pi.single j (1 : K)) hv`. Conclude with `⟨u, hu, fun i => by rw [LinearMap.toMatrix'_apply]; exact hu' i⟩`. Use `choose u hu hu' using hcol`. Take `⟨U, hU, hUd⟩` from `det_denom p (LinearMap.toMatrix' f) u hu (fun i j => hu' j i)`.

Rewrite `hUd` using `[LinearMap.det_toMatrix']`. Conclude with `valuation_le_one_of_denom 𝔭 hp𝔭 hU hUd`.
-/
lemma det_valuation_le_one {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) :
    𝔭.valuation K (LinearMap.det ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
      (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))) ≤ 1 := by
  classical
  set f := ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
    (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) with hf
  have hcol : ∀ j : Fin 4 × n, ∃ u : ℕ, Nat.Coprime u p ∧
      ∀ i, (u : K) * LinearMap.toMatrix' f i j ∈ (algebraMap (𝓞 K) K).range := by
    intro j
    have hv : ∀ w, (Pi.single j (1 : K) : Fin 4 × n → K) w ∈ (algebraMap (𝓞 K) K).range := by
      intro w
      by_cases hw : w = j
      · subst hw
        rw [Pi.single_eq_same]
        exact one_mem _
      · rw [Pi.single_eq_of_ne hw]
        exact zero_mem _
    obtain ⟨u, hu, hu'⟩ := comp_denom hg hg' (Pi.single j (1 : K)) hv
    exact ⟨u, hu, fun i => by rw [LinearMap.toMatrix'_apply]; exact hu' i⟩
  choose u hu hu' using hcol
  obtain ⟨U, hU, hUd⟩ := det_denom p (LinearMap.toMatrix' f) u hu (fun i j => hu' j i)
  rw [LinearMap.det_toMatrix'] at hUd
  exact valuation_le_one_of_denom 𝔭 hp𝔭 hU hUd

/- English proof (translation)
Establish `h1 : 𝔭.valuation K (detRel g' g) ≤ 1` using `det_valuation_le_one 𝔭 hp𝔭 hg hg'`. Establish `h2 : 𝔭.valuation K (detRel g g') ≤ 1` using `det_valuation_le_one 𝔭 hp𝔭 hg' hg`. Establish `hprod : detRel g' g * detRel g g' = 1`. Unfold `detRel`. Rewrite using `[← LinearMap.det_comp]`.

Establish `hc : ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)).comp ((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) = LinearMap.id` using `LinearMap.ext fun x => by simp`. Rewrite using `[hc, LinearMap.det_id]`. Establish `hm : 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') = 1`. Rewrite using `[← map_mul, hprod, map_one]`. Establish `hv : 𝔭.valuation K (detRel g' g) = 1`.

Use `le_antisymm h1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Unfold `ordK`. Rewrite using `[hv]`. Simplify using the standard rewrite rules.
-/
theorem ordK_detRel_eq_zero {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) : ordK 𝔭 (detRel g' g) = 0 := by
  have h1 : 𝔭.valuation K (detRel g' g) ≤ 1 := det_valuation_le_one 𝔭 hp𝔭 hg hg'
  have h2 : 𝔭.valuation K (detRel g g') ≤ 1 := det_valuation_le_one 𝔭 hp𝔭 hg' hg
  have hprod : detRel g' g * detRel g g' = 1 := by
    unfold detRel
    rw [← LinearMap.det_comp]
    have hc : ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
        (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)).comp
        ((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) :
        (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) = LinearMap.id :=
      LinearMap.ext fun x => by simp
    rw [hc, LinearMap.det_id]
  have hm : 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') = 1 := by
    rw [← map_mul, hprod, map_one]
  have hv : 𝔭.valuation K (detRel g' g) = 1 := by
    refine le_antisymm h1 ?_
    calc 1 = 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') := hm.symm
      _ ≤ 𝔭.valuation K (detRel g' g) * 1 := by gcongr
      _ = 𝔭.valuation K (detRel g' g) := mul_one _
  unfold ordK
  rw [hv]
  simp

end PI.KerDetFinW
