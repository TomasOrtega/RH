import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LatTrace

open Polynomial

/- English proof (translation)
Establish `hpow : ∀ k : ℕ, (Q ^ k) *ᵥ v = μ ^ k • v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, map_add, Matrix.add_mulVec, hp, hq, add_smul]`. Consider the case `monomial k a`. Rewrite using `[aeval_monomial, aeval_monomial, ← Matrix.mulVec_mulVec, hpow, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, smul_mul_assoc, one_mul, smul_assoc]`.
-/
theorem aeval_mulVec_of_eigen {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : Type*}
    [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (μ : S) (v : n → S) (hv : Q *ᵥ v = μ • v) (p : R[X]) :
    (aeval Q p) *ᵥ v = (aeval μ p) • v := by
  have hpow : ∀ k : ℕ, (Q ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Matrix.mulVec_mulVec, hpow,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_mul_assoc, one_mul, smul_assoc]

/- English proof (translation)
Use `set f := LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ`. Establish `hpow : ∀ k : ℕ, (((f ^ k) x : L) : n → S) = (Q ^ k) *ᵥ (x : n → S)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, pow_succ', ← Matrix.mulVec_mulVec, ← ih]`. Both sides reduce to the same expression. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq, Matrix.add_mulVec]`.

Consider the case `monomial k a`. Rewrite using `[aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hpow, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]`.
-/
theorem aeval_restrict_coe {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (L : Submodule ℤ (n → S))
    (hQ : ∀ x ∈ L, (Q.mulVecLin.restrictScalars ℤ) x ∈ L) (p : ℤ[X]) (x : L) :
    ((aeval (LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ) p x : L) : n → S) =
      (aeval Q p) *ᵥ (x : n → S) := by
  set f := LinearMap.restrict (Q.mulVecLin.restrictScalars ℤ) hQ
  have hpow : ∀ k : ℕ, (((f ^ k) x : L) : n → S) = (Q ^ k) *ᵥ (x : n → S) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, pow_succ',
        ← Matrix.mulVec_mulVec, ← ih]
      rfl
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq,
      Matrix.add_mulVec]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow, ← Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]

/- English proof (translation)
Set `φ : K →+* AlgebraicClosure K` to `algebraMap K (AlgebraicClosure K)`. Take `⟨p, hpm, hp0⟩` from `hM`. Establish `hpM : aeval M p = 0` using `by rw [aeval_def]; exact hp0`. Use `set M' := M.map φ`. Establish `hpM' : aeval M' p = 0`.

Establish `h` using `Polynomial.aeval_algHom_apply (φ.mapMatrix (m := Fin n)).toIntAlgHom M p`. Rewrite `h` using `[hpM, map_zero]`. Conclude with `h`. Establish `htr : φ M.trace = M'.trace`. Simplify using `[Matrix.trace, M', map_sum]`.

Establish `hroots : ∀ μ ∈ M'.charpoly.roots, IsIntegral ℤ μ`. Introduce `μ hμ`. Establish `h0 : M'.charpoly.eval μ = 0` using `(Polynomial.mem_roots'.1 hμ).2`. Rewrite `h0` using `[Matrix.eval_charpoly]`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`.

Establish `hev : M' *ᵥ v = μ • v`. Establish `h1 : (Matrix.scalar (Fin n) μ - M') *ᵥ v = μ • v - M' *ᵥ v`. Rewrite using `[Matrix.sub_mulVec]`. Use `congr 1`. Use extensionality with `i`.

Simplify using `[Matrix.scalar_apply, Matrix.mulVec_diagonal]`. Rewrite `hv` using `[h1, sub_eq_zero]`. Conclude with `hv.symm`. Establish `h2` using `aeval_mulVec_of_eigen M' μ v hev p`. Rewrite `h2` using `[hpM', Matrix.zero_mulVec]`.

Establish `hz : aeval μ p = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hv0 ((smul_eq_zero.1 h2.symm).resolve_left hne)`. Conclude with `⟨p, hpm, by rw [← aeval_def]; exact hz⟩`. Establish `hsum : IsIntegral ℤ M'.trace`.

Rewrite using `[Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]`. Use `multiset_sum_mem (M'.charpoly.roots) (fun x hx => ((mem_integralClosure_iff ℤ (AlgebraicClosure K)).2 (hroots x hx) : x ∈ integralClosure ℤ (AlgebraicClosure K)))` as an intermediate fact. Conclude with `(mem_integralClosure_iff ℤ (AlgebraicClosure K)).1 this`. Rewrite `hsum` using `[← htr]`. Conclude with `(isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hsum`.
-/
theorem isIntegral_trace_of_isIntegral {K : Type} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨p, hpm, hp0⟩ := hM
  have hpM : aeval M p = 0 := by rw [aeval_def]; exact hp0
  set M' := M.map φ
  have hpM' : aeval M' p = 0 := by
    have h := Polynomial.aeval_algHom_apply (φ.mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hpM, map_zero] at h
    exact h
  have htr : φ M.trace = M'.trace := by
    simp [Matrix.trace, M', map_sum]
  have hroots : ∀ μ ∈ M'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have h0 : M'.charpoly.eval μ = 0 := (Polynomial.mem_roots'.1 hμ).2
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hev : M' *ᵥ v = μ • v := by
      have h1 : (Matrix.scalar (Fin n) μ - M') *ᵥ v = μ • v - M' *ᵥ v := by
        rw [Matrix.sub_mulVec]
        congr 1
        ext i
        simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rw [h1, sub_eq_zero] at hv
      exact hv.symm
    have h2 := aeval_mulVec_of_eigen M' μ v hev p
    rw [hpM', Matrix.zero_mulVec] at h2
    have hz : aeval μ p = 0 := by
      by_contra hne
      exact hv0 ((smul_eq_zero.1 h2.symm).resolve_left hne)
    exact ⟨p, hpm, by rw [← aeval_def]; exact hz⟩
  have hsum : IsIntegral ℤ M'.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    have := multiset_sum_mem (M'.charpoly.roots)
      (fun x hx => ((mem_integralClosure_iff ℤ (AlgebraicClosure K)).2 (hroots x hx) : x ∈ integralClosure ℤ (AlgebraicClosure K)))
    exact (mem_integralClosure_iff ℤ (AlgebraicClosure K)).1 this
  rw [← htr] at hsum
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp hsum

/- English proof (translation)
Use `set Lz := Λ.restrictScalars ℤ`. Establish `: Module.Finite ℤ Lz` using `Module.Finite.iff_fg.mpr hfg.restrictScalars`. Establish `hAz : ∀ x ∈ Lz, (A.mulVecLin.restrictScalars ℤ) x ∈ Lz` using `fun x hx => hA x hx`. Take `⟨p, hpm, hp⟩` from `LinearMap.exists_monic_and_aeval_eq_zero ℤ (LinearMap.restrict (A.mulVecLin.restrictScalars ℤ) hAz)`. Establish `hpA : aeval A p = 0`.

Establish `hker : ∀ x ∈ Λ, (aeval A p) *ᵥ x = 0`. Introduce `x hx`. Establish `h` using `aeval_restrict_coe A Lz hAz p ⟨x, hx⟩`. Rewrite `h` using `[hp]`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Establish `hle : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker (aeval A p).mulVecLin` using `Submodule.span_le.2 fun x hx => hker x hx`. Rewrite `hle` using `[hsp]`. Use extensionality with `i j`. Establish `h` using `congrFun (hle (Submodule.mem_top : Pi.single j (1 : E) ∈ ⊤)) i`.

Simplify `h` using `[Matrix.mulVec_single]`. Conclude with `⟨p, hpm, by rw [← aeval_def]; exact hpA⟩`.
-/
theorem isIntegral_of_preserves_lattice {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hA : ∀ x ∈ Λ, A *ᵥ x ∈ Λ) :
    IsIntegral ℤ A := by
  set Lz := Λ.restrictScalars ℤ
  have : Module.Finite ℤ Lz := Module.Finite.iff_fg.mpr hfg.restrictScalars
  have hAz : ∀ x ∈ Lz, (A.mulVecLin.restrictScalars ℤ) x ∈ Lz := fun x hx => hA x hx
  obtain ⟨p, hpm, hp⟩ :=
    LinearMap.exists_monic_and_aeval_eq_zero ℤ
      (LinearMap.restrict (A.mulVecLin.restrictScalars ℤ) hAz)
  have hpA : aeval A p = 0 := by
    have hker : ∀ x ∈ Λ, (aeval A p) *ᵥ x = 0 := by
      intro x hx
      have h := aeval_restrict_coe A Lz hAz p ⟨x, hx⟩
      rw [hp] at h
      rw [← h]; rfl
    have hle : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker (aeval A p).mulVecLin :=
      Submodule.span_le.2 fun x hx => hker x hx
    rw [hsp] at hle
    ext i j
    have h := congrFun (hle (Submodule.mem_top : Pi.single j (1 : E) ∈ ⊤)) i
    simpa [Matrix.mulVec_single] using h
  exact ⟨p, hpm, by rw [← aeval_def]; exact hpA⟩

/- English proof (translation)
Introduce `E _ _ r Λ A hfg hsp hA`. Conclude with `isIntegral_trace_of_isIntegral A (isIntegral_of_preserves_lattice Λ A hfg hsp hA)`.
-/
theorem trace_isIntegral_of_preserves_lattice : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), Λ.FG →
    Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, A *ᵥ x ∈ Λ) →
    IsIntegral ℤ A.trace := by
  intro E _ _ r Λ A hfg hsp hA
  exact isIntegral_trace_of_isIntegral A (isIntegral_of_preserves_lattice Λ A hfg hsp hA)

end GlobalTheory.LatTrace

end
