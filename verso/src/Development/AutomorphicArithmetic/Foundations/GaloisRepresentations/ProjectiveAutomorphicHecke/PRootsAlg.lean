import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast hq.ne'`. Establish `hρ : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (((n : ℂ) - 1) / 2)`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg q)]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[hρ, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast (q : ℂ) (j.choose 2), ← Complex.cpow_add _ _ hq0, Nat.cast_choose_two]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem cpow_key (q n j : ℕ) (hq : 0 < q) :
    (q : ℂ) ^ (j.choose 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) =
      (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hρ : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (((n : ℂ) - 1) / 2) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [hρ, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast (q : ℂ) (j.choose 2), ← Complex.cpow_add _ _ hq0,
    Nat.cast_choose_two]
  congr 1
  ring

/- English proof (translation)
Introduce `q n hq B hB a c ϑ h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `h 0 (Nat.zero_le n)`. Simplify `h0` using `[GlobalTheory.LFun.satEig, Multiset.esymm]`. Use `set ρ : ℂ := (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hρ set s : Multiset ℂ := B.map (fun b : ℂˣ => (b : ℂ)) with hs`.

Establish `hcard : Multiset.card s = n` using `by simp [hs, hB]`. Establish `e1 : (UpperTheory.V.Af.algSat n q B).map (· * c) = s.map (fun x => (ρ * c) • x)`. Establish `e0 : UpperTheory.V.Af.algSat n q B = s.map (fun α => ρ * α)` using `by show Multiset.map _ (B.bind fun b => ({(b : ℂ)} : Multiset ℂ)) = _`. Rewrite using `[Multiset.bind_singleton]`. Rewrite using `[e0, Multiset.map_map]`.

Use `Multiset.map_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : Multiset.card (s.map (fun x => (ρ * c) • x)) = n` using `by simp [hcard]`. Rewrite using `[e1, UpperTheory.Gal.crystallineComparison.rootPol, Multiset.prod_X_sub_X_eq_sum_esymm, e2, Finset.mul_sum, UpperTheory.Gal.crystallineComparison.heckePol]`.

Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hjn : j ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`. Establish `hk : _ = ρ ^ j` using `cpow_key q n j hq`. Rewrite using `[h j hjn, ← Multiset.pow_smul_esymm, smul_eq_mul]`. Establish `e3 : (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (a * GlobalTheory.LFun.satEig q n B j * c ^ j) = a * ((-1) ^ j * ((ρ * c) ^ j * s.esymm j))`.

Establish `e4 : GlobalTheory.LFun.satEig q n B j = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) * s.esymm j` using `rfl`. Rewrite using `[e4, mul_pow]`. Take the linear combination `((-1) ^ j * a * s.esymm j * c ^ j) * hk`. Rewrite using `[e3]`. Simplify using `only [map_mul, map_pow, map_neg, map_one]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pRootsAlg_of :
    UpperTheory.Gal.CertificateRingHomMap.RootsAlg := by
  intro q n hq B hB a c ϑ h
  refine ⟨?_, ?_⟩
  · have h0 := h 0 (Nat.zero_le n)
    simpa [GlobalTheory.LFun.satEig, Multiset.esymm] using h0
  · set ρ : ℂ := (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hρ
    set s : Multiset ℂ := B.map (fun b : ℂˣ => (b : ℂ)) with hs
    have hcard : Multiset.card s = n := by simp [hs, hB]
    have e1 : (UpperTheory.V.Af.algSat n q B).map (· * c) = s.map (fun x => (ρ * c) • x) := by
      have e0 : UpperTheory.V.Af.algSat n q B = s.map (fun α => ρ * α) := by
        show Multiset.map _ (B.bind fun b => ({(b : ℂ)} : Multiset ℂ)) = _
        rw [Multiset.bind_singleton]
      rw [e0, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      ring
    have e2 : Multiset.card (s.map (fun x => (ρ * c) • x)) = n := by simp [hcard]
    rw [e1, UpperTheory.Gal.crystallineComparison.rootPol, Multiset.prod_X_sub_X_eq_sum_esymm, e2, Finset.mul_sum, UpperTheory.Gal.crystallineComparison.heckePol]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hk : _ = ρ ^ j := cpow_key q n j hq
    rw [h j hjn, ← Multiset.pow_smul_esymm, smul_eq_mul]
    have e3 : (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (a * GlobalTheory.LFun.satEig q n B j * c ^ j) =
        a * ((-1) ^ j * ((ρ * c) ^ j * s.esymm j)) := by
      have e4 : GlobalTheory.LFun.satEig q n B j = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) * s.esymm j := rfl
      rw [e4, mul_pow]
      linear_combination ((-1) ^ j * a * s.esymm j * c ^ j) * hk
    rw [e3]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
