import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import ReciprocityTheory.AnalyticForms.AnalyticCharts.ExistsAnalyticGraphChartMvPolynomial

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {n : ℕ}

def dualEv (p v : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] DualNumber ℂ :=
  aeval fun j => (TrivSqZeroExt.inl (p j) + v j • DualNumber.eps : DualNumber ℂ)

/- English proof (translation)
Proceed by induction on `h using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `[dualEv, TrivSqZeroExt.algebraMap_eq_inl]`. Use `next q r hq hr =>`. Take `⟨h1, h2⟩` from `hq`.

Take `⟨h3, h4⟩` from `hr`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, TrivSqZeroExt.fst_add, h1, h3, map_add]`. Rewrite using `[map_add, TrivSqZeroExt.snd_add, h2, h4, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_add, map_add, add_mul]`. Use `next q i hq =>`. Take `⟨h1, h2⟩` from `hq`. Establish `hX : dualEv p v (X i) = TrivSqZeroExt.inl (p i) + v i • DualNumber.eps`. Simplify using `[dualEv]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, TrivSqZeroExt.fst_mul, h1, hX]`. Simplify using the standard rewrite rules. Rewrite using `[map_mul, TrivSqZeroExt.snd_mul, h1, h2, hX]`. Simplify using `[Derivation.leibniz, pderiv_X, Pi.single_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, DualNumber.snd_eps, DualNumber.fst_eps]`.

Establish `e1 : (∑ x, (eval p) (if i = x then q else 0) * v x) = eval p q * v i`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules. Rewrite using `[e1, Finset.sum_mul]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun x _ => by ring`.
-/
theorem dualEv_fst_snd (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).fst = eval p h ∧
      (dualEv p v h).snd = ∑ j, eval p (pderiv j h) * v j := by
  induction h using MvPolynomial.induction_on
  next a =>
    simp [dualEv, TrivSqZeroExt.algebraMap_eq_inl]
  next q r hq hr =>
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨h3, h4⟩ := hr
    refine ⟨?_, ?_⟩
    · rw [map_add, TrivSqZeroExt.fst_add, h1, h3, map_add]
    · rw [map_add, TrivSqZeroExt.snd_add, h2, h4, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_add, map_add, add_mul]
  next q i hq =>
    obtain ⟨h1, h2⟩ := hq
    have hX : dualEv p v (X i) = TrivSqZeroExt.inl (p i) + v i • DualNumber.eps := by
      simp [dualEv]
    refine ⟨?_, ?_⟩
    · rw [map_mul, TrivSqZeroExt.fst_mul, h1, hX]
      simp
    · rw [map_mul, TrivSqZeroExt.snd_mul, h1, h2, hX]
      simp [Derivation.leibniz, pderiv_X, Pi.single_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum,
        DualNumber.snd_eps, DualNumber.fst_eps]
      have e1 : (∑ x, (eval p) (if i = x then q else 0) * v x) = eval p q * v i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      rw [e1, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
The claim follows from `(dualEv_fst_snd p v h).1`.
-/
theorem dualEv_fst (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).fst = eval p h := (dualEv_fst_snd p v h).1

/- English proof (translation)
The claim follows from `(dualEv_fst_snd p v h).2`.
-/
theorem dualEv_snd (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).snd = ∑ j, eval p (pderiv j h) * v j := (dualEv_fst_snd p v h).2

/- English proof (translation)
Introduce `k hk`. Assume the negation of the conclusion as `hne`. Establish `hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p) k)` using `(IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) k).2 (fun h => hne (RingHom.mem_ker.1 h))`. Establish `htop : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K = ⊤` using `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hk) hu`. Establish `hs : Subsingleton (locRing K p)` using `Ideal.Quotient.subsingleton_iff.2 htop`.

Conclude with `not_subsingleton (locRing K p) hs`.
-/
theorem eval_eq_zero_of_isLocalRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsLocalRing (locRing K p)] : ∀ k ∈ K, eval p k = 0 := by
  intro k hk
  by_contra hne
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p) k) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) k).2 (fun h => hne (RingHom.mem_ker.1 h))
  have htop : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hk) hu
  have hs : Subsingleton (locRing K p) := Ideal.Quotient.subsingleton_iff.2 htop
  exact not_subsingleton (locRing K p) hs

/- English proof (translation)
Establish `hunit : ∀ y : (ptIdeal p).primeCompl, IsUnit ((dualEv p v).toRingHom (y : MvPolynomial (Fin n) ℂ))`. Introduce `y`. Use `TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ?_` and prove the remaining obligations. Establish `hy : eval p (y : MvPolynomial (Fin n) ℂ) ≠ 0` using `fun h => y.2 (RingHom.mem_ker.2 h)`. Use `dualEv_fst p v (y : MvPolynomial (Fin n) ℂ)` as an intermediate fact.

Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[this]`. Conclude with `hy.isUnit`. Set `g : locPt p →+* DualNumber ℂ` to `IsLocalization.lift (M := (ptIdeal p).primeCompl) hunit`. Establish `hg : ∀ x, g (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p) x) = dualEv p v x` using `fun x => IsLocalization.lift_eq hunit x`.

Establish `hK' : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≤ RingHom.ker g`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `k hk`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hg]`. Conclude with `hK k hk`.

Use `⟨Ideal.Quotient.lift _ g (fun a ha => RingHom.mem_ker.1 (hK' ha)), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) (locPt p) (locRing K p), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk, hg]`.
-/
theorem exists_dualEv_lift (K : Ideal (MvPolynomial (Fin n) ℂ)) (p v : Fin n → ℂ)
    (hK : ∀ k ∈ K, dualEv p v k = 0) :
    ∃ χ : locRing K p →+* DualNumber ℂ,
      ∀ x, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x) = dualEv p v x := by
  have hunit : ∀ y : (ptIdeal p).primeCompl, IsUnit ((dualEv p v).toRingHom (y : MvPolynomial (Fin n) ℂ)) := by
    intro y
    refine TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ?_
    have hy : eval p (y : MvPolynomial (Fin n) ℂ) ≠ 0 := fun h => y.2 (RingHom.mem_ker.2 h)
    have := dualEv_fst p v (y : MvPolynomial (Fin n) ℂ)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [this]
    exact hy.isUnit
  let g : locPt p →+* DualNumber ℂ := IsLocalization.lift (M := (ptIdeal p).primeCompl) hunit
  have hg : ∀ x, g (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p) x) = dualEv p v x := fun x =>
    IsLocalization.lift_eq hunit x
  have hK' : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap]
    intro k hk
    rw [Ideal.mem_comap, RingHom.mem_ker, hg]
    exact hK k hk
  refine ⟨Ideal.Quotient.lift _ g (fun a ha => RingHom.mem_ker.1 (hK' ha)), fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) (locPt p) (locRing K p),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk, hg]

/- English proof (translation)
Introduce `x hx`. Establish `h1 : algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x ∈ Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i))`. Rewrite using `[hr]`. Conclude with `Ideal.mem_map_of_mem _ hx`. Establish `h2 : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) ≤ RingHom.ker χ`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hχ i`. Conclude with `h2 h1`.
-/
theorem map_ptIdeal_eq_zero (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) {e : ℕ}
    (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p))
    (χ : locRing K p →+* DualNumber ℂ)
    (hχ : ∀ i, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) = 0) :
    ∀ x ∈ ptIdeal p, χ (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x) = 0 := by
  intro x hx
  have h1 : algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) x ∈
      Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) := by
    rw [hr]
    exact Ideal.mem_map_of_mem _ hx
  have h2 : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) ≤
      RingHom.ker χ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hχ i
  exact h2 h1

/- English proof (translation)
Establish `heval` using `eval_eq_zero_of_isLocalRing K p`. Establish `hF : ∀ k, dualEv p v (F k) = 0` using `fun k => TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact heval _ (hFK k)) (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; exact hvF k)`. Establish `hspanF : Ideal.span (Set.range F) ≤ RingHom.ker (dualEv p v).toRingHom`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `hF k`. Establish `hK : ∀ g ∈ K, dualEv p v g = 0`. Introduce `g hg`. Establish `h1 : dualEv p v (hh * g) = 0` using `hspanF (hcut g hg)`. Rewrite `h1` using `[map_mul]`.

Establish `hu : IsUnit (dualEv p v hh)` using `TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [dualEv_fst]; exact hhp.isUnit)`. Conclude with `hu.mul_right_eq_zero.1 h1`. Take `⟨χ, hχ⟩` from `exists_dualEv_lift K p v hK`. Take `⟨χ0, hχ0⟩` from `exists_dualEv_lift K p 0 (fun k hk => TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact heval k hk) (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; simp))`. Establish `hle : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p) ≤ RingHom.ker χ0`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hχ0]`. Conclude with `TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact RingHom.mem_ker.1 hx) (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; simp)`. Establish `hr0 : ∀ i, eval p (r i) = 0`.

Introduce `i`. Establish `hmem : algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i) ∈ Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p)`. Rewrite using `[← hr]`. Conclude with `Ideal.subset_span ⟨i, rfl⟩`. Establish `h1` using `RingHom.mem_ker.1 (hle hmem)`.

Rewrite `h1` using `[hχ0]`. Establish `h2` using `congrArg TrivSqZeroExt.fst h1`. Rewrite `h2` using `[dualEv_fst, TrivSqZeroExt.fst_zero]`. Then use the resulting hypothesis. Establish `hall` using `map_ptIdeal_eq_zero K p r hr χ (fun i => by`. Rewrite using `[hχ]`.

Conclude with `TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact hr0 i) (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; exact hvr i))`. Use function extensionality and compare the values at `j`. Establish `hx : (X j - C (p j) : MvPolynomial (Fin n) ℂ) ∈ ptIdeal p` using `RingHom.mem_ker.2 (by simp)`. Establish `h1` using `hall _ hx`. Rewrite `h1` using `[hχ]`.

Establish `h2` using `congrArg TrivSqZeroExt.snd h1`. Rewrite `h2` using `[dualEv_snd, TrivSqZeroExt.snd_zero]`. Simplify `h2` using `[pderiv_X, Pi.single_apply]`.
-/
theorem eq_zero_of_grad (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) {e : ℕ}
    [IsLocalRing (locRing K p)] (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p))
    {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hFK : ∀ i, F i ∈ K)
    (hh : MvPolynomial (Fin n) ℂ) (hhp : eval p hh ≠ 0)
    (hcut : ∀ g ∈ K, hh * g ∈ Ideal.span (Set.range F)) (v : Fin n → ℂ)
    (hvr : ∀ i, ∑ j, eval p (pderiv j (r i)) * v j = 0)
    (hvF : ∀ k, ∑ j, eval p (pderiv j (F k)) * v j = 0) : v = 0 := by
  have heval := eval_eq_zero_of_isLocalRing K p
  have hF : ∀ k, dualEv p v (F k) = 0 := fun k => TrivSqZeroExt.ext
    (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact heval _ (hFK k))
    (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; exact hvF k)
  have hspanF : Ideal.span (Set.range F) ≤ RingHom.ker (dualEv p v).toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hF k
  have hK : ∀ g ∈ K, dualEv p v g = 0 := by
    intro g hg
    have h1 : dualEv p v (hh * g) = 0 := hspanF (hcut g hg)
    rw [map_mul] at h1
    have hu : IsUnit (dualEv p v hh) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [dualEv_fst]; exact hhp.isUnit)
    exact hu.mul_right_eq_zero.1 h1
  obtain ⟨χ, hχ⟩ := exists_dualEv_lift K p v hK
  obtain ⟨χ0, hχ0⟩ := exists_dualEv_lift K p 0 (fun k hk => TrivSqZeroExt.ext
    (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact heval k hk)
    (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; simp))
  have hle : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p) ≤ RingHom.ker χ0 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hχ0]
    exact TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact RingHom.mem_ker.1 hx)
      (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; simp)
  have hr0 : ∀ i, eval p (r i) = 0 := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p) := by
      rw [← hr]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h1 := RingHom.mem_ker.1 (hle hmem)
    rw [hχ0] at h1
    have h2 := congrArg TrivSqZeroExt.fst h1
    rwa [dualEv_fst, TrivSqZeroExt.fst_zero] at h2
  have hall := map_ptIdeal_eq_zero K p r hr χ (fun i => by
    rw [hχ]
    exact TrivSqZeroExt.ext (by rw [dualEv_fst, TrivSqZeroExt.fst_zero]; exact hr0 i)
      (by rw [dualEv_snd, TrivSqZeroExt.snd_zero]; exact hvr i))
  funext j
  have hx : (X j - C (p j) : MvPolynomial (Fin n) ℂ) ∈ ptIdeal p := RingHom.mem_ker.2 (by simp)
  have h1 := hall _ hx
  rw [hχ] at h1
  have h2 := congrArg TrivSqZeroExt.snd h1
  rw [dualEv_snd, TrivSqZeroExt.snd_zero] at h2
  simpa [pderiv_X, Pi.single_apply] using h2

/- English proof (translation)
Conclude with `AnalyticOnNhd.eval_mvPolynomial q`.
-/
theorem analyticOnNhd_eval_univ (q : MvPolynomial (Fin n) ℂ) :
    AnalyticOnNhd ℂ (fun y : Fin n → ℂ => eval y q) Set.univ := by
  exact AnalyticOnNhd.eval_mvPolynomial q

end

end ReciprocityTheory.AnForm.R
