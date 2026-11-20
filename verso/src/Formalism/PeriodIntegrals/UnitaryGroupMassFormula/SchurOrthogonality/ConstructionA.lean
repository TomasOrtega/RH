import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • Formalism.GradedWeylDivisibility.rowW N N i) (fun i => zero_smul _ _), Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]`. Simplify using `[Formalism.GradedWeylDivisibility.rowW, Formalism.GradedWeylDivisibility.rowDeg]`. Introduce `b _ hb`. Simplify using `[Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem evA_weight_rowW {N : ℕ} (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d a = Formalism.GradedWeylDivisibility.rowDeg d a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • Formalism.GradedWeylDivisibility.rowW N N i) (fun i => zero_smul _ _),
    Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [Formalism.GradedWeylDivisibility.rowW, Formalism.GradedWeylDivisibility.rowDeg]
  · intro b _ hb
    simp [Formalism.GradedWeylDivisibility.rowW, Pi.single_apply, Ne.symm hb]
  · simp

/- English proof (translation)
Rewrite `hf` using `[Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N ν]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, hshape, rfl⟩` from `hx`. Introduce `m hm`.

Establish `h` using `Formalism.GradedWeylDivisibility.bidetDominance ℂ N N K sz hsz I m hm`. Rewrite `h` using `[hshape]`. Conclude with `h`. Consider the case `zero`. Introduce `m hm`.

Simplify using `at hm`. Consider the case `add x y _ _ hx hy`. Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with h | h` into its components or cases. Conclude with `hx m h`.

Conclude with `hy m h`. Consider the case `smul c x _ hx`. Introduce `m hm`. Conclude with `hx m (support_smul hm)`.
-/
theorem evA_dom {N : ℕ} (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, Formalism.GradedWeylDivisibility.rowDeg m a) ≤ ∑ t : Fin N with t.val < k, ν t) ∧
      ∑ a : Fin N, Formalism.GradedWeylDivisibility.rowDeg m a = ∑ t : Fin N, ν t := by
  classical
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := Formalism.GradedWeylDivisibility.bidetDominance ℂ N N K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

/- English proof (translation)
Establish `h1 : ∀ k : Fin N, (∑ a : Fin N, (μ a : ℤ)) - ∑ a : Fin N with a.val < k.val + 1, (μ a : ℤ) = ∑ a : Fin N, if k.val < a.val then (μ a : ℤ) else 0`. Introduce `k`. Rewrite using `[sub_eq_iff_eq_add, Finset.sum_filter, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> omega`.

Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`. Establish `hI : (Finset.univ.filter fun k : Fin N => k.val < a.val) = Finset.Iio a`.

Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_iff_val_lt_val]`. Rewrite using `[hI, Fin.card_Iio]`.
-/
theorem evA_ht_eq {N : ℕ} (μ : Fin N → ℕ) :
    ∑ a : Fin N, (a.val : ℤ) * (μ a : ℤ) =
      ∑ k : Fin N, ((∑ a : Fin N, (μ a : ℤ)) - ∑ a : Fin N with a.val < k.val + 1, (μ a : ℤ)) := by
  have h1 : ∀ k : Fin N, (∑ a : Fin N, (μ a : ℤ)) - ∑ a : Fin N with a.val < k.val + 1, (μ a : ℤ) =
      ∑ a : Fin N, if k.val < a.val then (μ a : ℤ) else 0 := by
    intro k
    rw [sub_eq_iff_eq_add, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> omega
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hI : (Finset.univ.filter fun k : Fin N => k.val < a.val) = Finset.Iio a := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_iff_val_lt_val]
  rw [hI, Fin.card_Iio]

/- English proof (translation)
Rewrite using `[evA_ht_eq ν, evA_ht_eq μ]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `k _`. Establish `hs : (∑ a : Fin N, (μ a : ℤ)) = ∑ a : Fin N, (ν a : ℤ)` using `by exact_mod_cast h2`. Establish `hk : (∑ a : Fin N with a.val < k.val + 1, (μ a : ℤ)) ≤ ∑ a : Fin N with a.val < k.val + 1, (ν a : ℤ)` using `by exact_mod_cast h1 (k.val + 1)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem evA_ht {N : ℕ} (μ ν : Fin N → ℕ)
    (h1 : ∀ k : ℕ, (∑ a : Fin N with a.val < k, μ a) ≤ ∑ a : Fin N with a.val < k, ν a)
    (h2 : ∑ a : Fin N, μ a = ∑ a : Fin N, ν a) :
    ∑ a : Fin N, (a.val : ℤ) * (ν a : ℤ) ≤ ∑ a : Fin N, (a.val : ℤ) * (μ a : ℤ) := by
  rw [evA_ht_eq ν, evA_ht_eq μ]
  apply Finset.sum_le_sum
  intro k _
  have hs : (∑ a : Fin N, (μ a : ℤ)) = ∑ a : Fin N, (ν a : ℤ) := by exact_mod_cast h2
  have hk : (∑ a : Fin N with a.val < k.val + 1, (μ a : ℤ)) ≤
      ∑ a : Fin N with a.val < k.val + 1, (ν a : ℤ) := by exact_mod_cast h1 (k.val + 1)
  linarith

/- English proof (translation)
Unfold `Formalism.REAL.fockF`. Rewrite using `[Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support), Finset.sum_subset (Finset.subset_union_right : g.support ⊆ f.support ∪ g.support)]`. Introduce `m _ hm`. Simplify using `only [MvPolynomial.mem_support_iff, not_not] at hm`. Simplify using `[hm]`.

Introduce `m _ hm`. Simplify using `only [MvPolynomial.mem_support_iff, not_not] at hm`. Simplify using `[hm]`.
-/
theorem evA_fock_right {σ : Type*} (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f g = ∑ m ∈ g.support,
      f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  classical
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support),
    Finset.sum_subset (Finset.subset_union_right : g.support ⊆ f.support ∪ g.support)]
  · intro m _ hm
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]
  · intro m _ hm
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]

/- English proof (translation)
Establish `hdiag : ∀ v ∈ d.support, v.1 = v.2`. Introduce `v hv`. Assume the negation of the conclusion as `hne`. Apply `h` to reduce the goal to its premises. Apply `Finset.prod_eq_zero hv` to reduce the goal to its premises.

Rewrite using `[Matrix.one_apply_ne hne]`. Conclude with `zero_pow (Finsupp.mem_support_iff.mp hv)`. Rewrite using `[Finsupp.weight_apply, Finsupp.weight_apply]`. Unfold `Finsupp.sum`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations.

Simplify using `[Formalism.GradedWeylDivisibility.rowW, Formalism.GradedWeylDivisibility.colW, hdiag v hv]`.
-/
theorem evA_diag {N : ℕ} (d : Fin N × Fin N →₀ ℕ)
    (h : (∏ v ∈ d.support, ((1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2) ^ d v) ≠ 0) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = Finsupp.weight (Formalism.GradedWeylDivisibility.colW N N) d := by
  have hdiag : ∀ v ∈ d.support, v.1 = v.2 := by
    intro v hv
    by_contra hne
    apply h
    apply Finset.prod_eq_zero hv
    rw [Matrix.one_apply_ne hne]
    exact zero_pow (Finsupp.mem_support_iff.mp hv)
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun v hv => ?_
  simp [Formalism.GradedWeylDivisibility.rowW, Formalism.GradedWeylDivisibility.colW, hdiag v hv]

/- English proof (translation)
Establish `key : ∀ (k : ℕ) (h1 : k ≤ N) (h2 : k ≤ N), MvPolynomial.eval (fun v : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2) (Formalism.GradedWeylDivisibility.lpMinor ℂ k h1 h2) = 1`. Introduce `k h1 h2`. Unfold `Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[RingHom.map_det]`. Establish `hM : (MvPolynomial.eval fun v : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2).mapMatrix (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin N × Fin N) ℂ)) = 1`.

Use extensionality with `p q`. Simplify using `[Matrix.one_apply]`. Rewrite using `[hM, Matrix.det_one]`. Unfold `evalM Formalism.GradedWeylDivisibility.hw`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_eq_one fun s _ => by rw [map_pow, key, one_pow]`.
-/
theorem evA_hw_one {N : ℕ} (ν : Fin N → ℕ) : evalM 1 (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) = 1 := by
  have key : ∀ (k : ℕ) (h1 : k ≤ N) (h2 : k ≤ N),
      MvPolynomial.eval (fun v : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2)
        (Formalism.GradedWeylDivisibility.lpMinor ℂ k h1 h2) = 1 := by
    intro k h1 h2
    unfold Formalism.GradedWeylDivisibility.lpMinor
    rw [RingHom.map_det]
    have hM : (MvPolynomial.eval fun v : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2).mapMatrix
        (Matrix.of fun p q : Fin k =>
          (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
      ext p q
      simp [Matrix.one_apply]
    rw [hM, Matrix.det_one]
  unfold evalM Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  exact Finset.prod_eq_one fun s _ => by rw [map_pow, key, one_pow]

/- English proof (translation)
Introduce `N lam s hs`. Use `set ν := lam.natW with hνdef`. Establish `hν : Antitone ν` using `fun i j hij => by`. Simplify using `only [hνdef, Formalism.BasicNotions.DomWeight.natW]`. Conclude with `Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)`.

Establish `hs' : s ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν` using `hs`. Establish `hscol : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW N N) s ν` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hs').1`. Use `set P := weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) ν s with hP`. Establish `hPmem : P ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν` using `Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N ν ν s hs'`. Establish `hPht : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.lhwinHt N N) P (∑ a : Fin N, (a.val : ℤ) * (ν a : ℤ))`.

Introduce `d hd`. Rewrite `hd` using `[hP, coeff_weightedHomogeneousComponent]`. Use `split_ifs at hd with hw`. Rewrite using `[Formalism.GradedWeylDivisibility.lhwin_weight_ht, hw]`. Conclude with `absurd rfl hd`.

Establish `hkill : ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k → Formalism.GradedWeylDivisibility.rowDiv ℂ a b k P = 0`. Introduce `a b hab k hk`. Assume the negation of the conclusion as `hne`. Establish `hQ` using `Formalism.GradedWeylDivisibility.lhwin_rowDiv_shift ℂ _ a b k P hPht`. Establish `hQmem` using `Formalism.GradedWeylDivisibility.rowDivStable ℂ N N ν a b k P hPmem`.

Take `⟨d, hd⟩` from `ne_zero_iff.mp hne`. Take `⟨h1, h2⟩` from `evA_dom ν _ hQmem d (mem_support_iff.mpr hd)`. Establish `hge` using `evA_ht (Formalism.GradedWeylDivisibility.rowDeg d) ν h1 h2`. Establish `hwt` using `hQ hd`. Rewrite `hwt` using `[Formalism.GradedWeylDivisibility.lhwin_weight_ht]`.

Simplify using `only [evA_weight_rowW] at hwt`. Establish `hab' : (a.val : ℤ) < b.val` using `by exact_mod_cast (Fin.lt_def.mp hab)`. Establish `hk' : (1 : ℤ) ≤ k` using `by exact_mod_cast hk`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨c, hc⟩` from `Formalism.GradedWeylDivisibility.hwLine ℂ N N le_rfl ν hν P hPmem hkill`.

Establish `he : extremal ℂ N lam = Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν` using `rfl`. Establish `heRow : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) ν`. Establish `h` using `Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl ν hν`. Establish `hr : (Formalism.GradedWeylDivisibility.rowNu (r` using `N) ν) = ν := by`. Use function extensionality and compare the values at `a`.

Simplify using `[Formalism.GradedWeylDivisibility.rowNu, a.isLt]`. Rewrite `h` using `[hr]`. Then use the resulting hypothesis. Establish `hsub : P.support ⊆ s.support` using `fun d hd => by`. Rewrite `hd`, the goal using `[mem_support_iff]`. Rewrite `hd` using `[hP, coeff_weightedHomogeneousComponent]`.

Use `split_ifs at hd with h`. Conclude with `hd`. Conclude with `absurd rfl hd`. Establish `hev : evalM 1 s = evalM 1 P`. Unfold `evalM`.

Rewrite using `[eval_eq, eval_eq]`. Use `symm`. Rewrite using `[Finset.sum_subset hsub (fun d _ hd => by rw [mem_support_iff, not_not] at hd; simp [hd])]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Distinguish the cases in `hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = ν`.

Rewrite using `[hP, coeff_weightedHomogeneousComponent, if_pos hw]`. Establish `hcol : Finsupp.weight (Formalism.GradedWeylDivisibility.colW N N) d = ν` using `hscol (mem_support_iff.mp hd)`. Establish `hz : (∏ v ∈ d.support, ((1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2) ^ d v) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hw ((evA_diag d hne).trans hcol)`.

Rewrite using `[hz, mul_zero, mul_zero]`. Establish `hfse : Formalism.REAL.fockF s (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) = Formalism.REAL.fockF P (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν)`. Rewrite using `[evA_fock_right s, evA_fock_right P]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) m = ν` using `heRow (mem_support_iff.mp hm)`.

Rewrite using `[hP, coeff_weightedHomogeneousComponent, if_pos hw]`. Establish `hfce : ∀ e : MvPolynomial (Fin N × Fin N) ℂ, Formalism.REAL.fockF (c • e) e = c * Formalism.REAL.fockF e e`. Introduce `e`. Rewrite using `[evA_fock_right, evA_fock_right, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hFne : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) ≠ 0`. Establish `h` using `(Formalism.GradedWeylDivisibility.fockPos (Fin N × Fin N) _ (Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl ν)).1`. Introduce `h0`.

Rewrite `h` using `[h0]`. Simplify using `at h`. Unfold `normFock`. Rewrite using `[he, hev, hfse, hc, hfce, mul_div_assoc, div_self hFne, mul_one]`. Unfold `evalM`.

Rewrite using `[smul_eq_C_mul, eval_mul, eval_C]`. Establish `h1` using `evA_hw_one ν`. Unfold `evalM at h1`. Rewrite using `[h1, mul_one]`.
-/
theorem evaluation_at_one : EvalOne := by
  intro N lam s hs
  classical
  set ν := lam.natW with hνdef
  have hν : Antitone ν := fun i j hij => by
    simp only [hνdef, Formalism.BasicNotions.DomWeight.natW]
    exact Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)
  have hs' : s ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν := hs
  have hscol : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW N N) s ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hs').1
  set P := weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.rowW N N) ν s with hP
  have hPmem : P ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν := Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N ν ν s hs'
  have hPht : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.lhwinHt N N) P
      (∑ a : Fin N, (a.val : ℤ) * (ν a : ℤ)) := by
    intro d hd
    rw [hP, coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with hw
    · rw [Formalism.GradedWeylDivisibility.lhwin_weight_ht, hw]
    · exact absurd rfl hd
  have hkill : ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k → Formalism.GradedWeylDivisibility.rowDiv ℂ a b k P = 0 := by
    intro a b hab k hk
    by_contra hne
    have hQ := Formalism.GradedWeylDivisibility.lhwin_rowDiv_shift ℂ _ a b k P hPht
    have hQmem := Formalism.GradedWeylDivisibility.rowDivStable ℂ N N ν a b k P hPmem
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
    obtain ⟨h1, h2⟩ := evA_dom ν _ hQmem d (mem_support_iff.mpr hd)
    have hge := evA_ht (Formalism.GradedWeylDivisibility.rowDeg d) ν h1 h2
    have hwt := hQ hd
    rw [Formalism.GradedWeylDivisibility.lhwin_weight_ht] at hwt
    simp only [evA_weight_rowW] at hwt
    have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith
  obtain ⟨c, hc⟩ := Formalism.GradedWeylDivisibility.hwLine ℂ N N le_rfl ν hν P hPmem hkill
  have he : extremal ℂ N lam = Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν := rfl
  have heRow : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) ν := by
    have h := Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl ν hν
    have hr : (Formalism.GradedWeylDivisibility.rowNu (r := N) ν) = ν := by
      funext a; simp [Formalism.GradedWeylDivisibility.rowNu, a.isLt]
    rwa [hr] at h
  have hsub : P.support ⊆ s.support := fun d hd => by
    rw [mem_support_iff] at hd ⊢
    rw [hP, coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with h
    · exact hd
    · exact absurd rfl hd
  have hev : evalM 1 s = evalM 1 P := by
    unfold evalM
    rw [eval_eq, eval_eq]
    symm
    rw [Finset.sum_subset hsub (fun d _ hd => by rw [mem_support_iff, not_not] at hd; simp [hd])]
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = ν
    · rw [hP, coeff_weightedHomogeneousComponent, if_pos hw]
    · have hcol : Finsupp.weight (Formalism.GradedWeylDivisibility.colW N N) d = ν := hscol (mem_support_iff.mp hd)
      have hz : (∏ v ∈ d.support, ((1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2) ^ d v) = 0 := by
        by_contra hne
        exact hw ((evA_diag d hne).trans hcol)
      rw [hz, mul_zero, mul_zero]
  have hfse : Formalism.REAL.fockF s (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) =
      Formalism.REAL.fockF P (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) := by
    rw [evA_fock_right s, evA_fock_right P]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) m = ν := heRow (mem_support_iff.mp hm)
    rw [hP, coeff_weightedHomogeneousComponent, if_pos hw]
  have hfce : ∀ e : MvPolynomial (Fin N × Fin N) ℂ,
      Formalism.REAL.fockF (c • e) e = c * Formalism.REAL.fockF e e := by
    intro e
    rw [evA_fock_right, evA_fock_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul]; ring
  have hFne : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) (Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν) ≠ 0 := by
    have h := (Formalism.GradedWeylDivisibility.fockPos (Fin N × Fin N) _ (Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl ν)).1
    intro h0; rw [h0] at h; simp at h
  unfold normFock
  rw [he, hev, hfse, hc, hfce, mul_div_assoc, div_self hFne, mul_one]
  unfold evalM
  rw [smul_eq_C_mul, eval_mul, eval_C]
  have h1 := evA_hw_one ν
  unfold evalM at h1
  rw [h1, mul_one]

end PI.WSF
