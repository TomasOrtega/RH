import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
import Mathlib

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

namespace PowSpanB

variable {m n : ℕ} (ε : Fin m → Bool)

def lf (b : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, b i j • (Qp ε j i : PX m n)

/- English proof (translation)
Simplify using `only [lf, C_mul']`.
-/
theorem lf_eq (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) = lf ε b := by
  simp only [lf, C_mul']

/- English proof (translation)
Simplify using `only [lf, Matrix.add_apply, add_smul, Finset.sum_add_distrib]`.
-/
theorem lf_add (b c : Matrix (Fin n) (Fin n) ℂ) : lf ε (b + c) = lf ε b + lf ε c := by
  simp only [lf, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [lf, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]`.
-/
theorem lf_smul (z : ℂ) (b : Matrix (Fin n) (Fin n) ℂ) : lf ε (z • b) = z • lf ε b := by
  simp only [lf, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/- English proof (translation)
Simplify using `[lf, Matrix.single_apply, ite_smul, ite_and]`.
-/
theorem lf_single (a b : Fin n) : lf ε (Matrix.single b a (1 : ℂ)) = (Qp ε a b : PX m n) := by
  simp [lf, Matrix.single_apply, ite_smul, ite_and]

def W : Set (PX m n) := {w | ∃ h : Matrix (Fin n) (Fin n) ℂ, h.IsHermitian ∧ w = lf ε h}

def S : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {R | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), b.IsHermitian ∧
    R = (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k}

/- English proof (translation)
Take `⟨h, hh, rfl⟩` from `hw`. Conclude with `Submodule.subset_span ⟨h, k, hh, by rw [lf_eq]⟩`.
-/
theorem pow_mem {w : PX m n} (hw : w ∈ W ε) (k : ℕ) : w ^ k ∈ S ε := by
  obtain ⟨h, hh, rfl⟩ := hw
  exact Submodule.subset_span ⟨h, k, hh, by rw [lf_eq]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, Matrix.isHermitian_zero, by simp [lf]⟩`.
-/
theorem zero_mem_W : (0 : PX m n) ∈ W ε :=
  ⟨0, Matrix.isHermitian_zero, by simp [lf]⟩

/- English proof (translation)
Take `⟨h1, hh1, rfl⟩` from `hw`. Take `⟨h2, hh2, rfl⟩` from `hv`. Use `⟨(t : ℂ) • h2 + h1, ?_, by rw [lf_add, lf_smul]⟩` and prove the remaining obligations. Use `show Matrix.conjTranspose ((t : ℂ) • h2 + h1) = _`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hh2.eq, hh1.eq]`.

Simplify using the standard rewrite rules.
-/
theorem natCast_smul_add_mem_W {w v : PX m n} (hw : w ∈ W ε) (hv : v ∈ W ε) (t : ℕ) : (t : ℂ) • v + w ∈ W ε := by
  obtain ⟨h1, hh1, rfl⟩ := hw
  obtain ⟨h2, hh2, rfl⟩ := hv
  refine ⟨(t : ℂ) • h2 + h1, ?_, by rw [lf_add, lf_smul]⟩
  show Matrix.conjTranspose ((t : ℂ) • h2 + h1) = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hh2.eq, hh1.eq]
  simp

/- English proof (translation)
Use `⟨(1 / 2 : ℂ) • (b + Matrix.conjTranspose b), (-Complex.I / 2) • (b - Matrix.conjTranspose b), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Matrix.conjTranspose ((1 / 2 : ℂ) • (b + Matrix.conjTranspose b)) = _`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use `show Matrix.conjTranspose ((-Complex.I / 2) • (b - Matrix.conjTranspose b)) = _`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `i j`.

Simplify using `[Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_decomp (b : Matrix (Fin n) (Fin n) ℂ) : ∃ H1 H2 : Matrix (Fin n) (Fin n) ℂ,
    H1.IsHermitian ∧ H2.IsHermitian ∧ b = H1 + Complex.I • H2 := by
  refine ⟨(1 / 2 : ℂ) • (b + Matrix.conjTranspose b), (-Complex.I / 2) • (b - Matrix.conjTranspose b), ?_, ?_, ?_⟩
  · show Matrix.conjTranspose ((1 / 2 : ℂ) • (b + Matrix.conjTranspose b)) = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  · show Matrix.conjTranspose ((-Complex.I / 2) • (b - Matrix.conjTranspose b)) = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring
  · ext i j
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring_nf
    rw [Complex.I_sq]
    ring

/- English proof (translation)
Set `V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ` to `Matrix.vandermonde (fun t : Fin (N + 1) => ((t : ℕ) : ℂ))`. Establish `hV : IsUnit V.det`. Use `isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)` and prove the remaining obligations. Introduce `a b hab`. Conclude with `Fin.ext (Nat.cast_injective hab)`.

Establish `key : ∑ t : Fin (N + 1), (V⁻¹ ⟨k, hk⟩ t) • (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j) = c k`. Establish `e : ∀ t : Fin (N + 1), (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j) = ∑ j : Fin (N + 1), V t j • c j`. Introduce `t`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun j => (((t : ℕ) : ℂ) ^ j) • c j)]`. Simplify using `[V, Matrix.vandermonde_apply]`.

Repeatedly rewrite using `[e, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`. Establish `hm : ∀ j : Fin (N + 1), ∑ t : Fin (N + 1), V⁻¹ ⟨k, hk⟩ t * V t j = (V⁻¹ * V) ⟨k, hk⟩ j`. Introduce `j`.

Rewrite using `[Matrix.mul_apply]`. Repeatedly rewrite using `[hm, Matrix.nonsing_inv_mul _ hV, Matrix.one_apply, ite_smul, one_smul, zero_smul]`. Simplify using the standard rewrite rules. Rewrite using `[← key]`. Conclude with `Submodule.sum_mem _ (fun t _ => T.smul_mem _ (h t))`.
-/
private theorem coeff_mem_of_forall_natCast_poly_sum_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Submodule ℂ M) (N : ℕ)
    (c : ℕ → M) (h : ∀ t : ℕ, ∑ j ∈ Finset.range (N + 1), ((t : ℂ) ^ j) • c j ∈ T)
    (k : ℕ) (hk : k < N + 1) : c k ∈ T := by
  let V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Matrix.vandermonde (fun t : Fin (N + 1) => ((t : ℕ) : ℂ))
  have hV : IsUnit V.det := by
    refine isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)
    intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  have key : ∑ t : Fin (N + 1), (V⁻¹ ⟨k, hk⟩ t) • (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j) = c k := by
    have e : ∀ t : Fin (N + 1), (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j)
        = ∑ j : Fin (N + 1), V t j • c j := by
      intro t
      rw [← Fin.sum_univ_eq_sum_range (fun j => (((t : ℕ) : ℂ) ^ j) • c j)]
      simp [V, Matrix.vandermonde_apply]
    simp_rw [e, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hm : ∀ j : Fin (N + 1), ∑ t : Fin (N + 1), V⁻¹ ⟨k, hk⟩ t * V t j = (V⁻¹ * V) ⟨k, hk⟩ j := by
      intro j
      rw [Matrix.mul_apply]
    simp_rw [hm, Matrix.nonsing_inv_mul _ hV, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  rw [← key]
  exact Submodule.sum_mem _ (fun t _ => T.smul_mem _ (h t))

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `_ w hw r`. Simplify using `using pow_mem ε hw r`.

Consider the case `cons v l ih`. Introduce `hl w hw r`. Establish `hv : v ∈ W ε` using `hl v (by simp)`. Establish `ih'` using `ih (fun u hu => hl u (by simp [hu]))`. Establish `h1 : ∀ t : ℕ, ∑ j ∈ Finset.range (r + 1 + 1), ((t : ℂ) ^ j) • (l.prod * (v ^ j * w ^ (r + 1 - j) * (((r + 1).choose j : ℕ) : PX m n))) ∈ S ε`.

Introduce `t`. Use `ih' _ (natCast_smul_add_mem_W ε hw hv t) (r + 1)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[add_pow, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[smul_pow, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]`. Establish `h2` using `coeff_mem_of_forall_natCast_poly_sum_mem (S ε) (r + 1) _ h1 1 (by omega)`. Establish `e : (v :: l).prod * w ^ r = ((r + 1 : ℕ) : ℂ)⁻¹ • (l.prod * (v ^ 1 * w ^ (r + 1 - 1) * (((r + 1).choose 1 : ℕ) : PX m n)))`. Rewrite using `[Nat.choose_one_right, pow_one, Nat.add_sub_cancel, List.prod_cons]`. Rewrite using `[show (((r + 1 : ℕ)) : PX m n) = ((r + 1 : ℕ) : ℂ) • (1 : PX m n) by`.

Rewrite using `[Nat.cast_smul_eq_nsmul, nsmul_one]]`. Rewrite using `[mul_smul_comm, mul_smul_comm, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)), one_smul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(S ε).smul_mem _ h2`.
-/
theorem core : ∀ l : List (PX m n), (∀ v ∈ l, v ∈ W ε) → ∀ w ∈ W ε, ∀ r : ℕ, l.prod * w ^ r ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ w hw r
    simpa using pow_mem ε hw r
  | cons v l ih =>
    intro hl w hw r
    have hv : v ∈ W ε := hl v (by simp)
    have ih' := ih (fun u hu => hl u (by simp [hu]))
    have h1 : ∀ t : ℕ, ∑ j ∈ Finset.range (r + 1 + 1), ((t : ℂ) ^ j) •
        (l.prod * (v ^ j * w ^ (r + 1 - j) * (((r + 1).choose j : ℕ) : PX m n))) ∈ S ε := by
      intro t
      have := ih' _ (natCast_smul_add_mem_W ε hw hv t) (r + 1)
      convert this using 1
      rw [add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_pow, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    have h2 := coeff_mem_of_forall_natCast_poly_sum_mem (S ε) (r + 1) _ h1 1 (by omega)
    have e : (v :: l).prod * w ^ r = ((r + 1 : ℕ) : ℂ)⁻¹ •
        (l.prod * (v ^ 1 * w ^ (r + 1 - 1) * (((r + 1).choose 1 : ℕ) : PX m n))) := by
      rw [Nat.choose_one_right, pow_one, Nat.add_sub_cancel, List.prod_cons]
      rw [show (((r + 1 : ℕ)) : PX m n) = ((r + 1 : ℕ) : ℂ) • (1 : PX m n) by
        rw [Nat.cast_smul_eq_nsmul, nsmul_one]]
      rw [mul_smul_comm, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)), one_smul]
      ring
    rw [e]
    exact (S ε).smul_mem _ h2

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `_ q hq`. Simplify using `using core ε q hq 0 (zero_mem_W ε) 0`.

Consider the case `cons x l ih`. Introduce `hl q hq`. Establish `hx : x ∈ Submodule.span ℂ (W ε)` using `hl x (by simp)`. Establish `hl' : ∀ y ∈ l, y ∈ Submodule.span ℂ (W ε)` using `fun y hy => hl y (by simp [hy])`. Use `clear hl`.

Rewrite using `[List.prod_cons]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Use `ih hl' (y :: q) (by` as an intermediate fact. Introduce `v hv`.

Break down `List.mem_cons.mp hv with h | h` into its components or cases. Conclude with `h ▸ hy`. Conclude with `hq v h)`. Rewrite `this` using `[List.prod_cons]`. Rewrite using `[← mul_assoc, mul_comm q.prod y]`.

Conclude with `this`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Rewrite using `[add_mul, mul_add]`. Conclude with `add_mem ha hb`.

Consider the case `smul z a _ ha`. Rewrite using `[smul_mul_assoc, mul_smul_comm]`. Conclude with `(S ε).smul_mem z ha`.
-/
private theorem list_prod_mul_span_prod_mem_S : ∀ l : List (PX m n), (∀ x ∈ l, x ∈ Submodule.span ℂ (W ε)) →
    ∀ q : List (PX m n), (∀ v ∈ q, v ∈ W ε) → q.prod * l.prod ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ q hq
    simpa using core ε q hq 0 (zero_mem_W ε) 0
  | cons x l ih =>
    intro hl q hq
    have hx : x ∈ Submodule.span ℂ (W ε) := hl x (by simp)
    have hl' : ∀ y ∈ l, y ∈ Submodule.span ℂ (W ε) := fun y hy => hl y (by simp [hy])
    clear hl
    rw [List.prod_cons]
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have := ih hl' (y :: q) (by
        intro v hv
        rcases List.mem_cons.mp hv with h | h
        · exact h ▸ hy
        · exact hq v h)
      rw [List.prod_cons] at this
      rw [← mul_assoc, mul_comm q.prod y]
      exact this
    | zero => simp
    | add a b _ _ ha hb =>
      rw [add_mul, mul_add]
      exact add_mem ha hb
    | smul z a _ ha =>
      rw [smul_mul_assoc, mul_smul_comm]
      exact (S ε).smul_mem z ha

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Algebra.adjoin_eq_span]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨l, hl, rfl⟩` from `Submonoid.exists_list_of_mem_closure hx`.

Use `list_prod_mul_span_prod_mem_S ε l (by` as an intermediate fact. Introduce `y hy`. Take `⟨⟨a, b⟩, rfl⟩` from `hl y hy`. Take `⟨H1, H2, h1, h2, hb⟩` from `herm_decomp (Matrix.single b a (1 : ℂ))`. Establish `e : (Qp ε a b : PX m n) = lf ε H1 + Complex.I • lf ε H2`.

Rewrite using `[← lf_single, hb, lf_add, lf_smul]`. Use `show (Qp ε a b : PX m n) ∈ _`. Rewrite using `[e]`. Conclude with `add_mem (Submodule.subset_span ⟨H1, h1, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨H2, h2, rfl⟩))) [] (by simp)`. Simplify using `using this`.

Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `R ⟨b, k, _, rfl⟩`. Use `show _ ∈ Algebra.adjoin ℂ _`. Use `Subalgebra.pow_mem _ (Subalgebra.sum_mem _ (fun i _ => Subalgebra.sum_mem _ (fun j _ => ?_))) k` and prove the remaining obligations. Use `Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨(j, i), rfl⟩)` and prove the remaining obligations.

Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `Subalgebra.algebraMap_mem _ _`.
-/
theorem span_eq :
    (Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))).toSubmodule = S ε := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.mpr ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    have := list_prod_mul_span_prod_mem_S ε l (by
      intro y hy
      obtain ⟨⟨a, b⟩, rfl⟩ := hl y hy
      obtain ⟨H1, H2, h1, h2, hb⟩ := herm_decomp (Matrix.single b a (1 : ℂ))
      have e : (Qp ε a b : PX m n) = lf ε H1 + Complex.I • lf ε H2 := by
        rw [← lf_single, hb, lf_add, lf_smul]
      show (Qp ε a b : PX m n) ∈ _
      rw [e]
      exact add_mem (Submodule.subset_span ⟨H1, h1, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨H2, h2, rfl⟩))) [] (by simp)
    simpa using this
  · refine Submodule.span_le.mpr ?_
    rintro R ⟨b, k, _, rfl⟩
    show _ ∈ Algebra.adjoin ℂ _
    refine Subalgebra.pow_mem _ (Subalgebra.sum_mem _ (fun i _ => Subalgebra.sum_mem _ (fun j _ => ?_))) k
    refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨(j, i), rfl⟩)
    rw [← MvPolynomial.algebraMap_eq]
    exact Subalgebra.algebraMap_mem _ _

end PowSpanB

/- English proof (translation)
Introduce `_ _ ε` and use `PowSpanB.span_eq ε`.
-/
theorem powSpan : PowSpan := fun _ _ ε => PowSpanB.span_eq ε

end PositivityTheory.Rg.Sw.FFTSteps
