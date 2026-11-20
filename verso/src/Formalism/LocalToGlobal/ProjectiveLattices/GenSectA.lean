import Mathlib

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)

abbrev KT : Type := MvPolynomial (Fin (D + 1) × Fin m) K

abbrev KTf : Type := FractionRing (KT K D m)

abbrev ΩT : Type := MvPolynomial (Fin (D + 1) × Fin m) Ω

def ktToΩ : KT K D m →+* ΩT Ω D m := MvPolynomial.map (algebraMap K Ω)

def KTS : Submonoid (ΩT Ω D m) := (nonZeroDivisors (KT K D m)).map (ktToΩ K Ω D m)

abbrev RS : Type := Localization (KTS K Ω D m)

instance algKTR : Algebra (KTf K D m) (RS K Ω D m) :=
  (IsLocalization.map (M := nonZeroDivisors (KT K D m)) (T := KTS K Ω D m) (RS K Ω D m) (ktToΩ K Ω D m)
    (Submonoid.le_comap_map _) :
    KTf K D m →+* RS K Ω D m).toAlgebra

variable {K Ω D m}

def sec (x : Fin m → Ω) (i : Fin D) : ΩT Ω D m := ∑ j, X (i.succ, j) * C (x j)

variable (K) in

def Is (x : Fin m → Ω) : Ideal (RS K Ω D m) :=
  Ideal.span (Set.range fun i : Fin D => algebraMap (ΩT Ω D m) (RS K Ω D m) (sec x i))

def Zs (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : Prop := p.1 ≠ 0 ∧ p.2 = j₀

instance (j₀ : Fin m) : DecidablePred (Zs (D := D) j₀) := fun p => by unfold Zs; infer_instance

variable (Ω D) in

abbrev CT (j₀ : Fin m) : Type := MvPolynomial {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p} Ω

def xv (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : CT Ω D j₀ :=
  if h : Zs j₀ p then 0 else X ⟨p, h⟩

def rr (x : Fin m → Ω) (j₀ : Fin m) (j : Fin m) : Ω := x j / x j₀

def gs (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : CT Ω D j₀ :=
  if Zs j₀ p then -∑ k, xv j₀ (p.1, k) * C (rr x j₀ k) else xv j₀ p

def psi (x : Fin m → Ω) (j₀ : Fin m) : ΩT Ω D m →ₐ[Ω] CT Ω D j₀ := aeval (gs x j₀)

def incl (j₀ : Fin m) : CT Ω D j₀ →ₐ[Ω] ΩT Ω D m := rename Subtype.val

/- English proof (translation)
Use `first`. Consider the case `(rw [xv, dif_neg h])`. Consider the case `simp [xv, h]`.
-/
theorem xv_of_not {j₀ : Fin m} {p : Fin (D + 1) × Fin m} (h : ¬ Zs j₀ p) :
    xv (Ω := Ω) j₀ p = X ⟨p, h⟩ := by
  first
  | (rw [xv, dif_neg h])
  | simp [xv, h]

/- English proof (translation)
Use `first`. Consider the case `(rw [xv, dif_pos h])`. Consider the case `simp [xv, h]`.
-/
theorem xv_of_Z {j₀ : Fin m} {p : Fin (D + 1) × Fin m} (h : Zs j₀ p) :
    xv (Ω := Ω) j₀ p = 0 := by
  first
  | (rw [xv, dif_pos h])
  | simp [xv, h]

/- English proof (translation)
Use `first`. Consider the case `(rw [psi, aeval_X])`. Consider the case `simp [psi]`.
-/
theorem psi_X (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) :
    psi x j₀ (X p) = gs x j₀ p := by
  first
  | (rw [psi, aeval_X])
  | simp [psi]

/- English proof (translation)
Use `first`. Consider the case `(rw [psi, aeval_C, MvPolynomial.algebraMap_eq])`. Consider the case `simp [psi]`. Consider the case `exact (psi x j₀).commutes a`.
-/
theorem psi_C (x : Fin m → Ω) (j₀ : Fin m) (a : Ω) :
    psi (D := D) x j₀ (C a) = C a := by
  first
  | (rw [psi, aeval_C, MvPolynomial.algebraMap_eq])
  | simp [psi]
  | exact (psi x j₀).commutes a

/- English proof (translation)
Use `first`. Consider the case `(rw [incl, rename_C])`. Consider the case `simp [incl]`. Consider the case `exact (incl j₀).commutes a`.
-/
theorem incl_C (j₀ : Fin m) (a : Ω) : incl (D := D) j₀ (C a) = C a := by
  first
  | (rw [incl, rename_C])
  | simp [incl]
  | exact (incl j₀).commutes a

/- English proof (translation)
Establish `h : (psi x j₀).comp (incl j₀) = AlgHom.id Ω (CT Ω D j₀)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `q`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, incl, rename_X, psi, aeval_X]`. Rewrite using `[gs, if_neg q.2, xv_of_not q.2]`.

Apply the tactic sequence `try rfl`. Conclude with `DFunLike.congr_fun h f`.
-/
theorem psi_incl (x : Fin m → Ω) (j₀ : Fin m) (f : CT Ω D j₀) : psi x j₀ (incl j₀ f) = f := by
  have h : (psi x j₀).comp (incl j₀) = AlgHom.id Ω (CT Ω D j₀) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [AlgHom.comp_apply, AlgHom.id_apply, incl, rename_X, psi, aeval_X]
    rw [gs, if_neg q.2, xv_of_not q.2]
    try rfl
  exact DFunLike.congr_fun h f

/- English proof (translation)
Distinguish the cases in `h : j = j₀`. Establish `hz : Zs j₀ (i.succ, j)`. Unfold `Zs`. Conclude with `⟨Fin.succ_ne_zero i, h⟩`. Rewrite using `[gs, if_pos hz, xv_of_Z hz, if_pos h, zero_add]`.

Apply the tactic sequence `try rfl`. Establish `hz : ¬ Zs j₀ (i.succ, j)`. Unfold `Zs`. Conclude with `fun hz => h hz.2`. Rewrite using `[gs, if_neg hz, if_neg h, add_zero]`.
-/
theorem gs_succ (x : Fin m → Ω) (j₀ : Fin m) (i : Fin D) (j : Fin m) :
    gs x j₀ (i.succ, j) = xv j₀ (i.succ, j) +
      if j = j₀ then -∑ k, xv j₀ (i.succ, k) * C (rr x j₀ k) else 0 := by
  by_cases h : j = j₀
  · have hz : Zs j₀ (i.succ, j) := by
      unfold Zs
      exact ⟨Fin.succ_ne_zero i, h⟩
    rw [gs, if_pos hz, xv_of_Z hz, if_pos h, zero_add]
    try rfl
  · have hz : ¬ Zs j₀ (i.succ, j) := by
      unfold Zs
      exact fun hz => h hz.2
    rw [gs, if_neg hz, if_neg h, add_zero]

/- English proof (translation)
Establish `hS : (∑ k, xv (Ω` using `Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) = ∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (x k) := by`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← C_mul, rr]`. Use `congr 2`.

Use `first`. Consider the case `exact div_mul_cancel₀ (x k) hx₀`. Consider the case `field_simp`. Establish `hI : ∑ j : Fin m, (if j = j₀ then -∑ k, xv (Ω` using `Ω) j₀ (i.succ, k) * C (rr x j₀ k) else 0) * C (x j) = -(∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) := by`. Rewrite using `[Finset.sum_eq_single j₀]`.

Rewrite using `[if_pos rfl]`. Introduce `b _ hb`. Rewrite using `[if_neg hb, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j₀) h`.

Establish `h1 : psi x j₀ (sec x i) = ∑ j, gs x j₀ (i.succ, j) * C (x j)`. Simplify using `only [sec, map_sum, map_mul, psi_X, psi_C]`. Rewrite using `[h1]`. Simplify using `only [gs_succ, add_mul]`. Rewrite using `[Finset.sum_add_distrib, hI, neg_mul, hS]`.

Use `first`. Consider the case `exact add_neg_cancel _`. Consider the case `exact add_right_neg _`. Consider the case `abel`.
-/
theorem psi_sec (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (i : Fin D) :
    psi x j₀ (sec x i) = 0 := by
  have hS : (∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) =
      ∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (x k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← C_mul, rr]
    congr 2
    first
    | exact div_mul_cancel₀ (x k) hx₀
    | field_simp
  have hI : ∑ j : Fin m, (if j = j₀ then -∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k) else 0) * C (x j) =
      -(∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) := by
    rw [Finset.sum_eq_single j₀]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  have h1 : psi x j₀ (sec x i) = ∑ j, gs x j₀ (i.succ, j) * C (x j) := by
    simp only [sec, map_sum, map_mul, psi_X, psi_C]
  rw [h1]
  simp only [gs_succ, add_mul]
  rw [Finset.sum_add_distrib, hI, neg_mul, hS]
  first
  | exact add_neg_cancel _
  | exact add_right_neg _
  | abel

/- English proof (translation)
Distinguish the cases in `h : k = j₀`. Establish `hz : Zs j₀ (i.succ, k)`. Unfold `Zs`. Conclude with `⟨Fin.succ_ne_zero i, h⟩`. Rewrite using `[xv_of_Z hz, map_zero, if_pos h]`.

Establish `hz : ¬ Zs j₀ (i.succ, k)`. Unfold `Zs`. Conclude with `fun hz => h hz.2`. Rewrite using `[xv_of_not hz, if_neg h, incl, rename_X]`. Apply the tactic sequence `try rfl`.
-/
theorem incl_xv_succ (j₀ : Fin m) (i : Fin D) (k : Fin m) :
    incl (Ω := Ω) j₀ (xv j₀ (i.succ, k)) = if k = j₀ then 0 else X (i.succ, k) := by
  by_cases h : k = j₀
  · have hz : Zs j₀ (i.succ, k) := by
      unfold Zs
      exact ⟨Fin.succ_ne_zero i, h⟩
    rw [xv_of_Z hz, map_zero, if_pos h]
  · have hz : ¬ Zs j₀ (i.succ, k) := by
      unfold Zs
      exact fun hz => h hz.2
    rw [xv_of_not hz, if_neg h, incl, rename_X]
    try rfl

/- English proof (translation)
Establish `hz : Zs j₀ (i.succ, j₀)`. Unfold `Zs`. Conclude with `⟨Fin.succ_ne_zero i, rfl⟩`. Rewrite using `[gs, if_pos hz]`. Simplify using `only [map_neg, map_sum, map_mul, incl_C, incl_xv_succ, sub_neg_eq_add, sec, Finset.mul_sum]`.

Establish `hX : (X (i.succ, j₀) : ΩT Ω D m) = ∑ j : Fin m, if j = j₀ then (X (i.succ, j₀) : ΩT Ω D m) else 0`. Simplify using the standard rewrite rules. Rewrite using `[hX, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j = j₀`.

Substitute `h` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, zero_mul, add_zero, mul_left_comm, ← C_mul, inv_mul_cancel₀ hx₀, C_1, mul_one]`. Rewrite using `[if_neg h, if_neg h, zero_add, rr, div_eq_mul_inv, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem X_sub_incl_gs (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (i : Fin D) :
    X (i.succ, j₀) - incl j₀ (gs x j₀ (i.succ, j₀)) = C (x j₀)⁻¹ * sec x i := by
  have hz : Zs j₀ (i.succ, j₀) := by
    unfold Zs
    exact ⟨Fin.succ_ne_zero i, rfl⟩
  rw [gs, if_pos hz]
  simp only [map_neg, map_sum, map_mul, incl_C, incl_xv_succ, sub_neg_eq_add, sec, Finset.mul_sum]
  have hX : (X (i.succ, j₀) : ΩT Ω D m) = ∑ j : Fin m, if j = j₀ then (X (i.succ, j₀) : ΩT Ω D m) else 0 := by
    simp
  rw [hX, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = j₀
  · subst h
    rw [if_pos rfl, if_pos rfl, zero_mul, add_zero, mul_left_comm, ← C_mul, inv_mul_cancel₀ hx₀, C_1, mul_one]
  · rw [if_neg h, if_neg h, zero_add, rr, div_eq_mul_inv, C_mul]
    ring

/- English proof (translation)
Establish `hgen : ∀ p : Fin (D + 1) × Fin m, X p - incl j₀ (psi x j₀ (X p)) ∈ Ideal.span (Set.range (sec x))`. Introduce `p`. Rewrite using `[psi_X]`. Distinguish the cases in `hp : Zs j₀ p`. Take `⟨i', j⟩` from `p`.

Establish `hp' : i' ≠ 0 ∧ j = j₀` using `hp`. Take `⟨i, rfl⟩ : ∃ i : Fin D, i.succ = i'` from `by first`. Consider the case `exact Fin.exists_succ_eq.mpr hp'.1`. Consider the case `exact ⟨i'.pred hp'.1, Fin.succ_pred i' hp'.1⟩`. Rewrite using `[hp'.2, X_sub_incl_gs x j₀ hx₀ i]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`. Use `first`. Consider the case `(rw [gs, if_neg hp, xv_of_not hp, incl, rename_X, sub_self]`. Conclude with `Ideal.zero_mem _)`. Consider the case `simp [gs, hp, xv_of_not hp, incl]`.

Proceed by induction on `f using MvPolynomial.induction_on`. Use `next a =>`. Rewrite using `[psi_C, incl_C, sub_self]`. Conclude with `Ideal.zero_mem _`. Use `next f g hf hg =>`.

Establish `e : f + g - incl j₀ (psi x j₀ (f + g)) = (f - incl j₀ (psi x j₀ f)) + (g - incl j₀ (psi x j₀ g))`. Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ hf hg`.

Use `next f p hf =>`. Establish `e : f * X p - incl j₀ (psi x j₀ (f * X p)) = (f - incl j₀ (psi x j₀ f)) * X p + incl j₀ (psi x j₀ f) * (X p - incl j₀ (psi x j₀ (X p)))`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (hgen p))`.
-/
theorem sub_incl_psi_mem (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    f - incl j₀ (psi x j₀ f) ∈ Ideal.span (Set.range (sec x)) := by
  have hgen : ∀ p : Fin (D + 1) × Fin m,
      X p - incl j₀ (psi x j₀ (X p)) ∈ Ideal.span (Set.range (sec x)) := by
    intro p
    rw [psi_X]
    by_cases hp : Zs j₀ p
    · obtain ⟨i', j⟩ := p
      have hp' : i' ≠ 0 ∧ j = j₀ := hp
      obtain ⟨i, rfl⟩ : ∃ i : Fin D, i.succ = i' := by
        first
        | exact Fin.exists_succ_eq.mpr hp'.1
        | exact ⟨i'.pred hp'.1, Fin.succ_pred i' hp'.1⟩
      rw [hp'.2, X_sub_incl_gs x j₀ hx₀ i]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · first
      | (rw [gs, if_neg hp, xv_of_not hp, incl, rename_X, sub_self]
         exact Ideal.zero_mem _)
      | simp [gs, hp, xv_of_not hp, incl]
  induction f using MvPolynomial.induction_on
  next a =>
    rw [psi_C, incl_C, sub_self]
    exact Ideal.zero_mem _
  next f g hf hg =>
    have e : f + g - incl j₀ (psi x j₀ (f + g)) =
        (f - incl j₀ (psi x j₀ f)) + (g - incl j₀ (psi x j₀ g)) := by
      simp only [map_add]
      ring
    rw [e]
    exact Ideal.add_mem _ hf hg
  next f p hf =>
    have e : f * X p - incl j₀ (psi x j₀ (f * X p)) =
        (f - incl j₀ (psi x j₀ f)) * X p + incl j₀ (psi x j₀ f) * (X p - incl j₀ (psi x j₀ (X p))) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (hgen p))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hm` using `sub_incl_psi_mem x j₀ hx₀ f`. Rewrite `hm` using `[h, map_zero, sub_zero]`. Then use the resulting hypothesis. Introduce `hf`.

Establish `hle : Ideal.span (Set.range (sec (D` using `D) x)) ≤ RingHom.ker (psi (D := D) x j₀) := by`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `RingHom.mem_ker.mpr (psi_sec x j₀ hx₀ i)`. Conclude with `RingHom.mem_ker.mp (hle hf)`.
-/
theorem psi_eq_zero_iff (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    psi x j₀ f = 0 ↔ f ∈ Ideal.span (Set.range (sec x)) := by
  constructor
  · intro h
    have hm := sub_incl_psi_mem x j₀ hx₀ f
    rwa [h, map_zero, sub_zero] at hm
  · intro hf
    have hle : Ideal.span (Set.range (sec (D := D) x)) ≤ RingHom.ker (psi (D := D) x j₀) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (psi_sec x j₀ hx₀ i)
    exact RingHom.mem_ker.mp (hle hf)

/- English proof (translation)
Distinguish the cases in `hp : Zs j₀ p`. Establish `hne : p ≠ q.1` using `fun h => q.2 (h ▸ hp)`. Rewrite using `[xv_of_Z hp, map_zero, if_neg hne]`. Rewrite using `[xv_of_not hp, pderiv_X, Pi.single_apply]`. Distinguish the cases in `h : p = q.1`.

Establish `e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) = q` using `Subtype.ext h`. Rewrite using `[if_pos e, if_pos h]`. Establish `e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) ≠ q` using `fun e => h (congrArg Subtype.val e)`. Rewrite using `[if_neg e, if_neg h]`.
-/
theorem pderiv_xv (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (p : Fin (D + 1) × Fin m) :
    pderiv q (xv (Ω := Ω) j₀ p) = if p = q.1 then 1 else 0 := by
  by_cases hp : Zs j₀ p
  · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
    rw [xv_of_Z hp, map_zero, if_neg hne]
  · rw [xv_of_not hp, pderiv_X, Pi.single_apply]
    by_cases h : p = q.1
    · have e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) = q := Subtype.ext h
      rw [if_pos e, if_pos h]
    · have e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) ≠ q :=
        fun e => h (congrArg Subtype.val e)
      rw [if_neg e, if_neg h]

/- English proof (translation)
Distinguish the cases in `hp : Zs j₀ p`. Establish `hne : p ≠ q.1` using `fun h => q.2 (h ▸ hp)`. Rewrite using `[gs, if_pos hp, if_neg hne, zero_sub, map_neg]`. Use `congr 1`. Simplify using `only [map_sum, Derivation.leibniz, pderiv_C, smul_zero, smul_eq_mul, pderiv_xv, mul_zero, zero_add]`.

Rewrite using `[Finset.sum_eq_single q.1.2]`. Distinguish the cases in `h1 : p.1 = q.1.1`. Establish `e : (p.1, q.1.2) = q.1` using `Prod.ext h1 rfl`. Rewrite using `[if_pos e, if_pos ⟨hp, h1⟩, mul_one]`. Establish `e : (p.1, q.1.2) ≠ q.1` using `fun h => h1 (by have h' := congrArg Prod.fst h; exact h')`.

Establish `hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1)` using `fun h => h1 h.2`. Rewrite using `[if_neg e, if_neg hn, mul_zero]`. Introduce `k _ hk`. Establish `e : (p.1, k) ≠ q.1` using `fun h => hk (congrArg Prod.snd h)`. Rewrite using `[if_neg e, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1)` using `fun h => hp h.1`. Rewrite using `[gs, if_neg hp, pderiv_xv, if_neg hn, sub_zero]`.
-/
theorem pderiv_gs (x : Fin m → Ω) (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p})
    (p : Fin (D + 1) × Fin m) :
    pderiv q (gs x j₀ p) = (if p = q.1 then 1 else 0) -
      if Zs j₀ p ∧ p.1 = q.1.1 then C (rr x j₀ q.1.2) else 0 := by
  by_cases hp : Zs j₀ p
  · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
    rw [gs, if_pos hp, if_neg hne, zero_sub, map_neg]
    congr 1
    simp only [map_sum, Derivation.leibniz, pderiv_C, smul_zero, smul_eq_mul, pderiv_xv, mul_zero, zero_add]
    rw [Finset.sum_eq_single q.1.2]
    · by_cases h1 : p.1 = q.1.1
      · have e : (p.1, q.1.2) = q.1 := Prod.ext h1 rfl
        rw [if_pos e, if_pos ⟨hp, h1⟩, mul_one]
      · have e : (p.1, q.1.2) ≠ q.1 := fun h => h1 (by have h' := congrArg Prod.fst h; exact h')
        have hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1) := fun h => h1 h.2
        rw [if_neg e, if_neg hn, mul_zero]
    · intro k _ hk
      have e : (p.1, k) ≠ q.1 := fun h => hk (congrArg Prod.snd h)
      rw [if_neg e, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1) := fun h => hp h.1
    rw [gs, if_neg hp, pderiv_xv, if_neg hn, sub_zero]

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on`. Use `next a => first`. Consider the case `(rw [aeval_C, MvPolynomial.algebraMap_apply, pderiv_C]`. Simplify using `only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero])`. Consider the case `simp`.

Use `next G₁ G₂ h₁ h₂ =>`. Simplify using `only [map_add, h₁, h₂, add_mul, Finset.sum_add_distrib]`. Use `next G i h =>`. Establish `e1 : ∀ p, pderiv p (G * X i) = G * pderiv p (X i) + X i * pderiv p G` using `fun p => by`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`.

Establish `hs : ∑ p, aeval u (G * pderiv p (X i)) * pderiv q (u p) = aeval u G * pderiv q (u i)`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[pderiv_X_self, mul_one]`. Introduce `b _ hb`. Establish `h0 : pderiv b (X i : MvPolynomial ι K) = 0` using `by first`.

Consider the case `exact pderiv_X_of_ne (Ne.symm hb)`. Consider the case `exact pderiv_X_of_ne hb`. Consider the case `simp [pderiv_X, Pi.single_apply, hb, Ne.symm hb]`. Rewrite using `[h0, mul_zero, map_zero, zero_mul]`. Introduce `hi`.

Conclude with `absurd (Finset.mem_univ i) hi`. Rewrite using `[map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h]`. Simplify using `only [e1, map_add, add_mul, Finset.sum_add_distrib]`. Rewrite using `[hs]`. Simplify using `only [map_mul, aeval_X, Finset.mul_sum, mul_assoc]`.
-/
theorem pderiv_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (j₀ : Fin m) (u : ι → CT Ω D j₀)
    (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (G : MvPolynomial ι K) :
    pderiv q (aeval u G) = ∑ p, aeval u (pderiv p G) * pderiv q (u p) := by
  induction G using MvPolynomial.induction_on
  next a =>
    first
    | (rw [aeval_C, MvPolynomial.algebraMap_apply, pderiv_C]
       simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero])
    | simp
  next G₁ G₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂, add_mul, Finset.sum_add_distrib]
  next G i h =>
    have e1 : ∀ p, pderiv p (G * X i) = G * pderiv p (X i) + X i * pderiv p G := fun p => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hs : ∑ p, aeval u (G * pderiv p (X i)) * pderiv q (u p) = aeval u G * pderiv q (u i) := by
      rw [Finset.sum_eq_single i]
      · rw [pderiv_X_self, mul_one]
      · intro b _ hb
        have h0 : pderiv b (X i : MvPolynomial ι K) = 0 := by
          first
          | exact pderiv_X_of_ne (Ne.symm hb)
          | exact pderiv_X_of_ne hb
          | simp [pderiv_X, Pi.single_apply, hb, Ne.symm hb]
        rw [h0, mul_zero, map_zero, zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h]
    simp only [e1, map_add, add_mul, Finset.sum_add_distrib]
    rw [hs]
    simp only [map_mul, aeval_X, Finset.mul_sum, mul_assoc]

end Formalism.L2.Pj.GenSect
