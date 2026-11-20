import Mathlib

noncomputable section

namespace GroundTheory.Automorphic.ContragredientTranspose

open Polynomial

section Cyclic

variable {F : Type*} [Field F]

def monicAssoc (q : F[X]) : F[X] := q * C q.leadingCoeff⁻¹

/- English proof (translation)
The claim follows from `monic_mul_leadingCoeff_inv hq`.
-/
theorem monicAssoc_monic {q : F[X]} (hq : q ≠ 0) : (monicAssoc q).Monic :=
  monic_mul_leadingCoeff_inv hq

/- English proof (translation)
The claim follows from `Dvd.intro _ rfl`.
-/
theorem dvd_monicAssoc (q : F[X]) : q ∣ monicAssoc q := Dvd.intro _ rfl

/- English proof (translation)
Distinguish the cases in `hq : q = 0`. Simplify using `[hq, monicAssoc]`. Use `⟨C q.leadingCoeff, ?_⟩` and prove the remaining obligations. Rewrite using `[monicAssoc, mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hq), C_1, mul_one]`.
-/
theorem monicAssoc_dvd (q : F[X]) : monicAssoc q ∣ q := by
  by_cases hq : q = 0
  · simp [hq, monicAssoc]
  · refine ⟨C q.leadingCoeff, ?_⟩
    rw [monicAssoc, mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hq), C_1, mul_one]

/- English proof (translation)
The claim follows from `associated_mul_unit_right _ _ (isUnit_C.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hq)).isUnit)`.
-/
theorem associated_monicAssoc {q : F[X]} (hq : q ≠ 0) : Associated q (monicAssoc q) :=
  associated_mul_unit_right _ _ (isUnit_C.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hq)).isUnit)

/- English proof (translation)
The claim follows from `natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hq))`.
-/
theorem natDegree_monicAssoc {q : F[X]} (hq : q ≠ 0) : (monicAssoc q).natDegree = q.natDegree :=
  natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hq))

def lcoeffMod (q f : F[X]) : F := (f %ₘ monicAssoc q).coeff (q.natDegree - 1)

/- English proof (translation)
Simplify using `[lcoeffMod, add_modByMonic]`.
-/
theorem lcoeffMod_add (q f g : F[X]) : lcoeffMod q (f + g) = lcoeffMod q f + lcoeffMod q g := by
  simp [lcoeffMod, add_modByMonic]

/- English proof (translation)
Simplify using `[lcoeffMod, ← smul_eq_C_mul, smul_modByMonic]`.
-/
theorem lcoeffMod_C_mul (q : F[X]) (c : F) (f : F[X]) :
    lcoeffMod q (C c * f) = c * lcoeffMod q f := by
  simp [lcoeffMod, ← smul_eq_C_mul, smul_modByMonic]

/- English proof (translation)
Establish `: f %ₘ monicAssoc q = 0` using `(modByMonic_eq_zero_iff_dvd (monicAssoc_monic hq)).2 ((monicAssoc_dvd q).trans h)`. Simplify using `[lcoeffMod, this]`.
-/
theorem lcoeffMod_of_dvd {q f : F[X]} (hq : q ≠ 0) (h : q ∣ f) : lcoeffMod q f = 0 := by
  have : f %ₘ monicAssoc q = 0 :=
    (modByMonic_eq_zero_iff_dvd (monicAssoc_monic hq)).2 ((monicAssoc_dvd q).trans h)
  simp [lcoeffMod, this]

/- English proof (translation)
Establish `e : f = (f - g) + g` using `by ring`. Rewrite using `[e, lcoeffMod_add, lcoeffMod_of_dvd hq h, zero_add]`.
-/
theorem lcoeffMod_eq_of_dvd_sub {q f g : F[X]} (hq : q ≠ 0) (h : q ∣ f - g) :
    lcoeffMod q f = lcoeffMod q g := by
  have e : f = (f - g) + g := by ring
  rw [e, lcoeffMod_add, lcoeffMod_of_dvd hq h, zero_add]

/- English proof (translation)
Use `set q' := monicAssoc q with hq'`. Establish `hm : q'.Monic` using `monicAssoc_monic hq`. Use `set r := f %ₘ q' with hr`. Establish `hr0 : r ≠ 0` using `fun h => hf ((dvd_monicAssoc q).trans ((modByMonic_eq_zero_iff_dvd hm).1 h))`. Establish `hdeg : r.natDegree < q.natDegree`.

Rewrite using `[← natDegree_monicAssoc hq]`. Conclude with `natDegree_lt_natDegree hr0 (degree_modByMonic_lt f hm)`. Use `set j := q.natDegree - 1 - r.natDegree`. Use `⟨X ^ j, ?_⟩` and prove the remaining obligations. Establish `e1 : (f * X ^ j) %ₘ q' = (r * X ^ j) %ₘ q'`.

Establish `: f * X ^ j = r * X ^ j + q' * ((f /ₘ q') * X ^ j)` using `by conv_lhs => rw [← modByMonic_add_div f q']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, add_modByMonic, ((modByMonic_eq_zero_iff_dvd hm).2 (dvd_mul_right _ _)), add_zero]`. Establish `hdeg2 : (r * X ^ j).natDegree = q.natDegree - 1`. Rewrite using `[natDegree_mul_X_pow _ hr0]`.

Use linear arithmetic over natural numbers and integers. Establish `e2 : (r * X ^ j) %ₘ q' = r * X ^ j`. Rewrite using `[modByMonic_eq_self_iff hm]`. Apply `degree_lt_degree` to reduce the goal to its premises. Rewrite using `[hdeg2, natDegree_monicAssoc hq]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[lcoeffMod, e1, e2]`. Establish `e3 : q.natDegree - 1 = r.natDegree + j` using `by omega`. Rewrite using `[e3, coeff_mul_X_pow]`. Conclude with `leadingCoeff_ne_zero.2 hr0`.
-/
theorem exists_lcoeffMod_mul_ne_zero {q f : F[X]} (hq : q ≠ 0) (hf : ¬ q ∣ f) :
    ∃ g, lcoeffMod q (f * g) ≠ 0 := by
  set q' := monicAssoc q with hq'
  have hm : q'.Monic := monicAssoc_monic hq
  set r := f %ₘ q' with hr
  have hr0 : r ≠ 0 := fun h =>
    hf ((dvd_monicAssoc q).trans ((modByMonic_eq_zero_iff_dvd hm).1 h))
  have hdeg : r.natDegree < q.natDegree := by
    rw [← natDegree_monicAssoc hq]
    exact natDegree_lt_natDegree hr0 (degree_modByMonic_lt f hm)
  set j := q.natDegree - 1 - r.natDegree
  refine ⟨X ^ j, ?_⟩
  have e1 : (f * X ^ j) %ₘ q' = (r * X ^ j) %ₘ q' := by
    have : f * X ^ j = r * X ^ j + q' * ((f /ₘ q') * X ^ j) := by
      conv_lhs => rw [← modByMonic_add_div f q']
      ring
    rw [this, add_modByMonic, ((modByMonic_eq_zero_iff_dvd hm).2 (dvd_mul_right _ _)), add_zero]
  have hdeg2 : (r * X ^ j).natDegree = q.natDegree - 1 := by
    rw [natDegree_mul_X_pow _ hr0]
    omega
  have e2 : (r * X ^ j) %ₘ q' = r * X ^ j := by
    rw [modByMonic_eq_self_iff hm]
    apply degree_lt_degree
    rw [hdeg2, natDegree_monicAssoc hq]
    omega
  rw [lcoeffMod, e1, e2]
  have e3 : q.natDegree - 1 = r.natDegree + j := by omega
  rw [e3, coeff_mul_X_pow]
  exact leadingCoeff_ne_zero.2 hr0

def ellQ (q : F[X]) (hq : q ≠ 0) : (F[X] ⧸ F[X] ∙ q) → F := fun a =>
  Quotient.liftOn' a (lcoeffMod q) (fun f g h => by
    have h' : f - g ∈ F[X] ∙ q := (Submodule.quotientRel_def _).1 h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h'
    exact lcoeffMod_eq_of_dvd_sub hq ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩)

variable {q : F[X]} (hq : q ≠ 0)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ellQ_mk (f : F[X]) : ellQ q hq (Submodule.Quotient.mk f) = lcoeffMod q f := rfl

omit hq in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mk_mul_mk (f g : F[X]) :
    (Submodule.Quotient.mk f : F[X] ⧸ F[X] ∙ q) * Submodule.Quotient.mk g =
      Submodule.Quotient.mk (f * g) := rfl

omit hq in
/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Rewrite using `[← Submodule.Quotient.mk_smul, smul_eq_mul, mk_mul_mk]`.
-/
theorem smul_eq_mk_mul (r : F[X]) (a : F[X] ⧸ F[X] ∙ q) :
    r • a = Submodule.Quotient.mk r * a := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mk_mul_mk]

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨g, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Rewrite using `[← Submodule.Quotient.mk_add, ellQ_mk, ellQ_mk, ellQ_mk, lcoeffMod_add]`.
-/
theorem ellQ_add (a b : F[X] ⧸ F[X] ∙ q) : ellQ q hq (a + b) = ellQ q hq a + ellQ q hq b := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [← Submodule.Quotient.mk_add, ellQ_mk, ellQ_mk, ellQ_mk, lcoeffMod_add]

/- English proof (translation)
Use `ellQ_add hq 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Simplify using `using this`.
-/
theorem ellQ_zero : ellQ q hq 0 = 0 := by
  have := ellQ_add hq 0 0
  rw [add_zero] at this
  simpa using this

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Rewrite using `[← Submodule.Quotient.mk_smul, smul_eq_mul, ellQ_mk, ellQ_mk, lcoeffMod_C_mul]`.
-/
theorem ellQ_C_smul (c : F) (a : F[X] ⧸ F[X] ∙ q) : ellQ q hq (C c • a) = c * ellQ q hq a := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, ellQ_mk, ellQ_mk, lcoeffMod_C_mul]

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Establish `hf : ¬ q ∣ f`. Introduce and unpack `⟨c, rfl⟩`. Apply `ha` to reduce the goal to its premises. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]`.

Conclude with `⟨c, by rw [smul_eq_mul, mul_comm]⟩`. Take `⟨g, hg⟩` from `exists_lcoeffMod_mul_ne_zero hq hf`. Conclude with `⟨Submodule.Quotient.mk g, by rwa [mk_mul_mk, ellQ_mk, mul_comm]⟩`.
-/
theorem exists_ellQ_mul_ne_zero {a : F[X] ⧸ F[X] ∙ q} (ha : a ≠ 0) :
    ∃ b, ellQ q hq (b * a) ≠ 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have hf : ¬ q ∣ f := by
    rintro ⟨c, rfl⟩
    apply ha
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    exact ⟨c, by rw [smul_eq_mul, mul_comm]⟩
  obtain ⟨g, hg⟩ := exists_lcoeffMod_mul_ne_zero hq hf
  exact ⟨Submodule.Quotient.mk g, by rwa [mk_mul_mk, ellQ_mk, mul_comm]⟩

end Cyclic

section Continuity

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

def ContCoeff {α : Type*} [TopologicalSpace α] (P : α → F[X]) : Prop :=
  ∀ k, Continuous fun a => (P a).coeff k

variable {α : Type*} [TopologicalSpace α]

/- English proof (translation)
Introduce `k` and use `by simp only [coeff_add] exact (hP k).add (hQ k)`.
-/
theorem ContCoeff.add {P Q : α → F[X]} (hP : ContCoeff P) (hQ : ContCoeff Q) :
    ContCoeff fun a => P a + Q a := fun k => by
  simp only [coeff_add]
  exact (hP k).add (hQ k)

/- English proof (translation)
Introduce `k` and use `by simp only [coeff_mul] exact continuous_finsetSum _ fun x _ => (hP x.1).mul (hQ x.2)`.
-/
theorem ContCoeff.mul {P Q : α → F[X]} (hP : ContCoeff P) (hQ : ContCoeff Q) :
    ContCoeff fun a => P a * Q a := fun k => by
  simp only [coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hP x.1).mul (hQ x.2)

omit [IsTopologicalRing F] in
/- English proof (translation)
Introduce `_` and use `continuous_const`.
-/
theorem ContCoeff.const (p : F[X]) : ContCoeff fun _ : α => p := fun _ => continuous_const

omit [IsTopologicalRing F] in
/- English proof (translation)
Introduce `k` and use `by simp only [coeff_C] split_ifs · exact hf · exact continuous_const`.
-/
theorem ContCoeff.C {f : α → F} (hf : Continuous f) : ContCoeff fun a => Polynomial.C (f a) :=
  fun k => by
    simp only [coeff_C]
    split_ifs
    · exact hf
    · exact continuous_const

/- English proof (translation)
Introduce `k` and use `by have e : ∀ a, (z • P a).coeff k = (z : F) * (P a).coeff k := fun a => by rw [zsmul_eq_mul, ← C_eq_intCast, coeff_C_mul] simp only [e] exact continuous_const.mul (hP k)`.
-/
theorem ContCoeff.zsmul {P : α → F[X]} (hP : ContCoeff P) (z : ℤ) :
    ContCoeff fun a => z • P a := fun k => by
  have e : ∀ a, (z • P a).coeff k = (z : F) * (P a).coeff k := fun a => by
    rw [zsmul_eq_mul, ← C_eq_intCast, coeff_C_mul]
  simp only [e]
  exact continuous_const.mul (hP k)

/- English proof (translation)
Introduce `k` and use `by simp only [finsetSum_coeff] exact continuous_finsetSum _ fun i hi => hP i hi k`.
-/
theorem ContCoeff.sum {ι : Type*} (s : Finset ι) {P : ι → α → F[X]}
    (hP : ∀ i ∈ s, ContCoeff (P i)) : ContCoeff fun a => ∑ i ∈ s, P i a := fun k => by
  simp only [finsetSum_coeff]
  exact continuous_finsetSum _ fun i hi => hP i hi k

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ContCoeff.const (α := α) (1 : F[X])`. Consider the case `insert j s hj ih`. Simplify using `only [Finset.prod_insert hj]`. Conclude with `(hP j (Finset.mem_insert_self _ _)).mul (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))`.
-/
theorem ContCoeff.prod {ι : Type*} (s : Finset ι) {P : ι → α → F[X]}
    (hP : ∀ i ∈ s, ContCoeff (P i)) : ContCoeff fun a => ∏ i ∈ s, P i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ContCoeff.const (α := α) (1 : F[X])
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    exact (hP j (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))

variable {m : Type*} [Fintype m] [DecidableEq m]

/- English proof (translation)
Apply the tactic sequence `have hentry : ∀ i j : m, ContCoeff fun A : Matrix m m F => A.charmatrix i j := by`. Introduce `i j`. Simplify using `only [Matrix.charmatrix_apply]`. Use `(ContCoeff.const _).add ?_` and prove the remaining obligations. Establish `hc : Continuous fun A : Matrix m m F => A i j` using `continuous_id.matrix_elem i j`.

Use `ContCoeff.C (α := Matrix m m F) (f := fun A => -A i j) hc.neg` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`. Establish `: ContCoeff fun A : Matrix m m F => A.charpoly`. Simplify using `only [Matrix.charpoly, Matrix.det_apply]`. Use `ContCoeff.sum _ fun σ _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `have hp := ContCoeff.prod Finset.univ fun i _ => hentry (σ i) i`. Use `hp.zsmul (Equiv.Perm.sign σ : ℤ)` as an intermediate fact. Simplify `this` using `only [Units.smul_def]`. Conclude with `this k`.
-/
theorem continuous_charpoly_coeff_of_fintype (k : ℕ) :
    Continuous fun A : Matrix m m F => A.charpoly.coeff k := by
  have hentry : ∀ i j : m, ContCoeff fun A : Matrix m m F => A.charmatrix i j := by
    intro i j
    simp only [Matrix.charmatrix_apply]
    refine (ContCoeff.const _).add ?_
    have hc : Continuous fun A : Matrix m m F => A i j := continuous_id.matrix_elem i j
    have := ContCoeff.C (α := Matrix m m F) (f := fun A => -A i j) hc.neg
    simpa [sub_eq_add_neg] using this
  have : ContCoeff fun A : Matrix m m F => A.charpoly := by
    simp only [Matrix.charpoly, Matrix.det_apply]
    refine ContCoeff.sum _ fun σ _ => ?_
    have hp := ContCoeff.prod Finset.univ fun i _ => hentry (σ i) i
    have := hp.zsmul (Equiv.Perm.sign σ : ℤ)
    simpa only [Units.smul_def] using this
  exact this k

/- English proof (translation)
The claim follows from `continuous_charpoly_coeff_of_fintype k`.
-/
theorem continuous_charpoly_coeff {n : ℕ} (k : ℕ) :
    Continuous fun A : Matrix (Fin n) (Fin n) F => A.charpoly.coeff k :=
  continuous_charpoly_coeff_of_fintype k

end Continuity

section Decomposition

universe u

variable {F : Type u} [Field F] {n : ℕ}

/- English proof (translation)
Establish `h : aeval (Matrix.toLin' A) A.charpoly = 0`. Rewrite using `[← Matrix.charpoly_toLin']`. Conclude with `LinearMap.aeval_self_charpoly _`. Take `⟨v, rfl⟩` from `(Module.AEval'.of (Matrix.toLin' A)).surjective m`. Rewrite using `[← Module.AEval.of_aeval_smul, h, zero_smul, map_zero]`.
-/
theorem charpoly_smul_eq_zero (A : Matrix (Fin n) (Fin n) F)
    (m : Module.AEval' (Matrix.toLin' A)) : A.charpoly • m = 0 := by
  have h : aeval (Matrix.toLin' A) A.charpoly = 0 := by
    rw [← Matrix.charpoly_toLin']
    exact LinearMap.aeval_self_charpoly _
  obtain ⟨v, rfl⟩ := (Module.AEval'.of (Matrix.toLin' A)).surjective m
  rw [← Module.AEval.of_aeval_smul, h, zero_smul, map_zero]

/- English proof (translation)
Establish `htors : Module.IsTorsion F[X] (Module.AEval' (Matrix.toLin' A))` using `Module.AEval.isTorsion_of_finiteDimensional F (Fin n → F) (Matrix.toLin' A)`. Take `⟨ι, hι, p, hp, e, ⟨E⟩⟩` from `Module.equiv_directSum_of_isTorsion htors`. Use `⟨ι, hι, fun i => p i ^ e i, fun i => pow_ne_zero _ (hp i).ne_zero, fun i => ?_, ⟨E⟩⟩` and prove the remaining obligations. Use `set x : DirectSum ι fun i => F[X] ⧸ F[X] ∙ p i ^ e i := DirectSum.of (fun i => F[X] ⧸ F[X] ∙ p i ^ e i) i (Submodule.Quotient.mk 1)`. Establish `h0 : A.charpoly • x = 0`.

Use `charpoly_smul_eq_zero A (E.symm x)` as an intermediate fact. Rewrite `this` using `[← map_smul, LinearEquiv.map_eq_zero_iff]`. Then use the resulting hypothesis. Rewrite `h0` using `[← DirectSum.of_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]`. Establish `h1` using `DirectSum.of_injective (β := fun i => F[X] ⧸ F[X] ∙ p i ^ e i) i (h0.trans (map_zero _).symm)`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)`.

Conclude with `⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩`.
-/
theorem exists_cyclic_decomposition (A : Matrix (Fin n) (Fin n) F) :
    ∃ (ι : Type u) (_ : Fintype ι) (q : ι → F[X]), (∀ i, q i ≠ 0) ∧ (∀ i, q i ∣ A.charpoly) ∧
      Nonempty (Module.AEval' (Matrix.toLin' A) ≃ₗ[F[X]] DirectSum ι fun i => F[X] ⧸ F[X] ∙ q i) := by
  classical
  have htors : Module.IsTorsion F[X] (Module.AEval' (Matrix.toLin' A)) :=
    Module.AEval.isTorsion_of_finiteDimensional F (Fin n → F) (Matrix.toLin' A)
  obtain ⟨ι, hι, p, hp, e, ⟨E⟩⟩ := Module.equiv_directSum_of_isTorsion htors
  refine ⟨ι, hι, fun i => p i ^ e i, fun i => pow_ne_zero _ (hp i).ne_zero, fun i => ?_, ⟨E⟩⟩
  set x : DirectSum ι fun i => F[X] ⧸ F[X] ∙ p i ^ e i :=
    DirectSum.of (fun i => F[X] ⧸ F[X] ∙ p i ^ e i) i (Submodule.Quotient.mk 1)
  have h0 : A.charpoly • x = 0 := by
    have := charpoly_smul_eq_zero A (E.symm x)
    rwa [← map_smul, LinearEquiv.map_eq_zero_iff] at this
  rw [← DirectSum.of_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one] at h0
  have h1 := DirectSum.of_injective (β := fun i => F[X] ⧸ F[X] ∙ p i ^ e i) i
    (h0.trans (map_zero _).symm)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
  exact ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩

end Decomposition

section SumForm

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → F[X])
  (hq : ∀ i, q i ≠ 0)

abbrev CycSum := DirectSum ι fun i => F[X] ⧸ F[X] ∙ q i

def sumForm (x y : CycSum q) : F := ∑ i, ellQ (q i) (hq i) (x i * y i)

omit [DecidableEq ι] in
/- English proof (translation)
Unfold `sumForm`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem sumForm_comm (x y : CycSum q) : sumForm q hq x y = sumForm q hq y x := by
  unfold sumForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

omit [DecidableEq ι] in
/- English proof (translation)
Unfold `sumForm`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[DirectSum.add_apply, add_mul, ellQ_add]`.
-/
theorem sumForm_add_left (x x' y : CycSum q) :
    sumForm q hq (x + x') y = sumForm q hq x y + sumForm q hq x' y := by
  unfold sumForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DirectSum.add_apply, add_mul, ellQ_add]

omit [DecidableEq ι] in
/- English proof (translation)
Unfold `sumForm`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[DirectSum.smul_apply, smul_mul_assoc, ellQ_C_smul]`.
-/
theorem sumForm_C_smul_left (c : F) (x y : CycSum q) :
    sumForm q hq (C c • x) y = c * sumForm q hq x y := by
  unfold sumForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DirectSum.smul_apply, smul_mul_assoc, ellQ_C_smul]

omit [DecidableEq ι] in
/- English proof (translation)
Unfold `sumForm`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[DirectSum.smul_apply, DirectSum.smul_apply, smul_eq_mk_mul, smul_eq_mk_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sumForm_X_smul (x y : CycSum q) :
    sumForm q hq ((X : F[X]) • x) y = sumForm q hq x ((X : F[X]) • y) := by
  unfold sumForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DirectSum.smul_apply, DirectSum.smul_apply, smul_eq_mk_mul, smul_eq_mk_mul]
  congr 1
  ring

/- English proof (translation)
Unfold `sumForm`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[DirectSum.of_eq_same]`. Introduce `j _ hj`. Rewrite using `[DirectSum.of_eq_of_ne _ _ _ hj, zero_mul, ellQ_zero]`.

Simplify using the standard rewrite rules.
-/
theorem sumForm_of_left (i : ι) (b : F[X] ⧸ F[X] ∙ q i) (y : CycSum q) :
    sumForm q hq (DirectSum.of (fun i => F[X] ⧸ F[X] ∙ q i) i b) y = ellQ (q i) (hq i) (b * y i) := by
  unfold sumForm
  rw [Finset.sum_eq_single i]
  · rw [DirectSum.of_eq_same]
  · intro j _ hj
    rw [DirectSum.of_eq_of_ne _ _ _ hj, zero_mul, ellQ_zero]
  · simp

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, y i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hy (DFinsupp.ext h)`. Take `⟨b, hb⟩` from `exists_ellQ_mul_ne_zero (hq i) hi`.

Conclude with `⟨_, by rwa [sumForm_of_left]⟩`.
-/
theorem exists_sumForm_ne_zero {y : CycSum q} (hy : y ≠ 0) : ∃ x, sumForm q hq x y ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (DFinsupp.ext h)
  obtain ⟨b, hb⟩ := exists_ellQ_mul_ne_zero (hq i) hi
  exact ⟨_, by rwa [sumForm_of_left]⟩

end SumForm

section Gram

universe u

open scoped Matrix

variable {F : Type u} [Field F] {n : ℕ}

/- English proof (translation)
Establish `hBaddr : ∀ v w w', B v (w + w') = B v w + B v w'` using `fun v w w' => by`. Rewrite using `[hBsymm, hBaddl, hBsymm w, hBsymm w']`. Establish `hBsmulr : ∀ (c : F) v w, B v (c • w) = c * B v w` using `fun c v w => by`. Rewrite using `[hBsymm, hBsmull, hBsymm]`. Establish `hexp : ∀ v w, B v w = ∑ l, w l * B v (Pi.single l 1)`.

Introduce `v w`. Establish `hsum : ∀ s : Finset (Fin n), B v (∑ l ∈ s, w l • Pi.single l (1 : F)) = ∑ l ∈ s, w l * B v (Pi.single l 1)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Simplify using `only [Finset.sum_empty]`. Use `hBsmulr 0 v 0` as an intermediate fact. Simplify using `using this`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hBaddr, ih, hBsmulr]`.

Establish `hw : ∑ l, w l • Pi.single l (1 : F) = w`. Use `(Pi.basisFun F (Fin n)).sum_repr w` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hsum Finset.univ, hw]`. Establish `hexpl : ∀ v w, B v w = ∑ l, v l * B (Pi.single l 1) w`.

Introduce `v w`. Rewrite using `[hBsymm, hexp]`. Simplify using `only [hBsymm w]`. Establish `hcol : ∀ k, A.mulVec (Pi.single k 1) = fun l => A l k`. Introduce `k`.

Rewrite using `[Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Set `S : Matrix (Fin n) (Fin n) F` to `Matrix.of fun j k => B (Pi.single j 1) (Pi.single k 1)`. Establish `hS : ∀ j k, S j k = B (Pi.single j 1) (Pi.single k 1)` using `fun _ _ => rfl`. Establish `hdet : S.det ≠ 0`.

Introduce `h0`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hw0` to reduce the goal to its premises. Apply `hBnd` to reduce the goal to its premises. Introduce `v`.

Rewrite using `[hexpl]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hj` using `congrFun hw j`. Simplify using `only [Matrix.mulVec, dotProduct, hS, Pi.zero_apply] at hj`. Rewrite using `[hexp, Finset.sum_congr rfl fun l _ => mul_comm _ _, hj, mul_zero]`.

Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero S hdet, ?_, ?_⟩` and prove the remaining obligations. Use `Matrix.IsSymm.ext fun j k => ?_ show S k j = S j k` and prove the remaining obligations. Rewrite using `[hS, hS, hBsymm]`. Use `show S * A = Aᵀ * S`. Use extensionality with `j k`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply]`. Establish `h1 : ∑ l, S j l * A l k = B (Pi.single j 1) (A.mulVec (Pi.single k 1))`. Rewrite using `[hexp, hcol]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [hS, mul_comm]`. Establish `h2 : ∑ l, A l j * S l k = B (A.mulVec (Pi.single j 1)) (Pi.single k 1)`.

Rewrite using `[hexpl, hcol]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [hS]`. Rewrite using `[h1, h2, hBA]`.
-/
theorem exists_isSymm_of_form (A : Matrix (Fin n) (Fin n) F) (B : (Fin n → F) → (Fin n → F) → F)
    (hBsymm : ∀ v w, B v w = B w v) (hBaddl : ∀ v v' w, B (v + v') w = B v w + B v' w)
    (hBsmull : ∀ (c : F) v w, B (c • v) w = c * B v w)
    (hBA : ∀ v w, B (A.mulVec v) w = B v (A.mulVec w))
    (hBnd : ∀ w, (∀ v, B v w = 0) → w = 0) :
    ∃ S : GL (Fin n) F, (S : Matrix (Fin n) (Fin n) F).IsSymm ∧
      (S : Matrix (Fin n) (Fin n) F) * A = Aᵀ * S := by
  classical
  have hBaddr : ∀ v w w', B v (w + w') = B v w + B v w' := fun v w w' => by
    rw [hBsymm, hBaddl, hBsymm w, hBsymm w']
  have hBsmulr : ∀ (c : F) v w, B v (c • w) = c * B v w := fun c v w => by
    rw [hBsymm, hBsmull, hBsymm]
  have hexp : ∀ v w, B v w = ∑ l, w l * B v (Pi.single l 1) := by
    intro v w
    have hsum : ∀ s : Finset (Fin n), B v (∑ l ∈ s, w l • Pi.single l (1 : F)) =
        ∑ l ∈ s, w l * B v (Pi.single l 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have := hBsmulr 0 v 0
        simpa using this
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hBaddr, ih, hBsmulr]
    have hw : ∑ l, w l • Pi.single l (1 : F) = w := by
      have := (Pi.basisFun F (Fin n)).sum_repr w
      simpa using this
    rw [← hsum Finset.univ, hw]
  have hexpl : ∀ v w, B v w = ∑ l, v l * B (Pi.single l 1) w := by
    intro v w
    rw [hBsymm, hexp]
    simp only [hBsymm w]
  have hcol : ∀ k, A.mulVec (Pi.single k 1) = fun l => A l k := by
    intro k
    rw [Matrix.mulVec_single_one]
    rfl
  let S : Matrix (Fin n) (Fin n) F := Matrix.of fun j k => B (Pi.single j 1) (Pi.single k 1)
  have hS : ∀ j k, S j k = B (Pi.single j 1) (Pi.single k 1) := fun _ _ => rfl
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hw0
    apply hBnd
    intro v
    rw [hexpl]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj := congrFun hw j
    simp only [Matrix.mulVec, dotProduct, hS, Pi.zero_apply] at hj
    rw [hexp, Finset.sum_congr rfl fun l _ => mul_comm _ _, hj, mul_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero S hdet, ?_, ?_⟩
  · refine Matrix.IsSymm.ext fun j k => ?_
    show S k j = S j k
    rw [hS, hS, hBsymm]
  · show S * A = Aᵀ * S
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have h1 : ∑ l, S j l * A l k = B (Pi.single j 1) (A.mulVec (Pi.single k 1)) := by
      rw [hexp, hcol]
      exact Finset.sum_congr rfl fun l _ => by rw [hS, mul_comm]
    have h2 : ∑ l, A l j * S l k = B (A.mulVec (Pi.single j 1)) (Pi.single k 1) := by
      rw [hexpl, hcol]
      exact Finset.sum_congr rfl fun l _ => by rw [hS]
    rw [h1, h2, hBA]

/- English proof (translation)
Take `⟨ι, hι, q, hq0, -, ⟨e⟩⟩` from `exists_cyclic_decomposition A`. Use `set φ := Matrix.toLin' A`. Set `E : (Fin n → F) → CycSum q` to `fun v => e (Module.AEval'.of φ v)`. Establish `hEadd : ∀ v w, E (v + w) = E v + E w` using `fun v w => by simp [E]`. Establish `hEsmul : ∀ (c : F) v, E (c • v) = C c • E v` using `fun c v => by`.

Simplify using `only [E, map_smul]`. Rewrite using `[← Module.AEval.C_smul, map_smul]`. Establish `hEA : ∀ v, E (A.mulVec v) = (X : F[X]) • E v` using `fun v => by`. Simplify using `only [E]`. Rewrite using `[← Matrix.toLin'_apply, ← Module.AEval'.X_smul_of, map_smul]`.

Establish `hEinj : ∀ w, E w = 0 → w = 0` using `fun w h => by`. Establish `: Module.AEval'.of φ w = 0`. Rewrite using `[← e.map_eq_zero_iff]`. Conclude with `h`. Simplify using `using this`.

Establish `hEsurj : ∀ x, ∃ v, E v = x` using `fun x => ⟨(Module.AEval'.of φ).symm (e.symm x), by simp [E]⟩`. Use `exists_isSymm_of_form A (fun v w => sumForm q hq0 (E v) (E w)) (fun v w => sumForm_comm q hq0 _ _) (fun v v' w => by simp only [hEadd, sumForm_add_left]) (fun c v w => by simp only [hEsmul, sumForm_C_smul_left]) (fun v w => by simp only [hEA, sumForm_X_smul]) (fun w hw => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hw0`. Take `⟨x, hx⟩` from `exists_sumForm_ne_zero q hq0 (fun h => hw0 (hEinj w h))`. Take `⟨v, rfl⟩` from `hEsurj x`.

Conclude with `hx (hw v)`.
-/
theorem exists_isSymm_mul_eq_transpose_mul (A : Matrix (Fin n) (Fin n) F) :
    ∃ S : GL (Fin n) F, (S : Matrix (Fin n) (Fin n) F).IsSymm ∧
      (S : Matrix (Fin n) (Fin n) F) * A = Aᵀ * S := by
  classical
  obtain ⟨ι, hι, q, hq0, -, ⟨e⟩⟩ := exists_cyclic_decomposition A
  set φ := Matrix.toLin' A
  let E : (Fin n → F) → CycSum q := fun v => e (Module.AEval'.of φ v)
  have hEadd : ∀ v w, E (v + w) = E v + E w := fun v w => by simp [E]
  have hEsmul : ∀ (c : F) v, E (c • v) = C c • E v := fun c v => by
    simp only [E, map_smul]
    rw [← Module.AEval.C_smul, map_smul]
  have hEA : ∀ v, E (A.mulVec v) = (X : F[X]) • E v := fun v => by
    simp only [E]
    rw [← Matrix.toLin'_apply, ← Module.AEval'.X_smul_of, map_smul]
  have hEinj : ∀ w, E w = 0 → w = 0 := fun w h => by
    have : Module.AEval'.of φ w = 0 := by
      rw [← e.map_eq_zero_iff]
      exact h
    simpa using this
  have hEsurj : ∀ x, ∃ v, E v = x := fun x =>
    ⟨(Module.AEval'.of φ).symm (e.symm x), by simp [E]⟩
  refine exists_isSymm_of_form A (fun v w => sumForm q hq0 (E v) (E w))
    (fun v w => sumForm_comm q hq0 _ _)
    (fun v v' w => by simp only [hEadd, sumForm_add_left])
    (fun c v w => by simp only [hEsmul, sumForm_C_smul_left])
    (fun v w => by simp only [hEA, sumForm_X_smul])
    (fun w hw => ?_)
  by_contra hw0
  obtain ⟨x, hx⟩ := exists_sumForm_ne_zero q hq0 (fun h => hw0 (hEinj w h))
  obtain ⟨v, rfl⟩ := hEsurj x
  exact hx (hw v)

end Gram

section Countable

universe u

variable {F : Type u} [Field F] {n : ℕ}

/- English proof (translation)
Use `set φx := Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) with hφx`. Use `set φy := Matrix.toLin' (y : Matrix (Fin n) (Fin n) F) with hφy`. Set `L : (Fin n → F) →ₗ[F] (Fin n → F)` to `(Module.AEval'.of φy).symm.toLinearMap ∘ₗ (E.restrictScalars F).toLinearMap ∘ₗ (Module.AEval'.of φx).toLinearMap`. Set `L' : (Fin n → F) →ₗ[F] (Fin n → F)` to `(Module.AEval'.of φx).symm.toLinearMap ∘ₗ (E.symm.restrictScalars F).toLinearMap ∘ₗ (Module.AEval'.of φy).toLinearMap`. Establish `hLL' : L ∘ₗ L' = LinearMap.id`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[L, L']`. Establish `hL'L : L' ∘ₗ L = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Simplify using `[L, L']`. Establish `hint : L ∘ₗ φx = φy ∘ₗ L`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Simplify using `only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]`. Rewrite using `[← Module.AEval'.X_smul_of, map_smul, Module.AEval'.of_symm_X_smul]`. Use `set P := LinearMap.toMatrix' L`. Use `set Q := LinearMap.toMatrix' L'`. Establish `hPQ : P * Q = 1`.

Rewrite using `[← LinearMap.toMatrix'_comp, hLL', LinearMap.toMatrix'_id]`. Establish `hQP : Q * P = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, hL'L, LinearMap.toMatrix'_id]`. Establish `hPx : P * (x : Matrix (Fin n) (Fin n) F) = y * P`. Establish `h1 : P * (x : Matrix (Fin n) (Fin n) F) = LinearMap.toMatrix' (L ∘ₗ φx)`.

Rewrite using `[LinearMap.toMatrix'_comp, hφx, LinearMap.toMatrix'_toLin']`. Establish `h2 : (y : Matrix (Fin n) (Fin n) F) * P = LinearMap.toMatrix' (φy ∘ₗ L)`. Rewrite using `[LinearMap.toMatrix'_comp, hφy, LinearMap.toMatrix'_toLin']`. Rewrite using `[h1, h2, hint]`. Set `g : GL (Fin n) F` to `⟨Q, P, hQP, hPQ⟩`.

Use `⟨g, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_mul]`. Use `show (x : Matrix (Fin n) (Fin n) F) = Q * y * P`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_conj_of_equiv {x y : GL (Fin n) F}
    (E : Module.AEval' (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]]
      Module.AEval' (Matrix.toLin' (y : Matrix (Fin n) (Fin n) F))) :
    ∃ g : GL (Fin n) F, x = g * y * g⁻¹ := by
  classical
  set φx := Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) with hφx
  set φy := Matrix.toLin' (y : Matrix (Fin n) (Fin n) F) with hφy
  let L : (Fin n → F) →ₗ[F] (Fin n → F) :=
    (Module.AEval'.of φy).symm.toLinearMap ∘ₗ (E.restrictScalars F).toLinearMap ∘ₗ
      (Module.AEval'.of φx).toLinearMap
  let L' : (Fin n → F) →ₗ[F] (Fin n → F) :=
    (Module.AEval'.of φx).symm.toLinearMap ∘ₗ (E.symm.restrictScalars F).toLinearMap ∘ₗ
      (Module.AEval'.of φy).toLinearMap
  have hLL' : L ∘ₗ L' = LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp [L, L']
  have hL'L : L' ∘ₗ L = LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp [L, L']
  have hint : L ∘ₗ φx = φy ∘ₗ L := by
    apply LinearMap.ext
    intro v
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    rw [← Module.AEval'.X_smul_of, map_smul, Module.AEval'.of_symm_X_smul]
  set P := LinearMap.toMatrix' L
  set Q := LinearMap.toMatrix' L'
  have hPQ : P * Q = 1 := by
    rw [← LinearMap.toMatrix'_comp, hLL', LinearMap.toMatrix'_id]
  have hQP : Q * P = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL'L, LinearMap.toMatrix'_id]
  have hPx : P * (x : Matrix (Fin n) (Fin n) F) = y * P := by
    have h1 : P * (x : Matrix (Fin n) (Fin n) F) = LinearMap.toMatrix' (L ∘ₗ φx) := by
      rw [LinearMap.toMatrix'_comp, hφx, LinearMap.toMatrix'_toLin']
    have h2 : (y : Matrix (Fin n) (Fin n) F) * P = LinearMap.toMatrix' (φy ∘ₗ L) := by
      rw [LinearMap.toMatrix'_comp, hφy, LinearMap.toMatrix'_toLin']
    rw [h1, h2, hint]
  let g : GL (Fin n) F := ⟨Q, P, hQP, hPQ⟩
  refine ⟨g, Units.ext ?_⟩
  simp only [Units.val_mul]
  show (x : Matrix (Fin n) (Fin n) F) = Q * y * P
  calc (x : Matrix (Fin n) (Fin n) F) = (Q * P) * x := by rw [hQP, one_mul]
    _ = Q * (P * x) := Matrix.mul_assoc _ _ _
    _ = Q * (y * P) := by rw [hPx]
    _ = Q * y * P := (Matrix.mul_assoc _ _ _).symm

/- English proof (translation)
Use `Set.Finite.of_finite_image (f := UniqueFactorizationMonoid.normalizedFactors) ?_ ?_` and prove the remaining obligations. Use `(UniqueFactorizationMonoid.normalizedFactors f).powerset.toFinset.finite_toSet.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, ⟨hgm, hgf⟩, rfl⟩`. Rewrite using `[Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_powerset]`. Conclude with `(UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hgm.ne_zero hf).1 hgf`.

Introduce and unpack `g₁ ⟨hg₁, -⟩ g₂ ⟨hg₂, -⟩ h`. Use `eq_of_monic_of_associated hg₁ hg₂ ?_` and prove the remaining obligations. Establish `a₁` using `UniqueFactorizationMonoid.prod_normalizedFactors hg₁.ne_zero`. Establish `a₂` using `UniqueFactorizationMonoid.prod_normalizedFactors hg₂.ne_zero`. Rewrite `a₁` using `[h]`.

Conclude with `a₁.symm.trans a₂`.
-/
theorem finite_monic_dvd {f : F[X]} (hf : f ≠ 0) : {g : F[X] | g.Monic ∧ g ∣ f}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := UniqueFactorizationMonoid.normalizedFactors) ?_ ?_
  · refine (UniqueFactorizationMonoid.normalizedFactors f).powerset.toFinset.finite_toSet.subset ?_
    rintro _ ⟨g, ⟨hgm, hgf⟩, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_powerset]
    exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      hgm.ne_zero hf).1 hgf
  · rintro g₁ ⟨hg₁, -⟩ g₂ ⟨hg₂, -⟩ h
    refine eq_of_monic_of_associated hg₁ hg₂ ?_
    have a₁ := UniqueFactorizationMonoid.prod_normalizedFactors hg₁.ne_zero
    have a₂ := UniqueFactorizationMonoid.prod_normalizedFactors hg₂.ne_zero
    rw [h] at a₁
    exact a₁.symm.trans a₂

/- English proof (translation)
Distinguish the cases in `hf : f = 0`. Use `⟨∅, Set.countable_empty, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `absurd (hx.trans hf) (Matrix.charpoly_monic _).ne_zero`. Set `D` to `{g : F[X] // g.Monic ∧ g ∣ f}`. Establish `: Finite D` using `(finite_monic_dvd hf).to_subtype`.

Set `N : (Σ k : ℕ, Fin k → D) → Type u` to `fun t => DirectSum (Fin t.1) fun j => F[X] ⧸ F[X] ∙ (t.2 j).1`. Set `R : (Σ k : ℕ, Fin k → D) → Prop` to `fun t => ∃ y : GL (Fin n) F, Nonempty (Module.AEval' (Matrix.toLin' (y : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]] N t)`. Set `rep : (Σ k : ℕ, Fin k → D) → GL (Fin n) F` to `fun t => if h : R t then h.choose else 1`. Use `⟨Set.range rep, Set.countable_range rep, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨ι, hι, q, hq0, hqd, ⟨e⟩⟩` from `exists_cyclic_decomposition (x : Matrix (Fin n) (Fin n) F)`.

Set `σ` to `Fintype.equivFin ι`. Set `t : Σ k : ℕ, Fin k → D` to `⟨Fintype.card ι, fun j => ⟨monicAssoc (q (σ.symm j)), monicAssoc_monic (hq0 _), (monicAssoc_dvd _).trans (hx ▸ hqd _)⟩⟩`. Establish `hspan : ∀ j : Fin (Fintype.card ι), (F[X] ∙ q (σ.symm j)) = (F[X] ∙ (t.2 j).1)` using `fun j => Ideal.span_singleton_eq_span_singleton.2 (associated_monicAssoc (hq0 _))`. Set `e' : Module.AEval' (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]] N t` to `e.trans ((DirectSum.lequivCongrLeft F[X] σ).trans (DFinsupp.mapRange.linearEquiv fun j => Submodule.quotEquivOfEq _ _ (hspan j)))`. Establish `hR : R t` using `⟨x, ⟨e'⟩⟩`.

Take `⟨e''⟩` from `hR.choose_spec`. Use `⟨rep t, ⟨t, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hrep : rep t = hR.choose` using `dif_pos hR`. Rewrite using `[hrep]`. Conclude with `exists_conj_of_equiv (e'.trans e''.symm)`.
-/
theorem exists_countable_conj_charpoly (f : F[X]) :
    ∃ s : Set (GL (Fin n) F), s.Countable ∧ ∀ x : GL (Fin n) F,
      (x : Matrix (Fin n) (Fin n) F).charpoly = f → ∃ y ∈ s, ∃ g : GL (Fin n) F,
        x = g * y * g⁻¹ := by
  classical
  by_cases hf : f = 0
  · refine ⟨∅, Set.countable_empty, fun x hx => ?_⟩
    exact absurd (hx.trans hf) (Matrix.charpoly_monic _).ne_zero
  let D := {g : F[X] // g.Monic ∧ g ∣ f}
  have : Finite D := (finite_monic_dvd hf).to_subtype
  let N : (Σ k : ℕ, Fin k → D) → Type u := fun t =>
    DirectSum (Fin t.1) fun j => F[X] ⧸ F[X] ∙ (t.2 j).1
  let R : (Σ k : ℕ, Fin k → D) → Prop := fun t => ∃ y : GL (Fin n) F,
    Nonempty (Module.AEval' (Matrix.toLin' (y : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]] N t)
  let rep : (Σ k : ℕ, Fin k → D) → GL (Fin n) F := fun t => if h : R t then h.choose else 1
  refine ⟨Set.range rep, Set.countable_range rep, fun x hx => ?_⟩
  obtain ⟨ι, hι, q, hq0, hqd, ⟨e⟩⟩ := exists_cyclic_decomposition (x : Matrix (Fin n) (Fin n) F)
  let σ := Fintype.equivFin ι
  let t : Σ k : ℕ, Fin k → D := ⟨Fintype.card ι, fun j =>
    ⟨monicAssoc (q (σ.symm j)), monicAssoc_monic (hq0 _), (monicAssoc_dvd _).trans (hx ▸ hqd _)⟩⟩
  have hspan : ∀ j : Fin (Fintype.card ι),
      (F[X] ∙ q (σ.symm j)) = (F[X] ∙ (t.2 j).1) := fun j =>
    Ideal.span_singleton_eq_span_singleton.2 (associated_monicAssoc (hq0 _))
  let e' : Module.AEval' (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]] N t :=
    e.trans ((DirectSum.lequivCongrLeft F[X] σ).trans
      (DFinsupp.mapRange.linearEquiv fun j => Submodule.quotEquivOfEq _ _ (hspan j)))
  have hR : R t := ⟨x, ⟨e'⟩⟩
  obtain ⟨e''⟩ := hR.choose_spec
  refine ⟨rep t, ⟨t, rfl⟩, ?_⟩
  have hrep : rep t = hR.choose := dif_pos hR
  rw [hrep]
  exact exists_conj_of_equiv (e'.trans e''.symm)

end Countable

end GroundTheory.Automorphic.ContragredientTranspose
