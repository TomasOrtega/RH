import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ProdMapPowSingle
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PairSym
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PderivPowMonomial

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.B3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb

variable {m n : ℕ}

def S1 (ε : Fin m → Bool) : Set ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) := {v | inF1 ε (Sum.elim id id v)}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[mem_supported]`. Introduce `v hv`. Rewrite `hv` using `[Finset.mem_coe, mem_vars]`.

Take `⟨t, ht, hvt⟩` from `hv`. Rewrite `hvt` using `[Finsupp.mem_support_iff]`. Consider the cases of `v with`. Consider the case `inl k => exact h t ht k (Or.inl hvt)`. Consider the case `inr k => exact h t ht k (Or.inr hvt)`.

Introduce `h t ht k hk`. Rewrite `h` using `[mem_supported]`. Break down `hk with hk | hk` into its components or cases. Conclude with `h (Finset.mem_coe.2 ((mem_vars _).2 ⟨t, ht, Finsupp.mem_support_iff.2 hk⟩))`. Conclude with `h (Finset.mem_coe.2 ((mem_vars _).2 ⟨t, ht, Finsupp.mem_support_iff.2 hk⟩))`.
-/
theorem symmetric_filtration_iff_supported (ε : Fin m → Bool) (s : Sym m n) : SymbolInFirstFamily ε s ↔ s ∈ supported ℂ (S1 ε) := by
  constructor
  · intro h
    rw [mem_supported]
    intro v hv
    rw [Finset.mem_coe, mem_vars] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Finsupp.mem_support_iff] at hvt
    cases v with
    | inl k => exact h t ht k (Or.inl hvt)
    | inr k => exact h t ht k (Or.inr hvt)
  · intro h t ht k hk
    rw [mem_supported] at h
    rcases hk with hk | hk
    · exact h (Finset.mem_coe.2 ((mem_vars _).2 ⟨t, ht, Finsupp.mem_support_iff.2 hk⟩))
    · exact h (Finset.mem_coe.2 ((mem_vars _).2 ⟨t, ht, Finsupp.mem_support_iff.2 hk⟩))

/- English proof (translation)
Rewrite `*` using `[symmetric_filtration_iff_supported]`. Conclude with `Subalgebra.mul_mem _ hu hv`.
-/
theorem symmetric_filtration_mul {ε : Fin m → Bool} {u v : Sym m n} (hu : SymbolInFirstFamily ε u) (hv : SymbolInFirstFamily ε v) : SymbolInFirstFamily ε (u * v) := by
  rw [symmetric_filtration_iff_supported] at *; exact Subalgebra.mul_mem _ hu hv

/- English proof (translation)
Rewrite `*` using `[symmetric_filtration_iff_supported]`. Conclude with `Subalgebra.add_mem _ hu hv`.
-/
theorem symmetric_filtration_add {ε : Fin m → Bool} {u v : Sym m n} (hu : SymbolInFirstFamily ε u) (hv : SymbolInFirstFamily ε v) : SymbolInFirstFamily ε (u + v) := by
  rw [symmetric_filtration_iff_supported] at *; exact Subalgebra.add_mem _ hu hv

/- English proof (translation)
Rewrite `*` using `[symmetric_filtration_iff_supported]`. Conclude with `Subalgebra.smul_mem _ hu c`.
-/
theorem symmetric_filtration_smul {ε : Fin m → Bool} (c : ℂ) {u : Sym m n} (hu : SymbolInFirstFamily ε u) : SymbolInFirstFamily ε (c • u) := by
  rw [symmetric_filtration_iff_supported] at *; exact Subalgebra.smul_mem _ hu c

/- English proof (translation)
Rewrite using `[symmetric_filtration_iff_supported]`. Conclude with `Subalgebra.zero_mem _`.
-/
theorem symmetric_filtration_zero (ε : Fin m → Bool) : SymbolInFirstFamily ε (0 : Sym m n) := by
  rw [symmetric_filtration_iff_supported]; exact Subalgebra.zero_mem _

/- English proof (translation)
Rewrite using `[symmetric_filtration_iff_supported]`. Conclude with `Subalgebra.one_mem _`.
-/
theorem symmetric_filtration_one (ε : Fin m → Bool) : SymbolInFirstFamily ε (1 : Sym m n) := by
  rw [symmetric_filtration_iff_supported]; exact Subalgebra.one_mem _

/- English proof (translation)
Rewrite using `[symmetric_filtration_iff_supported]`. Conclude with `Subalgebra.sum_mem _ fun i hi => (symmetric_filtration_iff_supported ε _).1 (hu i hi)`.
-/
theorem symmetric_filtration_sum {ε : Fin m → Bool} {ι : Type*} (T : Finset ι) (u : ι → Sym m n) (hu : ∀ i ∈ T, SymbolInFirstFamily ε (u i)) :
    SymbolInFirstFamily ε (∑ i ∈ T, u i) := by
  rw [symmetric_filtration_iff_supported]; exact Subalgebra.sum_mem _ fun i hi => (symmetric_filtration_iff_supported ε _).1 (hu i hi)

/- English proof (translation)
Rewrite using `[symmetric_filtration_iff_supported]`. Conclude with `(X_mem_supported).2 hv`.
-/
theorem symmetric_filtration_generator (ε : Fin m → Bool) (v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) (hv : v ∈ S1 ε) :
    SymbolInFirstFamily ε (X v : Sym m n) := by
  rw [symmetric_filtration_iff_supported]; exact (X_mem_supported).2 hv

def ed (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) : ℕ := ∑ k, t (Sum.inr k)

/- English proof (translation)
Simplify using `[ed, Finset.sum_add_distrib]`.
-/
theorem ed_add (t₁ t₂ : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) : ed (t₁ + t₂) = ed t₁ + ed t₂ := by
  simp [ed, Finset.sum_add_distrib]

def EtaEq (r : Sym m n) (d : ℕ) : Prop := ∀ t ∈ r.support, ed t = d

def EtaGt (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, N < ed t

/- English proof (translation)
Introduce `t ht`. Take `⟨t₁, ht₁, t₂, ht₂, rfl⟩` from `Finset.mem_add.1 (MvPolynomial.support_mul u v ht)`. Rewrite using `[ed_add, hu t₁ ht₁, hv t₂ ht₂]`.
-/
theorem etaEq_mul {u v : Sym m n} {d₁ d₂ : ℕ} (hu : EtaEq u d₁) (hv : EtaEq v d₂) : EtaEq (u * v) (d₁ + d₂) := by
  classical
  intro t ht
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul u v ht)
  rw [ed_add, hu t₁ ht₁, hv t₂ ht₂]

/- English proof (translation)
Introduce `t ht`. Break down `Finset.mem_union.1 (support_add ht) with h | h` into its components or cases. Use `exacts [hu t h, hv t h]`.
-/
theorem etaEq_add {u v : Sym m n} {d : ℕ} (hu : EtaEq u d) (hv : EtaEq v d) : EtaEq (u + v) d := by
  classical
  intro t ht
  rcases Finset.mem_union.1 (support_add ht) with h | h
  exacts [hu t h, hv t h]

/- English proof (translation)
Introduce `t ht`. Simplify using `at ht`.
-/
theorem etaEq_zero (d : ℕ) : EtaEq (0 : Sym m n) d := by intro t ht; simp at ht

/- English proof (translation)
The claim follows from `Finset.sum_induction _ (fun r => EtaEq r d) (fun _ _ => etaEq_add) (etaEq_zero d) hu`.
-/
theorem etaEq_sum {ι : Type*} (T : Finset ι) (u : ι → Sym m n) {d : ℕ} (hu : ∀ i ∈ T, EtaEq (u i) d) :
    EtaEq (∑ i ∈ T, u i) d := Finset.sum_induction _ (fun r => EtaEq r d) (fun _ _ => etaEq_add) (etaEq_zero d) hu

/- English proof (translation)
Introduce `t ht`. Rewrite `ht` using `[mem_support_iff, coeff_one]`. Use `split_ifs at ht with h`. Substitute `h` using the available equality. Simplify using `[ed]`.

Conclude with `absurd rfl ht`.
-/
theorem etaEq_one : EtaEq (1 : Sym m n) 0 := by
  intro t ht
  rw [mem_support_iff, coeff_one] at ht
  split_ifs at ht with h
  · subst h
    simp [ed]
  · exact absurd rfl ht

/- English proof (translation)
Introduce `t ht`. Rewrite `ht` using `[support_X, Finset.mem_singleton]`. Substitute `ht` using the available equality. Simplify using `[ed, Finsupp.single_apply]`.
-/
theorem etaEq_X_inl (k : Fin m × Fin n × Bool) : EtaEq (X (Sum.inl k) : Sym m n) 0 := by
  intro t ht
  rw [support_X, Finset.mem_singleton] at ht
  subst ht; simp [ed, Finsupp.single_apply]

/- English proof (translation)
Introduce `t ht`. Rewrite `ht` using `[support_X, Finset.mem_singleton]`. Substitute `ht` using the available equality. Simplify using `[ed, Finsupp.single_apply]`.
-/
theorem etaEq_X_inr (k : Fin m × Fin n × Bool) : EtaEq (X (Sum.inr k) : Sym m n) 1 := by
  intro t ht
  rw [support_X, Finset.mem_singleton] at ht
  subst ht; simp [ed, Finsupp.single_apply]

/- English proof (translation)
Introduce `t ht` and use `le_of_eq (h t ht)`.
-/
theorem etaLe_of_eq {r : Sym m n} {d : ℕ} (h : EtaEq r d) : EtaLe r d := fun t ht => le_of_eq (h t ht)

/- English proof (translation)
Introduce `t ht` and use `lt_of_lt_of_le (h t ht) hd`.
-/
theorem etaLt_mono {r : Sym m n} {d d' : ℕ} (h : EtaLt r d) (hd : d ≤ d') : EtaLt r d' := fun t ht => lt_of_lt_of_le (h t ht) hd

/- English proof (translation)
Introduce `t ht`. Break down `Finset.mem_union.1 (support_add ht) with h | h` into its components or cases. Use `exacts [hu t h, hv t h]`.
-/
theorem etaLt_add {u v : Sym m n} {d : ℕ} (hu : EtaLt u d) (hv : EtaLt v d) : EtaLt (u + v) d := by
  classical
  intro t ht
  rcases Finset.mem_union.1 (support_add ht) with h | h
  exacts [hu t h, hv t h]

/- English proof (translation)
Introduce `t ht`. Simplify using `at ht`.
-/
theorem etaLt_zero (d : ℕ) : EtaLt (0 : Sym m n) d := by intro t ht; simp at ht

/- English proof (translation)
Introduce `t ht` and use `hu t (support_smul ht)`.
-/
theorem etaLt_smul (c : ℂ) {u : Sym m n} {d : ℕ} (hu : EtaLt u d) : EtaLt (c • u) d :=
  fun t ht => hu t (support_smul ht)

/- English proof (translation)
The claim follows from `Finset.sum_induction _ (fun r => EtaLt r d) (fun _ _ => etaLt_add) (etaLt_zero d) hu`.
-/
theorem etaLt_sum {ι : Type*} (T : Finset ι) (u : ι → Sym m n) {d : ℕ} (hu : ∀ i ∈ T, EtaLt (u i) d) :
    EtaLt (∑ i ∈ T, u i) d := Finset.sum_induction _ (fun r => EtaLt r d) (fun _ _ => etaLt_add) (etaLt_zero d) hu

/- English proof (translation)
Introduce `t ht`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.1 (support_mul u v ht)`. Establish `h1` using `hu a ha`. Establish `h2` using `hv b hb`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem etaLt_mul_left {u v : Sym m n} {d₁ d₂ : ℕ} (hu : EtaLe u d₁) (hv : EtaLt v d₂) : EtaLt (u * v) (d₁ + d₂) := by
  classical
  intro t ht
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul u v ht)
  have h1 := hu a ha
  have h2 := hv b hb
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega

/- English proof (translation)
Introduce `t ht`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.1 (support_mul u v ht)`. Establish `h1` using `hu a ha`. Establish `h2` using `hv b hb`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem etaLt_mul_right {u v : Sym m n} {d₁ d₂ : ℕ} (hu : EtaLt u d₁) (hv : EtaLe v d₂) : EtaLt (u * v) (d₁ + d₂) := by
  classical
  intro t ht
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul u v ht)
  have h1 := hu a ha
  have h2 := hv b hb
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega

/- English proof (translation)
Introduce `t ht`. Break down `Finset.mem_union.1 (support_add ht) with h | h` into its components or cases. Use `exacts [hu t h, (hv t h).le]`.
-/
theorem etaLe_add_lt {u v : Sym m n} {d : ℕ} (hu : EtaLe u d) (hv : EtaLt v d) : EtaLe (u + v) d := by
  classical
  intro t ht
  rcases Finset.mem_union.1 (support_add ht) with h | h
  exacts [hu t h, (hv t h).le]

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[coeff_zero]`. Assume the negation of the conclusion as `hc`. Conclude with `Nat.not_lt_zero _ (h t (mem_support_iff.2 hc))`.
-/
theorem etaLt_zero_eq {r : Sym m n} (h : EtaLt r 0) : r = 0 := by
  ext t
  rw [coeff_zero]
  by_contra hc
  exact Nat.not_lt_zero _ (h t (mem_support_iff.2 hc))

/- English proof (translation)
Introduce `t ht` and use `by have := h t ht; omega`.
-/
theorem etaLe_pred {r : Sym m n} {N : ℕ} (h : EtaLt r N) : EtaLe r (N - 1) := fun t ht => by
  have := h t ht; omega

/- English proof (translation)
Introduce `t ht`. Break down `Finset.mem_union.1 (support_add ht) with h | h` into its components or cases. Use `exacts [hu t h, hv t h]`.
-/
theorem etaGt_add {u v : Sym m n} {N : ℕ} (hu : EtaGt u N) (hv : EtaGt v N) : EtaGt (u + v) N := by
  classical
  intro t ht
  rcases Finset.mem_union.1 (support_add ht) with h | h
  exacts [hu t h, hv t h]

/- English proof (translation)
The claim follows from `Finset.sum_induction _ (fun r => EtaGt r N) (fun _ _ => etaGt_add) (fun t ht => by simp at ht) hu`.
-/
theorem etaGt_sum {ι : Type*} (T : Finset ι) (u : ι → Sym m n) {N : ℕ} (hu : ∀ i ∈ T, EtaGt (u i) N) :
    EtaGt (∑ i ∈ T, u i) N := Finset.sum_induction _ (fun r => EtaGt r N) (fun _ _ => etaGt_add) (fun t ht => by simp at ht) hu

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[coeff_zero]`. Assume the negation of the conclusion as `hc`. Establish `ht` using `mem_support_iff.2 hc`. Establish `a : ed t ≤ N` using `h₁ t ht`.

Establish `b : N < ed t` using `h₂ t ht`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_zero_of_le_gt {r : Sym m n} {N : ℕ} (h₁ : EtaLe r N) (h₂ : EtaGt r N) : r = 0 := by
  ext t
  rw [coeff_zero]
  by_contra hc
  have ht := mem_support_iff.2 hc
  have a : ed t ≤ N := h₁ t ht
  have b : N < ed t := h₂ t ht
  omega

def pdeg (ε : Fin m → Bool) (a b : Fin m) : ℕ := (if ε a then 0 else 1) + (if ε b then 1 else 0)

/- English proof (translation)
Unfold `pairSym pdeg`. Apply `etaEq_sum` to reduce the goal to its premises. Introduce `i _`. Apply `etaEq_mul` to reduce the goal to its premises. Apply the tactic sequence `unfold vecVar split_ifs <;> simp [etaEq_X_inl, etaEq_X_inr]`.

Apply the tactic sequence `unfold covVar split_ifs <;> simp [etaEq_X_inl, etaEq_X_inr]`.
-/
theorem etaEq_pair (ε : Fin m → Bool) (a b : Fin m) : EtaEq (pairSym (n := n) ε a b) (pdeg ε a b) := by
  unfold pairSym pdeg
  apply etaEq_sum
  intro i _
  apply etaEq_mul
  · unfold vecVar
    split_ifs <;> simp [etaEq_X_inl, etaEq_X_inr]
  · unfold covVar
    split_ifs <;> simp [etaEq_X_inl, etaEq_X_inr]

/- English proof (translation)
Unfold `pairSym`. Use `symmetric_filtration_sum _ _ fun i _ => symmetric_filtration_mul ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `unfold vecVar; split_ifs with h <;> exact symmetric_filtration_generator ε _ (by simp [S1, inF1, h])`. Apply the tactic sequence `unfold covVar; split_ifs with h <;> exact symmetric_filtration_generator ε _ (by simp [S1, inF1, h])`.
-/
theorem symmetric_filtration_pairing (ε : Fin m → Bool) (a b : Fin m) : SymbolInFirstFamily ε (pairSym (n := n) ε a b) := by
  unfold pairSym
  refine symmetric_filtration_sum _ _ fun i _ => symmetric_filtration_mul ?_ ?_
  · unfold vecVar; split_ifs with h <;> exact symmetric_filtration_generator ε _ (by simp [S1, inF1, h])
  · unfold covVar; split_ifs with h <;> exact symmetric_filtration_generator ε _ (by simp [S1, inF1, h])

/- English proof (translation)
Rewrite using `[← C_1, op_C, one_smul]`.
-/
theorem op_one (f : PX m n) : op (1 : Sym m n) f = f := by
  rw [← C_1, op_C, one_smul]

/- English proof (translation)
Establish `h` using `op_mul_X_inl (1 : Sym m n) k f`. Rewrite `h` using `[one_mul, op_one]`. Then use the resulting hypothesis.
-/
theorem op_X_inl (k : Fin m × Fin n × Bool) (f : PX m n) : op (X (Sum.inl k) : Sym m n) f = X k * f := by
  have h := op_mul_X_inl (1 : Sym m n) k f
  rwa [one_mul, op_one] at h

/- English proof (translation)
Establish `h` using `op_mul_X_inr (1 : Sym m n) k f`. Rewrite `h` using `[one_mul, op_one]`. Then use the resulting hypothesis.
-/
theorem op_X_inr (k : Fin m × Fin n × Bool) (f : PX m n) : op (X (Sum.inr k) : Sym m n) f = pderiv k f := by
  have h := op_mul_X_inr (1 : Sym m n) k f
  rwa [one_mul, op_one] at h

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp [op_zero]`. Consider the case `insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add, ih]`.
-/
theorem op_sum' {ι : Type*} (T : Finset ι) (u : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ T, u i) f = ∑ i ∈ T, op (u i) f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [op_zero]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add, ih]

/- English proof (translation)
Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc`. Establish `key : ∀ f, opL (pairSym (n` using `n) ε a b) f = ∑ i : Fin n, op (vecVar ε a i * covVar ε b i) f := by`. Introduce `f`. Rewrite using `[← op_eq_opL]`. Conclude with `op_sum' _ _ f`.

Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b`. Use `⟨1, LinearMap.ext fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Simplify using `[firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]`. Use `⟨1 / (2 * (c : ℂ)), LinearMap.ext fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[key]`. Simplify using `[firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]`. Rewrite using `[smul_smul, show ((c : ℂ)⁻¹ * 2⁻¹) * (2 * c) = 1 by field_simp, one_smul]`. Conclude with `Finset.sum_congr rfl fun i _ => pderiv_comm' _ _ f`. Use `⟨-(2 * (c : ℂ)), LinearMap.ext fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[key]`. Simplify using `[firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]`. Rewrite using `[smul_smul, show (2 * (c : ℂ)) * ((c : ℂ)⁻¹ * 2⁻¹) = 1 by field_simp, one_smul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Use `⟨-1, LinearMap.ext fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[key]`. Simplify using `[firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]`.
-/
theorem opL_pair (ε : Fin m → Bool) (c : ℝ) (hc : c ≠ 0) (a b : Fin m) :
    ∃ κ : ℂ, opL (pairSym (n := n) ε a b) = κ • firstFamilyOperatorEnd ε c a b := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have key : ∀ f, opL (pairSym (n := n) ε a b) f = ∑ i : Fin n, op (vecVar ε a i * covVar ε b i) f := by
    intro f
    rw [← op_eq_opL]
    exact op_sum' _ _ f
  cases ha : ε a <;> cases hb : ε b
  · refine ⟨1, LinearMap.ext fun f => ?_⟩
    rw [key]
    simp [firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]
  · refine ⟨1 / (2 * (c : ℂ)), LinearMap.ext fun f => ?_⟩
    rw [key]
    simp [firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]
    rw [smul_smul, show ((c : ℂ)⁻¹ * 2⁻¹) * (2 * c) = 1 by field_simp, one_smul]
    exact Finset.sum_congr rfl fun i _ => pderiv_comm' _ _ f
  · refine ⟨-(2 * (c : ℂ)), LinearMap.ext fun f => ?_⟩
    rw [key]
    simp [firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]
    rw [smul_smul, show (2 * (c : ℂ)) * ((c : ℂ)⁻¹ * 2⁻¹) = 1 by field_simp, one_smul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine ⟨-1, LinearMap.ext fun f => ?_⟩
    rw [key]
    simp [firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]

/- English proof (translation)
Unfold `pairSym`. Rewrite using `[map_sum]`. Simplify using `only [Derivation.leibniz, smul_eq_mul]`. Unfold `vecVar covVar`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;>`.

Apply the tactic sequence `simp [symK, mkDerivation_X, ha, hb, mul_ite, ite_mul, Finset.sum_add_distrib] <;> ring`.
-/
theorem symK_pair (ε : Fin m → Bool) (i j : Fin n) (a b : Fin m) : symK ε i j (pairSym (n := n) ε a b) = 0 := by
  unfold pairSym
  rw [map_sum]
  simp only [Derivation.leibniz, smul_eq_mul]
  unfold vecVar covVar
  cases ha : ε a <;> cases hb : ε b <;>
    simp [symK, mkDerivation_X, ha, hb, mul_ite, ite_mul, Finset.sum_add_distrib] <;> ring

/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Establish `h` using `symK_op ε i j (pairSym (n := n) ε a b) f`. Rewrite `h` using `[symK_pair, op_zero]`. Simplify using `only [Module.End.mul_apply, ← op_eq_opL]`. Conclude with `(sub_eq_zero.1 h.symm).symm`.
-/
theorem pair_comm_K (ε : Fin m → Bool) (a b : Fin m) (i j : Fin n) :
    opL (pairSym (n := n) ε a b) * KopL ε i j = KopL ε i j * opL (pairSym (n := n) ε a b) := by
  refine LinearMap.ext fun f => ?_
  have h := symK_op ε i j (pairSym (n := n) ε a b) f
  rw [symK_pair, op_zero] at h
  simp only [Module.End.mul_apply, ← op_eq_opL]
  exact (sub_eq_zero.1 h.symm).symm

def PA (ε : Fin m → Bool) : Subalgebra ℂ (Module.End ℂ (PX m n)) :=
  Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => opL (pairSym (n := n) ε ab.1 ab.2))

/- English proof (translation)
Establish `hle : PA (n` using `n) ε ≤ Subalgebra.centralizer ℂ {KopL ε i j} := by`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨ab, rfl⟩`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`. Introduce `g hg`.

Rewrite `hg` using `[Set.mem_singleton_iff]`. Substitute `hg` using the available equality. Conclude with `(pair_comm_K ε ab.1 ab.2 i j).symm`. Conclude with `((Subalgebra.mem_centralizer_iff ℂ).1 (hle hw) _ (Set.mem_singleton _)).symm`.
-/
theorem adj_comm_K (ε : Fin m → Bool) (i j : Fin n) {w : Module.End ℂ (PX m n)} (hw : w ∈ PA ε) :
    w * KopL ε i j = KopL ε i j * w := by
  have hle : PA (n := n) ε ≤ Subalgebra.centralizer ℂ {KopL ε i j} := by
    apply Algebra.adjoin_le
    rintro _ ⟨ab, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (pair_comm_K ε ab.1 ab.2 i j).symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle hw) _ (Set.mem_singleton _)).symm

/- English proof (translation)
Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨ab, rfl⟩`. Take `⟨κ, hκ⟩` from `opL_pair (n := n) ε c hc ab.1 ab.2`. Rewrite using `[SetLike.mem_coe]`. Simplify using `only`.

Rewrite using `[hκ]`. Conclude with `Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self ab)) κ`.
-/
theorem PA_le (ε : Fin m → Bool) (c : ℝ) (hc : c ≠ 0) :
    PA (n := n) ε ≤ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2) := by
  apply Algebra.adjoin_le
  rintro _ ⟨ab, rfl⟩
  obtain ⟨κ, hκ⟩ := opL_pair (n := n) ε c hc ab.1 ab.2
  rw [SetLike.mem_coe]
  simp only
  rw [hκ]
  exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self ab)) κ

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simp`. Consider the case `succ e ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih]`. Use `show pderiv k (monomial _ _) = _`.

Rewrite using `[pderiv_monomial]`. Use `congr 1`. Rewrite using `[tsub_tsub, ← Finsupp.single_add]`. Rewrite using `[Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.descFactorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pderiv_pow_monomial' (k : Fin m × Fin n × Bool) (e : ℕ) (γ : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) :
    (((pderiv k : Derivation ℂ (PX m n) (PX m n)) : PX m n →ₗ[ℂ] PX m n) ^ e) (monomial γ c) =
      monomial (γ - Finsupp.single k e) (c * ((γ k).descFactorial e : ℂ)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    show pderiv k (monomial _ _) = _
    rw [pderiv_monomial]
    congr 1
    · rw [tsub_tsub, ← Finsupp.single_add]
    · rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.descFactorial_succ]
      push_cast
      ring

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_ γ c`. Simplify using the standard rewrite rules.

Consider the case `cons a L ih`. Introduce `hL γ c`. Rewrite `hL` using `[List.nodup_cons]`. Establish `haL : a ∉ L.toFinset` using `by simpa using hL.1`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, ih hL.2, pderiv_pow_monomial', List.toFinset_cons, Finset.sum_insert haL, Finset.prod_insert haL]`.

Establish `h0 : (∑ k ∈ L.toFinset, Finsupp.single k (e k)) a = 0`. Rewrite using `[Finsupp.finset_sum_apply]`. Use `Finset.sum_eq_zero fun k hk => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce and unpack `rfl`.

Conclude with `haL hk`. Use `congr 1`. Rewrite using `[tsub_tsub, add_comm]`. Rewrite using `[Finsupp.tsub_apply, h0, Nat.sub_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem list_prod_pderiv_pow_monomial (e : Fin m × Fin n × Bool → ℕ) :
    ∀ (L : List (Fin m × Fin n × Bool)), L.Nodup → ∀ (γ : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ),
      (L.map fun k => ((pderiv k : Derivation ℂ (PX m n) (PX m n)) : PX m n →ₗ[ℂ] PX m n) ^ e k).prod (monomial γ c) =
        monomial (γ - ∑ k ∈ L.toFinset, Finsupp.single k (e k)) (c * ∏ k ∈ L.toFinset, ((γ k).descFactorial (e k) : ℂ)) := by
  classical
  intro L
  induction L with
  | nil =>
    intro _ γ c
    simp
  | cons a L ih =>
    intro hL γ c
    rw [List.nodup_cons] at hL
    have haL : a ∉ L.toFinset := by simpa using hL.1
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih hL.2, pderiv_pow_monomial', List.toFinset_cons,
      Finset.sum_insert haL, Finset.prod_insert haL]
    have h0 : (∑ k ∈ L.toFinset, Finsupp.single k (e k)) a = 0 := by
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact haL hk
    congr 1
    · rw [tsub_tsub, add_comm]
    · rw [Finsupp.tsub_apply, h0, Nat.sub_zero]
      ring

/- English proof (translation)
Rewrite using `[opMono_eq]`. Establish `hD : (Dfun fun k => t (Sum.inr k)) (monomial γ 1 : PX m n) = monomial (γ - ∑ k, Finsupp.single k (t (Sum.inr k))) (∏ k, ((γ k).descFactorial (t (Sum.inr k)) : ℂ))`. Unfold `Dfun`. Rewrite using `[list_prod_pderiv_pow_monomial _ _ (Finset.nodup_toList _), Finset.toList_toFinset, one_mul]`. Rewrite using `[hD, monomial_mul, one_mul]`.
-/
theorem opMono_monomial (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (γ : Fin m × Fin n × Bool →₀ ℕ) :
    opMono t (monomial γ 1 : PX m n) =
      monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn + (γ - ∑ k, Finsupp.single k (t (Sum.inr k))))
        (∏ k, ((γ k).descFactorial (t (Sum.inr k)) : ℂ)) := by
  classical
  rw [opMono_eq]
  have hD : (Dfun fun k => t (Sum.inr k)) (monomial γ 1 : PX m n) =
      monomial (γ - ∑ k, Finsupp.single k (t (Sum.inr k))) (∏ k, ((γ k).descFactorial (t (Sum.inr k)) : ℂ)) := by
    unfold Dfun
    rw [list_prod_pderiv_pow_monomial _ _ (Finset.nodup_toList _), Finset.toList_toFinset, one_mul]
  rw [hD, monomial_mul, one_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hs`. Establish `hne : s.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]`. Conclude with `hs`. Take `⟨t0, ht0, hmin⟩` from `Finset.exists_min_image s.support ed hne`.

Establish `h1` using `h (monomial (t0.comapDomain Sum.inr Sum.inr_injective.injOn) 1)`. Unfold `op at h1`. Simplify using `only [opMono_monomial] at h1`. Establish `h2` using `congrArg (coeff (t0.comapDomain Sum.inl Sum.inl_injective.injOn)) h1`. Rewrite `h2` using `[coeff_sum, coeff_zero]`.

Simplify using `only [coeff_smul, coeff_monomial, smul_eq_mul] at h2`. Rewrite `h2` using `[Finset.sum_eq_single t0]`. Rewrite `h2` using `[if_pos]`. Use `absurd h2 (mul_ne_zero (mem_support_iff.1 ht0) ?_)` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.comapDomain_apply, Nat.descFactorial_self]`. Conclude with `Nat.factorial_ne_zero _` after adjusting the coercions. Use extensionality with `k`. Simplify using `[Finsupp.tsub_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]`. Introduce `b hb hbt split_ifs with hc`.

Apply `mul_eq_zero_of_right` to reduce the goal to its premises. Rewrite using `[Finset.prod_eq_zero_iff]`. Assume the negation of the conclusion as `hnz`. Use `push_neg at hnz`. Establish `hle : ∀ k, b (Sum.inr k) ≤ t0 (Sum.inr k)`.

Introduce `k`. Establish `hk` using `hnz k (Finset.mem_univ _)`. Rewrite `hk` using `[Finsupp.comapDomain_apply]`. Assume the negation of the conclusion as `hlt`. Conclude with `hk (by exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.2 (by omega))`.

Establish `hsum : ed b = ed t0` using `le_antisymm (Finset.sum_le_sum fun k _ => hle k) (hmin b hb)`. Establish `heq` using `(Finset.sum_eq_sum_iff_of_le fun k _ => hle k).1 hsum`. Apply `hbt` to reduce the goal to its premises. Use extensionality with `v`. Consider the cases of `v with`.

Consider the case `inr k => exact heq k (Finset.mem_univ _)`. Consider the case `inl k`. Establish `hck` using `DFunLike.congr_fun hc k`. Simplify using `[Finsupp.tsub_apply, Finsupp.finset_sum_apply, Finsupp.single_apply, heq k (Finset.mem_univ _)] at hck`. Conclude with `hck`.

Rewrite using `[mul_zero]`. Introduce `hn`. Conclude with `absurd ht0 hn`.
-/
theorem op_inj {s : Sym m n} (h : ∀ f, op s f = 0) : s = 0 := by
  classical
  by_contra hs
  have hne : s.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hs
  obtain ⟨t0, ht0, hmin⟩ := Finset.exists_min_image s.support ed hne
  have h1 := h (monomial (t0.comapDomain Sum.inr Sum.inr_injective.injOn) 1)
  unfold op at h1
  simp only [opMono_monomial] at h1
  have h2 := congrArg (coeff (t0.comapDomain Sum.inl Sum.inl_injective.injOn)) h1
  rw [coeff_sum, coeff_zero] at h2
  simp only [coeff_smul, coeff_monomial, smul_eq_mul] at h2
  rw [Finset.sum_eq_single t0] at h2
  · rw [if_pos] at h2
    · refine absurd h2 (mul_ne_zero (mem_support_iff.1 ht0) ?_)
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      rw [Finsupp.comapDomain_apply, Nat.descFactorial_self]
      exact_mod_cast Nat.factorial_ne_zero _
    · ext k
      simp [Finsupp.tsub_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  · intro b hb hbt
    split_ifs with hc
    · apply mul_eq_zero_of_right
      rw [Finset.prod_eq_zero_iff]
      by_contra hnz
      push_neg at hnz
      have hle : ∀ k, b (Sum.inr k) ≤ t0 (Sum.inr k) := by
        intro k
        have hk := hnz k (Finset.mem_univ _)
        rw [Finsupp.comapDomain_apply] at hk
        by_contra hlt
        exact hk (by exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.2 (by omega))
      have hsum : ed b = ed t0 := le_antisymm (Finset.sum_le_sum fun k _ => hle k) (hmin b hb)
      have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => hle k).1 hsum
      apply hbt
      ext v
      cases v with
      | inr k => exact heq k (Finset.mem_univ _)
      | inl k =>
        have hck := DFunLike.congr_fun hc k
        simp [Finsupp.tsub_apply, Finsupp.finset_sum_apply, Finsupp.single_apply, heq k (Finset.mem_univ _)] at hck
        exact hck
    · rw [mul_zero]
  · intro hn
    exact absurd ht0 hn

/- English proof (translation)
Proceed by induction on `hx using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨ab, rfl⟩` from `hx`. Conclude with `⟨_, etaEq_pair ε ab.1 ab.2, symmetric_filtration_pairing ε ab.1 ab.2, opL (pairSym ε ab.1 ab.2), Algebra.subset_adjoin ⟨ab, rfl⟩, 0, symmetric_filtration_zero ε, etaLt_zero _, fun f => by rw [add_zero, op_eq_opL]⟩`. Consider the case `one => exact ⟨0, etaEq_one, symmetric_filtration_one ε, 1, Subalgebra.one_mem _, 0, symmetric_filtration_zero ε, etaLt_zero _, fun f => by rw [add_zero, op_one]; rfl⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨d₁, he₁, hs₁, w₁, hw₁, r₁, hr₁, hl₁, hf₁⟩` from `hx`. Take `⟨d₂, he₂, hs₂, w₂, hw₂, r₂, hr₂, hl₂, hf₂⟩` from `hy`. Take `⟨r₀, hr₀, hl₀, hf₀⟩` from `hC m n ε (x + r₁) (y + r₂) d₁ d₂ (symmetric_filtration_add hs₁ hr₁) (symmetric_filtration_add hs₂ hr₂) (etaLe_add_lt (etaLe_of_eq he₁) hl₁) (etaLe_add_lt (etaLe_of_eq he₂) hl₂)`. Use `⟨d₁ + d₂, etaEq_mul he₁ he₂, symmetric_filtration_mul hs₁ hs₂, w₁ * w₂, Subalgebra.mul_mem _ hw₁ hw₂, x * r₂ + r₁ * y + r₁ * r₂ + r₀, ?_, ?_, fun f => ?_⟩` and prove the remaining obligations.

Conclude with `symmetric_filtration_add (symmetric_filtration_add (symmetric_filtration_add (symmetric_filtration_mul hs₁ hr₂) (symmetric_filtration_mul hr₁ hs₂)) (symmetric_filtration_mul hr₁ hr₂)) hr₀`. Use `etaLt_add (etaLt_add (etaLt_add (etaLt_mul_left (etaLe_of_eq he₁) hl₂) (etaLt_mul_right hl₁ (etaLe_of_eq he₂))) ?_) hl₀` and prove the remaining obligations. Conclude with `etaLt_mono (etaLt_mul_right hl₁ (fun t ht => (hl₂ t ht).le)) le_rfl`. Rewrite using `[Module.End.mul_apply, hf₂, hf₁, hf₀, ← op_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem closure_prop (hC : CompSt) (ε : Fin m → Bool) {x : Sym m n}
    (hx : x ∈ Submonoid.closure (Set.range fun ab : Fin m × Fin m => pairSym (n := n) ε ab.1 ab.2)) :
    ∃ d, EtaEq x d ∧ SymbolInFirstFamily ε x ∧ ∃ w ∈ PA (n := n) ε, ∃ r : Sym m n, SymbolInFirstFamily ε r ∧ EtaLt r d ∧ ∀ f, w f = op (x + r) f := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact ⟨_, etaEq_pair ε ab.1 ab.2, symmetric_filtration_pairing ε ab.1 ab.2, opL (pairSym ε ab.1 ab.2),
      Algebra.subset_adjoin ⟨ab, rfl⟩, 0, symmetric_filtration_zero ε, etaLt_zero _, fun f => by rw [add_zero, op_eq_opL]⟩
  | one => exact ⟨0, etaEq_one, symmetric_filtration_one ε, 1, Subalgebra.one_mem _, 0, symmetric_filtration_zero ε, etaLt_zero _,
      fun f => by rw [add_zero, op_one]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d₁, he₁, hs₁, w₁, hw₁, r₁, hr₁, hl₁, hf₁⟩ := hx
    obtain ⟨d₂, he₂, hs₂, w₂, hw₂, r₂, hr₂, hl₂, hf₂⟩ := hy
    obtain ⟨r₀, hr₀, hl₀, hf₀⟩ := hC m n ε (x + r₁) (y + r₂) d₁ d₂ (symmetric_filtration_add hs₁ hr₁) (symmetric_filtration_add hs₂ hr₂)
      (etaLe_add_lt (etaLe_of_eq he₁) hl₁) (etaLe_add_lt (etaLe_of_eq he₂) hl₂)
    refine ⟨d₁ + d₂, etaEq_mul he₁ he₂, symmetric_filtration_mul hs₁ hs₂, w₁ * w₂, Subalgebra.mul_mem _ hw₁ hw₂,
      x * r₂ + r₁ * y + r₁ * r₂ + r₀, ?_, ?_, fun f => ?_⟩
    · exact symmetric_filtration_add (symmetric_filtration_add (symmetric_filtration_add (symmetric_filtration_mul hs₁ hr₂) (symmetric_filtration_mul hr₁ hs₂)) (symmetric_filtration_mul hr₁ hr₂)) hr₀
    · refine etaLt_add (etaLt_add (etaLt_add (etaLt_mul_left (etaLe_of_eq he₁) hl₂)
        (etaLt_mul_right hl₁ (etaLe_of_eq he₂))) ?_) hl₀
      exact etaLt_mono (etaLt_mul_right hl₁ (fun t ht => (hl₂ t ht).le)) le_rfl
    · rw [Module.End.mul_apply, hf₂, hf₁, hf₀, ← op_add]
      congr 1; ring

/- English proof (translation)
Establish `hLe_add : ∀ {u v : Sym m n} {d : ℕ}, EtaLe u d → EtaLe v d → EtaLe (u + v) d`. Introduce `u v d hu hv t ht`. Break down `Finset.mem_union.1 (support_add ht) with h | h` into its components or cases. Use `exacts [hu t h, hv t h]`. Establish `hLe_neg : ∀ {u : Sym m n} {d : ℕ}, EtaLe u d → EtaLe (-u) d` using `fun hu t ht => hu t (by rwa [support_neg] at ht)`.

Establish `hLe_sum : ∀ {ι : Type} (T : Finset ι) (u : ι → Sym m n) {d : ℕ}, (∀ i ∈ T, EtaLe (u i) d) → EtaLe (∑ i ∈ T, u i) d` using `fun T u d hu => Finset.sum_induction _ (fun r => EtaLe r d) (fun _ _ => hLe_add) (fun t ht => by simp at ht) hu`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `s hs hK hN`.

Establish `hmem` using `hF hFFT m n ε s hs hK`. Establish `hmem' : s ∈ Submodule.span ℂ (Submonoid.closure (Set.range fun ab : Fin m × Fin m => pairSym (n` using `n) ε ab.1 ab.2) : Set (Sym m n)) := by`. Rewrite using `[← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]`. Conclude with `hmem`. Rewrite `hmem'` using `[Submodule.mem_span_set']`.

Take `⟨k, c, g, hsum⟩` from `hmem'`. Use `choose d hde hdf w hw r hrf hrl hop using fun i => closure_prop hC ε (SetLike.mem_coe.1 (g i).2)`. Establish `hsT : s = ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • (g i : Sym m n)`. Establish `hsplit` using `Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i ≤ N) (fun i => c i • (g i : Sym m n))`. Rewrite `hsplit` using `[hsum]`.

Establish `hz : ∑ i ∈ Finset.univ.filter (fun i => ¬ d i ≤ N), c i • (g i : Sym m n) = 0`. Apply `eq_zero_of_le_gt (N := N)` to reduce the goal to its premises. Establish `he : ∑ i ∈ Finset.univ.filter (fun i => ¬ d i ≤ N), c i • (g i : Sym m n) = s + -(∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • (g i : Sym m n))`. Rewrite using `[← hsplit]`. Normalize the expressions using the abelian group laws.

Rewrite using `[he]`. Use `hLe_add hN (hLe_neg (hLe_sum _ _ fun i hi => fun t ht => ?_))` and prove the remaining obligations. Conclude with `(hde i t (support_smul ht)).trans_le (Finset.mem_filter.1 hi).2`. Use `etaGt_sum _ _ fun i hi => fun t ht => ?_` and prove the remaining obligations. Establish `e1 : ed t = d i` using `hde i t (support_smul ht)`.

Establish `e2` using `(Finset.mem_filter.1 hi).2`. Use `show N < ed t`. Use linear arithmetic over natural numbers and integers. Rewrite `hsplit` using `[hz, add_zero]`. Conclude with `hsplit.symm`.

Establish `hWmem : (∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • w i) ∈ PA (n` using `n) ε := Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hw i) _`. Use `set W := ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • w i with hWdef`. Use `set R := ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • r i with hRdef`. Establish `hopS : ∀ f, op s f = W f - op R f`. Introduce `f`.

Rewrite using `[hsT, op_sum', hRdef, op_sum', hWdef, LinearMap.sum_apply, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[op_smul, op_smul, LinearMap.smul_apply, hop i f, op_add, smul_add, add_sub_cancel_right]`. Establish `hR : ∀ f, op R f = W f - op s f` using `fun f => by`. Rewrite using `[hopS]`.

Normalize the expressions using the abelian group laws. Establish `hRK : ∀ i j, symK ε i j R = 0`. Introduce `i j`. Apply `op_inj` to reduce the goal to its premises. Introduce `f`.

Establish `hc` using `adj_comm_K ε i j hWmem`. Establish `hs0` using `symK_op ε i j s f`. Rewrite `hs0` using `[hK i j, op_zero]`. Rewrite using `[symK_op, hR, hR, map_sub]`. Establish `e1 : KopL ε i j (W f) = W (KopL ε i j f)`.

Use `congrArg (fun F : Module.End ℂ (PX m n) => F f) hc` as an intermediate fact. Simplify `this.symm` using `[Module.End.mul_apply]`. Rewrite using `[e1, sub_eq_zero.1 hs0.symm]`. Normalize the expressions using the abelian group laws. Establish `hRf : SymbolInFirstFamily ε R` using `symmetric_filtration_sum _ _ fun i _ => symmetric_filtration_smul _ (hrf i)`.

Establish `hRlt : EtaLt R N` using `etaLt_sum _ _ fun i hi => etaLt_smul _ (etaLt_mono (hrl i) (Finset.mem_filter.1 hi).2)`. Distinguish the cases in `hN0 : N = 0`. Substitute `hN0` using the available equality. Establish `hR0` using `etaLt_zero_eq hRlt`. Use `⟨W, hWmem, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[hopS, hR0, op_zero, sub_zero]`. Take `⟨wR, hwR, hwRop⟩` from `ih (N - 1) (by omega) R hRf hRK (etaLe_pred hRlt)`. Use `⟨W - wR, Subalgebra.sub_mem _ hWmem hwR, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[hopS, hwRop, LinearMap.sub_apply]`.
-/
theorem main (hC : CompSt) (hF : FFTSym) (hFFT : PositivityTheory.Rg.Sw.FFT) (ε : Fin m → Bool) :
    ∀ N (s : Sym m n), SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) → EtaLe s N →
      ∃ w ∈ PA (n := n) ε, ∀ f, op s f = w f := by
  classical
  have hLe_add : ∀ {u v : Sym m n} {d : ℕ}, EtaLe u d → EtaLe v d → EtaLe (u + v) d := by
    intro u v d hu hv t ht
    rcases Finset.mem_union.1 (support_add ht) with h | h
    exacts [hu t h, hv t h]
  have hLe_neg : ∀ {u : Sym m n} {d : ℕ}, EtaLe u d → EtaLe (-u) d := fun hu t ht => hu t (by rwa [support_neg] at ht)
  have hLe_sum : ∀ {ι : Type} (T : Finset ι) (u : ι → Sym m n) {d : ℕ}, (∀ i ∈ T, EtaLe (u i) d) →
      EtaLe (∑ i ∈ T, u i) d := fun T u d hu =>
    Finset.sum_induction _ (fun r => EtaLe r d) (fun _ _ => hLe_add) (fun t ht => by simp at ht) hu
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro s hs hK hN
  have hmem := hF hFFT m n ε s hs hK
  have hmem' : s ∈ Submodule.span ℂ (Submonoid.closure (Set.range fun ab : Fin m × Fin m => pairSym (n := n) ε ab.1 ab.2) : Set (Sym m n)) := by
    rw [← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]
    exact hmem
  rw [Submodule.mem_span_set'] at hmem'
  obtain ⟨k, c, g, hsum⟩ := hmem'
  choose d hde hdf w hw r hrf hrl hop using fun i => closure_prop hC ε (SetLike.mem_coe.1 (g i).2)
  have hsT : s = ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • (g i : Sym m n) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i ≤ N) (fun i => c i • (g i : Sym m n))
    rw [hsum] at hsplit
    have hz : ∑ i ∈ Finset.univ.filter (fun i => ¬ d i ≤ N), c i • (g i : Sym m n) = 0 := by
      apply eq_zero_of_le_gt (N := N)
      · have he : ∑ i ∈ Finset.univ.filter (fun i => ¬ d i ≤ N), c i • (g i : Sym m n) =
            s + -(∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • (g i : Sym m n)) := by
          rw [← hsplit]
          abel
        rw [he]
        refine hLe_add hN (hLe_neg (hLe_sum _ _ fun i hi => fun t ht => ?_))
        exact (hde i t (support_smul ht)).trans_le (Finset.mem_filter.1 hi).2
      · refine etaGt_sum _ _ fun i hi => fun t ht => ?_
        have e1 : ed t = d i := hde i t (support_smul ht)
        have e2 := (Finset.mem_filter.1 hi).2
        show N < ed t
        omega
    rw [hz, add_zero] at hsplit
    exact hsplit.symm
  have hWmem : (∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • w i) ∈ PA (n := n) ε :=
    Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hw i) _
  set W := ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • w i with hWdef
  set R := ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • r i with hRdef
  have hopS : ∀ f, op s f = W f - op R f := by
    intro f
    rw [hsT, op_sum', hRdef, op_sum', hWdef, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [op_smul, op_smul, LinearMap.smul_apply, hop i f, op_add, smul_add, add_sub_cancel_right]
  have hR : ∀ f, op R f = W f - op s f := fun f => by
    rw [hopS]
    abel
  have hRK : ∀ i j, symK ε i j R = 0 := by
    intro i j
    apply op_inj
    intro f
    have hc := adj_comm_K ε i j hWmem
    have hs0 := symK_op ε i j s f
    rw [hK i j, op_zero] at hs0
    rw [symK_op, hR, hR, map_sub]
    have e1 : KopL ε i j (W f) = W (KopL ε i j f) := by
      have := congrArg (fun F : Module.End ℂ (PX m n) => F f) hc
      simpa [Module.End.mul_apply] using this.symm
    rw [e1, sub_eq_zero.1 hs0.symm]
    abel
  have hRf : SymbolInFirstFamily ε R := symmetric_filtration_sum _ _ fun i _ => symmetric_filtration_smul _ (hrf i)
  have hRlt : EtaLt R N := etaLt_sum _ _ fun i hi => etaLt_smul _ (etaLt_mono (hrl i) (Finset.mem_filter.1 hi).2)
  by_cases hN0 : N = 0
  · subst hN0
    have hR0 := etaLt_zero_eq hRlt
    refine ⟨W, hWmem, fun f => ?_⟩
    rw [hopS, hR0, op_zero, sub_zero]
  · obtain ⟨wR, hwR, hwRop⟩ := ih (N - 1) (by omega) R hRf hRK (etaLe_pred hRlt)
    refine ⟨W - wR, Subalgebra.sub_mem _ hWmem hwR, fun f => ?_⟩
    rw [hopS, hwRop, LinearMap.sub_apply]

/- English proof (translation)
Introduce `hFFT m n ε c hc s hs hinv`. Take `⟨w, hw, hf⟩` from `main hC hF hFFT ε (s.support.sup ed) s hs hinv fun t ht => Finset.le_sup (f := ed) ht`. Conclude with `⟨w, PA_le ε c hc.ne' hw, fun f _ => hf f⟩`.
-/
theorem invOp_of (hC : CompSt) (hF : FFTSym) : InvOp := by
  intro hFFT m n ε c hc s hs hinv
  obtain ⟨w, hw, hf⟩ := main hC hF hFFT ε (s.support.sup ed) s hs hinv fun t ht => Finset.le_sup (f := ed) ht
  exact ⟨w, PA_le ε c hc.ne' hw, fun f _ => hf f⟩

end PositivityTheory.Rg.Sw.LC.B3
