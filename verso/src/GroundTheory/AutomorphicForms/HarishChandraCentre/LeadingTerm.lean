import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
import GroundTheory.AutomorphicForms.HarishChandraCentre.Capelli

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

noncomputable abbrev polyLE (n d : ℕ) : Submodule ℂ (MvPolynomial (Fin n) ℂ) := restrictTotalDegree (Fin n) ℂ d

/- English proof (translation)
Rewrite using `[polyLE, mem_restrictTotalDegree]`.
-/
theorem mem_polyLE {d : ℕ} {p : MvPolynomial (Fin n) ℂ} : p ∈ polyLE n d ↔ p.totalDegree ≤ d := by
  rw [polyLE, mem_restrictTotalDegree]

/- English proof (translation)
Introduce `_ hp` and use `mem_polyLE.2 ((mem_polyLE.1 hp).trans h)`.
-/
theorem polyLE_mono {d d' : ℕ} (h : d ≤ d') : polyLE n d ≤ polyLE n d' :=
  fun _ hp => mem_polyLE.2 ((mem_polyLE.1 hp).trans h)

/- English proof (translation)
Rewrite using `[Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.degree_eq_sum, Fintype.sum_prod_type]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[diagExp_apply]`. Conclude with `Finset.single_le_sum (f := fun j => m (i, j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`.
-/
theorem sum_diagExp_le (m : Fin n × Fin n →₀ ℕ) :
    ((diagExp m).sum fun _ e => e) ≤ m.degree := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [diagExp_apply]
  exact Finset.single_le_sum (f := fun j => m (i, j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/- English proof (translation)
Distinguish the cases in `h : IsDiagExp m`. Rewrite using `[hcProjLin_canon_of_isDiagExp h, mem_polyLE]`. Conclude with `(totalDegree_monomial_le _ _).trans ((sum_diagExp_le m).trans hm)`. Rewrite using `[hcProjLin_canon_of_not h]`. Conclude with `Submodule.zero_mem _`.
-/
theorem hcProjLin_canon_mem_polyLE {d : ℕ} {m : Fin n × Fin n →₀ ℕ} (hm : m.degree ≤ d) :
    hcProjLin (canon m) ∈ polyLE n d := by
  by_cases h : IsDiagExp m
  · rw [hcProjLin_canon_of_isDiagExp h, mem_polyLE]
    exact (totalDegree_monomial_le _ _).trans ((sum_diagExp_le m).trans hm)
  · rw [hcProjLin_canon_of_not h]
    exact Submodule.zero_mem _

/- English proof (translation)
Establish `hu' : u ∈ Submodule.span ℂ {u | ∃ m : Fin n × Fin n →₀ ℕ, (∀ a ∈ m.support, True) ∧ 0 ≤ m.degree ∧ m.degree ≤ d ∧ canon m = u}` using `filt_le_canonSpan d hu`. Use `clear hu`. Proceed by induction on `hu' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, -, -, hm, rfl⟩` from `hx`.

Conclude with `hcProjLin_canon_mem_polyLE hm`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul r x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem hcProjLin_mem_polyLE {d : ℕ} {u : U n} (hu : u ∈ filt d) : hcProjLin u ∈ polyLE n d := by
  have hu' : u ∈ Submodule.span ℂ {u | ∃ m : Fin n × Fin n →₀ ℕ, (∀ a ∈ m.support, True) ∧
      0 ≤ m.degree ∧ m.degree ≤ d ∧ canon m = u} := filt_le_canonSpan d hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, -, -, hm, rfl⟩ := hx
    exact hcProjLin_canon_mem_polyLE hm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/- English proof (translation)
The claim follows from `mem_polyLE.1 (hcProjLin_mem_polyLE hu)`.
-/
theorem totalDegree_hcProjLin_le {d : ℕ} {u : U n} (hu : u ∈ filt d) :
    (hcProjLin u).totalDegree ≤ d :=
  mem_polyLE.1 (hcProjLin_mem_polyLE hu)

noncomputable def diagMain (w : List (Fin n × Fin n)) : MvPolynomial (Fin n) ℂ := by
  classical
  exact if ∀ a ∈ w, a.1 = a.2 then (w.map fun a => X a.1).prod else 0

/- English proof (translation)
Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem diagExp_add (m m' : Fin n × Fin n →₀ ℕ) : diagExp (m + m') = diagExp m + diagExp m' := by
  ext i; simp

/- English proof (translation)
Use extensionality with `j`. Rewrite using `[diagExp_apply, Finsupp.single_apply, Finsupp.single_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
theorem diagExp_single (i : Fin n) : diagExp (Finsupp.single (i, i) 1) = Finsupp.single i 1 := by
  ext j
  rw [diagExp_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil`. Establish `: diagExp (Multiset.toFinsupp (([] : List (Fin n × Fin n)) : Multiset (Fin n × Fin n))) = 0` using `by ext; simp`. Rewrite using `[this, monomial_zero', C_1]`. Simplify using the standard rewrite rules.

Consider the case `cons a w ih`. Rewrite using `[show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset (Fin n × Fin n)) by simp, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, diagExp_add, show a = (a.1, a.1) from Prod.ext rfl (hw a (List.mem_cons_self ..)).symm, diagExp_single, ← one_mul (1 : ℂ), ← monomial_mul, …`.
-/
theorem monomial_diagExp_toFinsupp (w : List (Fin n × Fin n)) (hw : ∀ a ∈ w, a.1 = a.2) :
    monomial (diagExp (Multiset.toFinsupp (w : Multiset (Fin n × Fin n)))) (1 : ℂ) =
      (w.map fun a => X a.1).prod := by
  induction w with
  | nil =>
    have : diagExp (Multiset.toFinsupp (([] : List (Fin n × Fin n)) : Multiset (Fin n × Fin n))) = 0 := by
      ext; simp
    rw [this, monomial_zero', C_1]
    simp
  | cons a w ih =>
    rw [show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset (Fin n × Fin n)) by simp,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, diagExp_add,
      show a = (a.1, a.1) from Prod.ext rfl (hw a (List.mem_cons_self ..)).symm, diagExp_single,
      ← one_mul (1 : ℂ), ← monomial_mul, ih fun b hb => hw b (List.mem_cons_of_mem _ hb),
      List.map_cons, List.prod_cons, ← pow_one (X a.1), X_pow_eq_monomial]

/- English proof (translation)
Use `set M := Multiset.toFinsupp (w : Multiset (Fin n × Fin n))`. Establish `h1` using `hcProjLin_mem_polyLE (word_sub_canon_mem_filt w)`. Rewrite `h1` using `[map_sub]`. Establish `h2 : hcProjLin (canon M) = diagMain w`. Distinguish the cases in `hw : ∀ a ∈ w, a.1 = a.2`.

Establish `hd : IsDiagExp M`. Introduce `a ha`. Establish `: a ∈ w`. Assume the negation of the conclusion as `h'`. Apply `ha` to reduce the goal to its premises.

Rewrite using `[Multiset.toFinsupp_apply]`. Conclude with `Multiset.count_eq_zero.2 (fun hm => h' (Multiset.mem_coe.1 hm))`. Conclude with `hw a this`. Rewrite using `[hcProjLin_canon_of_isDiagExp hd, monomial_diagExp_toFinsupp w hw, diagMain, if_pos hw]`. Establish `hd : ¬ IsDiagExp M` using `by push Not at hw`.

Take `⟨a, ha, hne⟩` from `hw`. Introduce `hd`. Use `hne (hd a ?_)` and prove the remaining obligations. Rewrite using `[Multiset.toFinsupp_apply]`. Conclude with `(Multiset.count_pos.2 (Multiset.mem_coe.2 ha)).ne'`.

Rewrite using `[hcProjLin_canon_of_not hd, diagMain, if_neg hw]`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.
-/
theorem hcProjLin_word_sub_mem (w : List (Fin n × Fin n)) :
    hcProjLin (word w) - diagMain w ∈ polyLE n (w.length - 1) := by
  classical
  set M := Multiset.toFinsupp (w : Multiset (Fin n × Fin n))
  have h1 := hcProjLin_mem_polyLE (word_sub_canon_mem_filt w)
  rw [map_sub] at h1
  have h2 : hcProjLin (canon M) = diagMain w := by
    by_cases hw : ∀ a ∈ w, a.1 = a.2
    · have hd : IsDiagExp M := by
        intro a ha
        have : a ∈ w := by
          by_contra h'
          apply ha
          rw [Multiset.toFinsupp_apply]
          exact Multiset.count_eq_zero.2 (fun hm => h' (Multiset.mem_coe.1 hm))
        exact hw a this
      rw [hcProjLin_canon_of_isDiagExp hd, monomial_diagExp_toFinsupp w hw, diagMain, if_pos hw]
    · have hd : ¬ IsDiagExp M := by
        push Not at hw
        obtain ⟨a, ha, hne⟩ := hw
        intro hd
        refine hne (hd a ?_)
        rw [Multiset.toFinsupp_apply]
        exact (Multiset.count_pos.2 (Multiset.mem_coe.2 ha)).ne'
      rw [hcProjLin_canon_of_not hd, diagMain, if_neg hw]
  rwa [h2] at h1

/- English proof (translation)
Proceed by induction on `t using Fin.induction with`. Consider the case `zero => rfl`. Consider the case `succ t ih`. Use `h (Fin.castSucc t)` as an intermediate fact. Rewrite `this` using `[finRotate_apply, Fin.coeSucc_eq_succ]`.

Rewrite using `[← this, ih]`.
-/
theorem const_of_forall_rotate {k : ℕ} {i : Fin (k + 1) → Fin n}
    (h : ∀ t, i t = i (finRotate (k + 1) t)) (t : Fin (k + 1)) : i t = i 0 := by
  induction t using Fin.induction with
  | zero => rfl
  | succ t ih =>
    have := h (Fin.castSucc t)
    rw [finRotate_apply, Fin.coeSucc_eq_succ] at this
    rw [← this, ih]

/- English proof (translation)
Distinguish the cases in `h : ∀ t, i t = i (finRotate (k + 1) t)`. Establish `hc` using `const_of_forall_rotate h`. Establish `hall : ∀ a ∈ List.ofFn (fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))), a.1 = a.2`. Introduce `a ha`. Take `⟨t, rfl⟩` from `List.mem_ofFn.1 ha`.

Conclude with `h t`. Rewrite using `[diagMain, if_pos hall, List.map_ofFn, List.prod_ofFn]`. Rewrite using `[Finset.sum_eq_single (i 0)]`. Rewrite using `[if_pos (funext hc)]`. Simplify using `only [Function.comp_apply, hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Introduce `c _ hc'`. Rewrite using `[if_neg]`. Introduce `he`. Conclude with `hc' (by rw [he])`. Simplify using the standard rewrite rules.

Establish `hnot : ¬ ∀ a ∈ List.ofFn (fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))), a.1 = a.2`. Introduce `hall`. Conclude with `h fun t => hall _ (List.mem_ofFn.2 ⟨t, rfl⟩)`. Rewrite using `[diagMain, if_neg hnot]`. Use `(Finset.sum_eq_zero fun c _ => ?_).symm` and prove the remaining obligations.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `h fun t => rfl`.
-/
theorem diagMain_capelliWord {k : ℕ} (i : Fin (k + 1) → Fin n) :
    diagMain (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) =
      ∑ c : Fin n, if i = (fun _ => c) then X c ^ (k + 1) else 0 := by
  classical
  by_cases h : ∀ t, i t = i (finRotate (k + 1) t)
  · have hc := const_of_forall_rotate h
    have hall : ∀ a ∈ List.ofFn (fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))),
        a.1 = a.2 := by
      intro a ha
      obtain ⟨t, rfl⟩ := List.mem_ofFn.1 ha
      exact h t
    rw [diagMain, if_pos hall, List.map_ofFn, List.prod_ofFn]
    rw [Finset.sum_eq_single (i 0)]
    · rw [if_pos (funext hc)]
      simp only [Function.comp_apply, hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · intro c _ hc'
      rw [if_neg]
      intro he
      exact hc' (by rw [he])
    · simp
  · have hnot : ¬ ∀ a ∈ List.ofFn (fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))),
        a.1 = a.2 := by
      intro hall
      exact h fun t => hall _ (List.mem_ofFn.2 ⟨t, rfl⟩)
    rw [diagMain, if_neg hnot]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rw [if_neg]
    rintro rfl
    exact h fun t => rfl

/- English proof (translation)
Repeatedly rewrite using `[diagMain_capelliWord]`. Rewrite using `[Finset.sum_comm, psum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq' Finset.univ (fun _ => c), if_pos (Finset.mem_univ _)]`.
-/
theorem sum_diagMain_capelliWord (k : ℕ) :
    ∑ i : Fin (k + 1) → Fin n,
      diagMain (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) =
        psum (Fin n) ℂ (k + 1) := by
  classical
  simp_rw [diagMain_capelliWord]
  rw [Finset.sum_comm, psum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (fun _ => c), if_pos (Finset.mem_univ _)]

/- English proof (translation)
Rewrite using `[capelli_eq_sum_word, map_sum, ← sum_diagMain_capelliWord, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `hcProjLin_word_sub_mem (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t)))` as an intermediate fact. Rewrite `this` using `[List.length_ofFn, Nat.add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem hcProjLin_capelli_sub_mem (k : ℕ) :
    hcProjLin (capelli (n := n) (k + 1)) - psum (Fin n) ℂ (k + 1) ∈ polyLE n k := by
  rw [capelli_eq_sum_word, map_sum, ← sum_diagMain_capelliWord, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := hcProjLin_word_sub_mem (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t)))
  rwa [List.length_ofFn, Nat.add_sub_cancel] at this

/- English proof (translation)
The claim follows from `Nat.lt_succ_of_le (mem_polyLE.1 (hcProjLin_capelli_sub_mem k))`.
-/
theorem totalDegree_hcProjLin_capelli_sub (k : ℕ) :
    (hcProjLin (capelli (n := n) (k + 1)) - psum (Fin n) ℂ (k + 1)).totalDegree < k + 1 :=
  Nat.lt_succ_of_le (mem_polyLE.1 (hcProjLin_capelli_sub_mem k))

/- English proof (translation)
Simplify using `[translate]`.
-/
theorem translate_X (c : Fin n → ℂ) (i : Fin n) : translate c (X i) = X i + C (c i) := by
  simp [translate]

/- English proof (translation)
Simplify using `[translate]`.
-/
theorem translate_C (c : Fin n → ℂ) (a : ℂ) : translate c (C a) = C a := by
  simp [translate]

/- English proof (translation)
Rewrite `*` using `[mem_polyLE]`. Conclude with `(totalDegree_mul p (X i)).trans (by rw [totalDegree_X]; omega)`.
-/
theorem mul_X_mem_polyLE {d : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ∈ polyLE n d) (i : Fin n) :
    p * X i ∈ polyLE n (d + 1) := by
  rw [mem_polyLE] at *
  exact (totalDegree_mul p (X i)).trans (by rw [totalDegree_X]; omega)

/- English proof (translation)
Rewrite `*` using `[mem_polyLE]`. Conclude with `(totalDegree_mul p (C a)).trans (by rw [totalDegree_C]; omega)`.
-/
theorem mul_C_mem_polyLE {d : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ∈ polyLE n d) (a : ℂ) :
    p * C a ∈ polyLE n d := by
  rw [mem_polyLE] at *
  exact (totalDegree_mul p (C a)).trans (by rw [totalDegree_C]; omega)

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `p hp`. Rewrite `hp` using `[mem_polyLE, Nat.le_zero, totalDegree_eq_zero_iff_eq_C]`.

Rewrite using `[hp, translate_C, sub_self]`. Conclude with `Submodule.zero_mem _`. Consider the case `succ d ih`. Introduce `p hp`. Rewrite using `[p.as_sum, map_sum, ← Finset.sum_sub_distrib]`.

Use `Submodule.sum_mem _ fun s hs => ?_` and prove the remaining obligations. Establish `hsd : (s.sum fun _ e => e) ≤ d + 1`. Use `mem_polyLE.1 hp` as an intermediate fact. Rewrite `this` using `[totalDegree]`. Conclude with `(Finset.le_sup hs).trans this`.

Distinguish the cases in `hs0 : s = 0`. Rewrite using `[hs0, monomial_zero', translate_C, sub_self]`. Conclude with `Submodule.zero_mem _`. Take `⟨i, hi⟩` from `Finsupp.ne_iff.1 hs0`. Use `set s' := s - Finsupp.single i 1`.

Establish `hss : s = s' + Finsupp.single i 1`. Rewrite using `[tsub_add_cancel_of_le]`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[Nat.one_le_iff_ne_zero.2 hi]`. Simplify using `[Ne.symm hj]`. Establish `hs'd : (s'.sum fun _ e => e) ≤ d`. Establish `: (s.sum fun _ e => e) = (s'.sum fun _ e => e) + 1`. Rewrite using `[hss, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]`.

Use linear arithmetic over natural numbers and integers. Establish `hmono : monomial s (coeff s p) = monomial (s' + Finsupp.single i 1) (coeff s p)`. Rewrite using `[← hss]`. Rewrite using `[hmono, monomial_add_single, pow_one, map_mul, translate_X]`. Use `set m' := monomial s' (coeff s p)`.

Establish `hm' : m' ∈ polyLE n d` using `mem_polyLE.2 ((totalDegree_monomial_le _ _).trans hs'd)`. Establish `hT : translate c m' - m' ∈ polyLE n (d - 1)` using `ih m' hm'`. Establish `hT' : translate c m' ∈ polyLE n d`. Use `Submodule.add_mem _ (polyLE_mono (Nat.sub_le d 1) hT) hm'` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Establish `: translate c m' * (X i + C (c i)) - m' * X i = (translate c m' - m') * X i + translate c m' * C (c i)` using `by ring`. Rewrite using `[this, Nat.add_sub_cancel]`. Use `Submodule.add_mem _ ?_ (mul_C_mem_polyLE hT' _)` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos d with hd | hd` into its components or cases. Substitute `hd` using the available equality.

Establish `hs'0 : s' = 0`. Use extensionality with `j`. Establish `: (s'.sum fun _ e => e) = 0` using `Nat.le_zero.1 hs'd`. Rewrite `this` using `[Finsupp.sum, Finset.sum_eq_zero_iff]`. Assume the negation of the conclusion as `hj`.

Conclude with `hj (this j (Finsupp.mem_support_iff.2 hj))`. Simplify using `only [m', hs'0, monomial_zero', translate_C, sub_self, zero_mul]`. Conclude with `Submodule.zero_mem _`. Use `mul_X_mem_polyLE hT i` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel hd]`. Then use the resulting hypothesis.
-/
theorem translate_sub_mem_polyLE (c : Fin n → ℂ) :
    ∀ (d : ℕ) (p : MvPolynomial (Fin n) ℂ), p ∈ polyLE n d → translate c p - p ∈ polyLE n (d - 1) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    rw [mem_polyLE, Nat.le_zero, totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, translate_C, sub_self]
    exact Submodule.zero_mem _
  | succ d ih =>
    intro p hp
    rw [p.as_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsd : (s.sum fun _ e => e) ≤ d + 1 := by
      have := mem_polyLE.1 hp
      rw [totalDegree] at this
      exact (Finset.le_sup hs).trans this
    by_cases hs0 : s = 0
    · rw [hs0, monomial_zero', translate_C, sub_self]
      exact Submodule.zero_mem _
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hs0
    set s' := s - Finsupp.single i 1
    have hss : s = s' + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      intro j
      by_cases hj : j = i
      · subst hj; simp [Nat.one_le_iff_ne_zero.2 hi]
      · simp [Ne.symm hj]
    have hs'd : (s'.sum fun _ e => e) ≤ d := by
      have : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + 1 := by
        rw [hss, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl]
      omega
    have hmono : monomial s (coeff s p) = monomial (s' + Finsupp.single i 1) (coeff s p) := by
      rw [← hss]
    rw [hmono, monomial_add_single, pow_one, map_mul, translate_X]
    set m' := monomial s' (coeff s p)
    have hm' : m' ∈ polyLE n d := mem_polyLE.2 ((totalDegree_monomial_le _ _).trans hs'd)
    have hT : translate c m' - m' ∈ polyLE n (d - 1) := ih m' hm'
    have hT' : translate c m' ∈ polyLE n d := by
      have := Submodule.add_mem _ (polyLE_mono (Nat.sub_le d 1) hT) hm'
      rwa [sub_add_cancel] at this
    have : translate c m' * (X i + C (c i)) - m' * X i =
        (translate c m' - m') * X i + translate c m' * C (c i) := by ring
    rw [this, Nat.add_sub_cancel]
    refine Submodule.add_mem _ ?_ (mul_C_mem_polyLE hT' _)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have hs'0 : s' = 0 := by
        ext j
        have : (s'.sum fun _ e => e) = 0 := Nat.le_zero.1 hs'd
        rw [Finsupp.sum, Finset.sum_eq_zero_iff] at this
        by_contra hj
        exact hj (this j (Finsupp.mem_support_iff.2 hj))
      simp only [m', hs'0, monomial_zero', translate_C, sub_self, zero_mul]
      exact Submodule.zero_mem _
    · have := mul_X_mem_polyLE hT i
      rwa [Nat.sub_add_cancel hd] at this

/- English proof (translation)
Rewrite using `[psum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mem_polyLE]`. Conclude with `(totalDegree_pow _ _).trans (by rw [totalDegree_X, mul_one])`.
-/
theorem psum_mem_polyLE (k : ℕ) : psum (Fin n) ℂ k ∈ polyLE n k := by
  rw [psum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mem_polyLE]
  exact (totalDegree_pow _ _).trans (by rw [totalDegree_X, mul_one])

/- English proof (translation)
Rewrite using `[harishChandraHom_apply]`. Use `set P := hcProjLin (capelli (n := n) (k + 1))`. Establish `h1 : P - psum (Fin n) ℂ (k + 1) ∈ polyLE n k` using `hcProjLin_capelli_sub_mem k`. Establish `hP : P ∈ polyLE n (k + 1)`. Use `Submodule.add_mem _ (polyLE_mono (Nat.le_succ k) h1) (psum_mem_polyLE (k + 1))` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `h2` using `translate_sub_mem_polyLE (-rhoVec n) (k + 1) P hP`. Rewrite `h2` using `[Nat.add_sub_cancel]`. Establish `: translate (-rhoVec n) P - psum (Fin n) ℂ (k + 1) = (translate (-rhoVec n) P - P) + (P - psum (Fin n) ℂ (k + 1))` using `by ring`. Rewrite using `[this]`.

Conclude with `Nat.lt_succ_of_le (mem_polyLE.1 (Submodule.add_mem _ h2 h1))`.
-/
theorem totalDegree_harishChandraHom_capelli_sub (k : ℕ) :
    (harishChandraHom (⟨capelli (k + 1), capelli_mem_center _⟩ : Subalgebra.center ℂ (U n)) -
      psum (Fin n) ℂ (k + 1)).totalDegree < k + 1 := by
  rw [harishChandraHom_apply]
  set P := hcProjLin (capelli (n := n) (k + 1))
  have h1 : P - psum (Fin n) ℂ (k + 1) ∈ polyLE n k := hcProjLin_capelli_sub_mem k
  have hP : P ∈ polyLE n (k + 1) := by
    have := Submodule.add_mem _ (polyLE_mono (Nat.le_succ k) h1) (psum_mem_polyLE (k + 1))
    rwa [sub_add_cancel] at this
  have h2 := translate_sub_mem_polyLE (-rhoVec n) (k + 1) P hP
  rw [Nat.add_sub_cancel] at h2
  have : translate (-rhoVec n) P - psum (Fin n) ℂ (k + 1) =
      (translate (-rhoVec n) P - P) + (P - psum (Fin n) ℂ (k + 1)) := by ring
  rw [this]
  exact Nat.lt_succ_of_le (mem_polyLE.1 (Submodule.add_mem _ h2 h1))

end GroundTheory.Automorphic.HarishChandra
