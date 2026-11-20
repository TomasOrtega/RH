import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CycSec

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.CycP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def gen (ε : Fin m → Bool) (k : Bool × Fin n × Fin n) : PX m n := Qb ε k.1 k.2.1 k.2.2

def Mon (ε : Fin m → Bool) (d : ℕ) : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {M | ∃ l : List (Bool × Fin n × Fin n), l.length ≤ d ∧ M = (l.map (gen ε)).prod}

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩`.
-/
theorem mon_mono (ε : Fin m → Bool) {d d' : ℕ} (h : d ≤ d') : Mon (n := n) ε d ≤ Mon ε d' :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, hl.trans h, e⟩

/- English proof (translation)
Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨k :: l, by simp; omega, by simp⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem gen_mul_mon (ε : Fin m → Bool) (d : ℕ) (k : Bool × Fin n × Fin n) {M : PX m n} (hM : M ∈ Mon ε d) :
    gen ε k * M ∈ Mon ε (d + 1) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact Submodule.subset_span ⟨k :: l, by simp; omega, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨l', hl', rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨l ++ l', by simp; omega, by simp⟩`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [mul_add]`. Conclude with `add_mem hu hv`.

Consider the case `smul c u _ hu => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ hu`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [add_mul]`. Conclude with `add_mem hu hv`.

Consider the case `smul c u _ hu => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ _ hu`.
-/
theorem mon_mul (ε : Fin m → Bool) {d d' : ℕ} {a b : PX m n} (ha : a ∈ Mon ε d) (hb : b ∈ Mon ε d') :
    a * b ∈ Mon ε (d + d') := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l', hl', rfl⟩ := hy
      exact Submodule.subset_span ⟨l ++ l', by simp; omega, by simp⟩
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu

/- English proof (translation)
Proceed by induction on `hR using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Conclude with `⟨1, Submodule.subset_span ⟨[k], by simp, by simp [gen]⟩⟩`. Consider the case `algebraMap r`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], by simp, by simp⟩)`. Consider the case `add x y _ _ hx hy`. Take `⟨d, hd⟩` from `hx`.

Take `⟨d', hd'⟩` from `hy`. Conclude with `⟨max d d', add_mem (mon_mono ε (le_max_left _ _) hd) (mon_mono ε (le_max_right _ _) hd')⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨d, hd⟩` from `hx`. Take `⟨d', hd'⟩` from `hy`.

Conclude with `⟨d + d', mon_mul ε hd hd'⟩`.
-/
theorem adjoin_le (ε : Fin m → Bool) {R : PX m n}
    (hR : R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))) :
    ∃ d, R ∈ Mon ε d := by
  induction hR using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨1, Submodule.subset_span ⟨[k], by simp, by simp [gen]⟩⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], by simp, by simp⟩)
  | add x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨max d d', add_mem (mon_mono ε (le_max_left _ _) hd) (mon_mono ε (le_max_right _ _) hd')⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    exact ⟨d + d', mon_mul ε hd hd'⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]`.
-/
theorem dsum_apply {ι : Type*} (s : Finset ι) (D : ι → Derivation ℂ (PX m n) (PX m n)) (x : PX m n) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

def eulD (H : Matrix (Fin n) (Fin n) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  ∑ a : Fin m, ∑ j : Fin n, ((∑ i, X (a, i, false) * C (H i j)) • pderiv (a, j, false) +
    (∑ i, X (a, i, true) * C (star (H i j))) • pderiv (a, j, true))

/- English proof (translation)
Simplify using `[eulH, eulD, dsum_apply, smul_eq_mul]`.
-/
theorem eulH_eq (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : eulH H R = eulD H R := by
  simp [eulH, eulD, dsum_apply, smul_eq_mul]

/- English proof (translation)
Simplify using `[eulD, dsum_apply, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]`.
-/
theorem eulD_X_false (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, false) : PX m n) = ∑ i, X (a, i, false) * C (H i j) := by
  simp [eulD, dsum_apply, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

/- English proof (translation)
Simplify using `[eulD, dsum_apply, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]`.
-/
theorem eulD_X_true (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) (j : Fin n) :
    eulD H (X (a, j, true) : PX m n) = ∑ i, X (a, i, true) * C (star (H i j)) := by
  simp [eulD, dsum_apply, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq]

/- English proof (translation)
Establish `: eulH H (gen ε k) = ∑ l, C (H l k.2.2) * gen ε (k.1, k.2.1, l) + ∑ l, C (star (H l k.2.1)) * gen ε (k.1, l, k.2.2)`. Take `⟨b, i, j⟩` from `k`. Rewrite using `[eulH_eq]`. Simplify using `only [gen, Qb, map_sum, Derivation.leibniz, smul_eq_mul, eulD_X_false, eulD_X_true, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_add_distrib]`.

Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring`.

Rewrite using `[this]`. Use `add_mem (Submodule.sum_mem _ fun l _ => ?_) (Submodule.sum_mem _ fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, k.2.1, l)], by simp, by simp⟩)`. Rewrite using `[← smul_eq_C_mul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, l, k.2.2)], by simp, by simp⟩)`.
-/
theorem eulH_gen (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (k : Bool × Fin n × Fin n) :
    eulH H (gen ε k) ∈ Mon ε 1 := by
  have : eulH H (gen ε k) = ∑ l, C (H l k.2.2) * gen ε (k.1, k.2.1, l) + ∑ l, C (star (H l k.2.1)) * gen ε (k.1, l, k.2.2) := by
    obtain ⟨b, i, j⟩ := k
    rw [eulH_eq]
    simp only [gen, Qb, map_sum, Derivation.leibniz, smul_eq_mul, eulD_X_false, eulD_X_true, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by ring
  rw [this]
  refine add_mem (Submodule.sum_mem _ fun l _ => ?_) (Submodule.sum_mem _ fun l _ => ?_)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, k.2.1, l)], by simp, by simp⟩)
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[(k.1, l, k.2.2)], by simp, by simp⟩)

/- English proof (translation)
Rewrite using `[eulH_eq]`. Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`. Proceed by induction on `l generalizing d with`.

Consider the case `nil => simp`. Consider the case `cons k l ih`. Simplify using `only [List.map_cons, List.prod_cons, Derivation.leibniz, smul_eq_mul]`. Simplify using `only [List.length_cons] at hl`. Establish `hd : l.length + 1 ≤ d` using `hl`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Conclude with `mon_mono ε hd (gen_mul_mon ε l.length k (ih l.length le_rfl))`. Establish `h1` using `eulH_gen ε H k`. Rewrite `h1` using `[eulH_eq]`. Establish `h2 : (l.map (gen ε)).prod ∈ Mon ε l.length` using `Submodule.subset_span ⟨l, le_rfl, rfl⟩`.

Rewrite using `[mul_comm ((l.map (gen ε)).prod)]`. Conclude with `mon_mono ε (by omega) (mon_mul ε h1 h2)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul a x _ hx => rw [(eulD H).map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem eulH_mon (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (d : ℕ) {M : PX m n} (hM : M ∈ Mon ε d) :
    eulH H M ∈ Mon ε d := by
  rw [eulH_eq]
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction l generalizing d with
    | nil => simp
    | cons k l ih =>
      simp only [List.map_cons, List.prod_cons, Derivation.leibniz, smul_eq_mul]
      simp only [List.length_cons] at hl
      have hd : l.length + 1 ≤ d := hl
      refine add_mem ?_ ?_
      · exact mon_mono ε hd (gen_mul_mon ε l.length k (ih l.length le_rfl))
      · have h1 := eulH_gen ε H k
        rw [eulH_eq] at h1
        have h2 : (l.map (gen ε)).prod ∈ Mon ε l.length := Submodule.subset_span ⟨l, le_rfl, rfl⟩
        rw [mul_comm ((l.map (gen ε)).prod)]
        exact mon_mono ε (by omega) (mon_mul ε h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [(eulD H).map_smul]; exact Submodule.smul_mem _ _ hx

end PositivityTheory.Rg.Sw.AbsSt.CycP
