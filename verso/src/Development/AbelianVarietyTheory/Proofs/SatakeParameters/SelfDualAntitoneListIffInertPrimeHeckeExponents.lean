import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `nil => rfl`. Consider the case `cons x t ih`. Rewrite `h` using `[List.pairwise_cons]`. Take `⟨hx, ht⟩` from `h`.

Establish `ih` using `ih ht`. Break down `lt_trichotomy 0 x with hpos | hzero | hneg` into its components or cases. Establish `h1 : ¬ x = 0` using `by omega`. Establish `h2 : ¬ x < 0` using `by omega`. Rewrite using `[List.filter_cons_of_pos (by simp [hpos]), List.filter_cons_of_neg (by simp [h1]), List.filter_cons_of_neg (by simp [h2]), List.cons_append, List.cons_append, ← ih]`.

Substitute `hzero` using the available equality. Establish `e1 : t.filter (fun x => decide (0 < x)) = []`. Rewrite using `[List.filter_eq_nil_iff]`. Introduce `y hy`. Simplify using `using hx y hy`.

Rewrite `ih` using `[e1, List.nil_append]`. Rewrite using `[List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp), List.filter_cons_of_neg (by simp), e1, List.nil_append, List.cons_append, ← ih]`. Establish `e1 : t.filter (fun x => decide (0 < x)) = []`. Rewrite using `[List.filter_eq_nil_iff]`. Introduce `y hy`.

Use `hx y hy` as an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `e2 : t.filter (fun x => decide (x = 0)) = []`. Rewrite using `[List.filter_eq_nil_iff]`.

Introduce `y hy`. Use `hx y hy` as an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `h1 : ¬ 0 < x` using `by omega`.

Establish `h2 : ¬ x = 0` using `by omega`. Rewrite `ih` using `[e1, e2, List.nil_append, List.nil_append]`. Rewrite using `[List.filter_cons_of_neg (by simp [h1]), List.filter_cons_of_neg (by simp [h2]), List.filter_cons_of_pos (by simp [hneg]), e1, e2, List.nil_append, List.nil_append, ← ih]`.
-/
private theorem sorted_list_sign_split (d : List ℤ) (h : d.Pairwise (fun a b => b ≤ a)) :
    d = d.filter (fun x => decide (0 < x)) ++ d.filter (fun x => decide (x = 0)) ++ d.filter (fun x => decide (x < 0)) := by
  induction d with
  | nil => rfl
  | cons x t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hx, ht⟩ := h
    have ih := ih ht
    rcases lt_trichotomy 0 x with hpos | hzero | hneg
    · have h1 : ¬ x = 0 := by omega
      have h2 : ¬ x < 0 := by omega
      rw [List.filter_cons_of_pos (by simp [hpos]), List.filter_cons_of_neg (by simp [h1]),
        List.filter_cons_of_neg (by simp [h2]), List.cons_append, List.cons_append, ← ih]
    · subst hzero
      have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; simpa using hx y hy
      rw [e1, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_pos (by simp),
        List.filter_cons_of_neg (by simp), e1, List.nil_append, List.cons_append, ← ih]
    · have e1 : t.filter (fun x => decide (0 < x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have e2 : t.filter (fun x => decide (x = 0)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy; have := hx y hy; simp; omega
      have h1 : ¬ 0 < x := by omega
      have h2 : ¬ x = 0 := by omega
      rw [e1, e2, List.nil_append, List.nil_append] at ih
      rw [List.filter_cons_of_neg (by simp [h1]), List.filter_cons_of_neg (by simp [h2]),
        List.filter_cons_of_pos (by simp [hneg]), e1, e2, List.nil_append, List.nil_append, ← ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => rw [List.flatMap_cons, List.map_cons, ih]`. Both sides reduce to the same expression.
-/
private theorem flatMap_singleton_natCast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = l.map (fun a : ℕ => (a : ℤ)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

/- English proof (translation)
Unfold `labIn`. Use `show List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s) ++ _ ++ List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s.reverse) = _`. Rewrite using `[flatMap_singleton_natCast, flatMap_singleton_natCast]`. Simplify using `[List.map_map, Function.comp_def]`.
-/
private theorem label_list_eq_signed (n : ℕ) (s : List ℕ) : labIn n s =
    s.map (fun a : ℕ => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a : ℕ => -(a : ℤ)) := by
  unfold labIn
  show List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s) ++ _ ++
      List.map _ (List.flatMap (fun a : ℕ => [(a : ℤ)]) s.reverse) = _
  rw [flatMap_singleton_natCast, flatMap_singleton_natCast]
  simp [List.map_map, Function.comp_def]

/- English proof (translation)
Introduce `n d`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hlen, hsort, hdual⟩`. Establish `hsplit` using `sorted_list_sign_split d hsort`. Use `set P := d.filter (fun x => decide (0 < x)) with hPdef`.

Use `set Z := d.filter (fun x => decide (x = 0)) with hZdef`. Use `set N := d.filter (fun x => decide (x < 0)) with hNdef`. Establish `hPN : P = (N.map Neg.neg).reverse`. Establish `e : P = (dualLab d).filter (fun x => decide (0 < x))` using `by rw [hdual]`. Rewrite using `[e, dualLab, List.filter_reverse, List.filter_map, hNdef]`.

Use `congr 2`. Apply `List.filter_congr` to reduce the goal to its premises. Introduce `x _`. Simplify using the standard rewrite rules. Establish `hN : N = P.reverse.map Neg.neg`.

Rewrite using `[hPN, List.reverse_reverse, List.map_map]`. Simplify using the standard rewrite rules. Establish `hZ : Z = List.replicate Z.length 0`. Rewrite using `[List.eq_replicate_iff]`. Use `⟨rfl, ?_⟩` and prove the remaining obligations.

Introduce `b hb`. Rewrite `hb` using `[hZdef]`. Simplify using `using (List.mem_filter.mp hb).2`. Establish `hlenPN : N.length = P.length` using `by rw [hN, List.length_map, List.length_reverse]`. Establish `hdlen : d.length = P.length + Z.length + N.length`.

Use `congrArg List.length hsplit` as an intermediate fact. Simplify `this` using `only [List.length_append]`. Establish `hposP : ∀ x ∈ P, 0 < x`. Introduce `x hx`. Rewrite `hx` using `[hPdef]`.

Simplify using `using (List.mem_filter.mp hx).2`. Establish `hcast : (P.map Int.toNat).map (fun a : ℕ => (a : ℤ)) = P`. Rewrite using `[List.map_map]`. Use `conv_rhs => rw [← List.map_id P]`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `x hx`. Use `hposP x hx` as an intermediate fact. Simplify using `only [Function.comp_apply, id]`. Use linear arithmetic over natural numbers and integers. Use `⟨P.map Int.toNat, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[List.length_map]`. Use linear arithmetic over natural numbers and integers. Establish `hPs : P.Pairwise (fun a b => b ≤ a)` using `hsort.filter _`. Rewrite using `[List.pairwise_map]`. Conclude with `hPs.imp (fun h => Int.toNat_le_toNat h)`.

Introduce `a ha`. Take `⟨x, hx, rfl⟩` from `List.mem_map.mp ha`. Use `hposP x hx` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hneg : ((P.map Int.toNat).reverse.map fun a : ℕ => -(a : ℤ)) = N`.

Rewrite using `[hN]`. Use `conv_rhs => rw [← hcast]`. Simplify using `[List.map_reverse, List.map_map, Function.comp_def]`. Establish `hZ' : Z = List.replicate (n - 2 * P.length) 0`. Rewrite using `[hZ]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[label_list_eq_signed, hcast, List.length_map, hneg, ← hZ']`. Conclude with `hsplit`. Introduce and unpack `⟨s, hs, hsort, hpos, rfl⟩`.

Rewrite using `[label_list_eq_signed]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [List.length_append, List.length_map, List.length_replicate, List.length_reverse]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[List.pairwise_append, List.pairwise_append]`.

Use `⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[List.pairwise_map]`. Conclude with `hsort.imp (fun h => by exact_mod_cast h)`. Rewrite using `[List.pairwise_replicate] right`. Conclude with `le_refl _`.

Introduce `a ha b hb`. Take `⟨x, hx, rfl⟩` from `List.mem_map.mp ha`. Rewrite using `[List.eq_of_mem_replicate hb]`. Conclude with `Nat.zero_le x` after adjusting the coercions. Rewrite using `[List.pairwise_map, List.pairwise_reverse]`.

Use `hsort.imp (fun h => ?_)` and prove the remaining obligations. Simplify using `only [neg_le_neg_iff]`. Conclude with `h` after adjusting the coercions. Introduce `a ha b hb`. Take `⟨y, _, rfl⟩` from `List.mem_map.mp hb`.

Establish `hb0 : -(y : ℤ) ≤ 0` using `by simp`. Break down `List.mem_append.mp ha with ha | ha` into its components or cases. Take `⟨x, _, rfl⟩` from `List.mem_map.mp ha`. Establish `: (0 : ℤ) ≤ x` using `by exact_mod_cast Nat.zero_le x`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[List.eq_of_mem_replicate ha]`. Conclude with `hb0`. Simplify using `[dualLab, List.map_append, List.reverse_append, List.map_reverse, List.map_map, Function.comp_def, List.map_replicate, List.reverse_replicate]`.
-/
theorem labIn_selfDual_iff : ∀ (n : ℕ) (d : List ℤ), (d.length = n ∧ d.Pairwise (fun a b => b ≤ a) ∧ dualLab d = d) ↔
    ∃ s : List ℕ, 2 * s.length ≤ n ∧ s.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ s, 0 < a) ∧ d = labIn n s := by
  intro n d
  constructor
  · rintro ⟨hlen, hsort, hdual⟩
    have hsplit := sorted_list_sign_split d hsort
    set P := d.filter (fun x => decide (0 < x)) with hPdef
    set Z := d.filter (fun x => decide (x = 0)) with hZdef
    set N := d.filter (fun x => decide (x < 0)) with hNdef
    have hPN : P = (N.map Neg.neg).reverse := by
      have e : P = (dualLab d).filter (fun x => decide (0 < x)) := by rw [hdual]
      rw [e, dualLab, List.filter_reverse, List.filter_map, hNdef]
      congr 2
      apply List.filter_congr
      intro x _
      simp
    have hN : N = P.reverse.map Neg.neg := by
      rw [hPN, List.reverse_reverse, List.map_map]
      simp
    have hZ : Z = List.replicate Z.length 0 := by
      rw [List.eq_replicate_iff]
      refine ⟨rfl, ?_⟩
      intro b hb
      rw [hZdef] at hb
      simpa using (List.mem_filter.mp hb).2
    have hlenPN : N.length = P.length := by rw [hN, List.length_map, List.length_reverse]
    have hdlen : d.length = P.length + Z.length + N.length := by
      have := congrArg List.length hsplit
      simpa only [List.length_append] using this
    have hposP : ∀ x ∈ P, 0 < x := by
      intro x hx
      rw [hPdef] at hx
      simpa using (List.mem_filter.mp hx).2
    have hcast : (P.map Int.toNat).map (fun a : ℕ => (a : ℤ)) = P := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id P]
      apply List.map_congr_left
      intro x hx
      have := hposP x hx
      simp only [Function.comp_apply, id]
      omega
    refine ⟨P.map Int.toNat, ?_, ?_, ?_, ?_⟩
    · rw [List.length_map]; omega
    · have hPs : P.Pairwise (fun a b => b ≤ a) := hsort.filter _
      rw [List.pairwise_map]
      exact hPs.imp (fun h => Int.toNat_le_toNat h)
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have := hposP x hx
      omega
    · have hneg : ((P.map Int.toNat).reverse.map fun a : ℕ => -(a : ℤ)) = N := by
        rw [hN]
        conv_rhs => rw [← hcast]
        simp [List.map_reverse, List.map_map, Function.comp_def]
      have hZ' : Z = List.replicate (n - 2 * P.length) 0 := by
        rw [hZ]
        congr 1
        omega
      rw [label_list_eq_signed, hcast, List.length_map, hneg, ← hZ']
      exact hsplit
  · rintro ⟨s, hs, hsort, hpos, rfl⟩
    rw [label_list_eq_signed]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_replicate, List.length_reverse]
      omega
    · rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hsort.imp (fun h => by exact_mod_cast h)
      · rw [List.pairwise_replicate]
        right; exact le_refl _
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [List.eq_of_mem_replicate hb]
        exact_mod_cast Nat.zero_le x
      · rw [List.pairwise_map, List.pairwise_reverse]
        refine hsort.imp (fun h => ?_)
        simp only [neg_le_neg_iff]
        exact_mod_cast h
      · intro a ha b hb
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
        have hb0 : -(y : ℤ) ≤ 0 := by simp
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
          have : (0 : ℤ) ≤ x := by exact_mod_cast Nat.zero_le x
          omega
        · rw [List.eq_of_mem_replicate ha]
          exact hb0
    · simp [dualLab, List.map_append, List.reverse_append, List.map_reverse, List.map_map,
        Function.comp_def, List.map_replicate, List.reverse_replicate]

end GlobalTheory.Hk3
