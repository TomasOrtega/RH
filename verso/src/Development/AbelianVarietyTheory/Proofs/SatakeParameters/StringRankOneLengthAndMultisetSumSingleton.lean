import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.SixthNumerics

/- English proof (translation)
Introduce `r t d n a A hr ht had hw hsum hpos hn hle`. Establish `hd : d = t + 2 * a` using `by omega`. Establish `hA : A ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hsum`.

Use linear arithmetic over natural numbers and integers. Establish `hmem : ∀ x ∈ A, x = 1`. Introduce `x hx`. Establish `h1` using `Multiset.count_le_of_le x hle`. Rewrite `h1` using `[Multiset.count_nsmul]`.

Establish `hc : 1 ≤ Multiset.count x A` using `Multiset.one_le_count_iff_mem.mpr hx`. Establish `h2 : d ≤ Multiset.count x (r ::ₘ Multiset.replicate t 1)` using `le_trans (by nlinarith) h1`. Assume the negation of the conclusion as `hx1`. Rewrite `h2` using `[Multiset.count_cons, Multiset.count_replicate]`. Apply the tactic sequence `split_ifs at h2 <;> omega`.

Establish `hrep : A = Multiset.replicate (Multiset.card A) 1` using `Multiset.eq_replicate_card.mpr hmem`. Establish `hcard : 1 ≤ Multiset.card A` using `Multiset.card_pos.mpr hA`. Establish `h1` using `Multiset.count_le_of_le 1 hle`. Rewrite `h1` using `[Multiset.count_nsmul, Multiset.count_cons, Multiset.count_replicate_self]`. Establish `hc1 : Multiset.count 1 A = Multiset.card A` using `by conv_lhs => rw [hrep]`.

Conclude with `Multiset.count_replicate_self _ _`. Rewrite `h1` using `[hc1]`. Establish `hr1 : (1 : ℕ) ≠ r` using `by omega`. Simplify using `[hr1] at h1`. Establish `hsum' : n = Multiset.card A`.

Rewrite using `[← hsum, hrep]`. Simplify using the standard rewrite rules. Establish `: Multiset.card A = 1` using `by nlinarith`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Establish `: a = 0` using `by nlinarith`.

Use linear arithmetic over natural numbers and integers.
-/
theorem numerics : Numerics := by
  intro r t d n a A hr ht had hw hsum hpos hn hle
  have hd : d = t + 2 * a := by omega
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hmem : ∀ x ∈ A, x = 1 := by
    intro x hx
    have h1 := Multiset.count_le_of_le x hle
    rw [Multiset.count_nsmul] at h1
    have hc : 1 ≤ Multiset.count x A := Multiset.one_le_count_iff_mem.mpr hx
    have h2 : d ≤ Multiset.count x (r ::ₘ Multiset.replicate t 1) :=
      le_trans (by nlinarith) h1
    by_contra hx1
    rw [Multiset.count_cons, Multiset.count_replicate] at h2
    split_ifs at h2 <;> omega
  have hrep : A = Multiset.replicate (Multiset.card A) 1 := Multiset.eq_replicate_card.mpr hmem
  have hcard : 1 ≤ Multiset.card A := Multiset.card_pos.mpr hA
  have h1 := Multiset.count_le_of_le 1 hle
  rw [Multiset.count_nsmul, Multiset.count_cons, Multiset.count_replicate_self] at h1
  have hc1 : Multiset.count 1 A = Multiset.card A := by
    conv_lhs => rw [hrep]
    exact Multiset.count_replicate_self _ _
  rw [hc1] at h1
  have hr1 : (1 : ℕ) ≠ r := by omega
  simp [hr1] at h1
  have hsum' : n = Multiset.card A := by
    rw [← hsum, hrep]; simp
  have : Multiset.card A = 1 := by nlinarith
  refine ⟨by omega, ?_⟩
  have : a = 0 := by nlinarith
  omega

/- English proof (translation)
Introduce `ι _ d A r hd hA hs`. Establish `hc` using `congrArg Multiset.card hs`. Establish `hc' : ∑ k, d k * Multiset.card (A k) = 1`. Rewrite `hc` using `[Multiset.card_sum]`. Simplify `hc` using `[Multiset.card_nsmul]`.

Establish `hterm : ∀ k, 1 ≤ d k * Multiset.card (A k)` using `fun k => Nat.mul_le_mul (hd k) (Multiset.card_pos.mpr (hA k))`. Establish `hle : ∀ k, d k * Multiset.card (A k) = 1`. Introduce `k`. Use `Finset.single_le_sum (f := fun k => d k * Multiset.card (A k)) (fun i _ => Nat.zero_le _) (Finset.mem_univ k)` as an intermediate fact. Use `hterm k` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hcardle : Fintype.card ι ≤ 1`. Use `Finset.card_nsmul_le_sum Finset.univ (fun k => d k * Multiset.card (A k)) 1 (fun k _ => hterm k)` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `hne : Nonempty ι`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Simplify using `at hs`. Establish `hcard : Fintype.card ι = 1` using `le_antisymm hcardle Fintype.card_pos`.

Use `⟨hcard, fun k => ?_⟩` and prove the remaining obligations. Establish `hdk : d k = 1` using `Nat.eq_one_of_mul_eq_one_right (hle k)`. Use `⟨hdk, ?_⟩` and prove the remaining obligations. Establish `hsub : Subsingleton ι` using `Fintype.card_le_one_iff_subsingleton.mp hcardle`. Rewrite `hs` using `[Finset.sum_eq_single k (fun b _ hb => absurd (Subsingleton.elim b k) hb) (fun h => absurd (Finset.mem_univ k) h), hdk, one_smul]`.

Conclude with `hs`.
-/
theorem rest : Rest := by
  intro ι _ d A r hd hA hs
  have hc := congrArg Multiset.card hs
  have hc' : ∑ k, d k * Multiset.card (A k) = 1 := by
    rw [Multiset.card_sum] at hc
    simpa [Multiset.card_nsmul] using hc
  have hterm : ∀ k, 1 ≤ d k * Multiset.card (A k) := fun k =>
    Nat.mul_le_mul (hd k) (Multiset.card_pos.mpr (hA k))
  have hle : ∀ k, d k * Multiset.card (A k) = 1 := by
    intro k
    have := Finset.single_le_sum (f := fun k => d k * Multiset.card (A k))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    have := hterm k
    omega
  have hcardle : Fintype.card ι ≤ 1 := by
    have := Finset.card_nsmul_le_sum Finset.univ (fun k => d k * Multiset.card (A k)) 1
      (fun k _ => hterm k)
    simp at this
    omega
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs
  have hcard : Fintype.card ι = 1 := le_antisymm hcardle Fintype.card_pos
  refine ⟨hcard, fun k => ?_⟩
  have hdk : d k = 1 := Nat.eq_one_of_mul_eq_one_right (hle k)
  refine ⟨hdk, ?_⟩
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcardle
  rw [Finset.sum_eq_single k (fun b _ hb => absurd (Subsingleton.elim b k) hb)
    (fun h => absurd (Finset.mem_univ k) h), hdk, one_smul] at hs
  exact hs

/- English proof (translation)
Assemble the required witnesses or components as `⟨numerics, rest⟩`.
-/
theorem numerics_and_rest : Numerics ∧ Rest := ⟨numerics, rest⟩

end GlobalTheory.SixthNumerics
