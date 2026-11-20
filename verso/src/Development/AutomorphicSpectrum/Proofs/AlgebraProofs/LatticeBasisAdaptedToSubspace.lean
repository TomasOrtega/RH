import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted

open GlobalTheory.CompanionTheory.Ar.Crv Module

variable {K : Type} [Field K] (C : ACurve K) (i : C.I)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `V _ _ b W`. Use `⟨b, 0, le_rfl, fun x => Iff.rfl, fun j => j.elim0, ?_⟩` and prove the remaining obligations.

Introduce `x _`. Establish `hx : x = 0`. Rewrite using `[← b.sum_repr x]`. Simplify using the standard rewrite rules. Rewrite using `[hx]`.

Conclude with `zero_mem _`. Consider the case `succ n ih`. Introduce `V _ _ b W`. Distinguish the cases in `hW : W = ⊥`. Use `⟨b, 0, Nat.zero_le _, fun x => Iff.rfl, fun j => j.elim0, ?_⟩` and prove the remaining obligations.

Rewrite using `[hW]`. Conclude with `bot_le`. Take `⟨w, hwW, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`. Take `⟨q, -, hq⟩` from `Finset.exists_max_image Finset.univ (fun j => C.v i (b.repr w j)) Finset.univ_nonempty`. Establish `hcq : b.repr w q ≠ 0`.

Introduce `h0`. Apply `hw0` to reduce the goal to its premises. Establish `hall : ∀ j, b.repr w j = 0`. Introduce `j`. Establish `hj` using `hq j (Finset.mem_univ j)`.

Rewrite `hj` using `[h0, map_zero]`. Conclude with `(Valuation.zero_iff _).1 (le_antisymm hj zero_le)`. Rewrite using `[← b.sum_repr w]`. Simplify using `[hall]`. Use `set u : V := (b.repr w q)⁻¹ • w with hu`.

Establish `huW : u ∈ W` using `W.smul_mem _ hwW`. Establish `hrepr_u : ∀ j, b.repr u j = (b.repr w q)⁻¹ * b.repr w j`. Introduce `j`. Simplify using `[hu]`. Establish `huq : b.repr u q = 1`.

Rewrite using `[hrepr_u, inv_mul_cancel₀ hcq]`. Establish `hpos : C.v i (b.repr w q) ≠ 0` using `(Valuation.ne_zero_iff _).2 hcq`. Establish `hu1 : ∀ j, C.v i (b.repr u j) ≤ 1`. Introduce `j`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hrepr_u, map_mul, map_inv₀]`. Use `_ ≤ (C.v i (b.repr w q))⁻¹ * C.v i (b.repr w q) := by gcongr`. Conclude with `hq j (Finset.mem_univ j)`. Use `_ = 1 := inv_mul_cancel₀ hpos`. Establish `hli : LinearIndependent K (b ∘ q.succAbove)` using `b.linearIndependent.comp _ Fin.succAbove_right_injective`.

Use `set N := Submodule.span K (Set.range (b ∘ q.succAbove)) with hN`. Establish `memN : ∀ x, x ∈ N ↔ b.repr x q = 0`. Introduce `x`. Rewrite using `[hN, Set.range_comp, b.mem_span_image, Fin.range_succAbove]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Assume the negation of the conclusion as `hne`. Conclude with `h (Finsupp.mem_support_iff.2 hne) rfl`. Introduce `h j hj hjq`. Rewrite `hjq` using `[Set.mem_singleton_iff]`.

Substitute `hjq` using the available equality. Conclude with `(Finsupp.mem_support_iff.1 hj) h`. Set `bN : Basis (Fin n) K N` to `Basis.span hli`. Establish `hsumN : ∀ c : Fin n → K, ∑ l, c l • b (q.succAbove l) = ∑ p, (Fin.insertNth (α` using `fun _ => K) q (0 : K) c p) • b p := by`. Introduce `c`.

Rewrite using `[Fin.sum_univ_succAbove _ q]`. Simplify using the standard rewrite rules. Establish `reprN : ∀ (y : N) (j : Fin n), b.repr (y : V) (q.succAbove j) = bN.repr y j`. Introduce `y j`. Establish `hy : (y : V) = ∑ l, bN.repr y l • b (q.succAbove l)` using `by conv_lhs => rw [← bN.sum_repr y]`.

Rewrite using `[Submodule.coe_sum]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, Basis.span_apply]`. Both sides reduce to the same expression. Rewrite using `[hy, hsumN, b.repr_sum_self]`.

Simplify using the standard rewrite rules. Take `⟨bN', k, hk, hlat, hmem, hspan⟩` from `ih bN (W.comap N.subtype)`. Establish `hli' : ∀ (c : K), ∀ x ∈ N, c • u + x = 0 → c = 0`. Introduce `c x hx h`. Establish `h2` using `congrArg (fun z => b.repr z q) h`.

Simplify using `only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, huq, mul_one, (memN x).1 hx, add_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2`. Conclude with `h2`. Establish `hsp' : ∀ z : V, ∃ c : K, z + c • u ∈ N`. Introduce `z`. Use `⟨-(b.repr z q), ?_⟩` and prove the remaining obligations.

Rewrite using `[memN]`. Simplify using `[huq]`. Set `b' : Basis (Fin (n + 1)) K V` to `Basis.mkFinCons u bN' hli' hsp'`. Establish `hcoe : ⇑b' = Fin.cons u (Subtype.val ∘ ⇑bN')` using `Basis.coe_mkFinCons _ _ _ _`. Establish `hb'0 : b' 0 = u` using `by rw [hcoe, Fin.cons_zero]`.

Establish `hb's : ∀ j, b' j.succ = (bN' j : V)`. Introduce `j`. Rewrite using `[hcoe, Fin.cons_succ]`. Both sides reduce to the same expression. Establish `hyN : ∀ x, x - b.repr x q • u ∈ N`.

Introduce `x`. Rewrite using `[memN]`. Simplify using `[huq]`. Establish `hrep : ∀ x, ⇑(b'.repr x) = Fin.cons (b.repr x q) (⇑(bN'.repr ⟨x - b.repr x q • u, hyN x⟩))`. Introduce `x`.

Establish `hy'` using `congrArg Subtype.val (bN'.sum_repr ⟨x - b.repr x q • u, hyN x⟩)`. Rewrite `hy'` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at hy'`. Establish `hx : x = ∑ p, (Fin.cons (b.repr x q) (⇑(bN'.repr ⟨x - b.repr x q • u, hyN x⟩)) : Fin (n + 1) → K) p • b' p`. Rewrite using `[Fin.sum_univ_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ, hb'0, hb's]`. Rewrite using `[hy']`. Use `show x = b.repr x q • u + (x - b.repr x q • u)`. Normalize the expressions using the abelian group laws. Use `conv_lhs => rw [hx]`.

Conclude with `b'.repr_sum_self _`. Establish `latiff : ∀ x, (∀ p, C.v i (b.repr x p) ≤ 1) ↔ (∀ p, C.v i (b'.repr x p) ≤ 1)`. Introduce `x`. Establish `hlatx` using `hlat ⟨x - b.repr x q • u, hyN x⟩`. Establish `h0 : b'.repr x 0 = b.repr x q` using `by rw [hrep]; rfl`.

Establish `hs : ∀ l, b'.repr x l.succ = bN'.repr ⟨x - b.repr x q • u, hyN x⟩ l`. Introduce `l`. Rewrite using `[hrep]`. Both sides reduce to the same expression. Establish `hcomp : ∀ l, bN.repr ⟨x - b.repr x q • u, hyN x⟩ l = b.repr x (q.succAbove l) - b.repr x q * b.repr u (q.succAbove l)`.

Introduce `l`. Rewrite using `[← reprN]`. Use `show b.repr (x - b.repr x q • u) (q.succAbove l) = _`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Introduce `hx p`. Use `Fin.cases ?_ (fun l => ?_) p` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `hx q`. Rewrite using `[hs]`.

Use `hlatx.1 (fun l' => ?_) l` and prove the remaining obligations. Rewrite using `[hcomp]`. Conclude with `Valuation.map_sub_le _ (hx _) (by rw [map_mul]; exact mul_le_one' (hx q) (hu1 _))`. Introduce `hx`. Establish `ha : C.v i (b.repr x q) ≤ 1`.

Rewrite using `[← h0]`. Conclude with `hx 0`. Establish `hl : ∀ l, C.v i (bN.repr ⟨x - b.repr x q • u, hyN x⟩ l) ≤ 1` using `hlatx.2 (fun l => by rw [← hs]; exact hx _)`. Introduce `p`. Break down `eq_or_ne p q with hpq | hpq` into its components or cases.

Rewrite using `[hpq]`. Conclude with `ha`. Take `⟨l, rfl⟩` from `Fin.exists_succAbove_eq hpq`. Establish `hl'` using `hl l`. Rewrite `hl'` using `[hcomp]`.

Establish `e : b.repr x (q.succAbove l) = (b.repr x (q.succAbove l) - b.repr x q * b.repr u (q.succAbove l)) + b.repr x q * b.repr u (q.succAbove l)` using `by ring`. Rewrite using `[e]`. Conclude with `Valuation.map_add_le _ hl' (by rw [map_mul]; exact mul_le_one' ha (hu1 _))`. Establish `hk' : k + 1 ≤ n + 1` using `Nat.succ_le_succ hk`. Establish `hc0 : Fin.castLE hk' 0 = 0` using `Fin.ext (by simp)`.

Establish `hcs : ∀ l : Fin k, Fin.castLE hk' l.succ = (Fin.castLE hk l).succ` using `fun l => Fin.ext (by simp)`. Use `⟨b', k + 1, hk', latiff, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Use `Fin.cases ?_ (fun l => ?_) j` and prove the remaining obligations. Rewrite using `[hc0, hb'0]`.

Conclude with `huW`. Rewrite using `[hcs, hb's]`. Conclude with `hmem l`. Introduce `x hx`. Establish `hy : (⟨x - b.repr x q • u, hyN x⟩ : N) ∈ W.comap N.subtype` using `by show x - b.repr x q • u ∈ W`.

Conclude with `W.sub_mem hx (W.smul_mem _ huW)`. Establish `h1` using `hspan hy`. Establish `h2` using `Submodule.mem_map_of_mem (f := N.subtype) h1`. Rewrite `h2` using `[Submodule.map_span, ← Set.range_comp]`. Establish `hsub : Set.range (N.subtype ∘ fun j : Fin k => bN' (Fin.castLE hk j)) ⊆ Set.range fun j : Fin (k + 1) => b' (Fin.castLE hk' j)`.

Introduce and unpack `_ ⟨l, rfl⟩`. Use `⟨l.succ, ?_⟩` and prove the remaining obligations. Simplify using `only [hcs, hb's, Function.comp_apply, Submodule.coe_subtype]`. Establish `h3 : x - b.repr x q • u ∈ Submodule.span K (Set.range fun j : Fin (k + 1) => b' (Fin.castLE hk' j))` using `Submodule.span_mono hsub h2`. Establish `hu' : u ∈ Submodule.span K (Set.range fun j : Fin (k + 1) => b' (Fin.castLE hk' j))`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [hc0, hb'0]`. Establish `e : x = b.repr x q • u + (x - b.repr x q • u)` using `by abel`. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ hu') h3`.
-/
private theorem H_affine_combination_eq_of_quadratic_relation : ∀ (n : ℕ) {V : Type} [AddCommGroup V] [Module K V]
    (b : Basis (Fin n) K V) (W : Submodule K V), ∃ (b' : Basis (Fin n) K V) (k : ℕ) (hk : k ≤ n),
      (∀ x, (∀ q, C.v i (b.repr x q) ≤ 1) ↔ (∀ q, C.v i (b'.repr x q) ≤ 1)) ∧
      (∀ j : Fin k, b' (Fin.castLE hk j) ∈ W) ∧
      W ≤ Submodule.span K (Set.range fun j : Fin k => b' (Fin.castLE hk j)) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ b W
    refine ⟨b, 0, le_rfl, fun x => Iff.rfl, fun j => j.elim0, ?_⟩
    intro x _
    have hx : x = 0 := by
      rw [← b.sum_repr x]
      simp
    rw [hx]
    exact zero_mem _
  | succ n ih =>
    intro V _ _ b W
    by_cases hW : W = ⊥
    · refine ⟨b, 0, Nat.zero_le _, fun x => Iff.rfl, fun j => j.elim0, ?_⟩
      rw [hW]
      exact bot_le
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨q, -, hq⟩ := Finset.exists_max_image Finset.univ (fun j => C.v i (b.repr w j))
      Finset.univ_nonempty
    have hcq : b.repr w q ≠ 0 := by
      intro h0
      apply hw0
      have hall : ∀ j, b.repr w j = 0 := by
        intro j
        have hj := hq j (Finset.mem_univ j)
        rw [h0, map_zero] at hj
        exact (Valuation.zero_iff _).1 (le_antisymm hj zero_le)
      rw [← b.sum_repr w]
      simp [hall]
    set u : V := (b.repr w q)⁻¹ • w with hu
    have huW : u ∈ W := W.smul_mem _ hwW
    have hrepr_u : ∀ j, b.repr u j = (b.repr w q)⁻¹ * b.repr w j := by
      intro j
      simp [hu]
    have huq : b.repr u q = 1 := by
      rw [hrepr_u, inv_mul_cancel₀ hcq]
    have hpos : C.v i (b.repr w q) ≠ 0 := (Valuation.ne_zero_iff _).2 hcq
    have hu1 : ∀ j, C.v i (b.repr u j) ≤ 1 := by
      intro j
      calc C.v i (b.repr u j) = (C.v i (b.repr w q))⁻¹ * C.v i (b.repr w j) := by
            rw [hrepr_u, map_mul, map_inv₀]
        _ ≤ (C.v i (b.repr w q))⁻¹ * C.v i (b.repr w q) := by
            gcongr
            exact hq j (Finset.mem_univ j)
        _ = 1 := inv_mul_cancel₀ hpos
    have hli : LinearIndependent K (b ∘ q.succAbove) :=
      b.linearIndependent.comp _ Fin.succAbove_right_injective
    set N := Submodule.span K (Set.range (b ∘ q.succAbove)) with hN
    have memN : ∀ x, x ∈ N ↔ b.repr x q = 0 := by
      intro x
      rw [hN, Set.range_comp, b.mem_span_image, Fin.range_succAbove]
      constructor
      · intro h
        by_contra hne
        exact h (Finsupp.mem_support_iff.2 hne) rfl
      · intro h j hj hjq
        rw [Set.mem_singleton_iff] at hjq
        subst hjq
        exact (Finsupp.mem_support_iff.1 hj) h
    let bN : Basis (Fin n) K N := Basis.span hli
    have hsumN : ∀ c : Fin n → K,
        ∑ l, c l • b (q.succAbove l) = ∑ p, (Fin.insertNth (α := fun _ => K) q (0 : K) c p) • b p := by
      intro c
      rw [Fin.sum_univ_succAbove _ q]
      simp
    have reprN : ∀ (y : N) (j : Fin n), b.repr (y : V) (q.succAbove j) = bN.repr y j := by
      intro y j
      have hy : (y : V) = ∑ l, bN.repr y l • b (q.succAbove l) := by
        conv_lhs => rw [← bN.sum_repr y]
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Submodule.coe_smul, Basis.span_apply]
        rfl
      rw [hy, hsumN, b.repr_sum_self]
      simp
    obtain ⟨bN', k, hk, hlat, hmem, hspan⟩ := ih bN (W.comap N.subtype)
    have hli' : ∀ (c : K), ∀ x ∈ N, c • u + x = 0 → c = 0 := by
      intro c x hx h
      have h2 := congrArg (fun z => b.repr z q) h
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, huq,
        mul_one, (memN x).1 hx, add_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
      exact h2
    have hsp' : ∀ z : V, ∃ c : K, z + c • u ∈ N := by
      intro z
      refine ⟨-(b.repr z q), ?_⟩
      rw [memN]
      simp [huq]
    let b' : Basis (Fin (n + 1)) K V := Basis.mkFinCons u bN' hli' hsp'
    have hcoe : ⇑b' = Fin.cons u (Subtype.val ∘ ⇑bN') := Basis.coe_mkFinCons _ _ _ _
    have hb'0 : b' 0 = u := by rw [hcoe, Fin.cons_zero]
    have hb's : ∀ j, b' j.succ = (bN' j : V) := by
      intro j
      rw [hcoe, Fin.cons_succ]
      rfl
    have hyN : ∀ x, x - b.repr x q • u ∈ N := by
      intro x
      rw [memN]
      simp [huq]
    have hrep : ∀ x, ⇑(b'.repr x) =
        Fin.cons (b.repr x q) (⇑(bN'.repr ⟨x - b.repr x q • u, hyN x⟩)) := by
      intro x
      have hy' := congrArg Subtype.val (bN'.sum_repr ⟨x - b.repr x q • u, hyN x⟩)
      rw [Submodule.coe_sum] at hy'
      simp only [Submodule.coe_smul] at hy'
      have hx : x = ∑ p, (Fin.cons (b.repr x q) (⇑(bN'.repr ⟨x - b.repr x q • u, hyN x⟩)) :
          Fin (n + 1) → K) p • b' p := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hb'0, hb's]
        rw [hy']
        show x = b.repr x q • u + (x - b.repr x q • u)
        abel
      conv_lhs => rw [hx]
      exact b'.repr_sum_self _
    have latiff : ∀ x, (∀ p, C.v i (b.repr x p) ≤ 1) ↔ (∀ p, C.v i (b'.repr x p) ≤ 1) := by
      intro x
      have hlatx := hlat ⟨x - b.repr x q • u, hyN x⟩
      have h0 : b'.repr x 0 = b.repr x q := by rw [hrep]; rfl
      have hs : ∀ l, b'.repr x l.succ = bN'.repr ⟨x - b.repr x q • u, hyN x⟩ l := by
        intro l
        rw [hrep]
        rfl
      have hcomp : ∀ l, bN.repr ⟨x - b.repr x q • u, hyN x⟩ l
          = b.repr x (q.succAbove l) - b.repr x q * b.repr u (q.succAbove l) := by
        intro l
        rw [← reprN]
        show b.repr (x - b.repr x q • u) (q.succAbove l) = _
        simp
      constructor
      · intro hx p
        refine Fin.cases ?_ (fun l => ?_) p
        · rw [h0]
          exact hx q
        · rw [hs]
          refine hlatx.1 (fun l' => ?_) l
          rw [hcomp]
          exact Valuation.map_sub_le _ (hx _) (by rw [map_mul]; exact mul_le_one' (hx q) (hu1 _))
      · intro hx
        have ha : C.v i (b.repr x q) ≤ 1 := by
          rw [← h0]
          exact hx 0
        have hl : ∀ l, C.v i (bN.repr ⟨x - b.repr x q • u, hyN x⟩ l) ≤ 1 :=
          hlatx.2 (fun l => by rw [← hs]; exact hx _)
        intro p
        rcases eq_or_ne p q with hpq | hpq
        · rw [hpq]
          exact ha
        · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hpq
          have hl' := hl l
          rw [hcomp] at hl'
          have e : b.repr x (q.succAbove l) = (b.repr x (q.succAbove l) - b.repr x q *
              b.repr u (q.succAbove l)) + b.repr x q * b.repr u (q.succAbove l) := by ring
          rw [e]
          exact Valuation.map_add_le _ hl' (by rw [map_mul]; exact mul_le_one' ha (hu1 _))
    have hk' : k + 1 ≤ n + 1 := Nat.succ_le_succ hk
    have hc0 : Fin.castLE hk' 0 = 0 := Fin.ext (by simp)
    have hcs : ∀ l : Fin k, Fin.castLE hk' l.succ = (Fin.castLE hk l).succ := fun l => Fin.ext (by simp)
    refine ⟨b', k + 1, hk', latiff, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun l => ?_) j
      · rw [hc0, hb'0]
        exact huW
      · rw [hcs, hb's]
        exact hmem l
    · intro x hx
      have hy : (⟨x - b.repr x q • u, hyN x⟩ : N) ∈ W.comap N.subtype := by
        show x - b.repr x q • u ∈ W
        exact W.sub_mem hx (W.smul_mem _ huW)
      have h1 := hspan hy
      have h2 := Submodule.mem_map_of_mem (f := N.subtype) h1
      rw [Submodule.map_span, ← Set.range_comp] at h2
      have hsub : Set.range (N.subtype ∘ fun j : Fin k => bN' (Fin.castLE hk j)) ⊆
          Set.range fun j : Fin (k + 1) => b' (Fin.castLE hk' j) := by
        rintro _ ⟨l, rfl⟩
        refine ⟨l.succ, ?_⟩
        simp only [hcs, hb's, Function.comp_apply, Submodule.coe_subtype]
      have h3 : x - b.repr x q • u ∈
          Submodule.span K (Set.range fun j : Fin (k + 1) => b' (Fin.castLE hk' j)) :=
        Submodule.span_mono hsub h2
      have hu' : u ∈ Submodule.span K (Set.range fun j : Fin (k + 1) => b' (Fin.castLE hk' j)) := by
        apply Submodule.subset_span
        refine ⟨0, ?_⟩
        simp only [hc0, hb'0]
      have e : x = b.repr x q • u + (x - b.repr x q • u) := by abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu') h3

/- English proof (translation)
Use `haveI : FiniteDimensional K V := Module.Finite.of_basis b`. Take `⟨b₀, k, hk, hlat, hmem, hspan⟩` from `H_affine_combination_eq_of_quadratic_relation C i n b W`. Establish `hkerW : LinearMap.ker g = W`. Use extensionality with `x`. Conclude with `(LinearMap.mem_ker).trans (hker x)`.

Establish `hrs : finrank K W + finrank K U = n`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker g`. Rewrite `h1` using `[LinearMap.range_eq_top.mpr hg, finrank_top, hkerW, Module.finrank_eq_card_basis b, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hrk : finrank K W = k`.

Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hli : LinearIndependent K (fun j : Fin k => (⟨b₀ (Fin.castLE hk j), hmem j⟩ : W))`. Apply `LinearIndependent.of_comp W.subtype` to reduce the goal to its premises. Conclude with `b₀.linearIndependent.comp _ (Fin.castLE_injective hk)`.

Simplify using `using hli.fintype_card_le_finrank`. Set `b' : Basis (Fin (finrank K W + finrank K U)) K V` to `b₀.reindex (finCongr hrs.symm)`. Establish `hlt : ∀ j : Fin (finrank K W), j.val < k` using `fun j => hrk ▸ j.isLt`. Establish `hidx : ∀ j : Fin (finrank K W), b' (Fin.castAdd (finrank K U) j) = b₀ (Fin.castLE hk ⟨j.val, hlt j⟩)`. Introduce `j`.

Rewrite using `[Basis.reindex_apply]`. Use `congr 1`. Establish `memW : ∀ j, b' (Fin.castAdd (finrank K U) j) ∈ W`. Introduce `j`. Rewrite using `[hidx]`.

Conclude with `hmem _`. Establish `hspanW : W ≤ Submodule.span K (Set.range fun j : Fin (finrank K W) => b' (Fin.castAdd (finrank K U) j))`. Use `hspan.trans (Submodule.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `⟨⟨j.val, by rw [hrk]; exact j.isLt⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[hidx]`. Establish `hzero : ∀ x ∈ W, ∀ j : Fin (finrank K U), b'.repr x (Fin.natAdd (finrank K W) j) = 0`. Introduce `x hx j`. Establish `h1` using `hspanW hx`.

Establish `e : (Set.range fun j : Fin (finrank K W) => b' (Fin.castAdd (finrank K U) j)) = b' '' Set.range (Fin.castAdd (finrank K U))` using `Set.range_comp _ _`. Rewrite `h1` using `[e, b'.mem_span_image]`. Assume the negation of the conclusion as `hne`. Take `⟨l, hl⟩` from `h1 (Finsupp.mem_support_iff.2 hne)`. Establish `hv` using `congrArg Fin.val hl`.

Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at hv`. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsplit : ∀ x, x = ∑ j, b'.repr x (Fin.castAdd _ j) • b' (Fin.castAdd _ j) + ∑ j, b'.repr x (Fin.natAdd _ j) • b' (Fin.natAdd _ j)`. Introduce `x`.

Use `conv_lhs => rw [← b'.sum_repr x]`. Rewrite using `[Fin.sum_univ_add]`. Set `famW : Fin (finrank K W) → W` to `fun j => ⟨b' (Fin.castAdd _ j), memW j⟩`. Establish `liW : LinearIndependent K famW`. Apply `LinearIndependent.of_comp W.subtype` to reduce the goal to its premises.

Conclude with `b'.linearIndependent.comp _ (fun a c hac => Fin.ext (by simpa using congrArg Fin.val hac))`. Establish `hexpW : ∀ w : W, w = ∑ j, b'.repr (w : V) (Fin.castAdd _ j) • famW j`. Introduce `w`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`.

Simplify using `only [Submodule.coe_smul]`. Use `conv_lhs => rw [hsplit (w : V)]`. Simplify using `[hzero _ w.2, famW]`. Establish `spW : ⊤ ≤ Submodule.span K (Set.range famW)`. Introduce `w _`.

Rewrite using `[hexpW w]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`. Set `bW : Basis (Fin (finrank K W)) K W` to `Basis.mk liW spW`. Establish `hbW : ⇑bW = famW` using `Basis.coe_mk _ _`. Establish `reprW : ∀ (w : W) j, bW.repr w j = b'.repr (w : V) (Fin.castAdd _ j)`.

Introduce `w j`. Establish `e : w = ∑ j, b'.repr (w : V) (Fin.castAdd _ j) • bW j`. Rewrite using `[hbW]`. Conclude with `hexpW w`. Use `conv_lhs => rw [e]`.

Rewrite using `[bW.repr_sum_self]`. Set `famQ : Fin (finrank K U) → U` to `fun j => g (b' (Fin.natAdd _ j))`. Establish `hg0 : ∀ j, g (b' (Fin.castAdd (finrank K U) j)) = 0` using `fun j => (hker _).2 (memW j)`. Establish `hgx : ∀ x, g x = ∑ j, b'.repr x (Fin.natAdd _ j) • famQ j`. Introduce `x`.

Use `conv_lhs => rw [hsplit x]`. Rewrite using `[map_add, map_sum, map_sum]`. Simplify using `[famQ, hg0]`. Establish `happ : ∀ c : Fin (finrank K U) → K, ∑ l, c l • b' (Fin.natAdd _ l) = ∑ p, (Fin.append (0 : Fin (finrank K W) → K) c p) • b' p`. Introduce `c`.

Rewrite using `[Fin.sum_univ_add]`. Simplify using the standard rewrite rules. Establish `liQ : LinearIndependent K famQ`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc j`.

Establish `hz : ∑ l, c l • b' (Fin.natAdd _ l) ∈ W`. Rewrite using `[← hker, map_sum]`. Simplify `hc` using `[famQ]`. Establish `hrep : b'.repr (∑ l, c l • b' (Fin.natAdd _ l)) (Fin.natAdd _ j) = c j`. Rewrite using `[happ, b'.repr_sum_self]`.

Simplify using the standard rewrite rules. Rewrite using `[← hrep]`. Conclude with `hzero _ hz j`. Establish `spQ : ⊤ ≤ Submodule.span K (Set.range famQ)`. Introduce `y _`.

Take `⟨x, rfl⟩` from `hg y`. Rewrite using `[hgx x]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`. Set `bQ : Basis (Fin (finrank K U)) K U` to `Basis.mk liQ spQ`. Establish `hbQ : ⇑bQ = famQ` using `Basis.coe_mk _ _`.

Establish `reprQ : ∀ x j, bQ.repr (g x) j = b'.repr x (Fin.natAdd _ j)`. Introduce `x j`. Establish `e : g x = ∑ j, b'.repr x (Fin.natAdd _ j) • bQ j`. Rewrite using `[hbQ]`. Conclude with `hgx x`.

Rewrite using `[e, bQ.repr_sum_self]`. Establish `hLa : IsLatOf C i b' L`. Introduce `x`. Rewrite using `[h x, hlat x]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx q`. Rewrite using `[Basis.repr_reindex_apply]`. Conclude with `hx _`. Introduce `hx q`. Establish `h1` using `hx (finCongr hrs.symm q)`.

Rewrite `h1` using `[Basis.repr_reindex_apply, Equiv.symm_apply_apply]`. Then use the resulting hypothesis. Establish `hLb : IsLatOf C i bW (L.comap W.subtype.toAddMonoidHom)`. Introduce `w`. Rewrite using `[AddSubgroup.mem_comap]`. Use `show (w : V) ∈ L ↔ _`.

Rewrite using `[hLa (w : V)]`. Prove the components needed by the constructor for the conclusion. Introduce `hx j`. Rewrite using `[reprW]`. Conclude with `hx _`.

Introduce `hx q`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) q` and prove the remaining obligations. Rewrite using `[← reprW]`. Conclude with `hx j`. Rewrite using `[hzero _ w.2, map_zero]`.

Conclude with `zero_le`. Establish `hLc : IsLatOf C i bQ (L.map g.toAddMonoidHom)`. Introduce `y`. Rewrite using `[AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩ j show C.v i (bQ.repr (g x) j) ≤ 1`. Rewrite using `[reprQ]`. Conclude with `(hLa x).1 hx _`. Introduce `hy`. Use `⟨∑ l, bQ.repr y l • b' (Fin.natAdd _ l), ?_, ?_⟩` and prove the remaining obligations.

Use `(hLa _).2 ?_` and prove the remaining obligations. Introduce `q`. Rewrite using `[happ, b'.repr_sum_self]`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) q` and prove the remaining obligations. Simplify using `only [Fin.append_left, Pi.zero_apply, map_zero]`.

Conclude with `zero_le`. Simplify using `only [Fin.append_right]`. Conclude with `hy j`. Use `show g _ = y`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul]`. Use `conv_rhs => rw [← bQ.sum_repr y]`. Simplify using `only [hbQ, famQ]`. Use `⟨bW, bQ, b', hLa, hLb, hLc, fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hbW]`.

Rewrite using `[hbQ]`.
-/
private theorem exists_lat_basis_compatible_quotient {V U : Type} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {n : ℕ} (b : Basis (Fin n) K V) (L : AddSubgroup V) (h : IsLatOf C i b L) (W : Submodule K V)
    (g : V →ₗ[K] U) (hg : Function.Surjective g) (hker : ∀ x, g x = 0 ↔ x ∈ W) :
    ∃ (bW : Basis (Fin (finrank K W)) K W) (bQ : Basis (Fin (finrank K U)) K U)
      (b' : Basis (Fin (finrank K W + finrank K U)) K V),
      IsLatOf C i b' L ∧ IsLatOf C i bW (L.comap W.subtype.toAddMonoidHom) ∧
      IsLatOf C i bQ (L.map g.toAddMonoidHom) ∧ (∀ j, b' (Fin.castAdd _ j) = bW j) ∧
      ∀ j, g (b' (Fin.natAdd _ j)) = bQ j := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨b₀, k, hk, hlat, hmem, hspan⟩ := H_affine_combination_eq_of_quadratic_relation C i n b W
  have hkerW : LinearMap.ker g = W := by
    ext x
    exact (LinearMap.mem_ker).trans (hker x)
  have hrs : finrank K W + finrank K U = n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr hg, finrank_top, hkerW, Module.finrank_eq_card_basis b,
      Fintype.card_fin] at h1
    omega
  have hrk : finrank K W = k := by
    apply le_antisymm
    · calc finrank K W
          ≤ finrank K (Submodule.span K (Set.range fun j : Fin k => b₀ (Fin.castLE hk j))) :=
            Submodule.finrank_mono hspan
        _ ≤ Fintype.card (Fin k) := finrank_range_le_card _
        _ = k := Fintype.card_fin k
    · have hli : LinearIndependent K (fun j : Fin k => (⟨b₀ (Fin.castLE hk j), hmem j⟩ : W)) := by
        apply LinearIndependent.of_comp W.subtype
        exact b₀.linearIndependent.comp _ (Fin.castLE_injective hk)
      simpa using hli.fintype_card_le_finrank
  let b' : Basis (Fin (finrank K W + finrank K U)) K V := b₀.reindex (finCongr hrs.symm)
  have hlt : ∀ j : Fin (finrank K W), j.val < k := fun j => hrk ▸ j.isLt
  have hidx : ∀ j : Fin (finrank K W),
      b' (Fin.castAdd (finrank K U) j) = b₀ (Fin.castLE hk ⟨j.val, hlt j⟩) := by
    intro j
    rw [Basis.reindex_apply]
    congr 1
  have memW : ∀ j, b' (Fin.castAdd (finrank K U) j) ∈ W := by
    intro j
    rw [hidx]
    exact hmem _
  have hspanW : W ≤ Submodule.span K
      (Set.range fun j : Fin (finrank K W) => b' (Fin.castAdd (finrank K U) j)) := by
    refine hspan.trans (Submodule.span_mono ?_)
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨j.val, by rw [hrk]; exact j.isLt⟩, ?_⟩
    dsimp only
    rw [hidx]
  have hzero : ∀ x ∈ W, ∀ j : Fin (finrank K U), b'.repr x (Fin.natAdd (finrank K W) j) = 0 := by
    intro x hx j
    have h1 := hspanW hx
    have e : (Set.range fun j : Fin (finrank K W) => b' (Fin.castAdd (finrank K U) j)) =
        b' '' Set.range (Fin.castAdd (finrank K U)) := Set.range_comp _ _
    rw [e, b'.mem_span_image] at h1
    by_contra hne
    obtain ⟨l, hl⟩ := h1 (Finsupp.mem_support_iff.2 hne)
    have hv := congrArg Fin.val hl
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have := l.isLt
    omega
  have hsplit : ∀ x, x = ∑ j, b'.repr x (Fin.castAdd _ j) • b' (Fin.castAdd _ j) +
      ∑ j, b'.repr x (Fin.natAdd _ j) • b' (Fin.natAdd _ j) := by
    intro x
    conv_lhs => rw [← b'.sum_repr x]
    rw [Fin.sum_univ_add]
  let famW : Fin (finrank K W) → W := fun j => ⟨b' (Fin.castAdd _ j), memW j⟩
  have liW : LinearIndependent K famW := by
    apply LinearIndependent.of_comp W.subtype
    exact b'.linearIndependent.comp _ (fun a c hac => Fin.ext (by simpa using congrArg Fin.val hac))
  have hexpW : ∀ w : W, w = ∑ j, b'.repr (w : V) (Fin.castAdd _ j) • famW j := by
    intro w
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    conv_lhs => rw [hsplit (w : V)]
    simp [hzero _ w.2, famW]
  have spW : ⊤ ≤ Submodule.span K (Set.range famW) := by
    intro w _
    rw [hexpW w]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bW : Basis (Fin (finrank K W)) K W := Basis.mk liW spW
  have hbW : ⇑bW = famW := Basis.coe_mk _ _
  have reprW : ∀ (w : W) j, bW.repr w j = b'.repr (w : V) (Fin.castAdd _ j) := by
    intro w j
    have e : w = ∑ j, b'.repr (w : V) (Fin.castAdd _ j) • bW j := by
      rw [hbW]
      exact hexpW w
    conv_lhs => rw [e]
    rw [bW.repr_sum_self]
  let famQ : Fin (finrank K U) → U := fun j => g (b' (Fin.natAdd _ j))
  have hg0 : ∀ j, g (b' (Fin.castAdd (finrank K U) j)) = 0 := fun j => (hker _).2 (memW j)
  have hgx : ∀ x, g x = ∑ j, b'.repr x (Fin.natAdd _ j) • famQ j := by
    intro x
    conv_lhs => rw [hsplit x]
    rw [map_add, map_sum, map_sum]
    simp [famQ, hg0]
  have happ : ∀ c : Fin (finrank K U) → K, ∑ l, c l • b' (Fin.natAdd _ l) =
      ∑ p, (Fin.append (0 : Fin (finrank K W) → K) c p) • b' p := by
    intro c
    rw [Fin.sum_univ_add]
    simp
  have liQ : LinearIndependent K famQ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hz : ∑ l, c l • b' (Fin.natAdd _ l) ∈ W := by
      rw [← hker, map_sum]
      simpa [famQ] using hc
    have hrep : b'.repr (∑ l, c l • b' (Fin.natAdd _ l)) (Fin.natAdd _ j) = c j := by
      rw [happ, b'.repr_sum_self]
      simp
    rw [← hrep]
    exact hzero _ hz j
  have spQ : ⊤ ≤ Submodule.span K (Set.range famQ) := by
    intro y _
    obtain ⟨x, rfl⟩ := hg y
    rw [hgx x]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bQ : Basis (Fin (finrank K U)) K U := Basis.mk liQ spQ
  have hbQ : ⇑bQ = famQ := Basis.coe_mk _ _
  have reprQ : ∀ x j, bQ.repr (g x) j = b'.repr x (Fin.natAdd _ j) := by
    intro x j
    have e : g x = ∑ j, b'.repr x (Fin.natAdd _ j) • bQ j := by
      rw [hbQ]
      exact hgx x
    rw [e, bQ.repr_sum_self]
  have hLa : IsLatOf C i b' L := by
    intro x
    rw [h x, hlat x]
    constructor
    · intro hx q
      rw [Basis.repr_reindex_apply]
      exact hx _
    · intro hx q
      have h1 := hx (finCongr hrs.symm q)
      rwa [Basis.repr_reindex_apply, Equiv.symm_apply_apply] at h1
  have hLb : IsLatOf C i bW (L.comap W.subtype.toAddMonoidHom) := by
    intro w
    rw [AddSubgroup.mem_comap]
    show (w : V) ∈ L ↔ _
    rw [hLa (w : V)]
    constructor
    · intro hx j
      rw [reprW]
      exact hx _
    · intro hx q
      refine Fin.addCases (fun j => ?_) (fun j => ?_) q
      · rw [← reprW]
        exact hx j
      · rw [hzero _ w.2, map_zero]
        exact zero_le
  have hLc : IsLatOf C i bQ (L.map g.toAddMonoidHom) := by
    intro y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      show C.v i (bQ.repr (g x) j) ≤ 1
      rw [reprQ]
      exact (hLa x).1 hx _
    · intro hy
      refine ⟨∑ l, bQ.repr y l • b' (Fin.natAdd _ l), ?_, ?_⟩
      · refine (hLa _).2 ?_
        intro q
        rw [happ, b'.repr_sum_self]
        refine Fin.addCases (fun j => ?_) (fun j => ?_) q
        · simp only [Fin.append_left, Pi.zero_apply, map_zero]
          exact zero_le
        · simp only [Fin.append_right]
          exact hy j
      · show g _ = y
        rw [map_sum]
        simp only [map_smul]
        conv_rhs => rw [← bQ.sum_repr y]
        simp only [hbQ, famQ]
  refine ⟨bW, bQ, b', hLa, hLb, hLc, fun j => ?_, fun j => ?_⟩
  · rw [hbW]
  · rw [hbQ]

/- English proof (translation)
Conclude with `exists_lat_basis_compatible_quotient C i b L h W W.mkQ (Submodule.mkQ_surjective W) (fun x => Submodule.Quotient.mk_eq_zero W)`.
-/
theorem exists_adapted (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    (i : C.I) (n : ℕ) (b : Module.Basis (Fin n) K V) (L : AddSubgroup V) (W : Submodule K V)
    (h : IsLatOf C i b L) :
    ∃ (bW : Module.Basis (Fin (Module.finrank K W)) K W)
      (bQ : Module.Basis (Fin (Module.finrank K (V ⧸ W))) K (V ⧸ W))
      (b' : Module.Basis (Fin (Module.finrank K W + Module.finrank K (V ⧸ W))) K V),
      IsLatOf C i b' L ∧ IsLatOf C i bW (L.comap W.subtype.toAddMonoidHom) ∧
      IsLatOf C i bQ (L.map W.mkQ.toAddMonoidHom) ∧ (∀ j, b' (Fin.castAdd _ j) = bW j) ∧
      ∀ j, W.mkQ (b' (Fin.natAdd _ j)) = bQ j := by
  exact exists_lat_basis_compatible_quotient C i b L h W W.mkQ (Submodule.mkQ_surjective W)
    (fun x => Submodule.Quotient.mk_eq_zero W)

end GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted
