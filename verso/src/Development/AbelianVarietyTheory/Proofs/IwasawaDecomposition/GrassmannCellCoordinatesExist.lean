import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.Normal

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A S h0 hc`. Establish `hAS : A ⊆ S` using `Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 h0)`. Take `rfl : A = S` from `Finset.eq_of_subset_of_card_le hAS hc.ge`.

Conclude with `⟨1, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => h⟩`. Consider the case `succ n ih`. Introduce `A S h0 hc`. Take `⟨x, hx⟩ : (A \ S).Nonempty` from `Finset.card_pos.1 (by omega)`. Establish `h1 : (S \ A).card = n + 1` using `by rw [← Finset.card_sdiff_comm hc]; exact h0`.

Take `⟨y, hy⟩ : (S \ A).Nonempty` from `Finset.card_pos.1 (by omega)`. Rewrite `hx`, `hy` using `[Finset.mem_sdiff]`. Establish `hyx : y ≠ x` using `fun e => hy.2 (e ▸ hx.1)`. Establish `hc' : (insert y (A.erase x)).card = S.card`. Rewrite using `[Finset.card_insert_of_notMem (fun h => hy.2 (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hx.1, ← hc]`.

Use `Finset.card_pos.2 ⟨x, hx.1⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h0' : (insert y (A.erase x) \ S).card = n`. Establish `e : insert y (A.erase x) \ S = (A \ S).erase x`. Use extensionality with `i`.

Distinguish the cases in `hiy : i = y`. Substitute `hiy` using the available equality. Simplify using `[hy.1]`. Simplify using `[hiy]`. The claim follows by propositional logic.

Rewrite using `[e, Finset.card_erase_of_mem (Finset.mem_sdiff.2 hx), h0]`. Both sides reduce to the same expression. Take `⟨w, f1, f2, f3⟩` from `ih _ S h0' hc'`. Use `⟨w * Equiv.swap x y, fun i hA hS => ?_, fun i hA hS => ?_, fun i hA => ?_⟩` and prove the remaining obligations. Establish `hix : i ≠ x` using `fun e => hx.2 (e ▸ hS)`.

Establish `hiy : i ≠ y` using `fun e => hy.2 (e ▸ hA)`. Rewrite using `[Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hix hiy]`. Conclude with `f1 i (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hix, hA⟩)) hS`. Establish `hix : i ≠ x` using `fun e => hA (e ▸ hx.1)`. Establish `hiy : i ≠ y` using `fun e => hS (e ▸ hy.1)`.

Rewrite using `[Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hix hiy]`. Use `f2 i (fun h => ?_) hS` and prove the remaining obligations. Break down `Finset.mem_insert.1 h with h | h` into its components or cases. Conclude with `hiy h`. Conclude with `hA (Finset.mem_of_mem_erase h)`.

Rewrite using `[Equiv.Perm.mul_apply]`. Distinguish the cases in `hix : i = x`. Substitute `hix` using the available equality. Rewrite using `[Equiv.swap_apply_left]`. Conclude with `f3 y (Finset.mem_insert_self _ _)`.

Establish `hiy : i ≠ y` using `fun e => hy.2 (e ▸ hA)`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hix hiy]`. Conclude with `f3 i (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hix, hA⟩))`.
-/
theorem exists_perm {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) : ∀ A S : Finset ι, (A \ S).card = n →
    A.card = S.card → ∃ w : Equiv.Perm ι, (∀ i, i ∈ A → i ∈ S → w i = i) ∧ (∀ i, i ∉ A → i ∉ S → w i = i) ∧
      ∀ i ∈ A, w i ∈ S := by
  induction n with
  | zero =>
    intro A S h0 hc
    have hAS : A ⊆ S := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 h0)
    obtain rfl : A = S := Finset.eq_of_subset_of_card_le hAS hc.ge
    exact ⟨1, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => h⟩
  | succ n ih =>
    intro A S h0 hc
    obtain ⟨x, hx⟩ : (A \ S).Nonempty := Finset.card_pos.1 (by omega)
    have h1 : (S \ A).card = n + 1 := by rw [← Finset.card_sdiff_comm hc]; exact h0
    obtain ⟨y, hy⟩ : (S \ A).Nonempty := Finset.card_pos.1 (by omega)
    rw [Finset.mem_sdiff] at hx hy
    have hyx : y ≠ x := fun e => hy.2 (e ▸ hx.1)
    have hc' : (insert y (A.erase x)).card = S.card := by
      rw [Finset.card_insert_of_notMem (fun h => hy.2 (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hx.1, ← hc]
      have := Finset.card_pos.2 ⟨x, hx.1⟩
      omega
    have h0' : (insert y (A.erase x) \ S).card = n := by
      have e : insert y (A.erase x) \ S = (A \ S).erase x := by
        ext i
        by_cases hiy : i = y
        · subst hiy
          simp [hy.1]
        · simp [hiy]
          tauto
      rw [e, Finset.card_erase_of_mem (Finset.mem_sdiff.2 hx), h0]
      rfl
    obtain ⟨w, f1, f2, f3⟩ := ih _ S h0' hc'
    refine ⟨w * Equiv.swap x y, fun i hA hS => ?_, fun i hA hS => ?_, fun i hA => ?_⟩
    · have hix : i ≠ x := fun e => hx.2 (e ▸ hS)
      have hiy : i ≠ y := fun e => hy.2 (e ▸ hA)
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hix hiy]
      exact f1 i (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hix, hA⟩)) hS
    · have hix : i ≠ x := fun e => hA (e ▸ hx.1)
      have hiy : i ≠ y := fun e => hS (e ▸ hy.1)
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hix hiy]
      refine f2 i (fun h => ?_) hS
      rcases Finset.mem_insert.1 h with h | h
      · exact hiy h
      · exact hA (Finset.mem_of_mem_erase h)
    · rw [Equiv.Perm.mul_apply]
      by_cases hix : i = x
      · subst hix
        rw [Equiv.swap_apply_left]
        exact f3 y (Finset.mem_insert_self _ _)
      · have hiy : i ≠ y := fun e => hy.2 (e ▸ hA)
        rw [Equiv.swap_apply_of_ne_of_ne hix hiy]
        exact f3 i (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hix, hA⟩))

variable {K : Type} [Field K]

/- English proof (translation)
Use `set v : Fin m → Fin k → K := fun i l => P l i with hv`. Establish `hspan : Submodule.span K (Set.range v) = ⊤`. Establish `h1 : (Matrix.of P).rank = k`. Use `LinearIndependent.rank_matrix (M := Matrix.of P) hr` as an intermediate fact. Simplify using `using this`.

Rewrite `h1` using `[Matrix.rank_eq_finrank_span_cols]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fin_fun]`. Conclude with `h1`. Take `⟨S, hSt, hsS, hsp, hS⟩` from `exists_linearIndepOn_extension (t := {i : Fin m | (i : ℕ) < b}) hc (fun i (hi : (i : ℕ) < a) => show (i : ℕ) < b by omega)`.

Establish `htop : Submodule.span K (v '' S) = ⊤`. Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Distinguish the cases in `hi : (i : ℕ) < b`. Conclude with `hsp ⟨i, hi, rfl⟩`.

Establish `: v i = 0` using `funext fun l => h0 l i (not_lt.1 hi)`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Establish `hcard : S.toFinset.card = k`. Establish `h2` using `finrank_span_eq_card (R := K) hS`.

Establish `h3 : Set.range (fun i : S => v i) = v '' S` using `(Set.image_eq_range v S).symm`. Rewrite `h2` using `[h3, htop, finrank_top, Module.finrank_fin_fun]`. Rewrite using `[Set.toFinset_card, ← h2]`. Establish `hA : (Finset.univ.map (Fin.castLEEmb hk)).card = S.toFinset.card`. Rewrite using `[Finset.card_map, Finset.card_univ, Fintype.card_fin, hcard]`.

Establish `hmem : ∀ i : Fin m, i ∈ Finset.univ.map (Fin.castLEEmb hk) ↔ (i : ℕ) < k`. Introduce `i`. Simplify using `only [Finset.mem_map, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, rfl⟩`.

Conclude with `j.2`. Introduce `h`. Conclude with `⟨⟨i, h⟩, rfl⟩`. Take `⟨w, f1, f2, f3⟩` from `exists_perm _ _ _ rfl hA`. Use `⟨⟨w, fun i hi => ?_⟩, ?_⟩` and prove the remaining obligations.

Break down `hi with hi | hi` into its components or cases. Conclude with `f1 i ((hmem i).2 (by omega)) (Set.mem_toFinset.2 (hsS hi))`. Use `f2 i (fun h => ?_) fun h => ?_` and prove the remaining obligations. Use `(hmem i).1 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `not_lt.2 hi (hSt (Set.mem_toFinset.1 h))`. Establish `hw : ∀ l : Fin k, w (Fin.castLE hk l) ∈ S` using `fun l => Set.mem_toFinset.1 (f3 _ ((hmem _).2 l.2))`. Establish `hli` using `LinearIndependent.comp hS (fun l : Fin k => (⟨w (Fin.castLE hk l), hw l⟩ : S)) fun l l' e => Fin.castLE_injective hk (w.injective (congrArg Subtype.val e))`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero`.
-/
theorem exists_minor {m a k b : ℕ} (hak : a ≤ k) (hkb : k ≤ b) (hk : k ≤ m) (P : Fin k → Fin m → K)
    (hr : LinearIndependent K P) (h0 : ∀ l (i : Fin m), b ≤ (i : ℕ) → P l i = 0)
    (hc : LinearIndepOn K (fun i l => P l i) {i : Fin m | (i : ℕ) < a}) :
    ∃ w : GPm m a b, (Matrix.of fun l l' : Fin k => P l (w.1 (Fin.castLE hk l'))).det ≠ 0 := by
  classical
  set v : Fin m → Fin k → K := fun i l => P l i with hv
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    have h1 : (Matrix.of P).rank = k := by
      have := LinearIndependent.rank_matrix (M := Matrix.of P) hr
      simpa using this
    rw [Matrix.rank_eq_finrank_span_cols] at h1
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact h1
  obtain ⟨S, hSt, hsS, hsp, hS⟩ := exists_linearIndepOn_extension (t := {i : Fin m | (i : ℕ) < b}) hc
    (fun i (hi : (i : ℕ) < a) => show (i : ℕ) < b by omega)
  have htop : Submodule.span K (v '' S) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : (i : ℕ) < b
    · exact hsp ⟨i, hi, rfl⟩
    · have : v i = 0 := funext fun l => h0 l i (not_lt.1 hi)
      rw [this]
      exact Submodule.zero_mem _
  have hcard : S.toFinset.card = k := by
    have h2 := finrank_span_eq_card (R := K) hS
    have h3 : Set.range (fun i : S => v i) = v '' S := (Set.image_eq_range v S).symm
    rw [h3, htop, finrank_top, Module.finrank_fin_fun] at h2
    rw [Set.toFinset_card, ← h2]
  have hA : (Finset.univ.map (Fin.castLEEmb hk)).card = S.toFinset.card := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hcard]
  have hmem : ∀ i : Fin m, i ∈ Finset.univ.map (Fin.castLEEmb hk) ↔ (i : ℕ) < k := by
    intro i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact j.2
    · intro h
      exact ⟨⟨i, h⟩, rfl⟩
  obtain ⟨w, f1, f2, f3⟩ := exists_perm _ _ _ rfl hA
  refine ⟨⟨w, fun i hi => ?_⟩, ?_⟩
  · rcases hi with hi | hi
    · exact f1 i ((hmem i).2 (by omega)) (Set.mem_toFinset.2 (hsS hi))
    · refine f2 i (fun h => ?_) fun h => ?_
      · have := (hmem i).1 h
        omega
      · exact not_lt.2 hi (hSt (Set.mem_toFinset.1 h))
  · have hw : ∀ l : Fin k, w (Fin.castLE hk l) ∈ S := fun l => Set.mem_toFinset.1 (f3 _ ((hmem _).2 l.2))
    have hli := LinearIndependent.comp hS (fun l : Fin k => (⟨w (Fin.castLE hk l), hw l⟩ : S)) fun l l' e =>
      Fin.castLE_injective hk (w.injective (congrArg Subtype.val e))
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero

def pr {n : ℕ} (d : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun v := ∑ r, d r * v r
  map_add' v v' := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_apply {n : ℕ} (d v : Fin n → K) : pr d v = ∑ r, d r * v r := rfl

variable {m n : ℕ} {D c : Fin m → Fin n → K}

/- English proof (translation)
Rewrite using `[pr_apply, h i j]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem pr_c (h : LeftInv D c) (i j : Fin m) : pr (D i) (c j) = if i = j then 1 else 0 := by
  rw [pr_apply, h i j]
  split_ifs <;> rfl

/- English proof (translation)
Simplify using `[map_sum, map_smul, pr_c h]`.
-/
theorem pr_sum (h : LeftInv D c) (t : Fin m → K) (i : Fin m) : pr (D i) (∑ j, t j • c j) = t i := by
  simp [map_sum, map_smul, pr_c h]

/- English proof (translation)
Take `⟨t, ht, rfl⟩` from `FlagMod.mem_initSpan.1 hv`. Simplify using `only [pr_sum h]`. Conclude with `⟨ht, trivial⟩`.
-/
theorem coord (h : LeftInv D c) {b : ℕ} {v : Fin n → K} (hv : v ∈ initSpan K c b) :
    (∀ i : Fin m, b ≤ (i : ℕ) → pr (D i) v = 0) ∧ ∑ i, pr (D i) v • c i = v := by
  obtain ⟨t, ht, rfl⟩ := FlagMod.mem_initSpan.1 hv
  simp only [pr_sum h]
  exact ⟨ht, trivial⟩

/- English proof (translation)
Use `exists_minor hak hkb hk (fun l i => pr (D i) (u l)) ?_ (fun l i hi => (coord h (h2 (Submodule.subset_span ⟨l, rfl⟩))).1 i hi) ?_` and prove the remaining obligations. Rewrite `hu`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Apply `hu g` to reduce the goal to its premises. Establish `hv : ∑ l, g l • u l ∈ initSpan K c b` using `h2 (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))`.

Rewrite using `[← (coord h hv).2]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `congrFun hg i` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at this`. Simplify using `only [map_sum, map_smul, this, zero_smul]`.

Rewrite using `[LinearIndepOn, Fintype.linearIndependent_iff]`. Introduce `g hg j`. Take `⟨t, ht⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 (h1 (Submodule.subset_span ⟨j.1, j.2, rfl⟩ : c j.1 ∈ initSpan K c a))`. Establish `e1 : ∑ i : {i : Fin m | (i : ℕ) < a}, g i * pr (D i.1) (c j.1) = 0`. Simplify using `only [← ht, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Use `congrFun hg l` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this`. Rewrite using `[← mul_zero (t l), ← this, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite `e1` using `[Finset.sum_eq_single j]`. Simplify `e1` using `[pr_c h]`. Introduce `i _ hi`. Rewrite using `[pr_c h, if_neg (fun e => hi (Subtype.ext e)), mul_zero]`.

Simplify using the standard rewrite rules.
-/
theorem exists_cell {a k b : ℕ} (hk : k ≤ m) {u : Fin k → Fin n → K} (hak : a ≤ k) (hkb : k ≤ b) (h : LeftInv D c)
    (hu : LinearIndependent K u) (h1 : initSpan K c a ≤ Submodule.span K (Set.range u))
    (h2 : Submodule.span K (Set.range u) ≤ initSpan K c b) :
    ∃ w : GPm m a b, (Matrix.of fun l l' : Fin k => pr (D (w.1 (Fin.castLE hk l'))) (u l)).det ≠ 0 := by
  classical
  refine exists_minor hak hkb hk (fun l i => pr (D i) (u l)) ?_
    (fun l i hi => (coord h (h2 (Submodule.subset_span ⟨l, rfl⟩))).1 i hi) ?_
  · rw [Fintype.linearIndependent_iff] at hu ⊢
    intro g hg
    apply hu g
    have hv : ∑ l, g l • u l ∈ initSpan K c b :=
      h2 (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
    rw [← (coord h hv).2]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at this
    simp only [map_sum, map_smul, this, zero_smul]
  · rw [LinearIndepOn, Fintype.linearIndependent_iff]
    intro g hg j
    obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
      (h1 (Submodule.subset_span ⟨j.1, j.2, rfl⟩ : c j.1 ∈ initSpan K c a))
    have e1 : ∑ i : {i : Fin m | (i : ℕ) < a}, g i * pr (D i.1) (c j.1) = 0 := by
      simp only [← ht, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      have := congrFun hg l
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
      rw [← mul_zero (t l), ← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_eq_single j] at e1
    · simpa [pr_c h] using e1
    · intro i _ hi
      rw [pr_c h, if_neg (fun e => hi (Subtype.ext e)), mul_zero]
    · simp

/- English proof (translation)
Use `⟨fun il => pr (D (w.1 il.1.1)) (u ⟨il.1.2, il.2.2.1⟩), fun l => ?_⟩` and prove the remaining obligations. Establish `hl` using `coord h (h2 (Submodule.subset_span ⟨l, rfl⟩))`. Rewrite using `[← hl.2, ← Equiv.sum_comp w.1, gvec]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`.

Unfold `gcell`. Use `split_ifs with c1 c2`. Both sides reduce to the same expression. Substitute `c2` using the available equality. Rewrite using `[hδ, if_pos rfl]`.

Distinguish the cases in `hik : (i : ℕ) < k`. Use `hδ l ⟨i, hik⟩` as an intermediate fact. Rewrite `this` using `[if_neg (fun e => c2 (by subst e; rfl))]`. Conclude with `this`. Distinguish the cases in `hib : (i : ℕ) < b`.

Establish `hla : (l : ℕ) < a`. Assume the negation of the conclusion as `hla`. Conclude with `c1 ⟨not_lt.1 hla, l.2, not_lt.1 hik, hib⟩`. Establish `hwl : w.1 (Fin.castLE hk l) = Fin.castLE hk l` using `w.2 _ (Or.inl hla)`. Take `⟨t, ht⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 (h1 (Submodule.subset_span ⟨Fin.castLE hk l, hla, rfl⟩ : c (Fin.castLE hk l) ∈ initSpan K c a))`.

Establish `htl : ∀ l', t l' = if l' = l then 1 else 0`. Introduce `l'`. Establish `e` using `congrArg (pr (D (w.1 (Fin.castLE hk l')))) ht`. Simplify using `only [map_sum, map_smul, hδ, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e`. Rewrite using `[e, pr_c h, ← hwl]`.

Simplify using the standard rewrite rules. Establish `hul : u l = c (Fin.castLE hk l)`. Rewrite using `[← ht]`. Simplify using `[htl]`. Rewrite using `[hul, pr_c h, if_neg]`.

Introduce `e`. Conclude with `c2 (w.1.injective (e.trans hwl.symm))`. Rewrite using `[w.2 i (Or.inr (not_lt.1 hib))]`. Conclude with `hl.1 i (not_lt.1 hib)`.
-/
theorem eq_gvec {a k b : ℕ} (hk : k ≤ m) {u : Fin k → Fin n → K} (hak : a ≤ k) (h : LeftInv D c)
    (h1 : initSpan K c a ≤ Submodule.span K (Set.range u))
    (h2 : Submodule.span K (Set.range u) ≤ initSpan K c b) (w : GPm m a b)
    (hδ : ∀ l l' : Fin k, pr (D (w.1 (Fin.castLE hk l'))) (u l) = if l = l' then 1 else 0) :
    ∃ x : GVar m a k b → K, ∀ l : Fin k, u l = gvec c w x (Fin.castLE hk l) := by
  refine ⟨fun il => pr (D (w.1 il.1.1)) (u ⟨il.1.2, il.2.2.1⟩), fun l => ?_⟩
  have hl := coord h (h2 (Submodule.subset_span ⟨l, rfl⟩))
  rw [← hl.2, ← Equiv.sum_comp w.1, gvec]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold gcell
  split_ifs with c1 c2
  · rfl
  · subst c2
    rw [hδ, if_pos rfl]
  · by_cases hik : (i : ℕ) < k
    · have := hδ l ⟨i, hik⟩
      rw [if_neg (fun e => c2 (by subst e; rfl))] at this
      exact this
    · by_cases hib : (i : ℕ) < b
      · have hla : (l : ℕ) < a := by
          by_contra hla
          exact c1 ⟨not_lt.1 hla, l.2, not_lt.1 hik, hib⟩
        have hwl : w.1 (Fin.castLE hk l) = Fin.castLE hk l := w.2 _ (Or.inl hla)
        obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
          (h1 (Submodule.subset_span ⟨Fin.castLE hk l, hla, rfl⟩ : c (Fin.castLE hk l) ∈ initSpan K c a))
        have htl : ∀ l', t l' = if l' = l then 1 else 0 := by
          intro l'
          have e := congrArg (pr (D (w.1 (Fin.castLE hk l')))) ht
          simp only [map_sum, map_smul, hδ, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true] at e
          rw [e, pr_c h, ← hwl]
          simp
        have hul : u l = c (Fin.castLE hk l) := by
          rw [← ht]
          simp [htl]
        rw [hul, pr_c h, if_neg]
        intro e
        exact c2 (w.1.injective (e.trans hwl.symm))
      · rw [w.2 i (Or.inr (not_lt.1 hib))]
        exact hl.1 i (not_lt.1 hib)

/- English proof (translation)
Use `set A : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' : Fin k => pr (D (w.1 (Fin.castLE hk l'))) (u l) with hA`. Establish `hU : IsUnit A.det` using `hd.isUnit`. Use `set u' : Fin k → Fin n → K := fun l => ∑ l', A⁻¹ l l' • u l' with hu'`. Establish `hsp : Submodule.span K (Set.range u) = Submodule.span K (Set.range u')`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`. Use `(Submodule.mem_span_range_iff_exists_fun K).2 ⟨A l, ?_⟩` and prove the remaining obligations. Simplify using `only [hu', Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.mul_nonsing_inv A hU, Matrix.one_apply]`. Simplify using the standard rewrite rules. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `(Submodule.mem_span_range_iff_exists_fun K).2 ⟨A⁻¹ l, rfl⟩`.

Rewrite `h1`, `h2`, the goal using `[hsp]`. Take `⟨x, hx⟩` from `eq_gvec hk hak h h1 h2 w fun l l' => by`. Establish `e` using `congrFun (congrFun (Matrix.nonsing_inv_mul A hU) l) l'`. Rewrite `e` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← e]`.

Simplify using `only [hu', map_sum, map_smul, smul_eq_mul]`. Both sides reduce to the same expression. Use `⟨x, congrArg (Submodule.span K) ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨l, rfl⟩`. Conclude with `⟨Fin.castLE hk l, l.2, (hx l).symm⟩`. Introduce and unpack `⟨j, hj, rfl⟩`. Conclude with `⟨⟨j, hj⟩, hx ⟨j, hj⟩⟩`.
-/
theorem mem_cell {a k b : ℕ} (hk : k ≤ m) {u : Fin k → Fin n → K} (hak : a ≤ k) (h : LeftInv D c)
    (h1 : initSpan K c a ≤ Submodule.span K (Set.range u))
    (h2 : Submodule.span K (Set.range u) ≤ initSpan K c b) (w : GPm m a b)
    (hd : (Matrix.of fun l l' : Fin k => pr (D (w.1 (Fin.castLE hk l'))) (u l)).det ≠ 0) :
    ∃ x : GVar m a k b → K, Submodule.span K (Set.range u) = initSpan K (gvec c w x) k := by
  set A : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' : Fin k => pr (D (w.1 (Fin.castLE hk l'))) (u l) with hA
  have hU : IsUnit A.det := hd.isUnit
  set u' : Fin k → Fin n → K := fun l => ∑ l', A⁻¹ l l' • u l' with hu'
  have hsp : Submodule.span K (Set.range u) = Submodule.span K (Set.range u') := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨A l, ?_⟩
      simp only [hu', Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.mul_nonsing_inv A hU, Matrix.one_apply]
      simp
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact (Submodule.mem_span_range_iff_exists_fun K).2 ⟨A⁻¹ l, rfl⟩
  rw [hsp] at h1 h2 ⊢
  obtain ⟨x, hx⟩ := eq_gvec hk hak h h1 h2 w fun l l' => by
    have e := congrFun (congrFun (Matrix.nonsing_inv_mul A hU) l) l'
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    rw [← e]
    simp only [hu', map_sum, map_smul, smul_eq_mul]
    rfl
  refine ⟨x, congrArg (Submodule.span K) ?_⟩
  ext v
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Fin.castLE hk l, l.2, (hx l).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, hx ⟨j, hj⟩⟩

/- English proof (translation)
Introduce `K _ m a k b N hk D c u hak hkb h hu h1 h2`. Establish `e : ∀ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q = (Matrix.of fun l l' : Fin k => pr (D (w.1 (Fin.castLE hk l'))) (u l)).det` using `fun w => FlagEmb.CauchyBinet.lform_plk K N k _ _ D u (w.1 ∘ Fin.castLE hk) id`. Simplify using `only [e]`. Conclude with `⟨exists_cell hk hak hkb h hu h1 h2, fun w hd => mem_cell hk hak h h1 h2 w hd⟩`.
-/
theorem main : ∀ (K : Type) [Field K] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → K) (u : Fin k → Fin (N + 1) → K), a ≤ k → k ≤ b → LeftInv D c → LinearIndependent K u → initSpan K c a ≤ Submodule.span K (Set.range u) → Submodule.span K (Set.range u) ≤ initSpan K c b → (∃ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q ≠ 0) ∧ ∀ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q ≠ 0 → ∃ x : GVar m a k b → K, Submodule.span K (Set.range u) = initSpan K (gvec c w x) k := by
  intro K _ m a k b N hk D c u hak hkb h hu h1 h2
  have e : ∀ w : GPm m a b, ∑ q, gell a b hk D w q * plk u id q =
      (Matrix.of fun l l' : Fin k => pr (D (w.1 (Fin.castLE hk l'))) (u l)).det := fun w =>
    FlagEmb.CauchyBinet.lform_plk K N k _ _ D u (w.1 ∘ Fin.castLE hk) id
  simp only [e]
  exact ⟨exists_cell hk hak hkb h hu h1 h2, fun w hd => mem_cell hk hak h h1 h2 w hd⟩

end GlobalTheory.GrCl.Normal
