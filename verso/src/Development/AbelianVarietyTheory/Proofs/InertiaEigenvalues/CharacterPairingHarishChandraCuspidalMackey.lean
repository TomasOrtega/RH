import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubsetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvariStatement

noncomputable section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.IpCuspProd

section
variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Unfold `ip`. Use `congr 1`. Conclude with `Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => by simp [mul_comm])`.
-/
theorem ip_comm {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => by simp [mul_comm])

/- English proof (translation)
Unfold `ip`. Rewrite using `[Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul, mul_inv]`. Simplify using `only [Prod.fst_inv, Prod.snd_inv]`. Rewrite using `[mul_mul_mul_comm, Finset.sum_mul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring` and prove the remaining obligations.
-/
theorem ip_prod {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] (A C : G → ℂ) (B D : H → ℂ) :
    ip (fun p : G × H => A p.1 * B p.2) (fun p => C p.1 * D p.2) = ip A C * ip B D := by
  unfold ip
  rw [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul, mul_inv]
  simp only [Prod.fst_inv, Prod.snd_inv]
  rw [mul_mul_mul_comm, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/- English proof (translation)
Unfold `ip`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem ip_sum_left {G ι : Type} [Group G] [Fintype G] (S : Finset ι) (f : ι → G → ℂ) (β : G → ℂ) :
    ip (fun x => ∑ i ∈ S, f i x) β = ∑ i ∈ S, ip (f i) β := by
  unfold ip
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Take `⟨V, hV⟩` from `h`. Introduce `x y`. Rewrite using `[← hV, ← hV]`. Conclude with `FDRep.char_conj V x y`.
-/
theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

/- English proof (translation)
Take `⟨-, ⟨V, -, hV⟩, -⟩` from `h`. Conclude with `⟨V, hV⟩`.
-/
theorem isChar_of_isCusp {d : ℕ} {χ : Gn g d → ℂ} (h : IsCusp χ) : IsChar χ := by
  obtain ⟨-, ⟨V, -, hV⟩, -⟩ := h
  exact ⟨V, hV⟩

/- English proof (translation)
Simplify using `[degL]`.
-/
theorem degL_cons (p : Pc g) (L : List (Pc g)) : degL (p :: L) = p.1 + degL L := by
  simp [degL]

/- English proof (translation)
Simplify using `[degL]`.
-/
theorem degL_append (L L' : List (Pc g)) : degL (L ++ L') = degL L + degL L' := by
  simp [degL]

/- English proof (translation)
Unfold `degL`. Conclude with `(h.map _).sum_eq`.
-/
theorem degL_perm {L L' : List (Pc g)} (h : L.Perm L') : degL L = degL L' := by
  unfold degL
  exact (h.map _).sum_eq

/- English proof (translation)
Consider the cases of `L with`. Consider the case `nil => rfl`. Consider the case `cons p r`. Rewrite `h0` using `[degL_cons]`. Use `(hc p (by simp)).1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem eq_nil_of_degL (L : List (Pc g)) (h0 : degL L = 0) (hc : ∀ p ∈ L, IsCusp p.2) : L = [] := by
  cases L with
  | nil => rfl
  | cons p r =>
    rw [degL_cons] at h0
    have := (hc p (by simp)).1
    omega

/- English proof (translation)
Consider the cases of `L with`. Consider the case `nil => exact absurd rfl hne`. Consider the case `cons p r`. Rewrite using `[degL_cons]`. Use `(hc p (by simp)).1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem degL_pos (L : List (Pc g)) (hne : L ≠ []) (hc : ∀ p ∈ L, IsCusp p.2) : 0 < degL L := by
  cases L with
  | nil => exact absurd rfl hne
  | cons p r =>
    rw [degL_cons]
    have := (hc p (by simp)).1
    omega

/- English proof (translation)
Unfold `degL`. Rewrite using `[List.map_map, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]`. Both sides reduce to the same expression.
-/
theorem degL_sort (L : List (Pc g)) (I : Finset (Fin L.length)) :
    degL ((I.sort (· ≤ ·)).map L.get) = ∑ i ∈ I, (L.get i).1 := by
  unfold degL
  rw [List.map_map, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
  rfl

/- English proof (translation)
Rewrite using `[← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.map_coe, ← Multiset.map_coe, Finset.sort_eq, Finset.sort_eq, ← Multiset.map_add, ← Finset.disjUnion_val I Iᶜ (disjoint_compl_right)]`. Rewrite using `[show I.disjUnion Iᶜ disjoint_compl_right = Finset.univ by`. Rewrite using `[Finset.disjUnion_eq_union, Finset.union_compl]]`. Rewrite using `[Fin.univ_val_map, List.ofFn_get]`.
-/
theorem perm_split (L : List (Pc g)) (I : Finset (Fin L.length)) :
    ((I.sort (· ≤ ·)).map L.get ++ (Iᶜ.sort (· ≤ ·)).map L.get).Perm L := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, ← Multiset.map_coe, ← Multiset.map_coe, Finset.sort_eq,
    Finset.sort_eq, ← Multiset.map_add, ← Finset.disjUnion_val I Iᶜ (disjoint_compl_right)]
  rw [show I.disjUnion Iᶜ disjoint_compl_right = Finset.univ by
    rw [Finset.disjUnion_eq_union, Finset.union_compl]]
  rw [Fin.univ_val_map, List.ofFn_get]

/- English proof (translation)
Take `⟨j, -, rfl⟩` from `List.mem_map.1 hp`. Conclude with `List.get_mem L j`.
-/
theorem mem_sort_map {L : List (Pc g)} {I : Finset (Fin L.length)} {p : Pc g}
    (hp : p ∈ (I.sort (· ≤ ·)).map L.get) : p ∈ L := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
  exact List.get_mem L j

/- English proof (translation)
Simplify using `[ip, hcL_nil, Finset.card_univ]`.
-/
theorem ip_triv : ip (hcL ([] : List (Pc g)) 0) (hcL ([] : List (Pc g)) 0) = 1 := by
  simp [ip, hcL_nil, Finset.card_univ]

/- English proof (translation)
Unfold `entN`. Simplify using the standard rewrite rules.
-/
theorem entN_fin' {n : ℕ} (M : Mt g n) (u v : Fin n) : entN M u v = M u v := by
  unfold entN
  simp

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[hcL_cons]`. Use `show hcT d (degL ([] : List (Pc g))) (fun x y => χ x * hcL [] _ y) d x = χ x`. Establish `hP : ∀ M : Mt g d, InPar d M` using `fun M i j _ h => absurd i.2 (by omega)`. Establish `htl : ∀ y : Gn g d, toG (tl d (y : Mt g d)) = y`.

Introduce `y`. Establish `: tl d (y : Mt g d) = (y : Mt g d)`. Use function extensionality and compare the values at `i j`. Conclude with `entN_fin' _ i j`. Rewrite using `[this]`.

Unfold `toG`. Rewrite using `[dif_pos (Units.isUnit y)]`. Conclude with `Units.ext rfl`. Unfold `hcT`. Establish `hcard : (Finset.univ.filter fun p : Gn g d => InPar d (p : Mt g d)) = Finset.univ` using `Finset.filter_true_of_mem (fun p _ => hP _)`.

Rewrite using `[hcard]`. Simplify using `only [hP, if_true, htl, hcL_nil, mul_one, Finset.card_univ]`. Establish `hc : ∀ y : Gn g d, χ (y⁻¹ * x * y) = χ x` using `fun y => by`. Simplify using `using hχ x y⁻¹`. Simplify using `only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Rewrite using `[← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]`.
-/
theorem hcL_single (d : ℕ) (χ : Gn g d → ℂ) (hχ : IsClass χ) : hcL [⟨d, χ⟩] d = χ := by
  funext x
  rw [hcL_cons]
  show hcT d (degL ([] : List (Pc g))) (fun x y => χ x * hcL [] _ y) d x = χ x
  have hP : ∀ M : Mt g d, InPar d M := fun M i j _ h => absurd i.2 (by omega)
  have htl : ∀ y : Gn g d, toG (tl d (y : Mt g d)) = y := by
    intro y
    have : tl d (y : Mt g d) = (y : Mt g d) := by
      funext i j; exact entN_fin' _ i j
    rw [this]
    unfold toG
    rw [dif_pos (Units.isUnit y)]
    exact Units.ext rfl
  unfold hcT
  have hcard : (Finset.univ.filter fun p : Gn g d => InPar d (p : Mt g d)) = Finset.univ :=
    Finset.filter_true_of_mem (fun p _ => hP _)
  rw [hcard]
  simp only [hP, if_true, htl, hcL_nil, mul_one, Finset.card_univ]
  have hc : ∀ y : Gn g d, χ (y⁻¹ * x * y) = χ x := fun y => by
    simpa using hχ x y⁻¹
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

/- English proof (translation)
Use `match K, hK with`. Consider the case `p :: r, hK`. Establish `hr : r ≠ []` using `by rintro rfl; simp at hK`. Establish `hp` using `(hc p (by simp)).1`. Establish `hrpos` using `degL_pos r hr (fun q hq => hc q (by simp [hq]))`.

Rewrite `hd` using `[degL_cons]`. Substitute `hd` using the available equality. Rewrite using `[hcL_cons, ip_comm]`. Use `show ip ψ (hcT p.1 (degL r) (fun x y => p.2 x * hcL r (degL r) y) _) = 0`. Rewrite using `[GlobalTheory.T.harishChandra_frobenius_reciprocity g p.1 (degL r) _ rfl ψ _ (isClass_of_isChar (isChar_of_isCusp hψ))]`.

Establish `h` using `GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g (p.1 + degL r) p.1 ψ hψ hp (by omega)`. Rewrite `h` using `[Nat.add_sub_cancel_left]`. Simplify using `[ip, h]`.
-/
theorem ip_long_cusp (a : ℕ) (ψ : Gn g a → ℂ) (hψ : IsCusp ψ) (K : List (Pc g)) (hK : 2 ≤ K.length)
    (hd : degL K = a) (hc : ∀ p ∈ K, IsCusp p.2) : ip (hcL K a) ψ = 0 := by
  match K, hK with
  | p :: r, hK =>
    have hr : r ≠ [] := by rintro rfl; simp at hK
    have hp := (hc p (by simp)).1
    have hrpos := degL_pos r hr (fun q hq => hc q (by simp [hq]))
    rw [degL_cons] at hd
    subst hd
    rw [hcL_cons, ip_comm]
    show ip ψ (hcT p.1 (degL r) (fun x y => p.2 x * hcL r (degL r) y) _) = 0
    rw [GlobalTheory.T.harishChandra_frobenius_reciprocity g p.1 (degL r) _ rfl ψ _ (isClass_of_isChar (isChar_of_isCusp hψ))]
    have h := GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g (p.1 + degL r) p.1 ψ hψ hp (by omega)
    rw [Nat.add_sub_cancel_left] at h
    simp [ip, h]

/- English proof (translation)
Take `⟨d, χ⟩` from `p`. Simplify using `only at hd hp`. Substitute `hd` using the available equality. Rewrite using `[hcL_single d χ (isClass_of_isChar (isChar_of_isCusp hp)), (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ ψ hp.2.1 hψ.2.1).2.2]`. Distinguish the cases in `h : χ = ψ`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem ip_single_cusp (a : ℕ) (ψ : Gn g a → ℂ) (hψ : IsCusp ψ) (p : Pc g) (hp : IsCusp p.2) (hd : p.1 = a) :
    ip (hcL [p] a) ψ = if p = ⟨a, ψ⟩ then 1 else 0 := by
  obtain ⟨d, χ⟩ := p
  dsimp only at hd hp
  subst hd
  rw [hcL_single d χ (isClass_of_isChar (isChar_of_isCusp hp)), (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ ψ hp.2.1 hψ.2.1).2.2]
  by_cases h : χ = ψ
  · subst h; simp
  · simp [h]

/- English proof (translation)
Establish `hcI : ∀ p ∈ (I.sort (· ≤ ·)).map L.get, IsCusp p.2` using `fun p hp => hc p (mem_sort_map hp)`. Distinguish the cases in `h2 : 2 ≤ I.card`. Rewrite using `[if_neg]`. Conclude with `ip_long_cusp a ψ hψ _ (by simpa using h2) ((degL_sort L I).trans hI) hcI`. Introduce and unpack `⟨i, rfl, -⟩`.

Simplify using `at h2`. Establish `hcard : I.card = 0 ∨ I.card = 1` using `by omega`. Break down `hcard with h0 | h1` into its components or cases. Rewrite `h0` using `[Finset.card_eq_zero]`. Substitute `h0` using the available equality.

Use `hψ.1` as an intermediate fact. Simplify using `at hI`. Use linear arithmetic over natural numbers and integers. Take `⟨i, rfl⟩` from `Finset.card_eq_one.1 h1`. Rewrite using `[Finset.sort_singleton, List.map_singleton]`.

Simplify using `only [Finset.sum_singleton] at hI`. Rewrite using `[ip_single_cusp a ψ hψ _ (hc _ (List.get_mem L i)) hI]`. Distinguish the cases in `h : L.get i = ⟨a, ψ⟩`. Rewrite using `[if_pos h, if_pos ⟨i, rfl, h⟩]`. Rewrite using `[if_neg h, if_neg]`.

Introduce and unpack `⟨j, hj, h'⟩`. Rewrite `hj` using `[Finset.singleton_inj]`. Substitute `hj` using the available equality. Conclude with `h h'`.
-/
theorem ip_sub_cusp (L : List (Pc g)) (hc : ∀ p ∈ L, IsCusp p.2) (a : ℕ) (ψ : Gn g a → ℂ) (hψ : IsCusp ψ)
    (I : Finset (Fin L.length)) (hI : ∑ i ∈ I, (L.get i).1 = a) :
    ip (hcL ((I.sort (· ≤ ·)).map L.get) a) ψ = if ∃ i, I = {i} ∧ L.get i = ⟨a, ψ⟩ then 1 else 0 := by
  have hcI : ∀ p ∈ (I.sort (· ≤ ·)).map L.get, IsCusp p.2 := fun p hp => hc p (mem_sort_map hp)
  by_cases h2 : 2 ≤ I.card
  · rw [if_neg]
    · exact ip_long_cusp a ψ hψ _ (by simpa using h2) ((degL_sort L I).trans hI) hcI
    · rintro ⟨i, rfl, -⟩
      simp at h2
  · have hcard : I.card = 0 ∨ I.card = 1 := by omega
    rcases hcard with h0 | h1
    · rw [Finset.card_eq_zero] at h0
      subst h0
      have := hψ.1
      simp at hI
      omega
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h1
      rw [Finset.sort_singleton, List.map_singleton]
      simp only [Finset.sum_singleton] at hI
      rw [ip_single_cusp a ψ hψ _ (hc _ (List.get_mem L i)) hI]
      by_cases h : L.get i = ⟨a, ψ⟩
      · rw [if_pos h, if_pos ⟨i, rfl, h⟩]
      · rw [if_neg h, if_neg]
        rintro ⟨j, hj, h'⟩
        rw [Finset.singleton_inj] at hj
        subst hj
        exact h h'

/- English proof (translation)
Introduce `L'`. Proceed by induction on `L' with`. Consider the case `nil`. Introduce `L n hL hL' hc _`. Establish `hn : n = 0` using `by rw [← hL']; rfl`.

Substitute `hn` using the available equality. Use `eq_nil_of_degL L hL hc` as an intermediate fact. Substitute `this` using the available equality. Conclude with `⟨fun h => absurd (List.Perm.refl _) h, fun _ _ => ip_triv⟩`. Consider the case `cons q M ih`.

Introduce `L n hL hL' hc hc'`. Take `⟨a, ψ⟩` from `q`. Rewrite `hL'` using `[degL_cons]`. Simplify using `only at hL'`. Substitute `hL'` using the available equality.

Establish `hψ : IsCusp ψ` using `hc' ⟨a, ψ⟩ (by simp)`. Establish `hcM : ∀ p ∈ M, IsCusp p.2` using `fun p hp => hc' p (by simp [hp])`. Establish `hclass : IsClass (hcL L (a + degL M))` using `isClass_of_isChar (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L _ hL.symm (fun p hp => isChar_of_isCusp (hc p hp))).1`. Establish `key : ip (hcL L (a + degL M)) (hcL (⟨a, ψ⟩ :: M) (a + degL M)) = ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ i ∈ I, (L.get i).1 = a), ip (hcL ((I.sort (· ≤ ·)).map L.get) a) ψ * ip (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) (degL M)) (hcL M (degL M))`. Rewrite using `[hcL_cons]`.

Use `show ip _ (hcT a (degL M) (fun x y => ψ x * hcL M (degL M) y) _) = _`. Rewrite using `[GlobalTheory.T.harishChandra_frobenius_reciprocity g a (degL M) _ rfl _ _ hclass]`. Establish `hres` using `GlobalTheory.T.harishChandraRestriction_cuspidal_product_sum_subsets g L a (degL M) hL hc`. Simplify using `only [hres]`. Rewrite using `[ip_sum_left]`.

Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Conclude with `ip_prod _ _ _ _`. Establish `hrest : ∀ i : Fin L.length, L.get i = ⟨a, ψ⟩ → (L.Perm (⟨a, ψ⟩ :: ((({i} : Finset _)ᶜ.sort (· ≤ ·)).map L.get))) ∧ degL ((({i} : Finset _)ᶜ.sort (· ≤ ·)).map L.get) = degL M`. Introduce `i hi`. Establish `hp` using `perm_split L {i}`.

Rewrite `hp` using `[Finset.sort_singleton, List.map_singleton, hi, List.singleton_append]`. Use `⟨hp.symm, ?_⟩` and prove the remaining obligations. Use `degL_perm hp` as an intermediate fact. Rewrite `this` using `[degL_cons, hL]`. Simplify using `only at this`.

Use linear arithmetic over natural numbers and integers. Establish `hcRest : ∀ I : Finset (Fin L.length), ∀ p ∈ (Iᶜ.sort (· ≤ ·)).map L.get, IsCusp p.2` using `fun I p hp => hc p (mem_sort_map hp)`. Use `⟨fun hperm => ?_, fun hperm hnd => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Use `Finset.sum_eq_zero fun I hI => ?_` and prove the remaining obligations.

Rewrite `hI` using `[Finset.mem_filter]`. Rewrite using `[ip_sub_cusp L hc a ψ hψ I hI.2]`. Use `split_ifs with hex`. Take `⟨i, rfl, hi⟩` from `hex`. Take `⟨hp, hd⟩` from `hrest i hi`.

Rewrite using `[(ih _ _ hd rfl (hcRest _) hcM).1 (fun h => hperm (hp.trans (h.cons _))), mul_zero]`. Rewrite using `[zero_mul]`. Rewrite using `[key]`. Establish `hq : (⟨a, ψ⟩ : Pc g) ∈ L` using `hperm.symm.subset (by simp)`. Take `⟨i₀, hi₀⟩` from `List.mem_iff_get.1 hq`.

Establish `hmem : ({i₀} : Finset (Fin L.length)) ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ i ∈ I, (L.get i).1 = a)`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_singleton, hi₀]`. Rewrite using `[Finset.sum_eq_single_of_mem _ hmem]`. Rewrite using `[ip_sub_cusp L hc a ψ hψ _ (Finset.mem_filter.1 hmem).2, if_pos ⟨i₀, rfl, hi₀⟩, one_mul]`. Take `⟨hp, hd⟩` from `hrest i₀ hi₀`.

Establish `hp' : ((({i₀} : Finset _)ᶜ.sort (· ≤ ·)).map L.get).Perm M` using `(hp.symm.trans hperm).cons_inv`. Establish `hnd'` using `(List.nodup_cons.1 (hp.nodup_iff.1 hnd)).2`. Conclude with `(ih _ _ hd rfl (hcRest _) hcM).2 hp' hnd'`. Introduce `I hI hne`. Rewrite using `[ip_sub_cusp L hc a ψ hψ I (Finset.mem_filter.1 hI).2]`.

Use `split_ifs with hex`. Take `⟨i, rfl, hi⟩` from `hex`. Conclude with `absurd (by rw [(List.Nodup.get_inj_iff hnd).1 (hi.trans hi₀.symm)]) hne`. Rewrite using `[zero_mul]`.
-/
theorem finiteRing_sq_sub_mul_sq_eq_of_card : ∀ (L' L : List (Pc g)) (n : ℕ), degL L = n → degL L' = n → (∀ p ∈ L, IsCusp p.2) →
    (∀ p ∈ L', IsCusp p.2) → (¬ L.Perm L' → ip (hcL L n) (hcL L' n) = 0) ∧
      (L.Perm L' → L.Nodup → ip (hcL L n) (hcL L' n) = 1) := by
  intro L'
  induction L' with
  | nil =>
    intro L n hL hL' hc _
    have hn : n = 0 := by rw [← hL']; rfl
    subst hn
    have := eq_nil_of_degL L hL hc
    subst this
    exact ⟨fun h => absurd (List.Perm.refl _) h, fun _ _ => ip_triv⟩
  | cons q M ih =>
    intro L n hL hL' hc hc'
    obtain ⟨a, ψ⟩ := q
    rw [degL_cons] at hL'
    dsimp only at hL'
    subst hL'
    have hψ : IsCusp ψ := hc' ⟨a, ψ⟩ (by simp)
    have hcM : ∀ p ∈ M, IsCusp p.2 := fun p hp => hc' p (by simp [hp])
    have hclass : IsClass (hcL L (a + degL M)) :=
      isClass_of_isChar (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant g L L _ hL.symm (fun p hp => isChar_of_isCusp (hc p hp))).1
    have key : ip (hcL L (a + degL M)) (hcL (⟨a, ψ⟩ :: M) (a + degL M)) =
        ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ i ∈ I, (L.get i).1 = a),
          ip (hcL ((I.sort (· ≤ ·)).map L.get) a) ψ *
            ip (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) (degL M)) (hcL M (degL M)) := by
      rw [hcL_cons]
      show ip _ (hcT a (degL M) (fun x y => ψ x * hcL M (degL M) y) _) = _
      rw [GlobalTheory.T.harishChandra_frobenius_reciprocity g a (degL M) _ rfl _ _ hclass]
      have hres := GlobalTheory.T.harishChandraRestriction_cuspidal_product_sum_subsets g L a (degL M) hL hc
      simp only [hres]
      rw [ip_sum_left]
      refine Finset.sum_congr rfl fun I _ => ?_
      exact ip_prod _ _ _ _
    have hrest : ∀ i : Fin L.length, L.get i = ⟨a, ψ⟩ →
        (L.Perm (⟨a, ψ⟩ :: ((({i} : Finset _)ᶜ.sort (· ≤ ·)).map L.get))) ∧
        degL ((({i} : Finset _)ᶜ.sort (· ≤ ·)).map L.get) = degL M := by
      intro i hi
      have hp := perm_split L {i}
      rw [Finset.sort_singleton, List.map_singleton, hi, List.singleton_append] at hp
      refine ⟨hp.symm, ?_⟩
      have := degL_perm hp
      rw [degL_cons, hL] at this
      dsimp only at this
      omega
    have hcRest : ∀ I : Finset (Fin L.length), ∀ p ∈ (Iᶜ.sort (· ≤ ·)).map L.get, IsCusp p.2 :=
      fun I p hp => hc p (mem_sort_map hp)
    refine ⟨fun hperm => ?_, fun hperm hnd => ?_⟩
    · rw [key]
      refine Finset.sum_eq_zero fun I hI => ?_
      rw [Finset.mem_filter] at hI
      rw [ip_sub_cusp L hc a ψ hψ I hI.2]
      split_ifs with hex
      · obtain ⟨i, rfl, hi⟩ := hex
        obtain ⟨hp, hd⟩ := hrest i hi
        rw [(ih _ _ hd rfl (hcRest _) hcM).1 (fun h => hperm (hp.trans (h.cons _))), mul_zero]
      · rw [zero_mul]
    · rw [key]
      have hq : (⟨a, ψ⟩ : Pc g) ∈ L := hperm.symm.subset (by simp)
      obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.1 hq
      have hmem : ({i₀} : Finset (Fin L.length)) ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter
          (fun I => ∑ i ∈ I, (L.get i).1 = a) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_singleton, hi₀]
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · rw [ip_sub_cusp L hc a ψ hψ _ (Finset.mem_filter.1 hmem).2, if_pos ⟨i₀, rfl, hi₀⟩, one_mul]
        obtain ⟨hp, hd⟩ := hrest i₀ hi₀
        have hp' : ((({i₀} : Finset _)ᶜ.sort (· ≤ ·)).map L.get).Perm M := (hp.symm.trans hperm).cons_inv
        have hnd' := (List.nodup_cons.1 (hp.nodup_iff.1 hnd)).2
        exact (ih _ _ hd rfl (hcRest _) hcM).2 hp' hnd'
      · intro I hI hne
        rw [ip_sub_cusp L hc a ψ hψ I (Finset.mem_filter.1 hI).2]
        split_ifs with hex
        · obtain ⟨i, rfl, hi⟩ := hex
          exact absurd (by rw [(List.Nodup.get_inj_iff hnd).1 (hi.trans hi₀.symm)]) hne
        · rw [zero_mul]

end
end GlobalTheory.GLq.IpCuspProd

namespace GlobalTheory.GLq.IpCuspProd

/- English proof (translation)
Introduce `g _ L L' n hL hL' hc hc'`. Conclude with `⟨(finiteRing_sq_sub_mul_sq_eq_of_card L' L n hL hL' hc hc').1, fun hnd => (finiteRing_sq_sub_mul_sq_eq_of_card L L n hL hL hc hc).2 (List.Perm.refl _) hnd⟩`.
-/
theorem ip_hcL_cusp : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), degL L = n → degL L' = n →
    (∀ p ∈ L, IsCusp p.2) → (∀ p ∈ L', IsCusp p.2) →
    (¬ L.Perm L' → ip (hcL L n) (hcL L' n) = 0) ∧ (L.Nodup → ip (hcL L n) (hcL L n) = 1) := by
  intro g _ L L' n hL hL' hc hc'
  exact ⟨(finiteRing_sq_sub_mul_sq_eq_of_card L' L n hL hL' hc hc').1, fun hnd => (finiteRing_sq_sub_mul_sq_eq_of_card L L n hL hL hc hc).2 (List.Perm.refl _) hnd⟩

end GlobalTheory.GLq.IpCuspProd
