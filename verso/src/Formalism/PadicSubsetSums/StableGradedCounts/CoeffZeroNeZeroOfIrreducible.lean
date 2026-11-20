import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
import Formalism.PadicSubsetSums.StableGradedCounts.IRRFrobOrbitIrred
import Formalism.PadicSubsetSums.StableGradedCounts.IRRSamePartCount
import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight

open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section roots

variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]

/- English proof (translation)
Establish `key : ∀ y : L, aeval y f = 0 → aeval (y ^ Fintype.card K) f = 0`. Introduce `y hy`. Rewrite using `[← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, hy, zero_pow Fintype.card_ne_zero]`. Proceed by induction on `n with`. Consider the case `zero => simpa using hx`.

Consider the case `succ n ih`. Rewrite using `[pow_succ, pow_mul]`. Conclude with `key _ ih`.
-/
theorem root_frob {f : K[X]} (n : ℕ) {x : L} (hx : aeval x f = 0) :
    aeval (x ^ Fintype.card K ^ n) f = 0 := by
  have key : ∀ y : L, aeval y f = 0 → aeval (y ^ Fintype.card K) f = 0 := by
    intro y hy
    rw [← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, hy, zero_pow Fintype.card_ne_zero]
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ, pow_mul]
    exact key _ ih

/- English proof (translation)
Establish `h` using `(frobenius_orbit_irreducible K L f hm hi).1.2`. Establish `mem : ∀ z : L, aeval z f = 0 → z ∈ (f.aroots L).toFinset`. Introduce `z hz`. Rewrite using `[Multiset.mem_toFinset, mem_aroots]`. Conclude with `⟨hi.ne_zero, hz⟩`.

Take `⟨n, hn⟩` from `h x (by convert mem x hx) y (by convert mem y hy)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn, pow_iterate]`.
-/
theorem root_conj {f : K[X]} (hm : f.Monic) (hi : Irreducible f) {x y : L} (hx : aeval x f = 0)
    (hy : aeval y f = 0) : ∃ n : ℕ, y = x ^ Fintype.card K ^ n := by
  classical
  have h := (frobenius_orbit_irreducible K L f hm hi).1.2
  have mem : ∀ z : L, aeval z f = 0 → z ∈ (f.aroots L).toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_aroots]
    exact ⟨hi.ne_zero, hz⟩
  obtain ⟨n, hn⟩ := h x (by convert mem x hx) y (by convert mem y hy)
  refine ⟨n, ?_⟩
  rw [← hn, pow_iterate]

/- English proof (translation)
Establish `hxi : IsIntegral K x` using `(show IsAlgebraic K x from ⟨f, hi.ne_zero, hx⟩).isIntegral`. Establish `hass` using `(minpoly.irreducible hxi).associated_of_dvd hi (minpoly.dvd K x hx)`. Establish `hdeg : (minpoly K x).natDegree = f.natDegree` using `Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hass)`. Use `haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hxi`. Use `haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K`.

Use `letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _`. Establish `hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ f.natDegree`. Rewrite using `[Module.card_eq_pow_finrank (K := K) (V := IntermediateField.adjoin K {x}), IntermediateField.adjoin.finrank hxi, hdeg]`. Establish `h` using `FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x})`. Rewrite `h` using `[hcard]`.

Simplify using `using congrArg Subtype.val h`.
-/
theorem root_pow_card {f : K[X]} (hi : Irreducible f) {x : L} (hx : aeval x f = 0) :
    x ^ Fintype.card K ^ f.natDegree = x := by
  classical
  have hxi : IsIntegral K x := (show IsAlgebraic K x from ⟨f, hi.ne_zero, hx⟩).isIntegral
  have hass := (minpoly.irreducible hxi).associated_of_dvd hi (minpoly.dvd K x hx)
  have hdeg : (minpoly K x).natDegree = f.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hass)
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hxi
  haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
  letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ f.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K) (V := IntermediateField.adjoin K {x}),
      IntermediateField.adjoin.finrank hxi, hdeg]
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x})
  rw [hcard] at h
  simpa using congrArg Subtype.val h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Nat.mul_succ, pow_add, pow_mul, ih, root_pow_card hi hx]`.
-/
theorem root_pow_card_mul {f : K[X]} (hi : Irreducible f) {x : L} (hx : aeval x f = 0) (k : ℕ) :
    x ^ Fintype.card K ^ (f.natDegree * k) = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, root_pow_card hi hx]

/- English proof (translation)
Introduce `h`. Rewrite `hx` using `[h, ← Polynomial.coeff_zero_eq_aeval_zero']`. Conclude with `h0 ((map_eq_zero_iff _ (algebraMap K L).injective).1 hx)`.
-/
theorem root_ne_zero {f : K[X]} (h0 : f.coeff 0 ≠ 0) {x : L} (hx : aeval x f = 0) : x ≠ 0 := by
  intro h
  rw [h, ← Polynomial.coeff_zero_eq_aeval_zero'] at hx
  exact h0 ((map_eq_zero_iff _ (algebraMap K L).injective).1 hx)

/- English proof (translation)
Introduce `h0`. Establish `hX : (X : K[X]) ∣ f` using `Polynomial.X_dvd_iff.2 h0`. Establish `hass` using `Polynomial.irreducible_X.associated_of_dvd hi hX`. Establish `hdeg` using `Polynomial.degree_eq_degree_of_associated hass`. Rewrite `hdeg` using `[Polynomial.degree_X]`.

Establish `: f.natDegree = 1` using `Polynomial.natDegree_eq_of_degree_eq_some hdeg.symm`. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_zero_ne_zero_of_irreducible {f : K[X]} (hi : Irreducible f) (hd : 2 ≤ f.natDegree) :
    f.coeff 0 ≠ 0 := by
  intro h0
  have hX : (X : K[X]) ∣ f := Polynomial.X_dvd_iff.2 h0
  have hass := Polynomial.irreducible_X.associated_of_dvd hi hX
  have hdeg := Polynomial.degree_eq_degree_of_associated hass
  rw [Polynomial.degree_X] at hdeg
  have : f.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg.symm
  omega

/- English proof (translation)
Establish `hx0 : x ≠ 0` using `root_ne_zero h0 hx`. Establish `h1` using `root_pow_card hi hx`. Establish `hpos : 1 ≤ Fintype.card K ^ f.natDegree` using `Nat.one_le_pow _ _ Fintype.card_pos`. Establish `e : x ^ Fintype.card K ^ f.natDegree = x ^ (Fintype.card K ^ f.natDegree - 1) * x`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hpos]`.

Rewrite `h1` using `[e]`. Use `mul_right_cancel₀ hx0 (h1.trans (one_mul x).symm)` as an intermediate fact. Conclude with `this`.
-/
theorem root_pow_sub_one {f : K[X]} (hi : Irreducible f) (h0 : f.coeff 0 ≠ 0) {x : L}
    (hx : aeval x f = 0) : x ^ (Fintype.card K ^ f.natDegree - 1) = 1 := by
  have hx0 : x ≠ 0 := root_ne_zero h0 hx
  have h1 := root_pow_card hi hx
  have hpos : 1 ≤ Fintype.card K ^ f.natDegree := Nat.one_le_pow _ _ Fintype.card_pos
  have e : x ^ Fintype.card K ^ f.natDegree = x ^ (Fintype.card K ^ f.natDegree - 1) * x := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  rw [e] at h1
  have := mul_right_cancel₀ hx0 (h1.trans (one_mul x).symm)
  exact this

/- English proof (translation)
Apply `monicOf_injective` to reduce the goal to its premises. Rewrite using `[minpoly.eq_of_irreducible_of_monic ha hxa (monicOf_monic a), minpoly.eq_of_irreducible_of_monic hb hxb (monicOf_monic b)]`.
-/
theorem eq_of_common_root {δ : ℕ} {a b : Fin δ → K} (ha : Irreducible (monicOf a))
    (hb : Irreducible (monicOf b)) {x : L} (hxa : aeval x (monicOf a) = 0)
    (hxb : aeval x (monicOf b) = 0) : a = b := by
  apply monicOf_injective
  rw [minpoly.eq_of_irreducible_of_monic ha hxa (monicOf_monic a),
    minpoly.eq_of_irreducible_of_monic hb hxb (monicOf_monic b)]

/- English proof (translation)
Use `choose! r hrS hr using h`. Use `Finset.card_le_card_of_injOn r (fun c hc => hrS c hc) ?_` and prove the remaining obligations. Introduce `a ha b hb hab`. Conclude with `eq_of_common_root (hF a ha) (hF b hb) (hr a ha) (hab ▸ hr b hb)`.
-/
theorem card_le_of_root_mem {δ : ℕ} (F : Finset (Fin δ → K))
    (hF : ∀ c ∈ F, Irreducible (monicOf c)) (S : Finset L)
    (h : ∀ c ∈ F, ∃ x ∈ S, aeval x (monicOf c) = 0) : F.card ≤ S.card := by
  classical
  choose! r hrS hr using h
  refine Finset.card_le_card_of_injOn r (fun c hc => hrS c hc) ?_
  intro a ha b hb hab
  exact eq_of_common_root (hF a ha) (hF b hb) (hr a ha) (hab ▸ hr b hb)

/- English proof (translation)
Establish `hsub : F.biUnion (fun c => ((monicOf c).aroots L).toFinset) ⊆ S`. Introduce `x hx`. Take `⟨c, hc, hxc⟩` from `Finset.mem_biUnion.mp hx`. Rewrite `hxc` using `[Multiset.mem_toFinset, mem_aroots]`. Conclude with `h c hc x hxc.2`.

Establish `hdisj : (F : Set (Fin δ → K)).PairwiseDisjoint (fun c => ((monicOf c).aroots L).toFinset)`. Introduce `a ha b hb hab`. Rewrite using `[Function.onFun, Finset.disjoint_left]`. Introduce `x hxa hxb`. Rewrite `hxa`, `hxb` using `[Multiset.mem_toFinset, mem_aroots]`.

Conclude with `hab (eq_of_common_root (hF a ha) (hF b hb) hxa.2 hxb.2)`. Establish `hcard : ∀ c ∈ F, (((monicOf c).aroots L).toFinset).card = δ`. Introduce `c hc`. Use `(frobenius_orbit_irreducible K L (monicOf c) (monicOf_monic c) (hF c hc)).2` as an intermediate fact. Rewrite `this` using `[monicOf_natDegree]`.

Use `this` and compare the differences between its conclusion and the goal. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]`. Use `_ = (F.biUnion (fun c => ((monicOf c).aroots L).toFinset)).card := (Finset.card_biUnion hdisj).symm`. Use `_ ≤ S.card := Finset.card_le_card hsub`.
-/
theorem mul_card_le_of_roots_mem {δ : ℕ} (F : Finset (Fin δ → K))
    (hF : ∀ c ∈ F, Irreducible (monicOf c)) (S : Finset L)
    (h : ∀ c ∈ F, ∀ x : L, aeval x (monicOf c) = 0 → x ∈ S) : δ * F.card ≤ S.card := by
  classical
  have hsub : F.biUnion (fun c => ((monicOf c).aroots L).toFinset) ⊆ S := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
    rw [Multiset.mem_toFinset, mem_aroots] at hxc
    exact h c hc x hxc.2
  have hdisj : (F : Set (Fin δ → K)).PairwiseDisjoint
      (fun c => ((monicOf c).aroots L).toFinset) := by
    intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxa hxb
    rw [Multiset.mem_toFinset, mem_aroots] at hxa hxb
    exact hab (eq_of_common_root (hF a ha) (hF b hb) hxa.2 hxb.2)
  have hcard : ∀ c ∈ F, (((monicOf c).aroots L).toFinset).card = δ := by
    intro c hc
    have := (frobenius_orbit_irreducible K L (monicOf c) (monicOf_monic c) (hF c hc)).2
    rw [monicOf_natDegree] at this
    convert this
  calc δ * F.card = ∑ c ∈ F, (((monicOf c).aroots L).toFinset).card := by
        rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = (F.biUnion (fun c => ((monicOf c).aroots L).toFinset)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ S.card := Finset.card_le_card hsub

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Unfold `Polynomial.nthRootsFinset`. Use `Multiset.toFinset_card_le (nthRoots m (1 : L))` and compare the differences between its conclusion and the goal. Use `_ ≤ m := Polynomial.card_nthRoots m 1`.
-/
theorem card_nthRootsFinset_le (m : ℕ) : (nthRootsFinset m (1 : L)).card ≤ m := by
  classical
  calc (nthRootsFinset m (1 : L)).card ≤ (nthRoots m (1 : L)).card := by
        unfold Polynomial.nthRootsFinset
        convert Multiset.toFinset_card_le (nthRoots m (1 : L))
    _ ≤ m := Polynomial.card_nthRoots m 1

end roots

/- English proof (translation)
Establish `hg0 : (0 : ℝ) ≤ g` using `Nat.cast_nonneg g`. Establish `h1 : ((l ^ v : ℕ) : ℝ) ^ 4 ≤ ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4`. Rewrite using `[← Real.rpow_natCast ((g : ℝ) ^ ((d : ℝ) / 4)) 4, ← Real.rpow_mul hg0]`. Establish `e : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = d` using `by push_cast; ring`. Rewrite using `[e, Real.rpow_natCast]`.

Establish `h2 : (l ^ v) ^ 4 ≤ g ^ d` using `by rw [← pow_mul, mul_comm]; exact hBB`. Conclude with `h2` after adjusting the coercions. Conclude with `(pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1`.
-/
theorem lpow_le_rpow_quarter {l v g d : ℕ} (hBB : l ^ (4 * v) ≤ g ^ d) :
    ((l ^ v : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4) := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have h1 : ((l ^ v : ℕ) : ℝ) ^ 4 ≤ ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 := by
    rw [← Real.rpow_natCast ((g : ℝ) ^ ((d : ℝ) / 4)) 4, ← Real.rpow_mul hg0]
    have e : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = d := by push_cast; ring
    rw [e, Real.rpow_natCast]
    have h2 : (l ^ v) ^ 4 ≤ g ^ d := by rw [← pow_mul, mul_comm]; exact hBB
    exact_mod_cast h2
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1

/- English proof (translation)
Introduce `K L _ _ _ _ _ δ l hl hδ hBB`. Establish `: Fact l.Prime` using `⟨hl⟩`. Use `set g := Fintype.card K with hgdef`. Establish `hg : 2 ≤ g` using `Fintype.one_lt_card`. Use `set n := g ^ δ - 1 with hn`.

Use `set v := padicValNat l n with hv`. Establish `hgd : 2 ≤ g ^ δ` using `hg.trans (Nat.le_self_pow (by omega) g)`. Establish `hn0 : n ≠ 0` using `by omega`. Establish `hg1 : (1 : ℝ) ≤ g` using `by exact_mod_cast (by omega : 1 ≤ g)`. Establish `hlv : ((l ^ v : ℕ) : ℝ) ≤ (g : ℝ) ^ ((δ : ℝ) / 4)` using `lpow_le_rpow_quarter hBB`.

Use `set B : ℝ := (g : ℝ) ^ ((δ : ℝ) / 2) * (g : ℝ) ^ ((δ : ℝ) / 4) with hB`. Use `set I := (Finset.range δ).filter (fun e => e ∣ δ) with hI`. Use `set T : ℕ → Finset L := fun e => nthRootsFinset ((g ^ e - 1) * l ^ v) (1 : L) with hT`. Establish `hmpos : ∀ e ∈ I, 0 < (g ^ e - 1) * l ^ v`. Introduce `e he`.

Simplify using `only [hI, Finset.mem_filter, Finset.mem_range] at he`. Establish `he1 : 1 ≤ e`. Break down `Nat.eq_zero_or_pos e with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Use `Nat.eq_zero_of_zero_dvd he.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Establish `hge : 2 ≤ g ^ e` using `hg.trans (Nat.le_self_pow (by omega) g)`. Conclude with `Nat.mul_pos (by omega) (pow_pos hl.pos _)`. Establish `hTe : ∀ e ∈ I, ((T e).card : ℝ) ≤ B`.

Introduce `e he`. Simplify using `only [hI, Finset.mem_filter, Finset.mem_range] at he`. Take `⟨hed, k, hk⟩` from `he`. Establish `h2e : 2 * e ≤ δ`. Establish `hk2 : 2 ≤ k`.

Assume the negation of the conclusion as `hlt`. Establish `: k = 0 ∨ k = 1` using `by omega`. Apply the tactic sequence `rcases this with rfl | rfl <;> omega`. Combine the equalities or inequalities in the displayed calculation. Establish `hc1 : (T e).card ≤ (g ^ e - 1) * l ^ v` using `card_nthRootsFinset_le _`.

Establish `hc2 : ((g ^ e - 1 : ℕ) : ℝ) ≤ (g : ℝ) ^ ((δ : ℝ) / 2)`. Establish `h4 : ((g ^ e - 1 : ℕ) : ℝ) ≤ (g : ℝ) ^ e`. Establish `: g ^ e - 1 ≤ g ^ e` using `Nat.sub_le _ _`. Conclude with `this` after adjusting the coercions. Use `h4.trans ?_` and prove the remaining obligations.

Rewrite using `[← Real.rpow_natCast]`. Apply `Real.rpow_le_rpow_of_exponent_le hg1` to reduce the goal to its premises. Establish `: ((2 * e : ℕ) : ℝ) ≤ (δ : ℝ)` using `by exact_mod_cast h2e`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Use `set F := (Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧ ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)) with hF`. Establish `hFirr : ∀ c ∈ F, Irreducible (monicOf c)` using `fun c hc => (Finset.mem_filter.mp hc).2.1`. Establish `hroots : ∀ c ∈ F, ∀ x : L, aeval x (monicOf c) = 0 → x ∈ I.biUnion T`. Introduce `c hc x' hx'`.

Take `⟨-, hirr, hninj⟩` from `Finset.mem_filter.mp hc`. Establish `hmon` using `monicOf_monic c`. Establish `hdeg : (monicOf c).natDegree = δ` using `monicOf_natDegree c`. Establish `hc0 : (monicOf c).coeff 0 ≠ 0` using `coeff_zero_ne_zero_of_irreducible hirr (by rw [hdeg]; exact hδ)`. Simplify using `only [Set.InjOn, not_forall] at hninj`.

Take `⟨x, hx, y, hy, hxy, hne⟩` from `hninj`. Establish `hx` using `(mem_rootSet.mp hx).2`. Establish `hy` using `(mem_rootSet.mp hy).2`. Take `⟨i, hi⟩` from `root_conj hmon hirr hx hy`. Take `⟨j, hj⟩` from `root_conj hmon hirr hx hx'`.

Establish `hxn : x ^ n = 1`. Use `root_pow_sub_one hirr hc0 hx` as an intermediate fact. Rewrite `this` using `[hdeg]`. Then use the resulting hypothesis. Establish `hxfin : IsOfFinOrder x` using `isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩`. Use `set z := primeToPart l x with hz`.

Establish `hzi : z ^ g ^ i = z`. Use `(prime_to_part_endomorphism L L l x x (powMonoidHom (g ^ i)) hl hxfin hxfin).2` as an intermediate fact. Simplify using `only [powMonoidHom_apply] at this`. Rewrite using `[hz, this, ← hi, ← hxy]`. Establish `hzn : z ^ n = 1`.

Rewrite using `[hz, primeToPart, ← pow_mul, mul_comm, pow_mul, hxn, one_pow]`. Establish `hz0 : z ≠ 0`. Introduce `h0`. Rewrite `hzn` using `[h0, zero_pow hn0]`. Conclude with `zero_ne_one hzn`.

Establish `hzi1 : z ^ (g ^ i - 1) = 1`. Establish `hpos : 0 < g ^ i` using `pow_pos (by omega) _`. Establish `: z ^ (g ^ i - 1) * z = 1 * z`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hpos, hzi, one_mul]`. Conclude with `mul_right_cancel₀ hz0 this`.

Use `set e := Nat.gcd i δ with he`. Establish `hze : z ^ (g ^ e - 1) = 1`. Rewrite using `[he, ← Nat.pow_sub_one_gcd_pow_sub_one]`. Conclude with `pow_gcd_eq_one.mpr ⟨hzi1, hzn⟩`. Establish `heδ : e ∣ δ` using `Nat.gcd_dvd_right i δ`.

Establish `helt : e < δ`. Use `lt_of_le_of_ne (Nat.le_of_dvd (by omega) heδ) ?_` and prove the remaining obligations. Introduce `h`. Establish `hdi : δ ∣ i` using `h ▸ Nat.gcd_dvd_left i δ`. Take `⟨k, hk⟩` from `hdi`.

Apply `hne` to reduce the goal to its premises. Use `root_pow_card_mul hirr hx k` as an intermediate fact. Rewrite `this` using `[hdeg, ← hk, ← hi]`. Conclude with `this.symm`. Establish `heI : e ∈ I`.

Simplify using `only [hI, Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨helt, heδ⟩`. Take `⟨_, a, ha⟩` from `prime_to_part_spec L l x hl hxfin`. Establish `h1 : (x ^ (g ^ e - 1)) ^ (l ^ a) = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, ha, ← pow_mul, mul_comm, pow_mul, hze, one_pow]`.

Establish `h2 : (x ^ (g ^ e - 1)) ^ n = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hxn, one_pow]`. Establish `h3` using `(lpow_order_iff hl hn0 _ h2).mp ⟨a, h1⟩`. Rewrite using `[Finset.mem_biUnion]`. Use `⟨e, heI, ?_⟩` and prove the remaining obligations.

Rewrite using `[hT]`. Simplify using `only`. Rewrite using `[mem_nthRootsFinset (hmpos e heI), hj, ← pow_mul, mul_comm, pow_mul, pow_mul, h3, one_pow]`. Establish `hcount` using `mul_card_le_of_roots_mem F hFirr (I.biUnion T) hroots`. Establish `hB0 : 0 ≤ B` using `by positivity`.

Establish `hIcard : (I.card : ℝ) ≤ δ`. Establish `: I.card ≤ δ` using `(Finset.card_filter_le _ _).trans (by simp)`. Conclude with `this` after adjusting the coercions. Establish `hS : ((I.biUnion T).card : ℝ) ≤ δ * B`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `Finset.card_biUnion_le` after adjusting the coercions. Use `_ = ∑ e ∈ I, ((T e).card : ℝ) := by push_cast; rfl`. Use `_ ≤ ∑ _e ∈ I, B := Finset.sum_le_sum hTe`. Use `_ = (I.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ δ * B := mul_le_mul_of_nonneg_right hIcard hB0`.

Establish `hδR : (0 : ℝ) < δ` using `by exact_mod_cast (by omega : 0 < δ)`. Establish `hfin : (δ : ℝ) * (F.card : ℝ) ≤ δ * B`. Use `le_trans ?_ hS` and prove the remaining obligations. Conclude with `hcount` after adjusting the coercions. Establish `hFB : (F.card : ℝ) ≤ B` using `le_of_mul_le_mul_left hfin hδR`.

Establish `hBeq : B = (g : ℝ) ^ (3 * (δ : ℝ) / 4)`. Rewrite using `[hB, ← Real.rpow_add (by linarith)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hBeq]`.

Conclude with `hFB`.
-/
theorem same_factor_count : SameFactorCount := by
  classical
  intro K L _ _ _ _ _ δ l hl hδ hBB
  have : Fact l.Prime := ⟨hl⟩
  set g := Fintype.card K with hgdef
  have hg : 2 ≤ g := Fintype.one_lt_card
  set n := g ^ δ - 1 with hn
  set v := padicValNat l n with hv
  have hgd : 2 ≤ g ^ δ := hg.trans (Nat.le_self_pow (by omega) g)
  have hn0 : n ≠ 0 := by omega
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hlv : ((l ^ v : ℕ) : ℝ) ≤ (g : ℝ) ^ ((δ : ℝ) / 4) := lpow_le_rpow_quarter hBB
  set B : ℝ := (g : ℝ) ^ ((δ : ℝ) / 2) * (g : ℝ) ^ ((δ : ℝ) / 4) with hB
  set I := (Finset.range δ).filter (fun e => e ∣ δ) with hI
  set T : ℕ → Finset L := fun e => nthRootsFinset ((g ^ e - 1) * l ^ v) (1 : L) with hT
  have hmpos : ∀ e ∈ I, 0 < (g ^ e - 1) * l ^ v := by
    intro e he
    simp only [hI, Finset.mem_filter, Finset.mem_range] at he
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; have := Nat.eq_zero_of_zero_dvd he.2; omega
      · exact h0
    have hge : 2 ≤ g ^ e := hg.trans (Nat.le_self_pow (by omega) g)
    exact Nat.mul_pos (by omega) (pow_pos hl.pos _)
  have hTe : ∀ e ∈ I, ((T e).card : ℝ) ≤ B := by
    intro e he
    simp only [hI, Finset.mem_filter, Finset.mem_range] at he
    obtain ⟨hed, k, hk⟩ := he
    have h2e : 2 * e ≤ δ := by
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have : k = 0 ∨ k = 1 := by omega
        rcases this with rfl | rfl <;> omega
      calc 2 * e = e * 2 := by ring
        _ ≤ e * k := Nat.mul_le_mul_left e hk2
        _ = δ := hk.symm
    have hc1 : (T e).card ≤ (g ^ e - 1) * l ^ v := card_nthRootsFinset_le _
    have hc2 : ((g ^ e - 1 : ℕ) : ℝ) ≤ (g : ℝ) ^ ((δ : ℝ) / 2) := by
      have h4 : ((g ^ e - 1 : ℕ) : ℝ) ≤ (g : ℝ) ^ e := by
        have : g ^ e - 1 ≤ g ^ e := Nat.sub_le _ _
        exact_mod_cast this
      refine h4.trans ?_
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hg1
      have : ((2 * e : ℕ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h2e
      push_cast at this
      linarith
    calc ((T e).card : ℝ) ≤ (((g ^ e - 1) * l ^ v : ℕ) : ℝ) := by exact_mod_cast hc1
      _ = ((g ^ e - 1 : ℕ) : ℝ) * ((l ^ v : ℕ) : ℝ) := by push_cast; ring
      _ ≤ B := mul_le_mul hc2 hlv (by positivity) (by positivity)
  set F := (Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)) with hF
  have hFirr : ∀ c ∈ F, Irreducible (monicOf c) := fun c hc => (Finset.mem_filter.mp hc).2.1
  have hroots : ∀ c ∈ F, ∀ x : L, aeval x (monicOf c) = 0 → x ∈ I.biUnion T := by
    intro c hc x' hx'
    obtain ⟨-, hirr, hninj⟩ := Finset.mem_filter.mp hc
    have hmon := monicOf_monic c
    have hdeg : (monicOf c).natDegree = δ := monicOf_natDegree c
    have hc0 : (monicOf c).coeff 0 ≠ 0 :=
      coeff_zero_ne_zero_of_irreducible hirr (by rw [hdeg]; exact hδ)
    simp only [Set.InjOn, not_forall] at hninj
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := hninj
    have hx := (mem_rootSet.mp hx).2
    have hy := (mem_rootSet.mp hy).2
    obtain ⟨i, hi⟩ := root_conj hmon hirr hx hy
    obtain ⟨j, hj⟩ := root_conj hmon hirr hx hx'
    have hxn : x ^ n = 1 := by
      have := root_pow_sub_one hirr hc0 hx
      rwa [hdeg] at this
    have hxfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩
    set z := primeToPart l x with hz
    have hzi : z ^ g ^ i = z := by
      have := (prime_to_part_endomorphism L L l x x (powMonoidHom (g ^ i)) hl hxfin hxfin).2
      simp only [powMonoidHom_apply] at this
      rw [hz, this, ← hi, ← hxy]
    have hzn : z ^ n = 1 := by
      rw [hz, primeToPart, ← pow_mul, mul_comm, pow_mul, hxn, one_pow]
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, zero_pow hn0] at hzn
      exact zero_ne_one hzn
    have hzi1 : z ^ (g ^ i - 1) = 1 := by
      have hpos : 0 < g ^ i := pow_pos (by omega) _
      have : z ^ (g ^ i - 1) * z = 1 * z := by
        rw [← pow_succ, Nat.sub_add_cancel hpos, hzi, one_mul]
      exact mul_right_cancel₀ hz0 this
    set e := Nat.gcd i δ with he
    have hze : z ^ (g ^ e - 1) = 1 := by
      rw [he, ← Nat.pow_sub_one_gcd_pow_sub_one]
      exact pow_gcd_eq_one.mpr ⟨hzi1, hzn⟩
    have heδ : e ∣ δ := Nat.gcd_dvd_right i δ
    have helt : e < δ := by
      refine lt_of_le_of_ne (Nat.le_of_dvd (by omega) heδ) ?_
      intro h
      have hdi : δ ∣ i := h ▸ Nat.gcd_dvd_left i δ
      obtain ⟨k, hk⟩ := hdi
      apply hne
      have := root_pow_card_mul hirr hx k
      rw [hdeg, ← hk, ← hi] at this
      exact this.symm
    have heI : e ∈ I := by
      simp only [hI, Finset.mem_filter, Finset.mem_range]; exact ⟨helt, heδ⟩
    obtain ⟨_, a, ha⟩ := prime_to_part_spec L l x hl hxfin
    have h1 : (x ^ (g ^ e - 1)) ^ (l ^ a) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ha, ← pow_mul, mul_comm, pow_mul, hze, one_pow]
    have h2 : (x ^ (g ^ e - 1)) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hxn, one_pow]
    have h3 := (lpow_order_iff hl hn0 _ h2).mp ⟨a, h1⟩
    rw [Finset.mem_biUnion]
    refine ⟨e, heI, ?_⟩
    rw [hT]
    simp only
    rw [mem_nthRootsFinset (hmpos e heI), hj, ← pow_mul, mul_comm, pow_mul, pow_mul, h3, one_pow]
  have hcount := mul_card_le_of_roots_mem F hFirr (I.biUnion T) hroots
  have hB0 : 0 ≤ B := by positivity
  have hIcard : (I.card : ℝ) ≤ δ := by
    have : I.card ≤ δ := (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hS : ((I.biUnion T).card : ℝ) ≤ δ * B := by
    calc ((I.biUnion T).card : ℝ) ≤ ((∑ e ∈ I, (T e).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ e ∈ I, ((T e).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _e ∈ I, B := Finset.sum_le_sum hTe
      _ = (I.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ δ * B := mul_le_mul_of_nonneg_right hIcard hB0
  have hδR : (0 : ℝ) < δ := by exact_mod_cast (by omega : 0 < δ)
  have hfin : (δ : ℝ) * (F.card : ℝ) ≤ δ * B := by
    refine le_trans ?_ hS
    exact_mod_cast hcount
  have hFB : (F.card : ℝ) ≤ B := le_of_mul_le_mul_left hfin hδR
  have hBeq : B = (g : ℝ) ^ (3 * (δ : ℝ) / 4) := by
    rw [hB, ← Real.rpow_add (by linarith)]
    congr 1
    ring
  rw [← hBeq]
  exact hFB

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
