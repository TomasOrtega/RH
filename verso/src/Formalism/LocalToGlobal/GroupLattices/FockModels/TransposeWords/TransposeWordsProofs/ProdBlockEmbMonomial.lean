import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

section general

variable {σ R : Type*} [CommRing R]

/- English proof (translation)
Unfold `fockR`. Apply `Finset.sum_subset h` to reduce the goal to its premises. Introduce `m _ hm`. Simplify using `[MvPolynomial.notMem_support_iff.mp hm]`.
-/
lemma fockR_eq_sum (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  apply Finset.sum_subset h
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.mp hm]

/- English proof (translation)
Rewrite using `[fockR_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, fockR_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma fockR_symm (f g : MvPolynomial σ R) : fockR f g = fockR g f := by
  classical
  rw [fockR_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    fockR_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/- English proof (translation)
Rewrite using `[fockR_eq_sum _ _ (f.support ∪ f'.support) MvPolynomial.support_add, fockR_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left, fockR_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma fockR_add_left (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [fockR_eq_sum _ _ (f.support ∪ f'.support) MvPolynomial.support_add,
    fockR_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    fockR_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_add]; ring

/- English proof (translation)
Rewrite using `[fockR_eq_sum _ _ f.support (MvPolynomial.support_smul), fockR, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma fockR_smul_left (c : R) (f g : MvPolynomial σ R) :
    fockR (c • f) g = c * fockR f g := by
  classical
  rw [fockR_eq_sum _ _ f.support (MvPolynomial.support_smul), fockR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_smul, smul_eq_mul]; ring

/- English proof (translation)
Rewrite using `[fockR_symm, fockR_add_left, fockR_symm g, fockR_symm g']`.
-/
lemma fockR_add_right (f g g' : MvPolynomial σ R) :
    fockR f (g + g') = fockR f g + fockR f g' := by
  rw [fockR_symm, fockR_add_left, fockR_symm g, fockR_symm g']

/- English proof (translation)
Rewrite using `[fockR_symm, fockR_smul_left, fockR_symm g]`.
-/
lemma fockR_smul_right (c : R) (f g : MvPolynomial σ R) :
    fockR f (c • g) = c * fockR f g := by
  rw [fockR_symm, fockR_smul_left, fockR_symm g]

/- English proof (translation)
Simplify using `[fockR]`.
-/
lemma fockR_zero_left (g : MvPolynomial σ R) : fockR 0 g = 0 := by
  simp [fockR]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp [fockR_zero_left]`. Consider the case `insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add_left, ih]`.
-/
lemma fockR_sum_left {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ t, f i) g = ∑ i ∈ t, fockR (f i) g := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fockR_zero_left]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add_left, ih]

/- English proof (translation)
Rewrite using `[fockR_symm, fockR_sum_left]`. Conclude with `Finset.sum_congr rfl fun i _ => fockR_symm _ _`.
-/
lemma fockR_sum_right {ι : Type*} (t : Finset ι) (f : MvPolynomial σ R) (g : ι → MvPolynomial σ R) :
    fockR f (∑ i ∈ t, g i) = ∑ i ∈ t, fockR f (g i) := by
  rw [fockR_symm, fockR_sum_left]
  exact Finset.sum_congr rfl fun i _ => fockR_symm _ _

/- English proof (translation)
Rewrite using `[fockR_eq_sum _ _ {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial]`. Distinguish the cases in `h : m = m'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : ¬ m' = m` using `fun e => h e.symm`.

Simplify using `[h, h']`.
-/
lemma fockR_monomial [DecidableEq (σ →₀ ℕ)] (m m' : σ →₀ ℕ) (a b : R) :
    fockR (monomial m a) (monomial m' b) =
      if m = m' then a * b * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) else 0 := by
  classical
  rw [fockR_eq_sum _ _ {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial]
  by_cases h : m = m'
  · subst h; simp
  · have h' : ¬ m' = m := fun e => h e.symm
    simp [h, h']

/- English proof (translation)
Rewrite using `[fockR_eq_sum _ _ f.support (support_map_subset φ f), fockR, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [coeff_map, map_mul, map_natCast]`.
-/
lemma fockR_map {S : Type*} [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R) :
    fockR (map φ f) (map φ g) = φ (fockR f g) := by
  rw [fockR_eq_sum _ _ f.support (support_map_subset φ f), fockR, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_map, map_mul, map_natCast]

end general

section block

variable {K S : Type*} [CommRing K] [Fintype S] {k n : ℕ}

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i t hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul]`.
-/
lemma prod_monomial_eq {ι τ : Type*} (t : Finset ι) (e : ι → τ →₀ ℕ) (a : ι → K) :
    ∏ i ∈ t, monomial (e i) (a i) = monomial (∑ i ∈ t, e i) (∏ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul]

def glue (p : S → (Fin k × Fin n →₀ ℕ)) : S × (Fin k × Fin n) →₀ ℕ :=
  ∑ t, (p t).mapDomain (Prod.mk t)

/- English proof (translation)
Unfold `glue`. Rewrite using `[Finsupp.finsetSum_apply, Finset.sum_eq_single s]`. Conclude with `Finsupp.mapDomain_apply (Prod.mk_right_injective s) _ _`. Introduce `t _ hts`. Apply `Finsupp.mapDomain_of_notMem_range` to reduce the goal to its premises.

Introduce and unpack `⟨w, hw⟩`. Conclude with `hts (congrArg Prod.fst hw)`. Simplify using the standard rewrite rules.
-/
lemma glue_apply (p : S → (Fin k × Fin n →₀ ℕ)) (s : S) (v : Fin k × Fin n) :
    glue p (s, v) = p s v := by
  classical
  unfold glue
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply (Prod.mk_right_injective s) _ _
  · intro t _ hts
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨w, hw⟩
    exact hts (congrArg Prod.fst hw)
  · simp

/- English proof (translation)
Introduce `p q h` and use `funext fun s => Finsupp.ext fun v => by rw [← glue_apply p, h, glue_apply]`.
-/
lemma glue_injective : Function.Injective (glue (S := S) (k := k) (n := n)) := fun p q h =>
  funext fun s => Finsupp.ext fun v => by rw [← glue_apply p, h, glue_apply]

/- English proof (translation)
Apply `Finset.prod_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `x _ hx`. Simplify using `[Finsupp.notMem_support_iff.mp hx]`.
-/
lemma fact_univ {τ : Type*} [Fintype τ] (m : τ →₀ ℕ) :
    ∏ x ∈ m.support, (m x).factorial = ∏ x, (m x).factorial := by
  apply Finset.prod_subset (Finset.subset_univ _)
  intro x _ hx
  simp [Finsupp.notMem_support_iff.mp hx]

/- English proof (translation)
Rewrite using `[fact_univ, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[fact_univ]`. Conclude with `Finset.prod_congr rfl fun v _ => by rw [glue_apply]`.
-/
lemma glue_fact (p : S → (Fin k × Fin n →₀ ℕ)) :
    ∏ x ∈ (glue p).support, (glue p x).factorial = ∏ s, ∏ v ∈ (p s).support, (p s v).factorial := by
  rw [fact_univ, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [fact_univ]
  exact Finset.prod_congr rfl fun v _ => by rw [glue_apply]

/- English proof (translation)
Simplify using `only [blockEmb, rename_monomial]`. Conclude with `prod_monomial_eq _ _ _`.
-/
lemma prod_blockEmb_monomial (p : S → (Fin k × Fin n →₀ ℕ)) (a : S → K) :
    ∏ s, blockEmb K s (monomial (p s) (a s)) = monomial (glue p) (∏ s, a s) := by
  simp only [blockEmb, rename_monomial]
  exact prod_monomial_eq _ _ _

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [(F s).as_sum]`. Rewrite using `[map_sum]`. Use `_ = ∑ p ∈ Fintype.piFinset (fun s => (F s).support), ∏ s, blockEmb K s (monomial (p s) (coeff (p s) (F s))) := Finset.prod_univ_sum _ _`.

Use `_ = _ := Finset.sum_congr rfl fun p _ => prod_blockEmb_monomial _ _`.
-/
lemma prod_blockEmb_expand [DecidableEq S] (F : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (F s) = ∑ p ∈ Fintype.piFinset (fun s => (F s).support),
      monomial (glue p) (∏ s, coeff (p s) (F s)) := by
  calc ∏ s, blockEmb K s (F s)
      = ∏ s, ∑ m ∈ (F s).support, blockEmb K s (monomial m (coeff m (F s))) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        conv_lhs => rw [(F s).as_sum]
        rw [map_sum]
    _ = ∑ p ∈ Fintype.piFinset (fun s => (F s).support),
          ∏ s, blockEmb K s (monomial (p s) (coeff (p s) (F s))) := Finset.prod_univ_sum _ _
    _ = _ := Finset.sum_congr rfl fun p _ => prod_blockEmb_monomial _ _

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum, g.as_sum]`. Rewrite using `[fockR_sum_left]`. Conclude with `Finset.sum_congr rfl fun m _ => fockR_sum_right _ _ _`.
-/
lemma fockR_expand {τ : Type*} (f g : MvPolynomial τ K) :
    fockR f g = ∑ m ∈ f.support, ∑ m' ∈ g.support,
      fockR (monomial m (coeff m f)) (monomial m' (coeff m' g)) := by
  conv_lhs => rw [f.as_sum, g.as_sum]
  rw [fockR_sum_left]
  exact Finset.sum_congr rfl fun m _ => fockR_sum_right _ _ _

/- English proof (translation)
Rewrite using `[prod_blockEmb_expand F, prod_blockEmb_expand G, fockR_sum_left]`. Repeatedly rewrite using `[fockR_sum_right, fockR_expand (F _) (G _)]`. Rewrite using `[Finset.prod_univ_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_univ_sum]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[fockR_monomial]`. Distinguish the cases in `h : p = q`. Substitute `h` using the available equality. Simplify using `only [if_true, glue_fact, Finset.prod_mul_distrib, Nat.cast_prod]`.

Establish `h' : glue p ≠ glue q` using `fun e => h (glue_injective e)`. Rewrite using `[if_neg h']`. Take `⟨s, hs⟩` from `Function.ne_iff.mp h`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)).symm`.
-/
theorem fockR_block (F G : S → MvPolynomial (Fin k × Fin n) K) :
    fockR (∏ s, blockEmb K s (F s)) (∏ s, blockEmb K s (G s)) = ∏ s, fockR (F s) (G s) := by
  classical
  rw [prod_blockEmb_expand F, prod_blockEmb_expand G, fockR_sum_left]
  simp_rw [fockR_sum_right, fockR_expand (F _) (G _)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [fockR_monomial]
  by_cases h : p = q
  · subst h
    simp only [if_true, glue_fact, Finset.prod_mul_distrib, Nat.cast_prod]
  · have h' : glue p ≠ glue q := fun e => h (glue_injective e)
    rw [if_neg h']
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)).symm

end block

/- English proof (translation)
Establish `hne : f.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `h`. Conclude with `hf (MvPolynomial.support_eq_empty.mp h)`. Unfold `fockR`.

Use `Finset.sum_pos (fun m hm => ?_) hne` and prove the remaining obligations. Establish `h1 : 0 < f.coeff m * f.coeff m` using `mul_self_pos.mpr (MvPolynomial.mem_support_iff.mp hm)`. Establish `h2 : (0 : ℤ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℤ)`. Conclude with `Finset.prod_pos fun k _ => Nat.factorial_pos _` after adjusting the coercions. Conclude with `mul_pos h1 h2`.
-/
lemma fockR_int_self_pos {σ : Type*} (f : MvPolynomial σ ℤ) (hf : f ≠ 0) : 0 < fockR f f := by
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; exact hf (MvPolynomial.support_eq_empty.mp h)
  unfold fockR
  refine Finset.sum_pos (fun m hm => ?_) hne
  have h1 : 0 < f.coeff m * f.coeff m := mul_self_pos.mpr (MvPolynomial.mem_support_iff.mp hm)
  have h2 : (0 : ℤ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℤ) := by
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  exact mul_pos h1 h2

/- English proof (translation)
Establish `pos : 0 < fockR (hw ℤ hn ν) (hw ℤ hn ν)` using `fockR_int_self_pos _ (hwNe ℤ r n hn ν)`. Use `⟨(fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat, by omega, fun R _ => ?_⟩` and prove the remaining obligations. Rewrite using `[← lclosedeq_hw_map (Int.castRingHom R) hn ν, fockR_map]`. Establish `e : (((fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat : ℕ) : ℤ) = fockR (hw ℤ hn ν) (hw ℤ hn ν)` using `Int.toNat_of_nonneg pos.le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fockR_hw_norm (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) : ∃ N : ℕ, 0 < N ∧
    ∀ (R : Type) [CommRing R], fockR (hw R hn ν) (hw R hn ν) = (N : R) := by
  have pos : 0 < fockR (hw ℤ hn ν) (hw ℤ hn ν) := fockR_int_self_pos _ (hwNe ℤ r n hn ν)
  refine ⟨(fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat, by omega, fun R _ => ?_⟩
  rw [← lclosedeq_hw_map (Int.castRingHom R) hn ν, fockR_map]
  have e : (((fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat : ℕ) : ℤ) = fockR (hw ℤ hn ν) (hw ℤ hn ν) :=
    Int.toNat_of_nonneg pos.le
  calc (Int.castRingHom R) (fockR (hw ℤ hn ν) (hw ℤ hn ν))
      = (Int.castRingHom R) (((fockR (hw ℤ hn ν) (hw ℤ hn ν)).toNat : ℕ) : ℤ) := by rw [e]
    _ = _ := by rw [eq_intCast, Int.cast_natCast]

/- English proof (translation)
Introduce `_ _ _ f f' g a` and use `⟨fockR_add_left f f' g, fockR_smul_left a f g, fockR_symm f g⟩`.
-/
theorem fock_pairing_bilinear : FockRBilin := fun _ _ _ f f' g a =>
  ⟨fockR_add_left f f' g, fockR_smul_left a f g, fockR_symm f g⟩

/- English proof (translation)
Introduce `_ _ _ _ _ φ f g` and use `fockR_map φ f g`.
-/
theorem fock_pairing_map : FockRMap := fun _ _ _ _ _ φ f g => fockR_map φ f g

/- English proof (translation)
Unfold `FockRMonomial`. Use `intros`. Use `split_ifs with h`. Rewrite using `[fockR_monomial, if_pos h]`. Rewrite using `[fockR_monomial, if_neg h]`.
-/
theorem fock_pairing_monomial : FockRMonomial := by
  unfold FockRMonomial
  intros
  classical
  split_ifs with h
  · rw [fockR_monomial, if_pos h]
  · rw [fockR_monomial, if_neg h]

/- English proof (translation)
Introduce `_ _ _ _ _ _ F G` and use `fockR_block F G`.
-/
theorem fock_pairing_block : FockRBlock := fun _ _ _ _ _ _ F G => fockR_block F G

/- English proof (translation)
The claim follows from `fockR_hw_norm`.
-/
theorem highest_weight_norm : HWNorm := fockR_hw_norm

end Formalism.L2.G.Model.TS
