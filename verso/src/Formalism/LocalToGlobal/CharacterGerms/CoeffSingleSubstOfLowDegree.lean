import Formalism.LocalToGlobal.CharacterGerms.AbstractGermZeroCondition
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace FormalGermZero

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

/- English proof (translation)
Rewrite using `[MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]`. Rewrite using `[finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `e he`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, e s ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `he (Finsupp.ext h)`. Rewrite using `[map_finsuppProd]`. Simplify using `only [map_pow, ha, Finsupp.prod]`.

Rewrite using `[Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]`.
-/
private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

/- English proof (translation)
Use `first`. Consider the case `exact Finsupp.degree_single c n`. Consider the case `simp [Finsupp.degree_single]`. Consider the case `simp [Finsupp.degree]`. Consider the case `(classical`.

Unfold `Finsupp.degree`. Apply the tactic sequence `by_cases h : n = 0 <;> simp [h])`.
-/
private theorem deg_single_lemma_0 {τ : Type} (c : τ) (n : ℕ) : Finsupp.degree (Finsupp.single c n) = n := by
  first
  | exact Finsupp.degree_single c n
  | simp [Finsupp.degree_single]
  | simp [Finsupp.degree]
  | (classical
     unfold Finsupp.degree
     by_cases h : n = 0 <;> simp [h])

/- English proof (translation)
Use `first`. Consider the case `exact (Finsupp.degree_eq_zero_iff d).mp h`. Consider the case `exact Finsupp.degree_eq_zero_iff.mp h`. Consider the case `simpa using h`.
-/
private theorem deg_zero_lemma_0 {τ : Type} (d : τ →₀ ℕ) (h : Finsupp.degree d = 0) : d = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff d).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h
  | simpa using h

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_mul]`. Use `Finset.sum_eq_zero (fun p hp => ?_)` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `hdeg` using `congrArg Finsupp.degree hp`. Rewrite `hdeg` using `[map_add, deg_single_lemma_0]`.

Break down `Nat.eq_zero_or_pos p.1.degree with h0 | h0` into its components or cases. Rewrite using `[deg_zero_lemma_0 p.1 h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]`. Establish `h1 : p.2.degree = 0` using `by omega`. Rewrite using `[deg_zero_lemma_0 p.2 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB, mul_zero]`.
-/
private theorem cs_mul_lemma {τ : Type} (A B : MvPowerSeries τ C) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (A * B) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg := congrArg Finsupp.degree hp
  rw [map_add, deg_single_lemma_0] at hdeg
  rcases Nat.eq_zero_or_pos p.1.degree with h0 | h0
  · rw [deg_zero_lemma_0 p.1 h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
  · have h1 : p.2.degree = 0 := by omega
    rw [deg_zero_lemma_0 p.2 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB, mul_zero]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, e s ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `he (Finsupp.ext h)`. Rewrite using `[map_finsuppProd]`.

Simplify using `only [map_pow, ha0, Finsupp.prod]`. Conclude with `Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)`.
-/
private theorem cs_prod_lemma_2 {σ τ : Type} (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : σ →₀ ℕ) (he : e ≠ 0) :
    MvPowerSeries.constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push_neg at h
    exact he (Finsupp.ext h)
  rw [map_finsuppProd]
  simp only [map_pow, ha0, Finsupp.prod]
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)

/- English proof (translation)
Establish `hne : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at he`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, e s ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne (Finsupp.ext h)`. Establish `hle : Finsupp.single s 1 ≤ e`. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `hsplit : e = Finsupp.single s 1 + (e - Finsupp.single s 1)` using `(add_tsub_cancel_of_le hle).symm`. Establish `hdeg : 1 ≤ (e - Finsupp.single s 1).degree`. Establish `h2` using `congrArg Finsupp.degree hsplit`. Rewrite `h2` using `[map_add, deg_single_lemma_0]`. Use linear arithmetic over natural numbers and integers.

Establish `hne' : e - Finsupp.single s 1 ≠ 0`. Introduce `h`. Rewrite `hdeg` using `[h]`. Simplify using `at hdeg`. Rewrite using `[hsplit, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (h := fun s n => a s ^ n) (pow_zero _), pow_one]`.

Conclude with `cs_mul_lemma _ _ (ha0 s) (cs_prod_lemma_2 a ha0 _ hne') c`.
-/
private theorem cs_prod_lemma_3 {σ τ : Type} (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (e : σ →₀ ℕ) (he : 2 ≤ e.degree) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (e.prod fun s n => a s ^ n) = 0 := by
  classical
  have hne : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finsupp.ext h)
  have hle : Finsupp.single s 1 ≤ e := by
    rw [Finsupp.single_le_iff]
    omega
  have hsplit : e = Finsupp.single s 1 + (e - Finsupp.single s 1) := (add_tsub_cancel_of_le hle).symm
  have hdeg : 1 ≤ (e - Finsupp.single s 1).degree := by
    have h2 := congrArg Finsupp.degree hsplit
    rw [map_add, deg_single_lemma_0] at h2
    omega
  have hne' : e - Finsupp.single s 1 ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  rw [hsplit, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun s n => a s ^ n) (pow_zero _), pow_one]
  exact cs_mul_lemma _ _ (ha0 s) (cs_prod_lemma_2 a ha0 _ hne') c

/- English proof (translation)
Establish `ha : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha0`. Rewrite using `[MvPowerSeries.coeff_subst ha]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `e`. Distinguish the cases in `he : e.degree < 2`.

Rewrite using `[hr e he, zero_smul]`. Rewrite using `[cs_prod_lemma_3 a ha0 e (by omega) c, smul_zero]`.
-/
theorem coeff_single_subst_of_low_degree {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (r : MvPowerSeries σ C)
    (hr : ∀ e : σ →₀ ℕ, e.degree < 2 → MvPowerSeries.coeff e r = 0) (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst a r) = 0 := by
  classical
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e.degree < 2
  · rw [hr e he, zero_smul]
  · rw [cs_prod_lemma_3 a ha0 e (by omega) c, smul_zero]

/- English proof (translation)
Establish `ha : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha0`. Establish `hr : ∀ e : σ →₀ ℕ, e.degree < 2 → MvPowerSeries.coeff e (f - MvPowerSeries.X i) = 0`. Introduce `e he`. Rewrite using `[map_sub, hf e (by omega), sub_self]`. Establish `hsplit : f = MvPowerSeries.X i + (f - MvPowerSeries.X i)` using `by ring`.

Rewrite using `[hsplit, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, map_add, coeff_single_subst_of_low_degree a ha0 _ hr c, add_zero]`.
-/
theorem coeff_single_subst_lin {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (i : σ)
    (hf : ∀ μ : σ →₀ ℕ, μ.degree ≤ 1 → MvPowerSeries.coeff μ f = MvPowerSeries.coeff μ (MvPowerSeries.X i))
    (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst a f) =
      MvPowerSeries.coeff (Finsupp.single c 1) (a i) := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hr : ∀ e : σ →₀ ℕ, e.degree < 2 → MvPowerSeries.coeff e (f - MvPowerSeries.X i) = 0 := by
    intro e he
    rw [map_sub, hf e (by omega), sub_self]
  have hsplit : f = MvPowerSeries.X i + (f - MvPowerSeries.X i) := by ring
  rw [hsplit, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, map_add,
    coeff_single_subst_of_low_degree a ha0 _ hr c, add_zero]

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)), map_zero]`. Rewrite using `[finsum_eq_single _ 0]`. Simplify using `[hf]`. Introduce `e he`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, e s ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `he (Finsupp.ext h)`. Simplify using `only [Pi.zero_apply, Finsupp.prod]`.

Rewrite using `[Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)]`. Simplify using the standard rewrite rules.
-/
theorem subst_zero_of_const {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (0 : σ → MvPowerSeries τ C) f = 0 := by
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)), map_zero]
  rw [finsum_eq_single _ 0]
  · simp [hf]
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    simp only [Pi.zero_apply, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)]
    simp

/- English proof (translation)
Rewrite using `[AbstractGermZero.intS_iff_alt]`. Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `AltInv.intC_one (v := V.v)`.

Conclude with `AltInv.intC_zero (v := V.v)`.
-/
theorem intS_X {V : VF C} {τ : Type} (c : τ) : IntS V (MvPowerSeries.X c : MvPowerSeries τ C) := by
  rw [AbstractGermZero.intS_iff_alt]
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact AltInv.intC_one (v := V.v)
  · exact AltInv.intC_zero (v := V.v)

/- English proof (translation)
Use `Finsupp.induction d ?_ ?_` and prove the remaining obligations. Simplify using `only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]`. Both sides reduce to the same expression. Introduce `a b f _ _ ih`. Rewrite using `[Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single, MvPowerSeries.X_pow_eq, MvPowerSeries.monomi …`.
-/
private theorem prod_X_lemma_8 {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
    (d.prod fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) =
      MvPowerSeries.monomial (d.mapDomain e) 1 := by
  classical
  refine Finsupp.induction d ?_ ?_
  · simp only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]
    rfl
  · intro a b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]

/- English proof (translation)
Establish `ha : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c'' : MvPowerSeries τ C))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)`. Establish `hcoef : MvPowerSeries.coeff (Finsupp.single () 1) (tyS l a) = a 0`. Establish `hl1 : l ≠ 1` using `by omega`. Unfold `tyS`. Use `first`.

Consider the case `(rw [show MvPowerSeries.coeff (Finsupp.single () 1) = PowerSeries.coeff (R := C) 1 from rfl, PowerSeries.coeff_mk]`. Simplify using `[Finset.sum_range_succ, hl1])`. Consider the case `(rw [show MvPowerSeries.coeff (Finsupp.single () 1) = PowerSeries.coeff C 1 from rfl, PowerSeries.coeff_mk]`. Simplify using `[Finset.sum_range_succ, hl1])`. Consider the case `(show (∑ s ∈ Finset.range (1 + 1), if l ^ s = 1 then a s else 0) = a 0`.

Simplify using `[Finset.sum_range_succ, hl1])`. Use `show MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c'' : MvPowerSeries τ C)) (tyS l a)) = _`. Rewrite using `[MvPowerSeries.coeff_subst ha]`. Simplify using `only [prod_X_lemma_8 (fun _ : Unit => c''), MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[finsum_eq_single _ (Finsupp.single () 1)]`.

Rewrite using `[Finsupp.mapDomain_single]`. Distinguish the cases in `h : c'' = c`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, hcoef]`. Rewrite using `[if_neg (fun h' => h ((Finsupp.single_left_injective one_ne_zero h').symm)), if_neg h]`.

Introduce `d hd`. Rewrite using `[if_neg]`. Introduce `h'`. Apply `hd` to reduce the goal to its premises. Rewrite `h'` using `[Finsupp.unique_single d, Finsupp.mapDomain_single]`.

Rewrite using `[Finsupp.unique_single d]`. Break down `(Finsupp.single_eq_single_iff _ _ _ _).mp h' with ⟨_, h2⟩ | ⟨h1, _⟩` into its components or cases. Rewrite using `[← h2]`. Conclude with `absurd h1 one_ne_zero`.
-/
theorem coeff_single_substX_tyS {τ : Type} {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (c c'' : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1)
        (PowerSeries.subst (MvPowerSeries.X c'' : MvPowerSeries τ C) (tyS l a)) =
      if c'' = c then a 0 else 0 := by
  classical
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c'' : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hcoef : MvPowerSeries.coeff (Finsupp.single () 1) (tyS l a) = a 0 := by
    have hl1 : l ≠ 1 := by omega
    unfold tyS
    first
    | (rw [show MvPowerSeries.coeff (Finsupp.single () 1) = PowerSeries.coeff (R := C) 1 from rfl,
        PowerSeries.coeff_mk]
       simp [Finset.sum_range_succ, hl1])
    | (rw [show MvPowerSeries.coeff (Finsupp.single () 1) = PowerSeries.coeff C 1 from rfl,
        PowerSeries.coeff_mk]
       simp [Finset.sum_range_succ, hl1])
    | (show (∑ s ∈ Finset.range (1 + 1), if l ^ s = 1 then a s else 0) = a 0
       simp [Finset.sum_range_succ, hl1])
  show MvPowerSeries.coeff (Finsupp.single c 1)
      (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c'' : MvPowerSeries τ C)) (tyS l a)) = _
  rw [MvPowerSeries.coeff_subst ha]
  simp only [prod_X_lemma_8 (fun _ : Unit => c''), MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [finsum_eq_single _ (Finsupp.single () 1)]
  · rw [Finsupp.mapDomain_single]
    by_cases h : c'' = c
    · subst h
      rw [if_pos rfl, if_pos rfl, hcoef]
    · rw [if_neg (fun h' => h ((Finsupp.single_left_injective one_ne_zero h').symm)), if_neg h]
  · intro d hd
    rw [if_neg]
    intro h'
    apply hd
    rw [Finsupp.unique_single d, Finsupp.mapDomain_single] at h'
    rw [Finsupp.unique_single d]
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h' with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [← h2]
    · exact absurd h1 one_ne_zero

/- English proof (translation)
Establish `hl : 2 ≤ V.l` using `V.l_prime.two_le`. Use extensionality with `μ`. Establish `key : ∀ c, MvPowerSeries.coeff μ (PowerSeries.subst (t c) (tyS V.l (fun s => S.al c s x))) = ∑ s ∈ Finset.range (μ.degree + 1), S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))`. Introduce `c`. Establish `hS : PowerSeries.HasSubst (t c)` using `PowerSeries.HasSubst.of_constantCoeff_zero (ht.1 c)`.

Establish `hlow : ∀ n, μ.degree < n → MvPowerSeries.coeff μ (t c ^ n) = 0` using `fun n hn => Formalism.FG.SolveVAux.low_pow ((Formalism.FG.SolveVAux.low_one_iff _).2 (ht.1 c)) n μ hn`. Rewrite using `[PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (μ.degree + 1))]`. Establish `e1 : ∀ n ∈ Finset.range (μ.degree + 1), PowerSeries.coeff n (tyS V.l fun s => S.al c s x) • MvPowerSeries.coeff μ (t c ^ n) = ∑ s ∈ Finset.range (μ.degree + 1), if V.l ^ s = n then S.al c s x * MvPowerSeries.coeff μ (t c ^ n) else 0`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_range]`.

Unfold `tyS`. Rewrite using `[PowerSeries.coeff_mk, smul_eq_mul, Finset.sum_mul]`. Simplify using `only [ite_mul, zero_mul]`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `s hs`.

Rewrite `hs`, the goal using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Introduce `s _ hs`. Rewrite `hs` using `[Finset.mem_range]`. Establish `: s < V.l ^ s` using `Nat.lt_pow_self (by omega)`.

Rewrite using `[if_neg (by omega)]`. Rewrite using `[Finset.sum_congr rfl e1, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite `h` using `[Finset.mem_range]`. Rewrite using `[hlow _ (by omega), mul_zero]`. Introduce `n hn`. Rewrite `hn` using `[Function.mem_support]`.

Rewrite using `[Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `h`. Conclude with `hn (by rw [hlow n (by omega), smul_zero])`. Rewrite using `[map_sum]`. Simplify using `only [key]`.

Rewrite using `[Finset.sum_comm, MvPowerSeries.coeff_X]`. Conclude with `ht.2 x μ`.
-/
theorem isT_sum {V : VF C} {d : ℕ} {I₁ J₁ : Type} [Fintype I₁] [Fintype J₁] {X₁ : Cart V d I₁ J₁} (S : Sys X₁)
    {t : I₁ → MvPowerSeries I₁ C} (ht : S.IsT t) (x : I₁) :
    ∑ c, PowerSeries.subst (t c) (tyS V.l (fun s => S.al c s x)) = MvPowerSeries.X x := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  ext μ
  have key : ∀ c, MvPowerSeries.coeff μ (PowerSeries.subst (t c) (tyS V.l (fun s => S.al c s x))) =
      ∑ s ∈ Finset.range (μ.degree + 1), S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s)) := by
    intro c
    have hS : PowerSeries.HasSubst (t c) := PowerSeries.HasSubst.of_constantCoeff_zero (ht.1 c)
    have hlow : ∀ n, μ.degree < n → MvPowerSeries.coeff μ (t c ^ n) = 0 := fun n hn =>
      Formalism.FG.SolveVAux.low_pow ((Formalism.FG.SolveVAux.low_one_iff _).2 (ht.1 c)) n μ hn
    rw [PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (μ.degree + 1))]
    · have e1 : ∀ n ∈ Finset.range (μ.degree + 1),
          PowerSeries.coeff n (tyS V.l fun s => S.al c s x) • MvPowerSeries.coeff μ (t c ^ n) =
            ∑ s ∈ Finset.range (μ.degree + 1),
              if V.l ^ s = n then S.al c s x * MvPowerSeries.coeff μ (t c ^ n) else 0 := by
        intro n hn
        rw [Finset.mem_range] at hn
        unfold tyS
        rw [PowerSeries.coeff_mk, smul_eq_mul, Finset.sum_mul]
        simp only [ite_mul, zero_mul]
        apply Finset.sum_subset
        · intro s hs
          rw [Finset.mem_range] at hs ⊢
          omega
        · intro s _ hs
          rw [Finset.mem_range] at hs
          have : s < V.l ^ s := Nat.lt_pow_self (by omega)
          rw [if_neg (by omega)]
      rw [Finset.sum_congr rfl e1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · rw [Finset.mem_range] at h
        rw [hlow _ (by omega), mul_zero]
    · intro n hn
      rw [Function.mem_support] at hn
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      exact hn (by rw [hlow n (by omega), smul_zero])
  rw [map_sum]
  simp only [key]
  rw [Finset.sum_comm, MvPowerSeries.coeff_X]
  exact ht.2 x μ

section Law

variable {dd : ℕ}

def addS {σ : Type} (F : Fin dd → PS C 2 dd) (a b : Fin dd → MvPowerSeries σ C) : Fin dd → MvPowerSeries σ C :=
  fun j => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2) (F j)

def gsum {σ ι : Type} (F : Fin dd → PS C 2 dd) (Γ : ι → Fin dd → MvPowerSeries σ C) :
    List ι → Fin dd → MvPowerSeries σ C
  | [] => 0
  | c :: l => addS F (Γ c) (gsum F Γ l)

/- English proof (translation)
Introduce and unpack `⟨j, k⟩`. Apply the tactic sequence `fin_cases j <;> simp [ha, hb]`.
-/
theorem pair_const {σ : Type} {a b : Fin dd → MvPowerSeries σ C} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (![a, b] q.1 q.2) = 0 := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]

/- English proof (translation)
Introduce and unpack `⟨j, k⟩`. Apply the tactic sequence `fin_cases j <;> simp [ha, hb]`.
-/
theorem pair_int {V : VF C} {σ : Type} {a b : Fin dd → MvPowerSeries σ C} (ha : ∀ j, IntS V (a j))
    (hb : ∀ j, IntS V (b j)) : ∀ q : Fin 2 × Fin dd, IntS V (![a, b] q.1 q.2) := by
  rintro ⟨j, k⟩
  fin_cases j <;> simp [ha, hb]

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

/- English proof (translation)
Use `Finsupp.induction d ?_ ?_` and prove the remaining obligations. Simplify using `only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]`. Both sides reduce to the same expression. Introduce `a b f _ _ ih`. Rewrite using `[Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single, MvPowerSeries.X_pow_eq, MvPowerSeries.monomi …`.
-/
private theorem prod_X_lemma {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
    (d.prod fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) =
      MvPowerSeries.monomial (d.mapDomain e) 1 := by
  classical
  refine Finsupp.induction d ?_ ?_
  · simp only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]
    rfl
  · intro a b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]`. Simplify using `only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]`. Establish `hμ : (μ.mapDomain Prod.snd).mapDomain (Prod.mk (0 : Fin 1)) = μ`. Rewrite using `[← Finsupp.mapDomain_comp]`.

Establish `hc : (Prod.mk (0 : Fin 1) ∘ (Prod.snd : Fin 1 × Fin dd → Fin dd)) = id`. Use function extensionality and compare the values at `p`. Conclude with `Prod.ext (Subsingleton.elim _ _) rfl`. Rewrite using `[hc, Finsupp.mapDomain_id]`. Rewrite using `[finsum_eq_single _ (μ.mapDomain Prod.snd)]`.

Rewrite using `[if_pos hμ.symm, smul_eq_mul, mul_one] show MvPowerSeries.coeff ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x))) f = _`. Rewrite using `[show (fun x : Fin dd => ((0 : Fin 1), x)) = Prod.mk (0 : Fin 1) from rfl, hμ]`. Introduce `d hd`. Rewrite using `[if_neg, smul_zero]`. Introduce `h`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[h, ← Finsupp.mapDomain_comp, show (Prod.snd ∘ Prod.mk (0 : Fin 1) : Fin dd → Fin dd) = id from rfl, Finsupp.mapDomain_id]`.
-/
private theorem un1_lift_lemma_2 (f : MvPowerSeries (Fin 1 × Fin dd) C) :
    MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))
      (un1 f) = f := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]
  have hμ : (μ.mapDomain Prod.snd).mapDomain (Prod.mk (0 : Fin 1)) = μ := by
    rw [← Finsupp.mapDomain_comp]
    have hc : (Prod.mk (0 : Fin 1) ∘ (Prod.snd : Fin 1 × Fin dd → Fin dd)) = id := by
      funext p
      exact Prod.ext (Subsingleton.elim _ _) rfl
    rw [hc, Finsupp.mapDomain_id]
  rw [finsum_eq_single _ (μ.mapDomain Prod.snd)]
  · rw [if_pos hμ.symm, smul_eq_mul, mul_one]
    show MvPowerSeries.coeff ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x))) f = _
    rw [show (fun x : Fin dd => ((0 : Fin 1), x)) = Prod.mk (0 : Fin 1) from rfl, hμ]
  · intro d hd
    rw [if_neg, smul_zero]
    intro h
    apply hd
    rw [h, ← Finsupp.mapDomain_comp,
      show (Prod.snd ∘ Prod.mk (0 : Fin 1) : Fin dd → Fin dd) = id from rfl, Finsupp.mapDomain_id]

/- English proof (translation)
Establish `hA : MvPowerSeries.HasSubst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)`. Establish `hB : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => (![Q] : Fin 1 → Pt C n dd) p.1 p.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by`. Break down `p with ⟨a, i⟩` into its components or cases. Use `fin_cases a`. Conclude with `hQ i)`.

Unfold `ev`. Use `conv_lhs => rw [← un1_lift_lemma_2 f]`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply hA hB]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[MvPowerSeries.subst_X hB]`. Both sides reduce to the same expression.
-/
private theorem ev1_lemma_3 {n : ℕ} (Q : Pt C n dd) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : PS C 1 dd) : ev ![Q] f = MvPowerSeries.subst Q (un1 f) := by
  have hA : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hB : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => (![Q] : Fin 1 → Pt C n dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨a, i⟩
      fin_cases a
      exact hQ i)
  unfold ev
  conv_lhs => rw [← un1_lift_lemma_2 f]
  rw [MvPowerSeries.subst_comp_subst_apply hA hB]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X hB]
  rfl

/- English proof (translation)
Establish `hpt : ∀ k : Fin 2, ∀ i, MvPowerSeries.constantCoeff (pt C dd k i) = 0` using `fun k i => by simp [pt]`. Establish `hadd : ∀ i, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C dd 0) (pt C dd 1) i) = 0` using `fun i => by show MvPowerSeries.constantCoeff (ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i)) = 0`. Unfold `ev`. Rewrite using `[cc_subst_lemma _ (fun p => by`. Break down `p with ⟨a, k⟩` into its components or cases.

Apply the tactic sequence `fin_cases a <;> simp [pt])]`. Conclude with `Y.B.G.const i`. Establish `hF' : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F`. Use function extensionality and compare the values at `i`. Use `show ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i) = Y.B.G.F i`.

Establish `hX : (fun p : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) p.1 p.2) = MvPowerSeries.X`. Use function extensionality and compare the values at `p`. Break down `p with ⟨a, k⟩` into its components or cases. Apply the tactic sequence `fin_cases a <;> rfl`. Unfold `ev`.

Rewrite using `[hX, ← MvPowerSeries.map_algebraMap_eq_subst_X]`. Simplify using the standard rewrite rules. Establish `hfb` using `Y.lg_add i`. Rewrite `hfb` using `[ev1_lemma_3 _ hadd, ev1_lemma_3 _ (hpt 0), ev1_lemma_3 _ (hpt 1), hF']`. Establish `hP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (pair_const ha hb)`.

Establish `hF : MvPowerSeries.HasSubst Y.B.G.F` using `MvPowerSeries.hasSubst_of_constantCoeff_zero Y.B.G.const`. Establish `hX0 : MvPowerSeries.HasSubst (pt C dd (0 : Fin 2))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (hpt 0)`. Establish `hX1 : MvPowerSeries.HasSubst (pt C dd (1 : Fin 2))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (hpt 1)`. Establish `e` using `congrArg (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2)) hfb`. Rewrite `e` using `[MvPowerSeries.subst_comp_subst_apply hF hP, MvPowerSeries.subst_add hP, MvPowerSeries.subst_comp_subst_apply hX0 hP, MvPowerSeries.subst_comp_subst_apply hX1 hP]`.

Simplify using `only [pt, MvPowerSeries.subst_X hP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e`. Conclude with `e`.
-/
theorem lg_addS {σ : Type} (Y : FBChart C V O dd) (a b : Fin dd → MvPowerSeries σ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0)
    (i : Fin dd) :
    MvPowerSeries.subst (addS Y.B.G.F a b) (un1 (Y.lg i)) =
      MvPowerSeries.subst a (un1 (Y.lg i)) + MvPowerSeries.subst b (un1 (Y.lg i)) := by
  have hpt : ∀ k : Fin 2, ∀ i, MvPowerSeries.constantCoeff (pt C dd k i) = 0 := fun k i => by simp [pt]
  have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C dd 0) (pt C dd 1) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i)) = 0
    unfold ev
    rw [cc_subst_lemma _ (fun p => by
      rcases p with ⟨a, k⟩
      fin_cases a <;> simp [pt])]
    exact Y.B.G.const i
  have hF' : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext i
    show ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i) = Y.B.G.F i
    have hX : (fun p : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) p.1 p.2) =
        MvPowerSeries.X := by
      funext p
      rcases p with ⟨a, k⟩
      fin_cases a <;> rfl
    unfold ev
    rw [hX, ← MvPowerSeries.map_algebraMap_eq_subst_X]
    simp
  have hfb := Y.lg_add i
  rw [ev1_lemma_3 _ hadd, ev1_lemma_3 _ (hpt 0), ev1_lemma_3 _ (hpt 1), hF'] at hfb
  have hP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (pair_const ha hb)
  have hF : MvPowerSeries.HasSubst Y.B.G.F := MvPowerSeries.hasSubst_of_constantCoeff_zero Y.B.G.const
  have hX0 : MvPowerSeries.HasSubst (pt C dd (0 : Fin 2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hpt 0)
  have hX1 : MvPowerSeries.HasSubst (pt C dd (1 : Fin 2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hpt 1)
  have e := congrArg (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2)) hfb
  rw [MvPowerSeries.subst_comp_subst_apply hF hP, MvPowerSeries.subst_add hP,
    MvPowerSeries.subst_comp_subst_apply hX0 hP, MvPowerSeries.subst_comp_subst_apply hX1 hP] at e
  simp only [pt, MvPowerSeries.subst_X hP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e
  exact e

/- English proof (translation)
The claim follows from `| [], j => by show MvPowerSeries.constantCoeff ((0 : Fin dd → MvPowerSeries σ C) j) = 0 simp | c :: l, j => constantCoeff_subst_zero (pair_const (hΓ c) (gsum_const Y Γ hΓ l)) (Y.B.G.const j)`.
-/
theorem gsum_const {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) :
    ∀ (l : List ι) j, MvPowerSeries.constantCoeff (gsum Y.B.G.F Γ l j) = 0
  | [], j => by
    show MvPowerSeries.constantCoeff ((0 : Fin dd → MvPowerSeries σ C) j) = 0
    simp
  | c :: l, j => constantCoeff_subst_zero (pair_const (hΓ c) (gsum_const Y Γ hΓ l)) (Y.B.G.const j)

/- English proof (translation)
The claim follows from `| [], j => by intro μ show V.Ge 0 (MvPowerSeries.coeff μ ((0 : Fin dd → MvPowerSeries σ C) j)) rw [Pi.zero_apply, map_zero] exact VF.Ge.zero 0 | c :: l, j => IntS.subst (pair_const (hΓ0 c) (gsum_const Y Γ hΓ0 l)) (pair_int (hΓ c) (gsum_int Y Γ hΓ0 hΓ l)) (Y.intF j)`.
-/
theorem gsum_int {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (hΓ : ∀ c j, IntS V (Γ c j)) :
    ∀ (l : List ι) j, IntS V (gsum Y.B.G.F Γ l j)
  | [], j => by
    intro μ
    show V.Ge 0 (MvPowerSeries.coeff μ ((0 : Fin dd → MvPowerSeries σ C) j))
    rw [Pi.zero_apply, map_zero]
    exact VF.Ge.zero 0
  | c :: l, j => IntS.subst (pair_const (hΓ0 c) (gsum_const Y Γ hΓ0 l))
      (pair_int (hΓ c) (gsum_int Y Γ hΓ0 hΓ l)) (Y.intF j)

/- English proof (translation)
The claim follows from `| [] => by rw [List.map_nil, List.sum_nil] exact subst_zero_of_const _ (by rw [constantCoeff_uncurry, Y.lg_const]) | c :: l => by rw [List.map_cons, List.sum_cons, ← gsum_lg Y Γ hΓ i l] exact lg_addS Y (Γ c) (gsum Y.B.G.F Γ l) (hΓ c) (gsum_const Y Γ hΓ l) i`.
-/
theorem gsum_lg {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) (i : Fin dd) :
    ∀ l : List ι, MvPowerSeries.subst (gsum Y.B.G.F Γ l) (un1 (Y.lg i)) =
      (l.map fun c => MvPowerSeries.subst (Γ c) (un1 (Y.lg i))).sum
  | [] => by
    rw [List.map_nil, List.sum_nil]
    exact subst_zero_of_const _ (by rw [constantCoeff_uncurry, Y.lg_const])
  | c :: l => by
    rw [List.map_cons, List.sum_cons, ← gsum_lg Y Γ hΓ i l]
    exact lg_addS Y (Γ c) (gsum Y.B.G.F Γ l) (hΓ c) (gsum_const Y Γ hΓ l) i

end Law

section Sys1

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]

/- English proof (translation)
Establish `hm : S.cur c ∈ (Y.raw p).TySet V g` using `(S.curve c).1`. Take `⟨γ, lam, hγ, -, hlog, -⟩` from `hm`. Conclude with `⟨γ, hγ, hlog⟩`.
-/
theorem sys_curve (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} (hg : (Y.raw p).CartHyp V g)
    (S : Sys (RawChart.cart hg)) (c : I g) :
    ∃ γ : Fin dd → PowerSeries C, IsCv V γ ∧ ∀ i, MvPowerSeries.subst γ (un1 (Y.lg i)) =
      ∑ c' : I g, p.u g c' i • tyS V.l (fun s => S.al c s c') := by
  have hm : S.cur c ∈ (Y.raw p).TySet V g := (S.curve c).1
  obtain ⟨γ, lam, hγ, -, hlog, -⟩ := hm
  exact ⟨γ, hγ, hlog⟩

/- English proof (translation)
Establish `hl : 2 ≤ V.l` using `V.l_prime.two_le`. Use `choose γ hγ hlog using fun c => sys_curve Y p hg S c`. Establish `hγ0 : ∀ c, ∀ j, MvPowerSeries.constantCoeff (γ c j) = 0` using `fun c j => (hγ c j).1`. Establish `hXc : ∀ c : I g, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C))` using `fun c => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X c`. Use `set Γ : I g → Fin dd → MvPowerSeries (I g) C := fun c j => PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (γ c j) with hΓdef`.

Establish `hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0` using `fun c j => constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X c) (hγ0 c j)`. Establish `hΓI : ∀ c j, IntS V (Γ c j)` using `fun c j => IntS.subst (fun _ => MvPowerSeries.constantCoeff_X c) (fun _ => intS_X c) (intS_ps.2 (hγ c j).2)`. Establish `hΓlg : ∀ c i, MvPowerSeries.subst (Γ c) (un1 (Y.lg i)) = ∑ c', p.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (tyS V.l (fun s => S.al c s c'))`. Introduce `c i`. Establish `e1 : MvPowerSeries.subst (Γ c) (un1 (Y.lg i)) = PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (MvPowerSeries.subst (γ c) (un1 (Y.lg i)))` using `by show _ = MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) _`.

Rewrite using `[MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (hγ0 c)) (hXc c)]`. Both sides reduce to the same expression. Rewrite using `[e1, hlog c i, ← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X c)), map_sum]`. Simplify using `only [map_smul]`. Use `set P : Fin dd → MvPowerSeries (I g) C := gsum Y.B.G.F Γ Finset.univ.toList with hPdef`.

Establish `hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0` using `gsum_const Y Γ hΓ0 _`. Establish `hPlg : ∀ i, MvPowerSeries.subst P (un1 (Y.lg i)) = ∑ c, ∑ c', p.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (tyS V.l (fun s => S.al c s c'))`. Introduce `i`. Rewrite using `[gsum_lg Y Γ hΓ0 i, Finset.sum_map_toList]`. Conclude with `Finset.sum_congr rfl fun c _ => hΓlg c i`.

Use `⟨P, hP0, gsum_int Y Γ hΓ0 hΓI _, ?_, ?_⟩` and prove the remaining obligations. Introduce `j c`. Establish `hlin` using `coeff_single_subst_lin P hP0 (un1 (Y.lg j)) j (Y.raw_lin p j) c`. Rewrite using `[← hlin, hPlg j, map_sum]`. Simplify using `only [map_sum, MvPowerSeries.coeff_smul, coeff_single_substX_tyS hl, mul_ite, mul_zero]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq']`. Simplify using `only [Finset.mem_univ, if_true]`. Use `congr 1`.

Conclude with `congrFun (S.curve c).2.1 (Sum.inl c')`. Introduce `t ht j`. Establish `ht0` using `ht.1`. Establish `hts` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ht0`. Use `set Q : Fin dd → MvPowerSeries (I g) C := fun j => MvPowerSeries.subst t (P j) with hQ`.

Establish `hQ0 : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0` using `fun j => constantCoeff_subst_zero ht0 (hP0 j)`. Establish `hPS` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hP0`. Establish `hQlg : ∀ i, MvPowerSeries.subst Q (un1 (Y.lg i)) = ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)`. Introduce `i`. Establish `e1 : MvPowerSeries.subst Q (un1 (Y.lg i)) = MvPowerSeries.subst t (MvPowerSeries.subst P (un1 (Y.lg i)))`.

Rewrite using `[MvPowerSeries.subst_comp_subst_apply hPS hts]`. Establish `e2 : ∀ c (A : PowerSeries C), MvPowerSeries.subst t (PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) A) = PowerSeries.subst (t c) A`. Introduce `c A`. Use `show MvPowerSeries.subst t (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) A) = MvPowerSeries.subst (fun _ : Unit => t c) A`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hXc c) hts]`.

Use `congr 1`. Use function extensionality and compare the values at `u`. Rewrite using `[MvPowerSeries.subst_X hts]`. Rewrite using `[e1, hPlg i, ← MvPowerSeries.coe_substAlgHom hts, map_sum]`. Simplify using `only [map_sum, map_smul, MvPowerSeries.coe_substAlgHom hts, e2]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.smul_sum, isT_sum S ht c']`. Establish `hlgS` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (Y.chart_log_constantCoeff p)`. Establish `hQS` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0`.

Establish `h` using `congrArg (MvPowerSeries.subst Q) (Y.raw_exlg p j)`. Rewrite `h` using `[MvPowerSeries.subst_comp_subst_apply hlgS hQS, MvPowerSeries.subst_X hQS]`. Use `show Q j = _`. Rewrite using `[← h]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `hQlg i`.
-/
theorem sys_P (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} (hg : (Y.raw p).CartHyp V g)
    (S : Sys (RawChart.cart hg)) :
    ∃ P : Fin dd → MvPowerSeries (I g) C, (∀ j, MvPowerSeries.constantCoeff (P j) = 0) ∧
      (∀ j, IntS V (P j)) ∧
      (∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', p.u g c' j * S.tan c c') ∧
      ∀ t : I g → MvPowerSeries (I g) C, S.IsT t → ∀ j,
        MvPowerSeries.subst t (P j) =
          MvPowerSeries.subst (fun i => ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C))
            ((Y.raw p).ex j) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  choose γ hγ hlog using fun c => sys_curve Y p hg S c
  have hγ0 : ∀ c, ∀ j, MvPowerSeries.constantCoeff (γ c j) = 0 := fun c j => (hγ c j).1
  have hXc : ∀ c : I g, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) :=
    fun c => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X c
  set Γ : I g → Fin dd → MvPowerSeries (I g) C :=
    fun c j => PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (γ c j) with hΓdef
  have hΓ0 : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0 := fun c j =>
    constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X c) (hγ0 c j)
  have hΓI : ∀ c j, IntS V (Γ c j) := fun c j =>
    IntS.subst (fun _ => MvPowerSeries.constantCoeff_X c) (fun _ => intS_X c) (intS_ps.2 (hγ c j).2)

  have hΓlg : ∀ c i, MvPowerSeries.subst (Γ c) (un1 (Y.lg i)) =
      ∑ c', p.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (tyS V.l (fun s => S.al c s c')) := by
    intro c i
    have e1 : MvPowerSeries.subst (Γ c) (un1 (Y.lg i)) =
        PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) (MvPowerSeries.subst (γ c) (un1 (Y.lg i))) := by
      show _ = MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) _
      rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (hγ0 c)) (hXc c)]
      rfl
    rw [e1, hlog c i, ← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X c)), map_sum]
    simp only [map_smul]
  set P : Fin dd → MvPowerSeries (I g) C := gsum Y.B.G.F Γ Finset.univ.toList with hPdef
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := gsum_const Y Γ hΓ0 _
  have hPlg : ∀ i, MvPowerSeries.subst P (un1 (Y.lg i)) =
      ∑ c, ∑ c', p.u g c' i • PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C)
        (tyS V.l (fun s => S.al c s c')) := by
    intro i
    rw [gsum_lg Y Γ hΓ0 i, Finset.sum_map_toList]
    exact Finset.sum_congr rfl fun c _ => hΓlg c i
  refine ⟨P, hP0, gsum_int Y Γ hΓ0 hΓI _, ?_, ?_⟩
  ·
    intro j c
    have hlin := coeff_single_subst_lin P hP0 (un1 (Y.lg j)) j (Y.raw_lin p j) c
    rw [← hlin, hPlg j, map_sum]
    simp only [map_sum, MvPowerSeries.coeff_smul, coeff_single_substX_tyS hl, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    congr 1
    exact congrFun (S.curve c).2.1 (Sum.inl c')
  ·
    intro t ht j
    have ht0 := ht.1
    have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
    set Q : Fin dd → MvPowerSeries (I g) C := fun j => MvPowerSeries.subst t (P j) with hQ
    have hQ0 : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := fun j => constantCoeff_subst_zero ht0 (hP0 j)
    have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
    have hQlg : ∀ i, MvPowerSeries.subst Q (un1 (Y.lg i)) =
        ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C) := by
      intro i
      have e1 : MvPowerSeries.subst Q (un1 (Y.lg i)) = MvPowerSeries.subst t (MvPowerSeries.subst P (un1 (Y.lg i))) := by
        rw [MvPowerSeries.subst_comp_subst_apply hPS hts]
      have e2 : ∀ c (A : PowerSeries C), MvPowerSeries.subst t
          (PowerSeries.subst (MvPowerSeries.X c : MvPowerSeries (I g) C) A) = PowerSeries.subst (t c) A := by
        intro c A
        show MvPowerSeries.subst t (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) A) =
          MvPowerSeries.subst (fun _ : Unit => t c) A
        rw [MvPowerSeries.subst_comp_subst_apply (hXc c) hts]
        congr 1
        funext u
        rw [MvPowerSeries.subst_X hts]
      rw [e1, hPlg i, ← MvPowerSeries.coe_substAlgHom hts, map_sum]
      simp only [map_sum, map_smul, MvPowerSeries.coe_substAlgHom hts, e2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← Finset.smul_sum, isT_sum S ht c']
    have hlgS := MvPowerSeries.hasSubst_of_constantCoeff_zero (Y.chart_log_constantCoeff p)
    have hQS := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
    have h := congrArg (MvPowerSeries.subst Q) (Y.raw_exlg p j)
    rw [MvPowerSeries.subst_comp_subst_apply hlgS hQS, MvPowerSeries.subst_X hQS] at h
    show Q j = _
    rw [← h]
    congr 1
    funext i
    exact hQlg i

end Sys1

/- English proof (translation)
The claim follows from `Finset.sum_induction x (fun y => (0 : WithTop ℝ) ≤ w y) (fun a b ha hb => le_trans (le_min ha hb) (AddValuation.map_add w a b)) (by show (0 : WithTop ℝ) ≤ w 0 rw [AddValuation.map_zero] exact le_top) hx`.
-/
private theorem v_sum_lemma {K : Type} [Field K] (w : AddValuation K (WithTop ℝ)) {ι : Type} (s : Finset ι)
    (x : ι → K) (hx : ∀ i ∈ s, (0 : WithTop ℝ) ≤ w (x i)) : (0 : WithTop ℝ) ≤ w (∑ i ∈ s, x i) :=
  Finset.sum_induction x (fun y => (0 : WithTop ℝ) ≤ w y) (fun a b ha hb => le_trans (le_min ha hb) (AddValuation.map_add w a b))
    (by
      show (0 : WithTop ℝ) ≤ w 0
      rw [AddValuation.map_zero]
      exact le_top) hx

end FormalGermZero

end Formalism.L2.FormalSeriesBounds
