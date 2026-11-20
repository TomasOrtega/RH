import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtRescaleGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

namespace GlobalTheory.PTypicalTangent

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

/- English proof (translation)
The claim follows from `| [] => rfl | x :: l => by rw [LogFGL.sumList, sumList_eq G l]; rfl`.
-/
theorem sumList_eq (G : LogFGL v d) :
    ∀ l : List (Fin d → PowerSeries C), G.sumList l = ptSumL G l
  | [] => rfl
  | x :: l => by rw [LogFGL.sumList, sumList_eq G l]; rfl

/- English proof (translation)
Rewrite using `[LogFGL.sumF, sumList_eq]`. Conclude with `ptSumL_good G _ fun x hx => by`. Take `⟨j, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `h j`.
-/
theorem sumF_good (G : LogFGL v d) {m : ℕ} (g : Fin m → Fin d → PowerSeries C)
    (h : ∀ j, PTGood v (g j)) : PTGood v (G.sumF g) := by
  rw [LogFGL.sumF, sumList_eq]
  exact ptSumL_good G _ fun x hx => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact h j

/- English proof (translation)
Use `show subst (G.sumF g) (G.lg a) = _`. Rewrite using `[LogFGL.sumF, sumList_eq, ptSumL_lg G _ (fun x hx => by`. Take `⟨j, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `fun c => (h j c).1)]`. Simplify using `[List.map_ofFn, List.sum_ofFn, LogFGL.lgCurve]`.
-/
theorem sumF_lg (G : LogFGL v d) {m : ℕ} (g : Fin m → Fin d → PowerSeries C)
    (h : ∀ j, PTGood v (g j)) (a : Fin d) :
    G.lgCurve (G.sumF g) a = ∑ j, G.lgCurve (g j) a := by
  show subst (G.sumF g) (G.lg a) = _
  rw [LogFGL.sumF, sumList_eq, ptSumL_lg G _ (fun x hx => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact fun c => (h j c).1)]
  simp [List.map_ofFn, List.sum_ofFn, LogFGL.lgCurve]

/- English proof (translation)
The claim follows from `| 0 => ptGood_zero | n + 1 => ptAdd_good G h (nsmul_good G h n)`.
-/
theorem nsmul_good (G : LogFGL v d) {ga : Fin d → PowerSeries C} (h : PTGood v ga) :
    ∀ n, PTGood v (G.nsmulF n ga)
  | 0 => ptGood_zero
  | n + 1 => ptAdd_good G h (nsmul_good G h n)

/- English proof (translation)
The claim follows from `| 0, a => by show subst (0 : Fin d → PowerSeries C) (G.lg a) = ((0 : ℕ) : C) • subst ga (G.lg a) rw [subst_zero_of_constantCoeff_zero (G.lg_const a), Nat.cast_zero, zero_smul] | n + 1, a => by show subst (ptAdd G ga (G.nsmulF n ga)) (G.lg a) = ((n + 1 : ℕ) : C) • subst ga (G.lg a …`.
-/
theorem nsmul_lg (G : LogFGL v d) {ga : Fin d → PowerSeries C} (h : PTGood v ga) :
    ∀ n a, G.lgCurve (G.nsmulF n ga) a = (n : C) • G.lgCurve ga a
  | 0, a => by
    show subst (0 : Fin d → PowerSeries C) (G.lg a) = ((0 : ℕ) : C) • subst ga (G.lg a)
    rw [subst_zero_of_constantCoeff_zero (G.lg_const a), Nat.cast_zero, zero_smul]
  | n + 1, a => by
    show subst (ptAdd G ga (G.nsmulF n ga)) (G.lg a) = ((n + 1 : ℕ) : C) • subst ga (G.lg a)
    rw [ptAdd_lg G (fun b => (h b).1) (fun b => (nsmul_good G h n b).1)]
    show subst ga (G.lg a) + G.lgCurve (G.nsmulF n ga) a = _
    rw [nsmul_lg G h n a, Nat.cast_succ, add_smul, one_smul, add_comm]
    rfl

/- English proof (translation)
Introduce `α hα`. Use `pt_low_of_lin (G.lg_const a) (fun s => if a = s then (1 : C) else 0) (fun s => G.lg_lin a s) α hα` as an intermediate fact. Simplify `this` using `[ite_smul, one_smul, zero_smul, Finset.sum_ite_eq]`.
-/
theorem lg_low (G : LogFGL v d) (a : Fin d) :
    ∀ α : Fin d →₀ ℕ, α.degree ≤ 1 → coeff α (G.lg a - X a) = 0 := by
  intro α hα
  have := pt_low_of_lin (G.lg_const a) (fun s => if a = s then (1 : C) else 0)
    (fun s => G.lg_lin a s) α hα
  simpa [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq] using this

/- English proof (translation)
Establish `hsx : HasSubst x` using `hasSubst_of_constantCoeff_zero hx`. Establish `hsy : HasSubst y` using `hasSubst_of_constantCoeff_zero hy`. Establish `split : ∀ z : Fin d → MvPowerSeries τ C, HasSubst z →`. Substitute `z (G.lg a) = z a + subst z (G.lg a - X a) := by` using the available equality. Introduce `z hz`.

Rewrite using `[subst_sub hz, subst_X hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[split x hsx, split y hsy, map_add, map_add, h a e he, pt_subst_agree hsx hsy hx hy (G.lg a - X a) k h (pt_hK_of_low (lg_low G a) x y) e (by omega)]`.
-/
theorem lg_agree (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (k : ℕ)
    (h : PTAgree k x y) (a : Fin d) (e : τ →₀ ℕ) (he : e.degree < k) :
    coeff e (subst x (G.lg a)) = coeff e (subst y (G.lg a)) := by
  have hsx : HasSubst x := hasSubst_of_constantCoeff_zero hx
  have hsy : HasSubst y := hasSubst_of_constantCoeff_zero hy
  have split : ∀ z : Fin d → MvPowerSeries τ C, HasSubst z →
      subst z (G.lg a) = z a + subst z (G.lg a - X a) := by
    intro z hz; rw [subst_sub hz, subst_X hz]; ring
  rw [split x hsx, split y hsy, map_add, map_add, h a e he,
    pt_subst_agree hsx hsy hx hy (G.lg a - X a) k h (pt_hK_of_low (lg_low G a) x y) e
      (by omega)]

/- English proof (translation)
Set `K : Fin d → MvPowerSeries (Fin d ⊕ Fin d) C` to `fun b => G.F b - X (Sum.inl b)`. Establish `hK : ∀ b (α : Fin d ⊕ Fin d →₀ ℕ), coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨ ∀ x y : Fin d → PowerSeries C, PTGood v x → PTGood v y → ∀ s ∈ α.support, Sum.elim x ge s = Sum.elim y ge s`. Introduce `b α hα`. Distinguish the cases in `h2 : 2 ≤ α.degree`. Conclude with `Or.inl h2`.

Use `right`. Establish `h1 : α.degree = 1`. Assume the negation of the conclusion as `h1`. Apply `hα` to reduce the goal to its premises. Rewrite using `[(Finsupp.degree_eq_zero_iff α).1 (by omega), coeff_zero_eq_constantCoeff_apply]`.

Simplify using `[K, G.F_const]`. Take `⟨s, rfl⟩` from `pt_degree_eq_one h1`. Establish `hc : coeff (Finsupp.single s 1) (K b) = if s = Sum.inr b then 1 else 0`. Simplify using `only [K, map_sub, pt_F_lin, pt_coeff_single_X]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hα` using `[hc]`. Establish `hs : s = Sum.inr b`. Assume the negation of the conclusion as `hs`. Conclude with `hα (if_neg hs)`. Introduce `x y _ _ t ht`.

Rewrite `ht` using `[Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]`. Rewrite using `[ht, hs]`. Both sides reduce to the same expression. Establish `hN : ∀ i j, (1 : Matrix (Fin d) (Fin d) C) i j ∈ ptIntSub v`. Introduce `i j`.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Take `⟨x, ⟨hx, hxe⟩, -⟩` from `pt_solve (v := v) (σ := Fin d ⊕ Fin d) (τ := Unit) (A := fun x => Sum.elim x ge) (K := K) 1 1 ga (by simp) (by simp) hN hg (fun x hx => ptc_elim_const (fun a => (hx a).1) (fun a => (he a).1)) (fun x hx s => by rcases s with s | s; exacts [(hx s).2, (he s).2]) (fun k x y _ _ hxy s …`.

Use `⟨x, hx, funext fun b => ?_⟩` and prove the remaining obligations. Establish `h0` using `ptc_elim_const (fun a => (hx a).1) (fun a => (he a).1)`. Establish `hs : HasSubst (Sum.elim x ge)` using `hasSubst_of_constantCoeff_zero h0`. Establish `e` using `hxe b`. Simplify using `only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, K, subst_sub hs, subst_X hs, Sum.elim_inl] at e`.

Rewrite using `[← e]`. Use `show subst (Sum.elim x ge) (G.F b) = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sub_exists (G : LogFGL v d) {ga ge : Fin d → PowerSeries C} (hg : PTGood v ga)
    (he : PTGood v ge) : ∃ s : Fin d → PowerSeries C, PTGood v s ∧ ptAdd G s ge = ga := by
  let K : Fin d → MvPowerSeries (Fin d ⊕ Fin d) C := fun b => G.F b - X (Sum.inl b)
  have hK : ∀ b (α : Fin d ⊕ Fin d →₀ ℕ), coeff α (K b) ≠ 0 → 2 ≤ α.degree ∨
      ∀ x y : Fin d → PowerSeries C, PTGood v x → PTGood v y →
        ∀ s ∈ α.support, Sum.elim x ge s = Sum.elim y ge s := by
    intro b α hα
    by_cases h2 : 2 ≤ α.degree
    · exact Or.inl h2
    right
    have h1 : α.degree = 1 := by
      by_contra h1
      apply hα
      rw [(Finsupp.degree_eq_zero_iff α).1 (by omega), coeff_zero_eq_constantCoeff_apply]
      simp [K, G.F_const]
    obtain ⟨s, rfl⟩ := pt_degree_eq_one h1
    have hc : coeff (Finsupp.single s 1) (K b) = if s = Sum.inr b then 1 else 0 := by
      simp only [K, map_sub, pt_F_lin, pt_coeff_single_X]; ring
    rw [hc] at hα
    have hs : s = Sum.inr b := by
      by_contra hs; exact hα (if_neg hs)
    intro x y _ _ t ht
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at ht
    rw [ht, hs]
    rfl
  have hN : ∀ i j, (1 : Matrix (Fin d) (Fin d) C) i j ∈ ptIntSub v := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  obtain ⟨x, ⟨hx, hxe⟩, -⟩ := pt_solve (v := v) (σ := Fin d ⊕ Fin d) (τ := Unit)
    (A := fun x => Sum.elim x ge) (K := K) 1 1 ga (by simp) (by simp) hN hg
    (fun x hx => ptc_elim_const (fun a => (hx a).1) (fun a => (he a).1))
    (fun x hx s => by rcases s with s | s; exacts [(hx s).2, (he s).2])
    (fun k x y _ _ hxy s e he' => by rcases s with s | s; exacts [hxy s e he', rfl])
    hK (fun b => Subring.sub_mem _ (G.F_int b) (ptIntSer_X _))
    (fun b => by simp [K, G.F_const])
  refine ⟨x, hx, funext fun b => ?_⟩
  have h0 := ptc_elim_const (fun a => (hx a).1) (fun a => (he a).1)
  have hs : HasSubst (Sum.elim x ge) := hasSubst_of_constantCoeff_zero h0
  have e := hxe b
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, K, subst_sub hs, subst_X hs, Sum.elim_inl] at e
  rw [← e]
  show subst (Sum.elim x ge) (G.F b) = _
  ring

/- English proof (translation)
Establish `e : ∀ j : ℕ, (ζ ^ j) ^ m = (ζ ^ m) ^ j` using `fun j => by`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`. Repeatedly rewrite using `[e]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) l]`. Use `split_ifs with hd`.

Rewrite using `[(hζ.pow_eq_one_iff_dvd m).2 hd]`. Simplify using the standard rewrite rules. Establish `hne : ζ ^ m - 1 ≠ 0` using `sub_ne_zero.2 fun h1 => hd ((hζ.pow_eq_one_iff_dvd m).1 h1)`. Establish `hg` using `geom_sum_mul (ζ ^ m) l`. Rewrite `hg` using `[← pow_mul, mul_comm m l, pow_mul, hζ.pow_eq_one, one_pow, sub_self]`.

Conclude with `(mul_eq_zero.1 hg).resolve_right hne`.
-/
theorem root_sum {ζ : C} {l : ℕ} (hζ : IsPrimitiveRoot ζ l) (m : ℕ) :
    ∑ j : Fin l, (ζ ^ (j : ℕ)) ^ m = if l ∣ m then (l : C) else 0 := by
  have e : ∀ j : ℕ, (ζ ^ j) ^ m = (ζ ^ m) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) l]
  split_ifs with hd
  · rw [(hζ.pow_eq_one_iff_dvd m).2 hd]
    simp
  · have hne : ζ ^ m - 1 ≠ 0 := sub_ne_zero.2 fun h1 => hd ((hζ.pow_eq_one_iff_dvd m).1 h1)
    have hg := geom_sum_mul (ζ ^ m) l
    rw [← pow_mul, mul_comm m l, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at hg
    exact (mul_eq_zero.1 hg).resolve_right hne

/- English proof (translation)
Establish `h1 : (ζ ^ j) ^ l = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Use `show 0 ≤ v (ζ ^ j)`. Rewrite using `[v_eq_zero_of_pow_eq_one hl h1]`.
-/
theorem root_int {ζ : C} {l : ℕ} (hl : l ≠ 0) (hζ : ζ ^ l = 1) (j : ℕ) :
    ζ ^ j ∈ ptIntSub v := by
  have h1 : (ζ ^ j) ^ l = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  show 0 ≤ v (ζ ^ j)
  rw [v_eq_zero_of_pow_eq_one hl h1]

/- English proof (translation)
Establish `hl0 : (l : C) ≠ 0` using `by exact_mod_cast (show l ≠ 0 by omega)`. Use `haveI : NeZero (l : C) := ⟨hl0⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot C l`. Set `g : Fin l → Fin d → PowerSeries C` to `fun j => rescaleCurve (ζ ^ (j : ℕ)) ga`. Establish `hgg : ∀ j, PTGood v (g j)` using `fun j => pt_rescale_good (root_int (by omega) hζ.pow_eq_one j) hg`.

Establish `hδ` using `sumF_good G g hgg`. Take `⟨ε, ⟨hε, hεe⟩, -⟩` from `nsmul_coprime_bijective_curves G hp hvp l hpl (G.sumF g) (isCurve_iff_good.2 hδ)`. Establish `hε'` using `isCurve_iff_good.1 hε`. Take `⟨s, hs, hse⟩` from `sub_exists G hg hε'`. Establish `hlgδ : ∀ a m, PowerSeries.coeff m (G.lgCurve (G.sumF g) a) = (if l ∣ m then (l : C) else 0) * PowerSeries.coeff m (G.lgCurve ga a)`.

Introduce `a m`. Rewrite using `[sumF_lg G g hgg a, map_sum]`. Simplify using `only [g, pt_lg_rescale G _ (fun b => (hg b).1) a, PowerSeries.coeff_rescale]`. Rewrite using `[← Finset.sum_mul, root_sum hζ m]`. Establish `hlgε : ∀ a m, PowerSeries.coeff m (G.lgCurve ε a) = (if l ∣ m then 1 else 0) * PowerSeries.coeff m (G.lgCurve ga a)`.

Introduce `a m`. Establish `h1` using `congrArg (PowerSeries.coeff m) (nsmul_lg G hε' l a)`. Rewrite `h1` using `[hεe, hlgδ, PowerSeries.coeff_smul, smul_eq_mul]`. Use `split_ifs at h1 ⊢ with hd`. Rewrite using `[one_mul]`.

Conclude with `(mul_left_cancel₀ hl0 h1).symm`. Rewrite `h1`, the goal using `[zero_mul]`. Conclude with `((mul_eq_zero.1 h1.symm).resolve_left hl0)`. Establish `hsum : ∀ a, G.lgCurve ga a = G.lgCurve s a + G.lgCurve ε a` using `fun a => by`. Use `ptAdd_lg G (fun b => (hs b).1) (fun b => (hε' b).1) a` as an intermediate fact.

Rewrite `this` using `[hse]`. Conclude with `this`. Establish `hlgs : ∀ a m, PowerSeries.coeff m (G.lgCurve s a) = if l ∣ m then 0 else PowerSeries.coeff m (G.lgCurve ga a)`. Introduce `a m`. Establish `h1` using `congrArg (PowerSeries.coeff m) (hsum a)`.

Rewrite `h1` using `[map_add, hlgε]`. Use `split_ifs at h1 ⊢ with hd`. Take the linear combination `-h1`. Take the linear combination `-h1`. Use `⟨s, hs, ?_, hlgs⟩` and prove the remaining obligations.

Use `pt_agree_of_lg G (fun a => (hs a).1) (fun a => (hg a).1) l fun a e he => ?_` and prove the remaining obligations. Rewrite `he` using `[Finsupp.unique_single e, Finsupp.degree_single]`. Rewrite using `[Finsupp.unique_single e]`. Establish `h2` using `hlgs a (e ())`. Express the relevant statement in the definitionally equal form `PowerSeries.coeff (e ()) (G.lgCurve s a) = PowerSeries.coeff (e ()) (G.lgCurve ga a)`.

Rewrite using `[h2]`. Use `split_ifs with hd`. Establish `he0 : e () = 0` using `Nat.eq_zero_of_dvd_of_lt hd he`. Rewrite using `[he0, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `(constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun b => (hg b).1) (fun b => (hg b).1) (G.lg_const a)).symm`.

Both sides reduce to the same expression.
-/
theorem delete_step [IsAlgClosed C] [CharZero C] (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    (hvp : v (p : C) = 1) {l : ℕ} (hl2 : 2 ≤ l) (hpl : ¬ p ∣ l) {ga : Fin d → PowerSeries C}
    (hg : PTGood v ga) :
    ∃ s : Fin d → PowerSeries C, PTGood v s ∧ PTAgree l s ga ∧ ∀ a m,
      PowerSeries.coeff m (G.lgCurve s a) =
        if l ∣ m then 0 else PowerSeries.coeff m (G.lgCurve ga a) := by
  have hl0 : (l : C) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
  haveI : NeZero (l : C) := ⟨hl0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C l
  let g : Fin l → Fin d → PowerSeries C := fun j => rescaleCurve (ζ ^ (j : ℕ)) ga
  have hgg : ∀ j, PTGood v (g j) := fun j =>
    pt_rescale_good (root_int (by omega) hζ.pow_eq_one j) hg
  have hδ := sumF_good G g hgg
  obtain ⟨ε, ⟨hε, hεe⟩, -⟩ := nsmul_coprime_bijective_curves G hp hvp l hpl (G.sumF g) (isCurve_iff_good.2 hδ)
  have hε' := isCurve_iff_good.1 hε
  obtain ⟨s, hs, hse⟩ := sub_exists G hg hε'
  have hlgδ : ∀ a m, PowerSeries.coeff m (G.lgCurve (G.sumF g) a) =
      (if l ∣ m then (l : C) else 0) * PowerSeries.coeff m (G.lgCurve ga a) := by
    intro a m
    rw [sumF_lg G g hgg a, map_sum]
    simp only [g, pt_lg_rescale G _ (fun b => (hg b).1) a, PowerSeries.coeff_rescale]
    rw [← Finset.sum_mul, root_sum hζ m]
  have hlgε : ∀ a m, PowerSeries.coeff m (G.lgCurve ε a) =
      (if l ∣ m then 1 else 0) * PowerSeries.coeff m (G.lgCurve ga a) := by
    intro a m
    have h1 := congrArg (PowerSeries.coeff m) (nsmul_lg G hε' l a)
    rw [hεe, hlgδ, PowerSeries.coeff_smul, smul_eq_mul] at h1
    split_ifs at h1 ⊢ with hd
    · rw [one_mul]; exact (mul_left_cancel₀ hl0 h1).symm
    · rw [zero_mul] at h1 ⊢; exact ((mul_eq_zero.1 h1.symm).resolve_left hl0)
  have hsum : ∀ a, G.lgCurve ga a = G.lgCurve s a + G.lgCurve ε a := fun a => by
    have := ptAdd_lg G (fun b => (hs b).1) (fun b => (hε' b).1) a
    rw [hse] at this
    exact this
  have hlgs : ∀ a m, PowerSeries.coeff m (G.lgCurve s a) =
      if l ∣ m then 0 else PowerSeries.coeff m (G.lgCurve ga a) := by
    intro a m
    have h1 := congrArg (PowerSeries.coeff m) (hsum a)
    rw [map_add, hlgε] at h1
    split_ifs at h1 ⊢ with hd
    · linear_combination -h1
    · linear_combination -h1
  refine ⟨s, hs, ?_, hlgs⟩
  refine pt_agree_of_lg G (fun a => (hs a).1) (fun a => (hg a).1) l fun a e he => ?_
  rw [Finsupp.unique_single e, Finsupp.degree_single] at he
  rw [Finsupp.unique_single e]
  have h2 := hlgs a (e ())
  change PowerSeries.coeff (e ()) (G.lgCurve s a) = PowerSeries.coeff (e ()) (G.lgCurve ga a)
  rw [h2]
  split_ifs with hd
  · have he0 : e () = 0 := Nat.eq_zero_of_dvd_of_lt hd he
    rw [he0, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun b => (hg b).1)
      (fun b => (hg b).1) (G.lg_const a)).symm
  · rfl

/- English proof (translation)
Distinguish the cases in `h : 2 ≤ n ∧ ¬ p ∣ n`. Take `⟨s, hs, hag, hlg⟩` from `delete_step G hp hvp h.1 h.2 (isCurve_iff_good.1 ga.2)`. Use `⟨⟨s, isCurve_iff_good.2 hs⟩, fun a m hm => ?_, fun a m => ?_⟩` and prove the remaining obligations. Conclude with `hag a (Finsupp.single () m) (by rw [Finsupp.degree_single]; have := h.1; omega)`. Rewrite using `[hlg]`.

Simplify using `[h.1, h.2]`. Use `⟨ga, fun _ _ _ => rfl, fun a m => ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]`.
-/
theorem uniform_step [IsAlgClosed C] [CharZero C] (G : LogFGL v d) {p : ℕ} (hp : p.Prime)
    (hvp : v (p : C) = 1) (n : ℕ) (ga : {g : Fin d → PowerSeries C // IsCurve v g}) :
    ∃ s : {g : Fin d → PowerSeries C // IsCurve v g},
      (∀ a m, m < max n 2 → PowerSeries.coeff m (s.1 a) = PowerSeries.coeff m (ga.1 a)) ∧
      ∀ a m, PowerSeries.coeff m (G.lgCurve s.1 a) =
        if 2 ≤ n ∧ ¬ p ∣ n ∧ n ∣ m then 0 else PowerSeries.coeff m (G.lgCurve ga.1 a) := by
  by_cases h : 2 ≤ n ∧ ¬ p ∣ n
  · obtain ⟨s, hs, hag, hlg⟩ := delete_step G hp hvp h.1 h.2 (isCurve_iff_good.1 ga.2)
    refine ⟨⟨s, isCurve_iff_good.2 hs⟩, fun a m hm => ?_, fun a m => ?_⟩
    · exact hag a (Finsupp.single () m) (by rw [Finsupp.degree_single]; have := h.1; omega)
    · rw [hlg]
      simp [h.1, h.2]
  · refine ⟨ga, fun _ _ _ => rfl, fun a m => ?_⟩
    rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]

/- English proof (translation)
Take `⟨e, l, hl, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one`. Use `⟨l, ?_, hl, Dvd.intro_left _ rfl⟩` and prove the remaining obligations. Break down `l with _ | _ | l` into its components or cases. Simplify using `at hl`. Conclude with `absurd (by simp) (hm e)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_divisor {p m : ℕ} (hp : p.Prime) (hm0 : m ≠ 0) (hm : ∀ n, m ≠ p ^ n) :
    ∃ l, 2 ≤ l ∧ ¬ p ∣ l ∧ l ∣ m := by
  obtain ⟨e, l, hl, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
  refine ⟨l, ?_, hl, Dvd.intro_left _ rfl⟩
  rcases l with _ | _ | l
  · simp at hl
  · exact absurd (by simp) (hm e)
  · omega

/- English proof (translation)
Introduce `C _ _ _ v p hp hvp d G u hu`. Use `choose st hst1 hst2 using uniform_step G hp hvp`. Establish `h0 : IsCurve v (fun a => PowerSeries.monomial 1 (u a))` using `fun a => by`. Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_monomial]`.

Simplify using the standard rewrite rules. Rewrite using `[PowerSeries.coeff_monomial] split_ifs`. Conclude with `hu a`. Simplify using `[IsIntV]`. Set `g : ℕ → {g : Fin d → PowerSeries C // IsCurve v g}` to `fun n => Nat.rec ⟨_, h0⟩ (fun n x => st n x) n`.

Establish `hg : ∀ n, g (n + 1) = st n (g n)` using `fun n => rfl`. Establish `hstab : ∀ k j, k ≤ j → ∀ a m, m < max k 2 → PowerSeries.coeff m ((g j).1 a) = PowerSeries.coeff m ((g k).1 a)`. Introduce `k j hkj a m hm`. Proceed by induction on `j, hkj using Nat.le_induction with`. Consider the case `base => rfl`.

Consider the case `succ j hj ih => rw [hg, hst1 j (g j) a m (by omega), ih]`. Establish `hvan : ∀ l m a, 2 ≤ l → ¬ p ∣ l → l ∣ m → ∀ j, l + 1 ≤ j → PowerSeries.coeff m (G.lgCurve (g j).1 a) = 0`. Introduce `l m a h1 h2 h3 j hj`. Proceed by induction on `j, hj using Nat.le_induction with`. Consider the case `base => rw [hg, hst2, if_pos ⟨h1, h2, h3⟩]`.

Consider the case `succ j hj ih => rw [hg, hst2, ih, ite_self]`. Set `γ : Fin d → PowerSeries C` to `fun a => PowerSeries.mk fun m => PowerSeries.coeff m ((g (m + 1)).1 a)`. Establish `hγ : ∀ a m, PowerSeries.coeff m (γ a) = PowerSeries.coeff m ((g (m + 1)).1 a)` using `fun a m => PowerSeries.coeff_mk _ _`. Establish `hc : IsCurve v γ` using `fun a => by`. Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `((g (0 + 1)).2 a).1`. Rewrite using `[hγ]`. Conclude with `((g (n + 1)).2 a).2 n`. Use `⟨γ, hc, fun a m hm => ?_, funext fun a => ?_⟩` and prove the remaining obligations.

Break down `eq_or_ne m 0 with rfl | hm0` into its components or cases. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun b => (hc b).1) (fun b => (hc b).1) (G.lg_const a)`. Take `⟨l, h1, h2, h3⟩` from `exists_divisor hp hm0 hm`. Establish `hle : l ≤ m` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h3`.

Establish `hag : PTAgree (m + 1) γ (g (m + 1)).1`. Introduce `b e he`. Rewrite `he`, the goal using `[PTb.unit_finsupp e]`. Rewrite `he` using `[Finsupp.degree_single]`. Express the relevant statement in the definitionally equal form `PowerSeries.coeff (e ()) (γ b) = PowerSeries.coeff (e ()) ((g (m + 1)).1 b)`.

Rewrite using `[hγ, hstab (e () + 1) (m + 1) (by omega) b _ (by omega)]`. Use `lg_agree G (fun b => (hc b).1) (fun b => ((g (m + 1)).2 b).1) (m + 1) hag a (Finsupp.single () m) (by rw [Finsupp.degree_single]; omega)` as an intermediate fact. Conclude with `this.trans (hvan l m a h1 h2 h3 (m + 1) (by omega))`. Use `show PowerSeries.coeff 1 (γ a) = u a`. Rewrite using `[hγ, hstab 0 (1 + 1) (by omega) a 1 (by omega)]`.

Use `show PowerSeries.coeff 1 (PowerSeries.monomial 1 (u a)) = u a`. Rewrite using `[PowerSeries.coeff_monomial, if_pos rfl]`.
-/
theorem exists_pTypical_tangent :
    (∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
      p.Prime → v (p : C) = 1 → ∀ (d : ℕ) (G : LogFGL v d) (u : Fin d → C),
      (∀ a, IsIntV v (u a)) →
      ∃ γ : Fin d → PowerSeries C, IsCurve v γ ∧ G.IsPTypical p γ ∧ tangent γ = u) := by
  intro C _ _ _ v p hp hvp d G u hu
  choose st hst1 hst2 using uniform_step G hp hvp
  have h0 : IsCurve v (fun a => PowerSeries.monomial 1 (u a)) := fun a => by
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_monomial]
      simp
    · rw [PowerSeries.coeff_monomial]
      split_ifs
      · exact hu a
      · simp [IsIntV]
  let g : ℕ → {g : Fin d → PowerSeries C // IsCurve v g} := fun n =>
    Nat.rec ⟨_, h0⟩ (fun n x => st n x) n
  have hg : ∀ n, g (n + 1) = st n (g n) := fun n => rfl
  have hstab : ∀ k j, k ≤ j → ∀ a m, m < max k 2 →
      PowerSeries.coeff m ((g j).1 a) = PowerSeries.coeff m ((g k).1 a) := by
    intro k j hkj a m hm
    induction j, hkj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [hg, hst1 j (g j) a m (by omega), ih]
  have hvan : ∀ l m a, 2 ≤ l → ¬ p ∣ l → l ∣ m → ∀ j, l + 1 ≤ j →
      PowerSeries.coeff m (G.lgCurve (g j).1 a) = 0 := by
    intro l m a h1 h2 h3 j hj
    induction j, hj using Nat.le_induction with
    | base => rw [hg, hst2, if_pos ⟨h1, h2, h3⟩]
    | succ j hj ih => rw [hg, hst2, ih, ite_self]
  let γ : Fin d → PowerSeries C := fun a =>
    PowerSeries.mk fun m => PowerSeries.coeff m ((g (m + 1)).1 a)
  have hγ : ∀ a m, PowerSeries.coeff m (γ a) = PowerSeries.coeff m ((g (m + 1)).1 a) :=
    fun a m => PowerSeries.coeff_mk _ _
  have hc : IsCurve v γ := fun a => by
    refine ⟨?_, fun n => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact ((g (0 + 1)).2 a).1
    · rw [hγ]; exact ((g (n + 1)).2 a).2 n
  refine ⟨γ, hc, fun a m hm => ?_, funext fun a => ?_⟩
  · rcases eq_or_ne m 0 with rfl | hm0
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun b => (hc b).1)
        (fun b => (hc b).1) (G.lg_const a)
    · obtain ⟨l, h1, h2, h3⟩ := exists_divisor hp hm0 hm
      have hle : l ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h3
      have hag : PTAgree (m + 1) γ (g (m + 1)).1 := by
        intro b e he
        rw [PTb.unit_finsupp e] at he ⊢
        rw [Finsupp.degree_single] at he
        change PowerSeries.coeff (e ()) (γ b) = PowerSeries.coeff (e ()) ((g (m + 1)).1 b)
        rw [hγ, hstab (e () + 1) (m + 1) (by omega) b _ (by omega)]
      have := lg_agree G (fun b => (hc b).1) (fun b => ((g (m + 1)).2 b).1) (m + 1) hag a
        (Finsupp.single () m) (by rw [Finsupp.degree_single]; omega)
      exact this.trans (hvan l m a h1 h2 h3 (m + 1) (by omega))
  · show PowerSeries.coeff 1 (γ a) = u a
    rw [hγ, hstab 0 (1 + 1) (by omega) a 1 (by omega)]
    show PowerSeries.coeff 1 (PowerSeries.monomial 1 (u a)) = u a
    rw [PowerSeries.coeff_monomial, if_pos rfl]

end

end GlobalTheory.PTypicalTangent
