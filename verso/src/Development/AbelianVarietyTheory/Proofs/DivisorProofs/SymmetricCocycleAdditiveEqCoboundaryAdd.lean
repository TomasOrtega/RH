import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmCocycleApplyFinsetSumStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Establish `hs : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R))` using `hasSubst_of_constantCoeff_zero fun _ => map_zero _`. Use extensionality with `e`. Rewrite using `[coeff_subst hs, finsum_eq_single _ 0]`. Apply the tactic sequence `rw [Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff_apply, coeff_C, coeff_one, smul_eq_mul] split_ifs <;> simp`. Introduce `dd hdd`.

Take `⟨s, hs'⟩` from `Finsupp.ne_iff.1 hdd`. Establish `hmem : s ∈ dd.support` using `Finsupp.mem_support_iff.2 (by simpa using hs')`. Rewrite using `[Finsupp.prod, Finset.prod_eq_zero hmem (zero_pow (Finsupp.mem_support_iff.1 hmem)), map_zero, smul_zero]`.
-/
theorem subst_zeroPt {σ τ : Type} [Finite σ] (f : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) f = C (constantCoeff f) := by
  classical
  have hs : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · rw [Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff_apply, coeff_C, coeff_one, smul_eq_mul]
    split_ifs <;> simp
  · intro dd hdd
    obtain ⟨s, hs'⟩ := Finsupp.ne_iff.1 hdd
    have hmem : s ∈ dd.support := Finsupp.mem_support_iff.2 (by simpa using hs')
    rw [Finsupp.prod, Finset.prod_eq_zero hmem (zero_pow (Finsupp.mem_support_iff.1 hmem)), map_zero,
      smul_zero]

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]`.
-/
theorem hs2 {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

/- English proof (translation)
Unfold `at2`. Rewrite using `[subst_comp_subst_apply (hs2 hu hv) (hasSubst_of_constantCoeff_zero ha)]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `cases s <;> rfl`.
-/
theorem subst_powerSeriesEvalTwoGroups {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hs2 hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl

/- English proof (translation)
Unfold `at2`. Rewrite using `[subst_X (hs2 hu hv)]`.
-/
theorem powerSeriesEvalTwoGroups_X {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (s : Fin d ⊕ Fin d) :
    at2 (X s) u v = Sum.elim u v s := by
  unfold at2
  rw [subst_X (hs2 hu hv)]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Unfold `op addLaw at2`. Rewrite using `[subst_add (hs2 hu hv), subst_X (hs2 hu hv), subst_X (hs2 hu hv)]`. Both sides reduce to the same expression.
-/
theorem op_addLaw {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : op (addLaw R d) u v = u + v := by
  funext i
  unfold op addLaw at2
  rw [subst_add (hs2 hu hv), subst_X (hs2 hu hv), subst_X (hs2 hu hv)]
  rfl

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Use `set a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w) with ha_def`. Establish `ha0 : ∀ t, constantCoeff (a t) = 0` using `fun t => by`. Apply the tactic sequence `rcases t with t | t | t <;> simp [a, hu, hv, hw]`. Establish `ha : HasSubst a` using `hasSubst_of_constantCoeff_zero ha0`. Establish `h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0` using `fun i => by simp [x1]`.

Establish `h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0` using `fun i => by simp [x2]`. Establish `h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0` using `fun i => by simp [x3]`. Establish `e1 : (fun i => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = u`. Use function extensionality and compare the values at `i`. Simplify using `only [x1]`.

Rewrite using `[subst_X ha]`. Both sides reduce to the same expression. Establish `e2 : (fun i => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = v`. Use function extensionality and compare the values at `i`. Simplify using `only [x2]`.

Rewrite using `[subst_X ha]`. Both sides reduce to the same expression. Establish `e3 : (fun i => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = w`. Use function extensionality and compare the values at `i`. Simplify using `only [x3]`.

Rewrite using `[subst_X ha]`. Both sides reduce to the same expression. Establish `hadd : ∀ p q : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R, (fun i => subst a ((p + q) i)) = (fun i => subst a (p i)) + (fun i => subst a (q i))`. Introduce `p q`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply]`. Rewrite using `[subst_add ha]`. Establish `h12 : ∀ i, constantCoeff ((x1 + x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0` using `fun i => by simp [h1, h2]`. Establish `h23 : ∀ i, constantCoeff ((x2 + x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0` using `fun i => by simp [h2, h3]`. Establish `key` using `congrArg (subst a) hc`.

Unfold `cob2 at key`. Rewrite `key` using `[op_addLaw h1 h2, op_addLaw h2 h3]`. Rewrite `key` using `[subst_sub ha, subst_add ha, subst_sub ha, subst_powerSeriesEvalTwoGroups h2 h3 ha0, subst_powerSeriesEvalTwoGroups h12 h3 ha0, subst_powerSeriesEvalTwoGroups h1 h23 ha0, subst_powerSeriesEvalTwoGroups h1 h2 ha0, hadd, hadd, e1, e2, e3]`. Rewrite using `[key, ← coe_substAlgHom ha, map_zero]`.
-/
theorem coc_at {τ : Type} [Finite τ] {c : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hc : cob2 (addLaw R d) c = 0) {u v w : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    at2 c v w - at2 c (u + v) w + at2 c u (v + w) - at2 c u v = 0 := by
  set a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w) with ha_def
  have ha0 : ∀ t, constantCoeff (a t) = 0 := fun t => by
    rcases t with t | t | t <;> simp [a, hu, hv, hw]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x1]
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x2]
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x3]
  have e1 : (fun i => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = u := by
    funext i; simp only [x1]; rw [subst_X ha]; rfl
  have e2 : (fun i => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = v := by
    funext i; simp only [x2]; rw [subst_X ha]; rfl
  have e3 : (fun i => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = w := by
    funext i; simp only [x3]; rw [subst_X ha]; rfl
  have hadd : ∀ p q : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R,
      (fun i => subst a ((p + q) i)) = (fun i => subst a (p i)) + (fun i => subst a (q i)) := by
    intro p q; funext i; simp only [Pi.add_apply]; rw [subst_add ha]
  have h12 : ∀ i, constantCoeff ((x1 + x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [h1, h2]
  have h23 : ∀ i, constantCoeff ((x2 + x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [h2, h3]
  have key := congrArg (subst a) hc
  unfold cob2 at key
  rw [op_addLaw h1 h2, op_addLaw h2 h3] at key
  rw [subst_sub ha, subst_add ha, subst_sub ha, subst_powerSeriesEvalTwoGroups h2 h3 ha0, subst_powerSeriesEvalTwoGroups h12 h3 ha0,
    subst_powerSeriesEvalTwoGroups h1 h23 ha0, subst_powerSeriesEvalTwoGroups h1 h2 ha0, hadd, hadd, e1, e2, e3] at key
  rw [key, ← coe_substAlgHom ha, map_zero]

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

variable (R d) in

def PtGrp (τ : Type) : AddSubgroup (Fin d → MvPowerSeries τ R) where
  carrier := {u | ∀ i, constantCoeff (u i) = 0}
  zero_mem' := fun i => by simp
  add_mem' := fun {u v} hu hv i => by simp [hu i, hv i]
  neg_mem' := fun {u} hu i => by simp [hu i]

/- English proof (translation)
Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.single_apply]`. Rewrite using `[Finset.sum_ite_eq]`.
-/
theorem sum_single_apply {M : Type} [AddCommMonoid M] (s : Finset (Fin d)) (w : Fin d → M) (i : Fin d) :
    (∑ j ∈ s, Pi.single j (w j) : Fin d → M) i = if i ∈ s then w i else 0 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq]

/- English proof (translation)
Establish `hS : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Use function extensionality and compare the values at `i`. Rewrite using `[sum_single_apply, sum_single_apply]`. Use `split_ifs`. Conclude with `subst_X hS i`.

Rewrite using `[← coe_substAlgHom hS, map_zero]`.
-/
theorem subst_sum_single {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (s : Finset (Fin d)) :
    (fun i => subst a ((∑ j ∈ s, Pi.single j (X j) : Fin d → MvPowerSeries (Fin d) R) i)) =
      ∑ j ∈ s, Pi.single j (a j) := by
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  funext i
  rw [sum_single_apply, sum_single_apply]
  split_ifs
  · exact subst_X hS i
  · rw [← coe_substAlgHom hS, map_zero]

/- English proof (translation)
Apply the tactic sequence `rw [sum_single_apply]; split_ifs <;> simp [hw]`.
-/
theorem cc_sum_single {τ : Type} (s : Finset (Fin d)) (w : Fin d → MvPowerSeries τ R)
    (hw : ∀ j, constantCoeff (w j) = 0) (i : Fin d) :
    constantCoeff ((∑ j ∈ s, Pi.single j (w j) : Fin d → MvPowerSeries τ R) i) = 0 := by
  rw [sum_single_apply]; split_ifs <;> simp [hw]

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Establish `hS : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.single_apply, Pi.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `subst_X hS i`. Rewrite using `[← coe_substAlgHom hS, map_zero]`.
-/
theorem subst_single {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (m : Fin d) :
    (fun i => subst a ((Pi.single m (X m) : Fin d → MvPowerSeries (Fin d) R) i)) = Pi.single m (a m) := by
  classical
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  funext i
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h; exact subst_X hS i
  · rw [← coe_substAlgHom hS, map_zero]

variable (R) in

def corr (c : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ m : Fin d, at2 c (∑ j ∈ Finset.univ.filter (· < m), Pi.single j (X j))
    (Pi.single m (X m) : Fin d → MvPowerSeries (Fin d) R)

/- English proof (translation)
Establish `hS : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Unfold `corr`. Rewrite using `[← coe_substAlgHom hS, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rw [coe_substAlgHom hS, subst_powerSeriesEvalTwoGroups (cc_sum_single _ _ (fun j => by simp)) (fun i => by rw [Pi.single_apply]; split_ifs <;> simp) ha, subst_sum_single ha, subst_single ha]`.
-/
theorem subst_corr {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (corr R c) = ∑ m : Fin d, at2 c (∑ j ∈ Finset.univ.filter (· < m), Pi.single j (a j))
      (Pi.single m (a m)) := by
  classical
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  unfold corr
  rw [← coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coe_substAlgHom hS, subst_powerSeriesEvalTwoGroups (cc_sum_single _ _ (fun j => by simp))
    (fun i => by rw [Pi.single_apply]; split_ifs <;> simp) ha, subst_sum_single ha, subst_single ha]

end GlobalTheory.SymCocAdd

namespace GlobalTheory

open GlobalTheory.SymCocAdd in

/- English proof (translation)
Set `τ` to `Fin d ⊕ Fin d`. Set `A` to `PtGrp R d τ`. Set `γ : A → A → MvPowerSeries τ R` to `fun u v => at2 c u.1 v.1`. Establish `hsymm : ∀ u v, γ u v = γ v u`. Introduce `u v`.

Establish `hX1 : ∀ i, constantCoeff ((fun i => (X (Sum.inr i) : MvPowerSeries τ R)) i) = 0` using `fun i => by simp`. Establish `hX2 : ∀ i, constantCoeff ((fun i => (X (Sum.inl i) : MvPowerSeries τ R)) i) = 0` using `fun i => by simp`. Establish `huv : ∀ t, constantCoeff (Sum.elim u.1 v.1 t) = 0` using `fun t => by`. Consider the cases of `t with`. Consider the case `inl t => exact u.2 t`.

Consider the case `inr t => exact v.2 t`. Use `subst_powerSeriesEvalTwoGroups hX1 hX2 huv c` as an intermediate fact. Express the relevant statement in the definitionally equal form `at2 (swap c) u.1 v.1 = _ at this`. Rewrite `this` using `[hc.2]`. Simplify using `only [γ]`.

Rewrite using `[this]`. Establish `hS : HasSubst (Sum.elim u.1 v.1)` using `hasSubst_of_constantCoeff_zero huv`. Apply the tactic sequence `congr 1 <;> funext i <;> rw [subst_X hS] <;> rfl`. Establish `hcoc : ∀ x y z : A, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0` using `fun x y z => coc_at hc.1 x.2 y.2 z.2`. Establish `hzero : γ 0 0 = 0`.

Simplify using `only [γ]`. Unfold `at2`. Apply the tactic sequence `have : Sum.elim ((0 : A) : Fin d → MvPowerSeries τ R) ((0 : A) : Fin d → MvPowerSeries τ R) = fun _ => 0 := by funext t; cases t <;> rfl`. Rewrite using `[this, subst_zeroPt, h0, map_zero]`. Set `x : Fin d → A` to `fun m => ⟨Pi.single m (X (Sum.inl m)), fun i => by`.

Apply the tactic sequence `rw [Pi.single_apply]; split_ifs <;> simp⟩`. Set `y : Fin d → A` to `fun m => ⟨Pi.single m (X (Sum.inr m)), fun i => by`. Apply the tactic sequence `rw [Pi.single_apply]; split_ifs <;> simp⟩`. Establish `key` using `GlobalTheory.T.symmCocycle_apply_finset_sum A (MvPowerSeries τ R) γ hsymm hcoc hzero d x y`. Establish `coeA : ∀ (s : Finset (Fin d)) (f : Fin d → A), ((∑ j ∈ s, f j : A) : Fin d → MvPowerSeries τ R) = ∑ j ∈ s, (f j : Fin d → MvPowerSeries τ R)` using `fun s f => map_sum A.subtype f s`.

Establish `hL : γ (∑ m, x m) (∑ m, y m) = c`. Simplify using `only [γ]`. Rewrite using `[coeA, coeA]`. Simplify using `only [x, y]`. Rewrite using `[Finset.univ_sum_single (fun m => (X (Sum.inl m) : MvPowerSeries τ R)), Finset.univ_sum_single (fun m => (X (Sum.inr m) : MvPowerSeries τ R))]`.

Unfold `at2`. Establish `: Sum.elim (fun m => (X (Sum.inl m) : MvPowerSeries τ R)) (fun m => X (Sum.inr m)) = X`. Apply the tactic sequence `funext t; cases t <;> rfl`. Rewrite using `[this, subst_self]`. Both sides reduce to the same expression.

Establish `hT : ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) - (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) - ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) = cob1 (addLaw R d) (corr R c)`. Unfold `cob1 inL inR`. Rewrite using `[subst_corr (fun i => by simp [addLaw]), subst_corr (fun i => by simp), subst_corr (fun i => by simp)]`. Simplify using `only [γ, coeA]`. Simplify using `only [x, y, AddSubgroup.coe_add, ← Pi.single_add]`.

Both sides reduce to the same expression. Use `⟨corr R c, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem symmetricCocycle_additive_eq_coboundary_add_alt (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : IsCoc (addLaw R d) c) (h0 : constantCoeff c = 0) :
    ∃ b : MvPowerSeries (Fin d) R, c = cob1 (addLaw R d) b +
      ∑ m : Fin d, at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (Pi.single m (X (Sum.inr m))) := by
  classical
  let τ := Fin d ⊕ Fin d
  let A := PtGrp R d τ
  let γ : A → A → MvPowerSeries τ R := fun u v => at2 c u.1 v.1
  have hsymm : ∀ u v, γ u v = γ v u := by
    intro u v
    have hX1 : ∀ i, constantCoeff ((fun i => (X (Sum.inr i) : MvPowerSeries τ R)) i) = 0 :=
      fun i => by simp
    have hX2 : ∀ i, constantCoeff ((fun i => (X (Sum.inl i) : MvPowerSeries τ R)) i) = 0 :=
      fun i => by simp
    have huv : ∀ t, constantCoeff (Sum.elim u.1 v.1 t) = 0 := fun t => by
      cases t with
      | inl t => exact u.2 t
      | inr t => exact v.2 t
    have := subst_powerSeriesEvalTwoGroups hX1 hX2 huv c
    change at2 (swap c) u.1 v.1 = _ at this
    rw [hc.2] at this
    simp only [γ]
    rw [this]
    have hS : HasSubst (Sum.elim u.1 v.1) := hasSubst_of_constantCoeff_zero huv
    congr 1 <;> funext i <;> rw [subst_X hS] <;> rfl
  have hcoc : ∀ x y z : A, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0 :=
    fun x y z => coc_at hc.1 x.2 y.2 z.2
  have hzero : γ 0 0 = 0 := by
    simp only [γ]
    unfold at2
    have : Sum.elim ((0 : A) : Fin d → MvPowerSeries τ R) ((0 : A) : Fin d → MvPowerSeries τ R) =
        fun _ => 0 := by funext t; cases t <;> rfl
    rw [this, subst_zeroPt, h0, map_zero]
  let x : Fin d → A := fun m => ⟨Pi.single m (X (Sum.inl m)), fun i => by
    rw [Pi.single_apply]; split_ifs <;> simp⟩
  let y : Fin d → A := fun m => ⟨Pi.single m (X (Sum.inr m)), fun i => by
    rw [Pi.single_apply]; split_ifs <;> simp⟩
  have key := GlobalTheory.T.symmCocycle_apply_finset_sum A (MvPowerSeries τ R) γ hsymm hcoc hzero d x y
  have coeA : ∀ (s : Finset (Fin d)) (f : Fin d → A),
      ((∑ j ∈ s, f j : A) : Fin d → MvPowerSeries τ R) = ∑ j ∈ s, (f j : Fin d → MvPowerSeries τ R) :=
    fun s f => map_sum A.subtype f s
  have hL : γ (∑ m, x m) (∑ m, y m) = c := by
    simp only [γ]
    rw [coeA, coeA]
    simp only [x, y]
    rw [Finset.univ_sum_single (fun m => (X (Sum.inl m) : MvPowerSeries τ R)),
      Finset.univ_sum_single (fun m => (X (Sum.inr m) : MvPowerSeries τ R))]
    unfold at2
    have : Sum.elim (fun m => (X (Sum.inl m) : MvPowerSeries τ R)) (fun m => X (Sum.inr m)) = X := by
      funext t; cases t <;> rfl
    rw [this, subst_self]; rfl
  have hT : ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) -
      (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) -
      ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) = cob1 (addLaw R d) (corr R c) := by
    unfold cob1 inL inR
    rw [subst_corr (fun i => by simp [addLaw]), subst_corr (fun i => by simp),
      subst_corr (fun i => by simp)]
    simp only [γ, coeA]
    simp only [x, y, AddSubgroup.coe_add, ← Pi.single_add]
    rfl
  refine ⟨corr R c, ?_⟩
  calc c = γ (∑ m, x m) (∑ m, y m) := hL.symm
    _ = _ := key
    _ = _ := by rw [hT, add_comm]

end GlobalTheory
