import Mathlib

namespace GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)

def stab (x : V) : Subgroup L where
  carrier := {l | π (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_stab {x : V} {l : L} : l ∈ stab π L x ↔ π (l : G) x = x := Iff.rfl

noncomputable def cv (H : Subgroup L) (x : V) (q : L ⧸ H) : V := π ((q.out : L) : G) x

/- English proof (translation)
Unfold `cv`. Use `set b : L := (QuotientGroup.mk a : L ⧸ H).out with hb`. Establish `h1 : (QuotientGroup.mk b : L ⧸ H) = QuotientGroup.mk a` using `QuotientGroup.out_eq' _`. Establish `h2 : b⁻¹ * a ∈ H` using `QuotientGroup.eq.mp h1`. Establish `h3` using `(mem_stab π L).mp (hH h2)`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply] at h3`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem cv_mk {H : Subgroup L} {x : V} (hH : H ≤ stab π L x) (a : L) :
    cv π L H x (QuotientGroup.mk a) = π (a : G) x := by
  unfold cv
  set b : L := (QuotientGroup.mk a : L ⧸ H).out with hb
  have h1 : (QuotientGroup.mk b : L ⧸ H) = QuotientGroup.mk a := QuotientGroup.out_eq' _
  have h2 : b⁻¹ * a ∈ H := QuotientGroup.eq.mp h1
  have h3 := (mem_stab π L).mp (hH h2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply] at h3
  calc π (b : G) x = π (b : G) (π (b : G)⁻¹ (π (a : G) x)) := by rw [h3]
    _ = π (a : G) x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

noncomputable def avgH (H : Subgroup L) (x : V) : V :=
  ((H.index : ℂ))⁻¹ • ∑ᶠ q : L ⧸ H, cv π L H x q

/- English proof (translation)
Use `haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le hle`. Establish `hrel` using `Subgroup.relIndex_mul_index hle`. Use `haveI : (H'.subgroupOf H).FiniteIndex := by`. Use `⟨?_⟩` and prove the remaining obligations. Introduce `h0`.

Establish `h4 : H'.index = 0` using `by rw [← hrel]; simp [Subgroup.relIndex, h0]`. Conclude with `Subgroup.FiniteIndex.index_ne_zero h4`. Use `haveI := Fintype.ofFinite (L ⧸ H)`. Use `haveI := Fintype.ofFinite (L ⧸ H')`. Use `haveI := Fintype.ofFinite (H ⧸ H'.subgroupOf H)`.

Unfold `avgH`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`. Set `e` to `Subgroup.quotientEquivProdOfLE hle`. Establish `hcv : ∀ q : L ⧸ H', cv π L H' x q = cv π L H x (e q).1`. Introduce `q`.

Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H a`. Rewrite using `[cv_mk π L (le_trans hle hH), show (e (QuotientGroup.mk a)).1 = QuotientGroup.mk a from rfl, cv_mk π L hH]`. Establish `hsum : ∑ q : L ⧸ H', cv π L H' x q = (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) • ∑ q : L ⧸ H, cv π L H x q`. Repeatedly rewrite using `[hcv]`.

Rewrite using `[Equiv.sum_comp e (fun p => cv π L H x p.1), Fintype.sum_prod_type]`. Simplify using `only [Finset.sum_const, Finset.card_univ]`. Rewrite using `[Finset.smul_sum]`. Simplify using `[Nat.cast_smul_eq_nsmul]`. Establish `hc : Fintype.card (H ⧸ H'.subgroupOf H) = H'.relIndex H`.

Rewrite using `[Fintype.card_eq_nat_card]`. Both sides reduce to the same expression. Rewrite using `[hsum, hc, ← hrel, smul_smul]`. Use `congr 1`. Establish `h5 : (H'.relIndex H : ℂ) ≠ 0`.

Use `Subgroup.FiniteIndex.index_ne_zero (H := H'.subgroupOf H)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem avgH_refine {H H' : Subgroup L} {x : V} (hle : H' ≤ H) (hH : H ≤ stab π L x)
    [H'.FiniteIndex] : avgH π L H' x = avgH π L H x := by
  classical
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hrel := Subgroup.relIndex_mul_index hle
  haveI : (H'.subgroupOf H).FiniteIndex := by
    refine ⟨?_⟩
    intro h0
    have h4 : H'.index = 0 := by rw [← hrel]; simp [Subgroup.relIndex, h0]
    exact Subgroup.FiniteIndex.index_ne_zero h4
  haveI := Fintype.ofFinite (L ⧸ H)
  haveI := Fintype.ofFinite (L ⧸ H')
  haveI := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  unfold avgH
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let e := Subgroup.quotientEquivProdOfLE hle
  have hcv : ∀ q : L ⧸ H', cv π L H' x q = cv π L H x (e q).1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L (le_trans hle hH), show (e (QuotientGroup.mk a)).1 = QuotientGroup.mk a from rfl,
        cv_mk π L hH]
  have hsum : ∑ q : L ⧸ H', cv π L H' x q =
      (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) • ∑ q : L ⧸ H, cv π L H x q := by
    simp_rw [hcv]
    rw [Equiv.sum_comp e (fun p => cv π L H x p.1), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [Finset.smul_sum]
    simp [Nat.cast_smul_eq_nsmul]
  have hc : Fintype.card (H ⧸ H'.subgroupOf H) = H'.relIndex H := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hsum, hc, ← hrel, smul_smul]
  congr 1
  have h5 : (H'.relIndex H : ℂ) ≠ 0 := by
    have := Subgroup.FiniteIndex.index_ne_zero (H := H'.subgroupOf H)
    exact_mod_cast this
  push_cast
  field_simp

/- English proof (translation)
Use `haveI : Finite (Set.range fun l : L => π (l : G) x) := hx.to_subtype`. Set `F : L ⧸ stab π L x → Set.range fun l : L => π (l : G) x` to `fun q => ⟨cv π L (stab π L x) x q, ⟨_, rfl⟩⟩`. Establish `hF : Function.Injective F`. Introduce `q1 q2 h`. Proceed by induction on `q1 using QuotientGroup.induction_on with`.

Consider the case `H a`. Proceed by induction on `q2 using QuotientGroup.induction_on with`. Consider the case `H b`. Establish `h' : π (a : G) x = π (b : G) x`. Use `congrArg Subtype.val h` as an intermediate fact.

Simplify `this` using `only [F, cv_mk π L le_rfl]`. Apply `QuotientGroup.eq.mpr` to reduce the goal to its premises. Rewrite using `[mem_stab]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply, ← h']`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Use `haveI : Finite (L ⧸ stab π L x) := Finite.of_injective F hF`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
theorem stab_finiteIndex {x : V} (hx : (Set.range fun l : L => π (l : G) x).Finite) :
    (stab π L x).FiniteIndex := by
  haveI : Finite (Set.range fun l : L => π (l : G) x) := hx.to_subtype
  let F : L ⧸ stab π L x → Set.range fun l : L => π (l : G) x :=
    fun q => ⟨cv π L (stab π L x) x q, ⟨_, rfl⟩⟩
  have hF : Function.Injective F := by
    intro q1 q2 h
    induction q1 using QuotientGroup.induction_on with
    | H a =>
    induction q2 using QuotientGroup.induction_on with
    | H b =>
    have h' : π (a : G) x = π (b : G) x := by
      have := congrArg Subtype.val h
      simpa only [F, cv_mk π L le_rfl] using this
    apply QuotientGroup.eq.mpr
    rw [mem_stab]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply, ← h']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  haveI : Finite (L ⧸ stab π L x) := Finite.of_injective F hF
  exact Subgroup.finiteIndex_of_finite_quotient

/- English proof (translation)
Introduce `l hl`. Rewrite using `[mem_stab, map_add, (mem_stab π L).mp hl.1, (mem_stab π L).mp hl.2]`.
-/
theorem stab_le_add (x y : V) : stab π L x ⊓ stab π L y ≤ stab π L (x + y) := by
  intro l hl
  rw [mem_stab, map_add, (mem_stab π L).mp hl.1, (mem_stab π L).mp hl.2]

/- English proof (translation)
Introduce `l hl`. Rewrite using `[mem_stab, map_smul, (mem_stab π L).mp hl]`.
-/
theorem stab_le_smul (c : ℂ) (x : V) : stab π L x ≤ stab π L (c • x) := by
  intro l hl
  rw [mem_stab, map_smul, (mem_stab π L).mp hl]

/- English proof (translation)
Use `haveI := Fintype.ofFinite (L ⧸ H)`. Unfold `avgH cv`. Simplify using `only [finsum_eq_sum_of_fintype, map_add, Finset.sum_add_distrib, smul_add]`.
-/
theorem avgH_add (H : Subgroup L) [H.FiniteIndex] (x y : V) :
    avgH π L H (x + y) = avgH π L H x + avgH π L H y := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_add, Finset.sum_add_distrib, smul_add]

/- English proof (translation)
Use `haveI := Fintype.ofFinite (L ⧸ H)`. Unfold `avgH cv`. Simplify using `only [finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum, smul_comm c]`.
-/
theorem avgH_smul (H : Subgroup L) [H.FiniteIndex] (c : ℂ) (x : V) :
    avgH π L H (c • x) = c • avgH π L H x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum, smul_comm c]

noncomputable def avg (x : V) : V := avgH π L (stab π L x) x

/- English proof (translation)
The claim follows from `(avgH_refine π L hH le_rfl).symm`.
-/
theorem avg_eq {H : Subgroup L} {x : V} [H.FiniteIndex] (hH : H ≤ stab π L x) :
    avg π L x = avgH π L H x := (avgH_refine π L hH le_rfl).symm

/- English proof (translation)
Use `haveI := Fintype.ofFinite (L ⧸ H)`. Unfold `avgH`. Rewrite using `[finsum_eq_sum_of_fintype]`. Conclude with `D.smul_mem _ (D.sum_mem fun q _ => hD _ (q.out).2 x hx)`.
-/
theorem avgH_mem (D : Submodule ℂ V) (hD : ∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) (H : Subgroup L)
    [H.FiniteIndex] {x : V} (hx : x ∈ D) : avgH π L H x ∈ D := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH
  rw [finsum_eq_sum_of_fintype]
  exact D.smul_mem _ (D.sum_mem fun q _ => hD _ (q.out).2 x hx)

/- English proof (translation)
Use `haveI := Fintype.ofFinite (L ⧸ stab π L x)`. Unfold `avg avgH`. Establish `: ∀ q : L ⧸ stab π L x, cv π L (stab π L x) x q = x` using `fun q => hfix _ (q.out).2`. Simplify using `only [finsum_eq_sum_of_fintype, this, Finset.sum_const, Finset.card_univ]`. Rewrite using `[Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`.

Establish `h0 : ((stab π L x).index : ℂ) ≠ 0` using `by exact_mod_cast hx.index_ne_zero`. Rewrite using `[show Nat.card (L ⧸ stab π L x) = (stab π L x).index from rfl, inv_mul_cancel₀ h0, one_smul]`.
-/
theorem avg_fixed {x : V} (hx : (stab π L x).FiniteIndex) (hfix : ∀ l ∈ L, π l x = x) :
    avg π L x = x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH
  have : ∀ q : L ⧸ stab π L x, cv π L (stab π L x) x q = x := fun q => hfix _ (q.out).2
  simp only [finsum_eq_sum_of_fintype, this, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h0 : ((stab π L x).index : ℂ) ≠ 0 := by exact_mod_cast hx.index_ne_zero
  rw [show Nat.card (L ⧸ stab π L x) = (stab π L x).index from rfl, inv_mul_cancel₀ h0, one_smul]

/- English proof (translation)
Use `haveI := Fintype.ofFinite (L ⧸ stab π L x)`. Unfold `avg avgH`. Rewrite using `[finsum_eq_sum_of_fintype, map_smul, map_sum]`. Use `congr 1`. Establish `h : ∀ q : L ⧸ stab π L x, π (l : G) (cv π L (stab π L x) x q) = cv π L (stab π L x) x (l • q)`.

Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H a`. Rewrite using `[cv_mk π L le_rfl, MulAction.Quotient.smul_mk, cv_mk π L le_rfl, smul_eq_mul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]`. Repeatedly rewrite using `[h]`.

Conclude with `Equiv.sum_comp (MulAction.toPerm l) (cv π L (stab π L x) x)`.
-/
theorem avg_invariant {x : V} (hx : (stab π L x).FiniteIndex) (l : L) :
    π (l : G) (avg π L x) = avg π L x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH
  rw [finsum_eq_sum_of_fintype, map_smul, map_sum]
  congr 1
  have h : ∀ q : L ⧸ stab π L x, π (l : G) (cv π L (stab π L x) x q) =
      cv π L (stab π L x) x (l • q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L le_rfl, MulAction.Quotient.smul_mk, cv_mk π L le_rfl, smul_eq_mul, Subgroup.coe_mul, map_mul,
        Module.End.mul_apply]
  simp_rw [h]
  exact Equiv.sum_comp (MulAction.toPerm l) (cv π L (stab π L x) x)

/- English proof (translation)
Use `haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance`. Rewrite using `[avg_eq π L (stab_le_add π L x y), avg_eq π L (inf_le_left : stab π L x ⊓ stab π L y ≤ stab π L x), avg_eq π L (inf_le_right : stab π L x ⊓ stab π L y ≤ stab π L y), avgH_add]`.
-/
theorem avg_add {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    avg π L (x + y) = avg π L x + avg π L y := by
  haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance
  rw [avg_eq π L (stab_le_add π L x y), avg_eq π L (inf_le_left : stab π L x ⊓ stab π L y ≤ stab π L x),
    avg_eq π L (inf_le_right : stab π L x ⊓ stab π L y ≤ stab π L y), avgH_add]

/- English proof (translation)
Rewrite using `[avg_eq π L (stab_le_smul π L c x), avgH_smul]`. Both sides reduce to the same expression.
-/
theorem avg_smul {x : V} (hx : (stab π L x).FiniteIndex) (c : ℂ) :
    avg π L (c • x) = c • avg π L x := by
  rw [avg_eq π L (stab_le_smul π L c x), avgH_smul]
  rfl

/- English proof (translation)
Use `set N := (stab π L x ⊓ stab π L y).normalCore with hN`. Establish `hNx : N ≤ stab π L x` using `le_trans (Subgroup.normalCore_le _) inf_le_left`. Establish `hNy : N ≤ stab π L y` using `le_trans (Subgroup.normalCore_le _) inf_le_right`. Use `haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance`. Use `haveI : N.FiniteIndex := Subgroup.finiteIndex_normalCore _`.

Use `haveI := Fintype.ofFinite (L ⧸ N)`. Set `r : L ⧸ N → G` to `fun q => ((q.out : L) : G)`. Establish `hr : Function.Injective r`. Introduce `q1 q2 h`. Establish `h1 : q1.out = q2.out` using `Subtype.ext h`.

Rewrite using `[← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, h1]`. Set `s : Finset G` to `Finset.univ.image r`. Establish `hcard : s.card = N.index`. Rewrite using `[Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_eq_nat_card]`. Both sides reduce to the same expression.

Establish `hsum : ∀ z : V, N ≤ stab π L z → avg π L z = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g z`. Introduce `z hz`. Establish `hzf : (stab π L z).FiniteIndex` using `Subgroup.finiteIndex_of_le hz`. Rewrite using `[avg_eq π L hz, hcard, Finset.sum_image (fun a _ b _ h => hr h)]`. Unfold `avgH`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Both sides reduce to the same expression. Set `f : G → G` to `fun g => if h : g ∈ L then (((((QuotientGroup.mk (⟨g, h⟩ : L) : L ⧸ N))⁻¹).out : L) : G) else g`. Establish `hf : ∀ q : L ⧸ N, f (r q) = r q⁻¹`. Introduce `q`.

Simplify using `only [f, r, Subtype.coe_eta, QuotientGroup.out_eq']`. Rewrite using `[dif_pos (q.out).2]`. Establish `hmem : ∀ g, g ∈ s ↔ ∃ q, r q = g`. Introduce `g`. Simplify using `[s]`.

Use `⟨s, f, ?_, ?_, hsum x hNx, hsum y hNy, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨r 1, (hmem _).mpr ⟨1, rfl⟩⟩`. Introduce `g hg`. Take `⟨q, rfl⟩` from `(hmem g).mp hg`. Conclude with `(q.out).2`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨q, rfl⟩` from `(hmem g).mp hg`. Rewrite using `[Finset.mem_coe, hf]`. Conclude with `(hmem _).mpr ⟨_, rfl⟩`.

Introduce `g1 hg1 g2 hg2 h`. Take `⟨q1, rfl⟩` from `(hmem g1).mp hg1`. Take `⟨q2, rfl⟩` from `(hmem g2).mp hg2`. Rewrite `h` using `[hf, hf]`. Rewrite using `[inv_injective (hr h)]`.

Introduce `g hg`. Take `⟨q, rfl⟩` from `(hmem g).mp hg`. Use `⟨r q⁻¹, (hmem _).mpr ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, inv_inv]`. Introduce `g hg`.

Take `⟨q, rfl⟩` from `(hmem g).mp hg`. Rewrite using `[hf]`. Establish `e1 : π (r q⁻¹) y = cv π L N y q⁻¹` using `rfl`. Establish `e2 : π (r q)⁻¹ y = cv π L N y (QuotientGroup.mk (q.out)⁻¹)`. Rewrite using `[cv_mk π L hNy]`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, QuotientGroup.mk_inv, QuotientGroup.out_eq']`.
-/
theorem avg_pair {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧
      avg π L x = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g x ∧
      avg π L y = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g y ∧
      Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ y = π (f g) y := by
  classical
  set N := (stab π L x ⊓ stab π L y).normalCore with hN
  have hNx : N ≤ stab π L x := le_trans (Subgroup.normalCore_le _) inf_le_left
  have hNy : N ≤ stab π L y := le_trans (Subgroup.normalCore_le _) inf_le_right
  haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance
  haveI : N.FiniteIndex := Subgroup.finiteIndex_normalCore _
  haveI := Fintype.ofFinite (L ⧸ N)
  let r : L ⧸ N → G := fun q => ((q.out : L) : G)
  have hr : Function.Injective r := by
    intro q1 q2 h
    have h1 : q1.out = q2.out := Subtype.ext h
    rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, h1]
  let s : Finset G := Finset.univ.image r
  have hcard : s.card = N.index := by
    rw [Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_eq_nat_card]; rfl
  have hsum : ∀ z : V, N ≤ stab π L z → avg π L z = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g z := by
    intro z hz
    have hzf : (stab π L z).FiniteIndex := Subgroup.finiteIndex_of_le hz
    rw [avg_eq π L hz, hcard, Finset.sum_image (fun a _ b _ h => hr h)]
    unfold avgH
    rw [finsum_eq_sum_of_fintype]
    rfl
  let f : G → G := fun g => if h : g ∈ L then
    (((((QuotientGroup.mk (⟨g, h⟩ : L) : L ⧸ N))⁻¹).out : L) : G) else g
  have hf : ∀ q : L ⧸ N, f (r q) = r q⁻¹ := by
    intro q
    simp only [f, r, Subtype.coe_eta, QuotientGroup.out_eq']
    rw [dif_pos (q.out).2]
  have hmem : ∀ g, g ∈ s ↔ ∃ q, r q = g := by
    intro g; simp [s]
  refine ⟨s, f, ?_, ?_, hsum x hNx, hsum y hNy, ?_, ?_⟩
  · exact ⟨r 1, (hmem _).mpr ⟨1, rfl⟩⟩
  · intro g hg
    obtain ⟨q, rfl⟩ := (hmem g).mp hg
    exact (q.out).2
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨q, rfl⟩ := (hmem g).mp hg
      rw [Finset.mem_coe, hf]
      exact (hmem _).mpr ⟨_, rfl⟩
    · intro g1 hg1 g2 hg2 h
      obtain ⟨q1, rfl⟩ := (hmem g1).mp hg1
      obtain ⟨q2, rfl⟩ := (hmem g2).mp hg2
      rw [hf, hf] at h
      rw [inv_injective (hr h)]
    · intro g hg
      obtain ⟨q, rfl⟩ := (hmem g).mp hg
      refine ⟨r q⁻¹, (hmem _).mpr ⟨_, rfl⟩, ?_⟩
      rw [hf, inv_inv]
  · intro g hg
    obtain ⟨q, rfl⟩ := (hmem g).mp hg
    rw [hf]
    have e1 : π (r q⁻¹) y = cv π L N y q⁻¹ := rfl
    have e2 : π (r q)⁻¹ y = cv π L N y (QuotientGroup.mk (q.out)⁻¹) := by
      rw [cv_mk π L hNy]; rfl
    rw [e1, e2, QuotientGroup.mk_inv, QuotientGroup.out_eq']

end GlobalTheory.OrbitAvg

open GlobalTheory.OrbitAvg in

/- English proof (translation)
Introduce `G V _ _ _ π L D hD hfin`. Establish `hfi : ∀ x : D, (stab π L (x : V)).FiniteIndex` using `fun x => stab_finiteIndex π L (hfin x x.2)`. Set `P : D →ₗ[ℂ] D` to `{ toFun := fun x => ⟨avg π L (x : V), by haveI := hfi x`. Conclude with `avgH_mem π L D hD _ x.2⟩`. Use the proof step `map_add' := fun x y => Subtype.ext (avg_add π L (hfi x) (hfi y))`.

Use the proof step `map_smul' := fun c x => Subtype.ext (avg_smul π L (hfi x) c) }`. Use `⟨P, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `Subtype.ext (avg_fixed π L (hfi x) fun l hl => hx l hl)`. Introduce `x l hl`.

Conclude with `avg_invariant π L (hfi x) ⟨l, hl⟩`. Introduce `x y`. Conclude with `avg_pair π L (hfi x) (hfi y)`.
-/
theorem GlobalTheory.orbitAverage_exists : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (π : G →* Module.End ℂ V) (L : Subgroup G) (D : Submodule ℂ V),
    (∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) → (∀ x ∈ D, (Set.range fun l : L => π (l : G) x).Finite) →
    ∃ P : D →ₗ[ℂ] D, (∀ x : D, (∀ l ∈ L, π l (x : V) = x) → P x = x) ∧
      (∀ x : D, ∀ l ∈ L, π l (P x : V) = P x) ∧
      ∀ x y : D, ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧
        (P x : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (x : V) ∧
        (P y : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (y : V) ∧
        Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ (y : V) = π (f g) (y : V) := by
  intro G V _ _ _ π L D hD hfin
  have hfi : ∀ x : D, (stab π L (x : V)).FiniteIndex := fun x => stab_finiteIndex π L (hfin x x.2)
  let P : D →ₗ[ℂ] D :=
    { toFun := fun x => ⟨avg π L (x : V), by
        haveI := hfi x
        exact avgH_mem π L D hD _ x.2⟩
      map_add' := fun x y => Subtype.ext (avg_add π L (hfi x) (hfi y))
      map_smul' := fun c x => Subtype.ext (avg_smul π L (hfi x) c) }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x hx
    exact Subtype.ext (avg_fixed π L (hfi x) fun l hl => hx l hl)
  · intro x l hl
    exact avg_invariant π L (hfi x) ⟨l, hl⟩
  · intro x y
    exact avg_pair π L (hfi x) (hfi y)
