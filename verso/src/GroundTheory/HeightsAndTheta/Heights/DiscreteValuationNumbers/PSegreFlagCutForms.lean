import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutForms
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionFormsTools
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor

noncomputable section

set_option linter.unusedSectionVars false

namespace SegreFlagCutForms

open FlagBundleSectionForms (chartPow chartPow_ne_zero)

section Dual

variable {R : Type} [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N : ℕ} {E : Type} [AddCommGroup E]
  [Module Ω E]

/- English proof (translation)
Establish `hY : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ _)`. Establish `hp : ∀ j, chartPow y c (b j) ≠ 0` using `fun j => chartPow_ne_zero hY _`. Establish `hgr : ∀ (j : Fin N) (s : Ω), (∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧ w.repr v j = s) ↔ ∃ r ∈ chartRing R (segreVec y) c, s = r * chartPow y c (b j)` using `fun j s => by`. Establish `h` using `hfl.graded c hc j`. Rewrite `h` using `[Set.ext_iff]`.

Conclude with `h s`. Establish `he : ∀ j : Fin N, ∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧ w.repr v j = chartPow y c (b j)` using `fun j => (hgr j _).2 ⟨1, one_mem _, (one_mul _).symm⟩`. Use `choose e heL heT heD using he`. Establish `hx : ∀ j : Fin N, e j - chartPow y c (b j) • w j ∈ Submodule.span Ω (w '' {m | (m : ℕ) < j})`. Introduce `j`.

Rewrite using `[w.mem_span_image]`. Introduce `m hm`. Simplify using `only [Finset.mem_coe, Finsupp.mem_support_iff] at hm`. Simplify using `only [Set.mem_setOf_eq]`. Assume the negation of the conclusion as `hjm`.

Use `push_neg at hjm`. Apply `hm` to reduce the goal to its premises. Break down `hjm.lt_or_eq with h | h` into its components or cases. Establish `hne : j ≠ m` using `fun h' => (ne_of_lt h) (congrArg Fin.val h')`. Simplify using `[heT j m h, Finsupp.single_apply, hne]`.

Establish `: m = j` using `Fin.ext h.symm`. Substitute `this` using the available equality. Simplify using `[heD]`. Establish `hspan : ∀ m ≤ N, Submodule.span Ω (e '' {j | (j : ℕ) < m}) = Submodule.span Ω (w '' {j | (j : ℕ) < m})`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `hm`.

Establish `hS : {j : Fin N | (j : ℕ) < m + 1} = insert (⟨m, hm⟩ : Fin N) {j : Fin N | (j : ℕ) < m}`. Use extensionality with `j`. Simplify using `only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hS, Set.image_insert_eq, Set.image_insert_eq, Submodule.span_insert, Submodule.span_insert, ih (by omega)]`.

Establish `hxm` using `hx ⟨m, hm⟩`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ le_sup_right` and prove the remaining obligations. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Use `Submodule.add_mem_sup (Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩)) (Submodule.mem_span_singleton_self (w ⟨m, hm⟩))) hxm` as an intermediate fact.

Simplify using `using this`. Use `sup_le ?_ le_sup_right` and prove the remaining obligations. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Use `Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩))⁻¹ (Submodule.sub_mem_sup (Submodule.mem_span_singleton_self (e ⟨m, hm⟩)) hxm)` as an intermediate fact. Simplify `this` using `[smul_smul, inv_mul_cancel₀ (hp _)]`.

Establish `htop : ⊤ ≤ Submodule.span Ω (Set.range e)`. Establish `h` using `hspan N le_rfl`. Establish `hu : {j : Fin N | (j : ℕ) < N} = Set.univ` using `Set.eq_univ_of_forall fun j => j.isLt`. Rewrite `h` using `[hu, Set.image_univ, Set.image_univ, w.span_eq]`. Rewrite using `[h]`.

Establish `hli : LinearIndependent Ω e` using `linearIndependent_of_top_le_span_of_card_eq_finrank htop (by rw [Module.finrank_eq_card_basis w])`. Set `eb` to `Module.Basis.mk hli htop`. Establish `heb : ⇑eb = e` using `funext (Module.Basis.mk_apply hli htop)`. Establish `hvan : ∀ x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}), eb.repr x i = 0`. Introduce `x hx'`.

Rewrite `hx'` using `[← hspan i i.isLt.le, ← heb, eb.mem_span_image]`. Assume the negation of the conclusion as `h`. Conclude with `lt_irrefl (i : ℕ) (hx' (Finsupp.mem_support_iff.2 h))`. Establish `hself : ∀ j m, eb.repr (e j) m = Finsupp.single j 1 m` using `fun j m => by`. Rewrite using `[← heb, eb.repr_self]`.

Establish `hint : ∀ m ≤ N, ∀ v ∈ B.lat c, (∀ j : Fin N, m ≤ (j : ℕ) → w.repr v j = 0) → ∀ j, eb.repr v j ∈ chartRing R (segreVec y) c`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `_ v _ hv j`.

Establish `: v = 0` using `w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])`. Simplify using `[this]`. Consider the case `succ m ih`. Introduce `hm v hvL hv j`. Take `⟨r, hr, hrv⟩` from `(hgr ⟨m, hm⟩ (w.repr v ⟨m, hm⟩)).1 ⟨v, hvL, fun j hj => hv j hj, rfl⟩`.

Establish `hv' : v - r • e ⟨m, hm⟩ ∈ B.lat c` using `sub_mem hvL (B.stable c r hr _ (heL _))`. Establish `h'` using `ih (by omega) _ hv' (by`. Introduce `j hj`. Break down `hj.lt_or_eq with h | h` into its components or cases. Simplify using `[hv j h, heT ⟨m, hm⟩ j h]`.

Establish `: j = ⟨m, hm⟩` using `Fin.ext h.symm`. Substitute `this` using the available equality. Simplify using `[heD, hrv])`. Establish `hsplit : eb.repr v j = eb.repr (v - r • e ⟨m, hm⟩) j + r * eb.repr (e ⟨m, hm⟩) j`. Rewrite using `[map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel]`.

Rewrite using `[hsplit, hself]`. Use `add_mem (h' j) (mul_mem hr ?_)` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Use `⟨eb.coord i, fun v hv => ?_, fun j hj => ?_, ?_⟩` and prove the remaining obligations. Conclude with `hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)) i`. Conclude with `hvan _ (Submodule.subset_span ⟨j, hj, rfl⟩)`. Establish `hw : w i = (chartPow y c (b i))⁻¹ • (e i - (e i - chartPow y c (b i) • w i))`.

Rewrite using `[sub_sub_cancel, smul_smul, inv_mul_cancel₀ (hp i), one_smul]`. Rewrite using `[Module.Basis.coord_apply, hw, map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply, hself, hvan _ (hx i)]`. Simplify using the standard rewrite rules.
-/
theorem exists_flag_dual (y : (Σ k, ι k) → Ω) (B : ChartBundle R (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b)
    (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing R (segreVec y) c) ∧
      (∀ j, j < i → ψ (w j) = 0) ∧ ψ (w i) = (chartPow y c (b i))⁻¹ := by
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ _)
  have hp : ∀ j, chartPow y c (b j) ≠ 0 := fun j => chartPow_ne_zero hY _
  have hgr : ∀ (j : Fin N) (s : Ω), (∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧ w.repr v j = s) ↔
      ∃ r ∈ chartRing R (segreVec y) c, s = r * chartPow y c (b j) := fun j s => by
    have h := hfl.graded c hc j
    rw [Set.ext_iff] at h
    exact h s
  have he : ∀ j : Fin N, ∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧
      w.repr v j = chartPow y c (b j) := fun j =>
    (hgr j _).2 ⟨1, one_mem _, (one_mul _).symm⟩
  choose e heL heT heD using he

  have hx : ∀ j : Fin N, e j - chartPow y c (b j) • w j ∈
      Submodule.span Ω (w '' {m | (m : ℕ) < j}) := by
    intro j
    rw [w.mem_span_image]
    intro m hm
    simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hm
    simp only [Set.mem_setOf_eq]
    by_contra hjm
    push_neg at hjm
    apply hm
    rcases hjm.lt_or_eq with h | h
    · have hne : j ≠ m := fun h' => (ne_of_lt h) (congrArg Fin.val h')
      simp [heT j m h, Finsupp.single_apply, hne]
    · have : m = j := Fin.ext h.symm
      subst this
      simp [heD]
  have hspan : ∀ m ≤ N, Submodule.span Ω (e '' {j | (j : ℕ) < m}) =
      Submodule.span Ω (w '' {j | (j : ℕ) < m}) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hS : {j : Fin N | (j : ℕ) < m + 1} = insert (⟨m, hm⟩ : Fin N) {j : Fin N | (j : ℕ) < m} := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hS, Set.image_insert_eq, Set.image_insert_eq, Submodule.span_insert, Submodule.span_insert,
        ih (by omega)]
      have hxm := hx ⟨m, hm⟩
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.add_mem_sup
          (Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩)) (Submodule.mem_span_singleton_self (w ⟨m, hm⟩)))
          hxm
        simpa using this
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩))⁻¹ (Submodule.sub_mem_sup
          (Submodule.mem_span_singleton_self (e ⟨m, hm⟩)) hxm)
        simpa [smul_smul, inv_mul_cancel₀ (hp _)] using this
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    have h := hspan N le_rfl
    have hu : {j : Fin N | (j : ℕ) < N} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
    rw [hu, Set.image_univ, Set.image_univ, w.span_eq] at h
    rw [h]
  have hli : LinearIndependent Ω e :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by rw [Module.finrank_eq_card_basis w])
  let eb := Module.Basis.mk hli htop
  have heb : ⇑eb = e := funext (Module.Basis.mk_apply hli htop)
  have hvan : ∀ x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}), eb.repr x i = 0 := by
    intro x hx'
    rw [← hspan i i.isLt.le, ← heb, eb.mem_span_image] at hx'
    by_contra h
    exact lt_irrefl (i : ℕ) (hx' (Finsupp.mem_support_iff.2 h))
  have hself : ∀ j m, eb.repr (e j) m = Finsupp.single j 1 m := fun j m => by
    rw [← heb, eb.repr_self]
  have hint : ∀ m ≤ N, ∀ v ∈ B.lat c, (∀ j : Fin N, m ≤ (j : ℕ) → w.repr v j = 0) →
      ∀ j, eb.repr v j ∈ chartRing R (segreVec y) c := by
    intro m
    induction m with
    | zero =>
      intro _ v _ hv j
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ m ih =>
      intro hm v hvL hv j
      obtain ⟨r, hr, hrv⟩ := (hgr ⟨m, hm⟩ (w.repr v ⟨m, hm⟩)).1 ⟨v, hvL, fun j hj => hv j hj, rfl⟩
      have hv' : v - r • e ⟨m, hm⟩ ∈ B.lat c := sub_mem hvL (B.stable c r hr _ (heL _))
      have h' := ih (by omega) _ hv' (by
        intro j hj
        rcases hj.lt_or_eq with h | h
        · simp [hv j h, heT ⟨m, hm⟩ j h]
        · have : j = ⟨m, hm⟩ := Fin.ext h.symm
          subst this
          simp [heD, hrv])
      have hsplit : eb.repr v j = eb.repr (v - r • e ⟨m, hm⟩) j + r * eb.repr (e ⟨m, hm⟩) j := by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel]
      rw [hsplit, hself]
      refine add_mem (h' j) (mul_mem hr ?_)
      rw [Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine ⟨eb.coord i, fun v hv => ?_, fun j hj => ?_, ?_⟩
  · exact hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)) i
  · exact hvan _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · have hw : w i = (chartPow y c (b i))⁻¹ • (e i - (e i - chartPow y c (b i) • w i)) := by
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ (hp i), one_smul]
    rw [Module.Basis.coord_apply, hw, map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply,
      hself, hvan _ (hx i)]
    simp

end Dual

section Avoid

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨0, h0, by simp⟩`. Consider the case `@insert Q₀ T _ ih`. Take `⟨x, hx, hxT⟩` from `ih fun Q h => hT Q (Finset.mem_insert_of_mem h)`. Take `⟨hQ₀, hC₀, y, hy, hyQ₀⟩` from `hT Q₀ (Finset.mem_insert_self _ _)`.

Establish `hsub : ∀ Q ∈ T, {t : R | x.2 + algebraMap R A t * y.2 ∈ Q}.Subsingleton`. Introduce `Q hQT t ht t' ht'`. Take `⟨hQ, hCQ, -⟩` from `hT Q (Finset.mem_insert_of_mem hQT)`. Establish `hd : algebraMap R A (t - t') * y.2 ∈ Q`. Establish `h` using `Q.sub_mem ht ht'`.

Rewrite using `[map_sub]`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Break down `hQ.mem_or_mem hd with h | h` into its components or cases. Conclude with `sub_eq_zero.mp (hCQ _ h)`.

Conclude with `absurd (by simpa using Q.sub_mem ht (Q.mul_mem_left (algebraMap R A t) h)) (hxT Q hQT)`. Establish `hfin : (insert 0 (⋃ Q ∈ T, {t : R | x.2 + algebraMap R A t * y.2 ∈ Q})).Finite` using `(T.finite_toSet.biUnion fun Q hQ => (hsub Q hQ).finite).insert 0`. Take `⟨t, ht⟩` from `Infinite.exists_notMem_finset hfin.toFinset`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists] at ht`. Take `⟨ht0, htT⟩` from `ht`.

Establish `hsnd : (x + t • y).2 = x.2 + algebraMap R A t * y.2`. Rewrite using `[Prod.snd_add, Prod.smul_snd, Algebra.smul_def]`. Distinguish the cases in `hxQ₀ : x.2 ∈ Q₀`. Use `⟨x + t • y, hG x hx y hy t, fun Q hQ => ?_⟩` and prove the remaining obligations. Rewrite using `[hsnd]`.

Break down `Finset.mem_insert.mp hQ with rfl | hQT` into its components or cases. Introduce `h`. Establish `h' : algebraMap R A t * y.2 ∈ Q` using `by simpa using Q.sub_mem h hxQ₀`. Break down `hQ₀.mem_or_mem h' with h'' | h''` into its components or cases. Conclude with `ht0 (hC₀ _ h'')`.

Conclude with `hyQ₀ h''`. Conclude with `htT Q hQT`. Use `⟨x, hx, fun Q hQ => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hQ with rfl | hQT` into its components or cases. Conclude with `hxQ₀`.

Conclude with `hxT Q hQT`.
-/
theorem exists_pair_not_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Infinite R]
    (G : Set (A × A)) (h0 : (0 : A × A) ∈ G) (hG : ∀ p ∈ G, ∀ q ∈ G, ∀ t : R, p + t • q ∈ G)
    (T : Finset (Ideal A))
    (hT : ∀ Q ∈ T, Q.IsPrime ∧ (∀ a : R, algebraMap R A a ∈ Q → a = 0) ∧ ∃ p ∈ G, p.2 ∉ Q) :
    ∃ p ∈ G, ∀ Q ∈ T, p.2 ∉ Q := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, h0, by simp⟩
  | @insert Q₀ T _ ih =>
    obtain ⟨x, hx, hxT⟩ := ih fun Q h => hT Q (Finset.mem_insert_of_mem h)
    obtain ⟨hQ₀, hC₀, y, hy, hyQ₀⟩ := hT Q₀ (Finset.mem_insert_self _ _)
    have hsub : ∀ Q ∈ T, {t : R | x.2 + algebraMap R A t * y.2 ∈ Q}.Subsingleton := by
      intro Q hQT t ht t' ht'
      obtain ⟨hQ, hCQ, -⟩ := hT Q (Finset.mem_insert_of_mem hQT)
      have hd : algebraMap R A (t - t') * y.2 ∈ Q := by
        have h := Q.sub_mem ht ht'
        rw [map_sub]
        convert h using 1
        ring
      rcases hQ.mem_or_mem hd with h | h
      · exact sub_eq_zero.mp (hCQ _ h)
      · exact absurd (by simpa using Q.sub_mem ht (Q.mul_mem_left (algebraMap R A t) h)) (hxT Q hQT)
    have hfin : (insert 0 (⋃ Q ∈ T, {t : R | x.2 + algebraMap R A t * y.2 ∈ Q})).Finite :=
      (T.finite_toSet.biUnion fun Q hQ => (hsub Q hQ).finite).insert 0
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset hfin.toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_iUnion, Set.mem_setOf_eq,
      not_or, not_exists] at ht
    obtain ⟨ht0, htT⟩ := ht
    have hsnd : (x + t • y).2 = x.2 + algebraMap R A t * y.2 := by
      rw [Prod.snd_add, Prod.smul_snd, Algebra.smul_def]
    by_cases hxQ₀ : x.2 ∈ Q₀
    · refine ⟨x + t • y, hG x hx y hy t, fun Q hQ => ?_⟩
      rw [hsnd]
      rcases Finset.mem_insert.mp hQ with rfl | hQT
      · intro h
        have h' : algebraMap R A t * y.2 ∈ Q := by simpa using Q.sub_mem h hxQ₀
        rcases hQ₀.mem_or_mem h' with h'' | h''
        · exact ht0 (hC₀ _ h'')
        · exact hyQ₀ h''
      · exact htT Q hQT
    · refine ⟨x, hx, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQT
      · exact hxQ₀
      · exact hxT Q hQT

end Avoid

section Flag

variable {Ω : Type} [Field Ω] {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

/- English proof (translation)
Unfold `genVal flagLineCoord`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : (j : ℕ) < k + 1`. Establish `hχ : χ (w j) = w'.repr (w j) ⟨k, hk⟩` using `by conv_lhs => rw [← w'.sum_repr (w j)]`. Rewrite using `[map_sum, Finset.sum_eq_single ⟨k, hk⟩]`.

Rewrite using `[map_smul, htop, smul_eq_mul, mul_one]`. Introduce `m _ hm`. Break down `lt_or_gt_of_ne hm with hlt | hgt` into its components or cases. Rewrite using `[map_smul, hlow m hlt, smul_zero]`. Establish `hjm : j < m`.

Rewrite `hgt`, the goal using `[Fin.lt_def]`. Simplify using `only at hgt`. Use linear arithmetic over natural numbers and integers. Rewrite using `[repr_flag_inv w w' hsame j m hjm, zero_smul, map_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[hχ]`. Establish `h0 : flagCoord w e t (k + 1) j = 0`. Unfold `flagCoord`. Rewrite using `[if_neg hj]`. Rewrite using `[h0, zero_mul, zero_mul]`.
-/
theorem genVal_flag (w w' e : Module.Basis (Fin N) Ω E) (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0)
    (t : Fin N → Φ) (k : ℕ) (hk : k < N) (χ : Module.Dual Ω E)
    (hlow : ∀ j, j < (⟨k, hk⟩ : Fin N) → χ (w' j) = 0) (htop : χ (w' ⟨k, hk⟩) = 1) :
    genVal w (flagCoord w e t (k + 1)) χ = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ := by
  unfold genVal flagLineCoord
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) < k + 1
  · have hχ : χ (w j) = w'.repr (w j) ⟨k, hk⟩ := by
      conv_lhs => rw [← w'.sum_repr (w j)]
      rw [map_sum, Finset.sum_eq_single ⟨k, hk⟩]
      · rw [map_smul, htop, smul_eq_mul, mul_one]
      · intro m _ hm
        rcases lt_or_gt_of_ne hm with hlt | hgt
        · rw [map_smul, hlow m hlt, smul_zero]
        · have hjm : j < m := by
            rw [Fin.lt_def] at hgt ⊢
            simp only at hgt
            omega
          rw [repr_flag_inv w w' hsame j m hjm, zero_smul, map_zero]
      · simp
    rw [hχ]
  · have h0 : flagCoord w e t (k + 1) j = 0 := by
      unfold flagCoord
      rw [if_neg hj]
    rw [h0, zero_mul, zero_mul]

/- English proof (translation)
Introduce `h0`. Establish `h1` using `flagLineCoord_flag w w' e hsame t k hk`. Rewrite `h1` using `[h0, mul_zero]`. Establish `h2 : flagLineCoord w w e t (k + 1) ⟨k, hk⟩ = ∑ i, w.repr (e i) ⟨k, hk⟩ • t i`. Unfold `flagLineCoord`.

Rewrite using `[Finset.sum_eq_single ⟨k, hk⟩]`. Rewrite using `[Module.Basis.repr_self, Finsupp.single_eq_same, map_one, mul_one]`. Unfold `flagCoord`. Rewrite using `[if_pos (Nat.lt_succ_self k)]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]`.

Introduce `j _ hj`. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply, if_neg hj, map_zero, mul_zero]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2]`. Establish `hz` using `Fintype.linearIndependent_iff.mp ht.linearIndependent _ h1`.

Establish `hc : w.coord ⟨k, hk⟩ = 0` using `e.ext fun i => by simpa using hz i`. Use `congrArg (fun f => f (w ⟨k, hk⟩)) hc` as an intermediate fact. Simplify using `at this`.
-/
theorem flagLineCoord_ne_zero (w w' e : Module.Basis (Fin N) Ω E)
    (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) (t : Fin N → Φ) (ht : AlgebraicIndependent Ω t)
    (k : ℕ) (hk : k < N) : flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ ≠ 0 := by
  intro h0
  have h1 := flagLineCoord_flag w w' e hsame t k hk
  rw [h0, mul_zero] at h1
  have h2 : flagLineCoord w w e t (k + 1) ⟨k, hk⟩ = ∑ i, w.repr (e i) ⟨k, hk⟩ • t i := by
    unfold flagLineCoord
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · rw [Module.Basis.repr_self, Finsupp.single_eq_same, map_one, mul_one]
      unfold flagCoord
      rw [if_pos (Nat.lt_succ_self k)]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    · intro j _ hj
      rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg hj, map_zero, mul_zero]
    · simp
  rw [h2] at h1
  have hz := Fintype.linearIndependent_iff.mp ht.linearIndependent _ h1
  have hc : w.coord ⟨k, hk⟩ = 0 := e.ext fun i => by simpa using hz i
  have := congrArg (fun f => f (w ⟨k, hk⟩)) hc
  simp at this

end Flag

section Chart

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]

/- English proof (translation)
Distinguish the cases in `hc : segreVec y c = 0`. Conclude with `⟨0, fun h => absurd hc h⟩`. Establish `hY : ∀ j, y ⟨j, c j⟩ ≠ 0` using `fun j => (Finset.prod_ne_zero_iff.1 hc) j (Finset.mem_univ _)`. Take `⟨ψ, hψint, hψlow, hψk⟩` from `exists_flag_dual y B' w' x' hfl' c hc ⟨k, hk⟩`. Take `⟨u, hu, hψ⟩` from `hφ'.generate c hc ψ hψint`.

Establish `hp` using `chartPow_ne_zero hY (x' ⟨k, hk⟩)`. Establish `hexpr : algebraMap O Ω 1 ^ 0 • (chartPow y c (x' ⟨k, hk⟩) • ψ) = ∑ l, (u l * ∏ j, y ⟨j, c j⟩ ^ (x' ⟨k, hk⟩ j - a₀' j)) • φ' l`. Rewrite using `[pow_zero, one_smul, hψ, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Use `congr 1`. Establish `hsplit : ∏ j, y ⟨j, c j⟩ ^ (x' ⟨k, hk⟩ j - a₀' j) = chartPow y c (x' ⟨k, hk⟩) * ∏ j, y ⟨j, c j⟩ ^ (-a₀' j)`. Unfold `chartPow`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[sub_eq_add_neg, zpow_add₀ (hY j)]`. Rewrite using `[hsplit]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨bG, bH, G, hG, hdeg, hval⟩` from `express_forms (M := M) (M' := M') y w φ φ' (flagCoord w e t (k + 1)) c hc (1 : O) φ' (chartPow y c (x' ⟨k, hk⟩) • ψ) a₀' (x' ⟨k, hk⟩) 0 u hu hexpr`. Establish `hgen : genVal w (flagCoord w e t (k + 1)) (chartPow y c (x' ⟨k, hk⟩) • ψ) = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩`.

Use `genVal_flag w w' e hsame t k hk _ (fun j hj => ?_) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, hψlow j hj, smul_zero]`. Rewrite using `[LinearMap.smul_apply, hψk, smul_eq_mul, mul_inv_cancel₀ hp]`. Rewrite `hval` using `[hgen]`. Simplify using `only [pow_zero, map_one, one_mul] at hval`.

Use `⟨bH, fun _ β hβ => ⟨(∑ l, X ⟨none, l⟩ * G l) * chartMonoZ O M M' c (β - bH), ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : IsMultiHomog (∑ l, X ⟨none, l⟩ * G l : MRing (bundleIdx (bundleIdx ι M) M') O) (Pi.single none 1 + vdeg bG)` using `IsWeightedHomogeneous.sum _ _ _ fun l _ => IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG l)`. Establish `h2` using `IsWeightedHomogeneous.mul h1 (chartMonoZ_homog (O := O) (M := M) (M' := M') c (β - bH))`. Establish `hd : (Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat) : Option (Option K) → ℕ) = Pi.single none 1 + vdeg bG + vdeg (β - bH)`. Use function extensionality and compare the values at `o`.

Break down `o with _ | _ | j` into its components or cases. Simplify using `[vdeg]`. Simplify using `[vdeg]`. Establish `h3` using `hdeg j`. Establish `h4` using `hβ j`.

Simplify using `[vdeg, Pi.single_apply]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hd]`. Conclude with `h2`. Establish `hpt : flagClosurePt y w e φ φ' t (k + 1) = pairProjCoord y w φ φ' (flagCoord w e t (k + 1))` using `rfl`.

Establish `hm : chartMonoZ O M M' c β = chartMonoZ O M M' c bH * chartMonoZ O M M' c (β - bH)`. Unfold `chartMonoZ`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add]`.

Use `congr 1`. Use `hβ j` as an intermediate fact. Simplify using `only [Pi.sub_apply]`. Use linear arithmetic over natural numbers and integers. Establish `hs : aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (∑ l, X ⟨none, l⟩ * G l : MRing (bundleIdx (bundleIdx ι M) M') O) = ∑ l, aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (G l) * genVal w (flagCoord w e t (k + 1)) (φ' l)`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [map_mul, aeval_X, mul_comm]; rfl`. Rewrite using `[hpt, map_mul, hs, ← hval, hm, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chart_pair (y : (Σ k, ι k) → Ω) (B' : ChartBundle O (segreVec y) N E)
    (w w' e : Module.Basis (Fin N) Ω E) (x' : Fin N → K → ℤ) (hfl' : IsFlagFrame y B' w' x')
    (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) (a₀' : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (hφ' : IsTwistedDualGens y B' a₀' φ')
    (t : Fin N → Φ) (k : ℕ) (hk : k < N) (c : ∀ k, ι k) :
    ∃ bH : K → ℕ, segreVec y c ≠ 0 → ∀ β : K → ℕ, (∀ j, bH j ≤ β j) →
      ∃ s : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsMultiHomog s (Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat)) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s =
          flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ *
            aeval (flagClosurePt y w e φ φ' t (k + 1)) (chartMonoZ O M M' c β) := by
  by_cases hc : segreVec y c = 0
  · exact ⟨0, fun h => absurd hc h⟩
  have hY : ∀ j, y ⟨j, c j⟩ ≠ 0 := fun j => (Finset.prod_ne_zero_iff.1 hc) j (Finset.mem_univ _)
  obtain ⟨ψ, hψint, hψlow, hψk⟩ := exists_flag_dual y B' w' x' hfl' c hc ⟨k, hk⟩
  obtain ⟨u, hu, hψ⟩ := hφ'.generate c hc ψ hψint
  have hp := chartPow_ne_zero hY (x' ⟨k, hk⟩)
  have hexpr : algebraMap O Ω 1 ^ 0 • (chartPow y c (x' ⟨k, hk⟩) • ψ) =
      ∑ l, (u l * ∏ j, y ⟨j, c j⟩ ^ (x' ⟨k, hk⟩ j - a₀' j)) • φ' l := by
    rw [pow_zero, one_smul, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    have hsplit : ∏ j, y ⟨j, c j⟩ ^ (x' ⟨k, hk⟩ j - a₀' j) =
        chartPow y c (x' ⟨k, hk⟩) * ∏ j, y ⟨j, c j⟩ ^ (-a₀' j) := by
      unfold chartPow
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [sub_eq_add_neg, zpow_add₀ (hY j)]
    rw [hsplit]
    ring
  obtain ⟨bG, bH, G, hG, hdeg, hval⟩ := express_forms (M := M) (M' := M') y w φ φ'
    (flagCoord w e t (k + 1)) c hc (1 : O) φ' (chartPow y c (x' ⟨k, hk⟩) • ψ) a₀' (x' ⟨k, hk⟩) 0 u hu hexpr
  have hgen : genVal w (flagCoord w e t (k + 1)) (chartPow y c (x' ⟨k, hk⟩) • ψ) =
      flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ := by
    refine genVal_flag w w' e hsame t k hk _ (fun j hj => ?_) ?_
    · rw [LinearMap.smul_apply, hψlow j hj, smul_zero]
    · rw [LinearMap.smul_apply, hψk, smul_eq_mul, mul_inv_cancel₀ hp]
  rw [hgen] at hval
  simp only [pow_zero, map_one, one_mul] at hval
  refine ⟨bH, fun _ β hβ => ⟨(∑ l, X ⟨none, l⟩ * G l) * chartMonoZ O M M' c (β - bH), ?_, ?_⟩⟩
  · have h1 : IsMultiHomog (∑ l, X ⟨none, l⟩ * G l : MRing (bundleIdx (bundleIdx ι M) M') O)
        (Pi.single none 1 + vdeg bG) :=
      IsWeightedHomogeneous.sum _ _ _ fun l _ =>
        IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG l)
    have h2 := IsWeightedHomogeneous.mul h1 (chartMonoZ_homog (O := O) (M := M) (M' := M') c (β - bH))
    have hd : (Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat) :
        Option (Option K) → ℕ) = Pi.single none 1 + vdeg bG + vdeg (β - bH) := by
      funext o
      rcases o with _ | _ | j
      · simp [vdeg]
      · simp [vdeg]
      · have h3 := hdeg j
        have h4 := hβ j
        simp [vdeg, Pi.single_apply]
        omega
    rw [hd]
    exact h2
  · have hpt : flagClosurePt y w e φ φ' t (k + 1) = pairProjCoord y w φ φ' (flagCoord w e t (k + 1)) := rfl
    have hm : chartMonoZ O M M' c β = chartMonoZ O M M' c bH * chartMonoZ O M M' c (β - bH) := by
      unfold chartMonoZ
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← pow_add]
      congr 1
      have := hβ j
      simp only [Pi.sub_apply]
      omega
    have hs : aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1)))
        (∑ l, X ⟨none, l⟩ * G l : MRing (bundleIdx (bundleIdx ι M) M') O) =
        ∑ l, aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (G l) *
          genVal w (flagCoord w e t (k + 1)) (φ' l) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, aeval_X, mul_comm]; rfl
    rw [hpt, map_mul, hs, ← hval, hm, map_mul]
    ring

end Chart

end SegreFlagCutForms

open SegreFlagCutForms in

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht k hk S hS`. Establish `hInf : Infinite O` using `Infinite.of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)`. Establish `hpt : flagClosurePt y w e φ φ' t (k + 1) = pairProjCoord y w φ φ' (flagCoord w e t (k + 1))` using `rfl`. Use `choose bH hbH using chart_pair (M := M) y B' w w' e x' hfl.flag' hfl.sameFlag a₀' φ φ' hφ' t k hk`. Choose the witnesses or unpack the hypotheses as in `⟨β, hβ, hβD⟩ : ∃ β : K → ℕ, (∀ c j, bH c j ≤ β j) ∧ ∀ j, 0 ≤ (β j : ℤ) + (x' ⟨k, hk⟩ j - a₀' j) := by`.

Use `⟨fun j => ∑ c, bH c j + (-(x' ⟨k, hk⟩ j - a₀' j)).toNat, fun c j => ?_, fun j => ?_⟩` and prove the remaining obligations. Conclude with `le_trans (Finset.single_le_sum (f := fun c => bH c j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)) (Nat.le_add_right _ _)`. Establish `h1` using `Int.self_le_toNat (-(x' ⟨k, hk⟩ j - a₀' j))`. Establish `h2 : ((-(x' ⟨k, hk⟩ j - a₀' j)).toNat : ℤ) ≤ ((∑ c, bH c j + (-(x' ⟨k, hk⟩ j - a₀' j)).toNat : ℕ) : ℤ)`. Conclude with `Nat.le_add_left _ _` after adjusting the coercions.

Use `beta_reduce`. Use linear arithmetic over natural numbers and integers. Use `set P := pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) with hPdef`. Use `set τ := flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ with hτdef`. Use `set pt := flagClosurePt y w e φ φ' t (k + 1) with hptdef`.

Set `G : Set (MRing (bundleIdx (bundleIdx ι M) M') O × MRing (bundleIdx (bundleIdx ι M) M') O)` to `{p | IsMultiHomog p.1 (Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat)) ∧ IsMultiHomog p.2 (vdeg β) ∧ aeval pt p.1 = τ * aeval pt p.2}`. Establish `h0 : (0 : MRing (bundleIdx (bundleIdx ι M) M') O × MRing (bundleIdx (bundleIdx ι M) M') O) ∈ G` using `⟨isWeightedHomogeneous_zero _ _ _, isWeightedHomogeneous_zero _ _ _, by simp⟩`. Establish `hG : ∀ p ∈ G, ∀ q ∈ G, ∀ r : O, p + r • q ∈ G`. Introduce `p hp q hq r`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (add_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp.1) (Submodule.smul_mem _ r ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hq.1)))`. Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (add_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp.2.1) (Submodule.smul_mem _ r ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hq.2.1)))`. Use `show aeval pt (p.1 + r • q.1) = τ * aeval pt (p.2 + r • q.2)`. Rewrite using `[map_add, map_add, map_smul, map_smul, hp.2.2, hq.2.2, mul_add, mul_smul_comm]`. Establish `hpair : ∀ (Q : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) (c : ∀ j, ι j), segreVec y c ≠ 0 → chartMonoZ O M M' c β ∉ Q → ∃ p ∈ G, p.2 ∉ Q`.

Introduce `Q c hc hcQ`. Take `⟨s, hs, hsv⟩` from `hbH c hc β (hβ c)`. Conclude with `⟨(s, chartMonoZ O M M' c β), ⟨hs, chartMonoZ_homog c β, hsv⟩, hcQ⟩`. Establish `hT : ∀ Q ∈ insert P S, Q.IsPrime ∧ (∀ a : O, algebraMap O (MRing (bundleIdx (bundleIdx ι M) M') O) a ∈ Q → a = 0) ∧ ∃ p ∈ G, p.2 ∉ Q`. Introduce `Q hQ`.

Rewrite using `[MvPolynomial.algebraMap_eq]`. Break down `Finset.mem_insert.mp hQ with rfl | hQS` into its components or cases. Use `⟨RingHom.ker_isPrime _, fun a ha => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : aeval pt (C a : MRing (bundleIdx (bundleIdx ι M) M') O) = 0` using `aeval_eq_zero_of_mem ha`. Rewrite `h1` using `[aeval_C, IsScalarTower.algebraMap_apply O Ω Φ]`.

Establish `h2 : algebraMap O Ω a = 0` using `(algebraMap Ω Φ).injective (by rw [h1, map_zero])`. Establish `h3 : (C a : MRing ι O) ∈ pointIdeal O y` using `mem_of_homog (b := 0) (isWeightedHomogeneous_C _ _) (by rw [aeval_C, h2])`. Establish `h4 : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)` using `h3`. Rewrite `h4` using `[hV.noTorsion]`. Conclude with `(Submodule.mem_bot O).mp h4`.

Use `choose c hc using hV.multiProj.relevant`. Establish `hY : ∀ j, y ⟨j, c j⟩ ≠ 0` using `fun j h0 => hc j (mem_of_homog (isWeightedHomogeneous_X O _ _) (by rw [aeval_X, h0]))`. Use `hpair _ c (Finset.prod_ne_zero_iff.mpr fun j _ => hY j) fun hm => ?_` and prove the remaining obligations. Establish `h1` using `aeval_eq_zero_of_mem hm`. Express the relevant statement in the definitionally equal form `aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (chartMonoZ O M M' c β) = 0 at h1`.

Rewrite `h1` using `[aeval_chartMonoZ]`. Conclude with `Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hY j)) ((map_eq_zero_iff _ (algebraMap Ω Φ).injective).mp h1)`. Take `⟨hQp, hQr, hPQ, hϖQ⟩` from `hS Q hQS`. Use `⟨hQp, fun a ha => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `ha0`.

Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ`. Rewrite `ha` using `[map_mul, map_pow]`. Break down `hQp.mem_or_mem ha with h | h` into its components or cases. Conclude with `hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ h (u.isUnit.map C))`. Conclude with `hϖQ (hQp.mem_of_pow_mem _ h)`.

Use `choose c hc using fun j : K => hQr (some (some j))`. Establish `nz : ∀ j, y ⟨j, c j⟩ ≠ 0`. Introduce `j h0`. Use `hc j (hPQ (mem_of_homog (isWeightedHomogeneous_X O _ _) ?_))` and prove the remaining obligations. Rewrite using `[aeval_X]`.

Use `show algebraMap Ω Φ (y ⟨j, c j⟩) = 0`. Rewrite using `[h0, map_zero]`. Use `hpair Q c (Finset.prod_ne_zero_iff.mpr fun j _ => nz j) fun hm => ?_` and prove the remaining obligations. Take `⟨j, -, hj⟩` from `hQp.prod_mem_iff.mp hm`. Conclude with `hc j (hQp.mem_of_pow_mem _ hj)`.

Take `⟨⟨s, h⟩, ⟨hs, hh, hval⟩, hav⟩` from `exists_pair_not_mem (R := O) G h0 hG (insert P S) hT`. Establish `hhP : h ∉ P` using `hav P (Finset.mem_insert_self _ _)`. Establish `hτ : τ ≠ 0` using `flagLineCoord_ne_zero w w' e hfl.sameFlag t ht k hk`. Establish `hsP : s ∉ P`. Introduce `hm`.

Establish `h1` using `aeval_eq_zero_of_mem hm`. Rewrite `h1` using `[hval]`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. Conclude with `hτ h2`. Conclude with `hhP (mem_of_homog hh h2)`.

Use `⟨_, _, s, h, hs, hh, ?_, hsP, hhP, hval, fun Q hQ => hav Q (Finset.mem_insert_of_mem hQ)⟩` and prove the remaining obligations. Use function extensionality and compare the values at `o`. Break down `o with _ | _ | j` into its components or cases. Simplify using `[vdeg, zetaSecond, liftPairDeg]`. Simplify using `[vdeg, zetaSecond, liftPairDeg]`.

Use `hβD j` as an intermediate fact. Simplify using `[vdeg, zetaSecond, liftPairDeg, Pi.single_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem SegreFlagCutForms.proof : SegreFlagCutForms.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk S hS
  classical
  have hInf : Infinite O :=
    Infinite.of_injective _ (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)
  have hpt : flagClosurePt y w e φ φ' t (k + 1) = pairProjCoord y w φ φ' (flagCoord w e t (k + 1)) := rfl
  choose bH hbH using chart_pair (M := M) y B' w w' e x' hfl.flag' hfl.sameFlag a₀' φ φ' hφ' t k hk
  obtain ⟨β, hβ, hβD⟩ : ∃ β : K → ℕ, (∀ c j, bH c j ≤ β j) ∧ ∀ j, 0 ≤ (β j : ℤ) + (x' ⟨k, hk⟩ j - a₀' j) := by
    refine ⟨fun j => ∑ c, bH c j + (-(x' ⟨k, hk⟩ j - a₀' j)).toNat, fun c j => ?_, fun j => ?_⟩
    · exact le_trans (Finset.single_le_sum (f := fun c => bH c j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)) (Nat.le_add_right _ _)
    · have h1 := Int.self_le_toNat (-(x' ⟨k, hk⟩ j - a₀' j))
      have h2 : ((-(x' ⟨k, hk⟩ j - a₀' j)).toNat : ℤ) ≤
          ((∑ c, bH c j + (-(x' ⟨k, hk⟩ j - a₀' j)).toNat : ℕ) : ℤ) := by
        exact_mod_cast Nat.le_add_left _ _
      beta_reduce
      omega
  set P := pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) with hPdef
  set τ := flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ with hτdef
  set pt := flagClosurePt y w e φ φ' t (k + 1) with hptdef
  let G : Set (MRing (bundleIdx (bundleIdx ι M) M') O × MRing (bundleIdx (bundleIdx ι M) M') O) :=
    {p | IsMultiHomog p.1 (Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat)) ∧
      IsMultiHomog p.2 (vdeg β) ∧ aeval pt p.1 = τ * aeval pt p.2}
  have h0 : (0 : MRing (bundleIdx (bundleIdx ι M) M') O × MRing (bundleIdx (bundleIdx ι M) M') O) ∈ G :=
    ⟨isWeightedHomogeneous_zero _ _ _, isWeightedHomogeneous_zero _ _ _, by simp⟩
  have hG : ∀ p ∈ G, ∀ q ∈ G, ∀ r : O, p + r • q ∈ G := by
    intro p hp q hq r
    refine ⟨?_, ?_, ?_⟩
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (add_mem
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp.1)
        (Submodule.smul_mem _ r ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hq.1)))
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (add_mem
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp.2.1)
        (Submodule.smul_mem _ r ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hq.2.1)))
    · show aeval pt (p.1 + r • q.1) = τ * aeval pt (p.2 + r • q.2)
      rw [map_add, map_add, map_smul, map_smul, hp.2.2, hq.2.2, mul_add, mul_smul_comm]

  have hpair : ∀ (Q : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) (c : ∀ j, ι j),
      segreVec y c ≠ 0 → chartMonoZ O M M' c β ∉ Q → ∃ p ∈ G, p.2 ∉ Q := by
    intro Q c hc hcQ
    obtain ⟨s, hs, hsv⟩ := hbH c hc β (hβ c)
    exact ⟨(s, chartMonoZ O M M' c β), ⟨hs, chartMonoZ_homog c β, hsv⟩, hcQ⟩
  have hT : ∀ Q ∈ insert P S, Q.IsPrime ∧
      (∀ a : O, algebraMap O (MRing (bundleIdx (bundleIdx ι M) M') O) a ∈ Q → a = 0) ∧ ∃ p ∈ G, p.2 ∉ Q := by
    intro Q hQ
    rw [MvPolynomial.algebraMap_eq]
    rcases Finset.mem_insert.mp hQ with rfl | hQS
    · refine ⟨RingHom.ker_isPrime _, fun a ha => ?_, ?_⟩
      · have h1 : aeval pt (C a : MRing (bundleIdx (bundleIdx ι M) M') O) = 0 := aeval_eq_zero_of_mem ha
        rw [aeval_C, IsScalarTower.algebraMap_apply O Ω Φ] at h1
        have h2 : algebraMap O Ω a = 0 := (algebraMap Ω Φ).injective (by rw [h1, map_zero])
        have h3 : (C a : MRing ι O) ∈ pointIdeal O y :=
          mem_of_homog (b := 0) (isWeightedHomogeneous_C _ _) (by rw [aeval_C, h2])
        have h4 : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := h3
        rw [hV.noTorsion] at h4
        exact (Submodule.mem_bot O).mp h4
      · choose c hc using hV.multiProj.relevant
        have hY : ∀ j, y ⟨j, c j⟩ ≠ 0 := fun j h0 =>
          hc j (mem_of_homog (isWeightedHomogeneous_X O _ _) (by rw [aeval_X, h0]))
        refine hpair _ c (Finset.prod_ne_zero_iff.mpr fun j _ => hY j) fun hm => ?_
        have h1 := aeval_eq_zero_of_mem hm
        change aeval (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) (chartMonoZ O M M' c β) = 0 at h1
        rw [aeval_chartMonoZ] at h1
        exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hY j))
          ((map_eq_zero_iff _ (algebraMap Ω Φ).injective).mp h1)
    · obtain ⟨hQp, hQr, hPQ, hϖQ⟩ := hS Q hQS
      refine ⟨hQp, fun a ha => ?_, ?_⟩
      · by_contra ha0
        obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
        rw [map_mul, map_pow] at ha
        rcases hQp.mem_or_mem ha with h | h
        · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ h (u.isUnit.map C))
        · exact hϖQ (hQp.mem_of_pow_mem _ h)
      · choose c hc using fun j : K => hQr (some (some j))
        have nz : ∀ j, y ⟨j, c j⟩ ≠ 0 := by
          intro j h0
          refine hc j (hPQ (mem_of_homog (isWeightedHomogeneous_X O _ _) ?_))
          rw [aeval_X]
          show algebraMap Ω Φ (y ⟨j, c j⟩) = 0
          rw [h0, map_zero]
        refine hpair Q c (Finset.prod_ne_zero_iff.mpr fun j _ => nz j) fun hm => ?_
        obtain ⟨j, -, hj⟩ := hQp.prod_mem_iff.mp hm
        exact hc j (hQp.mem_of_pow_mem _ hj)
  obtain ⟨⟨s, h⟩, ⟨hs, hh, hval⟩, hav⟩ := exists_pair_not_mem (R := O) G h0 hG (insert P S) hT
  have hhP : h ∉ P := hav P (Finset.mem_insert_self _ _)
  have hτ : τ ≠ 0 := flagLineCoord_ne_zero w w' e hfl.sameFlag t ht k hk
  have hsP : s ∉ P := by
    intro hm
    have h1 := aeval_eq_zero_of_mem hm
    rw [hval] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hτ h2
    · exact hhP (mem_of_homog hh h2)
  refine ⟨_, _, s, h, hs, hh, ?_, hsP, hhP, hval, fun Q hQ => hav Q (Finset.mem_insert_of_mem hQ)⟩
  funext o
  rcases o with _ | _ | j
  · simp [vdeg, zetaSecond, liftPairDeg]
  · simp [vdeg, zetaSecond, liftPairDeg]
  · have := hβD j
    simp [vdeg, zetaSecond, liftPairDeg, Pi.single_apply]
    omega

end

end GroundTheory.Heights₂.Heights.NumbersDVR
