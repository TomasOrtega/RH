import Development.WeilBound.CoreStatements.VolumeEquality.DegPushVal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly

noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)]

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, d = n + 1` from `⟨d - 1, by have := i.pos; omega⟩`. Establish `key : inum k z a = inum k z (a ∘ Equiv.swap i (Fin.last n))`. Unfold `inum NumbersDVR.intNum`. Rewrite using `[FieldNumbers.mixedDiff_comp_perm]`. Rewrite using `[key, ← Fin.snoc_init_self (a ∘ Equiv.swap i (Fin.last n))]`.

Apply `h3 k Ω K ι z n _ _ hz ht` to reduce the goal to its premises. Use `show ValEq k z (a (Equiv.swap i (Fin.last n) (Fin.last n))) z 0`. Rewrite using `[Equiv.swap_apply_right]`. Conclude with `h`.
-/
theorem inum_eq_zero_of_valEq_zero (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a : Fin d → K → ℤ) (i : Fin d) (h : ValEq k z (a i) z 0) : inum k z a = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := i.pos; omega⟩
  have key : inum k z a = inum k z (a ∘ Equiv.swap i (Fin.last n)) := by
    unfold inum NumbersDVR.intNum
    rw [FieldNumbers.mixedDiff_comp_perm]
  rw [key, ← Fin.snoc_init_self (a ∘ Equiv.swap i (Fin.last n))]
  apply h3 k Ω K ι z n _ _ hz ht
  show ValEq k z (a (Equiv.swap i (Fin.last n) (Fin.last n))) z 0
  rw [Equiv.swap_apply_right]
  exact h

/- English proof (translation)
Take `⟨hprime, hdim, -⟩` from `h1 k Ω K ι z d hz`. Establish `hadd` using `FieldNumbers.IntNumAdd.full k K ι (NumbersDVR.pointIdeal k z) hprime.multiHomog hprime.relevant d hdim a i (b - a i) (a i)`. Rewrite `hadd` using `[sub_add_cancel, Function.update_eq_self]`. Establish `hz0 : inum k z (Function.update a i (b - a i)) = 0`. Apply `inum_eq_zero_of_valEq_zero h3 hz ht _ i` to reduce the goal to its premises.

Rewrite using `[Function.update_self]`. Take `⟨ρ, hρ, hO⟩` from `h`. Use `⟨ρ, hρ, fun O hk => ?_⟩` and prove the remaining obligations. Establish `e` using `hO O hk`. Establish `hne : ∀ c : K, (Finset.univ.sup fun j : ι c => O.valuation (z ⟨c, j⟩)) ≠ 0`.

Introduce `c h0`. Take `⟨j, hj⟩` from `hz.1 c`. Establish `hle : O.valuation (z ⟨c, j⟩) ≤ 0` using `h0 ▸ Finset.le_sup (f := fun j : ι c => O.valuation (z ⟨c, j⟩)) (Finset.mem_univ j)`. Conclude with `hj ((Valuation.zero_iff _).mp (le_antisymm hle zero_le'))`. Establish `hv : vdeg O z (b - a i) * vdeg O z (a i) = vdeg O z b`.

Unfold `vdeg`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.sub_apply, ← zpow_add₀ (hne c), sub_add_cancel]`. Establish `hne' : vdeg O z (a i) ≠ 0`.

Unfold `vdeg`. Conclude with `Finset.prod_ne_zero_iff.mpr fun c _ => zpow_ne_zero _ (hne c)`. Establish `h0 : vdeg O z (0 : K → ℤ) = 1`. Unfold `vdeg`. Simplify using the standard rewrite rules.

Rewrite using `[h0, mul_one]`. Apply `mul_right_cancel₀ hne'` to reduce the goal to its premises. Rewrite using `[hv, e]`. Unfold `inum at hz0 ⊢`. Use `hadd using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hz0, zero_add]`.
-/
theorem inum_update (h1 : PtDim) (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a : Fin d → K → ℤ) (i : Fin d) (b : K → ℤ) (h : ValEq k z b z (a i)) : inum k z (Function.update a i b) = inum k z a := by
  classical
  obtain ⟨hprime, hdim, -⟩ := h1 k Ω K ι z d hz
  have hadd := FieldNumbers.IntNumAdd.full k K ι (NumbersDVR.pointIdeal k z) hprime.multiHomog hprime.relevant d hdim
    a i (b - a i) (a i)
  rw [sub_add_cancel, Function.update_eq_self] at hadd
  have hz0 : inum k z (Function.update a i (b - a i)) = 0 := by
    apply inum_eq_zero_of_valEq_zero h3 hz ht _ i
    rw [Function.update_self]
    obtain ⟨ρ, hρ, hO⟩ := h
    refine ⟨ρ, hρ, fun O hk => ?_⟩
    have e := hO O hk
    have hne : ∀ c : K, (Finset.univ.sup fun j : ι c => O.valuation (z ⟨c, j⟩)) ≠ 0 := by
      intro c h0
      obtain ⟨j, hj⟩ := hz.1 c
      have hle : O.valuation (z ⟨c, j⟩) ≤ 0 :=
        h0 ▸ Finset.le_sup (f := fun j : ι c => O.valuation (z ⟨c, j⟩)) (Finset.mem_univ j)
      exact hj ((Valuation.zero_iff _).mp (le_antisymm hle zero_le'))
    have hv : vdeg O z (b - a i) * vdeg O z (a i) = vdeg O z b := by
      unfold vdeg
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [Pi.sub_apply, ← zpow_add₀ (hne c), sub_add_cancel]
    have hne' : vdeg O z (a i) ≠ 0 := by
      unfold vdeg
      exact Finset.prod_ne_zero_iff.mpr fun c _ => zpow_ne_zero _ (hne c)
    have h0 : vdeg O z (0 : K → ℤ) = 1 := by
      unfold vdeg
      simp
    rw [h0, mul_one]
    apply mul_right_cancel₀ hne'
    rw [hv, e]
  unfold inum at hz0 ⊢
  convert hadd using 1
  rw [hz0, zero_add]

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin d), inum k z (fun j => if j ∈ s then a' j else a j) = inum k z a`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `i s hi ih`.

Rewrite using `[← ih]`. Establish `e : (fun j => if j ∈ insert i s then a' j else a j) = Function.update (fun j => if j ∈ s then a' j else a j) i (a' i)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hj]`. Rewrite using `[e]`. Apply `inum_update h1 h3 hz ht` to reduce the goal to its premises. Simplify `(h i).symm` using `[hi]`.

Simplify using `using (key Finset.univ).symm`.
-/
theorem inum_congr (h1 : PtDim) (h3 : UnitZero) {z : (Σ b, ι b) → Ω} {d : ℕ} (hz : IsPt k z d) (ht : fnField k z = ⊤)
    (a a' : Fin d → K → ℤ) (h : ∀ j, ValEq k z (a j) z (a' j)) : inum k z a = inum k z a' := by
  classical
  have key : ∀ s : Finset (Fin d), inum k z (fun j => if j ∈ s then a' j else a j) = inum k z a := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi ih
      rw [← ih]
      have e : (fun j => if j ∈ insert i s then a' j else a j) =
          Function.update (fun j => if j ∈ s then a' j else a j) i (a' i) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [hj]
      rw [e]
      apply inum_update h1 h3 hz ht
      simpa [hi] using (h i).symm
  simpa using (key Finset.univ).symm

/- English proof (translation)
Unfold `fnField`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `t ⟨p, q, hpq, rfl⟩`. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Conclude with `⟨⟨Sum.inl p.1, p.2⟩, ⟨Sum.inl q.1, q.2⟩, congrArg Sum.inl hpq, rfl⟩`.
-/
theorem fnField_le_join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) : fnField k y ≤ fnField k (joinPt y y') := by
  unfold fnField
  rw [IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, hpq, rfl⟩
  apply IntermediateField.subset_adjoin
  exact ⟨⟨Sum.inl p.1, p.2⟩, ⟨Sum.inl q.1, q.2⟩, congrArg Sum.inl hpq, rfl⟩

/- English proof (translation)
Use `letI := (IntermediateField.inclusion h).toRingHom.toAlgebra`. Use `haveI : IsScalarTower F F' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Conclude with `Module.Finite.of_restrictScalars_finite F F' Ω`.
-/
theorem finite_of_le {F F' : IntermediateField k Ω} (h : F ≤ F') [FiniteDimensional F Ω] : FiniteDimensional F' Ω := by
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F F' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite F F' Ω

/- English proof (translation)
Take `⟨h0, hf, ht⟩` from `h`. Use `⟨?_, ?_, ht⟩` and prove the remaining obligations. Introduce and unpack `(b | b)`. Conclude with `h0 b`. Conclude with `h' b`.

Use `haveI := hf`. Conclude with `finite_of_le (fnField_le_join_inl (k := k) y y')`.
-/
theorem IsPt.join_inl {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d) (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) :
    IsPt k (joinPt y y') d := by
  obtain ⟨h0, hf, ht⟩ := h
  refine ⟨?_, ?_, ht⟩
  · rintro (b | b)
    · exact h0 b
    · exact h' b
  · haveI := hf
    exact finite_of_le (fnField_le_join_inl (k := k) y y')

/- English proof (translation)
Establish `hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inl : K → K ⊕ K') (fun p : (Σ b, ι b) => (⟨Sum.inl p.1, p.2⟩ : Σ b, Sum.elim ι ι' b))`. Use `⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩` and prove the remaining obligations. Introduce `p q hpq`. Take `⟨b, i⟩` from `p`. Take `⟨b', i'⟩` from `q`.

Consider the cases of `hpq`. Both sides reduce to the same expression. Introduce and unpack `⟨b, i⟩ ⟨c, rfl⟩`. Conclude with `⟨⟨c, i⟩, rfl⟩`. Establish `hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inl : K → K ⊕ K') (a j) = Sum.elim (a j) (0 : K' → ℤ)`.

Introduce `j`. Use function extensionality and compare the values at `x`. Consider the cases of `x with`. Consider the case `inl c => exact Sum.inl_injective.extend_apply (a j) 0 c`. Consider the case `inr c => show Function.extend Sum.inl (a j) 0 (Sum.inr c) = 0`.

Rewrite using `[Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]`. Both sides reduce to the same expression. Use `h2 k Ω K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl _ (joinPt y y') d a hv (h.join_inl h') h` as an intermediate fact. Simplify using `only [hp] at this`. Conclude with `this`.
-/
theorem num_join_inl (h2 : NumPull) {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d)
    (h' : ∀ b, ∃ i, y' ⟨b, i⟩ ≠ 0) (a : Fin d → K → ℤ) : num k (joinPt y y') (fun j => Sum.elim (a j) 0) = num k y a := by
  have hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inl : K → K ⊕ K')
      (fun p : (Σ b, ι b) => (⟨Sum.inl p.1, p.2⟩ : Σ b, Sum.elim ι ι' b)) := by
    refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
    · intro p q hpq
      obtain ⟨b, i⟩ := p
      obtain ⟨b', i'⟩ := q
      cases hpq
      rfl
    · rintro ⟨b, i⟩ ⟨c, rfl⟩
      exact ⟨⟨c, i⟩, rfl⟩
  have hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inl : K → K ⊕ K') (a j) = Sum.elim (a j) (0 : K' → ℤ) := by
    intro j
    funext x
    cases x with
    | inl c => exact Sum.inl_injective.extend_apply (a j) 0 c
    | inr c =>
      show Function.extend Sum.inl (a j) 0 (Sum.inr c) = 0
      rw [Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]
      rfl
  have := h2 k Ω K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl _ (joinPt y y') d a hv (h.join_inl h') h
  simp only [hp] at this
  exact this

/- English proof (translation)
Establish `hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inr : K' → K ⊕ K') (fun p : (Σ b, ι' b) => (⟨Sum.inr p.1, p.2⟩ : Σ b, Sum.elim ι ι' b))`. Use `⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩` and prove the remaining obligations. Introduce `p q hpq`. Take `⟨b, i⟩` from `p`. Take `⟨b', i'⟩` from `q`.

Consider the cases of `hpq`. Both sides reduce to the same expression. Introduce and unpack `⟨b, i⟩ ⟨c, rfl⟩`. Conclude with `⟨⟨c, i⟩, rfl⟩`. Establish `hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inr : K' → K ⊕ K') (a j) = Sum.elim (0 : K → ℤ) (a j)`.

Introduce `j`. Use function extensionality and compare the values at `x`. Consider the cases of `x with`. Consider the case `inr c => exact Sum.inr_injective.extend_apply (a j) 0 c`. Consider the case `inl c => show Function.extend Sum.inr (a j) 0 (Sum.inl c) = 0`.

Rewrite using `[Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]`. Both sides reduce to the same expression. Use `h2 k Ω K' ι' (K ⊕ K') (Sum.elim ι ι') Sum.inr _ (joinPt y y') d a hv (h.join_inl h'.1) h'` as an intermediate fact. Simplify using `only [hp] at this`. Conclude with `this`.
-/
theorem num_join_inr (h2 : NumPull) {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {d : ℕ} (h : IsPt k y d) (h' : IsPt k y' d)
    (a : Fin d → K' → ℤ) : num k (joinPt y y') (fun j => Sum.elim 0 (a j)) = num k y' a := by
  have hv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inr : K' → K ⊕ K')
      (fun p : (Σ b, ι' b) => (⟨Sum.inr p.1, p.2⟩ : Σ b, Sum.elim ι ι' b)) := by
    refine ⟨Sum.inr_injective, ?_, fun _ => rfl, ?_⟩
    · intro p q hpq
      obtain ⟨b, i⟩ := p
      obtain ⟨b', i'⟩ := q
      cases hpq
      rfl
    · rintro ⟨b, i⟩ ⟨c, rfl⟩
      exact ⟨⟨c, i⟩, rfl⟩
  have hp : ∀ j, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg (Sum.inr : K' → K ⊕ K') (a j) = Sum.elim (0 : K → ℤ) (a j) := by
    intro j
    funext x
    cases x with
    | inr c => exact Sum.inr_injective.extend_apply (a j) 0 c
    | inl c =>
      show Function.extend Sum.inr (a j) 0 (Sum.inl c) = 0
      rw [Function.extend_apply' _ _ _ (by rintro ⟨c', hc⟩; cases hc)]
      rfl
  have := h2 k Ω K' ι' (K ⊕ K') (Sum.elim ι ι') Sum.inr _ (joinPt y y') d a hv (h.join_inl h'.1) h'
  simp only [hp] at this
  exact this

/- English proof (translation)
Set `B` to `Module.finBasis (fnField k y) Ω`. Use `⟨_, fun x => x.2.elim 1 B, fun _ => ⟨none, one_ne_zero⟩, eq_top_iff.2 fun t _ => ?_⟩` and prove the remaining obligations. Rewrite using `[← B.sum_repr t]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Use `mul_mem (fnField_le_join_inl y _ (B.repr t i).2) (IntermediateField.subset_adjoin _ _ ?_)` and prove the remaining obligations. Conclude with `⟨⟨.inr (), some i⟩, ⟨.inr (), none⟩, rfl, (div_one _).symm⟩`.
-/
theorem exists_top (y : (Σ b, ι b) → Ω) [FiniteDimensional (fnField k y) Ω] :
    ∃ (m : ℕ) (w : (Σ _ : Unit, Option (Fin m)) → Ω), (∀ b, ∃ i, w ⟨b, i⟩ ≠ 0) ∧ fnField k (joinPt y w) = ⊤ := by
  let B := Module.finBasis (fnField k y) Ω
  refine ⟨_, fun x => x.2.elim 1 B, fun _ => ⟨none, one_ne_zero⟩, eq_top_iff.2 fun t _ => ?_⟩
  rw [← B.sum_repr t]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  refine mul_mem (fnField_le_join_inl y _ (B.repr t i).2) (IntermediateField.subset_adjoin _ _ ?_)
  exact ⟨⟨.inr (), some i⟩, ⟨.inr (), none⟩, rfl, (div_one _).symm⟩

/- English proof (translation)
Introduce `h1 h2 h3 k _ Ω _ _ K _ ι _ K' _ ι' _ y y' d a a' hy hy' h`. Establish `hj` using `hy.join_inl hy'.1`. Use `haveI := hj.2.1`. Take `⟨m, w, hw, ht⟩` from `exists_top (k := k) (joinPt y y')`. Rewrite using `[← num_join_inl h2 hy hy'.1, ← num_join_inr h2 hy hy', ← num_join_inl h2 hj hw, ← num_join_inl h2 hj hw]`.

Unfold `num`. Use `congr 1`. Use `inum_congr h1 h3 (hj.join_inl hw) ht _ _ fun j => ?_` and prove the remaining obligations. Conclude with `((ValEq.join_inl _ w _).trans (ValEq.join_inl y y' _)).trans ((h j).trans ((ValEq.join_inl _ w _).trans (ValEq.join_inr y y' _)).symm)`.
-/
theorem numEq : PtDim → NumPull → UnitZero → NumEq := by
  intro h1 h2 h3 k _ Ω _ _ K _ ι _ K' _ ι' _ y y' d a a' hy hy' h
  have hj := hy.join_inl hy'.1
  haveI := hj.2.1
  obtain ⟨m, w, hw, ht⟩ := exists_top (k := k) (joinPt y y')
  rw [← num_join_inl h2 hy hy'.1, ← num_join_inr h2 hy hy', ← num_join_inl h2 hj hw, ← num_join_inl h2 hj hw]
  unfold num
  congr 1
  refine inum_congr h1 h3 (hj.join_inl hw) ht _ _ fun j => ?_
  exact ((ValEq.join_inl _ w _).trans (ValEq.join_inl y y' _)).trans
    ((h j).trans ((ValEq.join_inl _ w _).trans (ValEq.join_inr y y' _)).symm)

end SheetDecomposition
