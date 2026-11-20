import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IndepSpanRankTransferLargeFieldComplexStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares.BasisVals

section Abs

variable {K K' V V' Q : Type} [Field K] [Field K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']

def SameLin (K K' : Type) {V V' Q : Type} [Field K] [Field K'] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K' V'] (W : Q → Prop) (f : Q → V) (g : Q → V') : Prop :=
  ∀ (ι : Type) [Fintype ι] (p : ι → Q), (∀ i, W (p i)) →
    (LinearIndependent K (fun i => f (p i)) ↔ LinearIndependent K' (fun i => g (p i))) ∧
    ∀ q, W q → (f q ∈ Submodule.span K (Set.range fun i => f (p i)) ↔
      g q ∈ Submodule.span K' (Set.range fun i => g (p i)))

/- English proof (translation)
Introduce `ι _ p hp` and use `⟨(h ι p hp).1.symm, fun q hq => ((h ι p hp).2 q hq).symm⟩`.
-/
theorem SameLin.symm {W : Q → Prop} {f : Q → V} {g : Q → V'} (h : SameLin K K' W f g) : SameLin K' K W g f :=
  fun ι _ p hp => ⟨(h ι p hp).1.symm, fun q hq => ((h ι p hp).2 q hq).symm⟩

/- English proof (translation)
Take `⟨κ, φ, hφ, hsp, hli⟩` from `exists_linearIndependent' K (fun i => f (b i))`. Use `haveI : Finite κ := Finite.of_injective φ hφ`. Use `letI : Fintype κ := Fintype.ofFinite κ`. Establish `h1 : LinearIndependent K (fun i : Fin n ⊕ κ => f (Sum.elim a (b ∘ φ) i))`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `d hd`. Rewrite `hd` using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Function.comp] at hd`. Establish `hl : ∀ i, d (Sum.inl i) = 0`. Apply `hi` to reduce the goal to its premises.

Rewrite using `[eq_neg_of_add_eq_zero_left hd]`. Conclude with `Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨φ i, rfl⟩))`. Simplify using `only [hl, zero_smul, Finset.sum_const_zero, zero_add] at hd`. Establish `hr` using `Fintype.linearIndependent_iff.1 hli (fun i => d (Sum.inr i)) hd`. Introduce and unpack `(i | i)`.

Conclude with `hl i`. Conclude with `hr i`. Establish `h2` using `(h (Fin n ⊕ κ) (Sum.elim a (b ∘ φ)) (by rintro (i | i); exacts [ha i, hb _])).1.1 h1`. Establish `h3 : Submodule.span K' (Set.range fun i => g (b i)) ≤ Submodule.span K' (Set.range fun i => g (b (φ i)))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `((h κ (fun i => b (φ i)) (fun i => hb _)).2 (b i) (hb i)).1 ?_` and prove the remaining obligations. Establish `: f (b i) ∈ Submodule.span K (Set.range fun i => f (b i))` using `Submodule.subset_span ⟨i, rfl⟩`. Rewrite `this` using `[← hsp]`. Conclude with `this`.

Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun K').1 (h3 hc)`. Establish `h4` using `Fintype.linearIndependent_iff.1 h2 (Sum.elim c (-d)) (by`. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Function.comp, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hd, add_neg_cancel])`. Conclude with `fun i => h4 (Sum.inl i)`.
-/
theorem SameLin.indep_mod {W : Q → Prop} {f : Q → V} {g : Q → V'} (h : SameLin K K' W f g) {n : ℕ} {ι : Type}
    [Fintype ι] (a : Fin n → Q) (b : ι → Q) (ha : ∀ i, W (a i)) (hb : ∀ i, W (b i))
    (hi : ∀ c : Fin n → K, ∑ i, c i • f (a i) ∈ Submodule.span K (Set.range fun i => f (b i)) → ∀ i, c i = 0)
    (c : Fin n → K') (hc : ∑ i, c i • g (a i) ∈ Submodule.span K' (Set.range fun i => g (b i))) : ∀ i, c i = 0 := by
  obtain ⟨κ, φ, hφ, hsp, hli⟩ := exists_linearIndependent' K (fun i => f (b i))
  haveI : Finite κ := Finite.of_injective φ hφ
  letI : Fintype κ := Fintype.ofFinite κ
  have h1 : LinearIndependent K (fun i : Fin n ⊕ κ => f (Sum.elim a (b ∘ φ) i)) := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    rw [Fintype.sum_sum_type] at hd
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp] at hd
    have hl : ∀ i, d (Sum.inl i) = 0 := by
      apply hi
      rw [eq_neg_of_add_eq_zero_left hd]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨φ i, rfl⟩))
    simp only [hl, zero_smul, Finset.sum_const_zero, zero_add] at hd
    have hr := Fintype.linearIndependent_iff.1 hli (fun i => d (Sum.inr i)) hd
    rintro (i | i)
    · exact hl i
    · exact hr i
  have h2 := (h (Fin n ⊕ κ) (Sum.elim a (b ∘ φ)) (by rintro (i | i); exacts [ha i, hb _])).1.1 h1
  have h3 : Submodule.span K' (Set.range fun i => g (b i)) ≤ Submodule.span K' (Set.range fun i => g (b (φ i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ((h κ (fun i => b (φ i)) (fun i => hb _)).2 (b i) (hb i)).1 ?_
    have : f (b i) ∈ Submodule.span K (Set.range fun i => f (b i)) := Submodule.subset_span ⟨i, rfl⟩
    rw [← hsp] at this
    exact this
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K').1 (h3 hc)
  have h4 := Fintype.linearIndependent_iff.1 h2 (Sum.elim c (-d)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hd,
      add_neg_cancel])
  exact fun i => h4 (Sum.inl i)

/- English proof (translation)
Simplify using `only [Submodule.mem_span_range_iff_exists_fun, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, d, h⟩`. Conclude with `⟨Sum.elim c d, by simp [h]⟩`. Introduce and unpack `⟨c, h⟩`.

Conclude with `⟨fun i => c (Sum.inl i), fun i => c (Sum.inr i), by rw [← h]; abel⟩`.
-/
theorem sub_mem_iff {n : ℕ} {ι : Type} [Fintype ι] (x : V) (a : Fin n → V) (b : ι → V) :
    (∃ c : Fin n → K, x - ∑ i, c i • a i ∈ Submodule.span K (Set.range b)) ↔
      x ∈ Submodule.span K (Set.range (Sum.elim a b)) := by
  simp only [Submodule.mem_span_range_iff_exists_fun, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨c, d, h⟩
    exact ⟨Sum.elim c d, by simp [h]⟩
  · rintro ⟨c, h⟩
    exact ⟨fun i => c (Sum.inl i), fun i => c (Sum.inr i), by rw [← h]; abel⟩

/- English proof (translation)
Rewrite using `[sub_mem_iff, sub_mem_iff]`. Use `(h (Fin n ⊕ ι) (Sum.elim a b) (by rintro (i | i); exacts [ha i, hb _])).2 q hq` as an intermediate fact. Establish `e1 : (fun i => f (Sum.elim a b i)) = Sum.elim (fun i => f (a i)) (fun i => f (b i))`. Apply the tactic sequence `funext i; cases i <;> rfl`. Establish `e2 : (fun i => g (Sum.elim a b i)) = Sum.elim (fun i => g (a i)) (fun i => g (b i))`.

Apply the tactic sequence `funext i; cases i <;> rfl`. Rewrite `this` using `[e1, e2]`. Then use the resulting hypothesis.
-/
theorem SameLin.mem_mod {W : Q → Prop} {f : Q → V} {g : Q → V'} (h : SameLin K K' W f g) {n : ℕ} {ι : Type}
    [Fintype ι] (q : Q) (a : Fin n → Q) (b : ι → Q) (hq : W q) (ha : ∀ i, W (a i)) (hb : ∀ i, W (b i)) :
    (∃ c : Fin n → K, f q - ∑ i, c i • f (a i) ∈ Submodule.span K (Set.range fun i => f (b i))) ↔
    (∃ c : Fin n → K', g q - ∑ i, c i • g (a i) ∈ Submodule.span K' (Set.range fun i => g (b i))) := by
  rw [sub_mem_iff, sub_mem_iff]
  have := (h (Fin n ⊕ ι) (Sum.elim a b) (by rintro (i | i); exacts [ha i, hb _])).2 q hq
  have e1 : (fun i => f (Sum.elim a b i)) = Sum.elim (fun i => f (a i)) (fun i => f (b i)) := by
    funext i; cases i <;> rfl
  have e2 : (fun i => g (Sum.elim a b i)) = Sum.elim (fun i => g (a i)) (fun i => g (b i)) := by
    funext i; cases i <;> rfl
  rwa [e1, e2] at this

/- English proof (translation)
Take `⟨i, -, hi⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) (by omega)`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i)]`. Establish `h1 : α i = 1` using `by omega`. Establish `h2 : ∑ x ∈ Finset.univ.erase i, α x = 0` using `by omega`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[h1]`. Rewrite using `[Pi.single_eq_of_ne hk]`.

Conclude with `Finset.sum_eq_zero_iff.1 h2 k (by simp [hk])`.
-/
theorem eq_single_of_sum_eq_one {d : ℕ} {α : Fin d → ℕ} (h : ∑ i, α i = 1) : ∃ i, α = Pi.single i 1 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) (by omega)
  refine ⟨i, ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
  have h1 : α i = 1 := by omega
  have h2 : ∑ x ∈ Finset.univ.erase i, α x = 0 := by omega
  funext k
  by_cases hk : k = i
  · subst hk; simp [h1]
  · rw [Pi.single_eq_of_ne hk]
    exact Finset.sum_eq_zero_iff.1 h2 k (by simp [hk])

/- English proof (translation)
Simplify using `[Pi.single_apply, pow_ite]`.
-/
theorem prod_pow_single {A : Type} [CommRing A] {d : ℕ} (s : Fin d → A) (i : Fin d) :
    ∏ k, s k ^ (Pi.single i 1 : Fin d → ℕ) k = s i := by
  simp [Pi.single_apply, pow_ite]

/- English proof (translation)
Take `⟨i, rfl⟩` from `eq_single_of_sum_eq_one h`. Rewrite using `[prod_pow_single]`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hf`. Rewrite using `[Finset.mul_sum]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, l), rfl⟩)`.
-/
theorem mon_mul_mem {A : Type} [CommRing A] [Algebra K A] {d n : ℕ} (s : Fin d → A) (e : Fin n → A)
    {α : Fin d → ℕ} (h : ∑ i, α i = 1) {f : A} (hf : f ∈ Submodule.span K (Set.range e)) :
    (∏ k, s k ^ α k) * f ∈ Submodule.span K (Set.range fun p : Fin d × Fin n => s p.1 * e p.2) := by
  obtain ⟨i, rfl⟩ := eq_single_of_sum_eq_one h
  rw [prod_pow_single]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hf
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [mul_smul_comm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, l), rfl⟩)

end Abs

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (R : Rdg X)
  (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)

def secPoly (i : Fin (WeightFamilies.dimY D j + 1)) : MvPolynomial (Idx D j N) X.Forms :=
  ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))

/- English proof (translation)
Introduce `ι _ p hp` and use `⟨(GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la N t hg u ι p hp).1, (GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la N t hg u ι p hp).2.1⟩`.
-/
theorem sameLin (hg : R.Generic t) (u : WeightFamilies.Wt D j) :
    SameLin (Kp X la N) ℂ (OfWt X u) (toRp X la N) (R.toFn t) := fun ι _ p hp =>
  ⟨(GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la N t hg u ι p hp).1, (GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la N t hg u ι p hp).2.1⟩

include R la t in
/- English proof (translation)
Take `⟨h1, -, -, h4, -⟩` from `GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t`. Proceed by induction on `n with`. Consider the case `zero => simpa using hq`. Consider the case `succ n ih`. Rewrite using `[pow_succ', mul_assoc, ← add_assoc, ← wadd_addL]`.

Conclude with `h4 _ _ _ _ (h1 0).2.2 ih`.
-/
theorem ofWt_pow_mul (u : WeightFamilies.Wt D j) (k n : ℕ) (q : MvPolynomial (Idx D j N) X.Forms)
    (hq : OfWt X (addL u wL k) q) : OfWt X (addL u wL (k + n)) (secPoly X w 0 ^ n * q) := by
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t
  induction n with
  | zero => simpa using hq
  | succ n ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← wadd_addL]
    exact h4 _ _ _ _ (h1 0).2.2 ih

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, -⟩` from `GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t`. Take `⟨n, e, he⟩` from `Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j (addL u wL m))`. Use `⟨n, fun p => secPoly X w p.1.succ * MvPolynomial.C (X.inc _ (e p.2)), fun p => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← wadd_addL]`. Conclude with `h4 _ _ _ _ (h1 _).2.2 (h3 _ _)`.

Simplify using `only [map_mul, secPoly, (h1 _).1, (h2 _).1]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨p, rfl⟩`. Use `secPow_mul_mem_Mon X la w (u := u) (a := 1) (n := m) (α := Pi.single p.1 1) (by simp) (emb_mem_Vw X la N _ (e p.2))` as an intermediate fact.

Rewrite `this` using `[secPow, prod_pow_single (fun i => sec X la w i.succ)]`. Then use the resulting hypothesis. Use `iSup₂_le fun α hα => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `mon_mul_mem (fun i => sec X la w i.succ) (fun l => emb X la N (X.inc _ (e l))) hα ?_` and prove the remaining obligations. Rewrite `hv` using `[Vw_eq_span_image X la N _ he, ← Set.range_comp]`.

Conclude with `hv`. Simplify using `only [map_mul, secPoly, (h1 _).2.1, (h2 _).2]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨p, rfl⟩`.

Use `Submodule.subset_span ⟨Pi.single p.1 1, R.ev (X.inc _ (e p.2)), by simp, Submodule.subset_span ⟨e p.2, trivial, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Rdg.mon, prod_pow_single (fun i => R.s w t i.succ)]`. Rewrite using `[Rdg.deep, Submodule.span_le]`. Introduce and unpack `_ ⟨α, f, hα, hf, rfl⟩`. Use `mon_mul_mem (fun i => R.s w t i.succ) (fun l => R.ev (X.inc _ (e l))) hα ?_` and prove the remaining obligations.

Use `h7 _ (Set.range e)` as an intermediate fact. Rewrite `this` using `[he, Submodule.top_coe]`. Rewrite `hf` using `[this, Rdg.sp, ← Set.range_comp]`. Conclude with `hf`.
-/
theorem exists_family (u : WeightFamilies.Wt D j) (m : ℕ) :
    ∃ (n : ℕ) (b : Fin (WeightFamilies.dimY D j) × Fin n → MvPolynomial (Idx D j N) X.Forms),
      (∀ i, OfWt X (addL u wL (m + 1)) (b i)) ∧
      Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (b i)) = Mon X la w u 1 m ∧
      Submodule.span ℂ (Set.range fun i => R.toFn t (b i)) = R.deep w t (addL u wL m) 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t
  obtain ⟨n, e, he⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j (addL u wL m))
  refine ⟨n, fun p => secPoly X w p.1.succ * MvPolynomial.C (X.inc _ (e p.2)), fun p => ?_, ?_, ?_⟩
  · rw [← wadd_addL]
    exact h4 _ _ _ _ (h1 _).2.2 (h3 _ _)
  · simp only [map_mul, secPoly, (h1 _).1, (h2 _).1]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      have := secPow_mul_mem_Mon X la w (u := u) (a := 1) (n := m) (α := Pi.single p.1 1) (by simp)
        (emb_mem_Vw X la N _ (e p.2))
      rwa [secPow, prod_pow_single (fun i => sec X la w i.succ)] at this
    · refine iSup₂_le fun α hα => ?_
      rintro _ ⟨v, hv, rfl⟩
      refine mon_mul_mem (fun i => sec X la w i.succ) (fun l => emb X la N (X.inc _ (e l))) hα ?_
      rw [Vw_eq_span_image X la N _ he, ← Set.range_comp] at hv
      exact hv
  · simp only [map_mul, secPoly, (h1 _).2.1, (h2 _).2]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      refine Submodule.subset_span ⟨Pi.single p.1 1, R.ev (X.inc _ (e p.2)), by simp,
        Submodule.subset_span ⟨e p.2, trivial, rfl⟩, ?_⟩
      rw [Rdg.mon, prod_pow_single (fun i => R.s w t i.succ)]
    · rw [Rdg.deep, Submodule.span_le]
      rintro _ ⟨α, f, hα, hf, rfl⟩
      refine mon_mul_mem (fun i => R.s w t i.succ) (fun l => R.ev (X.inc _ (e l))) hα ?_
      have := h7 _ (Set.range e)
      rw [he, Submodule.top_coe] at this
      rw [this, Rdg.sp, ← Set.range_comp] at hf
      exact hf

/- English proof (translation)
Take `⟨h1, h2, h3, -⟩` from `GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t`. Take `⟨r, b, hb, e1, e2⟩` from `exists_family X R la w t u m`. Establish `hs` using `sameLin X R la t hg (addL u wL (m + 1))`. Establish `ha : ∀ i, OfWt X (addL u wL (m + 1)) (secPoly X w 0 ^ (m + 1) * MvPolynomial.C (X.inc u (θ i)))` using `fun i => by`. Use `ofWt_pow_mul X R la w t u 0 (m + 1) (MvPolynomial.C (X.inc u (θ i))) (by rw [addL_zero]; exact h3 _ _)` as an intermediate fact.

Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Establish `i1` using `hs.indep_mod _ b ha hb`. Establish `i2` using `hs.symm.indep_mod _ b ha hb`. Rewrite `i1`, `i2` using `[e1, e2]`. Simplify using `only [map_mul, map_pow, secPoly, (h1 _).1, (h1 _).2.1, (h2 _).1, (h2 _).2] at i1 i2`.

Simplify using `only [Finset.mul_sum, mul_smul_comm]`. Conclude with `⟨i1, i2⟩`.
-/
theorem indep_transfer (hg : R.Generic t) (u : WeightFamilies.Wt D j) {n : ℕ} (θ : Fin n → B.Cusp j u) (m : ℕ) :
    (∀ c : Fin n → Kp X la N, sec X la w 0 ^ (m + 1) * ∑ i, c i • emb X la N (X.inc u (θ i)) ∈ Mon X la w u 1 m →
      ∀ i, c i = 0) ↔
    (∀ c : Fin n → ℂ, R.s w t 0 ^ (m + 1) * ∑ i, c i • R.ev (X.inc u (θ i)) ∈ R.deep w t (addL u wL m) 1 →
      ∀ i, c i = 0) := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t
  obtain ⟨r, b, hb, e1, e2⟩ := exists_family X R la w t u m
  have hs := sameLin X R la t hg (addL u wL (m + 1))
  have ha : ∀ i, OfWt X (addL u wL (m + 1)) (secPoly X w 0 ^ (m + 1) * MvPolynomial.C (X.inc u (θ i))) := fun i => by
    have := ofWt_pow_mul X R la w t u 0 (m + 1) (MvPolynomial.C (X.inc u (θ i))) (by rw [addL_zero]; exact h3 _ _)
    rwa [zero_add] at this
  have i1 := hs.indep_mod _ b ha hb
  have i2 := hs.symm.indep_mod _ b ha hb
  rw [e1, e2] at i1 i2
  simp only [map_mul, map_pow, secPoly, (h1 _).1, (h1 _).2.1, (h2 _).1, (h2 _).2] at i1 i2
  simp only [Finset.mul_sum, mul_smul_comm]
  exact ⟨i1, i2⟩

/- English proof (translation)
Take `⟨h1, h2, h3, -⟩` from `GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t`. Take `⟨r, b, hb, e1, e2⟩` from `exists_family X R la w t u (k + m)`. Establish `hs` using `sameLin X R la t hg (addL u wL (k + m + 1))`. Establish `ha : ∀ i, OfWt X (addL u wL (k + m + 1)) (secPoly X w 0 ^ (m + 1) * (secPoly X w 0 ^ k * MvPolynomial.C (X.inc u (θ i))))` using `fun i => by`. Use `ofWt_pow_mul X R la w t u 0 k (MvPolynomial.C (X.inc u (θ i))) (by rw [addL_zero]; exact h3 _ _)` as an intermediate fact.

Rewrite `this` using `[zero_add]`. Conclude with `ofWt_pow_mul X R la w t u k (m + 1) _ this`. Establish `i1` using `hs.mem_mod _ _ b (ofWt_pow_mul X R la w t u k (m + 1) _ hF) ha hb`. Rewrite `i1` using `[e1, e2]`. Simplify using `only [map_mul, map_pow, secPoly, (h1 _).1, (h1 _).2.1, (h2 _).1, (h2 _).2] at i1`.

Simplify using `only [mul_sub, Finset.mul_sum, mul_smul_comm]`. Conclude with `i1`.
-/
theorem mem_transfer (hg : R.Generic t) (u : WeightFamilies.Wt D j) {n : ℕ} (θ : Fin n → B.Cusp j u) (k m : ℕ) (F : X.Forms)
    (hF : OfWt X (addL u wL k) (MvPolynomial.C F : MvPolynomial (Idx D j N) X.Forms)) :
    (∃ c : Fin n → Kp X la N, sec X la w 0 ^ (m + 1) *
      (emb X la N F - sec X la w 0 ^ k * ∑ i, c i • emb X la N (X.inc u (θ i))) ∈ Mon X la w u 1 (k + m)) ↔
    (∃ c : Fin n → ℂ, R.s w t 0 ^ (m + 1) * (R.ev F - R.s w t 0 ^ k * ∑ i, c i • R.ev (X.inc u (θ i))) ∈
      R.deep w t (addL u wL (k + m)) 1) := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t
  obtain ⟨r, b, hb, e1, e2⟩ := exists_family X R la w t u (k + m)
  have hs := sameLin X R la t hg (addL u wL (k + m + 1))
  have ha : ∀ i, OfWt X (addL u wL (k + m + 1))
      (secPoly X w 0 ^ (m + 1) * (secPoly X w 0 ^ k * MvPolynomial.C (X.inc u (θ i)))) := fun i => by
    have := ofWt_pow_mul X R la w t u 0 k (MvPolynomial.C (X.inc u (θ i))) (by rw [addL_zero]; exact h3 _ _)
    rw [zero_add] at this
    exact ofWt_pow_mul X R la w t u k (m + 1) _ this
  have i1 := hs.mem_mod _ _ b (ofWt_pow_mul X R la w t u k (m + 1) _ hF) ha hb
  rw [e1, e2] at i1
  simp only [map_mul, map_pow, secPoly, (h1 _).1, (h1 _).2.1, (h2 _).1, (h2 _).2] at i1
  simp only [mul_sub, Finset.mul_sum, mul_smul_comm]
  exact i1

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Establish `key : ∀ c : Fin n → Kp X la N, ∑ i, c i • rho0 X la w u ⟨emb X la N (X.inc u (θ i)), emb_mem_Vw X la N u _⟩ = 0 ↔ ∃ m : ℕ, sec X la w 0 ^ (m + 1) * ∑ i, c i • emb X la N (X.inc u (θ i)) ∈ Mon X la w u 1 m`. Introduce `c`. Simplify using `only [← map_smul]`. Rewrite using `[← map_sum, restriction_eq_zero_iff_mem_vanishingFiltration, mem_Fil]`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, k, hk, h⟩`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Conclude with `⟨m, h⟩`.

Introduce and unpack `⟨m, h⟩`. Conclude with `⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (emb_mem_Vw X la N u _), m + 1, by omega, h⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h m c hc`. Conclude with `h c ((key c).2 ⟨m, hc⟩)`.

Introduce `h c hc`. Take `⟨m, hm⟩` from `(key c).1 hc`. Conclude with `h m c hm`.
-/
theorem indep_iff (u : WeightFamilies.Wt D j) {n : ℕ} (θ : Fin n → B.Cusp j u) :
    LinearIndependent (Kp X la N) (fun i => rho0 X la w u ⟨emb X la N (X.inc u (θ i)), emb_mem_Vw X la N u _⟩) ↔
    ∀ (m : ℕ) (c : Fin n → Kp X la N),
      sec X la w 0 ^ (m + 1) * ∑ i, c i • emb X la N (X.inc u (θ i)) ∈ Mon X la w u 1 m → ∀ i, c i = 0 := by
  rw [Fintype.linearIndependent_iff]
  have key : ∀ c : Fin n → Kp X la N,
      ∑ i, c i • rho0 X la w u ⟨emb X la N (X.inc u (θ i)), emb_mem_Vw X la N u _⟩ = 0 ↔
      ∃ m : ℕ, sec X la w 0 ^ (m + 1) * ∑ i, c i • emb X la N (X.inc u (θ i)) ∈ Mon X la w u 1 m := by
    intro c
    simp only [← map_smul]
    rw [← map_sum, restriction_eq_zero_iff_mem_vanishingFiltration, mem_Fil]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    constructor
    · rintro ⟨-, k, hk, h⟩
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact ⟨m, h⟩
    · rintro ⟨m, h⟩
      exact ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (emb_mem_Vw X la N u _), m + 1, by omega, h⟩
  constructor
  · intro h m c hc
    exact h c ((key c).2 ⟨m, hc⟩)
  · intro h c hc
    obtain ⟨m, hm⟩ := (key c).1 hc
    exact h m c hm

/- English proof (translation)
Rewrite using `[← WKoneEquiv_toWK, LinearEquiv.map_eq_zero_iff, ← rhoK_apply, rhoK_eq_zero_iff, mem_Fil]`. Simplify using `only [Mon_addL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, l, hl, h⟩`. Take `⟨m, rfl⟩ : ∃ m, l = m + 1` from `⟨l - 1, by omega⟩`.

Conclude with `⟨m, h⟩`. Introduce and unpack `⟨m, h⟩`. Conclude with `⟨f.2, m + 1, by omega, h⟩`.
-/
theorem class_eq_zero_iff (u : WeightFamilies.Wt D j) (k : ℕ) (f : ↥(Vw X la N (addL u wL k))) :
    toA0K X la w u (toHK X la w u k f) = 0 ↔ ∃ m : ℕ, sec X la w 0 ^ (m + 1) * f ∈ Mon X la w u 1 (k + m) := by
  rw [← WKoneEquiv_toWK, LinearEquiv.map_eq_zero_iff, ← rhoK_apply, rhoK_eq_zero_iff, mem_Fil]
  simp only [Mon_addL]
  constructor
  · rintro ⟨-, l, hl, h⟩
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact ⟨m, h⟩
  · rintro ⟨m, h⟩
    exact ⟨f.2, m + 1, by omega, h⟩

/- English proof (translation)
Use `sec_pow_mul_mem X la w 0 u 0 k (v := g) (by rw [addL_zero]; exact g.2)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem pow_mul_mem (u : WeightFamilies.Wt D j) (k : ℕ) (g : ↥(Vw X la N u)) :
    sec X la w 0 ^ k * g ∈ Vw X la N (addL u wL k) := by
  have := sec_pow_mul_mem X la w 0 u 0 k (v := g) (by rw [addL_zero]; exact g.2)
  rwa [zero_add] at this

/- English proof (translation)
Rewrite using `[restriction_apply_eq_reduction]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_toHK, coe_toHK0, ← frac_zero]`. Use `frac_pow_mul X la w 0 k g` as an intermediate fact.

Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem class_pow_mul (u : WeightFamilies.Wt D j) (k : ℕ) (g : ↥(Vw X la N u)) :
    toA0K X la w u (toHK X la w u k ⟨sec X la w 0 ^ k * g, pow_mul_mem X la w u k g⟩) = rho0 X la w u g := by
  rw [restriction_apply_eq_reduction]
  congr 1
  apply Subtype.ext
  rw [coe_toHK, coe_toHK0, ← frac_zero]
  have := frac_pow_mul X la w 0 k g
  rwa [zero_add] at this

/- English proof (translation)
Rewrite using `[Submodule.mem_span_range_iff_exists_fun, exists_comm]`. Use `exists_congr fun c => ?_` and prove the remaining obligations. Simplify using `only [← map_smul]`. Rewrite using `[← map_sum, ← class_pow_mul X la w u k, eq_comm, ← sub_eq_zero, ← map_sub, ← map_sub, class_eq_zero_iff]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_sub]`.
-/
theorem class_mem_iff (u : WeightFamilies.Wt D j) {n : ℕ} (θ : Fin n → B.Cusp j u) (k : ℕ) (f : ↥(Vw X la N (addL u wL k))) :
    toA0K X la w u (toHK X la w u k f) ∈ Submodule.span (Kp X la N)
      (Set.range fun i => rho0 X la w u ⟨emb X la N (X.inc u (θ i)), emb_mem_Vw X la N u _⟩) ↔
    ∃ (m : ℕ) (c : Fin n → Kp X la N), sec X la w 0 ^ (m + 1) *
      (f - sec X la w 0 ^ k * ∑ i, c i • emb X la N (X.inc u (θ i))) ∈ Mon X la w u 1 (k + m) := by
  rw [Submodule.mem_span_range_iff_exists_fun, exists_comm]
  refine exists_congr fun c => ?_
  simp only [← map_smul]
  rw [← map_sum, ← class_pow_mul X la w u k, eq_comm, ← sub_eq_zero, ← map_sub, ← map_sub, class_eq_zero_iff]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_sub]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k F`. Conclude with `(class_mem_iff X la w u θ k ⟨_, emb_mem_Vw X la N _ F⟩).1 (h ▸ Submodule.mem_top)`. Introduce `h`. Rewrite using `[eq_top_iff]`.

Introduce and unpack `x -`. Take `⟨k, ⟨f, hf⟩, rfl⟩` from `exists_reduction_fraction_eq X la w u x`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨F, rfl⟩` from `hf`.

Conclude with `(class_mem_iff X la w u θ k ⟨_, emb_mem_Vw X la N _ F⟩).2 (h k F)`. Consider the case `zero`. Establish `: (⟨0, Submodule.zero_mem _⟩ : ↥(Vw X la N (addL u wL k))) = 0` using `rfl`. Use `erw [this, map_zero, map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y hx hy ix iy`. Establish `: (⟨x + y, Submodule.add_mem _ hx hy⟩ : ↥(Vw X la N (addL u wL k))) = ⟨x, hx⟩ + ⟨y, hy⟩` using `rfl`. Use `erw [this, map_add, map_add]`. Conclude with `Submodule.add_mem _ ix iy`. Consider the case `smul a x hx ix`.

Establish `: (⟨a • x, Submodule.smul_mem _ _ hx⟩ : ↥(Vw X la N (addL u wL k))) = a • ⟨x, hx⟩` using `rfl`. Use `erw [this, map_smul, LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ _ ix`.
-/
theorem span_top_iff (u : WeightFamilies.Wt D j) {n : ℕ} (θ : Fin n → B.Cusp j u) :
    Submodule.span (Kp X la N)
      (Set.range fun i => rho0 X la w u ⟨emb X la N (X.inc u (θ i)), emb_mem_Vw X la N u _⟩) = ⊤ ↔
    ∀ (k : ℕ) (F : B.Cusp j (addL u wL k)), ∃ (m : ℕ) (c : Fin n → Kp X la N), sec X la w 0 ^ (m + 1) *
      (emb X la N (X.inc _ F) - sec X la w 0 ^ k * ∑ i, c i • emb X la N (X.inc u (θ i))) ∈
        Mon X la w u 1 (k + m) := by
  constructor
  · intro h k F
    exact (class_mem_iff X la w u θ k ⟨_, emb_mem_Vw X la N _ F⟩).1 (h ▸ Submodule.mem_top)
  · intro h
    rw [eq_top_iff]
    rintro x -
    obtain ⟨k, ⟨f, hf⟩, rfl⟩ := exists_reduction_fraction_eq X la w u x
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨F, rfl⟩ := hf
      exact (class_mem_iff X la w u θ k ⟨_, emb_mem_Vw X la N _ F⟩).2 (h k F)
    | zero =>
      have : (⟨0, Submodule.zero_mem _⟩ : ↥(Vw X la N (addL u wL k))) = 0 := rfl
      erw [this, map_zero, map_zero]
      exact Submodule.zero_mem _
    | add x y hx hy ix iy =>
      have : (⟨x + y, Submodule.add_mem _ hx hy⟩ : ↥(Vw X la N (addL u wL k))) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      erw [this, map_add, map_add]
      exact Submodule.add_mem _ ix iy
    | smul a x hx ix =>
      have : (⟨a • x, Submodule.smul_mem _ _ hx⟩ : ↥(Vw X la N (addL u wL k))) = a • ⟨x, hx⟩ := rfl
      erw [this, map_smul, LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ ix

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨α, f, hα, -, rfl⟩` from `hg`. Take `⟨i, rfl⟩` from `eq_single_of_sum_eq_one hα`. Rewrite using `[Rdg.mon, prod_pow_single (fun i => R.s w t i.succ), Pi.mul_apply, hy, zero_mul]`.

Consider the case `zero => rfl`. Consider the case `add x y _ _ hx hy => rw [Pi.add_apply, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [Pi.smul_apply, hx, smul_zero]`.
-/
theorem deep_vanish (u : WeightFamilies.Wt D j) {y : R.Y} (hy : ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ y = 0)
    {g : R.Y → ℂ} (hg : g ∈ R.deep w t u 1) : g y = 0 := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, f, hα, -, rfl⟩ := hg
    obtain ⟨i, rfl⟩ := eq_single_of_sum_eq_one hα
    rw [Rdg.mon, prod_pow_single (fun i => R.s w t i.succ), Pi.mul_apply, hy, zero_mul]
  | zero => rfl
  | add x y _ _ hx hy => rw [Pi.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [Pi.smul_apply, hx, smul_zero]

include la in
/- English proof (translation)
Take `⟨h1, -, -, -, h5, h6, -⟩` from `GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t`. Proceed by induction on `k with`. Consider the case `zero => rw [addL_zero]`. Simplify using `using hg`. Consider the case `succ n ih`.

Rewrite using `[pow_succ', mul_assoc, ← wadd_addL]`. Use `h6 _ _ _ ?_ _ ih` and prove the remaining obligations. Rewrite using `[← (h1 0).2.1]`. Conclude with `(h5 _ _ (h1 0).2.2).2`.
-/
theorem s_pow_mul_mem (u : WeightFamilies.Wt D j) (k : ℕ) {g : R.Y → ℂ} (hg : g ∈ R.sp u Set.univ) :
    R.s w t 0 ^ k * g ∈ R.sp (addL u wL k) Set.univ := by
  obtain ⟨h1, -, -, -, h5, h6, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t
  induction k with
  | zero => rw [addL_zero]; simpa using hg
  | succ n ih =>
    rw [pow_succ', mul_assoc, ← wadd_addL]
    refine h6 _ _ _ ?_ _ ih
    rw [← (h1 0).2.1]
    exact (h5 _ _ (h1 0).2.2).2

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨θ i, trivial, rfl⟩)`.
-/
theorem sum_mem_sp (u : WeightFamilies.Wt D j) {n : ℕ} (θ : Fin n → B.Cusp j u) (c : Fin n → ℂ) :
    ∑ i, c i • R.ev (X.inc u (θ i)) ∈ R.sp u Set.univ :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨θ i, trivial, rfl⟩)

end GlobalTheory.Shares.BasisVals

namespace GlobalTheory.Shares

open BasisVals

/- English proof (translation)
Introduce `D B P j X ka wL wF G R t T Mg δ xs hg hA _ la`. Take `⟨-, -, h3, -⟩` from `GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t`. Establish `hI : LinearIndependent (Kp X la G.N) (tL G la) ↔ LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (G.th' i)))`. Use `(indep_iff X la G.w wF G.th').trans ?_` and prove the remaining obligations. Simplify using `only [indep_transfer X R la G.w t hg wF G.th']`.

Rewrite using `[Fintype.linearIndependent_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h c hc`. Take `⟨m, hm⟩` from `hA.vandiv 0 (∑ i, c i • R.ev (X.inc wF (G.th' i))) (by rw [addL_zero]; exact sum_mem_sp X R wF G.th' c) (fun q => by simpa [vals, Finset.sum_apply] using congrFun hc q)`. Rewrite `hm` using `[zero_add]`.

Conclude with `h m c hm`. Introduce `h m c hc`. Apply `h c` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Use `deep_vanish X R G.w t _ (hA.zero q).2 hc` as an intermediate fact.

Rewrite `this` using `[Pi.mul_apply, Pi.pow_apply, mul_eq_zero]`. Use `this.resolve_left (pow_ne_zero _ (hA.zero q).1)` as an intermediate fact. Simplify `this` using `[vals, Finset.sum_apply]`. Establish `hS : Submodule.span (Kp X la G.N) (Set.range (tL G la)) = ⊤ ↔ Submodule.span ℂ (Set.range (vals xs fun i => R.ev (X.inc wF (G.th' i)))) = ⊤`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[eq_top_iff]`. Introduce and unpack `v -`. Take `⟨f, hf, hv⟩` from `hA.interp v`. Take `rfl : v = fun q => f (xs q)` from `funext fun q => (hv q).symm`.

Use `clear hv`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨F, -, rfl⟩` from `hf`. Establish `hF : emb X la G.N (X.inc wF F) ∈ Vw X la G.N (addL wF wL 0)`.

Rewrite using `[addL_zero]`. Conclude with `emb_mem_Vw X la G.N wF F`. Establish `htop : Submodule.span (Kp X la G.N) (Set.range fun i => rho0 X la G.w wF ⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF _⟩) = ⊤` using `h`. Take `⟨m, hm⟩` from `(class_mem_iff X la G.w wF G.th' 0 ⟨_, hF⟩).1 (htop ▸ Submodule.mem_top)`. Take `⟨c, hc⟩` from `(mem_transfer X R la G.w t hg wF G.th' 0 m (X.inc wF F) (by rw [addL_zero]; exact h3 _ _)).1 hm`.

Use `(Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Use `deep_vanish X R G.w t _ (hA.zero q).2 hc` as an intermediate fact. Rewrite `this` using `[Pi.mul_apply, Pi.pow_apply, mul_eq_zero]`. Use `this.resolve_left (pow_ne_zero _ (hA.zero q).1)` as an intermediate fact.

Rewrite `this` using `[pow_zero, one_mul, Pi.sub_apply, sub_eq_zero]`. Simplify `this.symm` using `[vals, Finset.sum_apply]`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => exact Submodule.smul_mem _ a hx`.

Introduce `h`. Use `(span_top_iff X la G.w wF G.th').2 fun k F => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 (h ▸ Submodule.mem_top : (fun q => R.ev (X.inc _ F) (xs q) / R.s G.w t 0 (xs q) ^ k) ∈ Submodule.span ℂ (Set.range (vals xs fun i => R.ev (X.inc wF (G.th' i)))))`. Take `⟨m, hm⟩` from `hA.vandiv k (R.ev (X.inc _ F) - R.s G.w t 0 ^ k * ∑ i, c i • R.ev (X.inc wF (G.th' i))) (Submodule.sub_mem _ (Submodule.subset_span ⟨F, trivial, rfl⟩) (s_pow_mul_mem X R la G.w t wF k (sum_mem_sp X R wF G.th' c))) (fun q => by`. Establish `h1 : (∑ i, c i • R.ev (X.inc wF (G.th' i))) (xs q) = R.ev (X.inc _ F) (xs q) / R.s G.w t 0 (xs q) ^ k`.

Simplify `congrFun hc q` using `[vals, Finset.sum_apply]`. Rewrite using `[Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, h1, mul_div_cancel₀ _ (pow_ne_zero _ (hA.zero q).1), sub_self])`. Conclude with `⟨m, (mem_transfer X R la G.w t hg wF G.th' k m (X.inc _ F) (h3 _ _)).2 ⟨c, hm⟩⟩`. Rewrite using `[InBasis, hI, hS]`. Use `and_congr_right fun hli => ?_` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `finrank_span_eq_card hli` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `using this.symm`.

Introduce `h`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hli]`. Simplify using `using h`.
-/
theorem inBasis_iff_vals : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → ∀ la, InBasis G la ↔ (LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (G.th' i))) ∧ G.del = δ) := by
  intro D B P j X ka wL wF G R t T Mg δ xs hg hA _ la
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  have hI : LinearIndependent (Kp X la G.N) (tL G la) ↔
      LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (G.th' i))) := by
    refine (indep_iff X la G.w wF G.th').trans ?_
    simp only [indep_transfer X R la G.w t hg wF G.th']
    rw [Fintype.linearIndependent_iff]
    constructor
    · intro h c hc
      obtain ⟨m, hm⟩ := hA.vandiv 0 (∑ i, c i • R.ev (X.inc wF (G.th' i)))
        (by rw [addL_zero]; exact sum_mem_sp X R wF G.th' c)
        (fun q => by simpa [vals, Finset.sum_apply] using congrFun hc q)
      rw [zero_add] at hm
      exact h m c hm
    · intro h m c hc
      apply h c
      funext q
      have := deep_vanish X R G.w t _ (hA.zero q).2 hc
      rw [Pi.mul_apply, Pi.pow_apply, mul_eq_zero] at this
      have := this.resolve_left (pow_ne_zero _ (hA.zero q).1)
      simpa [vals, Finset.sum_apply] using this
  have hS : Submodule.span (Kp X la G.N) (Set.range (tL G la)) = ⊤ ↔
      Submodule.span ℂ (Set.range (vals xs fun i => R.ev (X.inc wF (G.th' i)))) = ⊤ := by
    constructor
    · intro h
      rw [eq_top_iff]
      rintro v -
      obtain ⟨f, hf, hv⟩ := hA.interp v
      obtain rfl : v = fun q => f (xs q) := funext fun q => (hv q).symm
      clear hv
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨F, -, rfl⟩ := hf
        have hF : emb X la G.N (X.inc wF F) ∈ Vw X la G.N (addL wF wL 0) := by
          rw [addL_zero]; exact emb_mem_Vw X la G.N wF F
        have htop : Submodule.span (Kp X la G.N) (Set.range fun i => rho0 X la G.w wF
          ⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF _⟩) = ⊤ := h
        obtain ⟨m, hm⟩ := (class_mem_iff X la G.w wF G.th' 0 ⟨_, hF⟩).1 (htop ▸ Submodule.mem_top)
        obtain ⟨c, hc⟩ := (mem_transfer X R la G.w t hg wF G.th' 0 m (X.inc wF F)
          (by rw [addL_zero]; exact h3 _ _)).1 hm
        refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, ?_⟩
        funext q
        have := deep_vanish X R G.w t _ (hA.zero q).2 hc
        rw [Pi.mul_apply, Pi.pow_apply, mul_eq_zero] at this
        have := this.resolve_left (pow_ne_zero _ (hA.zero q).1)
        rw [pow_zero, one_mul, Pi.sub_apply, sub_eq_zero] at this
        simpa [vals, Finset.sum_apply] using this.symm
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul a x _ hx => exact Submodule.smul_mem _ a hx
    · intro h
      refine (span_top_iff X la G.w wF G.th').2 fun k F => ?_
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
        (h ▸ Submodule.mem_top : (fun q => R.ev (X.inc _ F) (xs q) / R.s G.w t 0 (xs q) ^ k) ∈
          Submodule.span ℂ (Set.range (vals xs fun i => R.ev (X.inc wF (G.th' i)))))
      obtain ⟨m, hm⟩ := hA.vandiv k (R.ev (X.inc _ F) - R.s G.w t 0 ^ k * ∑ i, c i • R.ev (X.inc wF (G.th' i)))
        (Submodule.sub_mem _ (Submodule.subset_span ⟨F, trivial, rfl⟩)
          (s_pow_mul_mem X R la G.w t wF k (sum_mem_sp X R wF G.th' c)))
        (fun q => by
          have h1 : (∑ i, c i • R.ev (X.inc wF (G.th' i))) (xs q) =
              R.ev (X.inc _ F) (xs q) / R.s G.w t 0 (xs q) ^ k := by
            simpa [vals, Finset.sum_apply] using congrFun hc q
          rw [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, h1, mul_div_cancel₀ _ (pow_ne_zero _ (hA.zero q).1), sub_self])
      exact ⟨m, (mem_transfer X R la G.w t hg wF G.th' k m (X.inc _ F) (h3 _ _)).2 ⟨c, hm⟩⟩
  rw [InBasis, hI, hS]
  refine and_congr_right fun hli => ?_
  constructor
  · intro h
    have := finrank_span_eq_card hli
    rw [h] at this
    simpa using this.symm
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli]
    simpa using h

end GlobalTheory.Shares
