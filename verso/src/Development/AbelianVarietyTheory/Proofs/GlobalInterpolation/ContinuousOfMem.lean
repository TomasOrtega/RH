import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CoordinateEmbeddingSplits

section General

variable {G : Type} [Mul G]

def Splits (A : Subalgebra ℂ (G → ℂ)) (p : G → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → G → ℂ), (∀ i, a i ∈ A ∧ b i ∈ A) ∧
    ∀ x k, p (x * k) = ∑ i, a i x * b i k

/- English proof (translation)
Introduce `p hp`. Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem p hp => exact hS p hp`. Consider the case `algebraMap c`. Conclude with `⟨Unit, inferInstance, fun _ => algebraMap ℂ _ c, fun _ => 1, fun _ => ⟨Subalgebra.algebraMap_mem _ c, one_mem _⟩, fun x k => by simp⟩`.

Consider the case `add p q _ _ hp hq`. Take `⟨ι, _, a, b, hab, h⟩` from `hp`. Take `⟨κ, _, c, d, hcd, h'⟩` from `hq`. Use `⟨ι ⊕ κ, inferInstance, Sum.elim a c, Sum.elim b d, ?_, fun x k => ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | i)`.

Conclude with `hab i`. Conclude with `hcd i`. Rewrite using `[Pi.add_apply, h, h', Fintype.sum_sum_type]`. Both sides reduce to the same expression. Consider the case `mul p q _ _ hp hq`.

Take `⟨ι, _, a, b, hab, h⟩` from `hp`. Take `⟨κ, _, c, d, hcd, h'⟩` from `hq`. Use `⟨ι × κ, inferInstance, fun t => a t.1 * c t.2, fun t => b t.1 * d t.2, fun t => ⟨mul_mem (hab _).1 (hcd _).1, mul_mem (hab _).2 (hcd _).2⟩, fun x k => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem splits_adjoin (S : Set (G → ℂ)) (hS : ∀ p ∈ S, Splits (Algebra.adjoin ℂ S) p) :
    ∀ p ∈ Algebra.adjoin ℂ S, Splits (Algebra.adjoin ℂ S) p := by
  intro p hp
  induction hp using Algebra.adjoin_induction with
  | mem p hp => exact hS p hp
  | algebraMap c =>
    exact ⟨Unit, inferInstance, fun _ => algebraMap ℂ _ c, fun _ => 1,
      fun _ => ⟨Subalgebra.algebraMap_mem _ c, one_mem _⟩, fun x k => by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨ι, _, a, b, hab, h⟩ := hp
    obtain ⟨κ, _, c, d, hcd, h'⟩ := hq
    refine ⟨ι ⊕ κ, inferInstance, Sum.elim a c, Sum.elim b d, ?_, fun x k => ?_⟩
    · rintro (i | i)
      · exact hab i
      · exact hcd i
    · rw [Pi.add_apply, h, h', Fintype.sum_sum_type]
      rfl
  | mul p q _ _ hp hq =>
    obtain ⟨ι, _, a, b, hab, h⟩ := hp
    obtain ⟨κ, _, c, d, hcd, h'⟩ := hq
    refine ⟨ι × κ, inferInstance, fun t => a t.1 * c t.2, fun t => b t.1 * d t.2,
      fun t => ⟨mul_mem (hab _).1 (hcd _).1, mul_mem (hab _).2 (hcd _).2⟩, fun x k => ?_⟩
    rw [Pi.mul_apply, h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.mul_apply]
    ring

/- English proof (translation)
Take `⟨ι, _, a, b, hab, h⟩` from `h`. Use `⟨Fintype.card ι, fun i => a ((Fintype.equivFin ι).symm i), fun i => b ((Fintype.equivFin ι).symm i), fun i => hab _, fun x k => ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `(Equiv.sum_comp (Fintype.equivFin ι).symm fun i => a i x * b i k).symm`.
-/
theorem Splits.fin {A : Subalgebra ℂ (G → ℂ)} {p : G → ℂ} (h : Splits A p) :
    ∃ (m : ℕ) (a b : Fin m → G → ℂ), (∀ i, a i ∈ A ∧ b i ∈ A) ∧
      ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  obtain ⟨ι, _, a, b, hab, h⟩ := h
  refine ⟨Fintype.card ι, fun i => a ((Fintype.equivFin ι).symm i), fun i => b ((Fintype.equivFin ι).symm i),
    fun i => hab _, fun x k => ?_⟩
  rw [h]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm fun i => a i x * b i k).symm

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Unfold `coord`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem coord_star (τ : E →+* ℂ) (a : Cinf E) : coord τ (star a) = star (coord τ a) := by
  unfold coord
  split_ifs <;> rfl

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Unfold `coord`. Use `split_ifs`. Conclude with `continuous_apply (InfinitePlace.mk τ)`. Conclude with `Complex.continuous_conj.comp (continuous_apply (InfinitePlace.mk τ))`.
-/
theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply (InfinitePlace.mk τ)
  · exact Complex.continuous_conj.comp (continuous_apply (InfinitePlace.mk τ))

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Unfold `coord`. Rewrite using `[InfinitePlace.mk_embedding, if_pos rfl]`. Both sides reduce to the same expression.
-/
theorem coord_embedding (w : InfinitePlace E) (a : Cinf E) : coord w.embedding a = a w := by
  unfold coord
  rw [InfinitePlace.mk_embedding, if_pos rfl]
  rfl

/- English proof (translation)
Establish `hne : ComplexEmbedding.conjugate τ ≠ τ` using `fun h => (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))) ⟨τ, ComplexEmbedding.isReal_iff.2 h, rfl⟩`. Unfold `coord`. Rewrite using `[InfinitePlace.mk_conjugate_eq]`. Break down `InfinitePlace.embedding_mk_eq τ with h | h` into its components or cases. Rewrite using `[if_pos h, if_neg (fun h' => hne (h'.symm.trans h))]`.

Both sides reduce to the same expression. Rewrite using `[if_pos h, if_neg (fun h' => hne (h.symm.trans h'))]`. Conclude with `(star_star _).symm`.
-/
theorem coord_conjugate (τ : E →+* ℂ) (a : Cinf E) :
    coord (ComplexEmbedding.conjugate τ) a = star (coord τ a) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      ⟨τ, ComplexEmbedding.isReal_iff.2 h, rfl⟩
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (fun h' => hne (h'.symm.trans h))]
    rfl
  · rw [if_pos h, if_neg (fun h' => hne (h.symm.trans h'))]
    exact (star_star _).symm

/- English proof (translation)
Establish `: Continuous (infEq E).symm` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)`. Conclude with `this.comp continuous_fst`.
-/
theorem continuous_pInf : Continuous (pInf E) := by
  have : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  exact this.comp continuous_fst

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(infEq E).symm (infEq E _) = _`. Rewrite using `[RingEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem pInf_conj (a : Ad E) : pInf E (conjAd E a) = star (pInf E a) := by
  change (infEq E).symm (infEq E _) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cEmb_apply (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x).val i j = coord τ (pInf E (x.1.val i j)) := rfl

/- English proof (translation)
Establish `h : (x.1.val.map (conjAd E))ᵀ * 1 * x.1.val = 1` using `x.2`. Rewrite `h` using `[Matrix.mul_one]`. Establish `h2 : (x.1⁻¹).val = (x.1.val.map (conjAd E))ᵀ` using `Units.inv_eq_of_mul_eq_one_left h`. Rewrite using `[cEmb_apply, cEmb_apply, ← coord_star, ← pInf_conj]`. Conclude with `congrArg (fun M : Matrix (Fin n) (Fin n) (Ad E) => coord τ (pInf E (M i j))) h2`.
-/
theorem cEmb_inv (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x⁻¹).val i j = star ((cEmb τ x).val j i) := by
  have h : (x.1.val.map (conjAd E))ᵀ * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at h
  have h2 : (x.1⁻¹).val = (x.1.val.map (conjAd E))ᵀ := Units.inv_eq_of_mul_eq_one_left h
  rw [cEmb_apply, cEmb_apply, ← coord_star, ← pInf_conj]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) (Ad E) => coord τ (pInf E (M i j))) h2

variable (E n) in

abbrev coeffs : Set (infU E n → ℂ) :=
  {f | ∃ (τ : E →+* ℂ) (i : Fin n) (j : Fin n), f = fun x : infU E n => (cEmb τ x.val).val i j}

/- English proof (translation)
Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem p hp`. Take `⟨τ, i, j, rfl⟩` from `hp`. Establish `h : Continuous fun x : infU E n => x.1.1.val i j` using `(Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j`. Conclude with `(continuous_coord τ).comp (continuous_pInf.comp h)`.

Consider the case `algebraMap c => exact continuous_const`. Consider the case `add p q _ _ hp hq => exact hp.add hq`. Consider the case `mul p q _ _ hp hq => exact hp.mul hq`.
-/
theorem continuous_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) : Continuous p := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    have h : Continuous fun x : infU E n => x.1.1.val i j :=
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j
    exact (continuous_coord τ).comp (continuous_pInf.comp h)
  | algebraMap c => exact continuous_const
  | add p q _ _ hp hq => exact hp.add hq
  | mul p q _ _ hp hq => exact hp.mul hq

/- English proof (translation)
Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem p hp`. Take `⟨τ, i, j, rfl⟩` from `hp`. Conclude with `Algebra.subset_adjoin ⟨ComplexEmbedding.conjugate τ, i, j, funext fun x => (coord_conjugate τ _).symm⟩`. Consider the case `algebraMap c => exact Subalgebra.algebraMap_mem _ (star c)`.

Consider the case `add p q _ _ hp hq => rw [star_add]`. Conclude with `add_mem hp hq`. Consider the case `mul p q _ _ hp hq => rw [star_mul]`. Conclude with `mul_mem hq hp`.
-/
theorem star_mem_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) :
    star p ∈ Algebra.adjoin ℂ (coeffs E n) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    exact Algebra.subset_adjoin ⟨ComplexEmbedding.conjugate τ, i, j, funext fun x => (coord_conjugate τ _).symm⟩
  | algebraMap c => exact Subalgebra.algebraMap_mem _ (star c)
  | add p q _ _ hp hq => rw [star_add]; exact add_mem hp hq
  | mul p q _ _ hp hq => rw [star_mul]; exact mul_mem hq hp

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `hxy (Subtype.ext (Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))))` and prove the remaining obligations. Establish `h1 : pInf E (x.1.1.val i j) = pInf E (y.1.1.val i j)`. Use function extensionality and compare the values at `w`. Use `(coord_embedding w _).symm.trans (Eq.trans ?_ (coord_embedding w _))` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Conclude with `hcon ⟨_, Algebra.subset_adjoin ⟨w.embedding, i, j, rfl⟩, hne⟩`. Establish `hx : GeneralLinearGroup.map (pFin E) x.1.1 = 1` using `x.2`. Establish `hy : GeneralLinearGroup.map (pFin E) y.1.1 = 1` using `y.2`. Establish `h2` using `congrArg (fun g : GL (Fin n) (Af E) => g.val i j) (hx.trans hy.symm)`.

Conclude with `Prod.ext ((infEq E).symm.injective h1) h2`.
-/
theorem separates (x y : infU E n) (hxy : x ≠ y) : ∃ p ∈ Algebra.adjoin ℂ (coeffs E n), p x ≠ p y := by
  by_contra hcon
  refine hxy (Subtype.ext (Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))))
  have h1 : pInf E (x.1.1.val i j) = pInf E (y.1.1.val i j) := by
    funext w
    refine (coord_embedding w _).symm.trans (Eq.trans ?_ (coord_embedding w _))
    by_contra hne
    exact hcon ⟨_, Algebra.subset_adjoin ⟨w.embedding, i, j, rfl⟩, hne⟩
  have hx : GeneralLinearGroup.map (pFin E) x.1.1 = 1 := x.2
  have hy : GeneralLinearGroup.map (pFin E) y.1.1 = 1 := y.2
  have h2 := congrArg (fun g : GL (Fin n) (Af E) => g.val i j) (hx.trans hy.symm)
  exact Prod.ext ((infEq E).symm.injective h1) h2

/- English proof (translation)
Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem p hp`. Take `⟨τ, i, j, rfl⟩` from `hp`. Establish `h` using `star_mem_of_mem (E := E) (n := n) _ (Algebra.subset_adjoin ⟨τ, j, i, rfl⟩)`. Establish `e : (fun x : infU E n => (cEmb τ (x⁻¹).val).val i j) = star fun x : infU E n => (cEmb τ x.val).val j i` using `funext fun x => cEmb_inv τ x.1 i j`.

Conclude with `e ▸ h`. Consider the case `algebraMap c => exact Subalgebra.algebraMap_mem _ c`. Consider the case `add p q _ _ hp hq => exact add_mem hp hq`. Consider the case `mul p q _ _ hp hq => exact mul_mem hp hq`.
-/
theorem inv_mem_of_mem (p : infU E n → ℂ) (hp : p ∈ Algebra.adjoin ℂ (coeffs E n)) :
    (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ (coeffs E n) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨τ, i, j, rfl⟩ := hp
    have h := star_mem_of_mem (E := E) (n := n) _ (Algebra.subset_adjoin ⟨τ, j, i, rfl⟩)
    have e : (fun x : infU E n => (cEmb τ (x⁻¹).val).val i j) =
        star fun x : infU E n => (cEmb τ x.val).val j i := funext fun x => cEmb_inv τ x.1 i j
    exact e ▸ h
  | algebraMap c => exact Subalgebra.algebraMap_mem _ c
  | add p q _ _ hp hq => exact add_mem hp hq
  | mul p q _ _ hp hq => exact mul_mem hp hq

/- English proof (translation)
Use `splits_adjoin _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, i, j, rfl⟩`. Use `⟨Fin n, inferInstance, fun l x => (cEmb τ x.val).val i l, fun l x => (cEmb τ x.val).val l j, fun l => ⟨Algebra.subset_adjoin ⟨τ, i, l, rfl⟩, Algebra.subset_adjoin ⟨τ, l, j, rfl⟩⟩, fun x k => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cEmb τ (x.val * k.val)).val i j = _`. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_apply]`.
-/
theorem splits_of_mem : ∀ p ∈ Algebra.adjoin ℂ (coeffs E n), Splits (Algebra.adjoin ℂ (coeffs E n)) p := by
  refine splits_adjoin _ ?_
  rintro _ ⟨τ, i, j, rfl⟩
  refine ⟨Fin n, inferInstance, fun l x => (cEmb τ x.val).val i l, fun l x => (cEmb τ x.val).val l j,
    fun l => ⟨Algebra.subset_adjoin ⟨τ, i, l, rfl⟩, Algebra.subset_adjoin ⟨τ, l, j, rfl⟩⟩, fun x k => ?_⟩
  change (cEmb τ (x.val * k.val)).val i j = _
  rw [map_mul, Units.val_mul, Matrix.mul_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨continuous_of_mem, star_mem_of_mem, separates, inv_mem_of_mem, fun p hp => (splits_of_mem p hp).fin⟩`.
-/
theorem main (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), Continuous p) ∧
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), star p ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
    (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ (coeffs E n), p x ≠ p y) ∧
    (∀ p ∈ Algebra.adjoin ℂ (coeffs E n), (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
    ∀ p ∈ Algebra.adjoin ℂ (coeffs E n), ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ),
      (∀ i, a i ∈ Algebra.adjoin ℂ (coeffs E n) ∧ b i ∈ Algebra.adjoin ℂ (coeffs E n)) ∧
        ∀ x k : infU E n, p (x * k) = ∑ i, a i x * b i k :=
  ⟨continuous_of_mem, star_mem_of_mem, separates, inv_mem_of_mem, fun p hp => (splits_of_mem p hp).fin⟩

end GlobalTheory.CoordinateEmbeddingSplits

end
