import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottComplex.StSpecOf

universe u v

namespace PIW.ENSpec

open MvPolynomial RingTheory.Sequence
open scoped Pointwise

section General

variable {S : Type u} [CommRing S]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Proceed by induction. A detailed English derivation is pending.
-/
theorem wreg_of_subsingleton {M : Type v} [AddCommGroup M] [Module S M] [Subsingleton M] (rs : List S) :
    IsWeaklyRegular M rs := by
  refine (isWeaklyRegular_iff M rs).2 fun i _ => ?_
  intro a b _
  induction a using Submodule.Quotient.induction_on
  induction b using Submodule.Quotient.induction_on
  exact congrArg _ (Subsingleton.elim _ _)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem wreg_ses (rs : List S) : ∀ {M' M M'' : Type v} [AddCommGroup M'] [Module S M'] [AddCommGroup M]
    [Module S M] [AddCommGroup M''] [Module S M''] (f : M' →ₗ[S] M) (g : M →ₗ[S] M''),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsWeaklyRegular M' rs → IsWeaklyRegular M'' rs → IsWeaklyRegular M rs := by
  induction rs with
  | nil => intros; exact IsWeaklyRegular.nil S _
  | cons r rs ih =>
    intro M' M M'' _ _ _ _ _ _ f g hf hfg hg h1 h2
    rw [isWeaklyRegular_cons_iff] at h1 h2 ⊢
    refine ⟨isSMulRegular_of_range_eq_ker hf hfg.linearMap_ker_eq.symm h1.1 h2.1, ?_⟩
    refine ih (QuotSMulTop.map r f) (QuotSMulTop.map r g) ?_ (QuotSMulTop.map_exact r hfg hg)
      (QuotSMulTop.map_surjective r hg) h1.2 h2.2
    have h0 : Function.Exact (0 : PUnit.{v + 1} →ₗ[S] M') f :=
      (LinearMap.exact_zero_iff_injective _ f).2 hf
    have he := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h0 hfg h2.1
    rw [map_zero] at he
    exact (LinearMap.exact_zero_iff_injective _ _).1 he

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem wreg_neg {M : Type v} [AddCommGroup M] [Module S M] (rs : List S) :
    IsWeaklyRegular M (rs.map Neg.neg) ↔ IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil => simp
  | cons r rs ih =>
    have hs : ((-r) • ⊤ : Submodule S M) = r • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.span_singleton_neg,
        Submodule.ideal_span_singleton_smul]
    have hreg : IsSMulRegular M (-r) ↔ IsSMulRegular M r := by
      constructor
      · intro h a b hab
        exact h (by simp only [neg_smul] at hab ⊢; exact congrArg Neg.neg hab)
      · intro h a b hab
        exact h (by simp only [neg_smul] at hab; exact neg_injective hab)
    rw [List.map_cons, isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff, hreg,
      ih (M := QuotSMulTop (-r) M)]
    exact and_congr_right fun _ =>
      (Submodule.quotEquivOfEq _ _ hs).isWeaklyRegular_congr rs

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem forall₂_ofFn {α β : Type*} {P : α → β → Prop} :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, P (f i) (g i)) →
      List.Forall₂ P (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (forall₂_ofFn _ _ fun i => h i.succ)

end General

section Piece

variable {R : Type u} [CommRing R] {D : ℕ}

local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem homog_mem_pow {a : ℕ} {p : MvPolynomial (Fin D) R} (hp : p.IsHomogeneous a) : p ∈ 𝔛 ^ a := by
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff]
  intro d hd
  have h0 := hp (mem_support_iff.1 hd)
  have h1 : d.degree = a := by rw [Finsupp.degree_eq_weight_one]; exact h0
  omega

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. By extensionality, compare the relevant components. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem homog_mem_pow_succ {a : ℕ} {p : MvPolynomial (Fin D) R} (hp : p.IsHomogeneous a)
    (h : p ∈ 𝔛 ^ (a + 1)) : p = 0 := by
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff] at h
  ext d
  by_contra hne
  have h0 := hp hne
  have h1 : d.degree = a := by rw [Finsupp.degree_eq_weight_one]; exact h0
  have h2 := h d (mem_support_iff.2 hne)
  omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem free_homog (a : ℕ) : Module.Free R (homogeneousSubmodule (Fin D) R a) :=
  Module.Free.of_equiv
    ((LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin D) R a)).trans
      (((AddMonoidAlgebra.coeffLinearEquiv R).ofSubmodule' _).trans
        (Finsupp.supportedEquivFinsupp _))).symm

noncomputable def gmap (a : ℕ) : (MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) →ₗ[MvPolynomial (Fin D) R]
    (MvPolynomial (Fin D) R ⧸ 𝔛 ^ a) :=
  Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ a))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gmap_mk (a : ℕ) (p : MvPolynomial (Fin D) R) :
    gmap a (Submodule.Quotient.mk p) = Submodule.Quotient.mk p :=
  Submodule.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ a)) p

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gmap_surjective (a : ℕ) : Function.Surjective (gmap (R := R) (D := D) a) :=
  Submodule.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ a))

noncomputable def emb (a : ℕ) : homogeneousSubmodule (Fin D) R a →+ LinearMap.ker (gmap (R := R) (D := D) a) where
  toFun h := ⟨Submodule.Quotient.mk h.1, by
    rw [LinearMap.mem_ker, gmap_mk, Submodule.Quotient.mk_eq_zero]; exact homog_mem_pow h.2⟩
  map_zero' := by ext; simp
  map_add' h h' := by ext; simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem emb_injective (a : ℕ) : Function.Injective (emb (R := R) (D := D) a) := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  have h1 : (Submodule.Quotient.mk h.1 : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) = 0 :=
    congrArg Subtype.val hh
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact Subtype.ext (homog_mem_pow_succ h.2 h1)

/- English proof (translation)
Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem emb_surjective (a : ℕ) : Function.Surjective (emb (R := R) (D := D) a) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearMap.mem_ker, gmap_mk, Submodule.Quotient.mk_eq_zero] at hq
  refine ⟨⟨homogeneousComponent a p, homogeneousComponent_mem a p⟩, ?_⟩
  apply Subtype.ext
  change (Submodule.Quotient.mk (homogeneousComponent a p) : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) =
    Submodule.Quotient.mk p
  rw [Submodule.Quotient.eq, show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff']
  rw [show 𝔛 = idealOfVars (Fin D) R from rfl, mem_pow_idealOfVars_iff'] at hq
  intro d hd
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : d.degree = a
  · simp [h]
  · have : d.degree < a := by omega
    simp [h, hq d this]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem emb_smul (a : ℕ) (x : Fin D → R) (i : Fin D) (h : homogeneousSubmodule (Fin D) R a) :
    emb a ((-x i) • h) = (MvPolynomial.X i - MvPolynomial.C (x i)) • emb a h := by
  apply Subtype.ext
  change (Submodule.Quotient.mk ((-x i) • h.1) : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) =
    (MvPolynomial.X i - MvPolynomial.C (x i)) • Submodule.Quotient.mk h.1
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_C_mul, smul_eq_mul]
  have : MvPolynomial.C (-x i) * h.1 - (MvPolynomial.X i - MvPolynomial.C (x i)) * h.1 =
      -(MvPolynomial.X i * h.1) := by rw [map_neg]; ring
  rw [this, pow_succ']
  exact neg_mem (Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (homog_mem_pow h.2))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem piece_wreg (a : ℕ) (x : Fin D → R) (hx : IsWeaklyRegular R (List.ofFn x)) :
    IsWeaklyRegular (LinearMap.ker (gmap (R := R) (D := D) a)) (tl x) := by
  have hneg : IsWeaklyRegular R (List.ofFn fun i => -x i) := by
    have := (wreg_neg (M := R) (List.ofFn x)).2 hx
    simpa [List.map_ofFn, Function.comp_def] using this
  have := free_homog (R := R) (D := D) a
  have ht := hneg.isWeaklyRegular_lTensor (M₂ := homogeneousSubmodule (Fin D) R a)
  have hH := ((TensorProduct.rid R (homogeneousSubmodule (Fin D) R a)).isWeaklyRegular_congr _).1 ht
  exact ((AddEquiv.ofBijective (emb a) ⟨emb_injective a, emb_surjective a⟩).isWeaklyRegular_congr
    (forall₂_ofFn _ _ fun i h => emb_smul a x i h)).1 hH

end Piece

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Establish an intermediate fact. Treat this case separately.

A detailed English derivation is pending.
-/
theorem stRegN : StRegN.{u} := by
  intro R _ D a x hx
  induction a with
  | zero =>
    have : Subsingleton (MvPolynomial (Fin D) R ⧸
        (Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    exact wreg_of_subsingleton _
  | succ a ih =>
    exact wreg_ses (tl x) (LinearMap.ker (gmap a)).subtype (gmap a) Subtype.val_injective
      (LinearMap.exact_subtype_ker_map _) (gmap_surjective a) (piece_wreg a x hx) ih

end PIW.ENSpec
