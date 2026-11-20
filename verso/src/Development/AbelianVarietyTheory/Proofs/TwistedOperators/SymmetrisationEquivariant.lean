import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymbolCongr

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section

namespace GlobalTheory.InducedPBW.Equivariant

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {p q : ℕ}

abbrev unitP (ab : PIx p q) : Mat p q := Eab ab.1.1 ab.1.2

/- English proof (translation)
Unfold `pLin`. Rewrite using `[Finset.sum_eq_single ab]`. Simplify using `[unitP, Eab]`. Introduce `c _ hc`. Establish `hne : ¬ (ab.1.1 = c.1.1 ∧ ab.1.2 = c.1.2)` using `fun hh => hc (Subtype.ext (Prod.ext hh.1.symm hh.2.symm))`.

Simplify using `[unitP, Eab, Matrix.single_apply, hne]`. Introduce `hab`. Conclude with `absurd (Finset.mem_univ ab) hab`.
-/
theorem pLin_unitP (ab : PIx p q) : pLin (unitP ab) = MvPolynomial.X ab := by
  unfold pLin
  rw [Finset.sum_eq_single ab]
  · simp [unitP, Eab]
  · intro c _ hc
    have hne : ¬ (ab.1.1 = c.1.1 ∧ ab.1.2 = c.1.2) := fun hh =>
      hc (Subtype.ext (Prod.ext hh.1.symm hh.2.symm))
    simp [unitP, Eab, Matrix.single_apply, hne]
  · intro hab
    exact absurd (Finset.mem_univ ab) hab

/- English proof (translation)
Establish `hl` using `(UniversalEnvelopingAlgebra.ι ℂ : Mat p q →ₗ⁅ℂ⁆ Ug p q).map_lie Y Z`. Rewrite `hl` using `[Ring.lie_def, Ring.lie_def]`. Simplify `hl` using `[ugι]`.
-/
theorem ug_comm (Y Z : Mat p q) :
    ugι p q (Y * Z - Z * Y) = ugι p q Y * ugι p q Z - ugι p q Z * ugι p q Y := by
  have hl := (UniversalEnvelopingAlgebra.ι ℂ : Mat p q →ₗ⁅ℂ⁆ Ug p q).map_lie Y Z
  rw [Ring.lie_def, Ring.lie_def] at hl
  simpa [ugι] using hl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `MvPolynomial.mkDerivation ℂ (fun c : PIx p q => pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y)) (MvPolynomial.X ab) = _`. Rewrite using `[MvPolynomial.mkDerivation_X]`.
-/
theorem kOnS_X (Y : Mat p q) (ab : PIx p q) :
    kOnS Y (MvPolynomial.X ab) = pLin (Y * unitP ab - unitP ab * Y) := by
  change MvPolynomial.mkDerivation ℂ (fun c : PIx p q => pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y))
    (MvPolynomial.X ab) = _
  rw [MvPolynomial.mkDerivation_X]

/- English proof (translation)
Conclude with `(MvPolynomial.mkDerivation ℂ fun c : PIx p q => pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y)).map_one_eq_zero`.
-/
theorem kOnS_one (Y : Mat p q) : kOnS Y 1 = 0 := by
  exact (MvPolynomial.mkDerivation ℂ fun c : PIx p q =>
    pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y)).map_one_eq_zero

/- English proof (translation)
Conclude with `(MvPolynomial.mkDerivation ℂ fun c : PIx p q => pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y)).leibniz P Q`.
-/
theorem kOnS_mul (Y : Mat p q) (P Q : MvPolynomial (PIx p q) ℂ) :
    kOnS Y (P * Q) = P * kOnS Y Q + Q * kOnS Y P := by
  exact (MvPolynomial.mkDerivation ℂ fun c : PIx p q =>
    pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y)).leibniz P Q

variable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)

def cls (v : V) : Ug p q →ₗ[ℂ] Ind act :=
  (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cls_apply (v : V) (u : Ug p q) :
    cls act v u = (indRel act).mkQ (TensorProduct.tmul ℂ u v) := rfl

/- English proof (translation)
Rewrite using `[cls_apply, cls_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Conclude with `Submodule.subset_span ⟨u, Y, v, hY, rfl⟩`.
-/
theorem cls_mul (v : V) (u : Ug p q) {Y : Mat p q} (hY : IsKC Y) :
    cls act v (u * ugι p q Y) = cls act (act Y v) u := by
  rw [cls_apply, cls_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨u, Y, v, hY, rfl⟩

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `nil => rfl`. Consider the case `cons c a ih => simp only [List.map_cons, pLin_unitP, ih]`.
-/
theorem map_pLin (a : List (PIx p q)) :
    (a.map unitP).map pLin = a.map MvPolynomial.X := by
  induction a with
  | nil => rfl
  | cons c a ih => simp only [List.map_cons, pLin_unitP, ih]

/- English proof (translation)
Use `noncomm_ring`.
-/
private theorem mul_commutator_mul_expand {R : Type*} [Ring R] (B y x P : R) :
    B * (y * (x * P) - x * P * y) = B * ((y * x - x * y) * P) + B * x * (y * P - P * y) := by
  noncomm_ring

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mul_leibniz_comm {R : Type*} [CommRing R] (B x Q dx dQ : R) :
    B * (x * dQ + Q * dx) = B * (dx * Q) + B * x * dQ := by
  ring

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `nil`. Introduce `b`. Simplify using `[kOnS_one]`. Consider the case `cons e a ih`.

Introduce `b`. Establish `h1` using `h (b ++ (Y * unitP e - unitP e * Y) :: a.map unitP) v`. Establish `h2` using `ih (b ++ [unitP e])`. Rewrite `h1` using `[← cls_apply, ← cls_apply]`. Simplify using `only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, List.length_append, List.length_cons, List.length_nil, zero_add, List.length_map, ug_comm, map_pLin, pLin_unitP] at h1 h2 ⊢`.

Rewrite `h1` using `[← kOnS_X]`. Rewrite `h2` using `[show b.length + 1 + a.length = b.length + (a.length + 1) by omega]`. Rewrite using `[kOnS_mul, mul_commutator_mul_expand, mul_leibniz_comm, map_add, map_add, map_add]`. Establish `hs` using `Submodule.add_mem _ h1 h2`. Use `hs using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws.
-/
theorem comm_mem (h : SymbolCongr act) (Y : Mat p q) (v : V) (a : List (PIx p q)) :
    ∀ b : List (Mat p q),
      cls act v ((b.map (ugι p q)).prod *
        (ugι p q Y * ((a.map unitP).map (ugι p q)).prod -
          ((a.map unitP).map (ugι p q)).prod * ugι p q Y)) -
      cls act v (symU p q ((b.map pLin).prod * kOnS Y (a.map MvPolynomial.X).prod)) ∈
        indFlt act (b.length + a.length) := by
  induction a with
  | nil =>
    intro b
    simp [kOnS_one]
  | cons e a ih =>
    intro b
    have h1 := h (b ++ (Y * unitP e - unitP e * Y) :: a.map unitP) v
    have h2 := ih (b ++ [unitP e])
    rw [← cls_apply, ← cls_apply] at h1
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, List.length_append, List.length_cons, List.length_nil, zero_add,
      List.length_map, ug_comm, map_pLin, pLin_unitP] at h1 h2 ⊢
    rw [← kOnS_X] at h1
    rw [show b.length + 1 + a.length = b.length + (a.length + 1) by omega] at h2
    rw [kOnS_mul, mul_commutator_mul_expand, mul_leibniz_comm, map_add, map_add, map_add]
    have hs := Submodule.add_mem _ h1 h2
    convert hs using 1
    abel

/- English proof (translation)
Establish `h1` using `comm_mem act h Y v a []`. Establish `h2` using `h (a.map unitP) (act Y v)`. Rewrite `h2` using `[← cls_apply, ← cls_apply, map_pLin, List.length_map]`. Simplify using `only [List.map_nil, List.prod_nil, one_mul, List.length_nil, zero_add, map_sub] at h1`. Rewrite `h1` using `[cls_mul act v _ hY]`.

Establish `hs` using `Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)`. Use `hs using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem list_mem (h : SymbolCongr act) {Y : Mat p q} (hY : IsKC Y) (v : V) (a : List (PIx p q)) :
    cls act v (symU p q (kOnS Y (a.map MvPolynomial.X).prod)) +
      cls act (act Y v) (symU p q (a.map MvPolynomial.X).prod) -
      cls act v (ugι p q Y * ((a.map unitP).map (ugι p q)).prod) ∈ indFlt act a.length := by
  have h1 := comm_mem act h Y v a []
  have h2 := h (a.map unitP) (act Y v)
  rw [← cls_apply, ← cls_apply, map_pLin, List.length_map] at h2
  simp only [List.map_nil, List.prod_nil, one_mul, List.length_nil, zero_add, map_sub] at h1
  rw [cls_mul act v _ hY] at h1
  have hs := Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)
  convert hs using 1
  abel

/- English proof (translation)
Rewrite using `[← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList, Finset.prod_multiset_map_count, Finsupp.toFinset_toMultiset, MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod]`. Simplify using `[Finsupp.count_toMultiset]`.
-/
theorem toList_prod (α : PIx p q →₀ ℕ) :
    ((Finsupp.toMultiset α).toList.map (MvPolynomial.X (R := ℂ))).prod =
      MvPolynomial.monomial α 1 := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList, Finset.prod_multiset_map_count,
    Finsupp.toFinset_toMultiset, MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod]
  simp [Finsupp.count_toMultiset]

/- English proof (translation)
Rewrite using `[show MvPolynomial.monomial α (1 : ℂ) = MvPolynomial.basisMonomials (PIx p q) ℂ α by`. Rewrite using `[MvPolynomial.coe_basisMonomials]]`. Unfold `symU`. Rewrite using `[Module.Basis.constr_basis]`. Unfold `symProd`.

Rewrite using `[mul_smul_comm, Finset.mul_sum]`. Simplify using `only [List.map_ofFn]`. Both sides reduce to the same expression.
-/
private theorem mul_symU_monomial_eq_avg_perm (α : PIx p q →₀ ℕ) (y : Ug p q) :
    y * symU p q (MvPolynomial.monomial α 1) =
      (((Finsupp.toMultiset α).toList.length.factorial : ℂ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin (Finsupp.toMultiset α).toList.length),
          y * (((List.ofFn fun i => (Finsupp.toMultiset α).toList.get (σ i)).map unitP).map
            (ugι p q)).prod := by
  rw [show MvPolynomial.monomial α (1 : ℂ) = MvPolynomial.basisMonomials (PIx p q) ℂ α by
    rw [MvPolynomial.coe_basisMonomials]]
  unfold symU
  rw [Module.Basis.constr_basis]
  unfold symProd
  rw [mul_smul_comm, Finset.mul_sum]
  simp only [List.map_ofFn]
  rfl

/- English proof (translation)
Rewrite using `[List.map_ofFn, List.prod_ofFn]`. Use `conv_rhs => rw [← List.ofFn_get l, List.map_ofFn, List.prod_ofFn]`. Conclude with `Equiv.prod_comp σ (fun i => MvPolynomial.X (l.get i))`.
-/
private theorem prod_ofFn_perm_map_X_eq_prod (l : List (PIx p q)) (σ : Equiv.Perm (Fin l.length)) :
    ((List.ofFn fun i => l.get (σ i)).map (MvPolynomial.X (R := ℂ))).prod =
      (l.map MvPolynomial.X).prod := by
  rw [List.map_ofFn, List.prod_ofFn]
  conv_rhs => rw [← List.ofFn_get l, List.map_ofFn, List.prod_ofFn]
  exact Equiv.prod_comp σ (fun i => MvPolynomial.X (l.get i))

/- English proof (translation)
Establish `hx : x = ((n.factorial : ℂ)⁻¹) • ∑ _σ : Equiv.Perm (Fin n), x`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]`. Rewrite using `[hx, ← smul_sub, ← Finset.sum_sub_distrib]`. Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => hf σ)`.
-/
private theorem sub_inv_factorial_smul_sum_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M)
    (n : ℕ) (x : M) (f : Equiv.Perm (Fin n) → M) (hf : ∀ σ, x - f σ ∈ S) :
    x - ((n.factorial : ℂ)⁻¹) • ∑ σ, f σ ∈ S := by
  have hx : x = ((n.factorial : ℂ)⁻¹) • ∑ _σ : Equiv.Perm (Fin n), x := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]
  rw [hx, ← smul_sub, ← Finset.sum_sub_distrib]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => hf σ)

/- English proof (translation)
Rewrite using `[mul_symU_monomial_eq_avg_perm, map_smul, map_sum]`. Apply `sub_inv_factorial_smul_sum_mem` to reduce the goal to its premises. Introduce `σ`. Establish `hσ` using `list_mem act h hY v (List.ofFn fun i => (Finsupp.toMultiset α).toList.get (σ i))`. Rewrite `hσ` using `[prod_ofFn_perm_map_X_eq_prod, toList_prod, List.length_ofFn]`.

Conclude with `hσ`.
-/
theorem monomial_mem (h : SymbolCongr act) {Y : Mat p q} (hY : IsKC Y) (v : V)
    (α : PIx p q →₀ ℕ) :
    cls act v (symU p q (kOnS Y (MvPolynomial.monomial α 1))) +
      cls act (act Y v) (symU p q (MvPolynomial.monomial α 1)) -
      cls act v (ugι p q Y * symU p q (MvPolynomial.monomial α 1)) ∈
        indFlt act (Finsupp.toMultiset α).toList.length := by
  rw [mul_symU_monomial_eq_avg_perm, map_smul, map_sum]
  apply sub_inv_factorial_smul_sum_mem
  intro σ
  have hσ := list_mem act h hY v (List.ofFn fun i => (Finsupp.toMultiset α).toList.get (σ i))
  rw [prod_ofFn_perm_map_X_eq_prod, toList_prod, List.length_ofFn] at hσ
  exact hσ

/- English proof (translation)
Establish `hlin : ∀ Q : MvPolynomial (PIx p q) ℂ, cls act v (symU p q (kOnS Y Q)) + cls act (act Y v) (symU p q Q) - cls act v (ugι p q Y * symU p q Q) = (cls act v ∘ₗ symU p q ∘ₗ kOnS Y + cls act (act Y v) ∘ₗ symU p q - cls act v ∘ₗ LinearMap.mulLeft ℂ (ugι p q Y) ∘ₗ symU p q) Q` using `fun Q => by`. Simplify using the standard rewrite rules. Rewrite using `[hlin, MvPolynomial.as_sum P, map_sum]`. Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[show MvPolynomial.monomial d (P.coeff d) = P.coeff d • MvPolynomial.monomial d 1 by`.

Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[← hlin]`. Establish `hk : (Finsupp.toMultiset d).toList.length = k`. Establish `hw` using `hP (MvPolynomial.mem_support_iff.mp hd)`.

Simplify `hw` using `[Multiset.length_toList, Finsupp.card_toMultiset, Finsupp.weight_apply, Finsupp.sum]`. Establish `hm` using `monomial_mem act h hY v d`. Rewrite `hm` using `[hk]`. Conclude with `hm`.
-/
theorem homog_mem (h : SymbolCongr act) {Y : Mat p q} (hY : IsKC Y) (v : V) (k : ℕ)
    (P : MvPolynomial (PIx p q) ℂ) (hP : P.IsHomogeneous k) :
    cls act v (symU p q (kOnS Y P)) + cls act (act Y v) (symU p q P) -
      cls act v (ugι p q Y * symU p q P) ∈ indFlt act k := by
  have hlin : ∀ Q : MvPolynomial (PIx p q) ℂ,
      cls act v (symU p q (kOnS Y Q)) + cls act (act Y v) (symU p q Q) -
        cls act v (ugι p q Y * symU p q Q) =
      (cls act v ∘ₗ symU p q ∘ₗ kOnS Y + cls act (act Y v) ∘ₗ symU p q -
        cls act v ∘ₗ LinearMap.mulLeft ℂ (ugι p q Y) ∘ₗ symU p q) Q := fun Q => by
    simp
  rw [hlin, MvPolynomial.as_sum P, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [show MvPolynomial.monomial d (P.coeff d) = P.coeff d • MvPolynomial.monomial d 1 by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [← hlin]
  have hk : (Finsupp.toMultiset d).toList.length = k := by
    have hw := hP (MvPolynomial.mem_support_iff.mp hd)
    simpa [Multiset.length_toList, Finsupp.card_toMultiset, Finsupp.weight_apply, Finsupp.sum] using hw
  have hm := monomial_mem act h hY v d
  rw [hk] at hm
  exact hm

end GlobalTheory.InducedPBW.Equivariant

namespace GlobalTheory.InducedPBW

open Equivariant in

/- English proof (translation)
Introduce `p q V _ _ act h k Y hY z hz`. Unfold `symTens at hz`. Rewrite `hz` using `[LinearMap.mem_range]`. Take `⟨w, rfl⟩` from `hz`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul P v`. Simplify using `only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, Submodule.coe_subtype, map_add, LinearMap.mulLeft_apply, ← cls_apply]`. Conclude with `homog_mem act h hY v k P ((MvPolynomial.mem_homogeneousSubmodule k _).mp P.2)`. Consider the case `add x y hx hy`.

Establish `hs` using `Submodule.add_mem _ hx hy`. Use `hs using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem symmetrisation_equivariant : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), SymbolCongr act → ∀ (k : ℕ) (Y : Mat p q), IsKC Y → ∀ z ∈ symTens p q V k, (indRel act).mkQ (LinearMap.rTensor V (symU p q) (LinearMap.rTensor V (kOnS Y) z + LinearMap.lTensor _ (act Y) z)) - (indRel act).mkQ (LinearMap.rTensor V (LinearMap.mulLeft ℂ (ugι p q Y)) (LinearMap.rTensor V (symU p q) z)) ∈ indFlt act k := by
  intro p q V _ _ act h k Y hY z hz
  unfold symTens at hz
  rw [LinearMap.mem_range] at hz
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, Submodule.coe_subtype, map_add,
      LinearMap.mulLeft_apply, ← cls_apply]
    exact homog_mem act h hY v k P ((MvPolynomial.mem_homogeneousSubmodule k _).mp P.2)
  | add x y hx hy =>
    have hs := Submodule.add_mem _ hx hy
    convert hs using 1
    simp only [map_add]
    abel

end GlobalTheory.InducedPBW
