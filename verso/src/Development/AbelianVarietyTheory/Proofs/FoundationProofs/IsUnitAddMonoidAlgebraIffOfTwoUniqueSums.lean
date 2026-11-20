import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TupleDifferentialTupleDifferential
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorCoeffOfMemTorusWeightSpace

open TensorProduct Coalgebra AddMonoidAlgebra

namespace GlobalTheory

section Units

variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]

noncomputable def monomialUnitHom (A : Type*) [CommRing A] (X : Type*) [AddCommGroup X] :
    Aˣ × Multiplicative X →* (A[X])ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun p => single p.2.toAdd (p.1 : A)
      map_one' := rfl
      map_mul' := fun p q => by simp [single_mul_single] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_monomialUnitHom (p : Aˣ × Multiplicative X) :
    (monomialUnitHom A X p : A[X]) = single p.2.toAdd (p.1 : A) := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem monomialUnitHom_injective [Nontrivial A] : Function.Injective (monomialUnitHom A X) := by
  classical
  refine (injective_iff_map_eq_one _).2 fun p hp => ?_
  have h : (Finsupp.single p.2.toAdd (p.1 : A)) = Finsupp.single 0 1 :=
    congrArg (fun u : (A[X])ˣ => (u : A[X]).coeff) hp
  rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact Prod.ext (Units.ext h2) h1
  · exact absurd h2 one_ne_zero

variable [IsDomain A]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem isUnit_addMonoidAlgebra_iff_of_twoUniqueSums [TwoUniqueSums X] (f : A[X]) :
    IsUnit f ↔ ∃ (x : X) (a : Aˣ), f = single x (a : A) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, c, ⟨a, rfl⟩, e⟩ := ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.isUnit_eq_single h
    exact ⟨x, a, e⟩
  · rintro ⟨x, a, rfl⟩
    exact (monomialUnitHom A X (a, .ofAdd x)).isUnit

variable [Module.Free ℤ X]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isUnit_addMonoidAlgebra_iff (f : A[X]) :
    IsUnit f ↔ ∃ (x : X) (a : Aˣ), f = single x (a : A) :=
  isUnit_addMonoidAlgebra_iff_of_twoUniqueSums f

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem monomialUnitHom_bijective : Function.Bijective (monomialUnitHom A X) := by
  refine ⟨monomialUnitHom_injective, fun u => ?_⟩
  obtain ⟨x, a, e⟩ := (isUnit_addMonoidAlgebra_iff (u : A[X])).1 u.isUnit
  exact ⟨(a, .ofAdd x), Units.ext e.symm⟩

variable (A X) in

noncomputable def unitsAddMonoidAlgebraEquiv : Aˣ × Multiplicative X ≃* (A[X])ˣ :=
  MulEquiv.ofBijective (monomialUnitHom A X) monomialUnitHom_bijective

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_unitsAddMonoidAlgebraEquiv (p : Aˣ × Multiplicative X) :
    (unitsAddMonoidAlgebraEquiv A X p : A[X]) = single p.2.toAdd (p.1 : A) := rfl

end Units

section Coordinates

variable {X : Type*} [Zero X] {N : Type*} [AddCommGroup N]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Treat this case separately. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem coboundary_apply_zero_left (g : X →₀ N) (x : X) :
    (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) (0, x) = g x := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← hf, ← hg]; abel
  | single y m =>
    simp only [Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply, Prod.mk.injEq]
    by_cases h : y = 0
    · subst h; simp
    · simp [h]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Treat this case separately. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem finsupp_two_cocycle_eq_coboundary (f : X × X →₀ N)
    (hf : f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
      f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) = 0)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) :
    g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) = f := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  have key : ∀ (f : X × X →₀ N) (q : X × X),
      (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) +
      ((s f).mapDomain (fun y => ((0 : X), y)) - (s f).mapDomain (fun y => (y, y)) +
        (s f).mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) q = f q := by
    intro f q
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add, Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
      rw [← hf, ← hg]; abel
    | single p m =>
      obtain ⟨y, z⟩ := p
      by_cases h : y = 0
      · subst h
        have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
          ext x; simp [hs, Finsupp.single_apply]
        simp [this, Finsupp.single_apply]
      · have : s (Finsupp.single (y, z) m) = 0 := by
          ext x; simp [hs, h]
        simp [this, Finsupp.single_apply, h]
  have e : g = s f := Finsupp.ext hg
  ext q
  rw [← key f q, hf, e]
  simp

end Coordinates

section Ring

variable {X : Type*} [Zero X] {A : Type*} [Ring A]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem addMonoidAlgebra_coboundary_eq_iff (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0)
    (g : A[X]) :
    mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f ↔ ∀ x, g.coeff x = f.coeff (0, x) := by
  refine ⟨fun h x => ?_, fun h => coeff_injective
    (finsupp_two_cocycle_eq_coboundary f.coeff (congrArg coeff hf) g.coeff h)⟩
  rw [← h]
  exact (coboundary_apply_zero_left g.coeff x).symm

/- English proof (translation)
Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem addMonoidAlgebra_existsUnique_coboundary (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0) :
    ∃! g : A[X], mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f := by
  simp only [addMonoidAlgebra_coboundary_eq_iff f hf]
  exact ⟨ofCoeff (f.coeff.comapDomain (fun x => ((0 : X), x)) (Prod.mk_right_injective 0).injOn),
    fun _ => rfl, fun g hg => coeff_injective (Finsupp.ext hg)⟩

end Ring

section Tensor

variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def hochschildD₀ (ρ : M →ₗ[R] M ⊗[R] H) : M →ₗ[R] M ⊗[R] H :=
  ρ - (TensorProduct.mk R M H).flip 1

noncomputable def hochschildD₁ (ρ : M →ₗ[R] M ⊗[R] H) : M ⊗[R] H →ₗ[R] M ⊗[R] (H ⊗[R] H) :=
  (TensorProduct.assoc R M H H).toLinearMap ∘ₗ ρ.rTensor H - (comul (R := R)).lTensor M +
    ((TensorProduct.mk R H H).flip 1).lTensor M

noncomputable def hochschildD₂ (ρ : M →ₗ[R] M ⊗[R] H) :
    M ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  (TensorProduct.assoc R M H (H ⊗[R] H)).toLinearMap ∘ₗ ρ.rTensor (H ⊗[R] H) -
    ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ (comul (R := R)).rTensor H).lTensor M +
    ((comul (R := R)).lTensor H).lTensor M -
    (((TensorProduct.mk R H H).flip 1).lTensor H).lTensor M

variable (R H M) in

noncomputable def trivialCoaction : M →ₗ[R] M ⊗[R] H := (TensorProduct.mk R M H).flip 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem trivialCoaction_apply (m : M) : trivialCoaction R H M m = m ⊗ₜ 1 := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
@[simp] theorem hochschildD₀_trivialCoaction : hochschildD₀ (trivialCoaction R H M) = 0 :=
  sub_self _

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem hochschildD₁_trivialCoaction : hochschildD₁ (trivialCoaction R H M) =
    (TensorProduct.mk R H H 1).lTensor M - (comul (R := R)).lTensor M +
      ((TensorProduct.mk R H H).flip 1).lTensor M := by
  ext m h; simp [hochschildD₁]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem hochschildD₂_trivialCoaction : hochschildD₂ (trivialCoaction R H M) =
    (TensorProduct.mk R H (H ⊗[R] H) 1).lTensor M -
      ((TensorProduct.assoc R H H H).toLinearMap ∘ₗ (comul (R := R)).rTensor H).lTensor M +
      ((comul (R := R)).lTensor H).lTensor M -
      (((TensorProduct.mk R H H).flip 1).lTensor H).lTensor M := by
  ext m h k; simp [hochschildD₂]

variable {X : Type*} [AddMonoid X]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem hochschild_homotopy_one (ρ : M →ₗ[R] M ⊗[R] R[X]) (f : M ⊗[R] R[X]) :
    (tensorCoeff R R[X] (0 : X)).lTensor M (hochschildD₁ ρ f) -
      hochschildD₀ ρ (tensorCoeff R M 0 f) = f := by
  classical
  induction f with
  | zero => simp
  | add a b ha hb => simp only [map_add]; rw [add_sub_add_comm, ha, hb]
  | tmul m p =>
    have h : ∀ (t : M ⊗[R] R[X]) (p : R[X]), (tensorCoeff R R[X] (0 : X)).lTensor M
        (TensorProduct.assoc R M R[X] R[X] (t ⊗ₜ p)) = p.coeff 0 • t := by
      intro t p
      induction t with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb, smul_add]
      | tmul m q => simp
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
    | single y r =>
      simp only [hochschildD₁, hochschildD₀, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul, map_add, map_sub, h]
      by_cases hy : y = 0
      · subst hy; simp [one_def, ← tmul_smul]
      · simp [one_def, hy]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem hochschild_homotopy_two (ρ : M →ₗ[R] M ⊗[R] R[X]) (f : M ⊗[R] (R[X] ⊗[R] R[X])) :
    hochschildD₁ ρ ((tensorCoeff R R[X] (0 : X)).lTensor M f) -
      ((tensorCoeff R R[X] (0 : X)).lTensor R[X]).lTensor M (hochschildD₂ ρ f) = f := by
  classical
  induction f with
  | zero => simp
  | add a b ha hb => simp only [map_add]; rw [add_sub_add_comm, ha, hb]
  | tmul m u =>
    have h : ∀ (t : M ⊗[R] R[X]) (u : R[X] ⊗[R] R[X]),
        ((tensorCoeff R R[X] (0 : X)).lTensor R[X]).lTensor M
        (TensorProduct.assoc R M R[X] (R[X] ⊗[R] R[X]) (t ⊗ₜ u)) =
        TensorProduct.assoc R M R[X] R[X] (t ⊗ₜ tensorCoeff R R[X] (0 : X) u) := by
      intro t u
      induction t with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
      | tmul m q => simp
    induction u with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
    | tmul p q =>
      induction p using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
      | single x c =>
        induction q using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
        | single y r =>
          simp only [hochschildD₁, hochschildD₂, LinearMap.add_apply, LinearMap.sub_apply,
            LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
            LinearMap.lTensor_tmul, map_add, map_sub, h]
          by_cases hy : y = 0
          · subst hy
            have e : (single x (r * c) : R[X]) ⊗ₜ[R] (single 0 1 : R[X]) =
                single x c ⊗ₜ[R] single 0 r := by
              rw [← smul_eq_mul, ← smul_single, smul_tmul, smul_single, smul_eq_mul, _root_.mul_one]
            simp [one_def, e]
          · simp [one_def, hy]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Introduce a local definition for the expression.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem IsCoaction.exact_hochschildD₀_hochschildD₁ {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Function.Exact (hochschildD₀ ρ) (hochschildD₁ ρ) := by
  classical
  intro f
  refine ⟨fun hf => ⟨-tensorCoeff R M 0 f, ?_⟩, ?_⟩
  · simpa [hf] using hochschild_homotopy_one ρ f
  · rintro ⟨m, rfl⟩
    let := h.decomposition
    induction m using DirectSum.Decomposition.inductionOn (torusWeightSpace ρ) with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | homogeneous m =>
      simp [hochschildD₀, hochschildD₁, mem_coactionWeightSpace.1 m.2, one_def]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Introduce a local definition for the expression.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Normalize the expressions using the abelian group laws.
-/
theorem IsCoaction.exact_hochschildD₁_hochschildD₂ {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ) :
    Function.Exact (hochschildD₁ ρ) (hochschildD₂ ρ) := by
  classical
  intro f
  refine ⟨fun hf => ⟨(tensorCoeff R R[X] (0 : X)).lTensor M f, ?_⟩, ?_⟩
  · simpa [hf] using hochschild_homotopy_two ρ f
  · rintro ⟨g, rfl⟩
    let := h.decomposition
    induction g with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | tmul m p =>
      induction m using DirectSum.Decomposition.inductionOn (torusWeightSpace ρ) with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb, add_zero]
      | homogeneous m =>
        induction p using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => simp only [tmul_add, map_add, ha, hb, add_zero]
        | single y r =>
          rw [← _root_.mul_one r, ← smul_eq_mul, ← smul_single, tmul_smul, map_smul, map_smul]
          refine smul_eq_zero_of_right _ ?_
          simp [hochschildD₂, hochschildD₁, mem_coactionWeightSpace.1 m.2, one_def]
          abel

variable (R M X) in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem hochschildD₁_trivialCoaction_injective :
    Function.Injective (hochschildD₁ (trivialCoaction R R[X] M)) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  simpa [hf] using (hochschild_homotopy_one (trivialCoaction R R[X] M) f).symm

end Tensor

universe u v w

end GlobalTheory
