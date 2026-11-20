import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SemilocalBasis

open scoped Pointwise

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_forall_notMem {A V J : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [AddCommGroup V] [Module A V] [Finite J]
    (p : J → Submodule A V) (hp : ∀ i, p i ≠ ⊤)
    (hm : ∀ i, ∀ a ∈ IsLocalRing.maximalIdeal A, ∀ x, a • x ∈ p i) : ∃ x : V, ∀ i, x ∉ p i := by
  classical
  have := Fintype.ofFinite J
  by_contra! h
  have hcov : ⋃ i ∈ (Finset.univ : Finset J),
      (0 : V) +ᵥ ((p i).toAddSubgroup : Set V) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun a => ?_
    obtain ⟨i, hi⟩ := h a
    simp only [zero_vadd, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, hi⟩
  obtain ⟨k, -, hk⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcov
  have hfin : Finite (V ⧸ p k) := AddSubgroup.finite_quotient_of_finiteIndex (H := (p k).toAddSubgroup)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ p k := by
    by_contra! h'
    exact hp k (Submodule.eq_top_iff'.mpr h')
  choose s hs using IsLocalRing.residue_surjective (R := A)
  have hinj : Function.Injective
      (fun c : IsLocalRing.ResidueField A => (p k).mkQ (s c • x)) := by
    intro c d hcd
    by_contra hne
    have h1 : (s c - s d) • x ∈ p k := by
      rw [sub_smul]
      exact (Submodule.Quotient.eq _).mp hcd
    have h2 : IsUnit (s c - s d) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hs, hs]
      exact sub_ne_zero.mpr hne
    exact hx (((p k).smul_mem_iff_of_isUnit h2).mp h1)
  have := Finite.of_injective _ hinj
  exact not_finite (IsLocalRing.ResidueField A)

noncomputable def red {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : M →ₗ[B] (Fin n → B ⧸ I) :=
  LinearMap.pi fun j => (Submodule.mkQ I).comp (e.coord j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem red_apply {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) (x : M) (j : Fin n) :
    red e I x j = Ideal.Quotient.mk I (e.repr x j) := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem red_surjective {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : Function.Surjective (red e I) := by
  intro y
  choose s hs using Ideal.Quotient.mk_surjective (I := I)
  refine ⟨e.equivFun.symm fun j => s (y j), ?_⟩
  ext j
  rw [red_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hs]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Introduce a local definition for the expression. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Equip the data with the indicated structure.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_linearIndependent {A B M : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B]
    [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    {n : ℕ} (e : Module.Basis (Fin n) B M) (N : Submodule A M)
    (hm : ∀ m : MaximalSpectrum B,
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal)
    (hN : Submodule.span B (N : Set M) = ⊤) (k : ℕ) (hk : k ≤ n) :
    ∃ v : Fin k → M, (∀ i, v i ∈ N) ∧ ∀ m : MaximalSpectrum B,
      LinearIndependent (B ⧸ m.asIdeal) (fun i => red e m.asIdeal (v i)) := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun _ => linearIndependent_empty_type⟩
  | succ k ih =>
    obtain ⟨v, hvN, hv⟩ := ih (by omega)
    let W : ∀ m : MaximalSpectrum B, Submodule (B ⧸ m.asIdeal) (Fin n → B ⧸ m.asIdeal) :=
      fun m => Submodule.span _ (Set.range fun i => red e m.asIdeal (v i))
    let q : MaximalSpectrum B → Submodule B M :=
      fun m => ((W m).restrictScalars B).comap (red e m.asIdeal)
    let p : MaximalSpectrum B → Submodule A N :=
      fun m => ((q m).restrictScalars A).comap N.subtype
    obtain ⟨x, hx⟩ := exists_forall_notMem p (fun m h => by
      have := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      have h1 : q m = ⊤ := by
        rw [eq_top_iff, ← hN, Submodule.span_le]
        intro y hy
        have : (⟨y, hy⟩ : N) ∈ p m := h ▸ Submodule.mem_top
        exact this
      have h2 : W m = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨z, rfl⟩ := red_surjective e m.asIdeal y
        have : z ∈ q m := h1 ▸ Submodule.mem_top
        exact this
      have h3 : Module.finrank (B ⧸ m.asIdeal) (W m) = k := by
        have := finrank_span_eq_card (hv m)
        simpa using this
      rw [h2] at h3
      simp at h3
      omega) (fun m a ha y => by
      have h0 : red e m.asIdeal (a • (y : M)) = 0 := by
        ext j
        rw [red_apply, ← algebraMap_smul B, map_smul, Finsupp.smul_apply, smul_eq_mul,
          Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (hm m (Ideal.mem_map_of_mem _ ha))
      change red e m.asIdeal (a • (y : M)) ∈ W m
      rw [h0]
      exact zero_mem _)
    refine ⟨Fin.cons (x : M) v, fun i => ?_, fun m => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact x.2
      · exact hvN j
    · have := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      have h1 : (fun i => red e m.asIdeal (Fin.cons (α := fun _ => M) (x : M) v i)) =
          Fin.cons (red e m.asIdeal x) (fun i => red e m.asIdeal (v i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [h1, linearIndependent_finCons]
      exact ⟨hv m, hx m⟩

end SemilocalBasis

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_basis_mem_of_span_eq_top_of_semilocal :
    ∀ (A B M : Type) [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] (n : ℕ) (_ : Module.Basis (Fin n) B M) (N : Submodule A M), (∀ m : MaximalSpectrum B, (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal) → Submodule.span B (N : Set M) = ⊤ → ∃ b : Module.Basis (Fin n) B M, ∀ i, b i ∈ N := by
  intro A B M _ _ _ _ _ _ _ _ _ _ n e N hm hN
  obtain ⟨v, hvN, hv⟩ := SemilocalBasis.exists_linearIndependent e N hm hN n le_rfl
  have hu : IsUnit (e.det v) := by
    by_contra hne
    obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits hne
    letI := Ideal.Quotient.field I
    have h1 := hv ⟨I, hI⟩
    have h2 : IsUnit ((e.toMatrix v).map (Ideal.Quotient.mk I)) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp h1
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← Module.Basis.det_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at h2
    exact not_isUnit_zero h2
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr hu
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simpa using hvN i⟩

end GlobalTheory
