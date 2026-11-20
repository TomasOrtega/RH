import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SemilocalBasis

open scoped Pointwise

/- English proof (translation)
Use `Fintype.ofFinite J` as an intermediate fact. Use `by_contra! h`. Establish `hcov : ⋃ i ∈ (Finset.univ : Finset J), (0 : V) +ᵥ ((p i).toAddSubgroup : Set V) = Set.univ`. Use `Set.eq_univ_iff_forall.mpr fun a => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `h a`.

Simplify using `only [zero_vadd, Set.mem_iUnion]`. Conclude with `⟨i, Finset.mem_univ i, hi⟩`. Take `⟨k, -, hk⟩` from `AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcov`. Establish `hfin : Finite (V ⧸ p k)` using `AddSubgroup.finite_quotient_of_finiteIndex (H := (p k).toAddSubgroup)`. Take `⟨x, hx⟩ : ∃ x, x ∉ p k` from `by by_contra! h'`.

Conclude with `hp k (Submodule.eq_top_iff'.mpr h')`. Use `choose s hs using IsLocalRing.residue_surjective (R := A)`. Establish `hinj : Function.Injective (fun c : IsLocalRing.ResidueField A => (p k).mkQ (s c • x))`. Introduce `c d hcd`. Assume the negation of the conclusion as `hne`.

Establish `h1 : (s c - s d) • x ∈ p k`. Rewrite using `[sub_smul]`. Conclude with `(Submodule.Quotient.eq _).mp hcd`. Establish `h2 : IsUnit (s c - s d)`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hs, hs]`.

Conclude with `sub_ne_zero.mpr hne`. Conclude with `hx (((p k).smul_mem_iff_of_isUnit h2).mp h1)`. Use `Finite.of_injective _ hinj` as an intermediate fact. Conclude with `not_finite (IsLocalRing.ResidueField A)`.
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
Introduce `y`. Use `choose s hs using Ideal.Quotient.mk_surjective (I := I)`. Use `⟨e.equivFun.symm fun j => s (y j), ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Rewrite using `[red_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hs]`.
-/
theorem red_surjective {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : Function.Surjective (red e I) := by
  intro y
  choose s hs using Ideal.Quotient.mk_surjective (I := I)
  refine ⟨e.equivFun.symm fun j => s (y j), ?_⟩
  ext j
  rw [red_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hs]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨Fin.elim0, fun i => i.elim0, fun _ => linearIndependent_empty_type⟩`. Consider the case `succ k ih`. Take `⟨v, hvN, hv⟩` from `ih (by omega)`. Set `W : ∀ m : MaximalSpectrum B, Submodule (B ⧸ m.asIdeal) (Fin n → B ⧸ m.asIdeal)` to `fun m => Submodule.span _ (Set.range fun i => red e m.asIdeal (v i))`.

Set `q : MaximalSpectrum B → Submodule B M` to `fun m => ((W m).restrictScalars B).comap (red e m.asIdeal)`. Set `p : MaximalSpectrum B → Submodule A N` to `fun m => ((q m).restrictScalars A).comap N.subtype`. Take `⟨x, hx⟩` from `exists_forall_notMem p (fun m h => by`. Use `m.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field m.asIdeal`.

Establish `h1 : q m = ⊤`. Rewrite using `[eq_top_iff, ← hN, Submodule.span_le]`. Introduce `y hy`. Establish `: (⟨y, hy⟩ : N) ∈ p m` using `h ▸ Submodule.mem_top`. Conclude with `this`.

Establish `h2 : W m = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨z, rfl⟩` from `red_surjective e m.asIdeal y`. Establish `: z ∈ q m` using `h1 ▸ Submodule.mem_top`.

Conclude with `this`. Establish `h3 : Module.finrank (B ⧸ m.asIdeal) (W m) = k`. Use `finrank_span_eq_card (hv m)` as an intermediate fact. Simplify using `using this`. Rewrite `h3` using `[h2]`.

Simplify using `at h3`. Use the proof step `omega) (fun m a ha y => by`. Establish `h0 : red e m.asIdeal (a • (y : M)) = 0`. Use extensionality with `j`. Rewrite using `[red_apply, ← algebraMap_smul B, map_smul, Finsupp.smul_apply, smul_eq_mul, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mul_mem_right _ _ (hm m (Ideal.mem_map_of_mem _ ha))`. Express the relevant statement in the definitionally equal form `red e m.asIdeal (a • (y : M)) ∈ W m`. Rewrite using `[h0]`. Conclude with `zero_mem _)`. Use `⟨Fin.cons (x : M) v, fun i => ?_, fun m => ?_⟩` and prove the remaining obligations.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Conclude with `x.2`. Conclude with `hvN j`. Use `m.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field m.asIdeal`.

Establish `h1 : (fun i => red e m.asIdeal (Fin.cons (α` using `fun _ => M) (x : M) v i)) = Fin.cons (red e m.asIdeal x) (fun i => red e m.asIdeal (v i)) := by`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> rfl`. Rewrite using `[h1, linearIndependent_finCons]`. Conclude with `⟨hv m, hx m⟩`.
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
Introduce `A B M _ _ _ _ _ _ _ _ _ _ n e N hm hN`. Take `⟨v, hvN, hv⟩` from `SemilocalBasis.exists_linearIndependent e N hm hN n le_rfl`. Establish `hu : IsUnit (e.det v)`. Assume the negation of the conclusion as `hne`. Take `⟨I, hI, hmem⟩` from `exists_max_ideal_of_mem_nonunits hne`.

Use `letI := Ideal.Quotient.field I`. Establish `h1` using `hv ⟨I, hI⟩`. Establish `h2 : IsUnit ((e.toMatrix v).map (Ideal.Quotient.mk I))` using `Matrix.linearIndependent_cols_iff_isUnit.mp h1`. Rewrite `h2` using `[Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Module.Basis.det_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem]`. Conclude with `not_isUnit_zero h2`.

Take `⟨hli, hsp⟩` from `e.is_basis_iff_det.mpr hu`. Conclude with `⟨Module.Basis.mk hli hsp.ge, fun i => by simpa using hvN i⟩`.
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
