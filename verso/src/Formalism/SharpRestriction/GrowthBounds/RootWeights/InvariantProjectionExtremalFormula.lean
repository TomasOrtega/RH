import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
import Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialPreservesDiagonalStable
import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringWordWeightOrNMinus
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExtremalProjectorLatticeScaledMem

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Establish `hs` using `gl_rep_shifts_weights hE`. Establish `htop` using `sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)`. Establish `hinv` using `trivial_isotypic_invariant_holds hE`. Establish `hkill` using `nontrivial_isotypic_weight_zero_killed hE hs`. Take `⟨_, h5b, h5c⟩` from `h5 K V n E hE 0 (by`.

Introduce `a b hab`. Establish `: (a : ℕ) < (b : ℕ)` using `hab`. Simplify using `only [Pi.zero_apply]`. Use the proof step `omega) ord hord T hT`. Establish `hle : ∀ mu, isoSub E mu ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π)`.

Introduce `mu x hx`. Rewrite using `[LinearMap.mem_eqLocus, Module.End.mul_apply]`. Distinguish the cases in `hmu : mu = 0`. Substitute `hmu` using the available equality. Take `⟨hx0, hxr⟩` from `hinv x hx`.

Rewrite using `[hInv.1 x hx, hπ.1 x hx0, h5c x hx0 hxr]`. Rewrite using `[hInv.2 mu hmu x hx, hkill _ π hπ h5b mu hmu x hx]`. Establish `: (⊤ : Submodule K V) ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π)`. Rewrite using `[← htop]`. Conclude with `iSup_le hle`.

Conclude with `LinearMap.ext fun x => this (Submodule.mem_top (x := x))`.
-/
theorem invariant_projection_extremal_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (π : Module.End K V) (hπ : IsWtProj E 0 π)
    (ord : List (Fin n × Fin n)) (hord : NormalOrder n ord) (T : ℕ) (hT : Module.finrank K V ≤ T) :
    Inv = pp E 0 ord T * π := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  have hinv := trivial_isotypic_invariant_holds hE
  have hkill := nontrivial_isotypic_weight_zero_killed hE hs
  obtain ⟨_, h5b, h5c⟩ := h5 K V n E hE 0 (by
    intro a b hab
    have : (a : ℕ) < (b : ℕ) := hab
    simp only [Pi.zero_apply]
    omega) ord hord T hT
  have hle : ∀ mu, isoSub E mu ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π) := by
    intro mu x hx
    rw [LinearMap.mem_eqLocus, Module.End.mul_apply]
    by_cases hmu : mu = 0
    · subst hmu
      obtain ⟨hx0, hxr⟩ := hinv x hx
      rw [hInv.1 x hx, hπ.1 x hx0, h5c x hx0 hxr]
    · rw [hInv.2 mu hmu x hx, hkill _ π hπ h5b mu hmu x hx]
  have : (⊤ : Submodule K V) ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π) := by
    rw [← htop]
    exact iSup_le hle
  exact LinearMap.ext fun x => this (Submodule.mem_top (x := x))

/- English proof (translation)
Establish `hcz` using `dvr_fraction_field_charZero_prime S hG.prime`. Take `⟨Θ, hΘ1, hΘ2⟩` from `weight_projections_integral_findim E`. Take `⟨ord, hord⟩` from `exists_normalOrder n`. Establish `hπ : IsWtProj E 0 (Θ 0)`. Prove the components needed by the constructor for the conclusion.

Introduce `y hy`. Rewrite using `[hΘ2 0 0 y hy, if_pos rfl]`. Introduce `nu hnu y hy`. Rewrite using `[hΘ2 0 nu y hy, if_neg hnu]`. Rewrite using `[invariant_projection_extremal_formula D h2 h5 E hE Inv hInv (Θ 0) hπ ord hord _ le_rfl, Module.End.mul_apply, ← normal_order_length_eq hord]`.

Conclude with `(extremal_projector_lattice_scaled_mem S hG.prime (gl_rep_shifts_weights hE) hM.1 L hL ord hord.2.1 _ _ (binomial_subring_preserves_lattice hM.1 _ (hΘ1 0) x hx) (weight_projection_mem_weightSpace E hE Θ hΘ2 0 x)).1`.
-/
theorem invariant_projection_denominator (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V) (hM : UZLattice E M)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L : ℕ)
    (hL : ∀ (k : ℕ) (a b : Fin n), a ≠ b → weightSp E 0 ≠ ⊥ → weightSp E ((k : ℤ) • rootW a b) ≠ ⊥ → k ≤ L)
    (x : V) (hx : x ∈ M) : ((p : O) ^ (N0 n * deF p n L)) • Inv x ∈ M := by
  have hcz := dvr_fraction_field_charZero_prime S hG.prime
  obtain ⟨Θ, hΘ1, hΘ2⟩ := weight_projections_integral_findim E
  obtain ⟨ord, hord⟩ := exists_normalOrder n
  have hπ : IsWtProj E 0 (Θ 0) := by
    constructor
    · intro y hy
      rw [hΘ2 0 0 y hy, if_pos rfl]
    · intro nu hnu y hy
      rw [hΘ2 0 nu y hy, if_neg hnu]
  rw [invariant_projection_extremal_formula D h2 h5 E hE Inv hInv (Θ 0) hπ ord hord _ le_rfl, Module.End.mul_apply, ← normal_order_length_eq hord]
  exact (extremal_projector_lattice_scaled_mem S hG.prime (gl_rep_shifts_weights hE) hM.1 L hL ord hord.2.1 _ _
    (binomial_subring_preserves_lattice hM.1 _ (hΘ1 0) x hx) (weight_projection_mem_weightSpace E hE Θ hΘ2 0 x)).1

/- English proof (translation)
Simplify using `[rootW, Pi.single_apply, hab]`.
-/
theorem root_multiple_apply_first {n : ℕ} (a b : Fin n) (hab : a ≠ b) (k : ℕ) : ((k : ℤ) • rootW a b) a = k := by
  simp [rootW, Pi.single_apply, hab]

/- English proof (translation)
Establish `hfin : (wtsOf E (⊤ : Submodule K V)).Finite`. Establish `hA : ∀ a : Fin n, {m : ℤ | (E a a).HasEigenvalue (m : K)}.Finite` using `fun a => (Module.End.finite_hasEigenvalue (E a a)).preimage Int.cast_injective.injOn`. Use `(Set.Finite.pi (t := fun a => {m : ℤ | (E a a).HasEigenvalue (m : K)}) hA).subset ?_` and prove the remaining obligations. Introduce `mu hmu`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]`.

Introduce `a`. Establish `hmu' : weightSp E mu ⊓ ⊤ ≠ ⊥` using `hmu`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hmu'`. Establish `hxw` using `(Submodule.mem_inf.1 hx).1`. Simplify using `only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hxw`.

Establish `h3` using `hxw a`. Rewrite `h3` using `[LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h3, hx0⟩`. Establish `hfin2 : ((fun p : (Fin n → ℤ) × Fin n => (p.1 p.2).toNat) '' (wtsOf E (⊤ : Submodule K V) ×ˢ (Set.univ : Set (Fin n)))).Finite` using `(hfin.prod Set.finite_univ).image _`. Use `hfin2.bddAbove.mono ?_` and prove the remaining obligations.

Introduce and unpack `k ⟨a, b, hab, h⟩`. Use `⟨((k : ℤ) • rootW a b, a), ⟨h, Set.mem_univ _⟩, ?_⟩` and prove the remaining obligations. Use `show (((k : ℤ) • rootW a b) a).toNat = k`. Rewrite using `[root_multiple_apply_first a b hab k]`. Simplify using the standard rewrite rules.
-/
private theorem bddAbove_root_multiples_in_weights {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (E : GLOps n K V) :
    BddAbove {k : ℕ | ∃ a b, a ≠ b ∧ (k : ℤ) • rootW a b ∈ wtsOf E (⊤ : Submodule K V)} := by
  classical
  have hfin : (wtsOf E (⊤ : Submodule K V)).Finite := by
    have hA : ∀ a : Fin n, {m : ℤ | (E a a).HasEigenvalue (m : K)}.Finite := fun a =>
      (Module.End.finite_hasEigenvalue (E a a)).preimage Int.cast_injective.injOn
    refine (Set.Finite.pi (t := fun a => {m : ℤ | (E a a).HasEigenvalue (m : K)}) hA).subset ?_
    intro mu hmu
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    intro a
    have hmu' : weightSp E mu ⊓ ⊤ ≠ ⊥ := hmu
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hmu'
    have hxw := (Submodule.mem_inf.1 hx).1
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hxw
    have h3 := hxw a
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h3
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h3, hx0⟩
  have hfin2 : ((fun p : (Fin n → ℤ) × Fin n => (p.1 p.2).toNat) ''
      (wtsOf E (⊤ : Submodule K V) ×ˢ (Set.univ : Set (Fin n)))).Finite :=
    (hfin.prod Set.finite_univ).image _
  refine hfin2.bddAbove.mono ?_
  rintro k ⟨a, b, hab, h⟩
  refine ⟨((k : ℤ) • rootW a b, a), ⟨h, Set.mem_univ _⟩, ?_⟩
  show (((k : ℤ) • rootW a b) a).toNat = k
  rw [root_multiple_apply_first a b hab k]
  simp

/- English proof (translation)
Unfold `InvariantDenominatorEllPBound`. Introduce `p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx`. Use `haveI := dvr_fraction_field_charZero_prime S hG.prime`. Use `invariant_projection_denominator D h2 h5 p n' O S hG n V E hE M hM Inv hInv _ ?_ x hx` and prove the remaining obligations. Introduce `k a b hab h0 hk`.

Rewrite using `[hMQ]`. Unfold `ellP`. Use `le_csSup (bddAbove_root_multiples_in_weights E) ⟨a, b, hab, ?_⟩` and prove the remaining obligations. Use `show weightSp E _ ⊓ ⊤ ≠ ⊥`. Rewrite using `[inf_top_eq]` and apply the resulting hypothesis.
-/
theorem invariant_denominator_sharp_of (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) : InvariantDenominatorEllPBound := by
  unfold InvariantDenominatorEllPBound
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI := dvr_fraction_field_charZero_prime S hG.prime
  refine invariant_projection_denominator D h2 h5 p n' O S hG n V E hE M hM Inv hInv _ ?_ x hx
  intro k a b hab h0 hk
  rw [hMQ]
  unfold ellP
  refine le_csSup (bddAbove_root_multiples_in_weights E) ⟨a, b, hab, ?_⟩
  show weightSp E _ ⊓ ⊤ ≠ ⊥
  rwa [inf_top_eq]

/- English proof (translation)
Establish `hfin : (wtsOf E (⊤ : Submodule K V)).Finite`. Establish `hA : ∀ a : Fin n, {m : ℤ | (E a a).HasEigenvalue (m : K)}.Finite` using `fun a => (Module.End.finite_hasEigenvalue (E a a)).preimage Int.cast_injective.injOn`. Use `(Set.Finite.pi (t := fun a => {m : ℤ | (E a a).HasEigenvalue (m : K)}) hA).subset ?_` and prove the remaining obligations. Introduce `mu hmu`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]`.

Introduce `a`. Establish `hmu' : weightSp E mu ⊓ ⊤ ≠ ⊥` using `hmu`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hmu'`. Establish `hxw` using `(Submodule.mem_inf.1 hx).1`. Simplify using `only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hxw`.

Establish `h3` using `hxw a`. Rewrite `h3` using `[LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h3, hx0⟩`. Establish `hfin2 : ((fun p : (Fin n → ℤ) × (Fin n → ℤ) × Fin n => (p.1 p.2.2 - p.2.1 p.2.2).toNat) '' (wtsOf E (⊤ : Submodule K V) ×ˢ (wtsOf E (⊤ : Submodule K V) ×ˢ (Set.univ : Set (Fin n))))).Finite` using `(hfin.prod (hfin.prod Set.finite_univ)).image _`. Use `hfin2.bddAbove.mono ?_` and prove the remaining obligations.

Introduce and unpack `k ⟨mu, hmu, nu, hnu, a, b, hab, h⟩`. Use `⟨(mu, nu, a), ⟨hmu, hnu, Set.mem_univ _⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun h a`. Simplify using `[rootW, Pi.single_apply, hab] at h1`. Use `show (mu a - nu a).toNat = k`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem bddAbove_root_multiples_in_weight_differences {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (E : GLOps n K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b, a ≠ b ∧
      mu - nu = (k : ℤ) • rootW a b} := by
  classical
  have hfin : (wtsOf E (⊤ : Submodule K V)).Finite := by
    have hA : ∀ a : Fin n, {m : ℤ | (E a a).HasEigenvalue (m : K)}.Finite := fun a =>
      (Module.End.finite_hasEigenvalue (E a a)).preimage Int.cast_injective.injOn
    refine (Set.Finite.pi (t := fun a => {m : ℤ | (E a a).HasEigenvalue (m : K)}) hA).subset ?_
    intro mu hmu
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    intro a
    have hmu' : weightSp E mu ⊓ ⊤ ≠ ⊥ := hmu
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hmu'
    have hxw := (Submodule.mem_inf.1 hx).1
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hxw
    have h3 := hxw a
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h3
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h3, hx0⟩
  have hfin2 : ((fun p : (Fin n → ℤ) × (Fin n → ℤ) × Fin n => (p.1 p.2.2 - p.2.1 p.2.2).toNat) ''
      (wtsOf E (⊤ : Submodule K V) ×ˢ (wtsOf E (⊤ : Submodule K V) ×ˢ (Set.univ : Set (Fin n))))).Finite :=
    (hfin.prod (hfin.prod Set.finite_univ)).image _
  refine hfin2.bddAbove.mono ?_
  rintro k ⟨mu, hmu, nu, hnu, a, b, hab, h⟩
  refine ⟨(mu, nu, a), ⟨hmu, hnu, Set.mem_univ _⟩, ?_⟩
  have h1 := congrFun h a
  simp [rootW, Pi.single_apply, hab] at h1
  show (mu a - nu a).toNat = k
  omega

/- English proof (translation)
Unfold `InvariantProjectionField`. Introduce `p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv`. Use `haveI := dvr_fraction_field_charZero_prime S hG.prime`. Use `⟨fun π hπ ord hord T hT => invariant_projection_extremal_formula D h2 h5 E hE Inv hInv π hπ ord hord T hT, fun x hx => ?_⟩` and prove the remaining obligations. Use `invariant_projection_denominator D h2 h5 p n' O S hG n V E hE M hM Inv hInv _ ?_ x hx` and prove the remaining obligations.

Introduce `k a b hab h0 hk`. Rewrite using `[hMQ]`. Unfold `ellOf`. Use `le_csSup (bddAbove_root_multiples_in_weight_differences E) ⟨(k : ℤ) • rootW a b, ?_, 0, ?_, a, b, hab, sub_zero _⟩` and prove the remaining obligations. Use `show weightSp E _ ⊓ ⊤ ≠ ⊥`.

Rewrite using `[inf_top_eq]` and apply the resulting hypothesis. Use `show weightSp E 0 ⊓ ⊤ ≠ ⊥`. Rewrite using `[inf_top_eq]` and apply the resulting hypothesis.
-/
theorem invariant_projection_lemma_of (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) : InvariantProjectionField D := by
  unfold InvariantProjectionField
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv
  haveI := dvr_fraction_field_charZero_prime S hG.prime
  refine ⟨fun π hπ ord hord T hT => invariant_projection_extremal_formula D h2 h5 E hE Inv hInv π hπ ord hord T hT, fun x hx => ?_⟩
  refine invariant_projection_denominator D h2 h5 p n' O S hG n V E hE M hM Inv hInv _ ?_ x hx
  intro k a b hab h0 hk
  rw [hMQ]
  unfold ellOf
  refine le_csSup (bddAbove_root_multiples_in_weight_differences E) ⟨(k : ℤ) • rootW a b, ?_, 0, ?_, a, b, hab, sub_zero _⟩
  · show weightSp E _ ⊓ ⊤ ≠ ⊥
    rwa [inf_top_eq]
  · show weightSp E 0 ⊓ ⊤ ≠ ⊥
    rwa [inf_top_eq]

end Formalism.MainNotions.G.GLWeightTheory
