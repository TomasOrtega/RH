import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Conv

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Pf_LvExp_coeff_neg (x : PowerSeries R) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff (Int.negSucc k) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify by unfolding definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Pf_LvExp_coeff_smul (x : PowerSeries R) (y : HahnModule ℤ R M) (m : ℤ)
    (hy : ∀ k < m, ((HahnModule.of R).symm y).coeff k = 0) (k : ℤ) (N : ℕ) (hN : k - m < N) :
    ((HahnModule.of R).symm (HahnSeries.ofPowerSeries ℤ R x • y)).coeff k =
      ∑ j ∈ Finset.range N, PowerSeries.coeff j x • ((HahnModule.of R).symm y).coeff (k - j) := by
  rw [HahnModule.coeff_smul]
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ => ((j : ℤ), k - j)) ?_ ?_ ?_ ?_
  · intro j _ hj
    have h1 : PowerSeries.coeff j x ≠ 0 := fun h => hj (by rw [h, zero_smul])
    have h2 : ((HahnModule.of R).symm y).coeff (k - j) ≠ 0 := fun h => hj (by rw [h, smul_zero])
    rw [Finset.mem_vaddAntidiagonal]
    refine ⟨?_, ?_, ?_⟩
    · rw [HahnSeries.mem_support, HahnSeries.ofPowerSeries_apply_coeff]
      exact h1
    · rw [HahnSeries.mem_support]
      exact h2
    · show (j : ℤ) + (k - j) = k
      ring
  · intro j _ _ j' _ _ h
    exact_mod_cast (Prod.mk.inj h).1
  · intro ij hij hne
    rw [Finset.mem_vaddAntidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    obtain ⟨i, i'⟩ := ij
    simp only at h1 h2 h3 hne
    cases i with
    | negSucc t => exact absurd (Pf_LvExp_coeff_neg x t) ((HahnSeries.mem_support _ _).1 h1)
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast, vadd_eq_add] at h3 hne
      have hi' : i' = k - j := by omega
      have hm' : m ≤ i' := by
        by_contra hlt
        push Not at hlt
        exact (HahnSeries.mem_support _ _).1 h2 (hy _ hlt)
      refine ⟨j, Finset.mem_range.2 (by omega), ?_, ?_⟩
      · rw [← hi']
        rwa [HahnSeries.ofPowerSeries_apply_coeff] at hne
      · simp [hi']
  · intro j _ _
    dsimp only
    rw [HahnSeries.ofPowerSeries_apply_coeff]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Pf_LvExp_finsum (f : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) :
    ∑ᶠ j : ℕ, PowerSeries.coeff j f • g (k - j) = ∑ j ∈ Finset.range N, PowerSeries.coeff j f • g (k - j) := by
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply hj
  show PowerSeries.coeff j f • g (k - j) = 0
  rw [hg (k - j) (by omega), smul_zero]

end Conv

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem Pf_LvExp_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

open Classical in

def Pf_LvExp_Φ (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem Pf_LvExp_Φ_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (f : Rs LL PD.p s → D) : Pf_LvExp_Φ W s D (toKsD W s D f) = f := by
  simp only [Pf_LvExp_Φ, toKsD, LinearEquiv.trans_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem Pf_LvExp_Φ_smul (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (f : KsW W s)
    (z : KsW W s ⊗[LL] D) (ζ : Rs LL PD.p s) :
    Pf_LvExp_Φ W s D (f • z) ζ = f ζ • Pf_LvExp_Φ W s D z ζ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul g d => simp [Pf_LvExp_Φ, TensorProduct.smul_tmul', TensorProduct.piScalarRightHom_tmul, mul_smul]
  | add z z' hz hz' => rw [smul_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hz, hz', smul_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Pf_LvExp_coeff_expN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) : ((HahnModule.of (KsW W s)).symm (expN Lb s T c y)).coeff k = coefN Lb s T c y k :=
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Pf_LvExp_Φ_coefN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) (ζ : Rs LL PD.p s) :
    ((Pf_LvExp_Φ W s (Dc W T c) (coefN Lb s T c y k) ζ : Dc W T c) : T.V ⊗[Qp] B) =
      Lb.levB T c ζ y k := by
  simp only [coefN, Pf_LvExp_Φ_toKsD]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem expSemi_holds (Lb : LevB W) (hR : Ring9 W) (T : LocLat G Qp LL O) (c : ZMod n)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k)) :
    ExpSemi Lb hR T c := by
  intro s a y hy
  obtain ⟨m, hm⟩ := bdd_coefN Lb s T c y
  have hm' : ∀ k < m, coefN Lb s T c y k = 0 := fun k hk => by
    by_contra h
    exact absurd (hm h) (not_le.2 hk)
  apply (HahnModule.of (KsW W s)).symm.injective
  ext k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N := ⟨(k - m).toNat + 1, by omega⟩
  rw [Pf_LvExp_coeff_smul _ _ m (fun k' hk' => by rw [Pf_LvExp_coeff_expN]; exact hm' k' hk') k N hN]
  simp only [Pf_LvExp_coeff_expN]
  apply (Pf_LvExp_Φ W s (Dc W T c)).injective
  funext ζ
  rw [map_sum, Finset.sum_apply]
  simp only [Pf_LvExp_Φ_smul]
  apply Subtype.ext
  apply Pf_LvExp_ιV_inj (PD := PD) T
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Pf_LvExp_Φ_coefN]
  simp only [← levN_eq]
  have hg : ∀ k' < m, W.levN T c ζ y k' = 0 := fun k' hk' => by
    rw [levN_eq, ← Pf_LvExp_Φ_coefN Lb s T c y k' ζ, hm' k' hk', map_zero]
    simp
  rw [show (⟨_, hy⟩ : ↥(W.N T)) = (baseIdOf hR).d a • y from rfl, W.levN_smul,
    Pf_LvExp_finsum _ _ m hg k N hN]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := congrArg (PowerSeries.coeff j) (map_eval_rhoL hR c s a ζ)
  rw [PowerSeries.coeff_map] at h
  exact h.symm

end Formalism.MainNotions.N.Ln03.Pf
