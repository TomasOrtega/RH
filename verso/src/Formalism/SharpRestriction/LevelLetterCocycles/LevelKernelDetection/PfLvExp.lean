import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Conv

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/- English proof (translation)
Rewrite using `[HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]`. Simplify using the standard rewrite rules.
-/
theorem Pf_LvExp_coeff_neg (x : PowerSeries R) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff (Int.negSucc k) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  simp

/- English proof (translation)
Rewrite using `[HahnModule.coeff_smul]`. Use `symm`. Use `Finset.sum_bij_ne_zero (fun j _ _ => ((j : ℤ), k - j)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j _ hj`. Establish `h1 : PowerSeries.coeff j x ≠ 0` using `fun h => hj (by rw [h, zero_smul])`.

Establish `h2 : ((HahnModule.of R).symm y).coeff (k - j) ≠ 0` using `fun h => hj (by rw [h, smul_zero])`. Rewrite using `[Finset.mem_vaddAntidiagonal]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[HahnSeries.mem_support, HahnSeries.ofPowerSeries_apply_coeff]`. Conclude with `h1`.

Rewrite using `[HahnSeries.mem_support]`. Conclude with `h2`. Use `show (j : ℤ) + (k - j) = k`. Expand and normalize the polynomial expressions, which then agree. Introduce `j _ _ j' _ _ h`.

Conclude with `(Prod.mk.inj h).1` after adjusting the coercions. Introduce `ij hij hne`. Rewrite `hij` using `[Finset.mem_vaddAntidiagonal]`. Take `⟨h1, h2, h3⟩` from `hij`. Take `⟨i, i'⟩` from `ij`.

Simplify using `only at h1 h2 h3 hne`. Consider the cases of `i with`. Consider the case `negSucc t => exact absurd (Pf_LvExp_coeff_neg x t) ((HahnSeries.mem_support _ _).1 h1)`. Consider the case `ofNat j`. Simplify using `only [Int.ofNat_eq_natCast, vadd_eq_add] at h3 hne`.

Establish `hi' : i' = k - j` using `by omega`. Establish `hm' : m ≤ i'`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Conclude with `(HahnSeries.mem_support _ _).1 h2 (hy _ hlt)`.

Use `⟨j, Finset.mem_range.2 (by omega), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hi']`. Rewrite `hne` using `[HahnSeries.ofPowerSeries_apply_coeff]`. Then use the resulting hypothesis. Simplify using `[hi']`. Introduce `j _ _ dsimp only`.

Rewrite using `[HahnSeries.ofPowerSeries_apply_coeff]`.
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
Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `j hj`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `h`. Apply `hj` to reduce the goal to its premises.

Use `show PowerSeries.coeff j f • g (k - j) = 0`. Rewrite using `[hg (k - j) (by omega), smul_zero]`.
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
Establish `h : ∀ y, ιV PD (LL` using `LL) (V := T.V) y = ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp [ιV]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp)` using `PD.ι_inj`. Introduce `a b hab`. Rewrite `hab` using `[h, h]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ hi hab`.
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
Simplify using `only [Pf_LvExp_Φ, toKsD, LinearEquiv.trans_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]`. Rewrite using `[← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem Pf_LvExp_Φ_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (f : Rs LL PD.p s → D) : Pf_LvExp_Φ W s D (toKsD W s D f) = f := by
  simp only [Pf_LvExp_Φ, toKsD, LinearEquiv.trans_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [← TensorProduct.comm_symm, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul g d => simp [Pf_LvExp_Φ, TensorProduct.smul_tmul', TensorProduct.piScalarRightHom_tmul, mul_smul]`. Consider the case `add z z' hz hz' => rw [smul_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hz, hz', smul_add]`.
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
Simplify using `only [coefN, Pf_LvExp_Φ_toKsD]`.
-/
theorem Pf_LvExp_Φ_coefN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (y : ↥(W.N T))
    (k : ℤ) (ζ : Rs LL PD.p s) :
    ((Pf_LvExp_Φ W s (Dc W T c) (coefN Lb s T c y k) ζ : Dc W T c) : T.V ⊗[Qp] B) =
      Lb.levB T c ζ y k := by
  simp only [coefN, Pf_LvExp_Φ_toKsD]

/- English proof (translation)
Introduce `s a y hy`. Take `⟨m, hm⟩` from `bdd_coefN Lb s T c y`. Establish `hm' : ∀ k < m, coefN Lb s T c y k = 0` using `fun k hk => by`. Assume the negation of the conclusion as `h`. Conclude with `absurd (hm h) (not_le.2 hk)`.

Apply `(HahnModule.of (KsW W s)).symm.injective` to reduce the goal to its premises. Use extensionality with `k`. Take `⟨N, hN⟩ : ∃ N : ℕ, k - m < N` from `⟨(k - m).toNat + 1, by omega⟩`. Rewrite using `[Pf_LvExp_coeff_smul _ _ m (fun k' hk' => by rw [Pf_LvExp_coeff_expN]; exact hm' k' hk') k N hN]`. Simplify using `only [Pf_LvExp_coeff_expN]`.

Apply `(Pf_LvExp_Φ W s (Dc W T c)).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `ζ`. Rewrite using `[map_sum, Finset.sum_apply]`. Simplify using `only [Pf_LvExp_Φ_smul]`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Pf_LvExp_ιV_inj (PD := PD) T` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Pf_LvExp_Φ_coefN]`. Simplify using `only [← levN_eq]`. Establish `hg : ∀ k' < m, W.levN T c ζ y k' = 0` using `fun k' hk' => by`. Rewrite using `[levN_eq, ← Pf_LvExp_Φ_coefN Lb s T c y k' ζ, hm' k' hk', map_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[show (⟨_, hy⟩ : ↥(W.N T)) = (baseIdOf hR).d a • y from rfl, W.levN_smul, Pf_LvExp_finsum _ _ m hg k N hN]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `h` using `congrArg (PowerSeries.coeff j) (map_eval_rhoL hR c s a ζ)`.

Rewrite `h` using `[PowerSeries.coeff_map]`. Conclude with `h.symm`.
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
