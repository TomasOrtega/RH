import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisCmpExist

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G]
  {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, smul_zero]`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Consider the case `tmul b x => simp [TWincl, TensorProduct.smul_tmul']`.
-/
theorem twincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul b x => simp [TWincl, TensorProduct.smul_tmul']

/- English proof (translation)
Use `haveI : Module.Free O ↥T.L.T := T.L.free`. Conclude with `Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf`.
-/
theorem twincl_injective {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (hf : Function.Injective f) : Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

/- English proof (translation)
Rewrite using `[inclL_apply, inclL_apply, ← Matrix.mulVec_smul]`. Conclude with `congrArg _ (funext fun i => map_mul _ _ _)`.
-/
theorem inclL_smul' (r : OA l O) (d : ι → OA l O) : inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

variable {I : Ident t ϖ P T} {m n : OA l O}

def dFun (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) : ι → OA l O :=
  (LinearMap.mem_range.1 (hn x)).choose

/- English proof (translation)
The claim follows from `(LinearMap.mem_range.1 (hn x)).choose_spec`.
-/
theorem dFun_spec (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) :
    inclL t ϖ P (dFun hn x) = inclO l O n • I.ofT x :=
  (LinearMap.mem_range.1 (hn x)).choose_spec

def dMap (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : ↥T.L.T →ₗ[O] (ι → OA l O) where
  toFun := dFun hn
  map_add' x y := inclL_injective t ϖ P (by
    rw [map_add, dFun_spec, dFun_spec, dFun_spec, map_add, smul_add])
  map_smul' r x := inclL_injective t ϖ P (by
    rw [LinearMap.map_smul, dFun_spec, dFun_spec, LinearMap.map_smul, RingHom.id_apply, smul_comm])

/- English proof (translation)
The claim follows from `dFun_spec hn x`.
-/
theorem dMap_spec (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) :
    inclL t ϖ P (dMap hn x) = inclO l O n • I.ofT x :=
  dFun_spec hn x

def gA (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : TW (OA l O) T →ₗ[OA l O] (ι → OA l O) :=
  LinearMap.liftBaseChange (OA l O) (dMap hn)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Consider the case `tmul b x`. Rewrite using `[gA, LinearMap.liftBaseChange_tmul, inclL_smul', dMap_spec]`.

Establish `: TWincl (inclO l O) T (b ⊗ₜ[O] x) = inclO l O b • ((1 : OW l O) ⊗ₜ[O] x)`. Simplify using `[TWincl, smul_tmul']`. Rewrite using `[this, LinearEquiv.map_smul, smul_comm]`. Both sides reduce to the same expression.
-/
theorem inclL_gA (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (z : TW (OA l O) T) :
    inclL t ϖ P (gA hn z) = inclO l O n • I.j.symm (TWincl (inclO l O) T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul b x =>
    rw [gA, LinearMap.liftBaseChange_tmul, inclL_smul', dMap_spec]
    have : TWincl (inclO l O) T (b ⊗ₜ[O] x) = inclO l O b • ((1 : OW l O) ⊗ₜ[O] x) := by
      simp [TWincl, smul_tmul']
    rw [this, LinearEquiv.map_smul, smul_comm]
    rfl

def zz (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z) (i : ι) :
    TW (OA l O) T :=
  (hm _ ⟨Pi.single i 1, rfl⟩).choose

/- English proof (translation)
The claim follows from `(hm _ ⟨Pi.single i 1, rfl⟩).choose_spec`.
-/
theorem zz_spec (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (i : ι) : I.j (inclO l O m • inclL t ϖ P (Pi.single i 1)) = TWincl (inclO l O) T (zz hm i) :=
  (hm _ ⟨Pi.single i 1, rfl⟩).choose_spec

def crisComparisonLToBcrisTensorMap (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z) :
    (ι → OB l O) →ₗ[OB l O] TW (OB l O) T :=
  (Pi.basisFun (OB l O) ι).constr (OB l O) fun i => TWincl (toB l O) T (zz hm i)

def crisComparisonBcrisTensorToLMap (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : TW (OB l O) T →ₗ[OB l O] (ι → OB l O) :=
  LinearMap.liftBaseChange (OB l O) (((toB l O).toLinearMap.compLeft ι) ∘ₗ dMap hn)

/- English proof (translation)
Establish `hz' : z = ∑ i, c i • zz hm i`. Apply `twincl_injective (T := T) (inclO l O) inclO_injective` to reduce the goal to its premises. Rewrite using `[← hz, map_sum]`. Establish `hc : inclL t ϖ P c = ∑ i, inclO l O (c i) • inclL t ϖ P (Pi.single i 1)` using `by conv_lhs => rw [pi_eq_sum_univ' c]`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => inclL_smul' _ _`. Rewrite using `[hc, Finset.smul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[twincl_smul, ← zz_spec hm i, smul_comm, LinearEquiv.map_smul]`. Rewrite using `[hz', map_sum, crisComparisonLToBcrisTensorMap, Module.Basis.constr_apply_fintype]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[twincl_smul, Pi.basisFun_equivFun]`. Both sides reduce to the same expression.
-/
theorem kisin_jB_toB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (c : ι → OA l O) (z : TW (OA l O) T)
    (hz : I.j (inclO l O m • inclL t ϖ P c) = TWincl (inclO l O) T z) :
    crisComparisonLToBcrisTensorMap hm (fun i => toB l O (c i)) = TWincl (toB l O) T z := by
  have hz' : z = ∑ i, c i • zz hm i := by
    apply twincl_injective (T := T) (inclO l O) inclO_injective
    rw [← hz, map_sum]
    have hc : inclL t ϖ P c = ∑ i, inclO l O (c i) • inclL t ϖ P (Pi.single i 1) := by
      conv_lhs => rw [pi_eq_sum_univ' c]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => inclL_smul' _ _
    rw [hc, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [twincl_smul, ← zz_spec hm i, smul_comm, LinearEquiv.map_smul]
  rw [hz', map_sum, crisComparisonLToBcrisTensorMap, Module.Basis.constr_apply_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [twincl_smul, Pi.basisFun_equivFun]
  rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => funext i`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add]`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Consider the case `tmul b x`. Establish `: TWincl (toB l O) T (b ⊗ₜ[O] x) = toB l O b ⊗ₜ[O] x` using `by simp [TWincl]`. Rewrite using `[this, crisComparisonBcrisTensorToLMap, gA, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul]`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules.
-/
theorem kisin_kB_tensor_incl (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (z : TW (OA l O) T) :
    crisComparisonBcrisTensorToLMap hn (TWincl (toB l O) T z) = fun i => toB l O (gA hn z i) := by
  induction z using TensorProduct.induction_on with
  | zero => funext i; simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]; funext i; simp
  | tmul b x =>
    have : TWincl (toB l O) T (b ⊗ₜ[O] x) = toB l O b ⊗ₜ[O] x := by simp [TWincl]
    rw [this, crisComparisonBcrisTensorToLMap, gA, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul]
    funext i
    simp

/- English proof (translation)
Establish `h : (crisComparisonBcrisTensorToLMap hn).comp (crisComparisonLToBcrisTensorMap hm) = (toB l O m * toB l O n) • LinearMap.id`. Use `(Pi.basisFun (OB l O) ι).ext fun i => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, crisComparisonLToBcrisTensorMap, Module.Basis.constr_basis, kisin_kB_tensor_incl, LinearMap.smul_apply, LinearMap.id_apply]`. Establish `hg : gA hn (zz hm i) = (m * n) • Pi.single i 1`. Apply `inclL_injective t ϖ P` to reduce the goal to its premises.

Rewrite using `[inclL_gA, ← zz_spec hm i, LinearEquiv.symm_apply_apply, inclL_smul', map_mul, mul_smul, smul_comm]`. Rewrite using `[hg, Pi.basisFun_apply]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hij]`. Conclude with `LinearMap.congr_fun h v`.
-/
theorem kisin_kB_comp_jB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (v : ι → OB l O) :
    crisComparisonBcrisTensorToLMap hn (crisComparisonLToBcrisTensorMap hm v) = (toB l O m * toB l O n) • v := by
  have h : (crisComparisonBcrisTensorToLMap hn).comp (crisComparisonLToBcrisTensorMap hm) = (toB l O m * toB l O n) • LinearMap.id := by
    refine (Pi.basisFun (OB l O) ι).ext fun i => ?_
    rw [LinearMap.comp_apply, crisComparisonLToBcrisTensorMap, Module.Basis.constr_basis, kisin_kB_tensor_incl, LinearMap.smul_apply, LinearMap.id_apply]
    have hg : gA hn (zz hm i) = (m * n) • Pi.single i 1 := by
      apply inclL_injective t ϖ P
      rw [inclL_gA, ← zz_spec hm i, LinearEquiv.symm_apply_apply, inclL_smul', map_mul, mul_smul, smul_comm]
    rw [hg, Pi.basisFun_apply]
    funext j
    by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_apply, hij]
  exact LinearMap.congr_fun h v

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]`. Consider the case `tmul b x`. Establish `h1 : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x)` using `by rw [smul_tmul', smul_eq_mul, mul_one]`.

Rewrite using `[h1, LinearMap.map_smul, LinearMap.map_smul, smul_comm]`. Use `congr 1`. Rewrite using `[crisComparisonBcrisTensorToLMap, LinearMap.liftBaseChange_tmul, one_smul]`. Express the relevant statement in the definitionally equal form `crisComparisonLToBcrisTensorMap hm (fun i => toB l O (dMap hn x i)) = _`. Rewrite using `[kisin_jB_toB hm (dMap hn x) ((m * n) ⊗ₜ[O] x)]`.

Simplify using `[TWincl, smul_tmul']`. Rewrite using `[dMap_spec, smul_smul, ← map_mul, LinearEquiv.map_smul, Ident.j_ofT]`. Simplify using `[TWincl, smul_tmul']`.
-/
theorem kisin_jB_comp_kB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (w : TW (OB l O) T) :
    crisComparisonLToBcrisTensorMap hm (crisComparisonBcrisTensorToLMap hn w) = (toB l O m * toB l O n) • w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | tmul b x =>
    have h1 : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [h1, LinearMap.map_smul, LinearMap.map_smul, smul_comm]
    congr 1
    rw [crisComparisonBcrisTensorToLMap, LinearMap.liftBaseChange_tmul, one_smul]
    change crisComparisonLToBcrisTensorMap hm (fun i => toB l O (dMap hn x i)) = _
    rw [kisin_jB_toB hm (dMap hn x) ((m * n) ⊗ₜ[O] x)]
    · simp [TWincl, smul_tmul']
    · rw [dMap_spec, smul_smul, ← map_mul, LinearEquiv.map_smul, Ident.j_ofT]
      simp [TWincl, smul_tmul']

/- English proof (translation)
Take `⟨u, hu'⟩` from `hu`. Take `⟨v, hv'⟩` from `hv`. Set `F : (ι → OB l O) →ₗ[OB l O] TW (OB l O) T` to `((u⁻¹ : (OB l O)ˣ) : OB l O) • crisComparisonLToBcrisTensorMap hm`. Set `Gm : TW (OB l O) T →ₗ[OB l O] (ι → OB l O)` to `((v⁻¹ : (OB l O)ˣ) : OB l O) • crisComparisonBcrisTensorToLMap hn`. Establish `key : ((u⁻¹ : (OB l O)ˣ) : OB l O) * (((v⁻¹ : (OB l O)ˣ) : OB l O) * (toB l O m * toB l O n)) = 1`.

Rewrite using `[← hu', ← hv']`. Combine the equalities or inequalities in the displayed calculation. Establish `key2 : ((v⁻¹ : (OB l O)ˣ) : OB l O) * (((u⁻¹ : (OB l O)ˣ) : OB l O) * (toB l O m * toB l O n)) = 1`. Rewrite using `[← key]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨LinearEquiv.ofLinear F Gm ?_ ?_, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Simplify using `only [F, Gm, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, kisin_jB_comp_kB, smul_smul, LinearMap.id_apply]`. Rewrite using `[key, one_smul]`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations.

Simplify using `only [F, Gm, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, kisin_kB_comp_jB, smul_smul, LinearMap.id_apply]`. Rewrite using `[key2, one_smul]`. Introduce `c z hz`. Rewrite using `[LinearEquiv.ofLinear_apply]`. Establish `hz2 : I.j (inclO l O m • inclL t ϖ P c) = TWincl (inclO l O) T (m • z)`.

Rewrite using `[LinearEquiv.map_smul, hz, twincl_smul]`. Simplify using `only [F, LinearMap.smul_apply]`. Rewrite using `[kisin_jB_toB hm c _ hz2, twincl_smul, smul_smul, ← hu', Units.inv_mul, one_smul]`.
-/
theorem exists_of (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (hu : IsUnit (toB l O m)) (hv : IsUnit (toB l O n)) :
    ∃ jB, IsCrisCmp I jB := by
  obtain ⟨u, hu'⟩ := hu
  obtain ⟨v, hv'⟩ := hv
  let F : (ι → OB l O) →ₗ[OB l O] TW (OB l O) T := ((u⁻¹ : (OB l O)ˣ) : OB l O) • crisComparisonLToBcrisTensorMap hm
  let Gm : TW (OB l O) T →ₗ[OB l O] (ι → OB l O) := ((v⁻¹ : (OB l O)ˣ) : OB l O) • crisComparisonBcrisTensorToLMap hn
  have key : ((u⁻¹ : (OB l O)ˣ) : OB l O) * (((v⁻¹ : (OB l O)ˣ) : OB l O) * (toB l O m * toB l O n)) = 1 := by
    rw [← hu', ← hv']
    calc _ = (((u⁻¹ : (OB l O)ˣ) : OB l O) * u) * (((v⁻¹ : (OB l O)ˣ) : OB l O) * v) := by ring
      _ = 1 := by rw [Units.inv_mul, Units.inv_mul, mul_one]
  have key2 : ((v⁻¹ : (OB l O)ˣ) : OB l O) * (((u⁻¹ : (OB l O)ˣ) : OB l O) * (toB l O m * toB l O n)) = 1 := by
    rw [← key]; ring
  refine ⟨LinearEquiv.ofLinear F Gm ?_ ?_, ?_⟩
  · refine LinearMap.ext fun w => ?_
    simp only [F, Gm, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, kisin_jB_comp_kB, smul_smul,
      LinearMap.id_apply]
    rw [key, one_smul]
  · refine LinearMap.ext fun w => ?_
    simp only [F, Gm, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, kisin_kB_comp_jB, smul_smul,
      LinearMap.id_apply]
    rw [key2, one_smul]
  · intro c z hz
    rw [LinearEquiv.ofLinear_apply]
    have hz2 : I.j (inclO l O m • inclL t ϖ P c) = TWincl (inclO l O) T (m • z) := by
      rw [LinearEquiv.map_smul, hz, twincl_smul]
    simp only [F, LinearMap.smul_apply]
    rw [kisin_jB_toB hm c _ hz2, twincl_smul, smul_smul, ← hu', Units.inv_mul, one_smul]

end GlobalTheory.BKGal.CrisCmpExist

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I`. Take `⟨α, β, hα, hβ⟩` from `P.exists_exponents`. Take `⟨ε, hε⟩` from `(GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1`. Take `⟨δ, hδ, -⟩` from `hε.2`. Take `⟨-, -, -, hunit, -, -, -⟩` from `(GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ`.

Take `⟨-, -, h3, h4⟩` from `GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ`. Establish `hU : ∀ k : ℕ, IsUnit (toB l O (1 ⊗ₜ (muOf ε ^ k)))` using `fun k => by`. Establish `: toB l O (1 ⊗ₜ (muOf ε ^ k)) = (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O) (acrisToBcris l (ainfToAcris l (muOf ε))) ^ k`. Rewrite using `[← map_pow, ← map_pow, ← map_pow]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `(hunit.map _).pow k`. Conclude with `GlobalTheory.BKGal.CrisCmpExist.exists_of h4 h3 (hU α) (hU β)`.
-/
theorem GlobalTheory.BKGal.exists_isCrisCmp : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jB, IsCrisCmp I jB := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, hunit, -, -, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  have hU : ∀ k : ℕ, IsUnit (toB l O (1 ⊗ₜ (muOf ε ^ k))) := fun k => by
    have : toB l O (1 ⊗ₜ (muOf ε ^ k)) = (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (muOf ε))) ^ k := by
      rw [← map_pow, ← map_pow, ← map_pow]
      rfl
    rw [this]
    exact (hunit.map _).pow k
  exact GlobalTheory.BKGal.CrisCmpExist.exists_of h4 h3 (hU α) (hU β)
