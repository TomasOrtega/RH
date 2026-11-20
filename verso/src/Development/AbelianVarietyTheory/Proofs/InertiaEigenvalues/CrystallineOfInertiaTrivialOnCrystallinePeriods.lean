import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixesMaximalUnramifiedExtensionQlStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodsExtensionSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaMulGaloisCompositumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpeiserDescentSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallinePeriodsLeSpanStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.CrysInertDescent

/- English proof (translation)
The claim follows from `GlobalTheory.T.inertia_fixes_maximalUnramifiedExtension_Ql`.
-/
theorem L_inert : ∀ (l : ℕ) [Fact l.Prime] (g : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l))), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) →
    ∀ x ∈ MaximalUnramifiedExtension l, (g : GQ l) x = x :=
  GlobalTheory.T.inertia_fixes_maximalUnramifiedExtension_Ql

/- English proof (translation)
The claim follows from `GlobalTheory.T.crystallinePeriods_extension_span`.
-/
theorem L_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
    ∀ (LL : FinExt l) (T : QLat LL) (K K'' : FinExt l), K.1 ≤ K''.1 → IsCrys (P.PD K) (T.ρ.comp (inclG K)) →
    DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')) ≤
      Submodule.span ↥(K0 K'') (↑(DcrisK₀ (P.PD K) (T.ρ.comp (inclG K))) : Set (P.R.B ⊗[ℚ_[l]] T.V)) :=
  GlobalTheory.T.crystallinePeriods_extension_span

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_inertia_mul_galois_compositum`.
-/
theorem L_lift : ∀ (l : ℕ) [Fact l.Prime] (K' F K'' : FinExt l), (GK K').Normal → K''.1 = K'.1 ⊔ F.1 →
    ∀ h : GQ l, h ∈ GK F → (∀ x ∈ K0 K'', h x = x) →
    ∃ i : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)), i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (i : GQ l) ∈ GK F ∧ (i : GQ l)⁻¹ * h ∈ GK K'' :=
  GlobalTheory.T.exists_inertia_mul_galois_compositum

/- English proof (translation)
The claim follows from `GlobalTheory.T.mem_span_fixed_of_semilinear_action`.
-/
theorem L_speiser : ∀ {G L Ω M : Type} [Group G] [Field L] [Field Ω] [Algebra L Ω] [AddCommGroup M] [Module Ω M]
    [Module L M] [IsScalarTower L Ω M] (b : G → Ω → Ω) (a : G → L →+* Ω) (σ : G → M →+ M) (W : Submodule L M),
    (∀ g h c, a (g * h) c = b g (a h c)) → (∀ c, a 1 c = algebraMap L Ω c) →
    (∀ m, σ 1 m = m) → (∀ g h m, σ (g * h) m = σ g (σ h m)) →
    (∀ g (c : L) m, σ g (c • m) = a g c • σ g m) → (Set.range a).Finite →
    (∀ g, ∀ m ∈ W, σ g m ∈ W) → (∀ g, (∀ c, a g c = algebraMap L Ω c) → ∀ m ∈ W, σ g m = m) →
    ∀ m ∈ W, m ∈ Submodule.span Ω {m | m ∈ W ∧ ∀ g, σ g m = m} :=
  GlobalTheory.T.mem_span_fixed_of_semilinear_action

/- English proof (translation)
The claim follows from `GlobalTheory.T.isCrys_of_crystallinePeriods_le_span`.
-/
theorem L_dim : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
    ∀ (LL : FinExt l) (T : QLat LL) (F K'' : FinExt l), IsCrys (P.PD K'') (T.ρ.comp (inclG K'')) →
    (∀ m ∈ DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')),
      m ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (↑(DcrisK₀ (P.PD F) (T.ρ.comp (inclG F))) : Set (P.R.B ⊗[ℚ_[l]] T.V))) →
    IsCrys (P.PD F) (T.ρ.comp (inclG F)) :=
  GlobalTheory.T.isCrys_of_crystallinePeriods_le_span

end GlobalTheory.CrysInertDescent

namespace GlobalTheory.CrysInertDescent

variable {l : ℕ} [Fact l.Prime]

def sigQ (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (g : Gl l) :
    P.R.B ⊗[ℚ_[l]] T.V →ₗ[ℚ_[l]] P.R.B ⊗[ℚ_[l]] T.V :=
  TensorProduct.map (P.actQ (g : GQ l)).toLinearMap ((T.ρ g).restrictScalars ℚ_[l])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigQ_tmul (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (g : Gl l) (b : P.R.B) (v : T.V) :
    sigQ P T g (b ⊗ₜ v) = P.actQ (g : GQ l) b ⊗ₜ T.ρ g v := rfl

/- English proof (translation)
The claim follows from `TensorProduct.ext' fun b v => by rw [sig_tmul, sigQ_tmul, P.PD_actB] rfl`.
-/
theorem sig_res (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (K : FinExt l) (k : ↥(GK K)) :
    sig (P.PD K) (T.ρ.comp (inclG K)) k = sigQ P T (inclG K k) :=
  TensorProduct.ext' fun b v => by
    rw [sig_tmul, sigQ_tmul, P.PD_actB]
    rfl

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b v`. Rewrite using `[sigQ_tmul, OneMemClass.coe_one, map_one, map_one]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, hx, hy]`.
-/
theorem sigQ_one (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (w : P.R.B ⊗[ℚ_[l]] T.V) :
    sigQ P T 1 w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [sigQ_tmul, OneMemClass.coe_one, map_one, map_one]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

end GlobalTheory.CrysInertDescent

namespace GlobalTheory.CrysInertDescent
variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `TensorProduct.ext' fun b v => by rw [LinearMap.comp_apply, sigQ_tmul, sigQ_tmul, sigQ_tmul] congr 1 · exact DFunLike.congr_fun (P.actQ.map_mul (g : GQ l) (h : GQ l)) b · exact DFunLike.congr_fun (T.ρ.map_mul g h) v`.
-/
theorem sigQ_mul (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (g h : Gl l) :
    sigQ P T (g * h) = (sigQ P T g).comp (sigQ P T h) :=
  TensorProduct.ext' fun b v => by
    rw [LinearMap.comp_apply, sigQ_tmul, sigQ_tmul, sigQ_tmul]
    congr 1
    · exact DFunLike.congr_fun (P.actQ.map_mul (g : GQ l) (h : GQ l)) b
    · exact DFunLike.congr_fun (T.ρ.map_mul g h) v

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c v`. Rewrite using `[TensorProduct.smul_tmul', sigQ_tmul, sigQ_tmul, TensorProduct.smul_tmul']`. Use `congr 1`.

Conclude with `map_mul (P.actQ (g : GQ l)) b c`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.
-/
theorem sigQ_smul (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (g : Gl l) (b : P.R.B)
    (w : P.R.B ⊗[ℚ_[l]] T.V) : sigQ P T g (b • w) = P.actQ (g : GQ l) b • sigQ P T g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.smul_tmul', sigQ_tmul, sigQ_tmul, TensorProduct.smul_tmul']
    congr 1
    exact map_mul (P.actQ (g : GQ l)) b c
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/- English proof (translation)
Establish `e : (TensorProduct.comm ℚ_[l] P.R.B T.V).toLinearMap ∘ₗ sigQ P T g = ((actVB (P.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g).restrictScalars ℚ_[l]) ∘ₗ (TensorProduct.comm ℚ_[l] P.R.B T.V).toLinearMap` using `TensorProduct.ext' fun b v => by`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, sigQ_tmul, TensorProduct.comm_tmul, LinearMap.restrictScalars_apply, actVB, AlgebraTensorModule.map_tmul]`. Use `congr 1`. Conclude with `(P.PD_actB _ g b).symm`. Conclude with `LinearMap.congr_fun e w`.
-/
theorem comm_sigQ (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (g : Gl l) (w : P.R.B ⊗[ℚ_[l]] T.V) :
    TensorProduct.comm ℚ_[l] P.R.B T.V (sigQ P T g w) =
      actVB (P.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (TensorProduct.comm ℚ_[l] P.R.B T.V w) := by
  have e : (TensorProduct.comm ℚ_[l] P.R.B T.V).toLinearMap ∘ₗ sigQ P T g =
      ((actVB (P.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g).restrictScalars ℚ_[l]) ∘ₗ
        (TensorProduct.comm ℚ_[l] P.R.B T.V).toLinearMap :=
    TensorProduct.ext' fun b v => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, sigQ_tmul, TensorProduct.comm_tmul,
        LinearMap.restrictScalars_apply, actVB, AlgebraTensorModule.map_tmul]
      congr 1
      exact (P.PD_actB _ g b).symm
  exact LinearMap.congr_fun e w

end GlobalTheory.CrysInertDescent

namespace GlobalTheory.CrysInertDescent
variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h1 : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l`. Unfold `MaximalUnramifiedExtension`. Rewrite using `[IntermediateField.adjoin_map]`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, ⟨m, hm, hl, hy⟩, rfl⟩`.

Conclude with `IntermediateField.subset_adjoin _ _ ⟨m, hm, hl, by rw [← map_pow, hy, map_one]⟩`. Conclude with `h1 ⟨x, hx, rfl⟩`.
-/
theorem kur_stable (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : g x ∈ MaximalUnramifiedExtension l := by
  have h1 : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨y, ⟨m, hm, hl, hy⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hl, by rw [← map_pow, hy, map_one]⟩
  exact h1 ⟨x, hx, rfl⟩

/- English proof (translation)
The claim follows from `P.actQ_Kur _ c c (L_inert l i hi c c.2)`.
-/
theorem inert_fix_B (P : LocPrime l) (i : Gl l) (hi : i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l)) (c : ↥(MaximalUnramifiedExtension l)) :
    P.actQ (i : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c :=
  P.actQ_Kur _ c c (L_inert l i hi c c.2)

/- English proof (translation)
Rewrite using `[← algebraMap_smul P.R.B c w, sigQ_smul, ← algebraMap_smul P.R.B c (sigQ P T i w)]`. Use `congr 1`. Conclude with `inert_fix_B P i hi _`.
-/
theorem sigQ_smul_K0 (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (K : FinExt l) (i : Gl l)
    (hi : i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l)) (c : ↥(K0 K)) (w : P.R.B ⊗[ℚ_[l]] T.V) :
    sigQ P T i (c • w) = c • sigQ P T i w := by
  rw [← algebraMap_smul P.R.B c w, sigQ_smul, ← algebraMap_smul P.R.B c (sigQ P T i w)]
  congr 1
  exact inert_fix_B P i hi _

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy]`.

Consider the case `smul c x _ hx => rw [hf, hf', hx]`.
-/
theorem eq_on_span {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] (f f' : M →+ M)
    (hf : ∀ (c : R) w, f (c • w) = c • f w) (hf' : ∀ (c : R) w, f' (c • w) = c • f' w) (s : Set M)
    (h : ∀ w ∈ s, f w = f' w) : ∀ w ∈ Submodule.span R s, f w = f' w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [hf, hf', hx]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Simplify using `only [actVB, mulVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, AlgEquiv.toAlgHom_toLinearMap, AlgEquiv.toLinearMap_apply, map_mul]`. Use `congr 1`.

Rewrite using `[P.PD_actB]`. Conclude with `congrArg (· * _) (inert_fix_B P i hi _)`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem actVB_mulVB_inert (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (K : FinExt l) (i : Gl l)
    (hi : i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l)) (c : ↥(K0 K)) (y : T.V ⊗[ℚ_[l]] P.R.B) :
    actVB (P.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ i (mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := T.V) (LL := ↥LL.1) c y) =
      mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := T.V) (LL := ↥LL.1) c (actVB (P.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ i y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [actVB, mulVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply,
      LinearMap.mulLeft_apply, AlgEquiv.toAlgHom_toLinearMap, AlgEquiv.toLinearMap_apply, map_mul]
    congr 1
    rw [P.PD_actB]
    exact congrArg (· * _) (inert_fix_B P i hi _)
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.CrysInertDescent

namespace GlobalTheory.CrysInertDescent
variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h0 : Commute (mulVB (K₀` using `↥(K0 K)) (B := P.R.B) (V := T.V) (LL := ↥LL.1) c) (actVB (P.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ i) := LinearMap.ext fun y => (actVB_mulVB_inert P T K i hi c y).symm`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [Polynomial.aeval_add]`. Conclude with `hp.add_right hq`. Consider the case `monomial n a`.

Rewrite using `[Polynomial.aeval_monomial]`. Conclude with `(Algebra.commute_algebraMap_right a _).mul_right (h0.pow_right n)`.
-/
theorem commute_aeval_mulVB (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (K : FinExt l) (i : Gl l)
    (hi : i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l)) (c : ↥(K0 K)) (p : Polynomial ↥LL.1) :
    Commute (mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := T.V) (LL := ↥LL.1) c)
      (Polynomial.aeval (actVB (P.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ i : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B)) p) := by
  have h0 : Commute (mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := T.V) (LL := ↥LL.1) c)
      (actVB (P.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ i) :=
    LinearMap.ext fun y => (actVB_mulVB_inert P T K i hi c y).symm
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.aeval_add]; exact hp.add_right hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_right a _).mul_right (h0.pow_right n)

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact hp _ hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]`.

Consider the case `smul c x _ hx`. Establish `e1` using `LinearMap.congr_fun (hcm c).eq (TensorProduct.comm ℚ_[l] P.R.B T.V x)`. Rewrite using `[comm_smul (LL := ↥LL.1)]`. Conclude with `e1.symm.trans ((congrArg (mulVB (K₀ := ↥(K0 K'')) (B := P.R.B) (V := T.V) (LL := ↥LL.1) c) hx).trans (map_zero _))`.
-/
theorem kill_span (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (K K'' : FinExt l)
    (Φ : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B))
    (hcm : ∀ c : ↥(K0 K''), Commute (mulVB (K₀ := ↥(K0 K'')) (B := P.R.B) (V := T.V) (LL := ↥LL.1) c) Φ)
    (hp : ∀ x ∈ Dcris (P.PD K) (T.ρ.comp (inclG K)), Φ x = 0) :
    ∀ w ∈ Submodule.span ↥(K0 K'') (↑(DcrisK₀ (P.PD K) (T.ρ.comp (inclG K))) : Set (P.R.B ⊗[ℚ_[l]] T.V)),
      Φ (TensorProduct.comm ℚ_[l] P.R.B T.V w) = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hp _ hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | smul c x _ hx =>
    have e1 := LinearMap.congr_fun (hcm c).eq (TensorProduct.comm ℚ_[l] P.R.B T.V x)
    rw [comm_smul (LL := ↥LL.1)]
    exact e1.symm.trans ((congrArg (mulVB (K₀ := ↥(K0 K'')) (B := P.R.B) (V := T.V) (LL := ↥LL.1) c) hx).trans
      (map_zero _))

end GlobalTheory.CrysInertDescent

namespace GlobalTheory.CrysInertDescent
variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[mem_DcrisK₀]`. Conclude with `forall_congr' fun k => by rw [sig_res]`.
-/
theorem mem_res (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (K : FinExt l) (w : P.R.B ⊗[ℚ_[l]] T.V) :
    w ∈ DcrisK₀ (P.PD K) (T.ρ.comp (inclG K)) ↔ ∀ k : ↥(GK K), sigQ P T (inclG K k) w = w := by
  rw [mem_DcrisK₀]
  exact forall_congr' fun k => by rw [sig_res]

def embeddingRestrictMaxUnramified (K : FinExt l) (g : GQ l) : ↥(K0 K) →+* ↥(MaximalUnramifiedExtension l) where
  toFun c := ⟨g c, kur_stable g ((inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c.2)⟩
  map_one' := Subtype.ext (map_one g)
  map_mul' x y := Subtype.ext (map_mul g (x : Om l) y)
  map_zero' := Subtype.ext (map_zero g)
  map_add' x y := Subtype.ext (map_add g (x : Om l) y)

/- English proof (translation)
Use `(Set.finite_range (fun φ : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) => (φ : ↥(K0 K) →+* ↥(MaximalUnramifiedExtension l)))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨{ embeddingRestrictMaxUnramified K (g : GQ l) with commutes' := fun r => Subtype.ext ((g : GQ l).commutes r) }, rfl⟩`.
-/
theorem finite_range_restrictGaloisMaxUnramifiedSubfield (K F : FinExt l) [FiniteDimensional ℚ_[l] ↥(K0 K)] :
    (Set.range fun g : ↥(GK F) => embeddingRestrictMaxUnramified K (g : GQ l)).Finite := by
  refine (Set.finite_range (fun φ : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) => (φ : ↥(K0 K) →+* ↥(MaximalUnramifiedExtension l)))).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨{ embeddingRestrictMaxUnramified K (g : GQ l) with commutes' := fun r => Subtype.ext ((g : GQ l).commutes r) }, rfl⟩

/- English proof (translation)
Establish `e : GK K'' = GK K' ⊓ GK F`. Unfold `GK`. Rewrite using `[hK'', IntermediateField.fixingSubgroup_sup]`. Rewrite `hk`, the goal using `[e]`. Take `⟨hk1, hk2⟩` from `Subgroup.mem_inf.1 hk`.

Use `Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem (inv_mem hg) hk2) hg⟩` and prove the remaining obligations. Use `hN.conj_mem k hk1 g⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem conj_mem (K' F K'' : FinExt l) (hN : (GK K').Normal) (hK'' : K''.1 = K'.1 ⊔ F.1) (g k : GQ l)
    (hg : g ∈ GK F) (hk : k ∈ GK K'') : g⁻¹ * k * g ∈ GK K'' := by
  have e : GK K'' = GK K' ⊓ GK F := by
    unfold GK
    rw [hK'', IntermediateField.fixingSubgroup_sup]
  rw [e] at hk ⊢
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.1 hk
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem (inv_mem hg) hk2) hg⟩
  have := hN.conj_mem k hk1 g⁻¹
  rwa [inv_inv] at this

end GlobalTheory.CrysInertDescent

namespace GlobalTheory.CrysInertDescent
variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `letI : Algebra ↥(K0 K'') ↥(MaximalUnramifiedExtension l) := (IntermediateField.inclusion (inf_le_right : K0 K'' ≤ MaximalUnramifiedExtension l)).toRingHom.toAlgebra`. Use `haveI : IsScalarTower ↥(K0 K'') ↥(MaximalUnramifiedExtension l) (P.R.B ⊗[ℚ_[l]] T.V) := IsScalarTower.of_algebraMap_smul fun c w => by`. Rewrite using `[← algebraMap_smul P.R.B c w, ← algebraMap_smul P.R.B (algebraMap ↥(K0 K'') ↥(MaximalUnramifiedExtension l) c) w]`. Both sides reduce to the same expression. Use `haveI := (P.PD K'').finK₀`.

Introduce `m hm`. Establish `key` using `L_speiser (G := ↥(GK F)) (L := ↥(K0 K'')) (Ω := ↥(MaximalUnramifiedExtension l)) (M := P.R.B ⊗[ℚ_[l]] T.V) (fun g c => ⟨(g : GQ l) c, kur_stable _ c.2⟩) (fun g => embeddingRestrictMaxUnramified K'' (g : GQ l)) (fun g => (sigQ P T (inclG F g)).toAddMonoidHom) (DcrisK₀ (P.PD K'') ( …`. Express the relevant statement in the definitionally equal form `sigQ P T (inclG F 1) w = w`. Rewrite using `[map_one]`. Conclude with `sigQ_one P T w)`.

Use the proof step `(fun g h w => by`. Express the relevant statement in the definitionally equal form `sigQ P T (inclG F (g * h)) w = sigQ P T (inclG F g) (sigQ P T (inclG F h) w)`. Rewrite using `[map_mul, sigQ_mul]`. Use the proof step `rfl)`. Use the proof step `(fun g c w => by`.

Express the relevant statement in the definitionally equal form `sigQ P T (inclG F g) (c • w) = embeddingRestrictMaxUnramified K'' (g : GQ l) c • sigQ P T (inclG F g) w`. Rewrite using `[← algebraMap_smul P.R.B c w, sigQ_smul, ← algebraMap_smul P.R.B (embeddingRestrictMaxUnramified K'' (g : GQ l) c)]`. Use `congr 1`. Conclude with `P.actQ_Kur _ _ _ rfl)`. Use the proof step `(finite_range_restrictGaloisMaxUnramifiedSubfield K'' F)`.

Use the proof step `(fun g w hw => by`. Express the relevant statement in the definitionally equal form `sigQ P T (inclG F g) w ∈ _`. Rewrite `hw`, the goal using `[mem_res]`. Introduce `k`. Establish `hk'` using `conj_mem K' F K'' hN hK'' (g : GQ l) (k : GQ l) g.2 k.2`.

Set `k' : Gl l` to `(inclG F g)⁻¹ * inclG K'' k * inclG F g`. Establish `e1 : inclG K'' k * inclG F g = inclG F g * k'` using `by show _ = inclG F g * ((inclG F g)⁻¹ * inclG K'' k * inclG F g) group`. Establish `e2 : sigQ P T k' w = w` using `hw ⟨_, hk'⟩`. Rewrite using `[← LinearMap.comp_apply, ← sigQ_mul, e1, sigQ_mul, LinearMap.comp_apply, e2])`. Use the proof step `(fun g hg w hw => by`.

Express the relevant statement in the definitionally equal form `sigQ P T (inclG F g) w = w`. Establish `hfx : ∀ x ∈ K0 K'', (g : GQ l) x = x` using `fun x hx => congrArg Subtype.val (hg ⟨x, hx⟩)`. Take `⟨i, hi, hiF, hih⟩` from `L_lift l K' F K'' hN hK'' (g : GQ l) g.2 hfx`. Set `j : Gl l` to `i⁻¹ * inclG F g`. Establish `e1 : inclG F g = i * j` using `(mul_inv_cancel_left i _).symm`.

Establish `e2 : sigQ P T j w = w`. Rewrite `hw` using `[mem_res]`. Conclude with `hw ⟨_, hih⟩`. Rewrite using `[e1, sigQ_mul, LinearMap.comp_apply, e2]`. Conclude with `hfix i hi hiF w hw)`.

Use `m hm`. Use `Submodule.span_mono ?_ key` and prove the remaining obligations. Introduce and unpack `w ⟨_, hinv⟩`. Rewrite using `[SetLike.mem_coe, mem_res]`. Conclude with `hinv`.
-/
theorem descend (P : LocPrime l) {LL : FinExt l} (T : QLat LL) (K' F K'' : FinExt l) (hN : (GK K').Normal)
    (hK'' : K''.1 = K'.1 ⊔ F.1)
    (hfix : ∀ i : Gl l, i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → (i : GQ l) ∈ GK F →
      ∀ w ∈ DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')), sigQ P T i w = w) :
    ∀ m ∈ DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')),
      m ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (↑(DcrisK₀ (P.PD F) (T.ρ.comp (inclG F))) : Set (P.R.B ⊗[ℚ_[l]] T.V)) := by
  letI : Algebra ↥(K0 K'') ↥(MaximalUnramifiedExtension l) :=
    (IntermediateField.inclusion (inf_le_right : K0 K'' ≤ MaximalUnramifiedExtension l)).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(K0 K'') ↥(MaximalUnramifiedExtension l) (P.R.B ⊗[ℚ_[l]] T.V) :=
    IsScalarTower.of_algebraMap_smul fun c w => by
      rw [← algebraMap_smul P.R.B c w, ← algebraMap_smul P.R.B (algebraMap ↥(K0 K'') ↥(MaximalUnramifiedExtension l) c) w]
      rfl
  haveI := (P.PD K'').finK₀
  intro m hm
  have key := L_speiser (G := ↥(GK F)) (L := ↥(K0 K'')) (Ω := ↥(MaximalUnramifiedExtension l)) (M := P.R.B ⊗[ℚ_[l]] T.V)
    (fun g c => ⟨(g : GQ l) c, kur_stable _ c.2⟩) (fun g => embeddingRestrictMaxUnramified K'' (g : GQ l))
    (fun g => (sigQ P T (inclG F g)).toAddMonoidHom) (DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')))
    (fun g h c => rfl) (fun c => rfl)
    (fun w => by
      change sigQ P T (inclG F 1) w = w
      rw [map_one]
      exact sigQ_one P T w)
    (fun g h w => by
      change sigQ P T (inclG F (g * h)) w = sigQ P T (inclG F g) (sigQ P T (inclG F h) w)
      rw [map_mul, sigQ_mul]
      rfl)
    (fun g c w => by
      change sigQ P T (inclG F g) (c • w) = embeddingRestrictMaxUnramified K'' (g : GQ l) c • sigQ P T (inclG F g) w
      rw [← algebraMap_smul P.R.B c w, sigQ_smul, ← algebraMap_smul P.R.B (embeddingRestrictMaxUnramified K'' (g : GQ l) c)]
      congr 1
      exact P.actQ_Kur _ _ _ rfl)
    (finite_range_restrictGaloisMaxUnramifiedSubfield K'' F)
    (fun g w hw => by
      change sigQ P T (inclG F g) w ∈ _
      rw [mem_res] at hw ⊢
      intro k
      have hk' := conj_mem K' F K'' hN hK'' (g : GQ l) (k : GQ l) g.2 k.2
      let k' : Gl l := (inclG F g)⁻¹ * inclG K'' k * inclG F g
      have e1 : inclG K'' k * inclG F g = inclG F g * k' := by
        show _ = inclG F g * ((inclG F g)⁻¹ * inclG K'' k * inclG F g)
        group
      have e2 : sigQ P T k' w = w := hw ⟨_, hk'⟩
      rw [← LinearMap.comp_apply, ← sigQ_mul, e1, sigQ_mul, LinearMap.comp_apply, e2])
    (fun g hg w hw => by
      change sigQ P T (inclG F g) w = w
      have hfx : ∀ x ∈ K0 K'', (g : GQ l) x = x := fun x hx => congrArg Subtype.val (hg ⟨x, hx⟩)
      obtain ⟨i, hi, hiF, hih⟩ := L_lift l K' F K'' hN hK'' (g : GQ l) g.2 hfx
      let j : Gl l := i⁻¹ * inclG F g
      have e1 : inclG F g = i * j := (mul_inv_cancel_left i _).symm
      have e2 : sigQ P T j w = w := by
        rw [mem_res] at hw
        exact hw ⟨_, hih⟩
      rw [e1, sigQ_mul, LinearMap.comp_apply, e2]
      exact hfix i hi hiF w hw)
    m hm
  refine Submodule.span_mono ?_ key
  rintro w ⟨_, hinv⟩
  rw [SetLike.mem_coe, mem_res]
  exact hinv

end GlobalTheory.CrysInertDescent

namespace GlobalTheory.CrysInertDescent

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `_ l _ LL Pl AI hstd K' F hN T hc`. Establish `hT : LocTied l Pl AI` using `hstd.some`. Use `haveI := K'.2`. Use `haveI := F.2`. Take `⟨K'', hK''⟩ : ∃ K'' : FinExt l, K''.1 = K'.1 ⊔ F.1` from `⟨⟨_, inferInstance⟩, rfl⟩`.

Establish `hK' : K'.1 ≤ K''.1` using `hK'' ▸ le_sup_left`. Establish `hF : F.1 ≤ K''.1` using `hK'' ▸ le_sup_right`. Express the relevant statement in the definitionally equal form `IsCrys (Pl.PD K') (T.ρ.comp (inclG K')) at hc`. Establish `hc'' : IsCrys (Pl.PD K'') (T.ρ.comp (inclG K''))` using `TiedRestrict.isCrys_restrict hK' (T.ρ.comp (inclG K')) hT hc`. Establish `hspan` using `L_span l Pl AI hstd LL T K' K'' hK' hc`.

Establish `hfixK : ∀ i : Gl l, i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → (∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ i x = x) → ∀ w ∈ DcrisK₀ (Pl.PD K'') (T.ρ.comp (inclG K'')), sigQ Pl T i w = w`. Introduce `i hi hfix w hw`. Use `eq_on_span (R := ↥(K0 K'')) (sigQ Pl T i).toAddMonoidHom (AddMonoidHom.id _) (fun c w => sigQ_smul_K0 Pl T K'' i hi c w) (fun c w => rfl) _ ?_ w (hspan hw)` and prove the remaining obligations. Introduce `u hu`. Apply `(TensorProduct.comm ℚ_[l] Pl.R.B T.V).injective` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `TensorProduct.comm ℚ_[l] Pl.R.B T.V (sigQ Pl T i u) = TensorProduct.comm ℚ_[l] Pl.R.B T.V u`. Rewrite using `[comm_sigQ]`. Conclude with `hfix _ hu`. Establish `hres : ∀ (K : FinExt l) (w : Pl.R.B ⊗[ℚ_[l]] T.V), w ∈ DcrisK₀ (Pl.PD K) (T.ρ.comp (inclG K)) ↔ ∀ k : ↥(GK K), sigQ Pl T (inclG K k) w = w`. Introduce `K w`.

Rewrite using `[mem_DcrisK₀]`. Conclude with `forall_congr' fun k => by rw [sig_res]`. Prove the components needed by the constructor for the conclusion. Introduce `hyp`. Express the relevant statement in the definitionally equal form `IsCrys (Pl.PD F) (T.ρ.comp (inclG F))`.

Conclude with `L_dim l Pl AI hstd LL T F K'' hc'' (descend Pl T K' F K'' hN hK'' fun i hi hiF => hfixK i hi (hyp i hi hiF))`. Introduce `g hg p hp show ∀ x : T.V ⊗[ℚ_[l]] Pl.R.B, x ∈ Dcris (Pl.PD F) (T.ρ.comp (inclG F)) → (Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p) x = 0`. Introduce `x hx`. Establish `hw : (TensorProduct.comm ℚ_[l] Pl.R.B T.V).symm x ∈ DcrisK₀ (Pl.PD K'') (T.ρ.comp (inclG K''))`. Establish `h1 : (TensorProduct.comm ℚ_[l] Pl.R.B T.V).symm x ∈ DcrisK₀ (Pl.PD F) (T.ρ.comp (inclG F))`.

Express the relevant statement in the definitionally equal form `TensorProduct.comm ℚ_[l] Pl.R.B T.V ((TensorProduct.comm ℚ_[l] Pl.R.B T.V).symm x) ∈ Dcris (Pl.PD F) (T.ρ.comp (inclG F))`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `hx`. Rewrite `h1`, the goal using `[hres]`. Introduce `k`.

Conclude with `h1 ⟨k.1, GK_le hF k.2⟩`. Establish `h2` using `kill_span Pl T K' K'' _ (fun c => commute_aeval_mulVB Pl T K'' g hg c p) hp _ (hspan hw)`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' F : FinExt l), (GK K').Normal → ∀ T : QLat LL, IsCrys (Pl.PD K') (resF T K').ρ → ((∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), (g : GQ l) ∈ GK F → ∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → IsCrys (Pl.PD F) (resF T F).ρ) ∧ ∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∀ p : Polynomial ↥LL.1, (∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p x = 0) → ∀ x ∈ Dcris (Pl.PD F) (resF T F).ρ, Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p x = 0 := by
  intro _ l _ LL Pl AI hstd K' F hN T hc
  have hT : LocTied l Pl AI := hstd.some
  haveI := K'.2
  haveI := F.2
  obtain ⟨K'', hK''⟩ : ∃ K'' : FinExt l, K''.1 = K'.1 ⊔ F.1 := ⟨⟨_, inferInstance⟩, rfl⟩
  have hK' : K'.1 ≤ K''.1 := hK'' ▸ le_sup_left
  have hF : F.1 ≤ K''.1 := hK'' ▸ le_sup_right
  change IsCrys (Pl.PD K') (T.ρ.comp (inclG K')) at hc
  have hc'' : IsCrys (Pl.PD K'') (T.ρ.comp (inclG K'')) :=
    TiedRestrict.isCrys_restrict hK' (T.ρ.comp (inclG K')) hT hc
  have hspan := L_span l Pl AI hstd LL T K' K'' hK' hc
  have hfixK : ∀ i : Gl l, i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) →
      (∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ i x = x) →
      ∀ w ∈ DcrisK₀ (Pl.PD K'') (T.ρ.comp (inclG K'')), sigQ Pl T i w = w := by
    intro i hi hfix w hw
    refine eq_on_span (R := ↥(K0 K'')) (sigQ Pl T i).toAddMonoidHom (AddMonoidHom.id _)
      (fun c w => sigQ_smul_K0 Pl T K'' i hi c w) (fun c w => rfl) _ ?_ w (hspan hw)
    intro u hu
    apply (TensorProduct.comm ℚ_[l] Pl.R.B T.V).injective
    change TensorProduct.comm ℚ_[l] Pl.R.B T.V (sigQ Pl T i u) = TensorProduct.comm ℚ_[l] Pl.R.B T.V u
    rw [comm_sigQ]
    exact hfix _ hu
  have hres : ∀ (K : FinExt l) (w : Pl.R.B ⊗[ℚ_[l]] T.V),
      w ∈ DcrisK₀ (Pl.PD K) (T.ρ.comp (inclG K)) ↔ ∀ k : ↥(GK K), sigQ Pl T (inclG K k) w = w := by
    intro K w
    rw [mem_DcrisK₀]
    exact forall_congr' fun k => by rw [sig_res]
  constructor
  · intro hyp
    change IsCrys (Pl.PD F) (T.ρ.comp (inclG F))
    exact L_dim l Pl AI hstd LL T F K'' hc'' (descend Pl T K' F K'' hN hK'' fun i hi hiF => hfixK i hi (hyp i hi hiF))
  · intro g hg p hp
    show ∀ x : T.V ⊗[ℚ_[l]] Pl.R.B, x ∈ Dcris (Pl.PD F) (T.ρ.comp (inclG F)) →
      (Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p) x = 0
    intro x hx
    have hw : (TensorProduct.comm ℚ_[l] Pl.R.B T.V).symm x ∈ DcrisK₀ (Pl.PD K'') (T.ρ.comp (inclG K'')) := by
      have h1 : (TensorProduct.comm ℚ_[l] Pl.R.B T.V).symm x ∈ DcrisK₀ (Pl.PD F) (T.ρ.comp (inclG F)) := by
        change TensorProduct.comm ℚ_[l] Pl.R.B T.V ((TensorProduct.comm ℚ_[l] Pl.R.B T.V).symm x) ∈
          Dcris (Pl.PD F) (T.ρ.comp (inclG F))
        rw [LinearEquiv.apply_symm_apply]
        exact hx
      rw [hres] at h1 ⊢
      intro k
      exact h1 ⟨k.1, GK_le hF k.2⟩
    have h2 := kill_span Pl T K' K'' _ (fun c => commute_aeval_mulVB Pl T K'' g hg c p) hp _ (hspan hw)
    rwa [LinearEquiv.apply_symm_apply] at h2

end GlobalTheory.CrysInertDescent
