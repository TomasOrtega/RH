import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmulMemFilV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFactorOfIdempotentSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAutLeOneIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSymbolBasis

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TauFrame

/- English proof (translation)
Use `haveI := Algebra.FormallyUnramified.of_isSeparable F K`. Take `⟨n, α, β, h⟩` from `TensorProduct.exists_sum_tmul_eq (Algebra.FormallyUnramified.elem F K)`. Use `⟨n, α, β, fun κ => ?_, ?_⟩` and prove the remaining obligations. Use `Algebra.FormallyUnramified.one_tmul_mul_elem (R := F) (S := K) κ` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this`. Conclude with `this.symm`. Use `Algebra.FormallyUnramified.lmul_elem (R := F) (S := K)` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `using this`.
-/
theorem exists_sep_elem (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Algebra.IsSeparable F K] :
    ∃ (n : ℕ) (α β : Fin n → K),
      (∀ κ : K, ∑ j, (κ * α j) ⊗ₜ[F] β j = ∑ j, α j ⊗ₜ[F] (κ * β j)) ∧ ∑ j, α j * β j = 1 := by
  haveI := Algebra.FormallyUnramified.of_isSeparable F K
  obtain ⟨n, α, β, h⟩ := TensorProduct.exists_sum_tmul_eq (Algebra.FormallyUnramified.elem F K)
  refine ⟨n, α, β, fun κ => ?_, ?_⟩
  · have := Algebra.FormallyUnramified.one_tmul_mul_elem (R := F) (S := K) κ
    rw [h] at this
    simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
    exact this.symm
  · have := Algebra.FormallyUnramified.lmul_elem (R := F) (S := K)
    rw [h] at this
    simpa using this

/- English proof (translation)
Use `set E := ∑ i, j (β i) • B (α i) with hE`. Set `φ : K ⊗[F] K →ₗ[F] R` to `TensorProduct.lift (LinearMap.mk₂ F (fun a c => j c • B a) (fun a a' c => by simp [smul_add]) (fun r a c => by rw [map_smul, smul_comm]) (fun a c c' => by simp [add_smul]) (fun r a c => by rw [map_smul, smul_assoc]))`. Establish `hφ : ∀ a c, φ (a ⊗ₜ c) = j c • B a` using `fun a c => rfl`. Establish `key : ∀ κ, B κ * E = j κ • E`. Introduce `κ`.

Use `congrArg φ (h1 κ)` as an intermediate fact. Simplify using `only [map_sum, hφ, map_mul] at this`. Rewrite using `[hE, Finset.mul_sum, Finset.smul_sum]`. Simplify using `only [mul_smul_comm, smul_smul]`. Conclude with `this`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [smul_mul_assoc, hE]`. Use `_ = j (∑ i, α i * β i) • E := by`. Simplify using `only [key, smul_smul, map_sum, map_mul, Finset.sum_smul, mul_comm]`. Use `_ = E := by rw [h2, map_one, one_smul]`.
-/
theorem sep_idem {F K C R : Type} [Field F] [Field K] [Algebra F K] [CommRing C] [Ring R]
    [Algebra F C] [Algebra C R] [Algebra F R] [IsScalarTower F C R] (B : K →ₐ[F] R) (j : K →ₐ[F] C)
    {n : ℕ} (α β : Fin n → K)
    (h1 : ∀ κ : K, ∑ i, (κ * α i) ⊗ₜ[F] β i = ∑ i, α i ⊗ₜ[F] (κ * β i)) (h2 : ∑ i, α i * β i = 1) :
    (∑ i, j (β i) • B (α i)) * (∑ i, j (β i) • B (α i)) = ∑ i, j (β i) • B (α i) := by
  set E := ∑ i, j (β i) • B (α i) with hE
  let φ : K ⊗[F] K →ₗ[F] R := TensorProduct.lift (LinearMap.mk₂ F (fun a c => j c • B a)
    (fun a a' c => by simp [smul_add]) (fun r a c => by rw [map_smul, smul_comm])
    (fun a c c' => by simp [add_smul]) (fun r a c => by rw [map_smul, smul_assoc]))
  have hφ : ∀ a c, φ (a ⊗ₜ c) = j c • B a := fun a c => rfl
  have key : ∀ κ, B κ * E = j κ • E := by
    intro κ
    have := congrArg φ (h1 κ)
    simp only [map_sum, hφ, map_mul] at this
    rw [hE, Finset.mul_sum, Finset.smul_sum]
    simp only [mul_smul_comm, smul_smul]
    exact this
  calc E * E = ∑ i, j (β i) • (B (α i) * E) := by
        conv_lhs => rw [hE, Finset.sum_mul]
        simp only [smul_mul_assoc, hE]
    _ = j (∑ i, α i * β i) • E := by
        simp only [key, smul_smul, map_sum, map_mul, Finset.sum_smul, mul_comm]
    _ = E := by rw [h2, map_one, one_smul]

def mulMat {F LL V : Type} (C : Type) [Field F] [Field LL] [Algebra F LL] [AddCommGroup V]
    [Module LL V] [Module F V] [IsScalarTower F LL V] [CommRing C] [Algebra F C] {d : ℕ}
    (b : Module.Basis (Fin d) F V) : LL →ₐ[F] Matrix (Fin d) (Fin d) C :=
  ((Algebra.ofId F C).mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toAlgHom).comp
    (Algebra.lsmul F F V)

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[mulMat, LinearMap.toMatrixAlgEquiv_apply, Algebra.ofId_apply]`.
-/
theorem mulMat_eq {F LL V : Type} (C : Type) [Field F] [Field LL] [Algebra F LL] [AddCommGroup V]
    [Module LL V] [Module F V] [IsScalarTower F LL V] [CommRing C] [Algebra F C] {d : ℕ}
    (b : Module.Basis (Fin d) F V) (a : LL) :
    mulMat C b a = Matrix.of fun i k => algebraMap F C (b.repr (a • b k) i) := by
  ext i k
  simp [mulMat, LinearMap.toMatrixAlgEquiv_apply, Algebra.ofId_apply]

/- English proof (translation)
Establish `h : N = ((Algebra.ofId F C).mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toAlgHom) (f.restrictScalars F)`. Use extensionality with `i k`. Simplify using `[hN, LinearMap.toMatrixAlgEquiv_apply, Algebra.ofId_apply]`. Rewrite using `[h, mulMat, AlgHom.comp_apply, ← map_mul, ← map_mul]`. Use `congr 1`.

Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem mulMat_comm {F LL V : Type} (C : Type) [Field F] [Field LL] [Algebra F LL] [AddCommGroup V]
    [Module LL V] [Module F V] [IsScalarTower F LL V] [CommRing C] [Algebra F C] {d : ℕ}
    (b : Module.Basis (Fin d) F V) (a : LL) (f : V →ₗ[LL] V) (N : Matrix (Fin d) (Fin d) C)
    (hN : ∀ i k, N i k = algebraMap F C (b.repr (f (b k)) i)) :
    mulMat C b a * N = N * mulMat C b a := by
  have h : N = ((Algebra.ofId F C).mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toAlgHom)
      (f.restrictScalars F) := by
    ext i k
    simp [hN, LinearMap.toMatrixAlgEquiv_apply, Algebra.ofId_apply]
  rw [h, mulMat, AlgHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  ext v
  simp

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Set `φ` to `AlgEquiv.ofBijective (τ.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)`. Use `⟨φ.symm, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.symm_apply_eq]`. Conclude with `(τ.liftNormal_commutes (Om l) x).symm`.
-/
theorem exists_undo (K LL : FinExt l) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    ∃ ι : GQ l, ∀ x : ↥K.1, ι (τ x : Om l) = (x : Om l) := by
  let φ := AlgEquiv.ofBijective (τ.liftNormal (Om l))
    (Algebra.IsAlgebraic.algHom_bijective _)
  refine ⟨φ.symm, fun x => ?_⟩
  rw [AlgEquiv.symm_apply_eq]
  exact (τ.liftNormal_commutes (Om l) x).symm

/- English proof (translation)
Use `sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _` and prove the remaining obligations. Take `⟨n, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Express the relevant statement in the definitionally equal form `x ^ (l ^ (s + n)) = 1`. Rewrite using `[pow_add, pow_mul, show x ^ l ^ s = 1 from hx, one_pow]`.
-/
theorem Ks_mono (K : FinExt l) {s m : ℕ} (hm : s ≤ m) : Ks K s ≤ Ks K m := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  change x ^ (l ^ (s + n)) = 1
  rw [pow_add, pow_mul, show x ^ l ^ s = 1 from hx, one_pow]

/- English proof (translation)
Assemble the required witnesses or components as `⟨algebraMap ℚ_[l] (Om l) c, F.algebraMap_mem c, (IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) c).symm⟩`.
-/
theorem rat_mem_subC (F : IntermediateField ℚ_[l] (Om l)) (c : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) c ∈ subC F :=
  ⟨algebraMap ℚ_[l] (Om l) c, F.algebraMap_mem c,
    (IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) c).symm⟩

/- English proof (translation)
Set `AK : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)` to `{ V := T.V, ρ := T.ρ, cont := T.cont }`. Establish `hK : Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ)` using `(h7K _ _ (GlobalTheory.LocalIntegers.goodO_integers l LL) AK).2.1.1`. Establish `hanti : ∀ a, FilV (P.PD K) (LL` using `↥LL.1) (V := T.V) (a + 1) ≤ FilV (P.PD K) a := by`. Take `⟨Φ, h1, -⟩` from `GlobalTheory.exists_coord_tensor_dR (P.PD K) T.ρ b`. Introduce `a z hz`.

Conclude with `(h1 a z).2 fun i => (P.PD K).Fil_anti a ((h1 _ z).1 hz i)`. Establish `hE : Module.Finite ↥LL.1 ↥(DdRE (P.PD K) T.ρ τ)` using `Module.Finite.of_injective (Submodule.inclusion (inf_le_left : DdRE (P.PD K) T.ρ τ ≤ _)) (Submodule.inclusion_injective _)`. Conclude with `GlobalTheory.finite_jumps_inf_filtration _ _ (DdRE (P.PD K) T.ρ τ) (fun a => FilV (P.PD K) a) hE hanti`.
-/
theorem finite_jumps (P : LocPrime l) (K LL : FinExt l) (h7K : fontCore (P.PD K))
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[l] T.V) : {u | IsJumpV (P.PD K) T.ρ τ u}.Finite := by
  let AK : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := T.V, ρ := T.ρ, cont := T.cont }
  have hK : Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ) :=
    (h7K _ _ (GlobalTheory.LocalIntegers.goodO_integers l LL) AK).2.1.1
  have hanti : ∀ a, FilV (P.PD K) (LL := ↥LL.1) (V := T.V) (a + 1) ≤ FilV (P.PD K) a := by
    obtain ⟨Φ, h1, -⟩ := GlobalTheory.exists_coord_tensor_dR (P.PD K) T.ρ b
    intro a z hz
    exact (h1 a z).2 fun i => (P.PD K).Fil_anti a ((h1 _ z).1 hz i)
  have hE : Module.Finite ↥LL.1 ↥(DdRE (P.PD K) T.ρ τ) :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : DdRE (P.PD K) T.ρ τ ≤ _))
      (Submodule.inclusion_injective _)
  exact GlobalTheory.finite_jumps_inf_filtration _ _ (DdRE (P.PD K) T.ρ τ) (fun a => FilV (P.PD K) a) hE hanti

/- English proof (translation)
Use `haveI := LL.2`. Establish `ha : IsAlgebraic ℤ_[l] a` using `(IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨c, hc, hint⟩` from `ha.exists_integral_multiple`. Establish `hc' : (c : ℚ_[l]) ≠ 0` using `fun h0 => hc (Subtype.ext h0)`. Establish `e : a = (c : ℚ_[l])⁻¹ • (c • a)`.

Express the relevant statement in the definitionally equal form `a = (c : ℚ_[l])⁻¹ • ((c : ℚ_[l]) • a)`. Rewrite using `[inv_smul_smul₀ hc']`. Establish `h1` using `h ⟨c • a, hint⟩ i j`. Rewrite using `[e, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Algebra.smul_def]`. Conclude with `mul_mem (rat_mem_subC F _) h1`.
-/
theorem conj_mem_subC (LL : FinExt l) (F : IntermediateField ℚ_[l] (Om l)) {d : ℕ}
    (B : ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin d) (Fin d) (PadicComplex l))
    (X Y : Matrix (Fin d) (Fin d) (PadicComplex l))
    (h : ∀ (a : ↥(OL LL)) i j, (X * B a * Y) i j ∈ subC F) (a : ↥LL.1) (i j : Fin d) :
    (X * B a * Y) i j ∈ subC F := by
  haveI := LL.2
  have ha : IsAlgebraic ℤ_[l] a :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨c, hc, hint⟩ := ha.exists_integral_multiple
  have hc' : (c : ℚ_[l]) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have e : a = (c : ℚ_[l])⁻¹ • (c • a) := by
    change a = (c : ℚ_[l])⁻¹ • ((c : ℚ_[l]) • a)
    rw [inv_smul_smul₀ hc']
  have h1 := h ⟨c • a, hint⟩ i j
  rw [e, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Algebra.smul_def]
  exact mul_mem (rat_mem_subC F _) h1

def toC (K : FinExt l) : ↥K.1 →ₐ[ℚ_[l]] PadicComplex l :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) (PadicComplex l)).comp K.1.val

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toC_apply (K : FinExt l) (x : ↥K.1) : toC K x = ((x : Om l) : PadicComplex l) := rfl

/- English proof (translation)
Use `haveI := K.2`. Establish `ha : IsActC AI.actC` using `⟨AI.actC_ext, AI.actC_norm⟩`. Take `⟨b, hbM, hbA, hbT⟩` from `exists_ratBasis_of_isMat l K LL T d M A hM`. Take `⟨n, α, β, h1, h2⟩` from `exists_sep_elem ℚ_[l] ↥K.1`. Establish `hfin` using `finite_jumps P K LL h7K T τ b`.

Take `⟨B, hB⟩ : ∃ B : ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin d) (Fin d) (PadicComplex l), B = mulMat (PadicComplex l) b` from `⟨_, rfl⟩`. Establish `hBe : ∀ a, B a = Matrix.of fun i k => algebraMap ℚ_[l] (PadicComplex l) (b.repr (a • b k) i)` using `fun a => by rw [hB, mulMat_eq]`. Take `⟨E, hE⟩ : ∃ E : Matrix (Fin d) (Fin d) (PadicComplex l), E = ∑ j, toC K (β j) • B (τ (α j))` from `⟨_, rfl⟩`. Establish `hEE : E * E = E`. Rewrite using `[hE]`.

Conclude with `sep_idem (B.comp τ) (toC K) α β h1 h2`. Establish `hG : Gj K m ≤ GK K` using `IntermediateField.fixingSubgroup_le hKm`. Establish `hβ : ∀ x : ↥K.1, toC K x ∈ subC (Ks K m)` using `fun x => ⟨x, hKm x.2, rfl⟩`. Establish `hEM : ∀ σ ∈ Gj K m, E * M σ = M σ * E`. Introduce `σ hσ`.

Rewrite using `[hE, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, hB, mulMat_comm _ b _ (T.ρ ⟨σ, hG hσ⟩) (M σ) (hbM ⟨σ, hG hσ⟩)]`. Establish `hEσ : ∀ σ ∈ Gj K m, E.map (AI.actC σ) = E`. Introduce `σ hσ`.

Use extensionality with `i k`. Use `act_fix ha hσ ?_` and prove the remaining obligations. Rewrite using `[hE, Matrix.sum_apply]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, hBe]`.

Conclude with `mul_mem (hβ _) (rat_mem_subC _ _)`. Establish `hEF : ∀ i k, (Dm⁻¹ * E * Dm) i k ∈ subC (Ks K m)`. Introduce `i k`. Rewrite using `[hE, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]`. Use `mul_mem (hβ _) (conj_mem_subC LL _ B _ _ (fun a i k => ?_) _ _ _)` and prove the remaining obligations. Establish `: B a = A a`. Rewrite using `[hBe]`. Use extensionality with `i k`.

Conclude with `(hbA a i k).symm`. Rewrite using `[this]`. Conclude with `(hA a i k).1`. Establish `hDD : Dm * Dm⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hD.1`. Take `⟨r, R, S, hR, hS, hRS, hRe, heSR⟩` from `GlobalTheory.exists_integral_factor_of_idempotent_subfield (PadicComplex l) (subC (Ks K m)) d (Dm⁻¹ * E * Dm) hEF (by`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hDD, Matrix.mul_one, hEE])`. Establish `ht : IsUnit (P.ιB P.tB)`. Rewrite using `[← P.period_datum_t_eq K]`.

Conclude with `(P.PD K).t_unit.map _`. Take `⟨u, y, hy0, hyD, hli, hfix⟩` from `GlobalTheory.DeRhamSymbolBasis.exists_symbol_basis l P AI Θ K LL T hDR d b M hbM ht.unit ht.unit_spec`. Take `⟨c1, c2, c3, c4, c5, Q, hQ⟩` from `frame_of_idem AI.actC P.χQ ha K m d r M U0 Dm E g hD hEM hEσ hEF R S hR hS hRS hRe heSR (fun k i => Θ.θ (y k i)) u hli (fun σ hσ k => hfix σ (hG hσ) k) (hfin.toFinset : Set ℤ) (by`. Introduce `k hk`. Assume the negation of the conclusion as `hJ`.

Apply `hk` to reduce the goal to its premises. Use `GlobalTheory.EmbeddingJump.proj_eq_zero l P AI Θ K LL T τ d b n α β h1 ht.unit ht.unit_spec (u k) (y k) (hy0 k) (hyD k) (by simpa using hJ)` as an intermediate fact. Rewrite using `[hE]`. Simplify using `only [hBe, toC_apply]`. Conclude with `this)`.

Use `⟨r, R * Dm⁻¹, _, g, hfin.toFinset, fun u hu => by simpa using hu, hfin, c1, c2, c3, c4, c5, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨x, hx, hxz⟩`. Take `⟨ι, hι⟩` from `exists_undo K LL τ`. Take `⟨ρ, Pr, p1, p2, p3⟩` from `GlobalTheory.EigenCoord.exists_matrix l K LL T d b hbT ι`. Establish `hPE : Pr * E = Pr`.

Rewrite using `[hE, Matrix.mul_sum]`. Establish `: ∀ j, Pr * (toC K (β j) • B (τ (α j))) = toC K (α j * β j) • Pr`. Introduce `j`. Rewrite using `[Matrix.mul_smul, hBe, p2, hι, smul_smul, map_mul, mul_comm, toC_apply K (α j)]`. Simplify using `only [this]`.

Rewrite using `[← Finset.sum_smul, ← map_sum, h2, map_one, one_smul]`. Apply `p3` to reduce the goal to its premises. Establish `: Pr.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (z a)) = Pr.mulVec x`. Establish `h3 : ∀ v, Pr.mulVec v = Pr.mulVec (Q.mulVec ((R * Dm⁻¹).mulVec v))` using `fun v => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, hPE]`.

Rewrite using `[h3 x, h3, hxz]`. Rewrite using `[this]`. Conclude with `norm_mulVec_le _ _ p1 hx`.
-/
theorem frame_of_dec (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K LL : FinExt l)
    (m : ℕ) (hKm : K.1 ≤ Ks K m) (h7K : fontCore (P.PD K))
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hDR : IsDR (P.PD K) T.ρ) {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T M A)
    (Dm : Matrix (Fin d) (Fin d) (PadicComplex l))
    (U0 : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l)
    (hD : IsDec AI.actC P.χQ K m M Dm U0 g)
    (hA : ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K m)) :
    ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l))
      (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ),
      (∀ u, u ∈ J → IsJumpV (P.PD K) T.ρ τ u) ∧ {u | IsJumpV (P.PD K) T.ρ τ u}.Finite ∧
      Frame P.χQ K m U g ∧ HTBasis AI.actC P.χQ (Gj K m) U (J : Set ℤ) ∧
      (∀ σ ∈ Gj K m, Pm * M σ = U σ * Pm.map (AI.actC σ)) ∧
      ball l r ⊆ Pm.mulVec '' ball l d ∧
      (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧
      ∀ y : Fin d → ℚ_[l],
        Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d →
        ∀ a, ‖y a‖ ≤ 1 := by
  haveI := K.2
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨b, hbM, hbA, hbT⟩ := exists_ratBasis_of_isMat l K LL T d M A hM
  obtain ⟨n, α, β, h1, h2⟩ := exists_sep_elem ℚ_[l] ↥K.1
  have hfin := finite_jumps P K LL h7K T τ b
  obtain ⟨B, hB⟩ : ∃ B : ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin d) (Fin d) (PadicComplex l),
      B = mulMat (PadicComplex l) b := ⟨_, rfl⟩
  have hBe : ∀ a, B a = Matrix.of fun i k =>
      algebraMap ℚ_[l] (PadicComplex l) (b.repr (a • b k) i) := fun a => by rw [hB, mulMat_eq]
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin d) (Fin d) (PadicComplex l),
      E = ∑ j, toC K (β j) • B (τ (α j)) := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hE]
    exact sep_idem (B.comp τ) (toC K) α β h1 h2
  have hG : Gj K m ≤ GK K := IntermediateField.fixingSubgroup_le hKm
  have hβ : ∀ x : ↥K.1, toC K x ∈ subC (Ks K m) := fun x => ⟨x, hKm x.2, rfl⟩
  have hEM : ∀ σ ∈ Gj K m, E * M σ = M σ * E := by
    intro σ hσ
    rw [hE, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hB,
      mulMat_comm _ b _ (T.ρ ⟨σ, hG hσ⟩) (M σ) (hbM ⟨σ, hG hσ⟩)]
  have hEσ : ∀ σ ∈ Gj K m, E.map (AI.actC σ) = E := by
    intro σ hσ
    ext i k
    refine act_fix ha hσ ?_
    rw [hE, Matrix.sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, hBe]
    exact mul_mem (hβ _) (rat_mem_subC _ _)
  have hEF : ∀ i k, (Dm⁻¹ * E * Dm) i k ∈ subC (Ks K m) := by
    intro i k
    rw [hE, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    refine mul_mem (hβ _) (conj_mem_subC LL _ B _ _ (fun a i k => ?_) _ _ _)
    have : B a = A a := by
      rw [hBe]
      ext i k
      exact (hbA a i k).symm
    rw [this]
    exact (hA a i k).1
  have hDD : Dm * Dm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD.1
  obtain ⟨r, R, S, hR, hS, hRS, hRe, heSR⟩ := GlobalTheory.exists_integral_factor_of_idempotent_subfield
    (PadicComplex l) (subC (Ks K m)) d (Dm⁻¹ * E * Dm) hEF (by
      calc Dm⁻¹ * E * Dm * (Dm⁻¹ * E * Dm) = Dm⁻¹ * (E * (Dm * Dm⁻¹) * E) * Dm := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hDD, Matrix.mul_one, hEE])
  have ht : IsUnit (P.ιB P.tB) := by
    rw [← P.period_datum_t_eq K]
    exact (P.PD K).t_unit.map _
  obtain ⟨u, y, hy0, hyD, hli, hfix⟩ := GlobalTheory.DeRhamSymbolBasis.exists_symbol_basis l P AI Θ K LL T
    hDR d b M hbM ht.unit ht.unit_spec
  obtain ⟨c1, c2, c3, c4, c5, Q, hQ⟩ := frame_of_idem AI.actC P.χQ ha K m d r M U0 Dm E g hD hEM
    hEσ hEF R S hR hS hRS hRe heSR (fun k i => Θ.θ (y k i)) u hli
    (fun σ hσ k => hfix σ (hG hσ) k) (hfin.toFinset : Set ℤ) (by
      intro k hk
      by_contra hJ
      apply hk
      have := GlobalTheory.EmbeddingJump.proj_eq_zero l P AI Θ K LL T τ d b n α β h1 ht.unit ht.unit_spec
        (u k) (y k) (hy0 k) (hyD k) (by simpa using hJ)
      rw [hE]
      simp only [hBe, toC_apply]
      exact this)
  refine ⟨r, R * Dm⁻¹, _, g, hfin.toFinset, fun u hu => by simpa using hu, hfin, c1, c2, c3, c4, c5,
    ?_⟩
  rintro z ⟨x, hx, hxz⟩
  obtain ⟨ι, hι⟩ := exists_undo K LL τ
  obtain ⟨ρ, Pr, p1, p2, p3⟩ := GlobalTheory.EigenCoord.exists_matrix l K LL T d b hbT ι
  have hPE : Pr * E = Pr := by
    rw [hE, Matrix.mul_sum]
    have : ∀ j, Pr * (toC K (β j) • B (τ (α j))) = toC K (α j * β j) • Pr := by
      intro j
      rw [Matrix.mul_smul, hBe, p2, hι, smul_smul, map_mul, mul_comm, toC_apply K (α j)]
    simp only [this]
    rw [← Finset.sum_smul, ← map_sum, h2, map_one, one_smul]
  apply p3
  have : Pr.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (z a)) = Pr.mulVec x := by
    have h3 : ∀ v, Pr.mulVec v = Pr.mulVec (Q.mulVec ((R * Dm⁻¹).mulVec v)) := fun v => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, hPE]
    rw [h3 x, h3, hxz]
  rw [this]
  exact norm_mulVec_le _ _ p1 hx

/- English proof (translation)
Introduce `D HW F h7 l _ K s LL h S E T M0 h0 τ hW d M A hM`. Take `⟨Θ⟩` from `GlobalTheory.ThetaTie.nonempty_thetaL D l`. Take `⟨Dm, U, g, hD, hA⟩` from `GlobalTheory.Cyc.Decomp.exists_decompletion D HW F l K s LL h T M0 h0 hW d M A hM`. Establish `hKm : K.1 ≤ Ks K (mN l s (M0 + h0))` using `h.2.2.1.trans (Ks_mono K (by unfold mN; omega))`. Conclude with `frame_of_dec (D.loc l) (D.locA l) Θ K LL _ hKm (h7 l K) T τ (GlobalTheory.Cyc.CrysDeRham.isDR_of_isCrysOn D HW h7 l K s LL h T hW.1) M A hM Dm U g hD hA`.
-/
theorem exists_tau_frame : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (τ : S.K →ₐ[S.Qp] S.LL), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ), (∀ u, u ∈ J → IsJumpV S.PD T.ρ τ u) ∧ {u | IsJumpV S.PD T.ρ τ u}.Finite ∧ Frame (D.loc l).χQ K (mN l s (M0 + h0)) U g ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K (mN l s (M0 + h0))) U (J : Set ℤ) ∧ (∀ σ ∈ Gj K (mN l s (M0 + h0)), Pm * M σ = U σ * Pm.map ((D.locA l).actC σ)) ∧ ball l r ⊆ Pm.mulVec '' ball l d ∧ (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧ ∀ y : Fin d → ℚ_[l], Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d → ∀ a, ‖y a‖ ≤ 1 := by
  intro D HW F h7 l _ K s LL h S E T M0 h0 τ hW d M A hM
  obtain ⟨Θ⟩ := GlobalTheory.ThetaTie.nonempty_thetaL D l
  obtain ⟨Dm, U, g, hD, hA⟩ := GlobalTheory.Cyc.Decomp.exists_decompletion D HW F l K s LL h T M0 h0 hW d M A hM
  have hKm : K.1 ≤ Ks K (mN l s (M0 + h0)) :=
    h.2.2.1.trans (Ks_mono K (by unfold mN; omega))
  exact frame_of_dec (D.loc l) (D.locA l) Θ K LL _ hKm (h7 l K) T τ
    (GlobalTheory.Cyc.CrysDeRham.isDR_of_isCrysOn D HW h7 l K s LL h T hW.1) M A hM Dm U g hD hA

end GlobalTheory.TauFrame
