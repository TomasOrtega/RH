import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeCoeffTensorAinfOfFrobeniusEqMatrixMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKExp

section Int

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O]

/- English proof (translation)
The claim follows from `GlobalTheory.T.mem_range_coeffTensorAinf_of_frobenius_eq_matrix_mul l O v Y h`.
-/
theorem integral_of_frob {n : Type} [Fintype n] (v : n → OW l O) (Y : Matrix n n (OA l O))
    (h : ∀ i, frobOW l O (v i) = (Y.map (inclO l O) *ᵥ v) i) : ∀ i, v i ∈ (inclO l O).range :=
  GlobalTheory.T.mem_range_coeffTensorAinf_of_frobenius_eq_matrix_mul l O v Y h

/- English proof (translation)
The claim follows from `integral_of_frob v Yᵀ fun i => by rw [h i, Matrix.transpose_map, Matrix.mulVec_transpose]`.
-/
theorem integral_of_frob_row {n : Type} [Fintype n] (v : n → OW l O) (Y : Matrix n n (OA l O))
    (h : ∀ i, frobOW l O (v i) = (v ᵥ* Y.map (inclO l O)) i) : ∀ i, v i ∈ (inclO l O).range :=
  integral_of_frob v Yᵀ fun i => by rw [h i, Matrix.transpose_map, Matrix.mulVec_transpose]

variable (l O) in

def jA : Ainf l →+* OW l O :=
  (inclO l O).toRingHom.comp (Algebra.TensorProduct.includeRight : Ainf l →ₐ[ℤ_[l]] OA l O).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jA_apply (x : Ainf l) : jA l O x = inclO l O (1 ⊗ₜ x) := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨1 ⊗ₜ x, rfl⟩`.
-/
theorem jA_mem (x : Ainf l) : jA l O x ∈ (inclO l O).range := ⟨1 ⊗ₜ x, rfl⟩

/- English proof (translation)
Rewrite using `[jA_apply, frobOW_inclO, frobOA_tmul]`. Both sides reduce to the same expression.
-/
theorem frobOW_jA (x : Ainf l) : frobOW l O (jA l O x) = jA l O (WittVector.frobenius x) := by
  rw [jA_apply, frobOW_inclO, frobOA_tmul]; rfl

variable {ξ ν μ : Ainf l} (hμ : μ = ξ * ν) (hφ : WittVector.frobenius ν = μ)
include hμ hφ

/- English proof (translation)
Use `choose Y' hY' using hY`. Establish `hY'' : ∀ i j, inclO l O (Y' i j) = jA l O (ξ ^ n) * Y i j` using `hY'`. Use `integral_of_frob (fun i => jA l O (ν ^ n) * v i) (Matrix.of Y') (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[map_mul, frobOW_jA, map_pow, hφ, hv, hμ, mul_pow, map_mul]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, hY'', Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem col_mem {ι : Type} [Fintype ι] (n : ℕ) (v : ι → OW l O) (Y : Matrix ι ι (OW l O))
    (hv : ∀ i, frobOW l O (v i) = (Y *ᵥ v) i) (hY : ∀ i j, jA l O (ξ ^ n) * Y i j ∈ (inclO l O).range)
    (i : ι) : jA l O (ν ^ n) * v i ∈ (inclO l O).range := by
  choose Y' hY' using hY
  have hY'' : ∀ i j, inclO l O (Y' i j) = jA l O (ξ ^ n) * Y i j := hY'
  refine integral_of_frob (fun i => jA l O (ν ^ n) * v i) (Matrix.of Y') (fun i => ?_) i
  rw [map_mul, frobOW_jA, map_pow, hφ, hv, hμ, mul_pow, map_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, hY'', Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use `choose Y' hY' using hY`. Establish `hY'' : ∀ i j, inclO l O (Y' i j) = jA l O (ξ ^ n) * Y i j` using `hY'`. Use `integral_of_frob_row (fun i => jA l O (ν ^ n) * v i) (Matrix.of Y') (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[map_mul, frobOW_jA, map_pow, hφ, hv, hμ, mul_pow, map_mul]`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.of_apply, hY'', Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem row_mem {ι : Type} [Fintype ι] (n : ℕ) (v : ι → OW l O) (Y : Matrix ι ι (OW l O))
    (hv : ∀ i, frobOW l O (v i) = (v ᵥ* Y) i) (hY : ∀ i j, jA l O (ξ ^ n) * Y i j ∈ (inclO l O).range)
    (i : ι) : jA l O (ν ^ n) * v i ∈ (inclO l O).range := by
  choose Y' hY' using hY
  have hY'' : ∀ i j, inclO l O (Y' i j) = jA l O (ξ ^ n) * Y i j := hY'
  refine integral_of_frob_row (fun i => jA l O (ν ^ n) * v i) (Matrix.of Y') (fun i => ?_) i
  rw [map_mul, frobOW_jA, map_pow, hφ, hv, hμ, mul_pow, map_mul]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.of_apply, hY'', Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Int

end GlobalTheory.BKExp

end

noncomputable section

namespace GlobalTheory.BKExp

section Setup

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `h1` using `ϖ.iW_of_mem t K (fun _ => EIn l e (A O K))`. Establish `h2` using `ϖ.iW_of_mem t K (fun τ => ⟨_, h τ⟩)`. Rewrite `h1` using `[PiSys.iTot_E]`. Rewrite using `[jA_apply, ← h1, ← map_pow, ← map_mul]`. Use `⟨_, h2.symm.trans (congrArg _ (funext fun τ => Subtype.ext ?_))⟩` and prove the remaining obligations.

Simplify using `[EIn]`.
-/
theorem iE_pow_mul_mem (y : ZMod a → invE l e (A O K)) (n : ℕ)
    (h : ∀ τ, E K l e ^ n * (y τ : K⟦X⟧) ∈ A O K) :
    jA l O (ϖ.ev a (eis l a e)) ^ n * ϖ.iW t K y ∈ (inclO l O).range := by
  have h1 := ϖ.iW_of_mem t K (fun _ => EIn l e (A O K))
  have h2 := ϖ.iW_of_mem t K (fun τ => ⟨_, h τ⟩)
  rw [PiSys.iTot_E] at h1
  rw [jA_apply, ← h1, ← map_pow, ← map_mul]
  refine ⟨_, h2.symm.trans (congrArg _ (funext fun τ => Subtype.ext ?_))⟩
  simp [EIn]

/- English proof (translation)
Set `m : Vec K a ι` to `Pi.single τ (P.mx τ *ᵥ Pi.single j 1)`. Establish `hm : m ∈ P.L` using `mem_tot.2 fun σ => by`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Simplify using `only [m, Pi.single_eq_same]`.

Conclude with `P.mem_extc.2 ⟨_, fun k => by`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _], rfl⟩`. Simplify using `only [m, Pi.single_eq_of_ne hσ]`.

Conclude with `zero_mem _`. Use `mem_tot.1 (hα m hm) τ i` as an intermediate fact. Simplify `this` using `[m]`.
-/
theorem mx_mem (P : PhiMod O K l e a ι) {α : ℕ} (hα : ∀ m ∈ P.L, E K l e ^ α • m ∈ P.M)
    (τ : ZMod a) (i j : ι) : E K l e ^ α * P.mx τ i j ∈ A O K := by
  let m : Vec K a ι := Pi.single τ (P.mx τ *ᵥ Pi.single j 1)
  have hm : m ∈ P.L := mem_tot.2 fun σ => by
    by_cases hσ : σ = τ
    · subst hσ
      simp only [m, Pi.single_eq_same]
      exact P.mem_extc.2 ⟨_, fun k => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _], rfl⟩
    · simp only [m, Pi.single_eq_of_ne hσ]
      exact zero_mem _
  have := mem_tot.1 (hα m hm) τ i
  simpa [m] using this

/- English proof (translation)
Set `m : Vec K a ι` to `Pi.single τ (Pi.single j 1)`. Establish `hm : m ∈ P.M` using `mem_tot.2 fun σ k => by show (m σ k : K⟦X⟧) ∈ A O K`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Simplify using `only [m, Pi.single_eq_same, Pi.single_apply]`.

Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Simplify using `only [m, Pi.single_eq_of_ne hσ, Pi.zero_apply]`. Conclude with `zero_mem _`. Use `P.mem_extc_iff.1 (mem_tot.1 (hβ m hm) τ) i` as an intermediate fact.

Simplify `this` using `[m, Matrix.mulVec_smul]`.
-/
theorem mxInv_mem (P : PhiMod O K l e a ι) {β : ℕ} (hβ : ∀ m ∈ P.M, E K l e ^ β • m ∈ P.L)
    (τ : ZMod a) (i j : ι) : E K l e ^ β * P.mxInv τ i j ∈ A O K := by
  let m : Vec K a ι := Pi.single τ (Pi.single j 1)
  have hm : m ∈ P.M := mem_tot.2 fun σ k => by
    show (m σ k : K⟦X⟧) ∈ A O K
    by_cases hσ : σ = τ
    · subst hσ
      simp only [m, Pi.single_eq_same, Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · simp only [m, Pi.single_eq_of_ne hσ, Pi.zero_apply]
      exact zero_mem _
  have := P.mem_extc_iff.1 (mem_tot.1 (hβ m hm) τ) i
  simpa [m, Matrix.mulVec_smul] using this

end Setup

end GlobalTheory.BKExp

end

noncomputable section

namespace GlobalTheory.BKExp

section Coord

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
  {κ : Type} (b : Module.Basis κ O ↥T.L.T)

def crd (k : κ) : TW (OW l O) T →ₗ[OW l O] OW l O :=
  (Finsupp.lapply k).comp (Algebra.TensorProduct.basis (OW l O) b).repr.toLinearMap

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x m`. Simplify using `only [crd, TWmap, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe, Finsupp.lapply_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes, AlgHom.toLinearMap_apply, LinearMap.id_apply]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem crd_TWmap (k : κ) (w : TW (OW l O) T) :
    crd b k (TWmap (frobOW l O) T w) = frobOW l O (crd b k w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
    simp only [crd, TWmap, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      Finsupp.lapply_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes, AlgHom.toLinearMap_apply,
      LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Establish `key : w ∈ LinearMap.range (TWincl (inclO l O) T)`. Rewrite using `[← (Algebra.TensorProduct.basis (OW l O) b).linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `h k`. Use `⟨z ⊗ₜ b k, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `TensorProduct.map (inclO l O).toLinearMap LinearMap.id (z ⊗ₜ b k) = _`. Rewrite using `[TensorProduct.map_tmul, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Conclude with `congrArg (· ⊗ₜ[O] b k) hz`. Conclude with `key`.
-/
theorem mem_range_TWincl (w : TW (OW l O) T) (h : ∀ k, crd b k w ∈ (inclO l O).range) :
    ∃ z : TW (OA l O) T, TWincl (inclO l O) T z = w := by
  have key : w ∈ LinearMap.range (TWincl (inclO l O) T) := by
    rw [← (Algebra.TensorProduct.basis (OW l O) b).linearCombination_repr w,
      Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨z, hz⟩ := h k
    refine ⟨z ⊗ₜ b k, ?_⟩
    change TensorProduct.map (inclO l O).toLinearMap LinearMap.id (z ⊗ₜ b k) = _
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
    exact congrArg (· ⊗ₜ[O] b k) hz
  exact key

variable (I : Ident t ϖ P T)

def rowv (k : κ) (i : ι) : OW l O := crd b k (I.j (fun j => if i = j then 1 else 0))

/- English proof (translation)
Use `LinearMap.pi_apply_eq_sum_univ ((crd b k).comp I.j.toLinearMap) v` as an intermediate fact. Simplify `this` using `[rowv, smul_eq_mul]`.
-/
theorem crd_j (k : κ) (v : ι → OW l O) : crd b k (I.j v) = ∑ i, v i * rowv b I k i := by
  have := LinearMap.pi_apply_eq_sum_univ ((crd b k).comp I.j.toLinearMap) v
  simpa [rowv, smul_eq_mul] using this

/- English proof (translation)
Establish `h` using `congrArg (crd b k) (I.j_φ (fun j => if i = j then 1 else 0))`. Rewrite `h` using `[crd_TWmap, crd_j, phiW_apply]`. Express the relevant statement in the definitionally equal form `frobOW l O (crd b k (I.j _)) = _`. Rewrite using `[← h]`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.mulVec, apply_ite (frobOW l O), map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Conclude with `Finset.sum_congr rfl fun m _ => mul_comm _ _`.
-/
theorem frob_rowv (k : κ) (i : ι) :
    frobOW l O (rowv b I k i) = (rowv b I k ᵥ* frobMat t ϖ P) i := by
  have h := congrArg (crd b k) (I.j_φ (fun j => if i = j then 1 else 0))
  rw [crd_TWmap, crd_j, phiW_apply] at h
  change frobOW l O (crd b k (I.j _)) = _
  rw [← h]
  simp only [Matrix.vecMul, dotProduct, Matrix.mulVec, apply_ite (frobOW l O), map_one, map_zero,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

end Coord

end GlobalTheory.BKExp

end

noncomputable section

namespace GlobalTheory.BKExp

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hα hβ ε δ hε hδ`. Take `⟨-, h2⟩` from `GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l`. Take `⟨⟨ξ, hξ, hμ⟩, hφ, -⟩` from `h2 ε δ hε hδ`. Take `⟨u, hu⟩` from `Ideal.span_singleton_eq_span_singleton.1 ((ϖ.span_ev_eis a).trans hξ.symm)`. Establish `hsplit : ∀ (n : ℕ) (y : OW l O), jA l O (ξ ^ n) * y = jA l O ((u : Ainf l) ^ n) * (jA l O (ϖ.ev a (eis l a e)) ^ n * y)` using `fun n y => by`.

Rewrite using `[← hu, mul_pow, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hX : ∀ i j, jA l O (ξ ^ α) * frobMat t ϖ P i j ∈ (inclO l O).range` using `fun i j => by`. Rewrite using `[hsplit]`. Conclude with `mul_mem (jA_mem _) (iE_pow_mul_mem t ϖ (fun τ => (P.mat τ : Matrix ι ι (invE l e (A O K))) i j) α fun τ => mx_mem P hα τ i j)`.

Establish `hXi : ∀ i j, jA l O (ξ ^ β) * frobMatInv t ϖ P i j ∈ (inclO l O).range` using `fun i j => by`. Rewrite using `[hsplit]`. Conclude with `mul_mem (jA_mem _) (iE_pow_mul_mem t ϖ (fun τ => (((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) : Matrix ι ι (invE l e (A O K))) i j) β fun τ => mxInv_mem P hβ τ i j)`. Establish `hT : ∀ x i, frobOW l O (I.ofT x i) = (frobMatInv t ϖ P *ᵥ I.ofT x) i` using `fun x i => by`. Establish `h1 : phiW t ϖ P (I.ofT x) = I.ofT x` using `mem_Treal.1 (I.range_ofT ▸ LinearMap.mem_range_self I.ofT x)`.

Rewrite `h1` using `[phiW_apply]`. Use `conv_rhs => rw [← h1]`. Rewrite using `[Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec]`. Establish `hc : ∀ x i, jA l O (muOf δ ^ β) * I.ofT x i ∈ (inclO l O).range` using `fun x => col_mem hμ hφ β _ _ (hT x) hXi`. Use `haveI := T.L.free`.

Set `b` to `Module.Free.chooseBasis O ↥T.L.T`. Establish `hr : ∀ k i, jA l O (muOf δ ^ α) * rowv b I k i ∈ (inclO l O).range` using `fun k => row_mem hμ hφ α _ _ (frob_rowv b I k) hX`. Use `⟨fun x => ?_, ?_, fun x => ?_, ?_⟩` and prove the remaining obligations. Use `choose c hc' using hc x`. Conclude with `⟨c, funext fun i => hc' i⟩`.

Introduce and unpack `_ ⟨c, rfl⟩`. Take `⟨z, hz⟩` from `mem_range_TWincl b (I.j (inclO l O (1 ⊗ₜ (muOf δ ^ α)) • inclV l O ι c)) fun k => by`. Rewrite using `[crd_j]`. Use `Subalgebra.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `: (inclO l O (1 ⊗ₜ (muOf δ ^ α)) • inclV l O ι c) i * rowv b I k i = inclO l O (c i) * (jA l O (muOf δ ^ α) * rowv b I k i)`.

Express the relevant statement in the definitionally equal form `jA l O (muOf δ ^ α) * inclO l O (c i) * _ = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem (AlgHom.mem_range_self _ _) (hr k i)`. Conclude with `⟨z, hz.symm⟩`.

Use `choose c hc' using hc x`. Establish `hc'' : ∀ i, inclO l O (c i) = jA l O (muOf δ ^ β) * I.ofT x i` using `hc'`. Use `⟨fun i => frobOA l O (c i), ?_⟩` and prove the remaining obligations. Establish `: (fun i => inclO l O (frobOA l O (c i))) = jA l O (muOf ε ^ β) • (frobMatInv t ϖ P *ᵥ I.ofT x)` using `funext fun i => by`. Rewrite using `[← frobOW_inclO, hc'' i, map_mul, frobOW_jA, map_pow, hφ, hT x i]`.

Both sides reduce to the same expression. Rewrite using `[inclL_apply, this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, frobMat_mul_inv, Matrix.one_mulVec]`. Both sides reduce to the same expression. Introduce and unpack `_ ⟨c, rfl⟩`. Take `⟨z, hz⟩` from `mem_range_TWincl b (I.j (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • inclL t ϖ P c)) fun k => by`.

Rewrite using `[crd_j]`. Establish `e1 : ∑ i, (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • inclL t ϖ P c) i * rowv b I k i = ∑ i, frobOW l O (jA l O (muOf δ ^ α) * rowv b I k i) * inclO l O (c i)`. Simplify using `only [map_mul, frobOW_jA, map_pow, hφ, frob_rowv, inclL_apply, Pi.smul_apply, smul_eq_mul]`. Establish `e2 : ∑ i, (frobMat t ϖ P *ᵥ fun i => inclO l O (c i)) i * rowv b I k i = ∑ i, (rowv b I k ᵥ* frobMat t ϖ P) i * inclO l O (c i)`. Use `Matrix.dotProduct_mulVec (rowv b I k) (frobMat t ϖ P) (fun i => inclO l O (c i))` as an intermediate fact.

Simplify using `only [dotProduct] at this`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Simplify using `only [mul_assoc, ← Finset.mul_sum, e2]`. Rewrite using `[← map_pow, jA_apply]`.

Rewrite using `[e1]`. Use `Subalgebra.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨d, hd⟩` from `hr k i`. Establish `hd' : inclO l O d = jA l O (muOf δ ^ α) * rowv b I k i` using `hd`. Rewrite using `[← hd', frobOW_inclO]`.

Conclude with `mul_mem (AlgHom.mem_range_self _ _) (AlgHom.mem_range_self _ _)`. Conclude with `⟨z, hz.symm⟩`.
-/
theorem exponents : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∀ x, inclO l O (1 ⊗ₜ (muOf δ ^ β)) • I.ofT x ∈ MA P) ∧ (∀ v ∈ MA P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf δ ^ α)) • v) = TWincl (inclO l O) T z) ∧ (∀ x, inclO l O (1 ⊗ₜ (muOf ε ^ β)) • I.ofT x ∈ LA t ϖ P) ∧ ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • v) = TWincl (inclO l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hα hβ ε δ hε hδ
  obtain ⟨-, h2⟩ := GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l
  obtain ⟨⟨ξ, hξ, hμ⟩, hφ, -⟩ := h2 ε δ hε hδ
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 ((ϖ.span_ev_eis a).trans hξ.symm)
  have hsplit : ∀ (n : ℕ) (y : OW l O), jA l O (ξ ^ n) * y =
      jA l O ((u : Ainf l) ^ n) * (jA l O (ϖ.ev a (eis l a e)) ^ n * y) := fun n y => by
    rw [← hu, mul_pow, map_mul, map_pow]; ring
  have hX : ∀ i j, jA l O (ξ ^ α) * frobMat t ϖ P i j ∈ (inclO l O).range := fun i j => by
    rw [hsplit]
    exact mul_mem (jA_mem _) (iE_pow_mul_mem t ϖ (fun τ => (P.mat τ : Matrix ι ι (invE l e (A O K))) i j) α
      fun τ => mx_mem P hα τ i j)
  have hXi : ∀ i j, jA l O (ξ ^ β) * frobMatInv t ϖ P i j ∈ (inclO l O).range := fun i j => by
    rw [hsplit]
    exact mul_mem (jA_mem _) (iE_pow_mul_mem t ϖ
      (fun τ => (((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) : Matrix ι ι (invE l e (A O K))) i j) β
      fun τ => mxInv_mem P hβ τ i j)
  have hT : ∀ x i, frobOW l O (I.ofT x i) = (frobMatInv t ϖ P *ᵥ I.ofT x) i := fun x i => by
    have h1 : phiW t ϖ P (I.ofT x) = I.ofT x :=
      mem_Treal.1 (I.range_ofT ▸ LinearMap.mem_range_self I.ofT x)
    rw [phiW_apply] at h1
    conv_rhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec]
  have hc : ∀ x i, jA l O (muOf δ ^ β) * I.ofT x i ∈ (inclO l O).range := fun x =>
    col_mem hμ hφ β _ _ (hT x) hXi
  haveI := T.L.free
  let b := Module.Free.chooseBasis O ↥T.L.T
  have hr : ∀ k i, jA l O (muOf δ ^ α) * rowv b I k i ∈ (inclO l O).range := fun k =>
    row_mem hμ hφ α _ _ (frob_rowv b I k) hX
  refine ⟨fun x => ?_, ?_, fun x => ?_, ?_⟩
  · choose c hc' using hc x
    exact ⟨c, funext fun i => hc' i⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨z, hz⟩ := mem_range_TWincl b (I.j (inclO l O (1 ⊗ₜ (muOf δ ^ α)) • inclV l O ι c)) fun k => by
      rw [crd_j]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      have : (inclO l O (1 ⊗ₜ (muOf δ ^ α)) • inclV l O ι c) i * rowv b I k i =
          inclO l O (c i) * (jA l O (muOf δ ^ α) * rowv b I k i) := by
        change jA l O (muOf δ ^ α) * inclO l O (c i) * _ = _
        ring
      rw [this]
      exact mul_mem (AlgHom.mem_range_self _ _) (hr k i)
    exact ⟨z, hz.symm⟩
  · choose c hc' using hc x
    have hc'' : ∀ i, inclO l O (c i) = jA l O (muOf δ ^ β) * I.ofT x i := hc'
    refine ⟨fun i => frobOA l O (c i), ?_⟩
    have : (fun i => inclO l O (frobOA l O (c i))) =
        jA l O (muOf ε ^ β) • (frobMatInv t ϖ P *ᵥ I.ofT x) := funext fun i => by
      rw [← frobOW_inclO, hc'' i, map_mul, frobOW_jA, map_pow, hφ, hT x i]
      rfl
    rw [inclL_apply, this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, frobMat_mul_inv, Matrix.one_mulVec]
    rfl
  · rintro _ ⟨c, rfl⟩
    obtain ⟨z, hz⟩ := mem_range_TWincl b (I.j (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • inclL t ϖ P c)) fun k => by
      rw [crd_j]
      have e1 : ∑ i, (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • inclL t ϖ P c) i * rowv b I k i =
          ∑ i, frobOW l O (jA l O (muOf δ ^ α) * rowv b I k i) * inclO l O (c i) := by
        simp only [map_mul, frobOW_jA, map_pow, hφ, frob_rowv, inclL_apply, Pi.smul_apply, smul_eq_mul]
        have e2 : ∑ i, (frobMat t ϖ P *ᵥ fun i => inclO l O (c i)) i * rowv b I k i =
            ∑ i, (rowv b I k ᵥ* frobMat t ϖ P) i * inclO l O (c i) := by
          have := Matrix.dotProduct_mulVec (rowv b I k) (frobMat t ϖ P) (fun i => inclO l O (c i))
          simp only [dotProduct] at this
          rw [← this]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        simp only [mul_assoc, ← Finset.mul_sum, e2]
        rw [← map_pow, jA_apply]
      rw [e1]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      obtain ⟨d, hd⟩ := hr k i
      have hd' : inclO l O d = jA l O (muOf δ ^ α) * rowv b I k i := hd
      rw [← hd', frobOW_inclO]
      exact mul_mem (AlgHom.mem_range_self _ _) (AlgHom.mem_range_self _ _)
    exact ⟨z, hz.symm⟩

end GlobalTheory.BKExp

end
