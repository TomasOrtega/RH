import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockJumpCount
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankAddOfBiprod
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.SecondTwistCrystallineSmallOfJumpsOfCrys
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDRAndDdRLeFilZeroOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltration

noncomputable section

namespace GlobalTheory.BlockJumps

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount GlobalTheory.HTW.SumJumps GlobalTheory.Cmp.SmallJumps
open ReciprocityTheory.Gal (cycZ)

/- English proof (translation)
Use `haveI : Algebra.FormallyUnramified Qp K := Algebra.FormallyUnramified.of_isSeparable Qp K`. Use `haveI : IsReduced (LL ⊗[Qp] K) := Algebra.FormallyUnramified.isReduced_of_field LL _`. Use `haveI : IsArtinianRing (LL ⊗[Qp] K) := IsArtinianRing.of_finite LL _`. Use `haveI : IsSemisimpleRing (LL ⊗[Qp] K) := IsArtinianRing.isSemisimpleRing_of_isReduced _`. Set `φ : LL ⊗[Qp] K →ₐ[LL] LL` to `Algebra.TensorProduct.lift (AlgHom.id LL LL) τ fun _ _ => .all _ _`.

Take `⟨e, he, hI⟩` from `IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker φ)`. Establish `hφe : φ e = 0`. Establish `: e ∈ RingHom.ker φ` using `hI ▸ Ideal.mem_span_singleton_self e`. Conclude with `this`. Establish `hmul : ∀ y, (∀ c : K, ((1 : LL) ⊗ₜ[Qp] c) * y = τ c • y) → ∀ z, z * y = φ z • y`.

Introduce `y hy z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a c`. Establish `: a ⊗ₜ[Qp] c = a • ((1 : LL) ⊗ₜ[Qp] c)` using `by rw [smul_tmul', smul_eq_mul, mul_one]`.

Rewrite using `[this, smul_mul_assoc, hy, map_smul, smul_smul]`. Simplify using `[φ]`. Consider the case `add a b ha hb => rw [add_mul, ha, hb, map_add, add_smul]`. Establish `hu : ∀ c : K, ((1 : LL) ⊗ₜ[Qp] c) * (1 - e) = τ c • (1 - e)`. Introduce `c`.

Establish `h1 : (1 : LL) ⊗ₜ[Qp] c - algebraMap LL _ (τ c) ∈ RingHom.ker φ`. Rewrite using `[RingHom.mem_ker, map_sub, AlgHom.commutes]`. Simplify using `[φ]`. Rewrite `h1` using `[hI, Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `h1`.

Rewrite using `[← sub_eq_zero, Algebra.smul_def, ← sub_mul, ← ha, mul_assoc, he.mul_one_sub_self, mul_zero]`. Use `⟨1 - e, fun h => ?_, fun y => ⟨fun hy => ?_, fun hy c => ?_⟩⟩` and prove the remaining obligations. Use `congrArg φ h` as an intermediate fact. Simplify using `[hφe] at this`. Establish `h1 : e * y = 0` using `by rw [hmul y hy, hφe, zero_smul]`.

Establish `h2 : y = y * (1 - e)` using `by rw [mul_sub, mul_one, mul_comm, h1, sub_zero]`. Rewrite using `[h2, hmul _ hu]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Rewrite using `[mul_smul_comm, hu, smul_comm]`.
-/
theorem exists_eigen_line {Qp K LL : Type} [Field Qp] [Field K] [Field LL] [Algebra Qp K] [Algebra Qp LL]
    [FiniteDimensional Qp K] [Algebra.IsSeparable Qp K] (τ : K →ₐ[Qp] LL) :
    ∃ u : LL ⊗[Qp] K, u ≠ 0 ∧
      ∀ y, (∀ c : K, ((1 : LL) ⊗ₜ[Qp] c) * y = τ c • y) ↔ y ∈ Submodule.span LL {u} := by
  haveI : Algebra.FormallyUnramified Qp K := Algebra.FormallyUnramified.of_isSeparable Qp K
  haveI : IsReduced (LL ⊗[Qp] K) := Algebra.FormallyUnramified.isReduced_of_field LL _
  haveI : IsArtinianRing (LL ⊗[Qp] K) := IsArtinianRing.of_finite LL _
  haveI : IsSemisimpleRing (LL ⊗[Qp] K) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  let φ : LL ⊗[Qp] K →ₐ[LL] LL := Algebra.TensorProduct.lift (AlgHom.id LL LL) τ fun _ _ => .all _ _
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (RingHom.ker φ)
  have hφe : φ e = 0 := by
    have : e ∈ RingHom.ker φ := hI ▸ Ideal.mem_span_singleton_self e
    exact this
  have hmul : ∀ y, (∀ c : K, ((1 : LL) ⊗ₜ[Qp] c) * y = τ c • y) → ∀ z, z * y = φ z • y := by
    intro y hy z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      have : a ⊗ₜ[Qp] c = a • ((1 : LL) ⊗ₜ[Qp] c) := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this, smul_mul_assoc, hy, map_smul, smul_smul]
      simp [φ]
    | add a b ha hb => rw [add_mul, ha, hb, map_add, add_smul]
  have hu : ∀ c : K, ((1 : LL) ⊗ₜ[Qp] c) * (1 - e) = τ c • (1 - e) := by
    intro c
    have h1 : (1 : LL) ⊗ₜ[Qp] c - algebraMap LL _ (τ c) ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
      simp [φ]
    rw [hI, Ideal.mem_span_singleton'] at h1
    obtain ⟨a, ha⟩ := h1
    rw [← sub_eq_zero, Algebra.smul_def, ← sub_mul, ← ha, mul_assoc, he.mul_one_sub_self, mul_zero]
  refine ⟨1 - e, fun h => ?_, fun y => ⟨fun hy => ?_, fun hy c => ?_⟩⟩
  · have := congrArg φ h
    simp [hφe] at this
  · have h1 : e * y = 0 := by rw [hmul y hy, hφe, zero_smul]
    have h2 : y = y * (1 - e) := by rw [mul_sub, mul_one, mul_comm, h1, sub_zero]
    rw [h2, hmul _ hu]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [mul_smul_comm, hu, smul_comm]

/- English proof (translation)
Set `e2` to `e.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) k k).symm`. Set `A` to `LinearMap.toMatrix' e2.toLinearMap`. Set `B` to `LinearMap.toMatrix' e2.symm.toLinearMap`. Establish `hAB : A * B = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]`.

Establish `hBA : B * A = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]`. Establish `hA : ∀ u, A.mulVec u = Sum.elim (e u).1 (e u).2` using `fun u => by`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Both sides reduce to the same expression.

Establish `hc : ∀ g, A * M g = Matrix.fromBlocks (P g) 0 0 (Matrix.diagonal (χ g)) * A` using `fun g => by`. Use `Matrix.ext_iff_mulVec.2 fun u => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, he, Matrix.fromBlocks_mulVec]`. Apply the tactic sequence `ext (a | a) <;> simp [Matrix.mulVec_diagonal]`. Establish `hAB' : A.map f * B.map f = 1` using `by rw [← Matrix.map_mul, hAB, Matrix.map_one _ f.map_zero f.map_one]`.

Establish `hBA' : B.map f * A.map f = 1` using `by rw [← Matrix.map_mul, hBA, Matrix.map_one _ f.map_zero f.map_one]`. Use `⟨(Matrix.toLin'OfInv hBA' hAB').trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) L L), fun g u => ?_⟩` and prove the remaining obligations. Establish `h1 : (A.map f).mulVec (((M g).map f).mulVec u) = ((Matrix.fromBlocks (P g) 0 0 (Matrix.diagonal (χ g))).map f).mulVec ((A.map f).mulVec u)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, hc]`. Rewrite `h1` using `[Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.diagonal_map f.map_zero]`.

Use `Prod.ext (funext fun a => ?_) (funext fun a => ?_)` and prove the remaining obligations. Use `congrFun h1 (Sum.inl a)` as an intermediate fact. Simplify using `only [Sum.elim_inl, Matrix.map_zero _ f.map_zero, Matrix.zero_mulVec, add_zero] at this`. Conclude with `this`. Use `congrFun h1 (Sum.inr a)` as an intermediate fact.

Simplify using `only [Sum.elim_inr, Matrix.map_zero _ f.map_zero, Matrix.zero_mulVec, zero_add, Matrix.mulVec_diagonal] at this`. Conclude with `this`.
-/
theorem split_map {k L Γ : Type} [Field k] [Field L] (f : k →+* L) {n r t : ℕ}
    (M : Γ → Matrix (Fin n) (Fin n) k) (P : Γ → Matrix (Fin r) (Fin r) k) (χ : Γ → Fin t → k)
    (e : (Fin n → k) ≃ₗ[k] ((Fin r → k) × (Fin t → k)))
    (he : ∀ g u, e ((M g).mulVec u) = ((P g).mulVec (e u).1, fun c => χ g c * (e u).2 c)) :
    ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)), ∀ g u,
      e' (((M g).map f).mulVec u) = (((P g).map f).mulVec (e' u).1, fun c => f (χ g c) * (e' u).2 c) := by
  let e2 := e.trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) k k).symm
  let A := LinearMap.toMatrix' e2.toLinearMap
  let B := LinearMap.toMatrix' e2.symm.toLinearMap
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hA : ∀ u, A.mulVec u = Sum.elim (e u).1 (e u).2 := fun u => by
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hc : ∀ g, A * M g = Matrix.fromBlocks (P g) 0 0 (Matrix.diagonal (χ g)) * A := fun g => by
    refine Matrix.ext_iff_mulVec.2 fun u => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, he, Matrix.fromBlocks_mulVec]
    ext (a | a) <;> simp [Matrix.mulVec_diagonal]
  have hAB' : A.map f * B.map f = 1 := by rw [← Matrix.map_mul, hAB, Matrix.map_one _ f.map_zero f.map_one]
  have hBA' : B.map f * A.map f = 1 := by rw [← Matrix.map_mul, hBA, Matrix.map_one _ f.map_zero f.map_one]
  refine ⟨(Matrix.toLin'OfInv hBA' hAB').trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) L L),
    fun g u => ?_⟩
  have h1 : (A.map f).mulVec (((M g).map f).mulVec u) =
      ((Matrix.fromBlocks (P g) 0 0 (Matrix.diagonal (χ g))).map f).mulVec ((A.map f).mulVec u) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, hc]
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.diagonal_map f.map_zero] at h1
  refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
  · have := congrFun h1 (Sum.inl a)
    simp only [Sum.elim_inl, Matrix.map_zero _ f.map_zero, Matrix.zero_mulVec, add_zero] at this
    exact this
  · have := congrFun h1 (Sum.inr a)
    simp only [Sum.elim_inr, Matrix.map_zero _ f.map_zero, Matrix.zero_mulVec, zero_add,
      Matrix.mulVec_diagonal] at this
    exact this

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Establish `hF : ∀ a, FilV PD (LL` using `LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := fun a => filV_anti PD (by omega)`. Establish `hfin` using `GlobalTheory.finite_jumps_inf_filtration LL _ _ _ h hF`. Establish `h0 : ∀ a, 0 ≤ multV PD ρ τ a` using `fun a => by haveI : FiniteDimensional LL (FildR PD ρ τ a) := Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left`. Establish `: finrank LL (FildR PD ρ τ (a + 1)) ≤ finrank LL (FildR PD ρ τ a)` using `Submodule.finrank_mono (inf_le_inf_left _ (hF a))`. Unfold `multV`.

Use linear arithmetic over natural numbers and integers. Establish `hs : (Function.support fun a => (multV PD ρ τ a).toNat).Finite` using `hfin.subset fun a ha he => by`. Establish `he' : FildR PD ρ τ (a + 1) = FildR PD ρ τ a` using `he`. Use `ha ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(multV PD ρ τ a).toNat = 0`.

Rewrite using `[multV, he', sub_self, Int.toNat_zero]`. Use `⟨Finsupp.toMultiset (Finsupp.ofSupportFinite _ hs), h, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.count_toMultiset, Finsupp.ofSupportFinite_coe, Int.toNat_of_nonneg (h0 a)]`.
-/
theorem exists_isJumpMultiset (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    (h : FiniteDimensional LL (DdRE PD ρ τ)) : ∃ J, IsJumpMultiset PD ρ τ J := by
  have hF : ∀ a, FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a :=
    fun a => filV_anti PD (by omega)
  have hfin := GlobalTheory.finite_jumps_inf_filtration LL _ _ _ h hF
  have h0 : ∀ a, 0 ≤ multV PD ρ τ a := fun a => by
    haveI : FiniteDimensional LL (FildR PD ρ τ a) :=
      Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
    have : finrank LL (FildR PD ρ τ (a + 1)) ≤ finrank LL (FildR PD ρ τ a) :=
      Submodule.finrank_mono (inf_le_inf_left _ (hF a))
    unfold multV
    omega
  have hs : (Function.support fun a => (multV PD ρ τ a).toNat).Finite := hfin.subset fun a ha he => by
    have he' : FildR PD ρ τ (a + 1) = FildR PD ρ τ a := he
    refine ha ?_
    change (multV PD ρ τ a).toNat = 0
    rw [multV, he', sub_self, Int.toNat_zero]
  refine ⟨Finsupp.toMultiset (Finsupp.ofSupportFinite _ hs), h, fun a => ?_⟩
  rw [Finsupp.count_toMultiset, Finsupp.ofSupportFinite_coe, Int.toNat_of_nonneg (h0 a)]

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Take `⟨s, hs1, hs⟩` from `hs`. Establish `h1 : (PD.ι PD.t) ^ e ∈ PD.Fil ((e : ℤ) + 1)`. Use `(PD.Fil _).smul_mem k⁻¹ hk` as an intermediate fact. Rewrite `this` using `[drTwistMap_apply, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ h0, one_smul]`. Then use the resulting hypothesis.

Establish `h2 : ∀ n : ℕ, (PD.ι PD.t) ^ n ∈ PD.Fil ((n : ℤ) + 1) → (1 : BdR) ∈ PD.Fil 1`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Introduce `hn`. Use `PD.Fil_mul _ _ _ _ hn hs1` as an intermediate fact. Rewrite `this` using `[pow_succ, mul_assoc, hs, mul_one]`. Conclude with `ih (by convert this using 2; push_cast; ring)`. Use `PD.Fil_mul _ _ _ _ (h2 e h1) PD.mem_filtration_one` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Conclude with `PD.not_mem_filtration_two this`.
-/
theorem eq_zero_of_twist_mem (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1) (e : ℕ) (k : K)
    (hk : drTwistMap PD e k ∈ PD.Fil ((e : ℤ) + 1)) : k = 0 := by
  by_contra h0
  obtain ⟨s, hs1, hs⟩ := hs
  have h1 : (PD.ι PD.t) ^ e ∈ PD.Fil ((e : ℤ) + 1) := by
    have := (PD.Fil _).smul_mem k⁻¹ hk
    rwa [drTwistMap_apply, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ h0, one_smul] at this
  have h2 : ∀ n : ℕ, (PD.ι PD.t) ^ n ∈ PD.Fil ((n : ℤ) + 1) → (1 : BdR) ∈ PD.Fil 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have := PD.Fil_mul _ _ _ _ hn hs1
      rw [pow_succ, mul_assoc, hs, mul_one] at this
      exact ih (by convert this using 2; push_cast; ring)
  have := PD.Fil_mul _ _ _ _ (h2 e h1) PD.mem_filtration_one
  rw [one_mul] at this
  exact PD.not_mem_filtration_two this

/- English proof (translation)
Use `haveI := PD.finK`. Establish `hr` using `drTwist_range PD ρ e h`. Use `set Ψ := AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (drTwistMap PD e) with hΨ`. Establish `hinj : Function.Injective Ψ` using `Module.Flat.lTensor_preserves_injective_linearMap (M := LL) _ (drTwistMap_injective PD e)`. Establish `hm : ∀ (c : K) y, mulVdR (LL` using `LL) c (Ψ y) = Ψ (((1 : LL) ⊗ₜ[Qp] c) * y) := by`.

Introduce `c y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v k => simp [hΨ, mulVdR, drTwistMap_apply, mul_assoc]`. Consider the case `add x y hx hy => simp only [map_add, mul_add, hx, hy]`.

Take `⟨u, hu0, hu⟩` from `exists_eigen_line τ`. Establish `hE : DdRE PD ρ τ = Submodule.span LL {Ψ u}`. Rewrite using `[← Set.image_singleton, ← Submodule.map_span]`. Use extensionality with `x`. Simplify using `only [DdRE, ← hr, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.mem_range, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, Submodule.mem_map, ← hu]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨y, rfl⟩, hy⟩`. Conclude with `⟨y, fun c => hinj (by rw [← hm, hy, map_smul]), rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨⟨y, rfl⟩, fun c => by rw [hm, hy, map_smul]⟩`.

Establish `h1 : finrank LL (DdRE PD ρ τ) = 1`. Rewrite using `[hE]`. Conclude with `finrank_span_singleton fun h0 => hu0 (hinj (h0.trans (map_zero _).symm))`. Establish `hle : DdR PD ρ ≤ FilV PD (LL` using `LL) (V := LL) e := by`. Rewrite using `[← hr]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b ha hb => rw [map_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Consider the case `tmul v k`. Use `⟨v ⊗ₜ ⟨drTwistMap PD e k, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[drTwistMap_apply, ← Algebra.smul_def]`. Conclude with `(PD.Fil _).smul_mem _ (drTwist_pow_mem PD e)`.

Establish `hbot : DdR PD ρ ⊓ FilV PD (LL` using `LL) (V := LL) ((e : ℤ) + 1) = ⊥ := by`. Rewrite using `[← hr, eq_bot_iff]`. Introduce and unpack `_ ⟨⟨y, rfl⟩, z, hz⟩`. Set `q` to `((PD.Fil ((e : ℤ) + 1)).restrictScalars Qp).mkQ`. Establish `hq : Function.Injective (q ∘ₗ drTwistMap PD e)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `k hk`. Conclude with `eq_zero_of_twist_mem PD hs e k ((Submodule.Quotient.mk_eq_zero _).1 hk)`. Establish `h2 : LinearMap.lTensor LL (q ∘ₗ drTwistMap PD e) y = 0`. Rewrite using `[LinearMap.lTensor_comp_apply]`.

Express the relevant statement in the definitionally equal form `LinearMap.lTensor LL q (Ψ y) = 0`. Rewrite using `[← hz]`. Express the relevant statement in the definitionally equal form `LinearMap.lTensor LL q (LinearMap.lTensor LL _ z) = 0`. Establish `h3 : q ∘ₗ ((PD.Fil ((e : ℤ) + 1)).restrictScalars Qp).subtype = 0` using `LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).2 x.2`. Rewrite using `[← LinearMap.lTensor_comp_apply, h3, LinearMap.lTensor_zero, LinearMap.zero_apply]`.

Use `Module.Flat.lTensor_preserves_injective_linearMap (M := LL) _ hq (h2.trans (map_zero _).symm)` as an intermediate fact. Rewrite using `[this, map_zero]`. Conclude with `Submodule.zero_mem _`. Establish `key : ∀ b : ℤ, (finrank LL (FildR PD ρ τ b) : ℤ) = if b ≤ e then 1 else 0`. Introduce `b`.

Use `split_ifs with hb`. Rewrite using `[show FildR PD ρ τ b = DdRE PD ρ τ from inf_eq_left.2 (inf_le_left.trans (hle.trans (filV_anti PD hb))), h1, Nat.cast_one]`. Rewrite using `[show FildR PD ρ τ b = ⊥ from eq_bot_iff.2 (hbot ▸ inf_le_inf inf_le_left (filV_anti PD (by omega))), finrank_bot, Nat.cast_zero]`. Rewrite using `[multV, key, key]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem multV_twist [Algebra.IsSeparable Qp K] (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1)
    (ρ : Representation LL G LL) (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = if a = e then 1 else 0 := by
  haveI := PD.finK
  have hr := drTwist_range PD ρ e h
  set Ψ := AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (drTwistMap PD e) with hΨ
  have hinj : Function.Injective Ψ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := LL) _ (drTwistMap_injective PD e)
  have hm : ∀ (c : K) y, mulVdR (LL := LL) c (Ψ y) = Ψ (((1 : LL) ⊗ₜ[Qp] c) * y) := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v k => simp [hΨ, mulVdR, drTwistMap_apply, mul_assoc]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  obtain ⟨u, hu0, hu⟩ := exists_eigen_line τ
  have hE : DdRE PD ρ τ = Submodule.span LL {Ψ u} := by
    rw [← Set.image_singleton, ← Submodule.map_span]
    ext x
    simp only [DdRE, ← hr, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.mem_range,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, Submodule.mem_map, ← hu]
    constructor
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, fun c => hinj (by rw [← hm, hy, map_smul]), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, fun c => by rw [hm, hy, map_smul]⟩
  have h1 : finrank LL (DdRE PD ρ τ) = 1 := by
    rw [hE]
    exact finrank_span_singleton fun h0 => hu0 (hinj (h0.trans (map_zero _).symm))
  have hle : DdR PD ρ ≤ FilV PD (LL := LL) (V := LL) e := by
    rw [← hr]
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul v k =>
      refine ⟨v ⊗ₜ ⟨drTwistMap PD e k, ?_⟩, rfl⟩
      rw [drTwistMap_apply, ← Algebra.smul_def]
      exact (PD.Fil _).smul_mem _ (drTwist_pow_mem PD e)
  have hbot : DdR PD ρ ⊓ FilV PD (LL := LL) (V := LL) ((e : ℤ) + 1) = ⊥ := by
    rw [← hr, eq_bot_iff]
    rintro _ ⟨⟨y, rfl⟩, z, hz⟩
    let q := ((PD.Fil ((e : ℤ) + 1)).restrictScalars Qp).mkQ
    have hq : Function.Injective (q ∘ₗ drTwistMap PD e) := by
      rw [injective_iff_map_eq_zero]
      intro k hk
      exact eq_zero_of_twist_mem PD hs e k ((Submodule.Quotient.mk_eq_zero _).1 hk)
    have h2 : LinearMap.lTensor LL (q ∘ₗ drTwistMap PD e) y = 0 := by
      rw [LinearMap.lTensor_comp_apply]
      change LinearMap.lTensor LL q (Ψ y) = 0
      rw [← hz]
      change LinearMap.lTensor LL q (LinearMap.lTensor LL _ z) = 0
      have h3 : q ∘ₗ ((PD.Fil ((e : ℤ) + 1)).restrictScalars Qp).subtype = 0 :=
        LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).2 x.2
      rw [← LinearMap.lTensor_comp_apply, h3, LinearMap.lTensor_zero, LinearMap.zero_apply]
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := LL) _ hq
      (h2.trans (map_zero _).symm)
    rw [this, map_zero]
    exact Submodule.zero_mem _
  have key : ∀ b : ℤ, (finrank LL (FildR PD ρ τ b) : ℤ) = if b ≤ e then 1 else 0 := by
    intro b
    split_ifs with hb
    · rw [show FildR PD ρ τ b = DdRE PD ρ τ from
        inf_eq_left.2 (inf_le_left.trans (hle.trans (filV_anti PD hb))), h1, Nat.cast_one]
    · rw [show FildR PD ρ τ b = ⊥ from eq_bot_iff.2 (hbot ▸ inf_le_inf inf_le_left
        (filV_anti PD (by omega))), finrank_bot, Nat.cast_zero]
  rw [multV, key, key]
  split_ifs <;> omega

def diagRep {t : ℕ} (χ : Fin t → G →* LLˣ) : Representation LL G (Fin t → LL) where
  toFun g := LinearMap.pi fun c => ((χ c g : LLˣ) : LL) • LinearMap.proj c
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagRep_apply {t : ℕ} (χ : Fin t → G →* LLˣ) (g : G) (v : Fin t → LL) (c : Fin t) :
    diagRep χ g v c = ((χ c g : LLˣ) : LL) * v c := rfl

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => haveI : Subsingleton ((Fin 0 → LL) ⊗[Qp] BdR) := inferInstance`. Simplify using `[multV, Module.finrank_zero_of_subsingleton]`. Consider the case `succ t ih => haveI : Module.Finite Qp (Fin t → LL) := inferInstance haveI := finite_ddR_of_isField PD hF (charRep (χ 0)) haveI := finite_ddR_of_isField PD hF (diagRep fun c : Fin t => χ c.succ)`. Rewrite using `[Fin.sum_univ_succ, ← ih]`.

Conclude with `multV_add PD (Fin.consLinearEquiv LL fun _ => LL).symm (fun g v => rfl) τ a`.
-/
theorem multV_diagRep (hF : IsField BdR) [FiniteDimensional Qp LL] {t : ℕ} (χ : Fin t → G →* LLˣ)
    (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD (diagRep χ) τ a = ∑ c, multV PD (charRep (χ c)) τ a := by
  induction t with
  | zero =>
    haveI : Subsingleton ((Fin 0 → LL) ⊗[Qp] BdR) := inferInstance
    simp [multV, Module.finrank_zero_of_subsingleton]
  | succ t ih =>
    haveI : Module.Finite Qp (Fin t → LL) := inferInstance
    haveI := finite_ddR_of_isField PD hF (charRep (χ 0))
    haveI := finite_ddR_of_isField PD hF (diagRep fun c : Fin t => χ c.succ)
    rw [Fin.sum_univ_succ, ← ih]
    exact multV_add PD (Fin.consLinearEquiv LL fun _ => LL).symm (fun g v => rfl) τ a

/- English proof (translation)
Set `χ : Fin t → G →* LLˣ` to `fun c => ((cycLL PD LL)⁻¹) ^ (c : ℕ)`. Establish `hχ : ∀ c g, ((χ c g : LLˣ) : LL) = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ (c : ℕ)` using `fun c g => by`. Simplify using `[χ, cycLL]`. Use `haveI := finite_ddR_of_isField PD hF ρ`. Use `haveI := finite_ddR_of_isField PD hF σ`.

Use `haveI := finite_ddR_of_isField PD hF (diagRep χ)`. Take `⟨J, hJ⟩` from `exists_isJumpMultiset PD ρ τ (Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left)`. Use `⟨J, hJ, Submodule.finiteDimensional_of_le (S₂ := DdR PD σ) inf_le_left, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[multV_add PD (ρ' := ρ) (ρ'' := diagRep χ) e (fun g v => by`. Rewrite using `[he]`.

Conclude with `Prod.ext rfl (funext fun c => congrArg (· * (e v).2 c) (hχ c g).symm)) τ a,`. Use the proof step `hJ.2, multV_diagRep PD hF, Multiset.count_add, count_blockJumps,`. Use the proof step `Finset.sum_congr rfl fun c _ => multV_twist PD hs (charRep (χ c)) c (fun g x => by rw [← hχ]; rfl) τ a]`. Use `push_cast`. Use `congr 1`.

Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single (⟨a.toNat, by omega⟩ : Fin t), if_pos (by simp only; omega)]`. Introduce `c _ hc`. Use `if_neg fun h' => hc (Fin.ext ?_)` and prove the remaining obligations. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Conclude with `fun h' => absurd (Finset.mem_univ _) h'`. Use `Finset.sum_eq_zero fun c _ => if_neg fun h' => h ?_` and prove the remaining obligations. Use `c.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem jumps_of_split [Algebra.IsSeparable Qp K] [FiniteDimensional Qp LL] (hF : IsField BdR)
    (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1) {n r t : ℕ}
    (σ : Representation LL G (Fin n → LL)) (ρ : Representation LL G (Fin r → LL))
    (e : (Fin n → LL) ≃ₗ[LL] ((Fin r → LL) × (Fin t → LL)))
    (he : ∀ g u, e (σ g u) =
      (ρ g (e u).1, fun c : Fin t => ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ (c : ℕ) * (e u).2 c))
    (τ : K →ₐ[Qp] LL) :
    ∃ J, IsJumpMultiset PD ρ τ J ∧ IsJumpMultiset PD σ τ (J + blockJumps t) := by
  let χ : Fin t → G →* LLˣ := fun c => ((cycLL PD LL)⁻¹) ^ (c : ℕ)
  have hχ : ∀ c g, ((χ c g : LLˣ) : LL) = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ (c : ℕ) := fun c g => by
    simp [χ, cycLL]
  haveI := finite_ddR_of_isField PD hF ρ
  haveI := finite_ddR_of_isField PD hF σ
  haveI := finite_ddR_of_isField PD hF (diagRep χ)
  obtain ⟨J, hJ⟩ := exists_isJumpMultiset PD ρ τ
    (Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left)
  refine ⟨J, hJ, Submodule.finiteDimensional_of_le (S₂ := DdR PD σ) inf_le_left, fun a => ?_⟩
  rw [multV_add PD (ρ' := ρ) (ρ'' := diagRep χ) e (fun g v => by
      rw [he]
      exact Prod.ext rfl (funext fun c => congrArg (· * (e v).2 c) (hχ c g).symm)) τ a,
    hJ.2, multV_diagRep PD hF, Multiset.count_add, count_blockJumps,
    Finset.sum_congr rfl fun c _ => multV_twist PD hs (charRep (χ c)) c
      (fun g x => by rw [← hχ]; rfl) τ a]
  push_cast
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨a.toNat, by omega⟩ : Fin t), if_pos (by simp only; omega)]
    · intro c _ hc
      refine if_neg fun h' => hc (Fin.ext ?_)
      simp only
      omega
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun c _ => if_neg fun h' => h ?_
    have := c.2
    omega

end Periods

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : CharZero Ω := Bw.j.charZero`. Use `haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Use `set u : ℤ_[l] := ((cycZ E Ω l (Br.ι Bw g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l]) with hu`. Establish `key : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - (u : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))`.

Introduce `m`. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)`. Establish `hζ'` using `hζ.map_of_injective Bw.j.injective`. Take `⟨a, ha, hga⟩` from `P.χQ_cyc (g : GQ l) m _ hζ'.pow_eq_one`.

Establish `hb : ((Br.ι Bw g : ↥Gw) : Ω ≃ₐ[E] Ω) ζ = ζ ^ (u.toZModPow m).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω ((Br.ι Bw g : ↥Gw) : Ω ≃ₐ[E] Ω)) ζ hζ.pow_eq_one`. Establish `hc` using `Bw.e_comm (Br.ι Bw g) ζ`. Rewrite `hc` using `[show Bw.e (Br.ι Bw g) = g from Bw.e.apply_symm_apply g, hga, hb, ← map_pow]`. Establish `hab : a ≡ (u.toZModPow m).val [MOD l ^ m]`. Establish `h0` using `Bw.j.injective hc`.

Generalize the expression as in `(u.toZModPow m).val = b at h0 ⊢`. Rewrite using `[hζ.eq_orderOf]`. Take `⟨v, rfl⟩` from `hζ.isUnit (NeZero.ne _)`. Rewrite using `[orderOf_units]`. Conclude with `pow_eq_pow_iff_modEq.mp (Units.ext (by simpa using h0))`.

Establish `h1 : ‖u - (a : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))`. Rewrite using `[PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 hab, ZMod.natCast_zmod_val, sub_self]`. Rewrite `h1` using `[PadicInt.norm_def]`. Move the coercions through the operations in `at h1`. Rewrite using `[show (P.χQ (g : GQ l) : ℚ_[l]) - (u : ℚ_[l]) = ((P.χQ (g : GQ l) : ℚ_[l]) - a) + -((u : ℚ_[l]) - a) by ring]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `h0 : ‖(P.χQ (g : GQ l) : ℚ_[l]) - (u : ℚ_[l])‖ ≤ 0` using `ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity) (inv_lt_one_of_one_lt₀ hl1)) fun m => by simpa using key m`. Conclude with `(sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm`.
-/
theorem cycZ_eq_chi {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (P : LocPrime l) (g : ↥(GK Bw.Kw)) :
    (((cycZ E Ω l (Br.ι Bw g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = (P.χQ (g : GQ l) : ℚ_[l]) := by
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := Bw.j.charZero
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  set u : ℤ_[l] := ((cycZ E Ω l (Br.ι Bw g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l]) with hu
  have key : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - (u : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hζ' := hζ.map_of_injective Bw.j.injective
    obtain ⟨a, ha, hga⟩ := P.χQ_cyc (g : GQ l) m _ hζ'.pow_eq_one
    have hb : ((Br.ι Bw g : ↥Gw) : Ω ≃ₐ[E] Ω) ζ = ζ ^ (u.toZModPow m).val :=
      cyclotomicCharacter.spec l
        (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω ((Br.ι Bw g : ↥Gw) : Ω ≃ₐ[E] Ω)) ζ hζ.pow_eq_one
    have hc := Bw.e_comm (Br.ι Bw g) ζ
    rw [show Bw.e (Br.ι Bw g) = g from Bw.e.apply_symm_apply g, hga, hb, ← map_pow] at hc
    have hab : a ≡ (u.toZModPow m).val [MOD l ^ m] := by
      have h0 := Bw.j.injective hc
      generalize (u.toZModPow m).val = b at h0 ⊢
      rw [hζ.eq_orderOf]
      obtain ⟨v, rfl⟩ := hζ.isUnit (NeZero.ne _)
      rw [orderOf_units]
      exact pow_eq_pow_iff_modEq.mp (Units.ext (by simpa using h0))
    have h1 : ‖u - (a : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
        map_sub, map_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 hab, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.norm_def] at h1
    push_cast at h1
    rw [show (P.χQ (g : GQ l) : ℚ_[l]) - (u : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]) - a) + -((u : ℚ_[l]) - a) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have h0 : ‖(P.χQ (g : GQ l) : ℚ_[l]) - (u : ℚ_[l])‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl1)) fun m => by simpa using key m
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm

/- English proof (translation)
Introduce `i r ρ π _ _ ⟨e, he⟩ w hw τ`. Use `haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E`. Set `s : Br.G D.nbr i w hw → GE D.nd` to `fun g => decS D.nd w (Br.iota D.nbr i w hw g)`. Set `f` to `Br.toLLK (D.nbr i w hw)`. Establish `hf : ∀ c, f (toK D.nd i c) = (D.nbr i w hw).toLL c` using `Br.toLLK_alg (D.nbr i w hw)`.

Establish `hχ : ∀ (c : Fin D.R.t) g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i ((c : ℕ) + 1) g = (epsU D.nd i g)⁻¹ ^ (c : ℕ)` using `fun c g => by`. Establish `h` using `D.nd.chi_def i ((c : ℕ) + 1) (by omega) c.2`. Express the relevant statement in the definitionally equal form `(D.nd.chi i 1)⁻¹ g * D.nd.chi i ((c : ℕ) + 1) g = _`. Rewrite using `[h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]`. Both sides reduce to the same expression.

Take `⟨e', he'⟩` from `split_map f (fun g => mapM (toK D.nd i) (rTwO D.nd i r π) (s g)) (fun g => mapM (toK D.nd i) (WpO D.nd i ρ π) (s g)) (fun g c => toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ (c : ℕ) : (D.nd.O i)ˣ) : D.nd.O i)) e (fun g u => by`. Establish `h1 : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) v, (mapM (toK D.nd i) (twistM M (chiU D.nd i 1)⁻¹) (s g)).mulVec v = toK D.nd i (((chiU D.nd i 1)⁻¹ (s g) : (D.nd.O i)ˣ) : D.nd.O i) • (mapM (toK D.nd i) M (s g)).mulVec v` using `fun M v => by`. Rewrite using `[← Matrix.smul_mulVec]`. Use `congr 1`. Use extensionality with `a b`.

Conclude with `map_mul (toK D.nd i) _ _`. Rewrite using `[rTwO, WpO, h1, h1, map_smul, he]`. Use `Prod.ext rfl (funext fun c => ?_)` and prove the remaining obligations. Simplify using `only [← hχ, Units.val_mul, map_mul, mul_assoc]`. Use the proof step `rfl)`.

Establish `hε : ∀ g, (D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i) = algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i])`. Introduce `g`. Rewrite using `[Br.PD, (D.loc _).PD_χ, ← cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]`. Conclude with `congrArg Subtype.val ((D.nbr i w hw).eO_alg _)`. Establish `hM : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) g v, matRep (Br.loc D.nbr i w hw M) g v = ((mapM (toK D.nd i) M (s g)).map f).mulVec v` using `fun M g v => by`.

Rewrite using `[show (mapM (toK D.nd i) M (s g)).map f = Br.loc D.nbr i w hw M g from Matrix.ext fun a b => hf _]`. Both sides reduce to the same expression. Use `jumps_of_split _ (GlobalTheory.SmallJumpExample.isField_bdR D _) ?_ _ _ e' (fun g u => ?_) τ` and prove the remaining obligations. Take `⟨x, hx, hx1⟩` from `GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one (D.locT (D.nd.l i))`. Use `⟨x, ?_, by rw [Br.PD, (D.loc _).PD_ι, (D.loc _).period_datum_t_eq, hx1]⟩` and prove the remaining obligations.

Conclude with `((D.locT _).fil _ _ _).2 (((D.locT _).fil _ _ _).1 hx)`. Rewrite using `[hM, hM, he']`. Use `Prod.ext rfl (funext fun c => ?_)` and prove the remaining obligations. Use `congrArg (· * (e' u).2 c) ?_` and prove the remaining obligations. Rewrite using `[hf, Units.val_pow_eq_pow_val, map_pow, map_units_inv, hε]`.
-/
theorem blockJumps_at_all (D : D7) : blockJumps_at D := by
  intro i r ρ π _ _ ⟨e, he⟩ w hw τ
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  let s : Br.G D.nbr i w hw → GE D.nd := fun g => decS D.nd w (Br.iota D.nbr i w hw g)
  let f := Br.toLLK (D.nbr i w hw)
  have hf : ∀ c, f (toK D.nd i c) = (D.nbr i w hw).toLL c := Br.toLLK_alg (D.nbr i w hw)
  have hχ : ∀ (c : Fin D.R.t) g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i ((c : ℕ) + 1) g =
      (epsU D.nd i g)⁻¹ ^ (c : ℕ) := fun c g => by
    have h := D.nd.chi_def i ((c : ℕ) + 1) (by omega) c.2
    change (D.nd.chi i 1)⁻¹ g * D.nd.chi i ((c : ℕ) + 1) g = _
    rw [h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl
  obtain ⟨e', he'⟩ := split_map f (fun g => mapM (toK D.nd i) (rTwO D.nd i r π) (s g))
    (fun g => mapM (toK D.nd i) (WpO D.nd i ρ π) (s g))
    (fun g c => toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ (c : ℕ) : (D.nd.O i)ˣ) : D.nd.O i)) e (fun g u => by
      have h1 : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) v,
          (mapM (toK D.nd i) (twistM M (chiU D.nd i 1)⁻¹) (s g)).mulVec v =
            toK D.nd i (((chiU D.nd i 1)⁻¹ (s g) : (D.nd.O i)ˣ) : D.nd.O i) •
              (mapM (toK D.nd i) M (s g)).mulVec v := fun M v => by
        rw [← Matrix.smul_mulVec]
        congr 1
        ext a b
        exact map_mul (toK D.nd i) _ _
      rw [rTwO, WpO, h1, h1, map_smul, he]
      refine Prod.ext rfl (funext fun c => ?_)
      simp only [← hχ, Units.val_mul, map_mul, mul_assoc]
      rfl)
  have hε : ∀ g, (D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
    intro g
    rw [Br.PD, (D.loc _).PD_χ, ← cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
    exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)
  have hM : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) g v,
      matRep (Br.loc D.nbr i w hw M) g v = ((mapM (toK D.nd i) M (s g)).map f).mulVec v := fun M g v => by
    rw [show (mapM (toK D.nd i) M (s g)).map f = Br.loc D.nbr i w hw M g from
      Matrix.ext fun a b => hf _]
    rfl
  refine jumps_of_split _ (GlobalTheory.SmallJumpExample.isField_bdR D _) ?_ _ _ e' (fun g u => ?_) τ
  · obtain ⟨x, hx, hx1⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one (D.locT (D.nd.l i))
    refine ⟨x, ?_, by rw [Br.PD, (D.loc _).PD_ι, (D.loc _).period_datum_t_eq, hx1]⟩
    exact ((D.locT _).fil _ _ _).2 (((D.locT _).fil _ _ _).1 hx)
  · rw [hM, hM, he']
    refine Prod.ext rfl (funext fun c => ?_)
    refine congrArg (· * (e' u).2 c) ?_
    rw [hf, Units.val_pow_eq_pow_val, map_pow, map_units_inv, hε]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ _ _ => blockJumps_at_all _⟩`.
-/
theorem blockJumpsF_all {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : blockJumpsF Fm CH :=
  ⟨0, fun _ _ _ => blockJumps_at_all _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => blockJumpsF_all _ _⟩⟩`.
-/
theorem blockJumpsClosed_all (𝒞 : FamClass) : blockJumpsClosed 𝒞 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ _ _ _ => blockJumpsF_all _ _⟩⟩

end GlobalTheory.BlockJumps
