import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealGeneratorsFromBase
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

/- English proof (translation)
Take `⟨bk, hbk⟩ : ∃ bk : Module.Basis n (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M), ∀ j, bk j = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bb j` from `⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bb, fun j => by simp⟩`. Establish `hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m) = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)`. Introduce `c m`. Establish `hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m) = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m` using `(TensorProduct.smul_tmul c 1 m).symm`. Establish `hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c`.

Rewrite using `[Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]`. Establish `hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m` using `rfl`. Rewrite using `[hA1, hA2, hA3, mul_one]`. Establish `hxsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x = ∑ j : n, IsLocalRing.residue A (bb.repr x j) • bk j` using `by conv_lhs => rw [← bb.sum_repr x]`. Rewrite using `[TensorProduct.tmul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by rw [hkey, hbk j]`. Establish `h2 : bk.repr ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) i = 0`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[hxsum, Module.Basis.repr_sum_self]`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`. Conclude with `h2`.
-/
private theorem repr_mem_maximalIdeal_of_tmul_eq_zero {A : Type*} [CommRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {n : Type*} [Fintype n]
    (bb : Module.Basis n A M) (x : M)
    (h : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x = 0) (i : n) :
    bb.repr x i ∈ IsLocalRing.maximalIdeal A := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis n (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M),
      ∀ j, bk j = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bb j :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bb, fun j => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
      = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
        = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m := (TensorProduct.smul_tmul c 1 m).symm
    have hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
    have hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)
        = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hxsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x
      = ∑ j : n, IsLocalRing.residue A (bb.repr x j) • bk j := by
    conv_lhs => rw [← bb.sum_repr x]
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hkey, hbk j]
  have h2 : bk.repr ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) i = 0 := by
    rw [h]
    simp
  rw [hxsum, Module.Basis.repr_sum_self] at h2
  rw [← IsLocalRing.residue_eq_zero_iff]
  exact h2

/- English proof (translation)
Take `⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M), ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bA i` from `⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bA, fun i => by simp⟩`. Establish `hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m) = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)`. Introduce `c m`. Establish `hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m) = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m` using `(TensorProduct.smul_tmul c 1 m).symm`. Establish `hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c`.

Rewrite using `[Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]`. Establish `hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m` using `rfl`. Rewrite using `[hA1, hA2, hA3, mul_one]`. Establish `hmat : ∀ i j : ι, bk.repr (B' j) i = IsLocalRing.residue A (bA.toMatrix G i j)`. Introduce `i j`.

Establish `hGj : B' j = ∑ l : ι, IsLocalRing.residue A (bA.repr (G j) l) • bk l`. Rewrite using `[hB' j]`. Use `conv_lhs => rw [← bA.sum_repr (G j)]`. Rewrite using `[TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[hkey, hbk l]`. Rewrite using `[hGj, Module.Basis.repr_sum_self, Module.Basis.toMatrix_apply]`. Establish `hdet : bk.det (⇑B') = IsLocalRing.residue A (bA.det G)`. Rewrite using `[Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `only [Module.Basis.toMatrix_apply]`. Conclude with `hmat i j`. Rewrite using `[← hdet]`. Conclude with `(bk.isUnit_det B').ne_zero`.
-/
private theorem residue_det_ne_zero_of_tmul_eq_basis {A : Type*} [CommRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bA : Module.Basis ι A M) (G : ι → M)
    (B' : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M))
    (hB' : ∀ i, B' i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] G i) :
    IsLocalRing.residue A (bA.det G) ≠ 0 := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] M),
      ∀ i, bk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] bA i :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) bA, fun i => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
      = IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (c • m)
        = (c • (1 : IsLocalRing.ResidueField A)) ⊗ₜ[A] m := (TensorProduct.smul_tmul c 1 m).symm
    have hA2 : c • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A c := by
      rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
    have hA3 : IsLocalRing.residue A c • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m)
        = (IsLocalRing.residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hmat : ∀ i j : ι, bk.repr (B' j) i = IsLocalRing.residue A (bA.toMatrix G i j) := by
    intro i j
    have hGj : B' j = ∑ l : ι, IsLocalRing.residue A (bA.repr (G j) l) • bk l := by
      rw [hB' j]
      conv_lhs => rw [← bA.sum_repr (G j)]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hkey, hbk l]
    rw [hGj, Module.Basis.repr_sum_self, Module.Basis.toMatrix_apply]
  have hdet : bk.det (⇑B') = IsLocalRing.residue A (bA.det G) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [Module.Basis.toMatrix_apply]
    exact hmat i j
  rw [← hdet]
  exact (bk.isUnit_det B').ne_zero

/- English proof (translation)
Take `⟨Jm, hJmdef⟩ : ∃ Jm : Ideal A, Jm = IsLocalRing.maximalIdeal A * J` from `⟨_, rfl⟩`. Establish `hmulJ : ∀ c ∈ IsLocalRing.maximalIdeal A, ∀ u ∈ J, c * u ∈ Jm`. Introduce `c hc u hu`. Rewrite using `[hJmdef]`. Conclude with `Ideal.mul_mem_mul hc hu`.

Establish `hJmle : Jm ≤ J`. Rewrite using `[hJmdef]`. Conclude with `Ideal.mul_le_right`. Establish `hsmulg : ∀ (c : A) (x : A ⧸ Jm), c • x = Ideal.Quotient.mk Jm c * x`. Introduce `c x`.

Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq]`. Establish `hsmulmk : ∀ c u : A, c • (Ideal.Quotient.mk Jm u) = Ideal.Quotient.mk Jm (c * u)`. Introduce `c u`. Rewrite using `[hsmulg, ← map_mul]`. Establish `hρ0 : ∀ a ∈ Jm, (Ideal.Quotient.mkₐ A J) a = 0`.

Introduce `a ha`. Use `show Ideal.Quotient.mk J a = 0`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (hJmle ha)`. Set `ρA : (A ⧸ Jm) →ₐ[A] (A ⧸ J)` to `Ideal.Quotient.liftₐ Jm (Ideal.Quotient.mkₐ A J) hρ0`. Set `ρ : (A ⧸ Jm) →ₐ[k] (A ⧸ J)` to `ρA.restrictScalars k`.

Establish `hρmkA : ∀ a : A, ρA (Ideal.Quotient.mk Jm a) = Ideal.Quotient.mk J a` using `fun _ => rfl`. Establish `hρmk : ∀ a : A, ρ (Ideal.Quotient.mk Jm a) = Ideal.Quotient.mk J a` using `fun _ => rfl`. Establish `hρsurj : Function.Surjective ρ`. Introduce `c`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective c`.

Conclude with `⟨Ideal.Quotient.mk Jm a, hρmk a⟩`. Establish `hker2 : RingHom.ker (ρ : (A ⧸ Jm) →+* (A ⧸ J)) ^ 2 = ⊥`. Rewrite using `[pow_two]`. Use `le_antisymm (Ideal.mul_le.mpr ?_) bot_le` and prove the remaining obligations. Introduce `u hu v hv`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Establish `ha : a ∈ J`. Establish `h1 : Ideal.Quotient.mk J a = 0`. Rewrite using `[← hρmk a]`.

Conclude with `RingHom.mem_ker.mp hu`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h1`. Establish `hb : b ∈ J`. Establish `h1 : Ideal.Quotient.mk J b = 0`. Rewrite using `[← hρmk b]`.

Conclude with `RingHom.mem_ker.mp hv`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h1`. Use `(Submodule.mem_bot _).mpr ?_` and prove the remaining obligations. Rewrite using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmulJ a (hJmax ha) b hb`.

Establish `hprod : ∀ u v : A ⧸ Jm, ρA u = 0 → ρA v = 0 → u * v = 0`. Introduce `u v hu hv`. Establish `hmem : u * v ∈ RingHom.ker (ρ : (A ⧸ Jm) →+* (A ⧸ J)) ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul (RingHom.mem_ker.mpr hu) (RingHom.mem_ker.mpr hv)`.

Rewrite `hmem` using `[hker2]`. Simplify using `using hmem`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ⟩ : ∃ σ : (A ⧸ J) →ₐ[k] (A ⧸ Jm), ∀ c, ρ (σ c) = c := by`. Use `⟨Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (A ⧸ J)) ρ hρsurj ⟨2, hker2⟩, fun c => ?_⟩` and prove the remaining obligations. Establish `h` using `Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k (A ⧸ J)) ρ hρsurj ⟨2, hker2⟩`.

Establish `h2` using `DFunLike.congr_fun h c`. Simplify using `using h2`. Establish `hρσ : ∀ c : A ⧸ J, ρA (σ c) = c` using `fun c => hσ c`. Establish `hkerel : ∀ a : A, ρA (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) = 0`. Introduce `a`.

Rewrite using `[map_sub, hρmkA a, hρσ (Ideal.Quotient.mk J a), sub_self]`. Establish `hmkJmsmul : ∀ (c : k) (a : A), Ideal.Quotient.mk Jm (c • a) = c • Ideal.Quotient.mk Jm a`. Introduce `c a`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply k A (A ⧸ Jm)]`. Establish `hmkJsmul : ∀ (c : k) (a : A), Ideal.Quotient.mk J (c • a) = c • Ideal.Quotient.mk J a`.

Introduce `c a`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply k A (A ⧸ J)]`. Establish `hadd : ∀ a b : A, Ideal.Quotient.mk Jm (a + b) - σ (Ideal.Quotient.mk J (a + b)) = (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) + (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b))`. Introduce `a b`. Simplify using `only [map_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsmulk : ∀ (c : k) (a : A), Ideal.Quotient.mk Jm (c • a) - σ (Ideal.Quotient.mk J (c • a)) = (RingHom.id k) c • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))`. Introduce `c a`. Use `show Ideal.Quotient.mk Jm (c • a) - σ (Ideal.Quotient.mk J (c • a)) = c • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))`. Rewrite using `[hmkJmsmul c a, hmkJsmul c a, map_smul, smul_sub]`.

Establish `hleib : ∀ a b : A, Ideal.Quotient.mk Jm (a * b) - σ (Ideal.Quotient.mk J (a * b)) = a • (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b)) + b • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))`. Introduce `a b`. Establish `hz2` using `hprod (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b)) (hkerel a) (hkerel b)`. Rewrite using `[hsmulg a, hsmulg b]`. Simplify using `only [map_mul]`.

Take the linear combination `-hz2`. Take `⟨Dder, hDapp⟩ : ∃ D : Derivation k A (A ⧸ Jm), ∀ a : A, D a = Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)` from `⟨Derivation.mk' { toFun := fun a => Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a) map_add' := hadd map_smul' := hsmulk } hleib, fun _ => rfl⟩`. Establish `hderivLift : ∀ a : A, Dder.liftKaehlerDifferential (KaehlerDifferential.D k A a) = Dder a`. Introduce `a`. Simplify using `[Derivation.liftKaehlerDifferential_comp_D]`.

Establish `hcomp : ∀ ω : KaehlerDifferential k A, ρA (Dder.liftKaehlerDifferential ω) = 0`. Establish `hker : (⊤ : Submodule A (KaehlerDifferential k A)) ≤ LinearMap.ker (ρA.toLinearMap.comp Dder.liftKaehlerDifferential)`. Rewrite using `[← KaehlerDifferential.span_range_derivation, Submodule.span_le]`. Introduce and unpack `y ⟨a, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply]`.

Use `show ρA (Dder.liftKaehlerDifferential (KaehlerDifferential.D k A a)) = 0`. Rewrite using `[hderivLift a, hDapp a]`. Conclude with `hkerel a`. Introduce `ω`. Establish `h2` using `hker (Submodule.mem_top : ω ∈ ⊤)`.

Rewrite `h2` using `[LinearMap.mem_ker, LinearMap.comp_apply]`. Conclude with `h2`. Establish `hcoef : ∀ i : n, bb.repr (KaehlerDifferential.D k A z) i ∈ IsLocalRing.maximalIdeal A` using `fun i => repr_mem_maximalIdeal_of_tmul_eq_zero bb (KaehlerDifferential.D k A z) h0 i`. Establish `hLb : ∀ i : n, ∃ u : A, u ∈ J ∧ Dder.liftKaehlerDifferential (bb i) = Ideal.Quotient.mk Jm u`. Introduce `i`.

Take `⟨u, hu⟩` from `Ideal.Quotient.mk_surjective (Dder.liftKaehlerDifferential (bb i))`. Use `⟨u, ?_, hu.symm⟩` and prove the remaining obligations. Establish `h1 : ρA (Ideal.Quotient.mk Jm u) = 0`. Rewrite using `[hu]`. Conclude with `hcomp (bb i)`.

Rewrite `h1` using `[hρmkA u]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h1`. Establish `hsum : Dder.liftKaehlerDifferential (KaehlerDifferential.D k A z) = 0` using `by conv_lhs => rw [← bb.sum_repr (KaehlerDifferential.D k A z)]`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Take `⟨u, huJ, hu⟩` from `hLb i`. Rewrite using `[map_smul, hu, hsmulmk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmulJ _ (hcoef i) u huJ`. Establish `hzval : Ideal.Quotient.mk Jm z = Dder.liftKaehlerDifferential (KaehlerDifferential.D k A z)`. Rewrite using `[hderivLift z, hDapp z, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero, sub_zero]`.

Establish `hfinal : Ideal.Quotient.mk Jm z = 0`. Rewrite using `[hzval, hsum]`. Rewrite using `[← hJmdef]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hfinal`.
-/
private theorem mem_maximalIdeal_mul_of_tmul_D_eq_zero (k : Type*) [CommRing k] (A : Type*)
    [CommRing A] [Algebra k A] [IsLocalRing A] {n : Type*} [Fintype n]
    (bb : Module.Basis n A (KaehlerDifferential k A))
    (J : Ideal A) (hJmax : J ≤ IsLocalRing.maximalIdeal A)
    [Algebra.FormallySmooth k (A ⧸ J)] (z : A) (hz : z ∈ J)
    (h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A z = 0) :
    z ∈ IsLocalRing.maximalIdeal A * J := by
  classical
  obtain ⟨Jm, hJmdef⟩ : ∃ Jm : Ideal A, Jm = IsLocalRing.maximalIdeal A * J := ⟨_, rfl⟩
  have hmulJ : ∀ c ∈ IsLocalRing.maximalIdeal A, ∀ u ∈ J, c * u ∈ Jm := by
    intro c hc u hu
    rw [hJmdef]
    exact Ideal.mul_mem_mul hc hu
  have hJmle : Jm ≤ J := by
    rw [hJmdef]
    exact Ideal.mul_le_right
  have hsmulg : ∀ (c : A) (x : A ⧸ Jm), c • x = Ideal.Quotient.mk Jm c * x := by
    intro c x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have hsmulmk : ∀ c u : A,
      c • (Ideal.Quotient.mk Jm u) = Ideal.Quotient.mk Jm (c * u) := by
    intro c u
    rw [hsmulg, ← map_mul]
  have hρ0 : ∀ a ∈ Jm, (Ideal.Quotient.mkₐ A J) a = 0 := by
    intro a ha
    show Ideal.Quotient.mk J a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJmle ha)
  let ρA : (A ⧸ Jm) →ₐ[A] (A ⧸ J) :=
    Ideal.Quotient.liftₐ Jm (Ideal.Quotient.mkₐ A J) hρ0
  let ρ : (A ⧸ Jm) →ₐ[k] (A ⧸ J) := ρA.restrictScalars k
  have hρmkA : ∀ a : A, ρA (Ideal.Quotient.mk Jm a) = Ideal.Quotient.mk J a := fun _ => rfl
  have hρmk : ∀ a : A, ρ (Ideal.Quotient.mk Jm a) = Ideal.Quotient.mk J a := fun _ => rfl
  have hρsurj : Function.Surjective ρ := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨Ideal.Quotient.mk Jm a, hρmk a⟩
  have hker2 : RingHom.ker (ρ : (A ⧸ Jm) →+* (A ⧸ J)) ^ 2 = ⊥ := by
    rw [pow_two]
    refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
    intro u hu v hv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have ha : a ∈ J := by
      have h1 : Ideal.Quotient.mk J a = 0 := by
        rw [← hρmk a]
        exact RingHom.mem_ker.mp hu
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have hb : b ∈ J := by
      have h1 : Ideal.Quotient.mk J b = 0 := by
        rw [← hρmk b]
        exact RingHom.mem_ker.mp hv
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    refine (Submodule.mem_bot _).mpr ?_
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hmulJ a (hJmax ha) b hb
  have hprod : ∀ u v : A ⧸ Jm, ρA u = 0 → ρA v = 0 → u * v = 0 := by
    intro u v hu hv
    have hmem : u * v ∈ RingHom.ker (ρ : (A ⧸ Jm) →+* (A ⧸ J)) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (RingHom.mem_ker.mpr hu) (RingHom.mem_ker.mpr hv)
    rw [hker2] at hmem
    simpa using hmem
  obtain ⟨σ, hσ⟩ : ∃ σ : (A ⧸ J) →ₐ[k] (A ⧸ Jm), ∀ c, ρ (σ c) = c := by
    refine ⟨Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id k (A ⧸ J)) ρ hρsurj ⟨2, hker2⟩, fun c => ?_⟩
    have h := Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id k (A ⧸ J)) ρ hρsurj ⟨2, hker2⟩
    have h2 := DFunLike.congr_fun h c
    simpa using h2
  have hρσ : ∀ c : A ⧸ J, ρA (σ c) = c := fun c => hσ c
  have hkerel : ∀ a : A,
      ρA (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) = 0 := by
    intro a
    rw [map_sub, hρmkA a, hρσ (Ideal.Quotient.mk J a), sub_self]
  have hmkJmsmul : ∀ (c : k) (a : A),
      Ideal.Quotient.mk Jm (c • a) = c • Ideal.Quotient.mk Jm a := by
    intro c a
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k A (A ⧸ Jm)]
  have hmkJsmul : ∀ (c : k) (a : A),
      Ideal.Quotient.mk J (c • a) = c • Ideal.Quotient.mk J a := by
    intro c a
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k A (A ⧸ J)]
  have hadd : ∀ a b : A,
      Ideal.Quotient.mk Jm (a + b) - σ (Ideal.Quotient.mk J (a + b))
        = (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
          + (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b)) := by
    intro a b
    simp only [map_add]
    ring
  have hsmulk : ∀ (c : k) (a : A),
      Ideal.Quotient.mk Jm (c • a) - σ (Ideal.Quotient.mk J (c • a))
        = (RingHom.id k) c • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) := by
    intro c a
    show Ideal.Quotient.mk Jm (c • a) - σ (Ideal.Quotient.mk J (c • a))
      = c • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
    rw [hmkJmsmul c a, hmkJsmul c a, map_smul, smul_sub]
  have hleib : ∀ a b : A,
      Ideal.Quotient.mk Jm (a * b) - σ (Ideal.Quotient.mk J (a * b))
        = a • (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b))
          + b • (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)) := by
    intro a b
    have hz2 := hprod (Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a))
      (Ideal.Quotient.mk Jm b - σ (Ideal.Quotient.mk J b)) (hkerel a) (hkerel b)
    rw [hsmulg a, hsmulg b]
    simp only [map_mul]
    linear_combination -hz2
  obtain ⟨Dder, hDapp⟩ : ∃ D : Derivation k A (A ⧸ Jm),
      ∀ a : A, D a = Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a) :=
    ⟨Derivation.mk'
      { toFun := fun a => Ideal.Quotient.mk Jm a - σ (Ideal.Quotient.mk J a)
        map_add' := hadd
        map_smul' := hsmulk } hleib, fun _ => rfl⟩
  have hderivLift : ∀ a : A,
      Dder.liftKaehlerDifferential (KaehlerDifferential.D k A a) = Dder a := by
    intro a
    simp [Derivation.liftKaehlerDifferential_comp_D]
  have hcomp : ∀ ω : KaehlerDifferential k A,
      ρA (Dder.liftKaehlerDifferential ω) = 0 := by
    have hker : (⊤ : Submodule A (KaehlerDifferential k A)) ≤
        LinearMap.ker (ρA.toLinearMap.comp Dder.liftKaehlerDifferential) := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
      rintro y ⟨a, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply]
      show ρA (Dder.liftKaehlerDifferential (KaehlerDifferential.D k A a)) = 0
      rw [hderivLift a, hDapp a]
      exact hkerel a
    intro ω
    have h2 := hker (Submodule.mem_top : ω ∈ ⊤)
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at h2
    exact h2
  have hcoef : ∀ i : n,
      bb.repr (KaehlerDifferential.D k A z) i ∈ IsLocalRing.maximalIdeal A :=
    fun i => repr_mem_maximalIdeal_of_tmul_eq_zero bb (KaehlerDifferential.D k A z) h0 i
  have hLb : ∀ i : n, ∃ u : A, u ∈ J ∧
      Dder.liftKaehlerDifferential (bb i) = Ideal.Quotient.mk Jm u := by
    intro i
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (Dder.liftKaehlerDifferential (bb i))
    refine ⟨u, ?_, hu.symm⟩
    have h1 : ρA (Ideal.Quotient.mk Jm u) = 0 := by
      rw [hu]
      exact hcomp (bb i)
    rw [hρmkA u] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hsum : Dder.liftKaehlerDifferential (KaehlerDifferential.D k A z) = 0 := by
    conv_lhs => rw [← bb.sum_repr (KaehlerDifferential.D k A z)]
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨u, huJ, hu⟩ := hLb i
    rw [map_smul, hu, hsmulmk, Ideal.Quotient.eq_zero_iff_mem]
    exact hmulJ _ (hcoef i) u huJ
  have hzval : Ideal.Quotient.mk Jm z
      = Dder.liftKaehlerDifferential (KaehlerDifferential.D k A z) := by
    rw [hderivLift z, hDapp z, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero, sub_zero]
  have hfinal : Ideal.Quotient.mk Jm z = 0 := by
    rw [hzval, hsum]
  rw [← hJmdef]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfinal

/- English proof (translation)
Establish `hsmeq : (IsLocalRing.maximalIdeal A • J : Ideal A) = IsLocalRing.maximalIdeal A * J`. Rewrite using `[Ideal.smul_eq_mul]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Establish `hstep : J ≤ Ideal.span (Set.range x) ⊔ IsLocalRing.maximalIdeal A • J`. Rewrite using `[hsmeq]`.

Introduce `y hy`. Establish `hy'` using `hspan y hy`. Rewrite `hy'` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `hy'`. Choose the witnesses or unpack the hypotheses as in `⟨c', hc'⟩ : ∃ c' : Fin r → A, ∀ i, IsLocalRing.residue A (c' i) = c i := by`.

Establish `hsurj : Function.Surjective (IsLocalRing.residue A)` using `Ideal.Quotient.mk_surjective`. Use `choose c' hc' using fun i => hsurj (c i)`. Conclude with `⟨c', hc'⟩`. Establish `hsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (∑ i, c' i * x i) = ∑ i, c i • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x i))`. Rewrite using `[map_sum, TensorProduct.tmul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (c' i) (x i), KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal, hc' i]`. Conclude with `hJmax (hxJ i)`. Establish `h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y - ∑ i, c' i * x i) = 0`. Rewrite using `[map_sub, TensorProduct.tmul_sub, hsum, hc, sub_self]`.

Establish `hmemJ : y - ∑ i, c' i * x i ∈ J` using `Submodule.sub_mem _ hy (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hxJ i))`. Establish `hsq` using `mem_maximalIdeal_mul_of_tmul_D_eq_zero k A bb J hJmax _ hmemJ h0`. Establish `hrw : y = (y - ∑ i, c' i * x i) + ∑ i, c' i * x i` using `by ring`. Rewrite using `[hrw]`. Use `Submodule.add_mem _ (Submodule.mem_sup_right hsq) (Submodule.mem_sup_left ?_)` and prove the remaining obligations.

Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`. Establish `hbotne : (⊥ : Ideal A) ≠ ⊤`. Introduce `hcon`. Establish `hmem1 : (1 : A) ∈ (⊥ : Ideal A)`. Rewrite using `[hcon]`.

Conclude with `Submodule.mem_top`. Establish `hz : (1 : A) = 0` using `by simp at hmem1`. Conclude with `one_ne_zero hz`. Conclude with `Submodule.le_of_le_smul_of_le_jacobson_bot hJfg (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) hbotne).ge hstep`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hxJ i`.
-/
private theorem ideal_eq_span_of_tmul_D_mem_span (k : Type*) [CommRing k] (A : Type*) [CommRing A]
    [Algebra k A] [IsLocalRing A] {n : Type*} [Fintype n]
    (bb : Module.Basis n A (KaehlerDifferential k A))
    (J : Ideal A) (hJfg : J.FG)
    (hJmax : J ≤ IsLocalRing.maximalIdeal A) [Algebra.FormallySmooth k (A ⧸ J)] (r : ℕ)
    (x : Fin r → A) (hxJ : ∀ i : Fin r, x i ∈ J)
    (hspan : ∀ y ∈ J,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin r =>
            (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x i))) :
    J = Ideal.span (Set.range x) := by
  classical
  have hsmeq : (IsLocalRing.maximalIdeal A • J : Ideal A)
      = IsLocalRing.maximalIdeal A * J := by
    rw [Ideal.smul_eq_mul]
  refine le_antisymm ?_ ?_
  · have hstep : J ≤ Ideal.span (Set.range x) ⊔ IsLocalRing.maximalIdeal A • J := by
      rw [hsmeq]
      intro y hy
      have hy' := hspan y hy
      rw [Submodule.mem_span_range_iff_exists_fun] at hy'
      obtain ⟨c, hc⟩ := hy'
      obtain ⟨c', hc'⟩ : ∃ c' : Fin r → A, ∀ i, IsLocalRing.residue A (c' i) = c i := by
        have hsurj : Function.Surjective (IsLocalRing.residue A) :=
          Ideal.Quotient.mk_surjective
        choose c' hc' using fun i => hsurj (c i)
        exact ⟨c', hc'⟩
      have hsum : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (∑ i, c' i * x i)
          = ∑ i, c i • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (x i)) := by
        rw [map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm (c' i) (x i),
          KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal, hc' i]
        exact hJmax (hxJ i)
      have h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y - ∑ i, c' i * x i) = 0 := by
        rw [map_sub, TensorProduct.tmul_sub, hsum, hc, sub_self]
      have hmemJ : y - ∑ i, c' i * x i ∈ J :=
        Submodule.sub_mem _ hy
          (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hxJ i))
      have hsq := mem_maximalIdeal_mul_of_tmul_D_eq_zero k A bb J hJmax _ hmemJ h0
      have hrw : y = (y - ∑ i, c' i * x i) + ∑ i, c' i * x i := by ring
      rw [hrw]
      refine Submodule.add_mem _ (Submodule.mem_sup_right hsq) (Submodule.mem_sup_left ?_)
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have hbotne : (⊥ : Ideal A) ≠ ⊤ := by
      intro hcon
      have hmem1 : (1 : A) ∈ (⊥ : Ideal A) := by
        rw [hcon]; exact Submodule.mem_top
      have hz : (1 : A) = 0 := by simp at hmem1
      exact one_ne_zero hz
    exact Submodule.le_of_le_smul_of_le_jacobson_bot hJfg
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) hbotne).ge hstep
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hxJ i

/- English proof (translation)
Establish `hgu : IsUnit (algebraMap S T₂ (g₁ * d))` using `IsLocalization.map_units (M := Submonoid.powers (g₁ * d)) T₂ ⟨g₁ * d, Submonoid.mem_powers _⟩`. Rewrite `hgu` using `[map_mul]`. Establish `hg1u : IsUnit (algebraMap S T₂ g₁)` using `isUnit_of_mul_isUnit_left hgu`. Establish `hFu : ∀ y : Submonoid.powers g₁, IsUnit (algebraMap S T₂ (y : S))`. Introduce and unpack `⟨y, m, rfl⟩`.

Use `show IsUnit (algebraMap S T₂ (g₁ ^ m))`. Rewrite using `[map_pow]`. Conclude with `hg1u.pow m`. Take `⟨F, hF⟩ : ∃ F : T₁ →+* T₂, F.comp (algebraMap S T₁) = algebraMap S T₂` from `⟨IsLocalization.lift (M := Submonoid.powers g₁) (S := T₁) hFu, RingHom.ext fun x => IsLocalization.lift_eq hFu x⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem map_eq_of_map_eq_of_away_mul {S : Type*} [CommRing S] {T₁ T₂ : Type*}
    [CommRing T₁] [CommRing T₂] [Algebra S T₁] [Algebra S T₂] (g₁ d : S)
    [IsLocalization (Submonoid.powers g₁) T₁]
    [IsLocalization (Submonoid.powers (g₁ * d)) T₂] (I J : Ideal S)
    (h : Ideal.map (algebraMap S T₁) I = Ideal.map (algebraMap S T₁) J) :
    Ideal.map (algebraMap S T₂) I = Ideal.map (algebraMap S T₂) J := by
  have hgu : IsUnit (algebraMap S T₂ (g₁ * d)) :=
    IsLocalization.map_units (M := Submonoid.powers (g₁ * d)) T₂
      ⟨g₁ * d, Submonoid.mem_powers _⟩
  rw [map_mul] at hgu
  have hg1u : IsUnit (algebraMap S T₂ g₁) := isUnit_of_mul_isUnit_left hgu
  have hFu : ∀ y : Submonoid.powers g₁, IsUnit (algebraMap S T₂ (y : S)) := by
    rintro ⟨y, m, rfl⟩
    show IsUnit (algebraMap S T₂ (g₁ ^ m))
    rw [map_pow]
    exact hg1u.pow m
  obtain ⟨F, hF⟩ : ∃ F : T₁ →+* T₂, F.comp (algebraMap S T₁) = algebraMap S T₂ :=
    ⟨IsLocalization.lift (M := Submonoid.powers g₁) (S := T₁) hFu,
      RingHom.ext fun x => IsLocalization.lift_eq hFu x⟩
  calc Ideal.map (algebraMap S T₂) I
      = Ideal.map F (Ideal.map (algebraMap S T₁) I) := by rw [Ideal.map_map, hF]
    _ = Ideal.map F (Ideal.map (algebraMap S T₁) J) := by rw [h]
    _ = Ideal.map (algebraMap S T₂) J := by rw [Ideal.map_map, hF]

/- English proof (translation)
Set `instKT : Algebra k T` to `((algebraMap S T).comp (algebraMap k S)).toAlgebra`. Set `instAlgebraMvPolynomial : Algebra (MvPolynomial ι k) T` to `((algebraMap S T).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra`. Establish `instTkS : IsScalarTower k S T` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `instTPS : IsScalarTower (MvPolynomial ι k) S T` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `instTkP : IsScalarTower k (MvPolynomial ι k) T` using `IsScalarTower.of_algebraMap_eq fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply k S T x, IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]`. Both sides reduce to the same expression. Establish `instFEST : Algebra.FormallyEtale S T` using `Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers g)`. Establish `instFEPT : Algebra.FormallyEtale (MvPolynomial ι k) T` using `Algebra.FormallyEtale.comp (MvPolynomial ι k) S T`. Establish `instFSkT : Algebra.FormallySmooth k T` using `Algebra.FormallySmooth.comp k (MvPolynomial ι k) T`.

Establish `hdet' : IsUnit ((basisKaehler k ι T).det fun i : ι => KaehlerDifferential.D k T (algebraMap S T (w i)))`. Rewrite using `[← algebraMap_det_basisKaehler k ι S T w]`. Conclude with `hdet`. Establish `h` using `formallyEtale_aeval_of_isUnit_det (basisKaehler k ι T) (fun i : ι => algebraMap S T (w i)) hdet'`. Conclude with `h`.
-/
private theorem formallyEtale_away_of_isUnit_det (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (g : S) (T : Type*) [CommRing T] [Algebra S T] [IsLocalization (Submonoid.powers g) T]
    (w : ι → S)
    (hdet : IsUnit (algebraMap S T
      ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))) :
    @Algebra.FormallyEtale (MvPolynomial ι k) T _ _
      (RingHom.toAlgebra
        (MvPolynomial.eval₂Hom ((algebraMap S T).comp (algebraMap k S))
          (fun j : ι => algebraMap S T (w j)))) := by
  classical
  let instKT : Algebra k T := ((algebraMap S T).comp (algebraMap k S)).toAlgebra
  let instAlgebraMvPolynomial : Algebra (MvPolynomial ι k) T :=
    ((algebraMap S T).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instTkS : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTPS : IsScalarTower (MvPolynomial ι k) S T :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTkP : IsScalarTower k (MvPolynomial ι k) T :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S T x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEST : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers g)
  have instFEPT : Algebra.FormallyEtale (MvPolynomial ι k) T :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S T
  have instFSkT : Algebra.FormallySmooth k T :=
    Algebra.FormallySmooth.comp k (MvPolynomial ι k) T
  have hdet' : IsUnit ((basisKaehler k ι T).det
      fun i : ι => KaehlerDifferential.D k T (algebraMap S T (w i))) := by
    rw [← algebraMap_det_basisKaehler k ι S T w]
    exact hdet
  have h := formallyEtale_aeval_of_isUnit_det (basisKaehler k ι T)
    (fun i : ι => algebraMap S T (w i)) hdet'
  exact h

end

section

variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  [IsNoetherianRing S] (I q : Ideal S) [q.IsPrime]

/- English proof (translation)
Establish `instFEloc : Algebra.FormallyEtale S A` using `Algebra.FormallyEtale.of_isLocalization (M := q.primeCompl)`. Set `instPA : Algebra (MvPolynomial ι k) A` to `((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra`. Establish `instT1 : IsScalarTower (MvPolynomial ι k) S A` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) A` using `IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply k S A x, IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]`.

Both sides reduce to the same expression. Establish `instFEPA : Algebra.FormallyEtale (MvPolynomial ι k) A` using `Algebra.FormallyEtale.comp (MvPolynomial ι k) S A`. Establish `hmapq : Ideal.map (algebraMap S A) q = IsLocalRing.maximalIdeal A` using `IsLocalization.AtPrime.map_eq_maximalIdeal q A`. Establish `hJAm : Ideal.map (algebraMap S A) I ≤ IsLocalRing.maximalIdeal A`. Rewrite using `[← hmapq]`.

Conclude with `Ideal.map_mono hIq`. Take `⟨tF, htF⟩ : I.FG` from `IsNoetherian.noetherian I`. Establish `hspanI : Ideal.span (↑(tF.image (algebraMap S A)) : Set A) = Ideal.map (algebraMap S A) I`. Rewrite using `[Finset.coe_image, ← htF, Ideal.map_span]`. Take `⟨bset, hbsub, hbspan, hbind⟩` from `exists_linearIndependent (K := IsLocalRing.ResidueField A) (t := ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a) '' (↑(tF.image (algebraMap S A)) : Set A)))`.

Establish `hbfin : bset.Finite` using `Set.Finite.subset (Set.Finite.image _ (Finset.finite_toSet _)) hbsub`. Set `_ : Fintype bset` to `hbfin.fintype`. Use `choose pre hpre1 hpre2 using fun v : bset => hbsub v.2`. Establish `hpre1' : ∀ v : bset, ∃ t : S, t ∈ tF ∧ algebraMap S A t = pre v`. Introduce `v`.

Establish `hv` using `hpre1 v`. Rewrite `hv` using `[Finset.mem_coe, Finset.mem_image]`. Take `⟨t, ht, hts⟩` from `hv`. Conclude with `⟨t, ht, hts⟩`. Use `choose pres hpres1 hpres2 using hpre1'`.

Take `⟨s, hs⟩ : ∃ s : Fin (Fintype.card bset) → S, ∀ i, s i = pres ((Fintype.equivFin bset).symm i)` from `⟨_, fun _ => rfl⟩`. Establish `hsI : ∀ i, s i ∈ I`. Introduce `i`. Rewrite using `[hs i, ← htF]`. Conclude with `Submodule.subset_span (Finset.mem_coe.mpr (hpres1 _))`.

Establish `hfun : (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (s i))) = fun i : Fin (Fintype.card bset) => (((Fintype.equivFin bset).symm i : bset) : IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)`. Use function extensionality and compare the values at `i`. Rewrite using `[hs i, hpres2]`. Conclude with `hpre2 _`. Establish `hind : LinearIndependent (IsLocalRing.ResidueField A) (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (s i)))`.

Rewrite using `[hfun]`. Conclude with `hbind.comp _ (Fintype.equivFin bset).symm.injective`. Establish `hrange : Set.range (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (s i))) = bset`. Rewrite using `[hfun]`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `((Fintype.equivFin bset).symm i).2`. Introduce `hv`. Conclude with `⟨(Fintype.equivFin bset) ⟨v, hv⟩, by simp⟩`.

Establish `hxJ : ∀ i, algebraMap S A (s i) ∈ Ideal.map (algebraMap S A) I` using `fun i => Ideal.mem_map_of_mem _ (hsI i)`. Establish `hgen : ∀ y ∈ Ideal.map (algebraMap S A) I, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈ Submodule.span (IsLocalRing.ResidueField A) ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a) '' (↑(tF.image (algebraMap S A)) : Set A) …`. Introduce `y hy`. Rewrite `hy` using `[← hspanI]`. Take `⟨f, -, hf⟩` from `Submodule.mem_span_finset.mp hy`.

Rewrite using `[← hf, map_sum, TensorProduct.tmul_sum]`. Use `Submodule.sum_mem _ fun a ha => ?_` and prove the remaining obligations. Establish `ham : a ∈ IsLocalRing.maximalIdeal A`. Use `hJAm ?_` and prove the remaining obligations. Rewrite using `[← hspanI]`.

Conclude with `Submodule.subset_span (Finset.mem_coe.mpr ha)`. Establish `heq : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f a • a) = IsLocalRing.residue A (f a) • ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a)`. Rewrite using `[smul_eq_mul, mul_comm, KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal]`. Conclude with `ham`. Rewrite using `[heq]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Finset.mem_coe.mpr ha, rfl⟩)`. Establish `hspanx : ∀ y ∈ Ideal.map (algebraMap S A) I, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈ Submodule.span (IsLocalRing.ResidueField A) (Set.range fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap …`. Introduce `y hy`. Rewrite using `[hrange, hbspan]`. Conclude with `hgen y hy`.

Establish `hJAeq : Ideal.map (algebraMap S A) I = Ideal.span (Set.range fun i : Fin (Fintype.card bset) => algebraMap S A (s i))` using `ideal_eq_span_of_tmul_D_mem_span k A (basisKaehler k ι A) (Ideal.map (algebraMap S A) I) (IsNoetherian.noetherian _) hJAm (Fintype.card bset) (fun i => algebraMap S A (s i)) hxJ hspanx`. Take `⟨bkk, hbk⟩ : ∃ bkk : Module.Basis ι (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A), ∀ i, bkk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (basisKaehler k ι A i)` from `⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (basisKaehler k ι A), fun i => by simp⟩`. Take `⟨Jst, B, hbasisInl, hbasisInr⟩` from `exists_basis_sum_of_linearIndependent bkk (Fintype.card bset) (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (s i))) hind`. Establish `hcard1 : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card (Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst})` using `Module.finrank_eq_card_basis B`. Establish `hcard2 : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card ι` using `Module.finrank_eq_card_basis bkk`.

Establish `hcard3 : Fintype.card {j : ι // j ∈ Jst} + Fintype.card {j : ι // ¬ (j ∈ Jst)} = Fintype.card ι`. Rewrite using `[← Fintype.card_sum]`. Conclude with `Fintype.card_congr (Equiv.sumCompl (fun j : ι => j ∈ Jst))`. Rewrite `hcard1` using `[Fintype.card_sum, Fintype.card_fin]`. Establish `hcard4 : Fintype.card {j : ι // ¬ (j ∈ Jst)} = Fintype.card bset` using `by omega`.

Establish `e : {j : ι // ¬ (j ∈ Jst)} ≃ Fin (Fintype.card bset)` using `Fintype.equivFinOfCardEq hcard4`. Take `⟨τ, hτl, hτr⟩ : ∃ τ : Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst} ≃ ι, (∀ l : Fin (Fintype.card bset), τ (Sum.inl l) = ((e.symm l : ι))) ∧ (∀ j : {j : ι // j ∈ Jst}, τ (Sum.inr j) = (j : ι))` from `⟨(Equiv.sumCongr e.symm (Equiv.refl {j : ι // j ∈ Jst})).trans ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun j : ι => j ∈ Jst))), fun l => rfl, fun j => rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = coord k ι S j) ∧ (∀ x : {j : ι // ¬ (j ∈ Jst)}, w (x : ι) = s (e x)) := by`. Use `⟨fun j => if hj : j ∈ Jst then coord k ι S j else s (e ⟨j, hj⟩), fun j hj => ?_, fun x => ?_⟩` and prove the remaining obligations. Conclude with `dif_pos hj`.

Conclude with `dif_neg x.2`. Establish `hbasisApply : ∀ x : Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst}, B x = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (w (τ x)))`. Introduce and unpack `(l | j)`. Rewrite using `[hbasisInl l, hτl l, hwn (e.symm l), Equiv.apply_symm_apply]`. Rewrite using `[hbasisInr j, hτr j, hwJ (j : ι) j.2, hbk (j : ι), basisKaehler_apply, algebraMap_coord]`.

Establish `hB'G : ∀ i : ι, (B.reindex τ) i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A (w i))`. Introduce `i`. Rewrite using `[Module.Basis.reindex_apply, hbasisApply (τ.symm i), Equiv.apply_symm_apply]`. Establish `hdetne` using `residue_det_ne_zero_of_tmul_eq_basis (basisKaehler k ι A) (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) (B.reindex τ) hB'G`. Establish `hdetA : algebraMap S A ((basisKaehler k ι S).det (fun i : ι => KaehlerDifferential.D k S (w i))) = (basisKaehler k ι A).det (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i)))` using `algebraMap_det_basisKaehler k ι S A w`.

Establish `hg₀q : ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)) ∉ q`. Introduce `hgq`. Apply `hdetne` to reduce the goal to its premises. Rewrite using `[← hdetA, IsLocalRing.residue_eq_zero_iff, ← hmapq]`. Conclude with `Ideal.mem_map_of_mem _ hgq`.

Establish `hspanA : Ideal.map (algebraMap S A) (Ideal.span (w '' (↑(Jstᶜ) : Set ι))) = Ideal.map (algebraMap S A) I`. Rewrite using `[Ideal.map_span, hJAeq]`. Use `congr 1`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, ⟨j, hj, rfl⟩, rfl⟩`. Establish `hj' : ¬ (j ∈ Jst)` using `Finset.mem_compl.mp (Finset.mem_coe.mp hj)`. Establish `hwj : w j = s (e ⟨j, hj'⟩)` using `hwn ⟨j, hj'⟩`. Conclude with `⟨e ⟨j, hj'⟩, by rw [hwj]⟩`. Introduce and unpack `⟨i, rfl⟩`.

Use `⟨w ((e.symm i : ι)), ⟨(e.symm i : ι), ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_coe.mpr (Finset.mem_compl.mpr (e.symm i).2)`. Establish `hwj : w ((e.symm i : ι)) = s (e (e.symm i))` using `hwn (e.symm i)`. Rewrite using `[hwj, Equiv.apply_symm_apply]`. Take `⟨g₁, hg₁q, hg₁eq⟩` from `exists_away_map_ideal_eq q A (Ideal.span (w '' (↑(Jstᶜ) : Set ι))) I (Submodule.fg_span (Set.Finite.image w (Finset.finite_toSet _))) (IsNoetherian.noetherian I) hspanA`.

Use `⟨g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)), w, Jstᶜ, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Break down `Ideal.IsPrime.mem_or_mem ‹q.IsPrime› hmem with h1 | h2` into its components or cases. Conclude with `hg₁q h1`. Conclude with `hg₀q h2`.

Introduce `j hj`. Establish `hj' : ¬ (j ∈ Jst)` using `Finset.mem_compl.mp hj`. Establish `hwj : w j = s (e ⟨j, hj'⟩)` using `hwn ⟨j, hj'⟩`. Rewrite using `[hwj]`. Conclude with `hsI _`.

Conclude with `map_eq_of_map_eq_of_away_mul g₁ ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)) _ _ hg₁eq`. Introduce `j hj`. Establish `hj' : j ∈ Jst`. Assume the negation of the conclusion as `hc`. Conclude with `hj (Finset.mem_compl.mpr hc)`.

Conclude with `⟨j, hwJ j hj'⟩`. Establish `hu : IsUnit (algebraMap S (Localization.Away (g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))) (g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))))` using `IsLocalization.map_units _ ⟨_, Submonoid.mem_powers _⟩`. Rewrite `hu` using `[map_mul]`. Conclude with `isUnit_of_mul_isUnit_right hu`.
-/
theorem exists_away_ideal_eq_span_and_isUnit_det
    (A : Type*) [CommRing A] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra.FormallySmooth k (A ⧸ Ideal.map (algebraMap S A) I)]
    (hIq : I ≤ q) :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S (Localization.Away g)) (Ideal.span (w '' (↑T : Set ι))) =
        Ideal.map (algebraMap S (Localization.Away g)) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      IsUnit (algebraMap S (Localization.Away g)
        ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))) := by
  classical
  have instFEloc : Algebra.FormallyEtale S A :=
    Algebra.FormallyEtale.of_isLocalization (M := q.primeCompl)
  let instPA : Algebra (MvPolynomial ι k) A :=
    ((algebraMap S A).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instT1 : IsScalarTower (MvPolynomial ι k) S A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k (MvPolynomial ι k) A :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S A x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEPA : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S A
  have hmapq : Ideal.map (algebraMap S A) q = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q A
  have hJAm : Ideal.map (algebraMap S A) I ≤ IsLocalRing.maximalIdeal A := by
    rw [← hmapq]
    exact Ideal.map_mono hIq
  obtain ⟨tF, htF⟩ : I.FG := IsNoetherian.noetherian I
  have hspanI : Ideal.span (↑(tF.image (algebraMap S A)) : Set A)
      = Ideal.map (algebraMap S A) I := by
    rw [Finset.coe_image, ← htF, Ideal.map_span]
  obtain ⟨bset, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent (K := IsLocalRing.ResidueField A)
      (t := ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A a) '' (↑(tF.image (algebraMap S A)) : Set A)))
  have hbfin : bset.Finite :=
    Set.Finite.subset (Set.Finite.image _ (Finset.finite_toSet _)) hbsub
  let _ : Fintype bset := hbfin.fintype
  choose pre hpre1 hpre2 using fun v : bset => hbsub v.2
  have hpre1' : ∀ v : bset, ∃ t : S, t ∈ tF ∧ algebraMap S A t = pre v := by
    intro v
    have hv := hpre1 v
    rw [Finset.mem_coe, Finset.mem_image] at hv
    obtain ⟨t, ht, hts⟩ := hv
    exact ⟨t, ht, hts⟩
  choose pres hpres1 hpres2 using hpre1'
  obtain ⟨s, hs⟩ : ∃ s : Fin (Fintype.card bset) → S,
      ∀ i, s i = pres ((Fintype.equivFin bset).symm i) := ⟨_, fun _ => rfl⟩
  have hsI : ∀ i, s i ∈ I := by
    intro i
    rw [hs i, ← htF]
    exact Submodule.subset_span (Finset.mem_coe.mpr (hpres1 _))
  have hfun : (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i)))
      = fun i : Fin (Fintype.card bset) =>
        (((Fintype.equivFin bset).symm i : bset) :
          IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) := by
    funext i
    rw [hs i, hpres2]
    exact hpre2 _
  have hind : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) := by
    rw [hfun]
    exact hbind.comp _ (Fintype.equivFin bset).symm.injective
  have hrange : Set.range (fun i : Fin (Fintype.card bset) =>
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) = bset := by
    rw [hfun]
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin bset).symm i).2
    · intro hv
      exact ⟨(Fintype.equivFin bset) ⟨v, hv⟩, by simp⟩
  have hxJ : ∀ i, algebraMap S A (s i) ∈ Ideal.map (algebraMap S A) I := fun i =>
    Ideal.mem_map_of_mem _ (hsI i)
  have hgen : ∀ y ∈ Ideal.map (algebraMap S A) I,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          ((fun a : A => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A a) '' (↑(tF.image (algebraMap S A)) : Set A)) := by
    intro y hy
    rw [← hspanI] at hy
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hy
    rw [← hf, map_sum, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have ham : a ∈ IsLocalRing.maximalIdeal A := by
      refine hJAm ?_
      rw [← hspanI]
      exact Submodule.subset_span (Finset.mem_coe.mpr ha)
    have heq : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f a • a)
        = IsLocalRing.residue A (f a) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a) := by
      rw [smul_eq_mul, mul_comm,
        KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal]
      exact ham
    rw [heq]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨a, Finset.mem_coe.mpr ha, rfl⟩)
  have hspanx : ∀ y ∈ Ideal.map (algebraMap S A) I,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin (Fintype.card bset) =>
            (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
              KaehlerDifferential.D k A (algebraMap S A (s i))) := by
    intro y hy
    rw [hrange, hbspan]
    exact hgen y hy
  have hJAeq : Ideal.map (algebraMap S A) I
      = Ideal.span (Set.range fun i : Fin (Fintype.card bset) => algebraMap S A (s i)) :=
    ideal_eq_span_of_tmul_D_mem_span k A (basisKaehler k ι A) (Ideal.map (algebraMap S A) I)
      (IsNoetherian.noetherian _) hJAm
      (Fintype.card bset) (fun i => algebraMap S A (s i)) hxJ hspanx
  obtain ⟨bkk, hbk⟩ : ∃ bkk : Module.Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      ∀ i, bkk i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (basisKaehler k ι A i) :=
    ⟨Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (basisKaehler k ι A),
      fun i => by simp⟩
  obtain ⟨Jst, B, hbasisInl, hbasisInr⟩ := exists_basis_sum_of_linearIndependent bkk (Fintype.card bset)
    (fun i : Fin (Fintype.card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (s i))) hind
  have hcard1 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)
      = Fintype.card (Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst}) :=
    Module.finrank_eq_card_basis B
  have hcard2 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) = Fintype.card ι :=
    Module.finrank_eq_card_basis bkk
  have hcard3 : Fintype.card {j : ι // j ∈ Jst} + Fintype.card {j : ι // ¬ (j ∈ Jst)}
      = Fintype.card ι := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun j : ι => j ∈ Jst))
  rw [Fintype.card_sum, Fintype.card_fin] at hcard1
  have hcard4 : Fintype.card {j : ι // ¬ (j ∈ Jst)} = Fintype.card bset := by omega
  have e : {j : ι // ¬ (j ∈ Jst)} ≃ Fin (Fintype.card bset) := Fintype.equivFinOfCardEq hcard4
  obtain ⟨τ, hτl, hτr⟩ : ∃ τ : Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst} ≃ ι,
      (∀ l : Fin (Fintype.card bset), τ (Sum.inl l) = ((e.symm l : ι))) ∧
      (∀ j : {j : ι // j ∈ Jst}, τ (Sum.inr j) = (j : ι)) :=
    ⟨(Equiv.sumCongr e.symm (Equiv.refl {j : ι // j ∈ Jst})).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun j : ι => j ∈ Jst))),
      fun l => rfl, fun j => rfl⟩
  obtain ⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = coord k ι S j) ∧
      (∀ x : {j : ι // ¬ (j ∈ Jst)}, w (x : ι) = s (e x)) := by
    refine ⟨fun j => if hj : j ∈ Jst then coord k ι S j else s (e ⟨j, hj⟩),
      fun j hj => ?_, fun x => ?_⟩
    · exact dif_pos hj
    · exact dif_neg x.2
  have hbasisApply : ∀ x : Fin (Fintype.card bset) ⊕ {j : ι // j ∈ Jst},
      B x = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (w (τ x))) := by
    rintro (l | j)
    · rw [hbasisInl l, hτl l, hwn (e.symm l), Equiv.apply_symm_apply]
    · rw [hbasisInr j, hτr j, hwJ (j : ι) j.2, hbk (j : ι), basisKaehler_apply,
        algebraMap_coord]
  have hB'G : ∀ i : ι, (B.reindex τ) i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A (w i)) := by
    intro i
    rw [Module.Basis.reindex_apply, hbasisApply (τ.symm i), Equiv.apply_symm_apply]
  have hdetne := residue_det_ne_zero_of_tmul_eq_basis (basisKaehler k ι A)
    (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) (B.reindex τ) hB'G
  have hdetA : algebraMap S A ((basisKaehler k ι S).det
      (fun i : ι => KaehlerDifferential.D k S (w i)))
      = (basisKaehler k ι A).det
        (fun i : ι => KaehlerDifferential.D k A (algebraMap S A (w i))) :=
    algebraMap_det_basisKaehler k ι S A w
  have hg₀q : ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)) ∉ q := by
    intro hgq
    apply hdetne
    rw [← hdetA, IsLocalRing.residue_eq_zero_iff, ← hmapq]
    exact Ideal.mem_map_of_mem _ hgq
  have hspanA : Ideal.map (algebraMap S A) (Ideal.span (w '' (↑(Jstᶜ) : Set ι)))
      = Ideal.map (algebraMap S A) I := by
    rw [Ideal.map_span, hJAeq]
    congr 1
    ext v
    constructor
    · rintro ⟨u, ⟨j, hj, rfl⟩, rfl⟩
      have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp (Finset.mem_coe.mp hj)
      have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
      exact ⟨e ⟨j, hj'⟩, by rw [hwj]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨w ((e.symm i : ι)), ⟨(e.symm i : ι), ?_, rfl⟩, ?_⟩
      · exact Finset.mem_coe.mpr (Finset.mem_compl.mpr (e.symm i).2)
      · have hwj : w ((e.symm i : ι)) = s (e (e.symm i)) := hwn (e.symm i)
        rw [hwj, Equiv.apply_symm_apply]
  obtain ⟨g₁, hg₁q, hg₁eq⟩ := exists_away_map_ideal_eq q A
    (Ideal.span (w '' (↑(Jstᶜ) : Set ι))) I
    (Submodule.fg_span (Set.Finite.image w (Finset.finite_toSet _)))
    (IsNoetherian.noetherian I) hspanA
  refine ⟨g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)), w,
    Jstᶜ, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹q.IsPrime› hmem with h1 | h2
    · exact hg₁q h1
    · exact hg₀q h2
  · intro j hj
    have hj' : ¬ (j ∈ Jst) := Finset.mem_compl.mp hj
    have hwj : w j = s (e ⟨j, hj'⟩) := hwn ⟨j, hj'⟩
    rw [hwj]
    exact hsI _
  · exact map_eq_of_map_eq_of_away_mul g₁
      ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)) _ _ hg₁eq
  · intro j hj
    have hj' : j ∈ Jst := by
      by_contra hc
      exact hj (Finset.mem_compl.mpr hc)
    exact ⟨j, hwJ j hj'⟩
  · have hu : IsUnit (algebraMap S
        (Localization.Away (g₁ *
          ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))))
        (g₁ * ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))) :=
      IsLocalization.map_units _ ⟨_, Submonoid.mem_powers _⟩
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu

/- English proof (translation)
Take `⟨g, w, T, hgq, hwI, hmap, hcoord, hdet⟩` from `exists_away_ideal_eq_span_and_isUnit_det k ι S I q A hIq`. Conclude with `⟨g, w, T, hgq, hwI, hmap, hcoord, formallyEtale_away_of_isUnit_det k ι S g (Localization.Away g) w hdet⟩`.
-/
theorem exists_away_ideal_eq_span_and_formallyEtale
    (A : Type*) [CommRing A] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra.FormallySmooth k (A ⧸ Ideal.map (algebraMap S A) I)]
    (hIq : I ≤ q) :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S (Localization.Away g)) (Ideal.span (w '' (↑T : Set ι))) =
        Ideal.map (algebraMap S (Localization.Away g)) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      @Algebra.FormallyEtale (MvPolynomial ι k) (Localization.Away g) _ _
        (RingHom.toAlgebra
          (MvPolynomial.eval₂Hom
            ((algebraMap S (Localization.Away g)).comp (algebraMap k S))
            (fun j : ι => algebraMap S (Localization.Away g) (w j)))) := by
  classical
  obtain ⟨g, w, T, hgq, hwI, hmap, hcoord, hdet⟩ :=
    exists_away_ideal_eq_span_and_isUnit_det k ι S I q A hIq
  exact ⟨g, w, T, hgq, hwI, hmap, hcoord,
    formallyEtale_away_of_isUnit_det k ι S g (Localization.Away g) w hdet⟩

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
