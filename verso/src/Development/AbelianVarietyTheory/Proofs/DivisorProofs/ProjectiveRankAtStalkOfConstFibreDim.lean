import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConstFibreFree

/- English proof (translation)
Rewrite using `[← (TensorProduct.AlgebraTensorModule.cancelBaseChange O k K K M).finrank_eq]`. Conclude with `Module.finrank_baseChange`.
-/
theorem finrank_tensor_tower (O k K M : Type) [CommRing O] [Field k] [Field K] [Algebra O k]
    [Algebra O K] [Algebra k K] [IsScalarTower O k K] [AddCommGroup M] [Module O M]
    [Module.Finite O M] :
    Module.finrank K (K ⊗[O] M) = Module.finrank k (k ⊗[O] M) := by
  rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange O k K K M).finrank_eq]
  exact Module.finrank_baseChange

/- English proof (translation)
Set `q` to `IsLocalRing.closedPoint O`. Set `φ : IsLocalRing.ResidueField O →+* q.asIdeal.ResidueField` to `Ideal.Quotient.lift _ (algebraMap O q.asIdeal.ResidueField) fun a ha => by`. Rewrite using `[← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]`. Conclude with `ha`. Use `letI : Algebra (IsLocalRing.ResidueField O) q.asIdeal.ResidueField := φ.toAlgebra`.

Use `haveI : IsScalarTower O (IsLocalRing.ResidueField O) q.asIdeal.ResidueField := IsScalarTower.of_algebraMap_eq fun a => (Ideal.Quotient.lift_mk _ _ _).symm`. Conclude with `finrank_tensor_tower O _ _ M`.
-/
theorem fibreDim_closedPoint (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] :
    fibreDim M (IsLocalRing.closedPoint O) =
      Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] M) := by
  let q := IsLocalRing.closedPoint O
  let φ : IsLocalRing.ResidueField O →+* q.asIdeal.ResidueField :=
    Ideal.Quotient.lift _ (algebraMap O q.asIdeal.ResidueField) fun a ha => by
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]; exact ha
  letI : Algebra (IsLocalRing.ResidueField O) q.asIdeal.ResidueField := φ.toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.Quotient.lift_mk _ _ _).symm
  exact finrank_tensor_tower O _ _ M

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩`. Consider the case `tmul c m`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective c`. Use `⟨a • m, ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Consider the case `add y z hy hz`. Take `⟨m₁, h₁⟩` from `hy`. Take `⟨m₂, h₂⟩` from `hz`.

Conclude with `⟨m₁ + m₂, by rw [TensorProduct.tmul_add, h₁, h₂]⟩`.
-/
theorem exists_one_tmul (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M] [Module O M]
    (y : IsLocalRing.ResidueField O ⊗[O] M) : ∃ m : M, (1 : IsLocalRing.ResidueField O) ⊗ₜ[O] m = y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul c m =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨a • m, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  | add y z hy hz =>
    obtain ⟨m₁, h₁⟩ := hy
    obtain ⟨m₂, h₂⟩ := hz
    exact ⟨m₁ + m₂, by rw [TensorProduct.tmul_add, h₁, h₂]⟩

/- English proof (translation)
Set `k` to `IsLocalRing.ResidueField O`. Establish `hk : Module.finrank k (k ⊗[O] M) = n` using `(fibreDim_closedPoint O M).symm.trans (h _)`. Set `b : Module.Basis (Fin n) k (k ⊗[O] M)` to `Module.finBasisOfFinrankEq k _ hk`. Use `choose f hf using fun i => exists_one_tmul O M (b i)`. Set `g : (Fin n → O) →ₗ[O] M` to `Fintype.linearCombination O f`.

Establish `hg : Function.Surjective g`. Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination]`. Conclude with `IsLocalRing.span_eq_top_of_tmul_eq_basis f b hf`. Establish `hinj : Function.Injective g`. Set `q₀ : PrimeSpectrum O` to `⟨⊥, Ideal.bot_prime⟩`.

Set `K` to `q₀.asIdeal.ResidueField`. Establish `hK : Module.finrank K (K ⊗[O] M) = n` using `h q₀`. Set `gK` to `g.baseChange K`. Establish `hgK : Function.Surjective gK` using `LinearMap.lTensor_surjective K hg`. Establish `hdim : Module.finrank K (K ⊗[O] (Fin n → O)) = Module.finrank K (K ⊗[O] M)`.

Rewrite using `[hK, Module.finrank_baseChange, Module.finrank_fin_fun]`. Establish `hgKi : Function.Injective gK` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hgK`. Establish `hO : Function.Injective (algebraMap O K)`. Rewrite using `[RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx`. Establish `h1 : gK ((1 : K) ⊗ₜ x) = 0` using `by simp [gK, hx]`. Establish `h2 : (1 : K) ⊗ₜ[O] x = 0` using `hgKi (h1.trans (map_zero gK).symm)`. Establish `h3` using `congrArg (TensorProduct.piScalarRight O K K (Fin n)) h2`. Use function extensionality and compare the values at `i`.

Establish `h4` using `congrFun h3 i`. Simplify using `at h4`. Conclude with `hO (by simpa using h4)`. Conclude with `⟨(LinearEquiv.ofBijective g ⟨hinj, hg⟩).symm⟩`.
-/
theorem nonempty_equiv_fin (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type)
    [AddCommGroup M] [Module O M] [Module.Finite O M] (n : ℕ)
    (h : ∀ q : PrimeSpectrum O, fibreDim M q = n) : Nonempty (M ≃ₗ[O] (Fin n → O)) := by
  let k := IsLocalRing.ResidueField O
  have hk : Module.finrank k (k ⊗[O] M) = n :=
    (fibreDim_closedPoint O M).symm.trans (h _)
  let b : Module.Basis (Fin n) k (k ⊗[O] M) := Module.finBasisOfFinrankEq k _ hk
  choose f hf using fun i => exists_one_tmul O M (b i)
  let g : (Fin n → O) →ₗ[O] M := Fintype.linearCombination O f
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis f b hf
  have hinj : Function.Injective g := by
    let q₀ : PrimeSpectrum O := ⟨⊥, Ideal.bot_prime⟩
    let K := q₀.asIdeal.ResidueField
    have hK : Module.finrank K (K ⊗[O] M) = n := h q₀
    let gK := g.baseChange K
    have hgK : Function.Surjective gK := LinearMap.lTensor_surjective K hg
    have hdim : Module.finrank K (K ⊗[O] (Fin n → O)) = Module.finrank K (K ⊗[O] M) := by
      rw [hK, Module.finrank_baseChange, Module.finrank_fin_fun]
    have hgKi : Function.Injective gK :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hgK
    have hO : Function.Injective (algebraMap O K) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : gK ((1 : K) ⊗ₜ x) = 0 := by simp [gK, hx]
    have h2 : (1 : K) ⊗ₜ[O] x = 0 := hgKi (h1.trans (map_zero gK).symm)
    have h3 := congrArg (TensorProduct.piScalarRight O K K (Fin n)) h2
    funext i
    have h4 := congrFun h3 i
    simp at h4
    exact hO (by simpa using h4)
  exact ⟨(LinearEquiv.ofBijective g ⟨hinj, hg⟩).symm⟩

/- English proof (translation)
Introduce `O _ _ _ M _ _ _ n h`. Take `⟨e⟩` from `nonempty_equiv_fin O M n h`. Use `haveI : Module.Free O M := Module.Free.of_equiv e.symm`. Use `⟨inferInstance, fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.rankAtStalk_eq]`.

Conclude with `h q`.
-/
theorem projective_and_rankAtStalk_of_fibreDim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
      [Module.Finite O M] (n : ℕ), (∀ q : PrimeSpectrum O, fibreDim M q = n) →
      Module.Projective O M ∧ ∀ q : PrimeSpectrum O, Module.rankAtStalk M q = n := by
  intro O _ _ _ M _ _ _ n h
  obtain ⟨e⟩ := nonempty_equiv_fin O M n h
  haveI : Module.Free O M := Module.Free.of_equiv e.symm
  refine ⟨inferInstance, fun q => ?_⟩
  rw [Module.rankAtStalk_eq]
  exact h q

end GlobalTheory.ConstFibreFree
