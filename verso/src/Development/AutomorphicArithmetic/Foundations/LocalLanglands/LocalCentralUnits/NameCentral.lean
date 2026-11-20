import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.PairCheckThreeTwo
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur

open CategoryTheory Polynomial Matrix GlobalTheory.GLq

namespace UpperTheory.Zero.LLC

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[GeneralLinearGroup.scalar, Matrix.scalar_apply, mul_comm]`.
-/
private theorem scalar_comm {g n : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (x : Gn g n) :
    GeneralLinearGroup.scalar (Fin n) c * x = x * GeneralLinearGroup.scalar (Fin n) c := by
  ext i j
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, mul_comm]

/- English proof (translation)
Set `F : τ ⟶ τ` to `⟨FGModuleCat.ofHom (τ.ρ s), fun x => by`. Use extensionality with `v`. Express the relevant statement in the definitionally equal form `τ.ρ s (τ.ρ x v) = τ.ρ x (τ.ρ s v)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hs]⟩`. Take `⟨l, hl⟩` from `endomorphism_simple_eq_smul_id ℂ F`.

Use `⟨l, fun v => ?_⟩` and prove the remaining obligations. Establish `: F.hom.hom.hom v = l • v` using `by rw [← hl]; rfl`. Conclude with `this`.
-/
private theorem schur_scalar {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) [Simple τ] (s : G)
    (hs : ∀ x : G, s * x = x * s) : ∃ l : ℂ, ∀ v : τ, τ.ρ s v = l • v := by
  let F : τ ⟶ τ := ⟨FGModuleCat.ofHom (τ.ρ s), fun x => by
    ext v
    change τ.ρ s (τ.ρ x v) = τ.ρ x (τ.ρ s v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hs]⟩
  obtain ⟨l, hl⟩ := endomorphism_simple_eq_smul_id ℂ F
  refine ⟨l, fun v => ?_⟩
  have : F.hom.hom.hom v = l • v := by rw [← hl]; rfl
  exact this

/- English proof (translation)
Establish `hx : IsIntegral F x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : aeval x (Algebra.leftMulMatrix b x).charpoly = 0`. Apply `Algebra.leftMulMatrix_injective b` to reduce the goal to its premises. Rewrite using `[← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]`. Conclude with `Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx) (Matrix.charpoly_monic _) (minpoly.dvd F x h0) (by rw [Matrix.charpoly_natDegree_eq_dim, hd, Fintype.card_fin])`.
-/
private theorem charpoly_lmul {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] {n : ℕ}
    (b : Module.Basis (Fin n) F K) (x : K) (hd : (minpoly F x).natDegree = n) :
    (Algebra.leftMulMatrix b x).charpoly = minpoly F x := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h0 : aeval x (Algebra.leftMulMatrix b x).charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx) (Matrix.charpoly_monic _)
    (minpoly.dvd F x h0) (by rw [Matrix.charpoly_natDegree_eq_dim, hd, Fintype.card_fin])

/- English proof (translation)
Establish `hE : IntermediateField.adjoin F {algebraMap F K c * x} = IntermediateField.adjoin F {x}`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F x)`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`.

Establish `h : algebraMap F K (c⁻¹ : Fˣ) * (algebraMap F K c * x) = x`. Rewrite using `[← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]`. Establish `hm` using `mul_mem (IntermediateField.algebraMap_mem (IntermediateField.adjoin F {algebraMap F K c * x}) ((c⁻¹ : Fˣ) : F)) (IntermediateField.mem_adjoin_simple_self F (algebraMap F K c * x))`. Rewrite `hm` using `[h]`. Then use the resulting hypothesis. Rewrite using `[← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x), hE]`.
-/
private theorem natDegree_smul {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (c : Fˣ) (x : K) : (minpoly F (algebraMap F K c * x)).natDegree = (minpoly F x).natDegree := by
  have hE : IntermediateField.adjoin F {algebraMap F K c * x} = IntermediateField.adjoin F {x} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h : algebraMap F K (c⁻¹ : Fˣ) * (algebraMap F K c * x) = x := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      have hm := mul_mem (IntermediateField.algebraMap_mem
        (IntermediateField.adjoin F {algebraMap F K c * x}) ((c⁻¹ : Fˣ) : F))
        (IntermediateField.mem_adjoin_simple_self F (algebraMap F K c * x))
      rwa [h] at hm
  rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x), hE]

end UpperTheory.Zero.LLC

/- English proof (translation)
Introduce `g _ n hn K _ _ hK τ θ hcusp hreg hnames c v`. Use `haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hn)`. Use `haveI : Simple τ := DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hcusp.2.1`. Take `⟨l, hl⟩` from `UpperTheory.Zero.LLC.schur_scalar τ (GeneralLinearGroup.scalar (Fin n) c) (UpperTheory.Zero.LLC.scalar_comm c)`. Take `⟨⟨z, hzdeg, hS⟩, -⟩` from `UpperTheory.Zero.LLC.pin g n hn K hK θ hreg`.

Set `b : Module.Basis (Fin n) (ZMod g) K` to `Module.finBasisOfFinrankEq _ _ hK`. Set `L : Kˣ →* Gn g n` to `Units.map (Algebra.leftMulMatrix b).toMonoidHom`. Set `cK : Kˣ` to `Units.map (algebraMap (ZMod g) K).toMonoidHom c`. Set `z' : Kˣ` to `cK * z`. Establish `hz' : (z' : K) = algebraMap (ZMod g) K c * z` using `rfl`.

Establish `hy : ((L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b z` using `rfl`. Establish `hsy : ((GeneralLinearGroup.scalar (Fin n) c * L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b z'`. Rewrite using `[Units.val_mul, hy, hz', map_mul, AlgHom.commutes]`. Use extensionality with `i j`. Simplify using `[GeneralLinearGroup.scalar, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]`.

Establish `hchar : ∀ (w : Kˣ), (minpoly (ZMod g) (w : K)).natDegree = n → ∀ M : Gn g n, (M : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b w → τ.character M = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (w ^ g ^ j) : ℂ)`. Introduce `w hw M hM`. Establish `hc : (M : Matrix (Fin n) (Fin n) (ZMod g)).charpoly = minpoly (ZMod g) (w : K)`. Rewrite using `[hM]`. Conclude with `UpperTheory.Zero.LLC.charpoly_lmul b w hw`.

Use `hnames M ?_ w ?_` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `minpoly.irreducible (Algebra.IsIntegral.isIntegral _)`. Rewrite using `[hc]`. Conclude with `minpoly.aeval _ _`.

Establish `hz'deg : (minpoly (ZMod g) (z' : K)).natDegree = n`. Rewrite using `[hz', UpperTheory.Zero.LLC.natDegree_smul]`. Conclude with `hzdeg`. Establish `h1` using `hchar z hzdeg (L z) hy`. Establish `h2` using `hchar z' hz'deg _ hsy`.

Establish `hρ : τ.ρ (GeneralLinearGroup.scalar (Fin n) c) = l • (1 : Module.End ℂ τ.V)` using `LinearMap.ext fun w => by rw [hl]; simp`. Establish `h3 : τ.character (GeneralLinearGroup.scalar (Fin n) c * L z) = l * τ.character (L z)`. Simplify using `only [FDRep.character, map_mul, hρ, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]`. Establish `hcpow : ∀ j : ℕ, cK ^ g ^ j = cK`. Introduce `j`.

Use `ext`. Simplify using `[cK, Units.val_pow_eq_pow_val, ← map_pow, ZMod.pow_card_pow]`. Establish `hsum : ∑ j ∈ Finset.range n, (θ (z' ^ g ^ j) : ℂ) = (θ cK : ℂ) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [z', mul_pow, hcpow, map_mul, Units.val_mul]`. Rewrite `h3` using `[h1, h2, hsum]`. Establish `hne : ((-1 : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ)) ≠ 0` using `mul_ne_zero (pow_ne_zero _ (by norm_num)) hS`. Establish `hl' : l = (θ cK : ℂ)`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises.

Take the linear combination `-h3`. Rewrite using `[hl, hl']`.
-/
theorem UpperTheory.Zero.LLC.nameCentral :
    UpperTheory.Zero.LLC.NameCentral := by
  intro g _ n hn K _ _ hK τ θ hcusp hreg hnames c v
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hn)
  haveI : Simple τ := DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hcusp.2.1
  obtain ⟨l, hl⟩ := UpperTheory.Zero.LLC.schur_scalar τ (GeneralLinearGroup.scalar (Fin n) c)
    (UpperTheory.Zero.LLC.scalar_comm c)
  obtain ⟨⟨z, hzdeg, hS⟩, -⟩ := UpperTheory.Zero.LLC.pin g n hn K hK θ hreg
  let b : Module.Basis (Fin n) (ZMod g) K := Module.finBasisOfFinrankEq _ _ hK
  let L : Kˣ →* Gn g n := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  let cK : Kˣ := Units.map (algebraMap (ZMod g) K).toMonoidHom c
  let z' : Kˣ := cK * z
  have hz' : (z' : K) = algebraMap (ZMod g) K c * z := rfl
  have hy : ((L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b z := rfl
  have hsy : ((GeneralLinearGroup.scalar (Fin n) c * L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g))
      = Algebra.leftMulMatrix b z' := by
    rw [Units.val_mul, hy, hz', map_mul, AlgHom.commutes]
    ext i j
    simp [GeneralLinearGroup.scalar, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
  have hchar : ∀ (w : Kˣ), (minpoly (ZMod g) (w : K)).natDegree = n → ∀ M : Gn g n,
      (M : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b w →
      τ.character M = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (w ^ g ^ j) : ℂ) := by
    intro w hw M hM
    have hc : (M : Matrix (Fin n) (Fin n) (ZMod g)).charpoly = minpoly (ZMod g) (w : K) := by
      rw [hM]
      exact UpperTheory.Zero.LLC.charpoly_lmul b w hw
    refine hnames M ?_ w ?_
    · rw [hc]
      exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
    · rw [hc]
      exact minpoly.aeval _ _
  have hz'deg : (minpoly (ZMod g) (z' : K)).natDegree = n := by
    rw [hz', UpperTheory.Zero.LLC.natDegree_smul]
    exact hzdeg
  have h1 := hchar z hzdeg (L z) hy
  have h2 := hchar z' hz'deg _ hsy
  have hρ : τ.ρ (GeneralLinearGroup.scalar (Fin n) c) = l • (1 : Module.End ℂ τ.V) :=
    LinearMap.ext fun w => by rw [hl]; simp
  have h3 : τ.character (GeneralLinearGroup.scalar (Fin n) c * L z) = l * τ.character (L z) := by
    simp only [FDRep.character, map_mul, hρ, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  have hcpow : ∀ j : ℕ, cK ^ g ^ j = cK := by
    intro j
    ext
    simp [cK, Units.val_pow_eq_pow_val, ← map_pow, ZMod.pow_card_pow]
  have hsum : ∑ j ∈ Finset.range n, (θ (z' ^ g ^ j) : ℂ)
      = (θ cK : ℂ) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [z', mul_pow, hcpow, map_mul, Units.val_mul]
  rw [h1, h2, hsum] at h3
  have hne : ((-1 : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hS
  have hl' : l = (θ cK : ℂ) := by
    apply mul_right_cancel₀ hne
    linear_combination -h3
  rw [hl, hl']
