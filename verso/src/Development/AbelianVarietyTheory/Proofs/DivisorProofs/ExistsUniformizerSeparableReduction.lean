import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqQuotientCharpolyPow

open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace GlobalTheory.UnramifiedGenerator

open IsLocalRing

/- English proof (translation)
Use `set k := ResidueField R`. Establish `hsurj : ∀ x : k ⊗[R] O, ∃ y : O, (1 : k) ⊗ₜ[R] y = x` using `fun x => TensorProduct.mk_surjective R O k residue_surjective x`. Establish `hker : ∀ y : O, (1 : k) ⊗ₜ[R] y = 0 ↔ ∃ z, y = algebraMap R O ϖ * z`. Introduce `y`. Establish `h1 : (1 : k) ⊗ₜ[R] y = 0 ↔ y ∈ LinearMap.ker (TensorProduct.mk R (R ⧸ maximalIdeal R) O 1)` using `Iff.rfl`.

Rewrite using `[h1, LinearMap.ker_tensorProductMk, hϖ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using `only [Submodule.mem_top, true_and, Algebra.smul_def]`. Conclude with `⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩`. Set `t : Module.End k (k ⊗[R] O)` to `(LinearMap.mulLeft R π).baseChange k`. Set `T : Module.End k (k ⊗[R] O)` to `(LinearMap.mulLeft R a).baseChange k`.

Establish `ht : ∀ y, t (1 ⊗ₜ y) = 1 ⊗ₜ (π * y)` using `fun y => by simp [t]`. Establish `hT : ∀ y, T (1 ⊗ₜ y) = 1 ⊗ₜ (a * y)` using `fun y => by simp [T]`. Establish `htp : ∀ (n : ℕ) y, (t ^ n) (1 ⊗ₜ y) = 1 ⊗ₜ (π ^ n * y)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih => intro y`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, ht, pow_succ', mul_assoc]`. Establish `hc : Commute t T`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hsurj x`. Simplify using `only [Module.End.mul_apply, ht, hT, mul_left_comm]`. Establish `hte : t ^ e = 0`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hsurj x`.

Rewrite using `[htp, LinearMap.zero_apply, hker]`. Conclude with `⟨(u⁻¹ : Oˣ) * y, by rw [hu, mul_assoc, Units.mul_inv_cancel_left]⟩`. Establish `hkt : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1))`. Introduce `x hx`. Take `⟨y, rfl⟩` from `hsurj x`.

Rewrite `hx` using `[ht, hker]`. Take `⟨z, hz⟩` from `hx`. Take `⟨n, rfl⟩ : ∃ n, e = n + 1` from `⟨e - 1, by omega⟩`. Use `⟨1 ⊗ₜ (u * z), ?_⟩` and prove the remaining obligations. Rewrite using `[htp, Nat.add_sub_cancel]`.

Use `congr 1`. Apply `mul_left_cancel₀ hπ0` to reduce the goal to its premises. Rewrite using `[hz, hu]`. Expand and normalize the polynomial expressions, which then agree. Establish `hTt : LinearMap.range t ≤ (LinearMap.range t).comap T`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨T x, LinearMap.congr_fun hc.eq x⟩`. Establish `key` using `GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow k (k ⊗[R] O) t T hc e he hte hkt hTt`. Establish `hbc : LinearMap.charpoly T = (LinearMap.charpoly (LinearMap.mulLeft R a)).map (residue R)` using `LinearMap.charpoly_baseChange _ k`. Rewrite using `[← hbc, key]`.

Use `congr 1`. Set `φ : k ⊗[R] O →ₗ[k] ResidueField O` to `(Algebra.TensorProduct.lift (Algebra.ofId k (ResidueField O)) (IsScalarTower.toAlgHom R O (ResidueField O)) (fun _ _ => Commute.all _ _)).toLinearMap`. Establish `hφ : ∀ y, φ (1 ⊗ₜ y) = residue O y` using `fun y => by simp [φ]`. Establish `hφs : Function.Surjective φ` using `fun w => by`. Take `⟨y, rfl⟩` from `residue_surjective w`.

Conclude with `⟨_, hφ y⟩`. Establish `hφk : LinearMap.range t = LinearMap.ker φ`. Use extensionality with `x`. Take `⟨y, rfl⟩` from `hsurj x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x', hx'⟩`. Take `⟨z, rfl⟩` from `hsurj x'`. Rewrite using `[← hx', ht, LinearMap.mem_ker, hφ, residue_eq_zero_iff, hπ]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Introduce `hy`.

Rewrite `hy` using `[LinearMap.mem_ker, hφ, residue_eq_zero_iff, hπ, Ideal.mem_span_singleton]`. Take `⟨z, rfl⟩` from `hy`. Conclude with `⟨_, ht z⟩`. Use `GlobalTheory.NilpFiltration.charpoly_eq_of_intertwine ((Submodule.quotEquivOfEq _ _ hφk).trans (φ.quotKerEquivOfSurjective hφs)) _ _ ?_` and prove the remaining obligations. Introduce `x`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨y, rfl⟩` from `hsurj x`. Express the relevant statement in the definitionally equal form `φ (T (1 ⊗ₜ y)) = residue O a * φ (1 ⊗ₜ y)`. Rewrite using `[hT, hφ, hφ, map_mul]`.
-/
theorem charpoly_map_residue {R O : Type} [CommRing R] [IsLocalRing R] [CommRing O] [IsDomain O]
    [IsLocalRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
    [IsLocalHom (algebraMap R O)] (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (π : O) (hπ0 : π ≠ 0) (hπ : maximalIdeal O = Ideal.span {π}) (e : ℕ) (he : 0 < e) (u : Oˣ)
    (hu : algebraMap R O ϖ = π ^ e * u) (a : O) :
    (LinearMap.charpoly (LinearMap.mulLeft R a)).map (residue R) =
      (LinearMap.charpoly (LinearMap.mulLeft (ResidueField R) (residue O a))) ^ e := by
  set k := ResidueField R
  have hsurj : ∀ x : k ⊗[R] O, ∃ y : O, (1 : k) ⊗ₜ[R] y = x := fun x =>
    TensorProduct.mk_surjective R O k residue_surjective x
  have hker : ∀ y : O, (1 : k) ⊗ₜ[R] y = 0 ↔ ∃ z, y = algebraMap R O ϖ * z := by
    intro y
    have h1 : (1 : k) ⊗ₜ[R] y = 0 ↔
        y ∈ LinearMap.ker (TensorProduct.mk R (R ⧸ maximalIdeal R) O 1) := Iff.rfl
    rw [h1, LinearMap.ker_tensorProductMk, hϖ, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and, Algebra.smul_def]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  let t : Module.End k (k ⊗[R] O) := (LinearMap.mulLeft R π).baseChange k
  let T : Module.End k (k ⊗[R] O) := (LinearMap.mulLeft R a).baseChange k
  have ht : ∀ y, t (1 ⊗ₜ y) = 1 ⊗ₜ (π * y) := fun y => by simp [t]
  have hT : ∀ y, T (1 ⊗ₜ y) = 1 ⊗ₜ (a * y) := fun y => by simp [T]
  have htp : ∀ (n : ℕ) y, (t ^ n) (1 ⊗ₜ y) = 1 ⊗ₜ (π ^ n * y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro y; rw [pow_succ', Module.End.mul_apply, ih, ht, pow_succ', mul_assoc]
  have hc : Commute t T := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hsurj x
    simp only [Module.End.mul_apply, ht, hT, mul_left_comm]
  have hte : t ^ e = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hsurj x
    rw [htp, LinearMap.zero_apply, hker]
    exact ⟨(u⁻¹ : Oˣ) * y, by rw [hu, mul_assoc, Units.mul_inv_cancel_left]⟩
  have hkt : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    rw [ht, hker] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
    refine ⟨1 ⊗ₜ (u * z), ?_⟩
    rw [htp, Nat.add_sub_cancel]
    congr 1
    apply mul_left_cancel₀ hπ0
    rw [hz, hu]
    ring
  have hTt : LinearMap.range t ≤ (LinearMap.range t).comap T := by
    rintro _ ⟨x, rfl⟩
    exact ⟨T x, LinearMap.congr_fun hc.eq x⟩
  have key := GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow k (k ⊗[R] O) t T hc e he hte hkt hTt
  have hbc : LinearMap.charpoly T = (LinearMap.charpoly (LinearMap.mulLeft R a)).map (residue R) :=
    LinearMap.charpoly_baseChange _ k
  rw [← hbc, key]
  congr 1
  let φ : k ⊗[R] O →ₗ[k] ResidueField O :=
    (Algebra.TensorProduct.lift (Algebra.ofId k (ResidueField O))
      (IsScalarTower.toAlgHom R O (ResidueField O)) (fun _ _ => Commute.all _ _)).toLinearMap
  have hφ : ∀ y, φ (1 ⊗ₜ y) = residue O y := fun y => by simp [φ]
  have hφs : Function.Surjective φ := fun w => by
    obtain ⟨y, rfl⟩ := residue_surjective w
    exact ⟨_, hφ y⟩
  have hφk : LinearMap.range t = LinearMap.ker φ := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨z, rfl⟩ := hsurj x'
      rw [← hx', ht, LinearMap.mem_ker, hφ, residue_eq_zero_iff, hπ]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hy
      rw [LinearMap.mem_ker, hφ, residue_eq_zero_iff, hπ, Ideal.mem_span_singleton] at hy
      obtain ⟨z, rfl⟩ := hy
      exact ⟨_, ht z⟩
  refine GlobalTheory.NilpFiltration.charpoly_eq_of_intertwine
    ((Submodule.quotEquivOfEq _ _ hφk).trans (φ.quotKerEquivOfSurjective hφs)) _ _ ?_
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := hsurj x
  change φ (T (1 ⊗ₜ y)) = residue O a * φ (1 ⊗ₜ y)
  rw [hT, hφ, hφ, map_mul]

/- English proof (translation)
Introduce `l hl O _ _ _ _ _ _`. Use `set k := ResidueField ℤ_[l]`. Use `haveI : Finite k := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hl0 : (l : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hl.out.ne_zero`.

Establish `hlm : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l]`. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `hl1 : algebraMap ℤ_[l] O l ≠ 0` using `(map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] O)).2 hl0`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl1 hπ`.

Establish `he : 0 < e`. Use `Nat.pos_of_ne_zero ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Establish `h1 : IsUnit (algebraMap ℤ_[l] O l)` using `by rw [hu]; simp`. Conclude with `hlm (isUnit_of_map_unit _ _ h1)`.

Rewrite `hu` using `[mul_comm]`. Set `pb : PowerBasis k (ResidueField O)` to `Field.powerBasisOfFiniteOfSeparable k (ResidueField O)`. Take `⟨a, ha⟩` from `residue_surjective pb.gen`. Establish `hm : (minpoly k pb.gen).Monic` using `minpoly.monic pb.isIntegral_gen`. Take `⟨h, hh, -, hhm⟩` from `lifts_and_natDegree_eq_and_monic (f := residue ℤ_[l]) ((mem_lifts _).2 (map_surjective _ residue_surjective _)) hm`.

Establish `hsep : (h.map (residue ℤ_[l])).Separable`. Rewrite using `[hh]`. Conclude with `Algebra.IsSeparable.isSeparable k pb.gen`. Establish `hch : (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map (residue ℤ_[l]) = (h.map (residue ℤ_[l])) ^ e`. Rewrite using `[charpoly_map_residue (l : ℤ_[l]) PadicInt.maximalIdeal_eq_span_p π hπ.ne_zero hπ.maximalIdeal_eq e he u hu a, hh, ha, ← charpoly_leftMulMatrix pb, ← LinearMap.charpoly_toMatrix _ pb.basis]`.

Both sides reduce to the same expression. Use `⟨e, π, a, u, h, he, by simpa using hu, hhm, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hπ.maximalIdeal_eq, ← residue_eq_zero_iff]`. Establish `h1` using `minpoly.aeval k pb.gen`. Rewrite `h1` using `[← hh, ← ha]`.

Rewrite using `[← h1]`. Conclude with `((aeval_algebraMap_apply (ResidueField O) a h).symm).trans (aeval_map_algebraMap k _ h).symm`. Establish `h1` using `congrArg natDegree hch`. Rewrite `h1` using `[(LinearMap.charpoly_monic _).natDegree_map, LinearMap.charpoly_natDegree, natDegree_pow, hhm.natDegree_map]`. Conclude with `h1.symm`.

Introduce `κ _ _ ψ`. Establish `hψ : ∀ x ∈ maximalIdeal ℤ_[l], ψ x = 0`. Introduce `x hx`. Rewrite `hx` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Take `⟨y, rfl⟩` from `hx`.

Simplify using the standard rewrite rules. Set `χ : k →+* κ` to `Ideal.Quotient.lift _ ψ hψ`. Establish `hχ : ψ = χ.comp (residue ℤ_[l])` using `RingHom.ext fun _ => rfl`. Rewrite using `[hχ, ← Polynomial.map_map, ← Polynomial.map_map, hch, Polynomial.map_pow]`. Conclude with `⟨hsep.map, rfl⟩`.
-/
theorem exists_ramification_and_generator : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O],
    ∃ (e : ℕ) (π a : O) (u : Oˣ) (h : ℤ_[l][X]), 0 < e ∧ (l : O) = π ^ e * u ∧ h.Monic ∧
      aeval a h ∈ Ideal.span {π} ∧ e * h.natDegree = Module.finrank ℤ_[l] O ∧
      ∀ (κ : Type) [Field κ] [CharP κ l] (ψ : ℤ_[l] →+* κ), (h.map ψ).Separable ∧
        (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map ψ = (h.map ψ) ^ e := by
  intro l hl O _ _ _ _ _ _
  set k := ResidueField ℤ_[l]
  haveI : Finite k := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hlm : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  have hl1 : algebraMap ℤ_[l] O l ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] O)).2 hl0
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl1 hπ
  have he : 0 < e := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    have h1 : IsUnit (algebraMap ℤ_[l] O l) := by rw [hu]; simp
    exact hlm (isUnit_of_map_unit _ _ h1)
  rw [mul_comm] at hu
  let pb : PowerBasis k (ResidueField O) := Field.powerBasisOfFiniteOfSeparable k (ResidueField O)
  obtain ⟨a, ha⟩ := residue_surjective pb.gen
  have hm : (minpoly k pb.gen).Monic := minpoly.monic pb.isIntegral_gen
  obtain ⟨h, hh, -, hhm⟩ := lifts_and_natDegree_eq_and_monic (f := residue ℤ_[l])
    ((mem_lifts _).2 (map_surjective _ residue_surjective _)) hm
  have hsep : (h.map (residue ℤ_[l])).Separable := by
    rw [hh]; exact Algebra.IsSeparable.isSeparable k pb.gen
  have hch : (LinearMap.charpoly (LinearMap.mulLeft ℤ_[l] a)).map (residue ℤ_[l]) =
      (h.map (residue ℤ_[l])) ^ e := by
    rw [charpoly_map_residue (l : ℤ_[l]) PadicInt.maximalIdeal_eq_span_p π hπ.ne_zero
      hπ.maximalIdeal_eq e he u hu a, hh, ha, ← charpoly_leftMulMatrix pb,
      ← LinearMap.charpoly_toMatrix _ pb.basis]
    rfl
  refine ⟨e, π, a, u, h, he, by simpa using hu, hhm, ?_, ?_, ?_⟩
  · rw [← hπ.maximalIdeal_eq, ← residue_eq_zero_iff]
    have h1 := minpoly.aeval k pb.gen
    rw [← hh, ← ha] at h1
    rw [← h1]
    exact ((aeval_algebraMap_apply (ResidueField O) a h).symm).trans
      (aeval_map_algebraMap k _ h).symm
  · have h1 := congrArg natDegree hch
    rw [(LinearMap.charpoly_monic _).natDegree_map, LinearMap.charpoly_natDegree,
      natDegree_pow, hhm.natDegree_map] at h1
    exact h1.symm
  · intro κ _ _ ψ
    have hψ : ∀ x ∈ maximalIdeal ℤ_[l], ψ x = 0 := by
      intro x hx
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      simp
    let χ : k →+* κ := Ideal.Quotient.lift _ ψ hψ
    have hχ : ψ = χ.comp (residue ℤ_[l]) := RingHom.ext fun _ => rfl
    rw [hχ, ← Polynomial.map_map, ← Polynomial.map_map, hch, Polynomial.map_pow]
    exact ⟨hsep.map, rfl⟩

end GlobalTheory.UnramifiedGenerator
