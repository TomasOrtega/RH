import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarCommonCoverStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistLatticeCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistAutomorphism
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompFieldExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrLinked

section Fields

open TensorProduct

/- English proof (translation)
Set `_` to `i.toAlgebra`. Establish `hb : Function.Bijective i.rangeRestrictField` using `⟨fun a b h => i.injective (congrArg Subtype.val h), fun ⟨x, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩`. Use `rank_eq_of_equiv_equiv (R := A) (R' := i.fieldRange) (M := Ω) (M₁ := Ω) i.rangeRestrictField (AddEquiv.refl Ω) hb (fun r m => by show r • m = _` as an intermediate fact. Rewrite using `[Algebra.smul_def]`. Use the proof step `rfl)`.

Conclude with `(congrArg Cardinal.toNat this).symm`.
-/
theorem finrank_fieldRange {A Ω : Type} [Field A] [Field Ω] (i : A →+* Ω) :
    Module.finrank i.fieldRange Ω = (letI := i.toAlgebra; Module.finrank A Ω) := by
  let _ := i.toAlgebra
  have hb : Function.Bijective i.rangeRestrictField := ⟨fun a b h => i.injective (congrArg Subtype.val h),
    fun ⟨x, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩
  have := rank_eq_of_equiv_equiv (R := A) (R' := i.fieldRange) (M := Ω) (M₁ := Ω) i.rangeRestrictField
    (AddEquiv.refl Ω) hb (fun r m => by
      show r • m = _
      rw [Algebra.smul_def]
      rfl)
  exact (congrArg Cardinal.toNat this).symm

/- English proof (translation)
Set `algA : Algebra F A` to `gA.toAlgebra`. Set `algB : Algebra F B` to `gB.toAlgebra`. Establish `finB : Module.Finite F B` using `hB`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (A ⊗[F] B)`. Set `fΩ : Field (A ⊗[F] B ⧸ m)` to `Ideal.Quotient.field m`.

Set `iA : A →+* (A ⊗[F] B ⧸ m)` to `(Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom)`. Set `iB : B →+* (A ⊗[F] B ⧸ m)` to `(Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : B →ₐ[F] A ⊗[F] B).toRingHom`. Establish `hcomp : iA.comp gA = iB.comp gB`. Use extensionality with `a`. Use `show Ideal.Quotient.mk m (algebraMap F A a ⊗ₜ 1) = Ideal.Quotient.mk m (1 ⊗ₜ algebraMap F B a)`.

Use `congr 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Use `⟨A ⊗[F] B ⧸ m, fΩ, iA, iB, hcomp, ?_⟩` and prove the remaining obligations. Establish `hfin : Module.Finite A (A ⊗[F] B ⧸ m)` using `inferInstance`. Establish `he : iA.toAlgebra = (inferInstance : Algebra A (A ⊗[F] B ⧸ m))` using `Algebra.algebra_ext _ _ fun a => rfl`.

Use `show @Module.Finite A _ _ _ iA.toAlgebra.toModule`. Rewrite using `[he]`. Conclude with `hfin`.
-/
theorem exists_tensor_field (F A B : Type) [Field F] [Field A] [Field B] (gA : F →+* A) (gB : F →+* B)
    (hB : letI := gB.toAlgebra; Module.Finite F B) :
    ∃ (Ω : Type) (_ : Field Ω) (iA : A →+* Ω) (iB : B →+* Ω), iA.comp gA = iB.comp gB ∧
      (letI := iA.toAlgebra; Module.Finite A Ω) := by
  let algA : Algebra F A := gA.toAlgebra
  let algB : Algebra F B := gB.toAlgebra
  have finB : Module.Finite F B := hB
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⊗[F] B)
  let fΩ : Field (A ⊗[F] B ⧸ m) := Ideal.Quotient.field m
  let iA : A →+* (A ⊗[F] B ⧸ m) := (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom)
  let iB : B →+* (A ⊗[F] B ⧸ m) := (Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[F] A ⊗[F] B).toRingHom
  have hcomp : iA.comp gA = iB.comp gB := by
    ext a
    show Ideal.Quotient.mk m (algebraMap F A a ⊗ₜ 1) = Ideal.Quotient.mk m (1 ⊗ₜ algebraMap F B a)
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨A ⊗[F] B ⧸ m, fΩ, iA, iB, hcomp, ?_⟩
  have hfin : Module.Finite A (A ⊗[F] B ⧸ m) := inferInstance
  have he : iA.toAlgebra = (inferInstance : Algebra A (A ⊗[F] B ⧸ m)) :=
    Algebra.algebra_ext _ _ fun a => rfl
  show @Module.Finite A _ _ _ iA.toAlgebra.toModule
  rw [he]
  exact hfin

/- English proof (translation)
Set `algA : Algebra F A` to `gA.toAlgebra`. Set `algB : Algebra F B` to `gB.toAlgebra`. Set `algC : Algebra F C` to `gC.toAlgebra`. Establish `finA : Module.Finite F A` using `Module.finite_of_finrank_pos (by rw [hA]; exact hdA)`. Establish `finB : Module.Finite F B` using `Module.finite_of_finrank_pos (by rw [hB]; exact hdB)`.

Take `⟨Ω, fΩ, iA, iB, hcomp, hfin⟩` from `exists_tensor_field F A B gA gB finB`. Establish `: CharZero Ω` using `charZero_of_injective_ringHom iA.injective`. Set `alA : Algebra A Ω` to `iA.toAlgebra`. Set `alB : Algebra B Ω` to `iB.toAlgebra`. Set `alF : Algebra F Ω` to `(iA.comp gA).toAlgebra`.

Establish `finΩ : Module.Finite A Ω` using `hfin`. Establish `tA : IsScalarTower F A Ω` using `.of_algebraMap_eq' rfl`. Establish `tB : IsScalarTower F B Ω` using `.of_algebraMap_eq' hcomp`. Establish `finF : Module.Finite F Ω` using `Module.Finite.trans A Ω`. Establish `finBΩ : Module.Finite B Ω` using `Module.Finite.of_restrictScalars_finite F B Ω`.

Establish `mA : dA * Module.finrank A Ω = Module.finrank F Ω`. Rewrite using `[← hA]`. Conclude with `Module.finrank_mul_finrank F A Ω`. Establish `mB : dB * Module.finrank B Ω = Module.finrank F Ω`. Rewrite using `[← hB]`.

Conclude with `Module.finrank_mul_finrank F B Ω`. Establish `pA : 0 < Module.finrank A Ω` using `Module.finrank_pos`. Establish `pB : 0 < Module.finrank B Ω` using `Module.finrank_pos`. Establish `pF : 0 < Module.finrank F Ω` using `Module.finrank_pos`. Establish `hsurj : Function.Surjective gC`.

Introduce `w`. Take `⟨a, ha⟩` from `(finrank_eq_one_iff_of_nonzero' (1 : C) one_ne_zero).1 hC w`. Conclude with `⟨a, by rw [← ha, Algebra.smul_def, mul_one]; rfl⟩`. Set `eC : F ≃+* C` to `RingEquiv.ofBijective gC ⟨gC.injective, hsurj⟩`. Set `iC : C →+* Ω` to `(iA.comp gA).comp eC.symm.toRingHom`.

Establish `hiC : iC.comp gC = iA.comp gA`. Use extensionality with `a`. Use `show iA (gA (eC.symm (gC a))) = _`. Establish `: eC.symm (gC a) = a` using `eC.symm_apply_apply a`. Rewrite using `[this]`.

Both sides reduce to the same expression. Establish `hrC : iC.fieldRange = (iA.comp gA).fieldRange`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨eC.symm a, rfl⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨gC a, RingHom.congr_fun hiC a⟩`. Establish `nA : Module.finrank iA.fieldRange Ω = Module.finrank A Ω` using `finrank_fieldRange iA`. Establish `nB : Module.finrank iB.fieldRange Ω = Module.finrank B Ω` using `finrank_fieldRange iB`.

Establish `nC : Module.finrank (iA.comp gA).fieldRange Ω = Module.finrank F Ω` using `finrank_fieldRange (iA.comp gA)`. Use `⟨Ω, fΩ, this, iA, iB, iC, hiC.symm, hcomp.symm.trans hiC.symm, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `FiniteDimensional.of_finrank_pos (by omega)`. Conclude with `FiniteDimensional.of_finrank_pos (by omega)`. Rewrite using `[hrC]`.

Conclude with `FiniteDimensional.of_finrank_pos (by omega)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[nA, nB, mul_comm, mA, mul_comm, mB]`.
-/
theorem exists_common_field (F A B C : Type) [Field F] [Field A] [Field B] [Field C] [CharZero A]
    (gA : F →+* A) (gB : F →+* B) (gC : F →+* C) (dA dB : ℕ) (hdA : 0 < dA) (hdB : 0 < dB)
    (hA : letI := gA.toAlgebra; Module.finrank F A = dA) (hB : letI := gB.toAlgebra; Module.finrank F B = dB)
    (hC : letI := gC.toAlgebra; Module.finrank F C = 1) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (iA : A →+* Ω) (iB : B →+* Ω) (iC : C →+* Ω),
      iA.comp gA = iC.comp gC ∧ iB.comp gB = iC.comp gC ∧ FiniteDimensional iA.fieldRange Ω ∧
      FiniteDimensional iB.fieldRange Ω ∧ FiniteDimensional iC.fieldRange Ω ∧
      Module.finrank iA.fieldRange Ω ≠ 0 ∧
      Module.finrank iA.fieldRange Ω * dA = Module.finrank iB.fieldRange Ω * dB := by
  let algA : Algebra F A := gA.toAlgebra
  let algB : Algebra F B := gB.toAlgebra
  let algC : Algebra F C := gC.toAlgebra
  have finA : Module.Finite F A := Module.finite_of_finrank_pos (by rw [hA]; exact hdA)
  have finB : Module.Finite F B := Module.finite_of_finrank_pos (by rw [hB]; exact hdB)
  obtain ⟨Ω, fΩ, iA, iB, hcomp, hfin⟩ := exists_tensor_field F A B gA gB finB
  have : CharZero Ω := charZero_of_injective_ringHom iA.injective
  let alA : Algebra A Ω := iA.toAlgebra
  let alB : Algebra B Ω := iB.toAlgebra
  let alF : Algebra F Ω := (iA.comp gA).toAlgebra
  have finΩ : Module.Finite A Ω := hfin
  have tA : IsScalarTower F A Ω := .of_algebraMap_eq' rfl
  have tB : IsScalarTower F B Ω := .of_algebraMap_eq' hcomp
  have finF : Module.Finite F Ω := Module.Finite.trans A Ω
  have finBΩ : Module.Finite B Ω := Module.Finite.of_restrictScalars_finite F B Ω
  have mA : dA * Module.finrank A Ω = Module.finrank F Ω := by
    rw [← hA]; exact Module.finrank_mul_finrank F A Ω
  have mB : dB * Module.finrank B Ω = Module.finrank F Ω := by
    rw [← hB]; exact Module.finrank_mul_finrank F B Ω
  have pA : 0 < Module.finrank A Ω := Module.finrank_pos
  have pB : 0 < Module.finrank B Ω := Module.finrank_pos
  have pF : 0 < Module.finrank F Ω := Module.finrank_pos
  have hsurj : Function.Surjective gC := by
    intro w
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (1 : C) one_ne_zero).1 hC w
    exact ⟨a, by rw [← ha, Algebra.smul_def, mul_one]; rfl⟩
  let eC : F ≃+* C := RingEquiv.ofBijective gC ⟨gC.injective, hsurj⟩
  let iC : C →+* Ω := (iA.comp gA).comp eC.symm.toRingHom
  have hiC : iC.comp gC = iA.comp gA := by
    ext a
    show iA (gA (eC.symm (gC a))) = _
    have : eC.symm (gC a) = a := eC.symm_apply_apply a
    rw [this]
    rfl
  have hrC : iC.fieldRange = (iA.comp gA).fieldRange := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨eC.symm a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gC a, RingHom.congr_fun hiC a⟩
  have nA : Module.finrank iA.fieldRange Ω = Module.finrank A Ω := finrank_fieldRange iA
  have nB : Module.finrank iB.fieldRange Ω = Module.finrank B Ω := finrank_fieldRange iB
  have nC : Module.finrank (iA.comp gA).fieldRange Ω = Module.finrank F Ω := finrank_fieldRange (iA.comp gA)
  refine ⟨Ω, fΩ, this, iA, iB, iC, hiC.symm, hcomp.symm.trans hiC.symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact FiniteDimensional.of_finrank_pos (by omega)
  · exact FiniteDimensional.of_finrank_pos (by omega)
  · rw [hrC]
    exact FiniteDimensional.of_finrank_pos (by omega)
  · omega
  · rw [nA, nB, mul_comm, mA, mul_comm, mB]

end Fields

end GlobalTheory.CompanionTheory.Ar.OrLinked

namespace GlobalTheory.CompanionTheory.Ar.OrLinked

section ModelSec

/- English proof (translation)
Take `⟨a, b, c, d⟩` from `h`. Take `⟨a', b', c', d'⟩` from `h'`. Use `⟨a'.comp a, b'.comp b, fun p => ?_, ?_⟩` and prove the remaining obligations. Use `show (v' (v p)).1 = κ' (κ p.1)`. Rewrite using `[c', c]`.

Introduce and unpack `q ⟨k, hk⟩`. Take `⟨r, rfl⟩` from `d' q ⟨κ k, hk⟩`. Establish `h1 : κ' r.1 = κ' (κ k)` using `by rw [← c']; exact hk.symm`. Take `⟨r', rfl⟩` from `d r ⟨k, (a' h1).symm⟩`. Conclude with `⟨r', rfl⟩`.
-/
theorem isBlockMap_comp {K₀ K₁ K₂ : Type} {ι₀ : K₀ → Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} [Fintype K₀] [Fintype K₁] [Fintype K₂] [∀ k, Fintype (ι₀ k)] [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)]
    {κ : K₀ → K₁} {v : (Σ k, ι₀ k) → Σ k, ι₁ k} {κ' : K₁ → K₂} {v' : (Σ k, ι₁ k) → Σ k, ι₂ k}
    (h : IsBlockMap κ v) (h' : IsBlockMap κ' v') : IsBlockMap (κ' ∘ κ) (v' ∘ v) := by
  obtain ⟨a, b, c, d⟩ := h
  obtain ⟨a', b', c', d'⟩ := h'
  refine ⟨a'.comp a, b'.comp b, fun p => ?_, ?_⟩
  · show (v' (v p)).1 = κ' (κ p.1)
    rw [c', c]
  · rintro q ⟨k, hk⟩
    obtain ⟨r, rfl⟩ := d' q ⟨κ k, hk⟩
    have h1 : κ' r.1 = κ' (κ k) := by rw [← c']; exact hk.symm
    obtain ⟨r', rfl⟩ := d r ⟨k, (a' h1).symm⟩
    exact ⟨r', rfl⟩

/- English proof (translation)
Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `t ⟨p, q, hpq, rfl⟩`. Use `IntermediateField.subset_adjoin _ _ ⟨v p, v q, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[h.2.2.1, h.2.2.1, hpq]`.
-/
theorem blockFnField_le {K₀ K₁ : Type} {ι₀ : K₀ → Type} {ι₁ : K₁ → Type} [Fintype K₀] [Fintype K₁] [∀ k, Fintype (ι₀ k)] [∀ k, Fintype (ι₁ k)]
    {κ : K₀ → K₁} {v : (Σ k, ι₀ k) → Σ k, ι₁ k} (h : IsBlockMap κ v) {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, ι₁ k) → Ω) : blockFnField (y ∘ v) ≤ blockFnField y := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro t ⟨p, q, hpq, rfl⟩
  refine IntermediateField.subset_adjoin _ _ ⟨v p, v q, ?_, rfl⟩
  rw [h.2.2.1, h.2.2.1, hpq]

/- English proof (translation)
Rewrite using `[finrank_fieldRange]`. Conclude with `Module.finrank_self Ω`.
-/
theorem finrank_id_fieldRange (Ω : Type) [Field Ω] : Module.finrank (RingHom.id Ω).fieldRange Ω = 1 := by
  rw [finrank_fieldRange]
  exact Module.finrank_self Ω

/- English proof (translation)
Take `⟨K', hK', ι', hι', κ₀', v₀', κ₁', v₁', y', Z', ξ', h₀', h₁', bm₀, bm₁, hy₀, hy₁, ha', hb', hall', htie', -, hd₀, hd₁, hr₀, hr₁⟩` from `GlobalTheory.T.arith_var_common_cover K₀ ι₀ K₁ ι₁ Ω₀ Ω₁ Ω i₀ i₁ y₀ y₁ d X₀ X₁ ξ₀ ξ₁ a₀ a₁ b₀ b₁ f₀ f₁ g₀ g₁ t₀ t₁`. Establish `fid : FiniteDimensional (RingHom.id Ω).fieldRange Ω` using `FiniteDimensional.of_finrank_pos (by rw [finrank_id_fieldRange]; exact one_pos)`. Take `⟨K, hK, ι, hι, κ, v, κ₂, v₂, y, Z, ξ, h, h₂, bm, bm₂, hy, hy₂, -, -, hall, htie, hnorm, hd, hd₂, hr, -⟩` from `GlobalTheory.T.arith_var_common_cover K' ι' K₂ ι₂ Ω Ω₂ Ω (RingHom.id Ω) i₂ y' y₂ d Z' X₂ ξ' ξ₂ ha' a₂ hb' b₂ fid f₂ hall' g₂ htie' t₂`. Establish `hyv : y ∘ v = y'` using `by simpa using hy`. Establish `hξ : ξ ≫ h = ξ'`.

Establish `: ξ ≫ h = _` using `hd`. Simplify using `using this`. Establish `hfield : blockFnField y = blockFnField y'`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Use `(IntermediateField.relfinrank_eq_one_iff).1 (hr.trans (finrank_id_fieldRange Ω))` as an intermediate fact.

Rewrite `this` using `[hyv]`. Then use the resulting hypothesis. Use `blockFnField_le bm y` as an intermediate fact. Rewrite `this` using `[hyv]`. Then use the resulting hypothesis. Establish `e₀ : y ∘ (v ∘ v₀') = y' ∘ v₀'` using `by rw [← Function.comp_assoc, hyv]`. Establish `e₁ : y ∘ (v ∘ v₁') = y' ∘ v₁'` using `by rw [← Function.comp_assoc, hyv]`.

Use `⟨K, hK, ι, hι, κ ∘ κ₀', v ∘ v₀', κ ∘ κ₁', v ∘ v₁', κ₂, v₂, y, Z, ξ, h ≫ h₀', h ≫ h₁', h₂, isBlockMap_comp bm₀ bm, isBlockMap_comp bm₁ bm, bm₂, ?_, ?_, hy₂, hall, htie, hnorm, ?_, ?_, hd₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e₀, hy₀]`. Rewrite using `[e₁, hy₁]`. Use `show ξ ≫ h ≫ h₀' = _`. Rewrite using `[← Category.assoc, hξ]`.

Conclude with `hd₀`. Use `show ξ ≫ h ≫ h₁' = _`. Rewrite using `[← Category.assoc, hξ]`. Conclude with `hd₁`. Rewrite using `[e₀, hfield]`.

Conclude with `hr₀`. Rewrite using `[e₁, hfield]`. Conclude with `hr₁`.
-/
theorem exists_common_model (K₀ : Type) [Fintype K₀] (ι₀ : K₀ → Type) [∀ k, Fintype (ι₀ k)]
    (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (Ω₀ Ω₁ Ω₂ Ω : Type) [Field Ω₀] [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω]
    (i₀ : Ω₀ →+* Ω) (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω)
    (y₀ : (Σ k, ι₀ k) → Ω₀) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ)
    (X₀ X₁ X₂ : Scheme.{0}) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁)
    (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂)
    (a₀ : IsArithVar (mCoordIdeal y₀) d) (a₁ : IsArithVar (mCoordIdeal y₁) d) (a₂ : IsArithVar (mCoordIdeal y₂) d)
    (b₀ : Birational y₀) (b₁ : Birational y₁) (b₂ : Birational y₂)
    (f₀ : FiniteDimensional i₀.fieldRange Ω) (f₁ : FiniteDimensional i₁.fieldRange Ω)
    (f₂ : FiniteDimensional i₂.fieldRange Ω)
    (g₀ : ∀ q : X₀, genPt ξ₀ ⤳ q) (g₁ : ∀ q : X₁, genPt ξ₁ ⤳ q) (g₂ : ∀ q : X₂, genPt ξ₂ ⤳ q)
    (t₀ : CoordTie ℤ ξ₀ (fun c' : (k : K₀) → ι₀ k => ∏ k, y₀ ⟨k, c' k⟩))
    (t₁ : CoordTie ℤ ξ₁ (fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩))
    (t₂ : CoordTie ℤ ξ₂ (fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩)) :
    ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ₀ : K₀ → K)
      (v₀ : (Σ k, ι₀ k) → Σ k, ι k) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K)
      (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (y : (Σ k, ι k) → Ω) (Z : Scheme.{0})
      (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₀ : Z ⟶ X₀) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂),
      IsBlockMap κ₀ v₀ ∧ IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧ y ∘ v₀ = (fun p => i₀ (y₀ p)) ∧
      y ∘ v₁ = (fun p => i₁ (y₁ p)) ∧ y ∘ v₂ = (fun p => i₂ (y₂ p)) ∧ (∀ q : Z, genPt ξ ⤳ q) ∧
      CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧
      GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h₀ i₀ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧
      IntermediateField.relfinrank (blockFnField (y ∘ v₀)) (blockFnField y) = Module.finrank i₀.fieldRange Ω ∧
      IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) = Module.finrank i₁.fieldRange Ω := by
  obtain ⟨K', hK', ι', hι', κ₀', v₀', κ₁', v₁', y', Z', ξ', h₀', h₁', bm₀, bm₁, hy₀, hy₁, ha', hb', hall', htie', -,
    hd₀, hd₁, hr₀, hr₁⟩ := GlobalTheory.T.arith_var_common_cover K₀ ι₀ K₁ ι₁ Ω₀ Ω₁ Ω i₀ i₁ y₀ y₁ d X₀ X₁ ξ₀ ξ₁ a₀ a₁ b₀ b₁ f₀ f₁ g₀ g₁ t₀ t₁
  have fid : FiniteDimensional (RingHom.id Ω).fieldRange Ω :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_id_fieldRange]; exact one_pos)
  obtain ⟨K, hK, ι, hι, κ, v, κ₂, v₂, y, Z, ξ, h, h₂, bm, bm₂, hy, hy₂, -, -, hall, htie, hnorm, hd, hd₂, hr, -⟩ :=
    GlobalTheory.T.arith_var_common_cover K' ι' K₂ ι₂ Ω Ω₂ Ω (RingHom.id Ω) i₂ y' y₂ d Z' X₂ ξ' ξ₂ ha' a₂ hb' b₂ fid f₂ hall' g₂ htie' t₂
  have hyv : y ∘ v = y' := by simpa using hy
  have hξ : ξ ≫ h = ξ' := by
    have : ξ ≫ h = _ := hd
    simpa using this
  have hfield : blockFnField y = blockFnField y' := by
    refine le_antisymm ?_ ?_
    · have := (IntermediateField.relfinrank_eq_one_iff).1 (hr.trans (finrank_id_fieldRange Ω))
      rwa [hyv] at this
    · have := blockFnField_le bm y
      rwa [hyv] at this
  have e₀ : y ∘ (v ∘ v₀') = y' ∘ v₀' := by rw [← Function.comp_assoc, hyv]
  have e₁ : y ∘ (v ∘ v₁') = y' ∘ v₁' := by rw [← Function.comp_assoc, hyv]
  refine ⟨K, hK, ι, hι, κ ∘ κ₀', v ∘ v₀', κ ∘ κ₁', v ∘ v₁', κ₂, v₂, y, Z, ξ, h ≫ h₀', h ≫ h₁', h₂,
    isBlockMap_comp bm₀ bm, isBlockMap_comp bm₁ bm, bm₂, ?_, ?_, hy₂, hall, htie, hnorm, ?_, ?_, hd₂, ?_, ?_⟩
  · rw [e₀, hy₀]
  · rw [e₁, hy₁]
  · show ξ ≫ h ≫ h₀' = _
    rw [← Category.assoc, hξ]; exact hd₀
  · show ξ ≫ h ≫ h₁' = _
    rw [← Category.assoc, hξ]; exact hd₁
  · rw [e₀, hfield]; exact hr₀
  · rw [e₁, hfield]; exact hr₁

end ModelSec

end GlobalTheory.CompanionTheory.Ar.OrLinked

namespace GlobalTheory.CompanionTheory.Ar.OrLinked

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `only [Lat.patch]`. Use `split_ifs with hF`. Use `iInf_congr fun p => iInf_congr fun hp => iInf_congr fun _ => ?_` and prove the remaining obligations. Rewrite using `[h p hp]`.

Both sides reduce to the same expression.
-/
theorem patch_congr {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] (T : Finset ℕ) (L₀ : Lat ξ V) (Lp Lp' : ℕ → Lat ξ V)
    (h : ∀ p ∈ T, Lp p = Lp' p) : Lat.patch T L₀ Lp = Lat.patch T L₀ Lp' := by
  funext q
  simp only [Lat.patch]
  split_ifs with hF
  · refine iInf_congr fun p => iInf_congr fun hp => iInf_congr fun _ => ?_
    rw [h p hp]
  · rfl

/- English proof (translation)
Consider the cases of `M`. Consider the cases of `M'`. Consider the cases of `h`. Both sides reduce to the same expression.
-/
theorem lieModel_ext {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V] [Module R V] {M M' : LieModel G x V}
    (h : M.pt = M'.pt) : M = M' := by
  cases M; cases M'; cases h; rfl

/- English proof (translation)
Establish `ha' : (FrameRebase.sabRebase A'.m hf.symm).φ = A'.m.φ` using `FrameRebase.sabRebase_φ _ _`. Take `⟨k, hk⟩` from `sabCancel pullCubCancel E H _ _ _ Y.t A.t A'.t A.f e.hom A.m (FrameRebase.sabRebase A'.m hf.symm)`. Rewrite `hk` using `[ha']`. Take `⟨M₁, P1, -, -, P4⟩` from `GlobalTheory.T.lie_model_iso_transport E H A.X A'.X e Ω A.ξ A'.ξ A.t A'.t k A.Li A.M he`. Take `⟨φ, hφ, -⟩` from `GlobalTheory.T.lie_model_existsUnique_equiv A'.X A'.t.G Ω A'.ξ A.Li A'.Li M₁ A'.M`.

Establish `hemb : A'.emb = A.emb`. Use function extensionality and compare the values at `s`. Simplify using `only [HodgeCpt.emb]`. Rewrite using `[hc]`. Establish `hact : ∀ a v, φ (A.ρ a v) = A'.ρ a (φ v)`.

Introduce `a v`. Apply `A'.M.inj` to reduce the goal to its premises. Establish `a1 : A.M.pt (A.ρ a v) = A.M.pt v ≫ A.t.act.act a` using `A.act a v`. Establish `a2 : A'.M.pt (A'.ρ a (φ v)) = A'.M.pt (φ v) ≫ A'.t.act.act a` using `A'.act a (φ v)`. Rewrite using `[a2, hφ, hφ]`.

Use `Over.OverMorphism.ext (k.cart.1.hom_ext ?_ ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (M₁.pt v).left ≫ k.cm.F = _ from P1 v]`. Use `_ = (M₁.pt v).left ≫ (A'.t.act.act a).left ≫ k.cm.F := by rw [k.act, Category.assoc]`. Use `_ = (M₁.pt v ≫ A'.t.act.act a).left ≫ k.cm.F := by rw [Over.comp_left, Category.assoc]`.

Rewrite using `[Over.w, Over.w]`. Set `M₂ : LieModel A'.t.G A'.ξ A.Li` to `Flat.lieModelOfEquiv A'.M φ`. Establish `hM : M₁ = M₂` using `lieModel_ext (funext fun v => (hφ v).symm)`. Establish `hT : ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧ (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M₁.htOm A'.t.PP.L n q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L n ⟨e.hom q.1, h⟩` using `P4`. Use `⟨φ, fun v => ?_, fun s v => ?_, fun q h => (hT q h).1, fun T hR s q h v => ?_⟩` and prove the remaining obligations.

Rewrite using `[hφ, hk, ← Category.assoc, P1]`. Use `show v ∈ eigSp A.ρ (A.emb s) ↔ φ v ∈ eigSp A'.ρ (A'.emb s)`. Rewrite using `[hemb]`. Simplify using `only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations.

Rewrite using `[← hact, ← map_smul, φ.injective.eq_iff]`. Establish `e1` using `CmpBund.patch_coe_eq E H A.X A'.X Ω A.ξ A'.ξ A.t.G A'.t.G A.Li A.M M₁ A.t.PP.L A'.t.PP.L T (fun p => p ^ A.R p) A.ρ A.emb s ⟨e.hom q.1, h⟩ q (hT q h).1 (hT q h).2.1 (hT q h).2.2`. Establish `e2` using `CmpBund.patch_comap_equiv E H A'.X Ω A'.ξ A'.t.G A'.Li A.Li A'.M φ A'.t.PP.L T (fun p => p ^ A.R p) A.ρ A'.ρ hact A.emb s`. Establish `e3 : Lat.patch T (A'.dR s) (fun p => A'.HT p s) = Lat.patch T (A'.M.eigLat A'.ρ (A.emb s)) (fun p => htLabel A'.M A'.t.PP.L (p ^ A.R p) A'.ρ A.emb s)`. Establish `: (A'.dR s) = A'.M.eigLat A'.ρ (A.emb s)` using `by show A'.M.eigLat A'.ρ (A'.emb s) = _`.

Rewrite using `[hemb]`. Rewrite using `[this]`. Use `patch_congr _ _ _ _ fun p hp => ?_` and prove the remaining obligations. Use `show htLabel A'.M A'.t.PP.L (p ^ A'.R p) A'.ρ A'.emb s = _`. Rewrite using `[hemb, hR p hp]`.

Rewrite using `[e3]`. Establish `e4 : v ∈ Lat.patch T (A.dR s) (fun p => A.HT p s) ⟨e.hom q.1, h⟩ ↔ v ∈ Lat.patch T (M₁.eigLat A.ρ (A.emb s)) (fun p => htLabel M₁ A'.t.PP.L (p ^ A.R p) A.ρ A.emb s) q`. Conclude with `(Set.ext_iff.1 e1 v).symm`. Rewrite using `[e4, hM, ← e2]`. Conclude with `Iff.rfl`.
-/
theorem same_base_cmp {S₁ S₂ : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} (A : HodgeCpt Y S₁ y) (A' : HodgeCpt Y S₂ y) (e : A'.X ≅ A.X)
    (he : A'.ξ ≫ e.hom = A.ξ) (hf : e.hom ≫ A.f = A'.f) (hc : A.cst = A'.cst) :
    ∃ φ : A.Li ≃ₗ[Ω] A'.Li,
      (∀ v, (A'.M.pt (φ v)).left ≫ A'.m.φ = (A.M.pt v).left ≫ A.m.φ) ∧
      (∀ s v, v ∈ A.Vgen s ↔ φ v ∈ A'.Vgen s) ∧
      (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩) ∧
      ∀ T : Finset ℕ, (∀ p ∈ T, A'.R p = A.R p) → ∀ s (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li),
        v ∈ Lat.patch T (A.dR s) (fun p => A.HT p s) ⟨e.hom q.1, h⟩ ↔
          φ v ∈ Lat.patch T (A'.dR s) (fun p => A'.HT p s) q := by
  have ha' : (FrameRebase.sabRebase A'.m hf.symm).φ = A'.m.φ := FrameRebase.sabRebase_φ _ _
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t A.t A'.t A.f e.hom A.m (FrameRebase.sabRebase A'.m hf.symm)
  rw [ha'] at hk
  obtain ⟨M₁, P1, -, -, P4⟩ := GlobalTheory.T.lie_model_iso_transport E H A.X A'.X e Ω A.ξ A'.ξ A.t A'.t k A.Li A.M he
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv A'.X A'.t.G Ω A'.ξ A.Li A'.Li M₁ A'.M
  have hemb : A'.emb = A.emb := by
    funext s
    simp only [HodgeCpt.emb]
    rw [hc]
  have hact : ∀ a v, φ (A.ρ a v) = A'.ρ a (φ v) := by
    intro a v
    apply A'.M.inj
    have a1 : A.M.pt (A.ρ a v) = A.M.pt v ≫ A.t.act.act a := A.act a v
    have a2 : A'.M.pt (A'.ρ a (φ v)) = A'.M.pt (φ v) ≫ A'.t.act.act a := A'.act a (φ v)
    rw [a2, hφ, hφ]
    refine Over.OverMorphism.ext (k.cart.1.hom_ext ?_ ?_)
    · calc (M₁.pt (A.ρ a v)).left ≫ k.cm.F = (A.M.pt (A.ρ a v)).left := P1 _
        _ = (A.M.pt v).left ≫ (A.t.act.act a).left := by rw [a1]; rfl
        _ = ((M₁.pt v).left ≫ k.cm.F) ≫ (A.t.act.act a).left := by
            rw [show (M₁.pt v).left ≫ k.cm.F = _ from P1 v]
        _ = (M₁.pt v).left ≫ (A'.t.act.act a).left ≫ k.cm.F := by rw [k.act, Category.assoc]
        _ = (M₁.pt v ≫ A'.t.act.act a).left ≫ k.cm.F := by rw [Over.comp_left, Category.assoc]
    · rw [Over.w, Over.w]
  let M₂ : LieModel A'.t.G A'.ξ A.Li := Flat.lieModelOfEquiv A'.M φ
  have hM : M₁ = M₂ := lieModel_ext (funext fun v => (hφ v).symm)
  have hT : ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
      (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
      ∀ n, (M₁.htOm A'.t.PP.L n q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L n ⟨e.hom q.1, h⟩ := P4
  refine ⟨φ, fun v => ?_, fun s v => ?_, fun q h => (hT q h).1, fun T hR s q h v => ?_⟩
  · rw [hφ, hk, ← Category.assoc, P1]
  · show v ∈ eigSp A.ρ (A.emb s) ↔ φ v ∈ eigSp A'.ρ (A'.emb s)
    rw [hemb]
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← hact, ← map_smul, φ.injective.eq_iff]
  · have e1 := CmpBund.patch_coe_eq E H A.X A'.X Ω A.ξ A'.ξ A.t.G A'.t.G A.Li A.M M₁ A.t.PP.L A'.t.PP.L T
      (fun p => p ^ A.R p) A.ρ A.emb s ⟨e.hom q.1, h⟩ q (hT q h).1 (hT q h).2.1 (hT q h).2.2
    have e2 := CmpBund.patch_comap_equiv E H A'.X Ω A'.ξ A'.t.G A'.Li A.Li A'.M φ A'.t.PP.L T
      (fun p => p ^ A.R p) A.ρ A'.ρ hact A.emb s
    have e3 : Lat.patch T (A'.dR s) (fun p => A'.HT p s) = Lat.patch T (A'.M.eigLat A'.ρ (A.emb s))
        (fun p => htLabel A'.M A'.t.PP.L (p ^ A.R p) A'.ρ A.emb s) := by
      have : (A'.dR s) = A'.M.eigLat A'.ρ (A.emb s) := by
        show A'.M.eigLat A'.ρ (A'.emb s) = _
        rw [hemb]
      rw [this]
      refine patch_congr _ _ _ _ fun p hp => ?_
      show htLabel A'.M A'.t.PP.L (p ^ A'.R p) A'.ρ A'.emb s = _
      rw [hemb, hR p hp]
    rw [e3]
    have e4 : v ∈ Lat.patch T (A.dR s) (fun p => A.HT p s) ⟨e.hom q.1, h⟩ ↔
        v ∈ Lat.patch T (M₁.eigLat A.ρ (A.emb s)) (fun p => htLabel M₁ A'.t.PP.L (p ^ A.R p) A.ρ A.emb s) q := by
      exact (Set.ext_iff.1 e1 v).symm
    rw [e4, hM, ← e2]
    exact Iff.rfl

end GlobalTheory.CompanionTheory.Ar.OrLinked

namespace GlobalTheory.CompanionTheory.Ar.OrLinked

section Transport

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V']

/- English proof (translation)
Establish `hg : genPt ξ = e.hom (genPt ξ')`. Rewrite using `[← he]`. Both sides reduce to the same expression. Rewrite using `[hg]`. Conclude with `q.2.map e.hom.base.hom.continuous`.
-/
theorem genPt_spec (e : X' ≅ X) (he : ξ' ≫ e.hom = ξ) (q : Cpt ξ') : genPt ξ ⤳ e.hom q.1 := by
  have hg : genPt ξ = e.hom (genPt ξ') := by
    rw [← he]; rfl
  rw [hg]
  exact q.2.map e.hom.base.hom.continuous

/- English proof (translation)
Simplify using `only [flagStep, Submodule.map_span]`. Use `congr 1`. Use extensionality with `w`. Simplify using `[Set.mem_image]`.
-/
theorem flagStep_comp (φ : V ≃ₗ[Ω] V') {r : ℕ} (b : Fin r → V) (i : ℕ) :
    flagStep Ω (fun k => φ (b k)) i = (flagStep Ω b i).map (φ : V →ₗ[Ω] V') := by
  simp only [flagStep, Submodule.map_span]
  congr 1
  ext w
  simp [Set.mem_image]

/- English proof (translation)
Use `⟨hb.1.map' φ.toLinearMap φ.ker, ?_⟩` and prove the remaining obligations. Establish `hpre : (φ ⁻¹' Set.range fun k => φ (b k)) = Set.range b`. Use extensionality with `v`. Simplify using `only [Set.mem_preimage, Set.mem_range, φ.injective.eq_iff]`. Establish `h1` using `CmpBund.comap_span_equiv (regAt ξ p) φ (Set.range fun k => φ (b k))`.

Rewrite `h1` using `[hpre]`. Use `SetLike.ext' ?_` and prove the remaining obligations. Rewrite using `[CmpBund.span_coe_congr _ _ hr]`. Use extensionality with `w`. Take `⟨v, rfl⟩` from `φ.surjective w`.

Rewrite using `[SetLike.mem_coe, SetLike.mem_coe, ← hm, hb.2, ← h1]`. Both sides reduce to the same expression.
-/
theorem frame_tr {L : Lat ξ V} {L' : Lat ξ' V'} (φ : V ≃ₗ[Ω] V') {p : Cpt ξ} {q : Cpt ξ'}
    (hr : regAt ξ' q = regAt ξ p) (hm : ∀ v, v ∈ L p ↔ φ v ∈ L' q) {r : ℕ} {b : Fin r → V}
    (hb : L.IsFrameAt b p) : L'.IsFrameAt (fun k => φ (b k)) q := by
  refine ⟨hb.1.map' φ.toLinearMap φ.ker, ?_⟩
  have hpre : (φ ⁻¹' Set.range fun k => φ (b k)) = Set.range b := by
    ext v
    simp only [Set.mem_preimage, Set.mem_range, φ.injective.eq_iff]
  have h1 := CmpBund.comap_span_equiv (regAt ξ p) φ (Set.range fun k => φ (b k))
  rw [hpre] at h1
  refine SetLike.ext' ?_
  rw [CmpBund.span_coe_congr _ _ hr]
  ext w
  obtain ⟨v, rfl⟩ := φ.surjective w
  rw [SetLike.mem_coe, SetLike.mem_coe, ← hm, hb.2, ← h1]
  rfl

variable (e : X' ≅ X) (he : ξ' ≫ e.hom = ξ) (φ : V ≃ₗ[Ω] V') {L : Lat ξ V} {L' : Lat ξ' V'}
  (hr : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩)
  (hm : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) (v : V), v ∈ L ⟨e.hom q.1, h⟩ ↔ φ v ∈ L' q)

include he hr hm in
/- English proof (translation)
Introduce `p' _`. Take `⟨U, hU, b, hb, hfr⟩` from `hL ⟨e.hom p'.1, genPt_spec e he p'⟩ trivial`. Use `⟨e.hom ⁻¹ᵁ U, hU, fun k => φ (b k), ?_, fun q' _ hq' => ?_⟩` and prove the remaining obligations. Establish `: W' = W.map (φ : V →ₗ[Ω] V')`. Use extensionality with `w`.

Take `⟨v, rfl⟩` from `φ.surjective w`. Rewrite using `[← hW]`. Simplify using the standard rewrite rules. Rewrite using `[this, ← hb, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.

Conclude with `frame_tr φ (hr q' _) (hm q' (genPt_spec e he q')) (hfr ⟨e.hom q'.1, genPt_spec e he q'⟩ trivial hq')`.
-/
theorem isVB_tr {r : ℕ} {W : Submodule Ω V} {W' : Submodule Ω V'} (hW : ∀ v, v ∈ W ↔ φ v ∈ W')
    (hL : L.IsVB r W) : L'.IsVB r W' := by
  intro p' _
  obtain ⟨U, hU, b, hb, hfr⟩ := hL ⟨e.hom p'.1, genPt_spec e he p'⟩ trivial
  refine ⟨e.hom ⁻¹ᵁ U, hU, fun k => φ (b k), ?_, fun q' _ hq' => ?_⟩
  · have : W' = W.map (φ : V →ₗ[Ω] V') := by
      ext w
      obtain ⟨v, rfl⟩ := φ.surjective w
      rw [← hW]
      simp
    rw [this, ← hb, Submodule.map_span, ← Set.range_comp]
    rfl
  · exact frame_tr φ (hr q' _) (hm q' (genPt_spec e he q')) (hfr ⟨e.hom q'.1, genPt_spec e he q'⟩ trivial hq')

include he hr hm in
/- English proof (translation)
Introduce `p' _`. Take `⟨U, hU, b, hb, hfr⟩` from `hL ⟨e.hom p'.1, genPt_spec e he p'⟩ trivial`. Use `⟨e.hom ⁻¹ᵁ U, hU, fun k => φ (b k), fun i => ?_, fun q' _ hq' => ?_⟩` and prove the remaining obligations. Rewrite using `[flagStep_comp, flagStep_comp, hb]`. Conclude with `frame_tr φ (hr q' _) (hm q' (genPt_spec e he q')) (hfr ⟨e.hom q'.1, genPt_spec e he q'⟩ trivial hq')`.
-/
theorem isFlagVB_tr {r : ℕ} {b₀ : Fin r → V} (hL : L.IsFlagVBOn Set.univ b₀) :
    L'.IsFlagVBOn Set.univ (fun k => φ (b₀ k)) := by
  intro p' _
  obtain ⟨U, hU, b, hb, hfr⟩ := hL ⟨e.hom p'.1, genPt_spec e he p'⟩ trivial
  refine ⟨e.hom ⁻¹ᵁ U, hU, fun k => φ (b k), fun i => ?_, fun q' _ hq' => ?_⟩
  · rw [flagStep_comp, flagStep_comp, hb]
  · exact frame_tr φ (hr q' _) (hm q' (genPt_spec e he q')) (hfr ⟨e.hom q'.1, genPt_spec e he q'⟩ trivial hq')

include hr hm in
/- English proof (translation)
Simplify using `only [Lat.gr]`. Rewrite using `[CmpBund.span_coe_congr _ _ (hr q h)]`. Use `congr 2`. Use extensionality with `t`. Simplify using `only [Set.mem_ofPred_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, hs⟩`. Take `⟨v, rfl⟩` from `φ.surjective w`. Use `⟨v, (hm q h v).2 hw, ?_⟩` and prove the remaining obligations. Rewrite `hs` using `[flagStep_comp]`.

Take `⟨u, hu, hu'⟩` from `Submodule.mem_map.1 hs`. Establish `: u = v - t • b₀ i` using `φ.injective (by`. Simplify `hu')` using `[map_sub, map_smul]`. Rewrite using `[← this]` and apply the resulting hypothesis. Introduce and unpack `⟨v, hv, hs⟩`.

Use `⟨φ v, (hm q h v).1 hv, ?_⟩` and prove the remaining obligations. Rewrite using `[flagStep_comp]`. Conclude with `Submodule.mem_map.2 ⟨_, hs, by simp [map_sub, map_smul]⟩`.
-/
theorem gr_tr {r : ℕ} (b₀ : Fin r → V) (i : Fin r) (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1) :
    (L'.gr (fun k => φ (b₀ k)) i q : Set Ω) = L.gr b₀ i ⟨e.hom q.1, h⟩ := by
  simp only [Lat.gr]
  rw [CmpBund.span_coe_congr _ _ (hr q h)]
  congr 2
  ext t
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, hs⟩
    obtain ⟨v, rfl⟩ := φ.surjective w
    refine ⟨v, (hm q h v).2 hw, ?_⟩
    rw [flagStep_comp] at hs
    obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.1 hs
    have : u = v - t • b₀ i := φ.injective (by
      simpa [map_sub, map_smul] using hu')
    rwa [← this]
  · rintro ⟨v, hv, hs⟩
    refine ⟨φ v, (hm q h v).1 hv, ?_⟩
    rw [flagStep_comp]
    exact Submodule.mem_map.2 ⟨_, hs, by simp [map_sub, map_smul]⟩

end Transport

section Deg

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}

/- English proof (translation)
Establish `hg : ∀ t, Λ'.IsGenAt q t ↔ Λ.IsGenAt ⟨e.hom q.1, h⟩ t`. Introduce `t`. Simplify using `only [Lat.IsGenAt]`. Use `and_congr Iff.rfl ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `h'`. Use `SetLike.ext' ?_` and prove the remaining obligations. Rewrite using `[← hΛ, h', CmpBund.span_coe_congr _ _ hr]`. Introduce `h'`. Use `SetLike.ext' ?_` and prove the remaining obligations.

Rewrite using `[hΛ, h', CmpBund.span_coe_congr _ _ hr]`. Simplify using `only [Lat.tens]`. Rewrite using `[CmpBund.span_coe_congr _ _ hr]`. Use `congr 2`. Use extensionality with `t`.

Simplify using `only [Set.mem_ofPred_eq, hg]`.
-/
theorem tens_tr (e : X' ≅ X) {Λ : Lat ξ Ω} {Λ' : Lat ξ' Ω} (a : ℤ) (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1)
    (hr : regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩) (hΛ : (Λ' q : Set Ω) = Λ ⟨e.hom q.1, h⟩) :
    (Lat.tens (fun _ : Unit => Λ') (fun _ => a) q : Set Ω) =
      Lat.tens (fun _ : Unit => Λ) (fun _ => a) ⟨e.hom q.1, h⟩ := by
  have hg : ∀ t, Λ'.IsGenAt q t ↔ Λ.IsGenAt ⟨e.hom q.1, h⟩ t := by
    intro t
    simp only [Lat.IsGenAt]
    refine and_congr Iff.rfl ?_
    constructor
    · intro h'
      refine SetLike.ext' ?_
      rw [← hΛ, h', CmpBund.span_coe_congr _ _ hr]
    · intro h'
      refine SetLike.ext' ?_
      rw [hΛ, h', CmpBund.span_coe_congr _ _ hr]
  simp only [Lat.tens]
  rw [CmpBund.span_coe_congr _ _ hr]
  congr 2
  ext t
  simp only [Set.mem_ofPred_eq, hg]

/- English proof (translation)
Use `⟨hL.1, fun q _ c hc => ?_⟩` and prove the remaining obligations. Establish `h` using `genPt_spec e he q`. Establish `h1` using `hL.2 ⟨e.hom q.1, h⟩ trivial c ⟨hc.1, fun c' => by rw [← hr q h]; exact hc.2 c'⟩`. Use `SetLike.ext' ?_` and prove the remaining obligations. Rewrite using `[hΛ q h, h1, CmpBund.span_coe_congr _ _ (hr q h)]`.
-/
theorem isDegOn_tr (e : X' ≅ X) (he : ξ' ≫ e.hom = ξ) {Λ : Lat ξ Ω} {Λ' : Lat ξ' Ω}
    (hr : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩)
    (hΛ : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), (Λ' q : Set Ω) = Λ ⟨e.hom q.1, h⟩)
    {K : Type} [Fintype K] {J : K → Type} (y : (Σ k, J k) → Ω) (a : K → ℤ) (e₀ : Ω)
    (hL : Λ.IsDegOn Set.univ y a e₀) : Λ'.IsDegOn Set.univ y a e₀ := by
  refine ⟨hL.1, fun q _ c hc => ?_⟩
  have h := genPt_spec e he q
  have h1 := hL.2 ⟨e.hom q.1, h⟩ trivial c ⟨hc.1, fun c' => by rw [← hr q h]; exact hc.2 c'⟩
  refine SetLike.ext' ?_
  rw [hΛ q h, h1, CmpBund.span_coe_congr _ _ (hr q h)]

end Deg

end GlobalTheory.CompanionTheory.Ar.OrLinked

namespace GlobalTheory.CompanionTheory.Ar.OrLinked

section Om

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Establish `hN : 0 < p ^ A.R p` using `pow_pos (A.S_prime p hp).pos _`. Establish `hn : p ^ A.R p ≠ 0` using `hN.ne'`. Establish `hy' : A'.ξ ≫ A'.f = (spMap i ≫ y₀) ≫ Y.j`. Establish `hd' : A'.ξ ≫ g = spMap i ≫ A.ξ` using `hd`. Rewrite using `[hf, ← Category.assoc, hd', Category.assoc, hy, Category.assoc]`.

Establish `hfd : FiniteDimensional Ω A.Li` using `(GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y A.X Ω A.ξ A.f y₀ A.t A.m A.Li A.M A.ρ A.cst hy A.cst_over A.act).1`. Take `⟨-, hspan, -⟩` from `GlobalTheory.T.lie_lattice_dominant_compat A.X A'.X Ω Ω' A.ξ A'.ξ g i A.t.G A'.t.G m.φ A.Li A'.Li A.M A'.M j₁ A.tie.gen A'.tie.gen hd m.cart A.t.semi.smooth hpt`. Take `⟨hrk, jd, hadj, hsm, hjs⟩` from `HFlag.exists_adjoint hext hspan`. Take `⟨s0, o, ⟨m0⟩⟩` from `GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ y₀ hy`. Take `⟨s0', o', ⟨m0'⟩⟩` from `GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A'.X A'.f A'.t A'.m Ω' A'.ξ (spMap i ≫ y₀) hy'`.

Use `((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1` as an intermediate fact. Use `((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω' A'.ξ ℤ _ _ A'.tie).2 A'.all).1` as an intermediate fact. Establish `htors' : FullTorsion A'.t.G A'.ξ (p ^ A.R p)`. Use `A'.tors p hp` as an intermediate fact. Rewrite `this` using `[hR]`. Then use the resulting hypothesis.

Establish `key : A'.M.htOm A'.t.PP.L (p ^ A.R p) = (A.M.htOm A.t.PP.L (p ^ A.R p)).pull A'.ξ g jd`. Break down `Nat.eq_zero_or_pos (D.p + D.q) with hpq | hpq` into its components or cases. Conclude with `(GlobalTheory.T.hodge_tate_weil_pullback A.X Ω A.ξ A.tie.gen ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω A.ξ A.tie.gen A.all).2.2 A.normal) A.t.G A.t.semi A.t.PP.L _ (Nat.one_le_iff_ne_zero.2 hn) (A.tors p hp) _ (OmLink.genWeil_trivial o A.t m0 hN hpq) A.Li A.M A'.X Ω' A'.ξ …`. Use function extensionality and compare the values at `p'`. Establish `hsp : genPt A.ξ ⤳ g p'.1` using `LatModel.dominates_spec hd p'`.

Establish `hnoeth` using `(GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1`. Establish `hnoeth'` using `(GlobalTheory.T.regAt_noetherian_model_noetherian A'.X Ω' A'.ξ ℤ _ _ A'.tie).1`. Establish `hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (g p'.1))` using `(A.normal _).2`. Establish `hn1 : IsNoetherianRing (A.X.presheaf.stalk (g p'.1))` using `HcptPull.noeth_stalk A.tie.gen ⟨g p'.1, hsp⟩ (hnoeth _)`. Establish `h1` using `GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨g p'.1, hsp⟩ A.tie.gen hN (A.tors p hp) hc1 hn1`.

Establish `h1'` using `GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A'.X Ω' A'.ξ s0' o' A'.t m0' A'.Li A'.M (p ^ A.R p) p' A'.tie.gen hN htors' (A'.normal _).2 (HcptPull.noeth_stalk A'.tie.gen _ (hnoeth' _))`. Establish `h2` using `GlobalTheory.T.omega_lattice_dominant_compat A.X A'.X Ω Ω' A.ξ A'.ξ g i A.t.G A'.t.G m.φ A.Li A'.Li A.M A'.M j₁ A.tie.gen A'.tie.gen hd m.cart A.t.semi.smooth hpt jd hadj (p ^ A.R p) hN p' hsp hc1 hn1 (h1.2.1 hpq) h1.1`. Rewrite using `[h1'.2.2, h2, HcptPull.pull_eq A'.ξ g _ jd p' hsp, HcptPull.pull_eq A'.ξ g _ jd p' hsp, h1.2.2]`. Establish `h2` using `GlobalTheory.T.lattice_vector_bundle_pullback A.X Ω A.ξ (Module.Dual Ω A.Li) A'.X Ω' A'.ξ g i (Module.Dual Ω' A'.Li) jd (HT.omP A p) {q | InFibre A.ξ p q} _ ⊤ hd hsm (fun _ _ hb => HFlag.li_of_adjoint j₁ jd hadj hb) h`. Establish `key' : HT.omP A' p = (HT.omP A p).pull A'.ξ g jd` using `by show A'.M.htOm A'.t.PP.L (p ^ A'.R p) = _`.

Rewrite using `[hR]`. Conclude with `key`. Rewrite `h2` using `[← key', hjs, ← hrk]`. Use `HFlag.isVBOn_mono (fun q hq => ?_) h2` and prove the remaining obligations. Use `⟨LatModel.dominates_spec hd q, fun hu => hq ?_⟩` and prove the remaining obligations.

Establish `hu' : unitAt A.ξ ⟨g q.1, LatModel.dominates_spec hd q⟩ (p : Ω)` using `hu`. Establish `e1 : (p : Ω') = i (p : Ω)` using `(map_natCast i p).symm`. Establish `e2 : (p : Ω')⁻¹ = i (p : Ω)⁻¹` using `by rw [map_inv₀, map_natCast]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`.

Conclude with `(map_ne_zero i).2 hu'.1`. Rewrite using `[e1]`. Conclude with `LatModel.dominates_regAt hd q _ hu'.2.1`. Rewrite using `[e2]`. Conclude with `LatModel.dominates_regAt hd q _ hu'.2.2`.
-/
theorem omP_ext' {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [CharZero Ω]
    [Field Ω'] [CharZero Ω'] (i : Ω →+* Ω') {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
    [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'} (A : HodgeCpt Y S y)
    (A' : HodgeCpt Y S y') (g : A'.X ⟶ A.X) (m : SABMap A'.t A.t g) (j₁ : A.Li →+ A'.Li) (y₀ : Sp Ω ⟶ Xo.XF c)
    (p : ℕ) (hp : p ∈ S) (hd : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ g i) (hf : A'.f = g ≫ A.f) (hR : A'.R = A.R)
    (hext : IsExtOver i j₁) (hpt : ∀ v, (A'.M.pt (j₁ v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left)
    (hy : A.ξ ≫ A.f = y₀ ≫ Y.j)
    (h : (HT.omP A p).IsVBOn {q | InFibre A.ξ p q} (Module.finrank Ω A.Li) ⊤) :
    (HT.omP A' p).IsVBOn {q | InFibre A'.ξ p q} (Module.finrank Ω' A'.Li) ⊤ := by
  classical
  have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
  have hn : p ^ A.R p ≠ 0 := hN.ne'
  have hy' : A'.ξ ≫ A'.f = (spMap i ≫ y₀) ≫ Y.j := by
    have hd' : A'.ξ ≫ g = spMap i ≫ A.ξ := hd
    rw [hf, ← Category.assoc, hd', Category.assoc, hy, Category.assoc]
  have hfd : FiniteDimensional Ω A.Li :=
    (GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y A.X Ω A.ξ A.f y₀ A.t A.m A.Li A.M A.ρ A.cst hy A.cst_over A.act).1
  obtain ⟨-, hspan, -⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X A'.X Ω Ω' A.ξ A'.ξ g i A.t.G A'.t.G m.φ A.Li A'.Li A.M A'.M j₁
    A.tie.gen A'.tie.gen hd m.cart A.t.semi.smooth hpt
  obtain ⟨hrk, jd, hadj, hsm, hjs⟩ := HFlag.exists_adjoint hext hspan
  obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ y₀ hy
  obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A'.X A'.f A'.t A'.m Ω' A'.ξ (spMap i ≫ y₀) hy'
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω' A'.ξ ℤ _ _ A'.tie).2 A'.all).1
  have htors' : FullTorsion A'.t.G A'.ξ (p ^ A.R p) := by
    have := A'.tors p hp
    rwa [hR] at this
  have key : A'.M.htOm A'.t.PP.L (p ^ A.R p) = (A.M.htOm A.t.PP.L (p ^ A.R p)).pull A'.ξ g jd := by
    rcases Nat.eq_zero_or_pos (D.p + D.q) with hpq | hpq
    · exact (GlobalTheory.T.hodge_tate_weil_pullback A.X Ω A.ξ A.tie.gen ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω A.ξ A.tie.gen A.all).2.2 A.normal) A.t.G A.t.semi
        A.t.PP.L _ (Nat.one_le_iff_ne_zero.2 hn) (A.tors p hp) _ (OmLink.genWeil_trivial o A.t m0 hN hpq) A.Li A.M A'.X Ω' A'.ξ A'.tie.gen
        ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω' A'.ξ A'.tie.gen A'.all).2.2 A'.normal) g i hd A'.t.G m.φ m.cart A'.t.PP.L _
        (OmLink.genWeil_trivial o' A'.t m0' hN hpq) A'.Li A'.M j₁ jd hpt hadj).1
    · funext p'
      have hsp : genPt A.ξ ⤳ g p'.1 := LatModel.dominates_spec hd p'
      have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
      have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian A'.X Ω' A'.ξ ℤ _ _ A'.tie).1
      have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (g p'.1)) := (A.normal _).2
      have hn1 : IsNoetherianRing (A.X.presheaf.stalk (g p'.1)) :=
        HcptPull.noeth_stalk A.tie.gen ⟨g p'.1, hsp⟩ (hnoeth _)
      have h1 := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨g p'.1, hsp⟩
        A.tie.gen hN (A.tors p hp) hc1 hn1
      have h1' := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A'.X Ω' A'.ξ s0' o' A'.t m0' A'.Li A'.M (p ^ A.R p) p'
        A'.tie.gen hN htors' (A'.normal _).2 (HcptPull.noeth_stalk A'.tie.gen _ (hnoeth' _))
      have h2 := GlobalTheory.T.omega_lattice_dominant_compat A.X A'.X Ω Ω' A.ξ A'.ξ g i A.t.G A'.t.G m.φ A.Li A'.Li A.M A'.M j₁ A.tie.gen
        A'.tie.gen hd m.cart A.t.semi.smooth hpt jd hadj (p ^ A.R p) hN p' hsp hc1 hn1 (h1.2.1 hpq) h1.1
      rw [h1'.2.2, h2, HcptPull.pull_eq A'.ξ g _ jd p' hsp, HcptPull.pull_eq A'.ξ g _ jd p' hsp, h1.2.2]
  have h2 := GlobalTheory.T.lattice_vector_bundle_pullback A.X Ω A.ξ (Module.Dual Ω A.Li) A'.X Ω' A'.ξ g i (Module.Dual Ω' A'.Li) jd (HT.omP A p)
    {q | InFibre A.ξ p q} _ ⊤ hd hsm (fun _ _ hb => HFlag.li_of_adjoint j₁ jd hadj hb) h
  have key' : HT.omP A' p = (HT.omP A p).pull A'.ξ g jd := by
    show A'.M.htOm A'.t.PP.L (p ^ A'.R p) = _
    rw [hR]
    exact key
  rw [← key', hjs, ← hrk] at h2
  refine HFlag.isVBOn_mono (fun q hq => ?_) h2
  refine ⟨LatModel.dominates_spec hd q, fun hu => hq ?_⟩
  have hu' : unitAt A.ξ ⟨g q.1, LatModel.dominates_spec hd q⟩ (p : Ω) := hu
  have e1 : (p : Ω') = i (p : Ω) := (map_natCast i p).symm
  have e2 : (p : Ω')⁻¹ = i (p : Ω)⁻¹ := by rw [map_inv₀, map_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact (map_ne_zero i).2 hu'.1
  · rw [e1]; exact LatModel.dominates_regAt hd q _ hu'.2.1
  · rw [e2]; exact LatModel.dominates_regAt hd q _ hu'.2.2

end Om

end GlobalTheory.CompanionTheory.Ar.OrLinked

namespace GlobalTheory.CompanionTheory.Ar.OrLinked

/- English proof (translation)
Simplify using `[spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Use `Spec.map_injective h` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Establish `: IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))`. Use `infer_instance`.
-/
theorem mono_int' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  infer_instance

/- English proof (translation)
Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Conclude with `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h`.
-/
theorem ringHom_ext_int {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {Ω : Type} [Field Ω] {f g : c.F →+* Ω} (h : f.comp (algebraMap (𝓞 c.F) c.F) = g.comp (algebraMap (𝓞 c.F) c.F)) :
    f = g := by
  have := c.fin
  have : NumberField c.F := {}
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h

/- English proof (translation)
Establish `: IsReduced Z`. Establish `: ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x)` using `fun x => by`. Use `(hn x).1` as an intermediate fact. Use `infer_instance`. Conclude with `isReduced_of_isReduced_stalk Z`.

Establish `: IsDominant ξ`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[DenseRange, dense_iff_inter_open]`. Introduce `U hU ⟨q, hq⟩`. Conclude with `⟨genPt ξ, (hall q).mem_open hU hq, ⟨_, rfl⟩⟩`.

Establish `hp : IsProper s` using `GlobalTheory.ProperFamily.isProper_of_isProjOver hs`. Establish `: W.IsSeparated` using `⟨by rw [← Limits.terminal.comp_from s]; infer_instance⟩`. Conclude with `ext_of_isDominant_of_isSeparated (Limits.terminal.from W) (Limits.terminal.hom_ext _ _) ξ h`.
-/
theorem map_eq_of_generic {Z W : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z} {R : Type} [CommRing R]
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (hall : ∀ q : Z, genPt ξ ⤳ q) (s : W ⟶ Sp R) (hs : IsProjOver s)
    {u v : Z ⟶ W} (h : ξ ≫ u = ξ ≫ v) : u = v := by
  have : IsReduced Z := by
    have : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x => by
      have := (hn x).1
      infer_instance
    exact isReduced_of_isReduced_stalk Z
  have : IsDominant ξ := by
    refine ⟨?_⟩
    rw [DenseRange, dense_iff_inter_open]
    intro U hU ⟨q, hq⟩
    exact ⟨genPt ξ, (hall q).mem_open hU hq, ⟨_, rfl⟩⟩
  have hp : IsProper s := GlobalTheory.ProperFamily.isProper_of_isProjOver hs
  have : W.IsSeparated := ⟨by rw [← Limits.terminal.comp_from s]; infer_instance⟩
  exact ext_of_isDominant_of_isSeparated (Limits.terminal.from W) (Limits.terminal.hom_ext _ _) ξ h

end GlobalTheory.CompanionTheory.Ar.OrLinked

namespace GlobalTheory.CompanionTheory.Ar.OrLinked

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S₀ S M₀ M₁ Rf Sys Fx o₀ o₁ oR hS hdisc hv₀ hv₁ hRR hdeg`. Establish `hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F))` using `mono_int' c`. Establish `pos₀ : 0 < o₀.Fl.deg`. Use `M₀.δ_pos` as an intermediate fact. Rewrite `this` using `[o₀.δ_eq]`.

Conclude with `Nat.pos_of_mul_pos_left this`. Establish `pos₁ : 0 < o₁.Fl.deg`. Use `M₁.δ_pos` as an intermediate fact. Rewrite `this` using `[o₁.δ_eq]`. Conclude with `Nat.pos_of_mul_pos_left this`.

Establish `cz₀ : CharZero M₀.Ω` using `charZero_of_injective_ringHom o₀.𝔐.cst.injective`. Establish `cz₁ : CharZero M₁.Ω` using `charZero_of_injective_ringHom o₁.𝔐.cst.injective`. Take `⟨Ω, fΩ, cz, i₀, i₁, iR, e0, e1, fd₀, fd₁, fdR, hne, htower⟩` from `exists_common_field Fx.Ωf M₀.Ω M₁.Ω Rf.Ω o₀.g o₁.g oR.g o₀.Fl.deg o₁.Fl.deg pos₀ pos₁ o₀.g_deg o₁.g_deg (oR.g_deg.trans hdeg)`. Take `⟨K, hK, J, hJ, κ₀, v₀, κ₁, v₁, κR, vR, y, Z, ξ, h₀, h₁, hRm, bm₀, bm₁, bmR, hy₀, hy₁, hyR, hall, htie, hnorm, hd₀, hd₁, -, hr₀, hr₁⟩` from `exists_common_model M₀.K M₀.ι M₁.K M₁.ι Rf.K Rf.ι M₀.Ω M₁.Ω Rf.Ω Ω i₀ i₁ iR M₀.y M₁.y Rf.y (dimFl (CMType H) (D.p + D.q) + 1) o₀.𝔐.X o₁.𝔐.X oR.𝔐.X o₀.𝔐.ξ o₁.𝔐.ξ oR.𝔐.ξ M₀.arith M₁.arith Rf.arith M₀.birational M₁.birational Rf.birational fd₀ fd₁ fdR o₀.𝔐.all o₁.𝔐.all oR.𝔐.all o₀.𝔐 …`. Take `⟨x₀, hx₀'⟩` from `GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S₀ M₀.Ω M₀.K M₀.ι M₀.y o₀.𝔐 hmono`.

Take `⟨x₁, hx₁'⟩` from `GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S M₁.Ω M₁.K M₁.ι M₁.y o₁.𝔐 hmono`. Establish `hx₀ : o₀.𝔐.ξ ≫ o₀.𝔐.f = (spMap o₀.𝔐.fn ≫ x₀) ≫ Y.j`. Rewrite using `[Category.assoc, ← hx₀']`. Conclude with `o₀.𝔐.fn_over`. Establish `hx₁ : o₁.𝔐.ξ ≫ o₁.𝔐.f = (spMap o₁.𝔐.fn ≫ x₁) ≫ Y.j`.

Rewrite using `[Category.assoc, ← hx₁']`. Conclude with `o₁.𝔐.fn_over`. Establish `hdisc₁ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S` using `fun p hp hd => hS (hdisc p hp hd)`. Take `⟨A, a₀, j₀, m₀, p1, p2, p3, p4, p5, p6, p7, -, p9⟩` from `GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S₀ M₀.Ω Ω i₀ M₀.K K M₀.ι J M₀.y y o₀.𝔐 _ Z ξ h₀ hx₀ hdisc (fun p hp s => (hv₀ p hp).2 s) hall htie hnorm hd₀`. Take `⟨𝔐, a₁, j₁, m₁, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩` from `GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S M₁.Ω Ω i₁ M₁.K K M₁.ι J M₁.y y o₁.𝔐 _ Z ξ h₁ hx₁ hdisc₁ (fun p hp s => (hv₁ p hp).2 s) hall htie hnorm hd₁`.

Establish `hdom₀ : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ o₀.𝔐.ξ (a₀.hom ≫ h₀) i₀` using `by show A.ξ ≫ a₀.hom ≫ h₀ = _`. Rewrite using `[← Category.assoc, p1]`. Conclude with `hd₀`. Establish `hdom₁ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o₁.𝔐.ξ (a₁.hom ≫ h₁) i₁` using `by show 𝔐.ξ ≫ a₁.hom ≫ h₁ = _`. Rewrite using `[← Category.assoc, q1]`.

Conclude with `hd₁`. Establish `hf₀ : A.f = (a₀.hom ≫ h₀) ≫ o₀.𝔐.f` using `by rw [p2, Category.assoc]`. Establish `hf₁ : 𝔐.f = (a₁.hom ≫ h₁) ≫ o₁.𝔐.f` using `by rw [q2, Category.assoc]`. Take `⟨Fl₀, hb₀, -, -, hl₀⟩` from `FlagPull.flag_pull E H D l Xo c _ _ Y S₀ M₀.Ω Ω i₀ M₀.K K M₀.ι J M₀.y y o₀.𝔐 A (a₀.hom ≫ h₀) j₀ m₀ κ₀ v₀ o₀.Fl bm₀ (fun q => congrFun hy₀ q) hdom₀ hf₀ p3 p4 p6 p7 p9 fd₀`. Take `⟨Fl, hb₁, -, -, hl₁⟩` from `FlagPull.flag_pull E H D l Xo c _ _ Y S M₁.Ω Ω i₁ M₁.K K M₁.ι J M₁.y y o₁.𝔐 𝔐 (a₁.hom ≫ h₁) j₁ m₁ κ₁ v₁ o₁.Fl bm₁ (fun q => congrFun hy₁ q) hdom₁ hf₁ q3 q4 q6 q7 q9 fd₁`.

Establish `e01 : i₀.comp o₀.g = i₁.comp o₁.g` using `e0.trans e1.symm`. Establish `hZ : h₀ ≫ o₀.𝔐.f = h₁ ≫ o₁.𝔐.f`. Use `map_eq_of_generic hnorm hall Y.s Y.proj ?_` and prove the remaining obligations. Establish `g0 : ξ ≫ h₀ = spMap i₀ ≫ o₀.𝔐.ξ` using `hd₀`. Establish `g1 : ξ ≫ h₁ = spMap i₁ ≫ o₁.𝔐.ξ` using `hd₁`.

Rewrite using `[← Category.assoc, ← Category.assoc, g0, g1, Category.assoc, Category.assoc, o₀.g_over, o₁.g_over, ← Category.assoc, ← Category.assoc, spMap_spMap', spMap_spMap', e01]`. Set `e : 𝔐.X ≅ A.X` to `a₁ ≪≫ a₀.symm`. Establish `he : 𝔐.ξ ≫ e.hom = A.ξ`. Simplify using `only [e, Iso.trans_hom, Iso.symm_hom]`. Rewrite using `[← Category.assoc, q1, ← p1, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.

Establish `hf : e.hom ≫ A.f = 𝔐.f`. Simplify using `only [e, Iso.trans_hom, Iso.symm_hom]`. Rewrite using `[p2, q2, ← hZ]`. Simplify using the standard rewrite rules. Establish `hc : A.cst = 𝔐.cst`.

Use `ringHom_ext_int c (spMap_inj' ?_)` and prove the remaining obligations. Rewrite using `[← A.cst_over, ← 𝔐.cst_over, ← hf, ← he]`. Simplify using `only [Category.assoc]`. Take `⟨φ, φt, φV, φr, φp⟩` from `same_base_cmp A 𝔐 e he hf hc`. Establish `hRS : ∀ p ∈ S₀, 𝔐.R p = A.R p` using `fun p hp => by rw [p5, q5]; exact (hRR p hp).symm`.

Establish `hbφ : ∀ s k, Fl.b s k = φ (Fl₀.b s k)`. Introduce `s k`. Apply `𝔐.M.inj` to reduce the goal to its premises. Use `Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))` and prove the remaining obligations. Use `show (𝔐.M.pt (Fl.b s k)).left ≫ 𝔐.m.φ = (𝔐.M.pt (φ (Fl₀.b s k))).left ≫ 𝔐.m.φ`.

Rewrite using `[φt, hb₀, hb₁, p3, q3, ← Category.assoc, ← Category.assoc, q7, p7, Category.assoc, Category.assoc, o₀.g_flag, o₁.g_flag, ← Category.assoc, ← Category.assoc, spMap_spMap', spMap_spMap', ← FlagPull.dualMap_comp, ← FlagPull.dualMap_comp, e01]`. Establish `hbf : ∀ s, Fl.b s = fun k => φ (Fl₀.b s k)` using `fun s => funext (hbφ s)`. Establish `hm` using `φp S₀ hRS`. Establish `hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)` using `fun s => isVB_tr e he φ φr (hm s) (φV s) (A.vb s)`. Establish `hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)` using `fun s => by`.

Rewrite using `[hbf s]`. Conclude with `isFlagVB_tr e he φ φr (hm s) (Fl₀.sub s)`. Establish `hlines : (Fl.shrink S₀ hS hvb hsub).RootLines (fun r => pullDeg κ₀ (M₀.xdeg r)) (fun r => i₀ (o₀.e r))`. Introduce `r`. Use `isDegOn_tr (Λ := Fl₀.rootLat r) e he φr (fun q h => ?_) y _ _ (hl₀ _ _ o₀.lines r)` and prove the remaining obligations.

Use `tens_tr e _ q h (φr q h) ?_` and prove the remaining obligations. Use `show ((𝔐.VAt S₀ (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 q : Set Ω) = _`. Rewrite using `[hbf]`. Conclude with `gr_tr e φ φr (hm _) _ _ q h`. Use `⟨Ω, fΩ, cz, K, hK, J, hJ, y, κ₀, v₀, κ₁, v₁, κR, vR, i₀, i₁, iR, 𝔐, Fl, bm₀, bm₁, bmR, fun p => congrFun hy₀ p, fun p => congrFun hy₁ p, fun p => congrFun hyR p, e0, e1, ?_, ?_, ⟨hS, hvb, hsub, hlines⟩, hl₁ _ _ o₁.lines, fun p hp => ⟨?_, q8 p hp⟩⟩` and prove the remaining obligations.

Rewrite using `[hr₀]`. Conclude with `hne`. Rewrite using `[hr₀, hr₁, o₀.δ_eq, o₁.δ_eq, mul_left_comm, mul_left_comm (Module.finrank i₁.fieldRange Ω), htower]`. Conclude with `omP_ext' i₁ o₁.𝔐 𝔐 (a₁.hom ≫ h₁) m₁ j₁ _ p hp hdom₁ hf₁ q5 q6 q7 hx₁ (hv₁ p hp).1`.
-/
theorem common : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (M₀ M₁ Rf : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (oR : RootOrigin Y ∅ Rf Fx), S₀ ⊆ S → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S₀) → o₀.𝔐.OmVB → o₁.𝔐.OmVB → (∀ p ∈ S₀, o₀.𝔐.R p = o₁.𝔐.R p) → oR.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (κ₀ : M₀.K → K) (v₀ : (Σ k, M₀.ι k) → Σ k, J k) (κ₁ : M₁.K → K) (v₁ : (Σ k, M₁.ι k) → Σ k, J k) (κR : Rf.K → K) (vR : (Σ k, Rf.ι k) → Σ k, J k) (i₀ : M₀.Ω →+* Ω) (i₁ : M₁.Ω →+* Ω) (iR : Rf.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), IsBlockMap κ₀ v₀ ∧ IsBlockMap κ₁ v₁ ∧ IsBlockMap κR vR ∧ (∀ p, y (v₀ p) = i₀ (M₀.y p)) ∧ (∀ p, y (v₁ p) = i₁ (M₁.y p)) ∧ (∀ p, y (vR p) = iR (Rf.y p)) ∧ i₀.comp o₀.g = iR.comp oR.g ∧ i₁.comp o₁.g = iR.comp oR.g ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₀)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₀)) (blockFnField y) * M₀.δ = IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) * M₁.δ ∧ (∃ (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)), (Fl.shrink S₀ h hvb hsub).RootLines (fun r => pullDeg κ₀ (M₀.xdeg r)) (fun r => i₀ (o₀.e r))) ∧ Fl.RootLines (fun r => pullDeg κ₁ (M₁.xdeg r)) (fun r => i₁ (o₁.e r)) ∧ ∀ p ∈ S, HT.HTFree 𝔐 p := by
  intro E _ _ _ H D l Xo c Y S₀ S M₀ M₁ Rf Sys Fx o₀ o₁ oR hS hdisc hv₀ hv₁ hRR hdeg
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := mono_int' c
  have pos₀ : 0 < o₀.Fl.deg := by
    have := M₀.δ_pos
    rw [o₀.δ_eq] at this
    exact Nat.pos_of_mul_pos_left this
  have pos₁ : 0 < o₁.Fl.deg := by
    have := M₁.δ_pos
    rw [o₁.δ_eq] at this
    exact Nat.pos_of_mul_pos_left this
  have cz₀ : CharZero M₀.Ω := charZero_of_injective_ringHom o₀.𝔐.cst.injective
  have cz₁ : CharZero M₁.Ω := charZero_of_injective_ringHom o₁.𝔐.cst.injective
  obtain ⟨Ω, fΩ, cz, i₀, i₁, iR, e0, e1, fd₀, fd₁, fdR, hne, htower⟩ :=
    exists_common_field Fx.Ωf M₀.Ω M₁.Ω Rf.Ω o₀.g o₁.g oR.g o₀.Fl.deg o₁.Fl.deg pos₀ pos₁ o₀.g_deg o₁.g_deg
      (oR.g_deg.trans hdeg)
  obtain ⟨K, hK, J, hJ, κ₀, v₀, κ₁, v₁, κR, vR, y, Z, ξ, h₀, h₁, hRm, bm₀, bm₁, bmR, hy₀, hy₁, hyR, hall, htie,
    hnorm, hd₀, hd₁, -, hr₀, hr₁⟩ :=
    exists_common_model M₀.K M₀.ι M₁.K M₁.ι Rf.K Rf.ι M₀.Ω M₁.Ω Rf.Ω Ω i₀ i₁ iR M₀.y M₁.y Rf.y
      (dimFl (CMType H) (D.p + D.q) + 1) o₀.𝔐.X o₁.𝔐.X oR.𝔐.X o₀.𝔐.ξ o₁.𝔐.ξ oR.𝔐.ξ M₀.arith M₁.arith Rf.arith
      M₀.birational M₁.birational Rf.birational fd₀ fd₁ fdR o₀.𝔐.all o₁.𝔐.all oR.𝔐.all o₀.𝔐.tie o₁.𝔐.tie oR.𝔐.tie
  obtain ⟨x₀, hx₀'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S₀ M₀.Ω M₀.K M₀.ι M₀.y o₀.𝔐 hmono
  obtain ⟨x₁, hx₁'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c _ _ Y S M₁.Ω M₁.K M₁.ι M₁.y o₁.𝔐 hmono
  have hx₀ : o₀.𝔐.ξ ≫ o₀.𝔐.f = (spMap o₀.𝔐.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hx₀']; exact o₀.𝔐.fn_over
  have hx₁ : o₁.𝔐.ξ ≫ o₁.𝔐.f = (spMap o₁.𝔐.fn ≫ x₁) ≫ Y.j := by
    rw [Category.assoc, ← hx₁']; exact o₁.𝔐.fn_over
  have hdisc₁ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S := fun p hp hd => hS (hdisc p hp hd)
  obtain ⟨A, a₀, j₀, m₀, p1, p2, p3, p4, p5, p6, p7, -, p9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S₀ M₀.Ω Ω i₀ M₀.K K M₀.ι J M₀.y y o₀.𝔐 _ Z ξ h₀ hx₀ hdisc
      (fun p hp s => (hv₀ p hp).2 s) hall htie hnorm hd₀
  obtain ⟨𝔐, a₁, j₁, m₁, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S M₁.Ω Ω i₁ M₁.K K M₁.ι J M₁.y y o₁.𝔐 _ Z ξ h₁ hx₁ hdisc₁
      (fun p hp s => (hv₁ p hp).2 s) hall htie hnorm hd₁
  have hdom₀ : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ o₀.𝔐.ξ (a₀.hom ≫ h₀) i₀ := by
    show A.ξ ≫ a₀.hom ≫ h₀ = _
    rw [← Category.assoc, p1]
    exact hd₀
  have hdom₁ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o₁.𝔐.ξ (a₁.hom ≫ h₁) i₁ := by
    show 𝔐.ξ ≫ a₁.hom ≫ h₁ = _
    rw [← Category.assoc, q1]
    exact hd₁
  have hf₀ : A.f = (a₀.hom ≫ h₀) ≫ o₀.𝔐.f := by rw [p2, Category.assoc]
  have hf₁ : 𝔐.f = (a₁.hom ≫ h₁) ≫ o₁.𝔐.f := by rw [q2, Category.assoc]
  obtain ⟨Fl₀, hb₀, -, -, hl₀⟩ := FlagPull.flag_pull E H D l Xo c _ _ Y S₀ M₀.Ω Ω i₀ M₀.K K M₀.ι J M₀.y y o₀.𝔐 A
    (a₀.hom ≫ h₀) j₀ m₀ κ₀ v₀ o₀.Fl bm₀ (fun q => congrFun hy₀ q) hdom₀ hf₀ p3 p4 p6 p7 p9 fd₀
  obtain ⟨Fl, hb₁, -, -, hl₁⟩ := FlagPull.flag_pull E H D l Xo c _ _ Y S M₁.Ω Ω i₁ M₁.K K M₁.ι J M₁.y y o₁.𝔐 𝔐
    (a₁.hom ≫ h₁) j₁ m₁ κ₁ v₁ o₁.Fl bm₁ (fun q => congrFun hy₁ q) hdom₁ hf₁ q3 q4 q6 q7 q9 fd₁
  have e01 : i₀.comp o₀.g = i₁.comp o₁.g := e0.trans e1.symm
  have hZ : h₀ ≫ o₀.𝔐.f = h₁ ≫ o₁.𝔐.f := by
    refine map_eq_of_generic hnorm hall Y.s Y.proj ?_
    have g0 : ξ ≫ h₀ = spMap i₀ ≫ o₀.𝔐.ξ := hd₀
    have g1 : ξ ≫ h₁ = spMap i₁ ≫ o₁.𝔐.ξ := hd₁
    rw [← Category.assoc, ← Category.assoc, g0, g1, Category.assoc, Category.assoc, o₀.g_over, o₁.g_over,
      ← Category.assoc, ← Category.assoc, spMap_spMap', spMap_spMap', e01]
  let e : 𝔐.X ≅ A.X := a₁ ≪≫ a₀.symm
  have he : 𝔐.ξ ≫ e.hom = A.ξ := by
    simp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, q1, ← p1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hf : e.hom ≫ A.f = 𝔐.f := by
    simp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [p2, q2, ← hZ]
    simp
  have hc : A.cst = 𝔐.cst := by
    refine ringHom_ext_int c (spMap_inj' ?_)
    rw [← A.cst_over, ← 𝔐.cst_over, ← hf, ← he]
    simp only [Category.assoc]
  obtain ⟨φ, φt, φV, φr, φp⟩ := same_base_cmp A 𝔐 e he hf hc
  have hRS : ∀ p ∈ S₀, 𝔐.R p = A.R p := fun p hp => by rw [p5, q5]; exact (hRR p hp).symm
  have hbφ : ∀ s k, Fl.b s k = φ (Fl₀.b s k) := by
    intro s k
    apply 𝔐.M.inj
    refine Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    show (𝔐.M.pt (Fl.b s k)).left ≫ 𝔐.m.φ = (𝔐.M.pt (φ (Fl₀.b s k))).left ≫ 𝔐.m.φ
    rw [φt, hb₀, hb₁, p3, q3, ← Category.assoc, ← Category.assoc, q7, p7, Category.assoc, Category.assoc,
      o₀.g_flag, o₁.g_flag, ← Category.assoc, ← Category.assoc, spMap_spMap', spMap_spMap',
      ← FlagPull.dualMap_comp, ← FlagPull.dualMap_comp, e01]
  have hbf : ∀ s, Fl.b s = fun k => φ (Fl₀.b s k) := fun s => funext (hbφ s)
  have hm := φp S₀ hRS
  have hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s) := fun s =>
    isVB_tr e he φ φr (hm s) (φV s) (A.vb s)
  have hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s) := fun s => by
    rw [hbf s]
    exact isFlagVB_tr e he φ φr (hm s) (Fl₀.sub s)
  have hlines : (Fl.shrink S₀ hS hvb hsub).RootLines (fun r => pullDeg κ₀ (M₀.xdeg r)) (fun r => i₀ (o₀.e r)) := by
    intro r
    refine isDegOn_tr (Λ := Fl₀.rootLat r) e he φr (fun q h => ?_) y _ _ (hl₀ _ _ o₀.lines r)
    refine tens_tr e _ q h (φr q h) ?_
    show ((𝔐.VAt S₀ (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 q : Set Ω) = _
    rw [hbf]
    exact gr_tr e φ φr (hm _) _ _ q h
  refine ⟨Ω, fΩ, cz, K, hK, J, hJ, y, κ₀, v₀, κ₁, v₁, κR, vR, i₀, i₁, iR, 𝔐, Fl, bm₀, bm₁, bmR,
    fun p => congrFun hy₀ p, fun p => congrFun hy₁ p, fun p => congrFun hyR p, e0, e1, ?_, ?_,
    ⟨hS, hvb, hsub, hlines⟩, hl₁ _ _ o₁.lines, fun p hp => ⟨?_, q8 p hp⟩⟩
  · rw [hr₀]; exact hne
  · rw [hr₀, hr₁, o₀.δ_eq, o₁.δ_eq, mul_left_comm, mul_left_comm (Module.finrank i₁.fieldRange Ω), htower]
  · exact omP_ext' i₁ o₁.𝔐 𝔐 (a₁.hom ≫ h₁) m₁ j₁ _ p hp hdom₁ hf₁ q5 q6 q7 hx₁ (hv₁ p hp).1

end GlobalTheory.CompanionTheory.Ar.OrLinked
