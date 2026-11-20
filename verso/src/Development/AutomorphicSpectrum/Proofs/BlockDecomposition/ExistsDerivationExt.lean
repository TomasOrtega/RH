import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.DerivExt

/- English proof (translation)
Use `letI := f.toAlgebra`. Set `φ : A →+* TrivSqZeroExt B B` to `{ toFun := fun x => (f x, f (D x)) map_one' := by`. Apply the tactic sequence `ext <;> simp`. Use the proof step `map_zero' := by`. Apply the tactic sequence `ext <;> simp`.

Use the proof step `map_add' := fun x y => by`. Apply the tactic sequence `ext <;> simp`. Use the proof step `map_mul' := fun x y => by`. Use `ext`. Simplify using the standard rewrite rules.

Simplify using `[Derivation.leibniz]`. Use `ring }`. Establish `hu : ∀ y : M, IsUnit (φ y)` using `fun y => by`. Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Conclude with `IsLocalization.map_units B y`.

Set `ψ : B →+* TrivSqZeroExt B B` to `IsLocalization.lift hu`. Establish `hψ : ∀ x, ψ (f x) = φ x` using `fun x => IsLocalization.lift_eq hu x`. Establish `hfst : ∀ b, (ψ b).fst = b`. Establish `: (TrivSqZeroExt.fstHom B B B).toRingHom.comp ψ = RingHom.id B` using `IsLocalization.ringHom_ext M (RingHom.ext fun x => by`. Express the relevant statement in the definitionally equal form `(ψ (f x)).fst = f x`.

Rewrite using `[hψ]`. Use the proof step `rfl)`. Conclude with `fun b => congrArg (· b) (congrArg DFunLike.coe this)`. Establish `hmul : ∀ b c, (ψ (b * c)).snd = b * (ψ c).snd + c * (ψ b).snd` using `fun b c => by`. Rewrite using `[map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul]`.

Simplify using `[hfst, mul_comm]`. Establish `hadd : ∀ b c, (ψ (b + c)).snd = (ψ b).snd + (ψ c).snd` using `fun b c => by`. Rewrite using `[map_add, TrivSqZeroExt.snd_add]`. Establish `hsm : ∀ (k : K) b, (ψ (k • b)).snd = k • (ψ b).snd` using `fun k b => by`. Establish `e : algebraMap K B k = f (algebraMap K A k)` using `(congrArg (· k) (congrArg DFunLike.coe hf)).symm`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, hmul, e, hψ]`. Establish `: (φ (algebraMap K A k)).snd = 0`. Express the relevant statement in the definitionally equal form `f (D _) = 0`. Rewrite using `[Derivation.map_algebraMap, map_zero]`. Rewrite using `[this, mul_zero, add_zero]`.

Set `L : B →ₗ[K] B` to `{ toFun := fun b => (ψ b).snd map_add' := hadd map_smul' := hsm }`. Use `⟨Derivation.mk' L fun b c => ?_, fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(ψ (b * c)).snd = b • (ψ c).snd + c • (ψ b).snd`. Rewrite using `[hmul]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `(ψ (f x)).snd = _`. Rewrite using `[hψ]`. Both sides reduce to the same expression.
-/
theorem exists_derivation_ext {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →+* B) (hf : f.comp (algebraMap K A) = algebraMap K B) (M : Submonoid A)
    (hloc : letI := f.toAlgebra; IsLocalization M B) (D : Derivation K A A) :
    ∃ p : Derivation K B B, ∀ x, p (f x) = f (D x) := by
  letI := f.toAlgebra
  let φ : A →+* TrivSqZeroExt B B :=
    { toFun := fun x => (f x, f (D x))
      map_one' := by
        ext <;> simp
      map_zero' := by
        ext <;> simp
      map_add' := fun x y => by
        ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp [Derivation.leibniz]
          ring }
  have hu : ∀ y : M, IsUnit (φ y) := fun y => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact IsLocalization.map_units B y
  let ψ : B →+* TrivSqZeroExt B B := IsLocalization.lift hu
  have hψ : ∀ x, ψ (f x) = φ x := fun x => IsLocalization.lift_eq hu x
  have hfst : ∀ b, (ψ b).fst = b := by
    have : (TrivSqZeroExt.fstHom B B B).toRingHom.comp ψ = RingHom.id B :=
      IsLocalization.ringHom_ext M (RingHom.ext fun x => by
        change (ψ (f x)).fst = f x
        rw [hψ]; rfl)
    exact fun b => congrArg (· b) (congrArg DFunLike.coe this)
  have hmul : ∀ b c, (ψ (b * c)).snd = b * (ψ c).snd + c * (ψ b).snd := fun b c => by
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul]
    simp [hfst, mul_comm]
  have hadd : ∀ b c, (ψ (b + c)).snd = (ψ b).snd + (ψ c).snd := fun b c => by
    rw [map_add, TrivSqZeroExt.snd_add]
  have hsm : ∀ (k : K) b, (ψ (k • b)).snd = k • (ψ b).snd := fun k b => by
    have e : algebraMap K B k = f (algebraMap K A k) := (congrArg (· k) (congrArg DFunLike.coe hf)).symm
    rw [Algebra.smul_def, Algebra.smul_def, hmul, e, hψ]
    have : (φ (algebraMap K A k)).snd = 0 := by
      change f (D _) = 0
      rw [Derivation.map_algebraMap, map_zero]
    rw [this, mul_zero, add_zero]
  let L : B →ₗ[K] B :=
    { toFun := fun b => (ψ b).snd
      map_add' := hadd
      map_smul' := hsm }
  refine ⟨Derivation.mk' L fun b c => ?_, fun x => ?_⟩
  · change (ψ (b * c)).snd = b • (ψ c).snd + c • (ψ b).snd
    rw [hmul]; rfl
  · change (ψ (f x)).snd = _
    rw [hψ]; rfl

/- English proof (translation)
Introduce `K _ X q V hV a`. Use `letI := (strV q V).toAlgebra`. Use `letI := (strV q (X.basicOpen a)).toAlgebra`. Introduce `d D`. Establish `hloc : letI` using `(rs (X.basicOpen_le a)).toAlgebra; IsLocalization (Submonoid.powers a) Γ(X, X.basicOpen a) := by`.

Use `letI := (rs (X.basicOpen_le a)).toAlgebra`. Conclude with `hV.isLocalization_basicOpen a`. Establish `hf : (rs (X.basicOpen_le a)).comp (algebraMap K Γ(X, V)) = algebraMap K Γ(X, X.basicOpen a)` using `GlobalTheory.CompanionTheory.CoordRes.rs_comp_strV q _`. Use `choose p hp using fun k => exists_derivation_ext _ hf _ hloc (D k)`. Conclude with `⟨p, hp⟩`.
-/
theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {V : X.Opens}, IsAffineOpen V → ∀ (a : Γ(X, V)),
    letI := (strV q V).toAlgebra
    letI := (strV q (X.basicOpen a)).toAlgebra
    ∀ {d : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), ∃ p : Fin d → Derivation K Γ(X, X.basicOpen a) Γ(X, X.basicOpen a),
      ∀ k x, p k (rs (X.basicOpen_le a) x) = rs (X.basicOpen_le a) (D k x) := by
  intro K _ X q V hV a
  letI := (strV q V).toAlgebra
  letI := (strV q (X.basicOpen a)).toAlgebra
  intro d D
  have hloc : letI := (rs (X.basicOpen_le a)).toAlgebra; IsLocalization (Submonoid.powers a) Γ(X, X.basicOpen a) := by
    letI := (rs (X.basicOpen_le a)).toAlgebra
    exact hV.isLocalization_basicOpen a
  have hf : (rs (X.basicOpen_le a)).comp (algebraMap K Γ(X, V)) = algebraMap K Γ(X, X.basicOpen a) :=
    GlobalTheory.CompanionTheory.CoordRes.rs_comp_strV q _
  choose p hp using fun k => exists_derivation_ext _ hf _ hloc (D k)
  exact ⟨p, hp⟩

end GlobalTheory.CompanionTheory.ConeLocal.DerivExt
