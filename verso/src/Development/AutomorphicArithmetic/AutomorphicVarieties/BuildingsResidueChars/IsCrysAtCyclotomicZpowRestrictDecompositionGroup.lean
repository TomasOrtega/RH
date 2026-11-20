import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ A O _ _ _ Bw j`. Use `set P := UpperTheory.V.Loc.PP l with hP`. Set `θ : ↥(GK Bw.Kw) →* (↥Bw.LL.1)ˣ` to `cycLL (P.PD Bw.Kw) ↥Bw.LL.1 ^ j`. Set `r : ↥(Dec (F` to `F) A) →* GL (Fin 1) ↥Bw.LL.1 := (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (θ.comp Bw.e.toMonoidHom)`. Establish `hr : ∀ g, ((r g : GL (Fin 1) ↥Bw.LL.1) : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) = ((θ (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) • (1 : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1)` using `fun g => GlobalTheory.HodgeOfTrue.coe_scalar _`.

Establish `key : ∀ g : ↥(Dec (F` using `F) A), algebraMap ↥Bw.LL.1 (Om l) ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) = ((cycBar F Ω l (g : G F Ω) : (Qbar l)ˣ) : Qbar l) := fun g => by`. Establish `h1` using `GlobalTheory.BlockCrys.cyc_bridge Bw P (Bw.e g)`. Establish `h2` using `P.PD_χ Bw.Kw (Bw.e g)`. Establish `h3 : Br.ι Bw (Bw.e g) = g` using `Bw.e.symm_apply_apply g`. Rewrite `h1` using `[h3]`.

Express the relevant statement in the definitionally equal form `algebraMap ↥Bw.LL.1 (Om l) (algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ (Bw.e g) : ℚ_[l]ˣ) : ℚ_[l])) = _`. Rewrite using `[h2, h1, ← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression. Use `⟨Bw.LL, r, ⟨le_rfl, ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `g a b`.

Express the relevant statement in the definitionally equal form `algebraMap ↥Bw.LL.1 (Om l) (((r g : GL (Fin 1) ↥Bw.LL.1) : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) a b) = ((Matrix.GeneralLinearGroup.scalar (Fin 1) ((cycBar F Ω l ^ j) (g : G F Ω)) : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) a b`. Rewrite using `[hr, GlobalTheory.HodgeOfTrue.coe_scalar, Subsingleton.elim a 0, Subsingleton.elim b 0]`. Simplify using `only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`. Express the relevant statement in the definitionally equal form `algebraMap ↥Bw.LL.1 (Om l) (((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g)) ^ j : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) = (((cycBar F Ω l (g : G F Ω)) ^ j : (Qbar l)ˣ) : Qbar l)`. Rewrite using `[Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, key]`.

Use `haveI := Bw.LL.2`. Establish `h1` using `GlobalTheory.BlockCrys.isCrys_cyc_zpow (LL := ↥Bw.LL.1) (P.PD Bw.Kw) j`. Use `GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD Bw.Kw) (LinearEquiv.funUnique (Fin 1) ↥Bw.LL.1 ↥Bw.LL.1).symm (fun g x => ?_) h1` and prove the remaining obligations. Rewrite using `[GlobalTheory.ConjLocal.repE_apply, hr, MulEquiv.apply_symm_apply, Matrix.smul_mulVec, Matrix.one_mulVec]`. Use function extensionality and compare the values at `a`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.isCrysAt_cyclotomic_zpow_restrict_decompositionGroup :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (j : ℤ), GlobalTheory.Pst.IsCrysAt (UpperTheory.V.Loc.PP l) Bw ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp ((cycBar F Ω l ^ j).comp (Dec (F := F) A).subtype)) := by
  intro F Ω _ _ _ _ _ l _ A O _ _ _ Bw j
  set P := UpperTheory.V.Loc.PP l with hP
  let θ : ↥(GK Bw.Kw) →* (↥Bw.LL.1)ˣ := cycLL (P.PD Bw.Kw) ↥Bw.LL.1 ^ j
  let r : ↥(Dec (F := F) A) →* GL (Fin 1) ↥Bw.LL.1 :=
    (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (θ.comp Bw.e.toMonoidHom)
  have hr : ∀ g, ((r g : GL (Fin 1) ↥Bw.LL.1) : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) =
      ((θ (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) • (1 : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) := fun g =>
    GlobalTheory.HodgeOfTrue.coe_scalar _
  have key : ∀ g : ↥(Dec (F := F) A), algebraMap ↥Bw.LL.1 (Om l)
      ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      ((cycBar F Ω l (g : G F Ω) : (Qbar l)ˣ) : Qbar l) := fun g => by
    have h1 := GlobalTheory.BlockCrys.cyc_bridge Bw P (Bw.e g)
    have h2 := P.PD_χ Bw.Kw (Bw.e g)
    have h3 : Br.ι Bw (Bw.e g) = g := Bw.e.symm_apply_apply g
    rw [h3] at h1
    change algebraMap ↥Bw.LL.1 (Om l) (algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ (Bw.e g) : ℚ_[l]ˣ) : ℚ_[l])) = _
    rw [h2, h1, ← IsScalarTower.algebraMap_apply]
    rfl
  refine ⟨Bw.LL, r, ⟨le_rfl, ?_⟩, ?_⟩
  · ext g a b
    change algebraMap ↥Bw.LL.1 (Om l) (((r g : GL (Fin 1) ↥Bw.LL.1) : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) a b) =
      ((Matrix.GeneralLinearGroup.scalar (Fin 1) ((cycBar F Ω l ^ j) (g : G F Ω)) : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) a b
    rw [hr, GlobalTheory.HodgeOfTrue.coe_scalar, Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    change algebraMap ↥Bw.LL.1 (Om l) (((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g)) ^ j : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      (((cycBar F Ω l (g : G F Ω)) ^ j : (Qbar l)ˣ) : Qbar l)
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, key]
  · haveI := Bw.LL.2
    have h1 := GlobalTheory.BlockCrys.isCrys_cyc_zpow (LL := ↥Bw.LL.1) (P.PD Bw.Kw) j
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD Bw.Kw) (LinearEquiv.funUnique (Fin 1) ↥Bw.LL.1 ↥Bw.LL.1).symm
      (fun g x => ?_) h1
    rw [GlobalTheory.ConjLocal.repE_apply, hr, MulEquiv.apply_symm_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext a
    rfl
