import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimCase
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.EigV
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Introduce `hR E Ω _ _ _ _ _ _ _ _ _ _ N _ ρ hρ l _ hl2 hlE O _ _ e he ψ hodd a ha`. Use `haveI : IsGalois ℚ E := inferInstance`. Set `c : HV.Coef l` to `⟨O, inferInstance, inferInstance⟩`. Set `ψ' : DirichletCharacter (↥c.O) N` to `MulChar.ofUnitHom (ψ.comp ρ)`. Establish `hcomp : MulChar.ringHomComp ψ' c.O.val.toRingHom = chiOf ρ ψ`.

Use extensionality with `b`. Simplify using `[ψ', chiOf, MulChar.ringHomComp_apply]`. Establish `hord : ¬ l ∣ orderOf ψ'`. Introduce `hdiv`. Apply `hlE` to reduce the goal to its premises.

Use `hdiv.trans ?_` and prove the remaining obligations. Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Use extensionality with `b`. Simplify using `only [ψ', MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MulChar.one_apply_coe]`.

Establish `h2 : ψ (ρ b) ^ Fintype.card Gal(E/ℚ) = 1`. Rewrite using `[← map_pow, pow_card_eq_one, map_one]`. Establish `h3` using `congrArg (fun u : (↥O)ˣ => ((u : ↥O) : PadicAlgCl l)) h2`. Simplify using `using h3`. Establish `hodd' : ψ' (-1) = (-1) ^ (e + 1)`.

Establish `h1` using `congrArg (fun χ => χ (-1)) hcomp`. Simplify using `only [MulChar.ringHomComp_apply] at h1`. Apply `Subtype.val_injective` to reduce the goal to its premises. Rewrite `h1` using `[hodd]`. Simplify using `using h1`.

Establish `key` using `vChar hR Ω l c hl2 N ψ' e he hord hodd' a (by rw [hcomp]; exact ha)`. Take `⟨_, hker, hlift⟩` from `galQuot ℚ E Ω`. Establish `hρσ : ∀ σ : G ℚ Ω, ρ (Chr.cls ℚ Ω N σ) = AlgEquiv.restrictNormalHom E σ`. Introduce `σ`. Establish `h1` using `hρ (Chr.cls ℚ Ω N σ) σ.toRingEquiv (fun x hx => Chr.cls_spec N σ x hx)`.

Establish `h2` using `hlift σ`. Use extensionality with `x`. Apply `(algebraMap E Ω).injective` to reduce the goal to its premises. Conclude with `(h1 x).symm.trans (h2 x)`. Establish `hdir : Chr.dirG ℚ Ω ψ' = ψ.comp (AlgEquiv.restrictNormalHom E)`.

Use extensionality with `σ`. Simplify using `[Chr.dirG, ψ', hρσ]`. Take `⟨_, hopen, hidx⟩` from `galEmbTop ℚ E Ω`. Use `haveI : (galOf ℚ E Ω).Normal := by`. Rewrite using `[← hker]`.

Use `infer_instance`. Establish `hle : galOf ℚ E Ω ≤ (ψ.comp (AlgEquiv.restrictNormalHom E)).ker`. Rewrite using `[← hker]`. Introduce `g hg`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`.

Simplify using `[hg]`. Establish `heig` using `Chr.eigV ℚ Ω l O e (ψ.comp (AlgEquiv.restrictNormalHom E)) (galOf ℚ E Ω) hopen hle (by rw [hidx]; exact hlE)`. Establish `hpsi : psiLen Ω e ψ = Chr.eigL l e (galOf ℚ E Ω) (ψ.comp (AlgEquiv.restrictNormalHom E))` using `rfl`. Rewrite using `[hpsi, heig, ← hdir]`. Conclude with `key`.
-/
theorem UpperTheory.V.ML.psiOf :
    Rec → PsiBound := by
  intro hR E Ω _ _ _ _ _ _ _ _ _ _ N _ ρ hρ l _ hl2 hlE O _ _ e he ψ hodd a ha
  haveI : IsGalois ℚ E := inferInstance
  let c : HV.Coef l := ⟨O, inferInstance, inferInstance⟩
  let ψ' : DirichletCharacter (↥c.O) N := MulChar.ofUnitHom (ψ.comp ρ)
  have hcomp : MulChar.ringHomComp ψ' c.O.val.toRingHom = chiOf ρ ψ := by
    ext b
    simp [ψ', chiOf, MulChar.ringHomComp_apply]
  have hord : ¬ l ∣ orderOf ψ' := by
    intro hdiv
    apply hlE
    refine hdiv.trans ?_
    rw [← IsGalois.card_aut_eq_finrank]
    apply orderOf_dvd_of_pow_eq_one
    ext b
    simp only [ψ', MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MulChar.one_apply_coe]
    have h2 : ψ (ρ b) ^ Fintype.card Gal(E/ℚ) = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    have h3 := congrArg (fun u : (↥O)ˣ => ((u : ↥O) : PadicAlgCl l)) h2
    simpa using h3
  have hodd' : ψ' (-1) = (-1) ^ (e + 1) := by
    have h1 := congrArg (fun χ => χ (-1)) hcomp
    simp only [MulChar.ringHomComp_apply] at h1
    apply Subtype.val_injective
    rw [hodd] at h1
    simpa using h1
  have key := vChar hR Ω l c hl2 N ψ' e he hord hodd' a (by rw [hcomp]; exact ha)
  obtain ⟨_, hker, hlift⟩ := galQuot ℚ E Ω
  have hρσ : ∀ σ : G ℚ Ω, ρ (Chr.cls ℚ Ω N σ) = AlgEquiv.restrictNormalHom E σ := by
    intro σ
    have h1 := hρ (Chr.cls ℚ Ω N σ) σ.toRingEquiv (fun x hx => Chr.cls_spec N σ x hx)
    have h2 := hlift σ
    ext x
    apply (algebraMap E Ω).injective
    exact (h1 x).symm.trans (h2 x)
  have hdir : Chr.dirG ℚ Ω ψ' = ψ.comp (AlgEquiv.restrictNormalHom E) := by
    ext σ
    simp [Chr.dirG, ψ', hρσ]
  obtain ⟨_, hopen, hidx⟩ := galEmbTop ℚ E Ω
  haveI : (galOf ℚ E Ω).Normal := by
    rw [← hker]
    infer_instance
  have hle : galOf ℚ E Ω ≤ (ψ.comp (AlgEquiv.restrictNormalHom E)).ker := by
    rw [← hker]
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  have heig := Chr.eigV ℚ Ω l O e (ψ.comp (AlgEquiv.restrictNormalHom E)) (galOf ℚ E Ω) hopen hle
    (by rw [hidx]; exact hlE)
  have hpsi : psiLen Ω e ψ = Chr.eigL l e (galOf ℚ E Ω) (ψ.comp (AlgEquiv.restrictNormalHom E)) := rfl
  rw [hpsi, heig, ← hdir]
  exact key
