import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.UOfSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd

/- English proof (translation)
Simplify using `[algSat, Multiset.bind_singleton, Multiset.map_map]`.
-/
private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

/- English proof (translation)
Introduce `A hA`. Use `⟨fun s hs => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `h1 : cycZ F Ω l s = 1` using `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by`. Rewrite using `[cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]`. Use the proof step `simp)`.

Rewrite using `[MonoidHom.inv_apply, cycBar, MonoidHom.comp_apply, h1, map_one, inv_one]`. Establish `h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ)`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _`. Rewrite using `[cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]`. Rewrite using `[MonoidHom.inv_apply, map_inv, inv_inv, h2, map_natCast]`.
-/
private theorem charEig_cyc_inv {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    CharEig ι (cycBar F Ω l)⁻¹ w (normV w : ℂ) := by
  intro A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ F Ω l s = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp)
    rw [MonoidHom.inv_apply, cycBar, MonoidHom.comp_apply, h1, map_one, inv_one]
  · have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
    rw [MonoidHom.inv_apply, map_inv, inv_inv, h2, map_natCast]

/- English proof (translation)
Establish `h` using `GlobalTheory.CuspRep.finId_det_locGL w (Matrix.GeneralLinearGroup.scalar (Fin 1) x)`. Rewrite `h`, the goal using `[locGL, GlobalTheory.CuspRep.cornerGL_scalar]`. Rewrite using `[finGL, GlobalTheory.CuspRep.cornerGL_scalar]`. Use `congr 1`. Conclude with `(congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))`.
-/
private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (Matrix.GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

/- English proof (translation)
Take `⟨ω, hω, -⟩` from `UpperTheory.V.Sd.Wc.centChar hP F π`. Establish `hv : ∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w` using `fun w α β h => by`. Take `⟨x, hx⟩` from `GlobalTheory.LFun.HasSatGL.exists_vec h`. Establish `hZ` using `(UpperTheory.V.Br.uOfSat F w _ _ x α β hx).2`. Establish `h2 : π.locRep w (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((ω.val w : ℂˣ) : ℂ) • x`.

Use `Subtype.ext (Subtype.ext (funext fun g => ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x.1.1 (g * finGL F 2 (locGL F 2 w _)) = _`. Rewrite using `[fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ x.2]`. Both sides reduce to the same expression. Conclude with `Units.ext (smul_left_injective ℂ hx.1 (hZ.symm.trans h2))`.

Use `⟨ω, hv, fun v => ?_⟩` and prove the remaining obligations. Establish `hiso : π.Iso (π.dual.twist ω)`. Use `hP.smoR F 2 one_le_two _ _ ?_` and prove the remaining obligations. Use `filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)] with w ⟨B, hB⟩ hu`. Take `⟨α, β, rfl⟩` from `Multiset.card_eq_two.1 hB.card`.

Establish `e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * ω.val w) = {α, β}`. Rewrite using `[← hv w α β hB, Multiset.pair_comm α β]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]`. Rewrite using `[mul_comm α β, inv_mul_cancel_left]`. Conclude with `Multiset.pair_comm α β`.

Conclude with `⟨_, hB, e ▸ hB.dual.twist hu⟩`. Take `⟨m, hm, -, hz⟩` from `hreg v`. Take `⟨x, y, rfl⟩` from `Multiset.card_eq_two.1 hm.1`. Take `⟨i, hi⟩` from `hz x (by simp)`. Take `⟨j, hj⟩` from `hz y (by simp)`.

Establish `h` using `congrArg Multiset.sum ((hiso.hasInfChar hm).unique (hm.dual.twist ω))`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton] at h`. Use `⟨i + j + 1, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at hi hj ⊢`. Take the linear combination `hi + hj - h / 2`.
-/
private theorem cent (hP : UpperTheory.V.Af.Hypotheses₂) {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    (hreg : π.IsRegAlg) (hs : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B) :
    ∃ ω : HChar F, (∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w) ∧ ∀ v, ∃ n : ℤ, TR.expo ω v = n := by
  obtain ⟨ω, hω, -⟩ := UpperTheory.V.Sd.Wc.centChar hP F π
  have hv : ∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w := fun w α β h => by
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec h
    have hZ := (UpperTheory.V.Br.uOfSat F w _ _ x α β hx).2
    have h2 : π.locRep w (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((ω.val w : ℂˣ) : ℂ) • x := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      change x.1.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ x.2]
      rfl
    exact Units.ext (smul_left_injective ℂ hx.1 (hZ.symm.trans h2))
  refine ⟨ω, hv, fun v => ?_⟩
  have hiso : π.Iso (π.dual.twist ω) := by
    refine hP.smoR F 2 one_le_two _ _ ?_
    filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)] with w ⟨B, hB⟩ hu
    obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * ω.val w) = {α, β} := by
      rw [← hv w α β hB, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, hB, e ▸ hB.dual.twist hu⟩
  obtain ⟨m, hm, -, hz⟩ := hreg v
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hm.1
  obtain ⟨i, hi⟩ := hz x (by simp)
  obtain ⟨j, hj⟩ := hz y (by simp)
  have h := congrArg Multiset.sum ((hiso.hasInfChar hm).unique (hm.dual.twist ω))
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton] at h
  refine ⟨i + j + 1, ?_⟩
  push_cast at hi hj ⊢
  linear_combination hi + hj - h / 2
