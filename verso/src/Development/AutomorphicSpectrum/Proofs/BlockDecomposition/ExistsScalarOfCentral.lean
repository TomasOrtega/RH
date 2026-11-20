import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.TranslAdele

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `σ (σ (g.val i j)) = g.val i j`. Conclude with `hσ _`.
-/
theorem thetaR_thetaR {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (n : ℕ)
    (g : GL (Fin n) A) : thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  ext i j
  change σ (σ (g.val i j)) = g.val i j
  exact hσ _

/- English proof (translation)
Establish `: z.val ∈ Set.range (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K)`. Apply `Matrix.mem_range_scalar_of_commute_transvectionStruct` to reduce the goal to its premises. Introduce `t`. Establish `h` using `hz ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩`. Establish `h'` using `congrArg Units.val h`.

Conclude with `h'.symm`. Take `⟨c, hc⟩` from `this`. Conclude with `⟨c, hc.symm⟩`.
-/
theorem exists_scalar_of_central {K : Type} [Field K] {n : ℕ} (z : GL (Fin n) K)
    (hz : ∀ h : GL (Fin n) K, z * h = h * z) : ∃ c : K, z.val = Matrix.scalar (Fin n) c := by
  have : z.val ∈ Set.range (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    have h := hz ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩
    have h' := congrArg Units.val h
    exact h'.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Phi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map f = GlobalTheory.Tw.Phi n S := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `E _ _ _ n u hu g`. Establish `hz : ∀ h : GL (Fin n) E, ((PhiU n E)⁻¹ * u) * h = h * ((PhiU n E)⁻¹ * u)`. Introduce `h`. Establish `hinv : thetaE E n (thetaE E n h) = h` using `thetaR_thetaR (conjE E) (fun x => IsCMField.complexConj_apply_apply E x) n h`. Establish `h1` using `hu.1 (thetaE E n h)`.

Rewrite `h1` using `[hinv]`. Establish `h2 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹`. Use `thetaGL_eq n E (IsCMField.complexConj E).toRingEquiv.toRingHom (thetaE E n h)` as an intermediate fact. Rewrite `this` using `[show thetaR (IsCMField.complexConj E).toRingEquiv.toRingHom n (thetaE E n h) = h from hinv]`. Conclude with `this`.

Rewrite `h1` using `[h2]`. Establish `h3 : h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * u * h`. Establish `h4 : PhiU n E * h * (PhiU n E)⁻¹ * u = u * h` using `by rw [h1]; group`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h3, mul_assoc h]`.

Take `⟨c, hc⟩` from `exists_scalar_of_central _ hz`. Use `set w : GA E n := ratGL E n ((PhiU n E)⁻¹ * u) with hw`. Establish `hwc : ∀ t : GA E n, w * t = t * w`. Introduce `t`. Apply `Units.ext` to reduce the goal to its premises.

Establish `hval : w.val = Matrix.scalar (Fin n) (algebraMap E (Ad E) c)`. Establish `: w.val = (((PhiU n E)⁻¹ * u : GL (Fin n) E).val).map (algebraMap E (Ad E))` using `rfl`. Rewrite using `[this, hc]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]`.

Rewrite using `[Units.val_mul, Units.val_mul, hval]`. Conclude with `Matrix.scalar_commute _ (fun r' => Commute.all _ _) _`. Establish `hP : ratGL E n (PhiU n E) = PhiU n (Ad E)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[phiU_val, ← Phi_map (algebraMap E (Ad E)) n, ← phiU_val]`.

Both sides reduce to the same expression. Establish `hr : ratGL E n u = PhiU n (Ad E) * w`. Rewrite using `[hw, map_mul, map_inv, hP, mul_inv_cancel_left]`. Rewrite using `[thetaGL_eq, hr]`. Establish `h5 : w * thetaA E n g * w⁻¹ = thetaA E n g` using `by rw [hwc]; group`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem translAd : TranslAd := by
  intro E _ _ _ n u hu g

  have hz : ∀ h : GL (Fin n) E, ((PhiU n E)⁻¹ * u) * h = h * ((PhiU n E)⁻¹ * u) := by
    intro h
    have hinv : thetaE E n (thetaE E n h) = h :=
      thetaR_thetaR (conjE E) (fun x => IsCMField.complexConj_apply_apply E x) n h
    have h1 := hu.1 (thetaE E n h)
    rw [hinv] at h1
    have h2 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹ := by
      have := thetaGL_eq n E (IsCMField.complexConj E).toRingEquiv.toRingHom (thetaE E n h)
      rw [show thetaR (IsCMField.complexConj E).toRingEquiv.toRingHom n (thetaE E n h) = h from hinv] at this
      exact this
    rw [h2] at h1
    have h3 : h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * u * h := by
      have h4 : PhiU n E * h * (PhiU n E)⁻¹ * u = u * h := by rw [h1]; group
      calc h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * (PhiU n E * h * (PhiU n E)⁻¹ * u) := by group
        _ = (PhiU n E)⁻¹ * u * h := by rw [h4]; group
    rw [← h3, mul_assoc h]
  obtain ⟨c, hc⟩ := exists_scalar_of_central _ hz

  set w : GA E n := ratGL E n ((PhiU n E)⁻¹ * u) with hw
  have hwc : ∀ t : GA E n, w * t = t * w := by
    intro t
    apply Units.ext
    have hval : w.val = Matrix.scalar (Fin n) (algebraMap E (Ad E) c) := by
      have : w.val = (((PhiU n E)⁻¹ * u : GL (Fin n) E).val).map (algebraMap E (Ad E)) := rfl
      rw [this, hc]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [Units.val_mul, Units.val_mul, hval]
    exact Matrix.scalar_commute _ (fun r' => Commute.all _ _) _
  have hP : ratGL E n (PhiU n E) = PhiU n (Ad E) := by
    apply Units.ext
    rw [phiU_val, ← Phi_map (algebraMap E (Ad E)) n, ← phiU_val]
    rfl
  have hr : ratGL E n u = PhiU n (Ad E) * w := by
    rw [hw, map_mul, map_inv, hP, mul_inv_cancel_left]
  rw [thetaGL_eq, hr]
  have h5 : w * thetaA E n g * w⁻¹ = thetaA E n g := by rw [hwc]; group
  calc PhiU n (Ad E) * thetaR (conjAd E) n g * (PhiU n (Ad E))⁻¹
      = PhiU n (Ad E) * (w * thetaA E n g * w⁻¹) * (PhiU n (Ad E))⁻¹ := by rw [h5]
    _ = PhiU n (Ad E) * w * thetaA E n g * (PhiU n (Ad E) * w)⁻¹ := by group

end GlobalTheory.CompanionTheory.TranslAdele

end
