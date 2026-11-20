import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalIffUnrOfLawsT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.CuspRep Polynomial
open UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Substitute `e` using the available equality. Rewrite `hz` using `[WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd]`. Rewrite `hz` using `[Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨i, -, hi⟩` from `hz`. Rewrite `hi` using `[Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, zpow_one]`.

Establish `hq : (((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) * ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = 1`. Establish `h0 : ((normV w : ℕ) : ℂ) ≠ 0`. Use `GlobalTheory.WeilDeligne.one_lt_normV w` as an intermediate fact. Conclude with `(by omega : (normV w : ℕ) ≠ 0)` after adjusting the coercions. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_add _ _ h0]`.

Establish `: ((((1 : ℝ) - n) / 2 : ℝ) : ℂ) + ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) = 0`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.cpow_zero]`. Use `⟨((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α i : ℂ), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[algSat, Multiset.mem_map]`. Use `⟨(α i : ℂ), ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map]`. Conclude with `Multiset.mem_map_of_mem (fun j => ((α j : ℂˣ) : ℂ)) (Finset.mem_univ i)`. Rewrite using `[hi]`.

Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, coe_qPow]`. Establish `ha : (α i : ℂ) ≠ 0` using `Units.ne_zero _`. Clear the denominators using the available nonvanishing facts. Conclude with `hq`.
-/
private theorem root_diag {n : ℕ} (α : Fin n → ℂˣ) (y : WD h)
    (e : y = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2))) (φ : ↥(Weil h)) (hd : deg φ = 1) (z : ℂ)
    (hz : (WD.charPol y φ).IsRoot z) : ∃ b ∈ algSat n (normV w) (Finset.univ.val.map α), z * b = 1 := by
  subst e
  rw [WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd] at hz
  rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, -, hi⟩ := hz
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, zpow_one] at hi
  have hq : (((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) * ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = 1 := by
    have h0 : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (by omega : (normV w : ℕ) ≠ 0)
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_add _ _ h0]
    have : ((((1 : ℝ) - n) / 2 : ℝ) : ℂ) + ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [this, Complex.cpow_zero]
  refine ⟨((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α i : ℂ), ?_, ?_⟩
  · rw [algSat, Multiset.mem_map]
    refine ⟨(α i : ℂ), ?_, rfl⟩
    simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map]
    exact Multiset.mem_map_of_mem (fun j => ((α j : ℂˣ) : ℂ)) (Finset.mem_univ i)
  · rw [hi]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_qPow]
    have ha : (α i : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    exact hq

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.CuspRep.ParLaws in
/- English proof (translation)
Take `⟨α, hα⟩` from `GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) n ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ (GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL hB)`. Use `⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩` and prove the remaining obligations. Establish `hx : GlobalTheory.SmGL.HasSatake (IrrGL.of σ.ρ σ.smooth σ.irred).rep α` using `⟨(IrrGL.of σ.ρ σ.smooth σ.irred).2.rep.irr, fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hα.2.1, (IsSubquotient.of_surjective (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toIntertwiningMap (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toLinearEquiv.surjective).trans hα.2.2⟩`. Establish `e` using `GlobalTheory.RecT.SphLaw.sat ((GlobalTheory.RecT.lawsT_iff a ha rc).2 L) (IrrGL.of σ.ρ σ.smooth σ.irred) α hx`. Rewrite using `[algNorm, L.nu, e, WD.lpTw_mk]`.

Use `WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩` and prove the remaining obligations. Simplify using `[mul_zpow, mul_comm, mul_left_comm, mul_assoc]`. Express the relevant statement in the definitionally equal form `(_ : ℂ) * ((_ : ℂ) * v i) = _ * (_ * v i)`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem algNorm_diag {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (w.adicCompletion E) → WD h} (L : LawsT a ha rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) n
    ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ (GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL hB)
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have hx : GlobalTheory.SmGL.HasSatake (IrrGL.of σ.ρ σ.smooth σ.irred).rep α :=
    ⟨(IrrGL.of σ.ρ σ.smooth σ.irred).2.rep.irr, fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hα.2.1,
      (IsSubquotient.of_surjective (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toIntertwiningMap (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toLinearEquiv.surjective).trans hα.2.2⟩
  have e := GlobalTheory.RecT.SphLaw.sat ((GlobalTheory.RecT.lawsT_iff a ha rc).2 L) (IrrGL.of σ.ρ σ.smooth σ.irred) α hx
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
  change (_ : ℂ) * ((_ : ℂ) * v i) = _ * (_ * v i)
  ring

end UpperTheory.V.Z.Kato.WeilSphericalRecords

/- English proof (translation)
Introduce `_ E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ B _ hB φ hd z hz`. Take `⟨α, rfl, e⟩` from `algNorm_diag L σ B hB`. Conclude with `root_diag α _ e φ hd z hz`.
-/
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.recFrob :
    Af.Hypotheses₂ → RecFrob := by
  intro _ E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ B _ hB φ hd z hz
  obtain ⟨α, rfl, e⟩ := algNorm_diag L σ B hB
  exact root_diag α _ e φ hd z hz
