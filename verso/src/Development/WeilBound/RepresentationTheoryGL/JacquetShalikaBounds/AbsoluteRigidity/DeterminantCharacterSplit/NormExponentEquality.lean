import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChiDetSplitCentre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.DiscSpec GlobalTheory.UnitaryBC
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.CuspRep.Central

namespace PositivityTheory.RgJS.NormExponentLemmas

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cpow_val (s : ℂ) (x) :
    (((cpowChar E s).1 x : ℂˣ) : ℂ) = Complex.exp (s * Real.log (ideleNorm (E := E) x)) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `x`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(((cpowChar E ((τ : ℂ) * Complex.I)).1 x : ℂˣ) : ℂ) * (((cpowChar E (((-τ : ℝ) : ℂ) * Complex.I)).1 x : ℂˣ) : ℂ) = 1`.

Rewrite using `[cpow_val, cpow_val, ← Complex.exp_add]`. Use `push_cast`. Put the polynomial expressions in normal form. Conclude with `Complex.exp_zero`.
-/
theorem cpow_mul_neg (τ : ℝ) :
    cpowChar E ((τ : ℂ) * Complex.I) * cpowChar E (((-τ : ℝ) : ℂ) * Complex.I) = 1 := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply Units.ext
  change (((cpowChar E ((τ : ℂ) * Complex.I)).1 x : ℂˣ) : ℂ) *
      (((cpowChar E (((-τ : ℝ) : ℂ) * Complex.I)).1 x : ℂˣ) : ℂ) = 1
  rw [cpow_val, cpow_val, ← Complex.exp_add]
  push_cast
  ring_nf
  exact Complex.exp_zero

/- English proof (translation)
Set `D : ℝ →+ ℝ` to `AddMonoidHom.mk' (fun t => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a t)))) fun x y => by`. Rewrite using `[splitCentre_add, map_mul, map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _)]`. Establish `hD : Continuous D` using `(continuous_ideleNorm.comp (GeneralLinearGroup.continuous_det.comp GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => ideleNorm_ne_zero _`. Establish `hDt : ∀ t, D t = t * D 1` using `fun t => by simpa using map_real_smul D hD t 1`. Establish `hD1 : 0 < D 1`.

Express the relevant statement in the definitionally equal form `0 < Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a 1)))`. Rewrite using `[det_splitCentre_one, map_pow, Real.log_pow]`. Conclude with `mul_pos (by exact_mod_cast ha) (Real.log_pos (one_lt_ideleNorm_eIdele E))`. Use `⟨c / D 1, fun t => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp ((((c / D 1 : ℝ) : ℂ) * Complex.I) * (D t : ℝ)) = _`.

Establish `: (D 1 : ℂ) ≠ 0` using `by exact_mod_cast hD1.ne'`. Rewrite using `[hDt t]`. Use `push_cast`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem chiDet_split {a : ℕ} (ha : 0 < a) (c : ℝ) :
    ∃ τ : ℝ, ∀ t : ℝ, ((chiDet a (cpowChar E ((τ : ℂ) * Complex.I)) (splitCentre E a t) : ℂˣ) : ℂ) =
      Complex.exp (c * Complex.I * t) := by
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a t)))) fun x y => by
      rw [splitCentre_add, map_mul, map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (continuous_ideleNorm.comp (GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a 1)))
    rw [det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast ha) (Real.log_pos (one_lt_ideleNorm_eIdele E))
  refine ⟨c / D 1, fun t => ?_⟩
  change Complex.exp ((((c / D 1 : ℝ) : ℂ) * Complex.I) * (D t : ℝ)) = _
  have : (D 1 : ℂ) ≠ 0 := by exact_mod_cast hD1.ne'
  rw [hDt t]; push_cast
  congr 1; field_simp

/- English proof (translation)
Introduce `x hx`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[HChar.loc, MonoidHom.comp_apply, cpow_val]`. Rewrite using `[show ideleNorm (Neutral.B1.localIdele E w x) = ‖(x : w.adicCompletion E)‖ from GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele w x, norm_eq_one_of_valued hx]`. Simplify using the standard rewrite rules.
-/
theorem unr (τ : ℝ) (w : HeightOneSpectrum (𝓞 E)) : (cpowChar E ((τ : ℂ) * Complex.I)).UnrAt w := by
  intro x hx
  apply Units.ext
  rw [HChar.loc, MonoidHom.comp_apply, cpow_val]
  rw [show ideleNorm (Neutral.B1.localIdele E w x) = ‖(x : w.adicCompletion E)‖ from
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele w x, norm_eq_one_of_valued hx]
  simp

/- English proof (translation)
Establish `hq : (1 : ℝ) < Ideal.absNorm w.asIdeal`. Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm w` after adjusting the coercions. Establish `hn : ‖((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ = (Ideal.absNorm w.asIdeal : ℝ)⁻¹`. Establish `hϖ` using `unif_spec (L := E) w`. Rewrite using `[FinitePlace.norm_def, show Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-1 : ℤ) from hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]`.

Establish `: Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0)) = -1` using `rfl`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[HChar.val, HChar.locK, MonoidHom.comp_apply, HChar.loc, MonoidHom.comp_apply, cpow_val]`. Rewrite using `[show ideleNorm (Neutral.B1.localIdele E w (atFin w (unif w))) = ‖((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ from GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele w _, hn, Real.log_inv]`.

Establish `hq0 : (Ideal.absNorm w.asIdeal : ℂ) ≠ 0`. Establish `: (0 : ℝ) < Ideal.absNorm w.asIdeal` using `by linarith`. Conclude with `this.ne'` after adjusting the coercions. Rewrite using `[Complex.cpow_def_of_ne_zero hq0]`. Use `congr 1`.

Rewrite using `[show (Ideal.absNorm w.asIdeal : ℂ) = ((Ideal.absNorm w.asIdeal : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_log (by positivity)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_eq (τ : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    (((cpowChar E ((τ : ℂ) * Complex.I)).val w : ℂˣ) : ℂ) =
      (Ideal.absNorm w.asIdeal : ℂ) ^ (-((τ : ℂ) * Complex.I)) := by
  have hq : (1 : ℝ) < Ideal.absNorm w.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hn : ‖((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ =
      (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
    have hϖ := unif_spec (L := E) w
    rw [FinitePlace.norm_def, show Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) from hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have : Multiplicative.toAdd (WithZero.unzero
        (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0)) = -1 := rfl
    rw [this]
    simp
  rw [HChar.val, HChar.locK, MonoidHom.comp_apply, HChar.loc, MonoidHom.comp_apply, cpow_val]
  rw [show ideleNorm (Neutral.B1.localIdele E w (atFin w (unif w))) =
      ‖((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ from
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele w _, hn, Real.log_inv]
  have hq0 : (Ideal.absNorm w.asIdeal : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Ideal.absNorm w.asIdeal := by linarith
    exact_mod_cast this.ne'
  rw [Complex.cpow_def_of_ne_zero hq0]
  congr 1
  rw [show (Ideal.absNorm w.asIdeal : ℂ) = ((Ideal.absNorm w.asIdeal : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log (by positivity)]
  push_cast
  ring

end PositivityTheory.RgJS.NormExponentLemmas

namespace PositivityTheory.RgJS

open NormExponentLemmas

/- English proof (translation)
Introduce `E _ _ _`. Use `⟨fun τ => cpowChar E ((τ : ℂ) * Complex.I), fun τ w => ⟨unr τ w, val_eq τ w⟩, fun m π hm hu => ?_⟩` and prove the remaining obligations. Proceed by induction on `π using Quotient.inductionOn with`. Consider the case `h π₁`. Take `⟨ω, hωu, hω⟩` from `hu`.

Establish `hω' : π₁.HasCentChar ω` using `hω`. Establish `hωc : π₁.HasCentral ω` using `CuspSub.hasCentral_iff.2 hω'`. Establish `hre : (dchi ω 1).re = 0`. Establish `h1` using `GlobalTheory.CompanionTheory.TwistNorm.val_expId ω 1`. Establish `h2` using `hωu (GlobalTheory.DiscChar.expId E 1)`.

Rewrite `h2` using `[h1, Complex.norm_exp]`. Simplify using `using h2`. Take `⟨τ₀, hν⟩` from `chiDet_split (E := E) (a := m) hm (-(dchi ω 1).im)`. Establish `hn : IsNormalised (π₁.twist (cpowChar E ((τ₀ : ℂ) * Complex.I)))` using `GlobalTheory.CompanionTheory.TwistNorm.isNormalised_twist hωc fun t => by`. Rewrite using `[hν t]`.

Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp [hre] <;> ring`. Use `⟨π₁.twist (cpowChar E ((τ₀ : ℂ) * Complex.I)), -τ₀, hn, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `CG.mk π₁ = CG.mk ((π₁.twist (cpowChar E ((τ₀ : ℂ) * Complex.I))).twist (cpowChar E (((-τ₀ : ℝ) : ℂ) * Complex.I)))`. Rewrite using `[← CuspSub.twist_mul, cpow_mul_neg, CuspSub.twist_one]`.
-/
theorem norm_exponent_equality : NormEx := by
  intro E _ _ _
  refine ⟨fun τ => cpowChar E ((τ : ℂ) * Complex.I), fun τ w => ⟨unr τ w, val_eq τ w⟩, fun m π hm hu => ?_⟩
  induction π using Quotient.inductionOn with
  | h π₁ =>
    obtain ⟨ω, hωu, hω⟩ := hu
    have hω' : π₁.HasCentChar ω := hω
    have hωc : π₁.HasCentral ω := CuspSub.hasCentral_iff.2 hω'
    have hre : (dchi ω 1).re = 0 := by
      have h1 := GlobalTheory.CompanionTheory.TwistNorm.val_expId ω 1
      have h2 := hωu (GlobalTheory.DiscChar.expId E 1)
      rw [h1, Complex.norm_exp] at h2
      simpa using h2
    obtain ⟨τ₀, hν⟩ := chiDet_split (E := E) (a := m) hm (-(dchi ω 1).im)
    have hn : IsNormalised (π₁.twist (cpowChar E ((τ₀ : ℂ) * Complex.I))) :=
      GlobalTheory.CompanionTheory.TwistNorm.isNormalised_twist hωc fun t => by
        rw [hν t]
        congr 1
        apply Complex.ext <;> simp [hre] <;> ring
    refine ⟨π₁.twist (cpowChar E ((τ₀ : ℂ) * Complex.I)), -τ₀, hn, ?_⟩
    change CG.mk π₁ = CG.mk ((π₁.twist (cpowChar E ((τ₀ : ℂ) * Complex.I))).twist
      (cpowChar E (((-τ₀ : ℝ) : ℂ) * Complex.I)))
    rw [← CuspSub.twist_mul, cpow_mul_neg, CuspSub.twist_one]

end PositivityTheory.RgJS
