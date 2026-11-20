import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentDifference
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerUniversalFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlagTangentKodairaSpencerUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentDifferenceStatement

section
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.FlagTan
/- English proof (translation)
Introduce `hP hG E _ _ _ H Dw l Xo c K _ _ y x' x'' M hpq h' h'' k' k''`. Take `⟨X, hX, hXy, hXM⟩ : ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalThe …` from `by first`. Consider the case `exact _root_.GlobalTheory.T.kodaira_spencer_universal_family hP hG E H Dw l Xo c K y hpq`. Consider the case `exact _root_.GlobalTheory.T.kodaira_spencer_universal_family hP E H Dw l Xo c K y hpq`. Consider the case `exact (_root_.GlobalTheory.T.kodaira_spencer_universal_family hP hG E H Dw l Xo c K y hpq)`.

Establish `htan : ∀ N, GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X)` using `fun N => by`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hX, sOf, sOf, ← Spec.map_comp]`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Conclude with `(GlobalTheory.FlagTan.dir c N).commutes _`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← hXy]`. Use `congr 2`.

Use extensionality with `z`. Simplify using the standard rewrite rules. Establish `uniq` using `fun x hx => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_unique hP E H Dw l Xo c K y x hpq hx`. Establish `key` using `exists_dir_eq_of_smooth (KA l) Xo.X Xo.s Dw.dim Xo.smooth K ((algebraMap c.F K).comp (IntermediateField.inclusion c.le).toRingHom) (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H)) (GlobalTheory.FlagTan.card_HIx (GlobalTheory.FlagTan.isHalf_psiSet H)) X (by rw [hX, sO …`. Establish `hk : ∀ x, GlobalTheory.FlagTan.IsTanX y x → ∃ N, x = spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X` using `fun x hx => key x (by rw [hx.1, sOf]) (hx.2.trans hXy.symm)`.

Take `⟨N', rfl⟩` from `hk x' h'`. Take `⟨N'', rfl⟩` from `hk x'' h''`. Rewrite using `[uniq _ (htan N') N' M (hXM N') k', uniq _ (htan N'') N'' M (hXM N'') k'']`.
-/
theorem eq_of_kodaira_spencer_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y x' x'' M hpq h' h'' k' k''
  obtain ⟨X, hX, hXy, hXM⟩ : ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧
      spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧
      ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
        GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
    first
    | exact _root_.GlobalTheory.T.kodaira_spencer_universal_family hP hG E H Dw l Xo c K y hpq
    | exact _root_.GlobalTheory.T.kodaira_spencer_universal_family hP E H Dw l Xo c K y hpq
    | exact (_root_.GlobalTheory.T.kodaira_spencer_universal_family hP hG E H Dw l Xo c K y hpq)
  have htan : ∀ N, GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X) := fun N => by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hX, sOf, sOf, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (GlobalTheory.FlagTan.dir c N).commutes _
    · rw [← Category.assoc, ← Spec.map_comp, ← hXy]
      congr 2
      ext z
      simp
  have uniq := fun x hx => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_unique hP E H Dw l Xo c K y x hpq hx
  have key := exists_dir_eq_of_smooth (KA l) Xo.X Xo.s Dw.dim Xo.smooth K ((algebraMap c.F K).comp (IntermediateField.inclusion c.le).toRingHom)
    (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H)) (GlobalTheory.FlagTan.card_HIx (GlobalTheory.FlagTan.isHalf_psiSet H)) X
    (by rw [hX, sOf])
    (fun N N' e => uniq _ (htan N) N N' (hXM N) (e ▸ hXM N'))
  have hk : ∀ x, GlobalTheory.FlagTan.IsTanX y x → ∃ N, x = spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X := fun x hx =>
    key x (by rw [hx.1, sOf]) (hx.2.trans hXy.symm)
  obtain ⟨N', rfl⟩ := hk x' h'
  obtain ⟨N'', rfl⟩ := hk x'' h''
  rw [uniq _ (htan N') N' M (hXM N') k', uniq _ (htan N'') N'' M (hXM N'') k'']
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq | exact _root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq | (intros; apply _root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.flag_deformations_eq_of_kodaira_spencer_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  first | exact @_root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq | exact _root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq | (intros; apply _root_.GlobalTheory.FlagTan.eq_of_kodaira_spencer_eq <;> assumption)
end
