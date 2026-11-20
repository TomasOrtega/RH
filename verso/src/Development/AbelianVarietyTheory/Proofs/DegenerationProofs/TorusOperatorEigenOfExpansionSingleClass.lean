import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperatorStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameOfOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreSectionLinearCombExistsUniqueThetaActionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExistsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointsLevelWeightsFromOrthogonalLabelsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

/- English proof (translation)
Introduce `h1 h2 hT o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs w₀ hw₀ α b σ Φ hσ hΦ hsupp t h`. Take `⟨hLL, -⟩` from `laws_all h1 h2`. Take `⟨hc, -, hadm, -⟩` from `GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy`. Establish `hodd : Odd S.N`. Rewrite using `[ρ.N_eq]`.

Conclude with `(ρ.n_odd.pow).pow`. Establish `hN1 : 1 ≤ S.N` using `le_trans (by norm_num) S.N_ge`. Take `⟨-, -, -, hval, -, hθ⟩` from `hs`. Take `⟨θ, hθs, hθa⟩` from `hθ (t : S.Gam)`. Take `⟨τ, q, hqy, hqt, hqx, hτ⟩` from `GlobalTheory.T.torusPoints_level_weights_from_orthogonal_labels h1 h2 hT o Ω S ρ p y₀ u l hy x hx t`.

Take `⟨⟨w, hw⟩, -⟩` from `GlobalTheory.UT.SymFrame.main hLL u.V _ hadm u.D (PadicAlgCl p) S.N hodd q`. Take `⟨-, -, c3, c4, c5⟩` from `GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s b`. Use `choose s' hs' using fun i => (c4 θ (s i)).exists`. Take `⟨σ', hσ'⟩` from `(c4 θ σ).exists`. Establish `hσ'c : IsComb u.A s' b σ'` using `(c3 θ s' σ σ' hs' hσ).1 hσ'`.

Establish `hσ'c2` using `c5 S.J (fun i j => y₀ (algebraMap o S.R (S.ρ t j i))) s' b σ' (fun i => hθa i _ (hs' i)) hσ'c`. Take `⟨hbij, hlin⟩` from `GlobalTheory.UT.expBijF_and_expandsF_lin hLL u.V _ hadm u.D u.A u.G u.semi u.U`. Take `⟨hb1, hb2⟩` from `hbij (PadicAlgCl p) S.N hN1 w₀ hw₀`. Take `⟨Φ', hΦ'⟩` from `(hb1 σ').exists`. Establish `hrel` using `GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q _ hqx θ hθs w₀ hw₀ w hw σ σ' Φ Φ' hΦ hΦ' hσ'`.

Establish `hwt` using `((GlobalTheory.UT.TorusWeight.torus_weight hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q τ hqy hqt w hw).2 Φ Φ').1 hrel`. Use `set κ : PadicAlgCl p := y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val with hκ`. Establish `hΦeq : Φ' = (κ - 1) • Φ + Φ`. Rewrite using `[sub_smul, one_smul, sub_add_cancel]`. Use `fam_ext fun β j => ?_` and prove the remaining obligations.

Rewrite using `[hwt β j, smul_f, ← constBF_eq]`. Distinguish the cases in `hβ : ∀ z : u.D.toPre.X, β ≠ α + S.N • z`. Rewrite using `[hsupp β hβ j, mul_zero, mul_zero]`. Use `push Not at hβ`. Take `⟨z, rfl⟩` from `hβ`.

Rewrite using `[hτ, hκ]`. Simplify using the standard rewrite rules. Take `⟨⟨σ'', hσ''⟩, -⟩` from `GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin 2) (fun _ => σ) ![κ - 1, 1]`. Establish `hσ''e : u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ'' ((κ - 1) • Φ + Φ)`. Use `hlin (PadicAlgCl p) S.N w₀ σ σ σ'' Φ Φ (κ - 1) hΦ hΦ fun j => ?_` and prove the remaining obligations.

Rewrite using `[hσ'' j, Fin.sum_univ_two]`. Simplify using `[liftFun, cF]`. Establish `heq : σ'' = σ'` using `(hb2 Φ').unique (hΦeq ▸ hσ''e) hΦ'`. Substitute `heq` using the available equality. Take `⟨v1, -, v3, -⟩` from `GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists h1 u.V u.A (PadicAlgCl p) S.N (x h) (e h)`.

Establish `a1` using `v1 S.J s b _ σ hσ (fun i => hval i h)`. Establish `a2` using `v1 S.J s _ _ σ'' hσ'c2 (fun i => hval i h)`. Establish `a3` using `v1 (Fin 2) (fun _ => σ) _ _ σ'' hσ'' (fun _ => a1)`. Rewrite using `[v3 _ _ _ a2 a3, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eigen_of_expansion_in_class : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (w₀ : W0 u.U.toUnifPre), w₀.IsGen → ∀ (α : u.D.toPre.X) (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N) (Φ : Fam u.D.toPre (PadicAlgCl p) S.N), IsComb u.A s b σ → u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ → (∀ β, (∀ z : u.D.toPre.X, β ≠ α + S.N • z) → ∀ j, (Φ.s β).f j = 0) → ∀ (t : S.perp l.yy.ker) (h : S.Gam), ∑ j, (∑ i, y₀ (algebraMap o S.R (S.ρ t j i)) * b i) * y₀ ⟨S.ev h j, S.ev_mem h j⟩ = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val * ∑ j, b j * y₀ ⟨S.ev h j, S.ev_mem h j⟩ := by
  intro h1 h2 hT o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs w₀ hw₀ α b σ Φ hσ hΦ hsupp t h
  obtain ⟨hLL, -⟩ := laws_all h1 h2
  obtain ⟨hc, -, hadm, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  have hodd : Odd S.N := by
    rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hN1 : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  obtain ⟨-, -, -, hval, -, hθ⟩ := hs
  obtain ⟨θ, hθs, hθa⟩ := hθ (t : S.Gam)
  obtain ⟨τ, q, hqy, hqt, hqx, hτ⟩ := GlobalTheory.T.torusPoints_level_weights_from_orthogonal_labels h1 h2 hT o Ω S ρ p y₀ u l hy x hx t
  obtain ⟨⟨w, hw⟩, -⟩ := GlobalTheory.UT.SymFrame.main hLL u.V _ hadm u.D (PadicAlgCl p) S.N hodd q
  obtain ⟨-, -, c3, c4, c5⟩ := GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s b
  choose s' hs' using fun i => (c4 θ (s i)).exists
  obtain ⟨σ', hσ'⟩ := (c4 θ σ).exists
  have hσ'c : IsComb u.A s' b σ' := (c3 θ s' σ σ' hs' hσ).1 hσ'
  have hσ'c2 := c5 S.J (fun i j => y₀ (algebraMap o S.R (S.ρ t j i))) s' b σ' (fun i => hθa i _ (hs' i)) hσ'c
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hLL u.V _ hadm u.D u.A u.G u.semi u.U
  obtain ⟨hb1, hb2⟩ := hbij (PadicAlgCl p) S.N hN1 w₀ hw₀
  obtain ⟨Φ', hΦ'⟩ := (hb1 σ').exists
  have hrel := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q _ hqx θ hθs w₀ hw₀ w hw
    σ σ' Φ Φ' hΦ hΦ' hσ'
  have hwt := ((GlobalTheory.UT.TorusWeight.torus_weight hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hodd q τ hqy
    hqt w hw).2 Φ Φ').1 hrel
  set κ : PadicAlgCl p := y₀ (algebraMap o S.R S.ζN) ^ (l.wt α t).val with hκ
  have hΦeq : Φ' = (κ - 1) • Φ + Φ := by
    rw [sub_smul, one_smul, sub_add_cancel]
    refine fam_ext fun β j => ?_
    rw [hwt β j, smul_f, ← constBF_eq]
    by_cases hβ : ∀ z : u.D.toPre.X, β ≠ α + S.N • z
    · rw [hsupp β hβ j, mul_zero, mul_zero]
    · push Not at hβ
      obtain ⟨z, rfl⟩ := hβ
      rw [hτ, hκ]
      simp
  obtain ⟨⟨σ'', hσ''⟩, -⟩ := GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin 2) (fun _ => σ) ![κ - 1, 1]
  have hσ''e : u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ'' ((κ - 1) • Φ + Φ) := by
    refine hlin (PadicAlgCl p) S.N w₀ σ σ σ'' Φ Φ (κ - 1) hΦ hΦ fun j => ?_
    rw [hσ'' j, Fin.sum_univ_two]
    simp [liftFun, cF]
  have heq : σ'' = σ' := (hb2 Φ').unique (hΦeq ▸ hσ''e) hΦ'
  subst heq
  obtain ⟨v1, -, v3, -⟩ := GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists h1 u.V u.A (PadicAlgCl p) S.N (x h) (e h)
  have a1 := v1 S.J s b _ σ hσ (fun i => hval i h)
  have a2 := v1 S.J s _ _ σ'' hσ'c2 (fun i => hval i h)
  have a3 := v1 (Fin 2) (fun _ => σ) _ _ σ'' hσ'' (fun _ => a1)
  rw [v3 _ _ _ a2 a3, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end GlobalTheory.TestFibre
