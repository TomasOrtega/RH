import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvaluationLemmaForNablaLevels
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverProductIndepOfLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelMapsRankZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

section Descent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.CoverDescent GlobalTheory.ClsVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClsDescent

/- English proof (translation)
Establish `hL : Laws` using `GlobalTheory.firstFiveLaws.1`. Establish `hN` using `GlobalTheory.LevelMapsAnyRank.levelMaps Dw`. Establish `hWD` using `(GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1`. Establish `hAT` using `GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂`. Use `haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad`.

Take `⟨hval, hnat⟩` from `GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hTr hLv a P hP (fun q => d.eF (w q)) β`. Establish `hinv` using `GlobalTheory.EquivariantLiftInvariance.cover_product_indep_of_lift hC E H Dw l Xo c n d hlev hA ⟨_, hnab⟩ ψ₀ hψ₀ w hw₀ Λ N hU hTr hLv a P hP β`. Establish `hbc` using `GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c`. Establish `hbc₂` using `GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂`. Establish `hcomp` using `(GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1`.

Take `⟨hdvd, hM, -, -, -, -, hlift, hsec, -⟩` from `id hlev`. Take `⟨r, jK, m, -, -, he, heA, -, hF⟩` from `hN l d.l₂ Xo d.Xo₂ hdvd`. Take `⟨rF, h1, h2, _, _, _, -⟩` from `hF c d.c₂ d.hF.symm`. Establish `hEta : DeltaDat.EtaOK { d with r` using `r, m := m } := by`. Use `⟨fun b => ?_, heA⟩` and prove the remaining obligations.

Use `he b` as an intermediate fact. Rewrite `this` using `[hM, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)]`. Then use the resulting hypothesis. Take `⟨hov1, hov2, -⟩` from `GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n { d with r := r, m := m }`. Take `⟨S, _, φ, j, x₂, f1, f2, f3, hj, hx, hx'⟩` from `exists_cover_point d.hF.symm r rF h1 h2 p.R y.x y.x_over`. Use `letI : Algebra p.R S := φ.toAlgebra`.

Use `letI : Algebra c.F S := (φ.comp (algebraMap c.F p.R)).toAlgebra`. Use `letI : Algebra d.c₂.F S := j.toAlgebra`. Use `haveI : Module.Finite p.R S := f1`. Use `haveI : Algebra.Smooth p.R S := f2`. Use `haveI : Module.FaithfullyFlat p.R S := f3`.

Use `haveI := isReduced_of_smooth_algebra p.R S`. Establish `hS : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a` using `fun a => RingHom.congr_fun hj a`. Set `φa : p.R →ₐ[c.F] S` to `{ φ with commutes' := fun _ => rfl }`. Take `⟨y', hy'⟩` from `hbc p.R S φa y`. Take `⟨y₂, -, hy₂⟩` from `hov1 S hS y' x₂ (hx.trans hy'.1.symm) hx'`.

Take `⟨v₀, hv₀, -⟩` from `hval S y₂`. Establish `core : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (χ : p.R →ₐ[c.F] k) (χ' : S →+* k), χ'.comp φ = χ.toRingHom → ∀ (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d …`. Introduce `k _ _ _ _ hk χ χ' hχ z z₂ hz hz₂ v hv`. Establish `c1 : ∀ a : c.F, χ' (algebraMap c.F S a) = algebraMap c.F k a` using `fun a => (RingHom.congr_fun hχ (algebraMap c.F p.R a)).trans (χ.commutes a)`. Set `ψ : S →ₐ[c.F] k` to `{ χ' with commutes' := c1 }`.

Set `ψ₂ : S →ₐ[d.c₂.F] k` to `{ χ' with commutes' := fun b => by`. Take `⟨a, rfl⟩` from `d.eF.surjective b`. Conclude with `(congrArg χ' (hS a)).trans ((c1 a).trans (hk a).symm) }`. Establish `hψ : ψ.comp φa = χ` using `AlgHom.ext fun x => RingHom.congr_fun hχ x`. Establish `hz' : FrMap ψ y' z` using `(hcomp _ _ _ φa ψ y y' z hy').2 (by rw [hψ]; exact hz)`.

Take `⟨w₂, hw₂⟩` from `hbc₂ S k ψ₂ y₂`. Establish `hw'` using `hov2 S hS k hk ψ ψ₂ rfl y' y₂ z w₂ hy₂ hz' hw₂`. Take `⟨v', hv', -⟩` from `hval k w₂`. Rewrite using `[hinv r m hEta k hk z z₂ w₂ hz₂ hw' v v' hv hv', ← hnat S k ψ₂ y₂ w₂ hw₂ v₀ v' hv₀ hv', evR_baseChange hWD hAT d.cδ hsec.1 ψ₂ y₂ w₂ hw₂]`. Conclude with `map_mul χ' _ _`.

Establish `pts : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : p.R →+* k), ∃ (_ : Algebra c.F k) (_ : Algebra d.c₂.F k) (χa : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k) (v : k), (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) ∧ χa.toRingHom = χ ∧ FrMap χa y z ∧ F …`. Introduce `k _ _ χ`. Use `letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra`. Use `letI i2 : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra`. Establish `hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a` using `fun a => congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)`.

Set `χa : p.R →ₐ[c.F] k` to `{ χ with commutes' := fun _ => rfl }`. Take `⟨z, hz⟩` from `hbc p.R k χa y`. Take `⟨z₂, hz₂⟩` from `hlift k hk z`. Take `⟨v, hv, -⟩` from `hval k z₂`. Conclude with `⟨i1, i2, χa, z, z₂, v, hk, rfl, hz, hz₂, hv⟩`.

Take `⟨u, hu⟩` from `exists_preimage_of_geometric p.R S (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) (by`. Introduce `k _ _ χ₁ χ₂ h12`. Take `⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩` from `pts k (χ₁.comp φ)`. Conclude with `(core k hk χa χ₁ hχ.symm z z₂ hz hz₂ v hv).trans (core k hk χa χ₂ (h12.symm.trans hχ.symm) z z₂ hz hz₂ v hv).symm)`. Use `ExistsUnique.intro u ?_ ?_` and prove the remaining obligations.

Introduce `k _ _ _ _ hk χ z z₂ hz hz₂ v hv`. Take `⟨χ', hχ'⟩` from `exists_lift_geometric p.R S k χ.toRingHom`. Rewrite using `[← core k hk χ χ' hχ' z z₂ hz hz₂ v hv, ← hu]`. Conclude with `(RingHom.congr_fun hχ' u).symm`. Introduce `u' hu'`.

Use `eq_of_geometric_points _ _ fun k _ _ χ => ?_` and prove the remaining obligations. Take `⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩` from `pts k χ`. Take `⟨χ', hχ'⟩` from `exists_lift_geometric p.R S k χ`. Substitute `hχ` using the available equality. Establish `e` using `core k hk χa χ' hχ' z z₂ hz hz₂ v hv`.

Rewrite `e` using `[← hu]`. Conclude with `(hu' k hk χa z z₂ hz hz₂ v hv).trans (e.symm.trans (RingHom.congr_fun hχ' u))`.
-/
theorem value_descends (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hlev : d.IsLev)
    (hA : d.l₂.A = l.A) [StarRing (𝓞 E)] (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (ψ₀ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (hψ₀ : d.PsiTie ψ₀) (w : (Fin n → LevQ Dw d.l₂) → c.F)
    (hw₀ : DatEq d ψ₀ w) (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod) (hTr : Λ.TrivAt d.l₂.M) (hLv : Λ.LevOK N d.l₂.M)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F)
    (hP : P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (β : d.c₂.F)
    (p : TRing c.F) (y : FrPt Xo c p.R) :
    ∃! u : p.R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
      ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P z₂ v →
        χ u = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hN := GlobalTheory.LevelMapsAnyRank.levelMaps Dw
  have hWD := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  have hAT := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hTr hLv a P hP
    (fun q => d.eF (w q)) β
  have hinv := GlobalTheory.EquivariantLiftInvariance.cover_product_indep_of_lift hC E H Dw l Xo c n d hlev hA ⟨_, hnab⟩ ψ₀ hψ₀ w hw₀ Λ N hU hTr hLv a P hP β
  have hbc := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c
  have hbc₂ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂
  have hcomp := (GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1
  obtain ⟨hdvd, hM, -, -, -, -, hlift, hsec, -⟩ := id hlev
  obtain ⟨r, jK, m, -, -, he, heA, -, hF⟩ := hN l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h1, h2, _, _, _, -⟩ := hF c d.c₂ d.hF.symm
  have hEta : DeltaDat.EtaOK { d with r := r, m := m } := by
    refine ⟨fun b => ?_, heA⟩
    have := he b
    rwa [hM, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)] at this
  obtain ⟨hov1, hov2, -⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n { d with r := r, m := m }
  obtain ⟨S, _, φ, j, x₂, f1, f2, f3, hj, hx, hx'⟩ :=
    exists_cover_point d.hF.symm r rF h1 h2 p.R y.x y.x_over
  letI : Algebra p.R S := φ.toAlgebra
  letI : Algebra c.F S := (φ.comp (algebraMap c.F p.R)).toAlgebra
  letI : Algebra d.c₂.F S := j.toAlgebra
  haveI : Module.Finite p.R S := f1
  haveI : Algebra.Smooth p.R S := f2
  haveI : Module.FaithfullyFlat p.R S := f3
  haveI := isReduced_of_smooth_algebra p.R S
  have hS : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := fun a =>
    RingHom.congr_fun hj a
  let φa : p.R →ₐ[c.F] S := { φ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := hbc p.R S φa y
  obtain ⟨y₂, -, hy₂⟩ := hov1 S hS y' x₂ (hx.trans hy'.1.symm) hx'
  obtain ⟨v₀, hv₀, -⟩ := hval S y₂
  have core : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (χ' : S →+* k), χ'.comp φ = χ.toRingHom →
      ∀ (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
      ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P z₂ v →
        χ' (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
    intro k _ _ _ _ hk χ χ' hχ z z₂ hz hz₂ v hv
    have c1 : ∀ a : c.F, χ' (algebraMap c.F S a) = algebraMap c.F k a := fun a =>
      (RingHom.congr_fun hχ (algebraMap c.F p.R a)).trans (χ.commutes a)
    let ψ : S →ₐ[c.F] k := { χ' with commutes' := c1 }
    let ψ₂ : S →ₐ[d.c₂.F] k := { χ' with
      commutes' := fun b => by
        obtain ⟨a, rfl⟩ := d.eF.surjective b
        exact (congrArg χ' (hS a)).trans ((c1 a).trans (hk a).symm) }
    have hψ : ψ.comp φa = χ := AlgHom.ext fun x => RingHom.congr_fun hχ x
    have hz' : FrMap ψ y' z := (hcomp _ _ _ φa ψ y y' z hy').2 (by rw [hψ]; exact hz)
    obtain ⟨w₂, hw₂⟩ := hbc₂ S k ψ₂ y₂
    have hw' := hov2 S hS k hk ψ ψ₂ rfl y' y₂ z w₂ hy₂ hz' hw₂
    obtain ⟨v', hv', -⟩ := hval k w₂
    rw [hinv r m hEta k hk z z₂ w₂ hz₂ hw' v v' hv hv', ← hnat S k ψ₂ y₂ w₂ hw₂ v₀ v' hv₀ hv',
      evR_baseChange hWD hAT d.cδ hsec.1 ψ₂ y₂ w₂ hw₂]
    exact map_mul χ' _ _
  have pts : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : p.R →+* k),
      ∃ (_ : Algebra c.F k) (_ : Algebra d.c₂.F k) (χa : p.R →ₐ[c.F] k) (z : FrPt Xo c k)
        (z₂ : FrPt d.Xo₂ d.c₂ k) (v : k),
        (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) ∧ χa.toRingHom = χ ∧
        FrMap χa y z ∧ FrOver d z₂ z ∧ ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) Λ β N P z₂ v := by
    intro k _ _ χ
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    letI i2 : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
      congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hbc p.R k χa y
    obtain ⟨z₂, hz₂⟩ := hlift k hk z
    obtain ⟨v, hv, -⟩ := hval k z₂
    exact ⟨i1, i2, χa, z, z₂, v, hk, rfl, hz, hz₂, hv⟩
  obtain ⟨u, hu⟩ := exists_preimage_of_geometric p.R S (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) (by
    intro k _ _ χ₁ χ₂ h12
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k (χ₁.comp φ)
    exact (core k hk χa χ₁ hχ.symm z z₂ hz hz₂ v hv).trans
      (core k hk χa χ₂ (h12.symm.trans hχ.symm) z z₂ hz hz₂ v hv).symm)
  refine ExistsUnique.intro u ?_ ?_
  · intro k _ _ _ _ hk χ z z₂ hz hz₂ v hv
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ.toRingHom
    rw [← core k hk χ χ' hχ' z z₂ hz hz₂ v hv, ← hu]
    exact (RingHom.congr_fun hχ' u).symm
  · intro u' hu'
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k χ
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ
    subst hχ
    have e := core k hk χa χ' hχ' z z₂ hz hz₂ v hv
    rw [← hu] at e
    exact (hu' k hk χa z z₂ hz hz₂ v hv).trans (e.symm.trans (RingHom.congr_fun hχ' u))

end GlobalTheory.ClsDescent

end Descent

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsDescent

open GlobalTheory.ShortDescent in

/- English proof (translation)
Introduce `hC E _ _ _ H Dw l Xo c n d hLev hA hnab ψ hψ w₀ hw₀ Λ N hU hT hO a P hP`. Take `⟨_, hnab⟩` from `hnab`. Establish `hL : Laws` using `GlobalTheory.firstFiveLaws.1`. Establish `hAll` using `GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c`. Establish `hP₂` using `(GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP`.

Take `⟨hex, -⟩` from `GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hT hO a _ hP₂ (fun q => d.eF (w₀ q)) 1`. Establish `hd` using `value_descends hC d hLev hA hnab ψ hψ w₀ hw₀ Λ N hU hT hO a _ hP₂ 1`. Take `⟨hlift, -, hbor⟩` from `GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d`. Use `⟨fun p y => (hd p y).exists.choose, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, ?_⟩` and prove the remaining obligations. Use `(hd q z).unique (hd q z).exists.choose_spec ?_` and prove the remaining obligations.

Introduce `k _ _ _ _ hk χ w w₂ hw ho v hv`. Conclude with `(hd p y).exists.choose_spec k hk (χ.comp φ) w w₂ (GlobalTheory.FramedBaseChange.trans φ χ h hw) ho v hv`. Use `(hd p y').unique (hd p y').exists.choose_spec ?_` and prove the remaining obligations. Introduce `k _ _ _ _ hk χ w' w₂' hw' ho' v' hv'`. Take `⟨w, hw⟩` from `GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χ y`.

Establish `hb` using `frBorBC _ _ χ t y y' w w' h hw hw'`. Take `⟨w₂, hx₂, ho⟩` from `hlift k hk w w₂'.x (ho'.1.trans hb.1) w₂'.x_over`. Establish `hb₂` using `hbor k hk _ w w' w₂ w₂' ho ho' hx₂.symm hb`. Take `⟨v, hv, -⟩` from `hex k w₂`. Establish `hv₂` using `(GlobalTheory.thetaValue_weight hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab k w₂ w₂' _ hb₂ n a _).2 hP₂ _ Λ _ N v hv`.

Establish `e` using `(hd p y).exists.choose_spec k hk χ w w₂ hw ho v hv`. Rewrite using `[(hex k w₂').unique hv' hv₂, map_mul, map_wchar, evR_eq_of_point_eq d hψ w₂ w₂' hx₂.symm]`. Use `(congrArg (_ * ·) e).trans ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `k _ _ _ _ hk y y₂ ho`.

Take `⟨v, hv, -⟩` from `hex k y₂`. Use `⟨fun _ => v, fun _ => hv, ?_⟩` and prove the remaining obligations. Establish `hy` using `hAll k y`. Establish `e : ∑ _cl : Unit, algebraMap c.F k (1 * (((1 : ℕ) : c.F))⁻¹ * 1) * v = v` using `by simp`. Rewrite using `[e]`.

Unfold `evR evalAt`. Rewrite using `[dif_pos hy]`. Conclude with `(hd _ _).exists.choose_spec k hk _ y y₂ hy.choose_spec.choose_spec.choose_spec ho v hv`.
-/
theorem exists_sec_oneClass : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ w : (Fin n → LevQ Dw d.l₂) → c.F, DatEq d ψ w → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d (fun _ : Unit => w) (fun _ => Λ) (fun _ => N) (fun _ => 1) 1 (fun _ => 1) LinearMap.id (fun _ => P) f := by
  intro hC E _ _ _ H Dw l Xo c n d hLev hA hnab ψ hψ w₀ hw₀ Λ N hU hT hO a P hP
  obtain ⟨_, hnab⟩ := hnab
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hAll := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c
  have hP₂ := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP
  obtain ⟨hex, -⟩ := GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hT hO a _ hP₂
    (fun q => d.eF (w₀ q)) 1
  have hd := value_descends hC d hLev hA hnab ψ hψ w₀ hw₀ Λ N hU hT hO a _ hP₂ 1
  obtain ⟨hlift, -, hbor⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d
  refine ⟨fun p y => (hd p y).exists.choose, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, ?_⟩
  · refine (hd q z).unique (hd q z).exists.choose_spec ?_
    intro k _ _ _ _ hk χ w w₂ hw ho v hv
    exact (hd p y).exists.choose_spec k hk (χ.comp φ) w w₂ (GlobalTheory.FramedBaseChange.trans φ χ h hw) ho v hv
  · refine (hd p y').unique (hd p y').exists.choose_spec ?_
    intro k _ _ _ _ hk χ w' w₂' hw' ho' v' hv'
    obtain ⟨w, hw⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χ y
    have hb := frBorBC _ _ χ t y y' w w' h hw hw'
    obtain ⟨w₂, hx₂, ho⟩ := hlift k hk w w₂'.x (ho'.1.trans hb.1) w₂'.x_over
    have hb₂ := hbor k hk _ w w' w₂ w₂' ho ho' hx₂.symm hb
    obtain ⟨v, hv, -⟩ := hex k w₂
    have hv₂ := (GlobalTheory.thetaValue_weight hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab k w₂ w₂' _ hb₂ n a _).2 hP₂
      _ Λ _ N v hv
    have e := (hd p y).exists.choose_spec k hk χ w w₂ hw ho v hv
    rw [(hex k w₂').unique hv' hv₂, map_mul, map_wchar, evR_eq_of_point_eq d hψ w₂ w₂' hx₂.symm]
    refine (congrArg (_ * ·) e).trans ?_
    ring
  · intro k _ _ _ _ hk y y₂ ho
    obtain ⟨v, hv, -⟩ := hex k y₂
    refine ⟨fun _ => v, fun _ => hv, ?_⟩
    have hy := hAll k y
    have e : ∑ _cl : Unit, algebraMap c.F k (1 * (((1 : ℕ) : c.F))⁻¹ * 1) * v = v := by simp
    rw [e]
    unfold evR evalAt
    rw [dif_pos hy]
    exact (hd _ _).exists.choose_spec k hk _ y y₂ hy.choose_spec.choose_spec.choose_spec ho v hv

end GlobalTheory.ClsDescent
