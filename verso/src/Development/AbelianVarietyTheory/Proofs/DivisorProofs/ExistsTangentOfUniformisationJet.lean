import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtFnEqValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapValHomFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderJetAlgHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

/- English proof (translation)
Introduce `A _ L g u hsep W x hx hxA h0 w ρ hρ`. Establish `hw : (spMap ρ.toRingHom ≫ x) ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ))`. Rewrite using `[Category.assoc, hxA, ← Cris.spMap_comp]`. Use `congr 1`. Conclude with `RingHom.ext fun c ↦ ρ.commutes c`.

Establish `hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = (u.ex 0).left`. Establish `e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ρ.toRingHom = (Hol.ev 0 h0).toRingHom` using `RingHom.ext fun f ↦ (hρ f).1.trans (Hol.ev_apply 0 h0 f).symm`. Rewrite using `[← Category.assoc, ← Cris.spMap_comp, e]`. Conclude with `hx 0 h0`. Use `⟨Over.homMk (spMap ρ.toRingHom ≫ x) hw, rfl, ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = _`. Rewrite using `[hfst, (u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]`. Introduce `U h f`. Express the relevant statement in the definitionally equal form `⊤ ≤ (spMap ρ.toRingHom ≫ x) ⁻¹ᵁ U at h`. Express the relevant statement in the definitionally equal form `(evalAt (spMap ρ.toRingHom ≫ x) U h f).snd = _`.

Establish `hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U`. Rewrite using `[← hfst]`. Conclude with `fun q _ ↦ h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) q))`. Set `q₀ : Sp ℂ` to `(default : PrimeSpectrum ℂ)`. Take `⟨U', hU', hq, hle⟩` from `exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left q₀) (U := U) (hU0 (Set.mem_univ q₀))`.

Establish `hU0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U'` using `fun q _ ↦ by`. Establish `: q = q₀` using `Subsingleton.elim (α := PrimeSpectrum ℂ) q q₀`. Substitute `this` using the available equality. Conclude with `hq`. Set `W' : Opens (Tot Empty g)` to `W ⊓ ⟨{p | ⊤ ≤ (u.ex p.2).left ⁻¹ᵁ U'}, (u.hol U' 0).1.preimage continuous_snd⟩`.

Establish `h0' : (0 : Tot Empty g) ∈ W'` using `⟨h0, hU0'⟩`. Take `⟨x', hx'U, hx'⟩` from `exists_pt_of_affine (fibUnif u) W' (fun _ _ ↦ trivial) U' hU' (fun p hp ↦ hp.2)`. Set `res : Hol W →ₐ[ℂ] Hol W'` to `Hol.comap id analyticOnNhd_id fun p hp ↦ hp.1`. Establish `hres : ∀ (k : Hol W), ∀ p ∈ W', (res k).fn p = k.fn p` using `fun k p hp ↦ Hol.fn_comap _ _ _ k hp`. Establish `hxx : spMap res.toRingHom ≫ x = x'`.

Use `point_hol_ext_of_isSeparated W' hsep _ _ fun p hp ↦ ?_` and prove the remaining obligations. Establish `e : (Hol.ev p hp).toRingHom.comp res.toRingHom = (Hol.ev p hp.1).toRingHom` using `RingHom.ext fun _ ↦ rfl`. Rewrite using `[hx' p hp, ← Category.assoc, ← Cris.spMap_comp, e]`. Conclude with `hx p hp.1`. Take `⟨ρ', hρ'⟩` from `Hol.exists_jet_algHom W' 0 h0' ((0, w) : Tot Empty g)`.

Establish `hρρ : ρ'.toRingHom.comp res.toRingHom = ρ.toRingHom` using `RingHom.ext fun k ↦ by`. Express the relevant statement in the definitionally equal form `ρ' (res k) = ρ k`. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[(hρ' _).1, (hρ _).1, hres k 0 h0']`. Rewrite using `[(hρ' _).2, (hρ _).2, Hol.fderiv_fn_congr _ (hres k) h0']`.

Establish `hv : spMap ρ.toRingHom ≫ x = spMap ρ'.toRingHom ≫ x'`. Rewrite using `[← hρρ, Cris.spMap_comp, Category.assoc, hxx]`. Establish `hx'U' : ⊤ ≤ x' ⁻¹ᵁ U` using `fun q hq ↦ hle (hx'U hq)`. Take `⟨h', hev, -⟩` from `GlobalTheory.EvalNat.evalAt_natural ρ'.toRingHom x' U hx'U'`. Establish `e1 : evalAt (spMap ρ.toRingHom ≫ x) U h f = ρ' (evalAt x' U hx'U' f)`.

Use `Eq.trans ?_ (hev f)` and prove the remaining obligations. Use `congr 2`. Establish `e2 : ∀ p ∈ W', (evalAt x' U hx'U' f).fn p = valAt' (u.ex p.2).left U f` using `fun p hp ↦ by`. Rewrite using `[(evalAt_fn_eq_valAt' W' x' U hx'U' f p hp).2, hx' p hp]`. Both sides reduce to the same expression.

Establish `hd : DifferentiableAt ℂ (fun z ↦ valAt' (u.ex z).left U f) 0` using `(u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds hU0)`. Rewrite using `[e1, (hρ' _).2, Hol.fderiv_fn_congr _ e2 h0']`. Establish `hc : HasFDerivAt (fun p : Tot Empty g ↦ valAt' (u.ex p.2).left U f) ((fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0).comp (ContinuousLinearMap.snd ℂ _ _)) 0` using `HasFDerivAt.comp (0 : Tot Empty g) (g := fun z ↦ valAt' (u.ex z).left U f) (f := Prod.snd) hd.hasFDerivAt hasFDerivAt_snd`. Rewrite using `[hc.fderiv]`. Both sides reduce to the same expression.
-/
theorem exists_tangent_of_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  intro A _ L g u hsep W x hx hxA h0 w ρ hρ
  have hw : (spMap ρ.toRingHom ≫ x) ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, hxA, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun c ↦ ρ.commutes c
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = (u.ex 0).left := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ρ.toRingHom = (Hol.ev 0 h0).toRingHom :=
      RingHom.ext fun f ↦ (hρ f).1.trans (Hol.ev_apply 0 h0 f).symm
    rw [← Category.assoc, ← Cris.spMap_comp, e]
    exact hx 0 h0
  refine ⟨Over.homMk (spMap ρ.toRingHom ≫ x) hw, rfl, ?_, ?_⟩
  · change spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = _
    rw [hfst, (u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  · intro U h f
    change ⊤ ≤ (spMap ρ.toRingHom ≫ x) ⁻¹ᵁ U at h
    change (evalAt (spMap ρ.toRingHom ≫ x) U h f).snd = _
    have hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      rw [← hfst]
      exact fun q _ ↦ h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) q))
    let q₀ : Sp ℂ := (default : PrimeSpectrum ℂ)
    obtain ⟨U', hU', hq, hle⟩ := exists_isAffineOpen_mem_and_subset
      (x := (u.ex 0).left q₀) (U := U) (hU0 (Set.mem_univ q₀))
    have hU0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U' := fun q _ ↦ by
      have : q = q₀ := Subsingleton.elim (α := PrimeSpectrum ℂ) q q₀
      subst this
      exact hq
    let W' : Opens (Tot Empty g) :=
      W ⊓ ⟨{p | ⊤ ≤ (u.ex p.2).left ⁻¹ᵁ U'}, (u.hol U' 0).1.preimage continuous_snd⟩
    have h0' : (0 : Tot Empty g) ∈ W' := ⟨h0, hU0'⟩
    obtain ⟨x', hx'U, hx'⟩ := exists_pt_of_affine (fibUnif u) W' (fun _ _ ↦ trivial) U' hU' (fun p hp ↦ hp.2)
    let res : Hol W →ₐ[ℂ] Hol W' := Hol.comap id analyticOnNhd_id fun p hp ↦ hp.1
    have hres : ∀ (k : Hol W), ∀ p ∈ W', (res k).fn p = k.fn p := fun k p hp ↦ Hol.fn_comap _ _ _ k hp
    have hxx : spMap res.toRingHom ≫ x = x' := by
      refine point_hol_ext_of_isSeparated W' hsep _ _ fun p hp ↦ ?_
      have e : (Hol.ev p hp).toRingHom.comp res.toRingHom = (Hol.ev p hp.1).toRingHom :=
        RingHom.ext fun _ ↦ rfl
      rw [hx' p hp, ← Category.assoc, ← Cris.spMap_comp, e]
      exact hx p hp.1
    obtain ⟨ρ', hρ'⟩ := Hol.exists_jet_algHom W' 0 h0' ((0, w) : Tot Empty g)
    have hρρ : ρ'.toRingHom.comp res.toRingHom = ρ.toRingHom := RingHom.ext fun k ↦ by
      change ρ' (res k) = ρ k
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [(hρ' _).1, (hρ _).1, hres k 0 h0']
      · rw [(hρ' _).2, (hρ _).2, Hol.fderiv_fn_congr _ (hres k) h0']
    have hv : spMap ρ.toRingHom ≫ x = spMap ρ'.toRingHom ≫ x' := by
      rw [← hρρ, Cris.spMap_comp, Category.assoc, hxx]
    have hx'U' : ⊤ ≤ x' ⁻¹ᵁ U := fun q hq ↦ hle (hx'U hq)
    obtain ⟨h', hev, -⟩ := GlobalTheory.EvalNat.evalAt_natural ρ'.toRingHom x' U hx'U'
    have e1 : evalAt (spMap ρ.toRingHom ≫ x) U h f = ρ' (evalAt x' U hx'U' f) := by
      refine Eq.trans ?_ (hev f)
      congr 2
    have e2 : ∀ p ∈ W', (evalAt x' U hx'U' f).fn p = valAt' (u.ex p.2).left U f := fun p hp ↦ by
      rw [(evalAt_fn_eq_valAt' W' x' U hx'U' f p hp).2, hx' p hp]
      rfl
    have hd : DifferentiableAt ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 :=
      (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds hU0)
    rw [e1, (hρ' _).2, Hol.fderiv_fn_congr _ e2 h0']
    have hc : HasFDerivAt (fun p : Tot Empty g ↦ valAt' (u.ex p.2).left U f)
        ((fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0).comp (ContinuousLinearMap.snd ℂ _ _)) 0 :=
      HasFDerivAt.comp (0 : Tot Empty g) (g := fun z ↦ valAt' (u.ex z).left U f) (f := Prod.snd)
        hd.hasFDerivAt hasFDerivAt_snd
    rw [hc.fderiv]
    rfl

end GlobalTheory.AnPer
