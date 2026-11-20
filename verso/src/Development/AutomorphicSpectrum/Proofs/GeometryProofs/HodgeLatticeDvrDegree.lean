import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeSpanIndependentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenSecondStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseConstantsRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddingsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGermEigenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreCurveGermPowersStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationBoundedFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

/- English proof (translation)
Establish `h1` using `(GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a`. Establish `h2` using `hg.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))`. Establish `h3` using `LinearMap.congr_fun h1 (vmap (genMap ξ p) y)`. Simplify using `only [LinearMap.comp_apply] at h3`. Establish `h4` using `vmap_rhoH (S.mapK p) a y`.

Use `(congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h4).trans ?_` and prove the remaining obligations. Use `(congrArg (toVec Ω d) h3.symm).trans ?_` and prove the remaining obligations. Conclude with `h2.symm`.
-/
theorem toH_rhoH {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X : Scheme.{0}}
    {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)} (S : GermSys t ξ M)
    {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗) (p : Cpt ξ) (a : 𝓞 E)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (rhoH (S.g p).B a y) = 𝓗.ρH a (toH S p y) := by
  have h1 := (GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a
  have h2 := hg.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))
  have h3 := LinearMap.congr_fun h1 (vmap (genMap ξ p) y)
  simp only [LinearMap.comp_apply] at h3
  have h4 := vmap_rhoH (S.mapK p) a y
  refine (congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h4).trans ?_
  refine (congrArg (toVec Ω d) h3.symm).trans ?_
  exact h2.symm

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

/- English proof (translation)
Use `eigW_induction (P := fun w => HT.eigProj 𝓗.ρH σ (toH S p w) = 0) hw ?_ ?_ ?_` and prove the remaining obligations. Introduce `a y`. Establish `hc : HT.eigProj 𝓗.ρH σ (𝓗.ρH a (toH S p y)) = 𝓗.ρH a (HT.eigProj 𝓗.ρH σ (toH S p y))`. Simplify using `only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]`. Establish `hm` using `HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem 𝓗.ρH σ (toH S p y)) a`. Establish `e1 : toH S p (rhoH (S.g p).B a y - τ a • y) = 𝓗.ρH a (toH S p y) - σ (a : E) • toH S p y` using `(toH_sub S p _ _).trans (congrArg₂ (· - ·) (toH_rhoH S hg p a y) ((toH_smul S p _ _).trans (congrArg (· • toH S p y) (hτ a))))`. Use `(congrArg _ e1).trans ?_` and prove the remaining obligations. Generalize the expression as in `toH S p y = v at hc hm`.

Rewrite using `[map_sub, map_smul, hc, hm, sub_self]`. Conclude with `(congrArg _ (toH_zero S p)).trans (map_zero _)`. Introduce `y y' h1 h2`. Use `(congrArg _ (toH_add S p y y')).trans ?_` and prove the remaining obligations. Conclude with `(map_add _ _ _).trans (by rw [h1, h2, add_zero])`.
-/
theorem eigProj_toH_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    {X : Scheme.{0}} {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗)
    (σ : E →+* Ω) (p : Cpt ξ) (τ : 𝓞 E →+* X.presheaf.stalk p.1) (hτ : ∀ a, genMap ξ p (τ a) = σ (a : E))
    {w : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)} (hw : w ∈ eigW (S.g p).B τ) :
    HT.eigProj 𝓗.ρH σ (toH S p w) = 0 := by
  refine eigW_induction (P := fun w => HT.eigProj 𝓗.ρH σ (toH S p w) = 0) hw ?_ ?_ ?_
  · intro a y
    have hc : HT.eigProj 𝓗.ρH σ (𝓗.ρH a (toH S p y)) = 𝓗.ρH a (HT.eigProj 𝓗.ρH σ (toH S p y)) := by
      simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    have hm := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem 𝓗.ρH σ (toH S p y)) a
    have e1 : toH S p (rhoH (S.g p).B a y - τ a • y) = 𝓗.ρH a (toH S p y) - σ (a : E) • toH S p y :=
      (toH_sub S p _ _).trans (congrArg₂ (· - ·) (toH_rhoH S hg p a y)
        ((toH_smul S p _ _).trans (congrArg (· • toH S p y) (hτ a))))
    refine (congrArg _ e1).trans ?_
    generalize toH S p y = v at hc hm
    rw [map_sub, map_smul, hc, hm, sub_self]
  · exact (congrArg _ (toH_zero S p)).trans (map_zero _)
  · intro y y' h1 h2
    refine (congrArg _ (toH_add S p y y')).trans ?_
    exact (map_add _ _ _).trans (by rw [h1, h2, add_zero])

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

/- English proof (translation)
Use `choose m hm using fun j => exists_sub_mem_eigW hxq τ (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)))`. Use `⟨Matrix.of m, ?_, hm⟩` and prove the remaining obligations. Establish `key : ∀ j, ∑ k, Ap j k • u k = ∑ k, ((Matrix.of m).map (genMap ξ q) * Aq) j k • u k`. Introduce `j`. Establish `h0` using `eigProj_toH_eq_zero S hg σ q τ hτ (hm j)`.

Establish `h1 : toH S q (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)) - ∑ l, m j l • xq l) = toH S p (xp j) - ∑ l, genMap ξ q (m j l) • toH S q (xq l)`. Use `(toH_sub S q _ _).trans (congrArg₂ (· - ·) (toH_spec S p q h he (xp j)).symm ?_)` and prove the remaining obligations. Conclude with `(toH_sum _ S q _).trans (Finset.sum_congr rfl fun l _ => toH_smul S q _ _)`. Establish `h2` using `(congrArg (HT.eigProj 𝓗.ρH σ) h1).symm.trans h0`. Rewrite `h2` using `[map_sub, sub_eq_zero, map_sum]`.

Use `((hAp j).symm.trans h2).trans ?_` and prove the remaining obligations. Simplify using `only [map_smul, hAq, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, Matrix.map_apply, Matrix.of_apply, smul_smul]`. Conclude with `Finset.sum_comm`. Use extensionality with `j k`. Use `(Fintype.linearIndependent_iff.1 hu) (fun k => Ap j k - ((Matrix.of m).map (genMap ξ q) * Aq) j k) (by simp only [sub_smul, Finset.sum_sub_distrib, key j, sub_self]) k` as an intermediate fact.

Conclude with `sub_eq_zero.1 this`.
-/
theorem exists_trans {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    {X : Scheme.{0}} {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {d r : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {𝓗 : HodgeLat M.lat ρ H.bar r} (hg : S.Gives 𝓗)
    (σ : E →+* Ω) (p q : Cpt ξ) (h : q.1 ⤳ p.1) (τ : 𝓞 E →+* X.presheaf.stalk q.1)
    (hτ : ∀ a, genMap ξ q (τ a) = σ (a : E)) {φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d}
    {lam' : Germ.PS (X.presheaf.stalk q.1) 2 d}
    (he : transH (S.φ p) (S.ψ p) (S.lam p) = transH (S.φ q) (S.ψ q) (S.lam q) ∘ₗ
      transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
        (MvPowerSeries.map (genMap ξ q) lam'))
    {xp : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)}
    {xq : Fin r → (Fin d → X.presheaf.stalk q.1) × (Fin d → X.presheaf.stalk q.1)}
    (hxq : IsHBasis (S.g q).B xq) {u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)}
    (hu : LinearIndependent Ω u) {Ap Aq : Matrix (Fin r) (Fin r) Ω}
    (hAp : ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (xp j)) = ∑ l, Ap j l • u l)
    (hAq : ∀ j, HT.eigProj 𝓗.ρH σ (toH S q (xq j)) = ∑ l, Aq j l • u l) :
    ∃ Mt : Matrix (Fin r) (Fin r) (X.presheaf.stalk q.1), Ap = Mt.map (genMap ξ q) * Aq ∧
      ∀ j, transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)) - ∑ l, Mt j l • xq l ∈
        eigW (S.g q).B τ := by
  choose m hm using fun j => exists_sub_mem_eigW hxq τ
    (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)))
  refine ⟨Matrix.of m, ?_, hm⟩
  have key : ∀ j, ∑ k, Ap j k • u k = ∑ k, ((Matrix.of m).map (genMap ξ q) * Aq) j k • u k := by
    intro j
    have h0 := eigProj_toH_eq_zero S hg σ q τ hτ (hm j)
    have h1 : toH S q (transH φ' ψ' lam' (vmap (X.presheaf.stalkSpecializes h).hom (xp j)) - ∑ l, m j l • xq l) =
        toH S p (xp j) - ∑ l, genMap ξ q (m j l) • toH S q (xq l) := by
      refine (toH_sub S q _ _).trans (congrArg₂ (· - ·) (toH_spec S p q h he (xp j)).symm ?_)
      exact (toH_sum _ S q _).trans (Finset.sum_congr rfl fun l _ => toH_smul S q _ _)
    have h2 := (congrArg (HT.eigProj 𝓗.ρH σ) h1).symm.trans h0
    rw [map_sub, sub_eq_zero, map_sum] at h2
    refine ((hAp j).symm.trans h2).trans ?_
    simp only [map_smul, hAq, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, Matrix.map_apply, Matrix.of_apply,
      smul_smul]
    exact Finset.sum_comm
  ext j k
  have := (Fintype.linearIndependent_iff.1 hu) (fun k => Ap j k - ((Matrix.of m).map (genMap ξ q) * Aq) j k)
    (by simp only [sub_smul, Finset.sum_sub_distrib, key j, sub_self]) k
  exact sub_eq_zero.1 this

end GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.DegZ in

/- English proof (translation)
Introduce `E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ 𝓗 O _ _ _ _ s _ _ ϖ p σ hϖ hp hdvd hs hξ hpow hgive hfib hcard hrange u hu hsp Γ`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hinj : Function.Injective (algebraMap O Ω)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Assume the negation of the conclusion as `hx0`. Take `⟨n, w, hw⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ`. Establish `h1 : algebraMap O Ω ϖ ^ n = 0` using `by rw [← map_pow, ← hw, map_mul, hx, zero_mul]`. Establish `h0 : algebraMap O Ω ϖ = 0` using `(pow_eq_zero_iff (fun hn => by simp [hn] at h1)).1 h1`. Take `⟨c, hc⟩` from `hdvd`.

Establish `h2` using `congrArg (algebraMap O Ω) hc`. Rewrite `h2` using `[map_natCast, map_mul, h0, zero_mul]`. Conclude with `hp.ne_zero (by exact_mod_cast h2)`. Establish `hreg` using `GlobalTheory.T.base_constants_regular X Ω ξ O s hs`. Establish `hσ : ∀ (q : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ q` using `fun q a => by`.

Take `⟨o, ho⟩` from `hrange σ a`. Conclude with `ho ▸ hreg q o`. Set `τ : ∀ q : Cpt ξ, 𝓞 E →+* X.presheaf.stalk q.1` to `fun q => (GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q).symm.toRingHom.comp ((σ.comp (algebraMap (𝓞 E) E)).codRestrict (regAt ξ q) (hσ q))`. Establish `hτ : ∀ (q : Cpt ξ) (a : 𝓞 E), genMap ξ q (τ q a) = σ (a : E)` using `fun q a => by`. Use `GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv_coe ξ hξ q (τ q a)` as an intermediate fact.

Rewrite using `[← this]`. Simplify using `[τ]`. Set `q0 : Cpt ξ` to `⟨centre Γ.η, Γ.η_spec⟩`. Set `qi : Γ.C.I → Cpt ξ` to `fun i => ⟨centre (Γ.z i), FibreCurve.z_spec Γ i⟩`. Set `v0 : X.presheaf.stalk q0.1 →+* Γ.κ` to `(Scheme.stalkClosedPointTo Γ.η).hom`.

Set `vi : ∀ i, X.presheaf.stalk (qi i).1 →+* (Γ.C.v i).valuationSubring` to `fun i => (Scheme.stalkClosedPointTo (Γ.z i)).hom`. Establish `hpκ : (p : Γ.κ) = 0`. Take `⟨hh, s0, hs0, hs1⟩` from `Γ.η_zero`. Take `⟨c, hc⟩` from `hdvd`. Take `⟨c', hc'⟩` from `hreg q0 c`.

Establish `e : (p : X.presheaf.stalk q0.1) = s0 * c'` using `hξ.inj q0 (by`. Establish `h2` using `congrArg (algebraMap O Ω) hc`. Rewrite `h2` using `[map_natCast, map_mul]`. Rewrite using `[map_natCast, map_mul, h2, hc']`. Conclude with `congrArg (· * algebraMap O Ω c) hs0.symm)`.

Establish `h3` using `congrArg v0 e`. Rewrite `h3` using `[map_natCast, map_mul]`. Rewrite using `[h3]`. Establish `h4 : v0 s0 = 0` using `hs1`. Rewrite using `[h4, zero_mul]`.

Use `haveI : CharP Γ.κ p := (CharP.charP_iff_prime_eq_zero hp).2 hpκ`. Take `⟨F, hF0, hFi⟩` from `GlobalTheory.T.fibre_curve_germ_powers E H hstar X t Ω ξ d M S O s _ p Γ hξ hpow hfib`. Use `choose hFB φ' ψ' lam' he hφ hψ hlam using hFi`. Use `choose xs A hxs hfr hpr using GlobalTheory.T.hodge_lattice_germ_eigen E H X t Ω ξ d r M S ρ 𝓗 σ u hξ hgive hσ hu hsp`. Establish `hdet` using `fun q => (GlobalTheory.T.hodge_lattice_span_independent X Ω ξ E (Fin d → Ω) M.lat ρ H.bar r 𝓗 σ u hσ hu hsp).2.2 q (A q) (hfr q)`.

Use `choose Mt hAM hMt using fun i => exists_trans S hgive σ (qi i) q0 (FibreCurve.generic_centre_specializes Γ i) (τ q0) (hτ q0) (he i) (hxs q0) hu (hpr (qi i)) (hpr q0)`. Set `χ : 𝓞 E →+* Γ.κ` to `v0.comp (τ q0)`. Establish `hsq : ∀ i, ((Γ.C.v i).valuationSubring.subtype).comp (vi i) = v0.comp (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom` using `fun i => by`. Establish `key` using `ProjectiveLinePlaces.stalk_square (FibreCurve.generic_centre_specializes Γ i) (Scheme.stalkClosedPointTo (Γ.z i)) (Scheme.stalkClosedPointTo Γ.η) (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype) ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk Γ.η).trans ((Γ.z_gen i).symm.tra …`. Conclude with `RingHom.ext fun s => (congrArg (fun g => g.hom s) key).symm`.

Establish `hτs : ∀ i a, (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom (τ (qi i) a) = τ q0 a` using `fun i a => hξ.inj q0 ((ProjectiveLinePlaces.genMap_specializes (FibreCurve.generic_centre_specializes Γ i) q0.2 (qi i).2 _).trans ((hτ (qi i) a).trans (hτ q0 a).symm))`. Establish `hχ : ∀ i a, Γ.C.v i (χ a) ≤ 1` using `fun i a => by`. Establish `e : χ a = ((vi i (τ (qi i) a) : (Γ.C.v i).valuationSubring) : Γ.κ)` using `(congrArg v0 (hτs i a).symm).trans (RingHom.congr_fun (hsq i) (τ (qi i) a)).symm`. Rewrite using `[e]`. Conclude with `(vi i (τ (qi i) a)).2`.

Set `x₀ : Fin r → (Fin d → Γ.κ) × (Fin d → Γ.κ)` to `fun l => vmap v0 (xs q0 l)`. Set `x : ∀ i : Γ.C.I, Fin r → (Fin d → (Γ.C.v i).valuationSubring) × (Fin d → (Γ.C.v i).valuationSubring)` to `fun i j => vmap (vi i) (xs (qi i) j)`. Set `N : Γ.C.I → Matrix (Fin r) (Fin r) Γ.κ` to `fun i => (Mt i).map v0`. Establish `hx₀ : IsHBasis F.B x₀` using `GlobalTheory.T.intersection_second E _ _ v0 d r _ _ _ hF0 (hxs q0)`. Establish `hx : ∀ i, IsHBasis (F.Bi i) (x i)` using `fun i => GlobalTheory.T.intersection_second E _ _ (vi i) d r _ _ _ (hFB i) (hxs (qi i))`.

Establish `hrel : ∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (Γ.C.v i).valuationSubring.subtype (x i j)) - ∑ l, N i j l • x₀ l ∈ eigW F.B χ` using `fun i j => by`. Establish `h1` using `vmap_mem_eigW hF0 (τ q0) (hMt i j)`. Establish `h2` using `vmap_rel v0 (vi i) (Γ.C.v i).valuationSubring.subtype _ (hsq i) (φ' i) (ψ' i) (lam' i) (xs (qi i) j) (Mt i j) (xs q0)`. Rewrite using `[hφ i, hψ i, hlam i]`. Conclude with `h2 ▸ h1`.

Take `⟨hne, hfin, hsum⟩` from `GlobalTheory.T.valuation_bounded_frame E Γ.κ Γ.C p d r F χ (GlobalTheory.T.charpoly_splits_of_embeddings E Ω O Γ.κ (v0.comp ((GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q0).symm.toRingHom.comp ((algebraMap O Ω).codRestrict (regAt ξ q0) (hreg q0)))) hinj hcard hrange) …`. Establish `hNdet : ∀ i, (N i).det = v0 (Mt i).det` using `fun i => (RingHom.map_det v0 (Mt i)).symm`. Establish `hAdet : ∀ i, (A (qi i)).det = genMap ξ q0 (Mt i).det * (A q0).det` using `fun i => by`. Rewrite using `[hAM i, Matrix.det_mul]`. Conclude with `congrArg (· * (A q0).det) (RingHom.map_det (genMap ξ q0) (Mt i)).symm`.

Establish `hunit : ∀ i, IsUnit (Mt i).det` using `fun i => by`. Establish `h1 : IsUnit (v0 (Mt i).det)` using `isUnit_iff_ne_zero.2 (hNdet i ▸ hne i)`. Use `haveI : IsLocalHom v0 := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo Γ.η).hom)`. Conclude with `(isUnit_map_iff v0 _).1 h1`. Use `⟨(A q0).det, fun i => (A (qi i)).det, fun i => ((N i).det)⁻¹, hdet q0, fun i => ⟨FibreCurve.z_spec Γ i, hdet (qi i)⟩, fun i => ⟨inv_ne_zero (hne i), ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨w, hw⟩` from `hunit i`. Establish `hw0 : genMap ξ q0 (w : X.presheaf.stalk q0.1) * genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hv0 : v0 (w : X.presheaf.stalk q0.1) * v0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Use `⟨Γ.η_spec, ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1), ?_, ?_⟩` and prove the remaining obligations. Establish `e0` using `(hdet q0).1`. Establish `e1 : (A (qi i)).det = genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det` using `(hAdet i).trans (congrArg (fun z => genMap ξ q0 z * (A q0).det) hw.symm)`. Establish `e2 : genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = (A q0).det / (genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det)`. Generalize the expression as in `genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = b at hw0`.

Generalize the expression as in `genMap ξ q0 (w : X.presheaf.stalk q0.1) = a at hw0`. Establish `ha : a ≠ 0` using `left_ne_zero_of_mul_eq_one hw0`. Rewrite using `[eq_div_iff (mul_ne_zero ha e0)]`. Take the linear combination `(A q0).det * hw0`. Conclude with `e2.trans (congrArg ((A q0).det / ·) e1.symm)`.

Establish `e3 : (N i).det = v0 (w : X.presheaf.stalk q0.1)` using `(hNdet i).trans (congrArg v0 hw.symm)`. Conclude with `(eq_inv_of_mul_eq_one_right hv0).trans (congrArg (·⁻¹) e3.symm)`. Use `hfin.subset fun i hi h1 => hi ?_` and prove the remaining obligations. Rewrite using `[map_inv₀, h1, inv_one]`. Establish `: ∀ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i ((N i).det)⁻¹)) = (Γ.C.w i : ℤ) * WithZero.log (Γ.C.v i (N i).det)` using `fun i => by`.

Rewrite using `[map_inv₀, WithZero.log_inv, neg_neg]`. Simplify using `only [this]`. Conclude with `hsum`.
-/
theorem germ_degZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Sp O) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : O) (p : ℕ) (σ : E →+* Ω), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → ξ ≫ s = spMap (algebraMap O Ω) → IsCptGen ξ → PowFns t → S.Gives 𝓗 → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → 𝓗.DegZero σ (algebraMap O Ω ϖ) := by
  intro E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ 𝓗 O _ _ _ _ s _ _ ϖ p σ hϖ hp hdvd hs hξ hpow hgive hfib hcard hrange
    u hu hsp Γ
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (algebraMap O Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
    have h1 : algebraMap O Ω ϖ ^ n = 0 := by rw [← map_pow, ← hw, map_mul, hx, zero_mul]
    have h0 : algebraMap O Ω ϖ = 0 := (pow_eq_zero_iff (fun hn => by simp [hn] at h1)).1 h1
    obtain ⟨c, hc⟩ := hdvd
    have h2 := congrArg (algebraMap O Ω) hc
    rw [map_natCast, map_mul, h0, zero_mul] at h2
    exact hp.ne_zero (by exact_mod_cast h2)
  have hreg := GlobalTheory.T.base_constants_regular X Ω ξ O s hs
  have hσ : ∀ (q : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ q := fun q a => by
    obtain ⟨o, ho⟩ := hrange σ a
    exact ho ▸ hreg q o
  let τ : ∀ q : Cpt ξ, 𝓞 E →+* X.presheaf.stalk q.1 := fun q =>
    (GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q).symm.toRingHom.comp
      ((σ.comp (algebraMap (𝓞 E) E)).codRestrict (regAt ξ q) (hσ q))
  have hτ : ∀ (q : Cpt ξ) (a : 𝓞 E), genMap ξ q (τ q a) = σ (a : E) := fun q a => by
    have := GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv_coe ξ hξ q (τ q a)
    rw [← this]
    simp [τ]
  let q0 : Cpt ξ := ⟨centre Γ.η, Γ.η_spec⟩
  let qi : Γ.C.I → Cpt ξ := fun i => ⟨centre (Γ.z i), FibreCurve.z_spec Γ i⟩
  let v0 : X.presheaf.stalk q0.1 →+* Γ.κ := (Scheme.stalkClosedPointTo Γ.η).hom
  let vi : ∀ i, X.presheaf.stalk (qi i).1 →+* (Γ.C.v i).valuationSubring :=
    fun i => (Scheme.stalkClosedPointTo (Γ.z i)).hom
  have hpκ : (p : Γ.κ) = 0 := by
    obtain ⟨hh, s0, hs0, hs1⟩ := Γ.η_zero
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨c', hc'⟩ := hreg q0 c
    have e : (p : X.presheaf.stalk q0.1) = s0 * c' := hξ.inj q0 (by
      have h2 := congrArg (algebraMap O Ω) hc
      rw [map_natCast, map_mul] at h2
      rw [map_natCast, map_mul, h2, hc']
      exact congrArg (· * algebraMap O Ω c) hs0.symm)
    have h3 := congrArg v0 e
    rw [map_natCast, map_mul] at h3
    rw [h3]
    have h4 : v0 s0 = 0 := hs1
    rw [h4, zero_mul]
  haveI : CharP Γ.κ p := (CharP.charP_iff_prime_eq_zero hp).2 hpκ
  obtain ⟨F, hF0, hFi⟩ := GlobalTheory.T.fibre_curve_germ_powers E H hstar X t Ω ξ d M S O s _ p Γ hξ hpow hfib
  choose hFB φ' ψ' lam' he hφ hψ hlam using hFi
  choose xs A hxs hfr hpr using GlobalTheory.T.hodge_lattice_germ_eigen E H X t Ω ξ d r M S ρ 𝓗 σ u hξ hgive hσ hu hsp
  have hdet := fun q => (GlobalTheory.T.hodge_lattice_span_independent X Ω ξ E (Fin d → Ω) M.lat ρ H.bar r 𝓗 σ u hσ hu hsp).2.2 q (A q) (hfr q)
  choose Mt hAM hMt using fun i => exists_trans S hgive σ (qi i) q0 (FibreCurve.generic_centre_specializes Γ i) (τ q0) (hτ q0)
    (he i) (hxs q0) hu (hpr (qi i)) (hpr q0)
  let χ : 𝓞 E →+* Γ.κ := v0.comp (τ q0)
  have hsq : ∀ i, ((Γ.C.v i).valuationSubring.subtype).comp (vi i) =
      v0.comp (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom := fun i => by
    have key := ProjectiveLinePlaces.stalk_square (FibreCurve.generic_centre_specializes Γ i) (Scheme.stalkClosedPointTo (Γ.z i))
      (Scheme.stalkClosedPointTo Γ.η) (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype)
      ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk Γ.η).trans ((Γ.z_gen i).symm.trans
        (congrArg (Spec.map (CommRingCat.ofHom (Γ.C.v i).valuationSubring.subtype) ≫ ·)
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (Γ.z i))).symm))
    exact RingHom.ext fun s => (congrArg (fun g => g.hom s) key).symm
  have hτs : ∀ i a, (X.presheaf.stalkSpecializes (FibreCurve.generic_centre_specializes Γ i)).hom (τ (qi i) a) = τ q0 a :=
    fun i a => hξ.inj q0 ((ProjectiveLinePlaces.genMap_specializes (FibreCurve.generic_centre_specializes Γ i) q0.2 (qi i).2 _).trans
      ((hτ (qi i) a).trans (hτ q0 a).symm))
  have hχ : ∀ i a, Γ.C.v i (χ a) ≤ 1 := fun i a => by
    have e : χ a = ((vi i (τ (qi i) a) : (Γ.C.v i).valuationSubring) : Γ.κ) :=
      (congrArg v0 (hτs i a).symm).trans (RingHom.congr_fun (hsq i) (τ (qi i) a)).symm
    rw [e]
    exact (vi i (τ (qi i) a)).2
  let x₀ : Fin r → (Fin d → Γ.κ) × (Fin d → Γ.κ) := fun l => vmap v0 (xs q0 l)
  let x : ∀ i : Γ.C.I, Fin r → (Fin d → (Γ.C.v i).valuationSubring) × (Fin d → (Γ.C.v i).valuationSubring) :=
    fun i j => vmap (vi i) (xs (qi i) j)
  let N : Γ.C.I → Matrix (Fin r) (Fin r) Γ.κ := fun i => (Mt i).map v0
  have hx₀ : IsHBasis F.B x₀ := GlobalTheory.T.intersection_second E _ _ v0 d r _ _ _ hF0 (hxs q0)
  have hx : ∀ i, IsHBasis (F.Bi i) (x i) := fun i => GlobalTheory.T.intersection_second E _ _ (vi i) d r _ _ _ (hFB i) (hxs (qi i))
  have hrel : ∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (Γ.C.v i).valuationSubring.subtype (x i j)) -
      ∑ l, N i j l • x₀ l ∈ eigW F.B χ := fun i j => by
    have h1 := vmap_mem_eigW hF0 (τ q0) (hMt i j)
    have h2 := vmap_rel v0 (vi i) (Γ.C.v i).valuationSubring.subtype _ (hsq i) (φ' i) (ψ' i) (lam' i)
      (xs (qi i) j) (Mt i j) (xs q0)
    rw [hφ i, hψ i, hlam i]
    exact h2 ▸ h1
  obtain ⟨hne, hfin, hsum⟩ := GlobalTheory.T.valuation_bounded_frame E Γ.κ Γ.C p d r F χ
    (GlobalTheory.T.charpoly_splits_of_embeddings E Ω O Γ.κ (v0.comp ((GlobalTheory.CompanionTheory.Ar.ValHom.stalkEquiv ξ hξ q0).symm.toRingHom.comp
      ((algebraMap O Ω).codRestrict (regAt ξ q0) (hreg q0)))) hinj hcard hrange) hχ x₀ x N hx₀ hx hrel
  have hNdet : ∀ i, (N i).det = v0 (Mt i).det := fun i => (RingHom.map_det v0 (Mt i)).symm
  have hAdet : ∀ i, (A (qi i)).det = genMap ξ q0 (Mt i).det * (A q0).det := fun i => by
    rw [hAM i, Matrix.det_mul]
    exact congrArg (· * (A q0).det) (RingHom.map_det (genMap ξ q0) (Mt i)).symm
  have hunit : ∀ i, IsUnit (Mt i).det := fun i => by
    have h1 : IsUnit (v0 (Mt i).det) := isUnit_iff_ne_zero.2 (hNdet i ▸ hne i)
    haveI : IsLocalHom v0 := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo Γ.η).hom)
    exact (isUnit_map_iff v0 _).1 h1
  refine ⟨(A q0).det, fun i => (A (qi i)).det, fun i => ((N i).det)⁻¹, hdet q0,
    fun i => ⟨FibreCurve.z_spec Γ i, hdet (qi i)⟩, fun i => ⟨inv_ne_zero (hne i), ?_⟩, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hunit i
    have hw0 : genMap ξ q0 (w : X.presheaf.stalk q0.1) * genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hv0 : v0 (w : X.presheaf.stalk q0.1) * v0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨Γ.η_spec, ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1), ?_, ?_⟩
    · have e0 := (hdet q0).1
      have e1 : (A (qi i)).det = genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det :=
        (hAdet i).trans (congrArg (fun z => genMap ξ q0 z * (A q0).det) hw.symm)
      have e2 : genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) =
          (A q0).det / (genMap ξ q0 (w : X.presheaf.stalk q0.1) * (A q0).det) := by
        generalize genMap ξ q0 ((w⁻¹ : _ˣ) : X.presheaf.stalk q0.1) = b at hw0
        generalize genMap ξ q0 (w : X.presheaf.stalk q0.1) = a at hw0
        have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hw0
        rw [eq_div_iff (mul_ne_zero ha e0)]
        linear_combination (A q0).det * hw0
      exact e2.trans (congrArg ((A q0).det / ·) e1.symm)
    · have e3 : (N i).det = v0 (w : X.presheaf.stalk q0.1) := (hNdet i).trans (congrArg v0 hw.symm)
      exact (eq_inv_of_mul_eq_one_right hv0).trans (congrArg (·⁻¹) e3.symm)
  · refine hfin.subset fun i hi h1 => hi ?_
    rw [map_inv₀, h1, inv_one]
  · have : ∀ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i ((N i).det)⁻¹)) =
        (Γ.C.w i : ℤ) * WithZero.log (Γ.C.v i (N i).det) := fun i => by
      rw [map_inv₀, WithZero.log_inv, neg_neg]
    simp only [this]
    exact hsum

end GlobalTheory.CompanionTheory.Ar.Flat
