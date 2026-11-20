import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsConstOfCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.DifferentiableOnFamPtAffine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.ArtinKernel

open GlobalTheory.TangentOrigin

section Main

variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]

/- English proof (translation)
Take `⟨lam, ⟨i₀, hi₀⟩, hlam⟩` from `exists_functional (fun i => s i - algebraMap ℂ R (ρ (s i))) (by obtain ⟨i, hi⟩ := hs; exact ⟨i, sub_ne_zero.2 hi⟩)`. Establish `hm : ∀ r : R, r - algebraMap ℂ R (ρ r) ∈ IsLocalRing.maximalIdeal R` using `fun r => hρ _ (by rw [map_sub, AlgHom.commutes]; simp)`. Establish `hkey : ∀ i r, lam (r * s i) = ρ r * (lam (s i) - ρ (s i) * lam 1) + ρ (s i) * lam r`. Introduce `i r`. Establish `h` using `hlam i _ (hm r)`.

Use `beta_reduce at h`. Rewrite `h` using `[sub_mul, map_sub, sub_eq_zero, Algebra.algebraMap_eq_smul_one (ρ r), smul_mul_assoc, _root_.one_mul, map_smul, smul_eq_mul]`. Establish `e1 : r * s i = r * (s i - algebraMap ℂ R (ρ (s i))) + ρ (s i) • r`. Rewrite using `[Algebra.algebraMap_eq_smul_one, mul_sub, mul_smul_comm, _root_.mul_one]`. Normalize the expressions using the abelian group laws.

Establish `e3 : lam (s i - algebraMap ℂ R (ρ (s i))) = lam (s i) - ρ (s i) * lam 1`. Rewrite using `[map_sub, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]`. Rewrite using `[e1, map_add, h, e3, map_smul, smul_eq_mul]`. Use `⟨lam - lam 1 • ρ.toLinearMap, by simp, ⟨i₀, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : (lam - lam 1 • ρ.toLinearMap) (s i₀) = lam (s i₀ - algebraMap ℂ R (ρ (s i₀)))`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul, map_sub, Algebra.algebraMap_eq_smul_one, map_smul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hi₀`. Introduce `i r`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]`. Rewrite using `[hkey]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_derivation (ρ : R →ₐ[ℂ] ℂ) (hρ : ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R)
    {J : Type*} (s : J → R) (hs : ∃ i, s i ≠ algebraMap ℂ R (ρ (s i))) :
    ∃ κ : R →ₗ[ℂ] ℂ, κ 1 = 0 ∧ (∃ i, κ (s i) ≠ 0) ∧
      ∀ i r, κ (r * s i) = ρ r * κ (s i) + ρ (s i) * κ r := by
  obtain ⟨lam, ⟨i₀, hi₀⟩, hlam⟩ := exists_functional (fun i => s i - algebraMap ℂ R (ρ (s i)))
    (by obtain ⟨i, hi⟩ := hs; exact ⟨i, sub_ne_zero.2 hi⟩)
  have hm : ∀ r : R, r - algebraMap ℂ R (ρ r) ∈ IsLocalRing.maximalIdeal R := fun r =>
    hρ _ (by rw [map_sub, AlgHom.commutes]; simp)
  have hkey : ∀ i r, lam (r * s i) = ρ r * (lam (s i) - ρ (s i) * lam 1) + ρ (s i) * lam r := by
    intro i r
    have h := hlam i _ (hm r)
    beta_reduce at h
    rw [sub_mul, map_sub, sub_eq_zero, Algebra.algebraMap_eq_smul_one (ρ r), smul_mul_assoc, _root_.one_mul,
      map_smul, smul_eq_mul] at h
    have e1 : r * s i = r * (s i - algebraMap ℂ R (ρ (s i))) + ρ (s i) • r := by
      rw [Algebra.algebraMap_eq_smul_one, mul_sub, mul_smul_comm, _root_.mul_one]
      abel
    have e3 : lam (s i - algebraMap ℂ R (ρ (s i))) = lam (s i) - ρ (s i) * lam 1 := by
      rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    rw [e1, map_add, h, e3, map_smul, smul_eq_mul]
  refine ⟨lam - lam 1 • ρ.toLinearMap, by simp, ⟨i₀, ?_⟩, ?_⟩
  · have e : (lam - lam 1 • ρ.toLinearMap) (s i₀) = lam (s i₀ - algebraMap ℂ R (ρ (s i₀))) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
        map_sub, Algebra.algebraMap_eq_smul_one, map_smul]
      ring
    rw [e]
    exact hi₀
  · intro i r
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
    rw [hkey]
    ring

omit [IsLocalRing R] [Module.Finite ℂ R] in

def jetOf {B : Type} [CommRing B] (ρ : R →ₐ[ℂ] ℂ) (κ : R →ₗ[ℂ] ℂ) (h1 : κ 1 = 0) (e : B →+* R)
    (h : ∀ f r, κ (r * e f) = ρ r * κ (e f) + ρ (e f) * κ r) : B →+* DualNumber ℂ where
  toFun f := (ρ (e f), κ (e f))
  map_one' := TrivSqZeroExt.ext (by change ρ (e 1) = 1; simp) (by change κ (e 1) = 0; simp [h1])
  map_zero' := TrivSqZeroExt.ext (by change ρ (e 0) = 0; simp) (by change κ (e 0) = 0; simp)
  map_add' f f' := TrivSqZeroExt.ext (by change ρ (e (f + f')) = ρ (e f) + ρ (e f'); simp)
    (by change κ (e (f + f')) = κ (e f) + κ (e f'); simp)
  map_mul' f f' := TrivSqZeroExt.ext (by change ρ (e (f * f')) = ρ (e f) * ρ (e f'); simp) (by
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    change κ (e (f * f')) = ρ (e f) * κ (e f') + κ (e f) * ρ (e f')
    rw [map_mul, h, mul_comm (ρ (e f'))])

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

/- English proof (translation)
Establish `hsub` using `subsingleton_primeSpectrum (R := R)`. Establish `hy : spMap ρ.toRingHom ≫ x.left = (u.ex 0).left`. Rewrite using `[← resPt_left, ← Over.comp_left, hx]`. Establish `hmem : ∀ W : A.left.Opens, ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W → ⊤ ≤ x.left ⁻¹ᵁ W` using `fun W hW => (top_le_iff_residue ρ.toRingHom x.left _ hy W).2 hW`. Establish `hres : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)), ρ (evalPt (R` using `R) x.left W h f) = valAt' (u.ex 0).left W f := fun W h f => residue_evalPt ρ.toRingHom x.left _ hy W h f`.

Set `J` to `{q : Σ W : A.left.Opens, Γ(A.left, W) // ⊤ ≤ x.left ⁻¹ᵁ q.1}`. Set `s : J → R` to `fun q => evalPt (R := R) x.left q.1.1 q.2 q.1.2`. Establish `hxU` using `hmem U h0`. Establish `hs : ∃ q : J, s q ≠ algebraMap ℂ R (ρ (s q))`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Apply `hx1` to reduce the goal to its premises. Establish `e : evalPt (R` using `R) x.left U hxU = evalPt (R := R) (toUnit (spO R) ≫ u.ex 0).left U (top_le_const (R := R) (u.ex 0) U h0) := by`. Use extensionality with `f`. Rewrite using `[evalPt_const (u.ex 0) U _ h0, ← hres U hxU f]`.

Conclude with `hcon ⟨⟨U, f⟩, hxU⟩`. Establish `e2` using `ext_evalPt hU hxU _ e`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[e2, ex_zero u, MonObj.comp_one]`. Take `⟨κ, hκ1, hκne, hκ⟩` from `exists_derivation ρ hρ s hs`.

Set `w : Fin g → ℂ` to `fun i => κ (evalPt (R := R) x.left U hxU (t i))`. Establish `core : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)), κ (evalPt (R` using `R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w := by`. Introduce `W h f`. Establish `hW0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W` using `(top_le_iff_residue ρ.toRingHom x.left _ hy W).1 h`. Choose the witnesses or unpack the hypotheses as in `⟨V, hVaff, hV0, hVle⟩ : ∃ V : A.left.Opens, IsAffineOpen V ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V ∧ V ≤ W ⊓ U := by`.

Establish `hpt : (u.ex 0).left (default : PrimeSpectrum ℂ) ∈ W ⊓ U` using `⟨hW0 trivial, h0 trivial⟩`. Take `⟨V, hV, hpV, hVle⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens A.left)) hpt`. Use `⟨V, hV, fun q _ => ?_, hVle⟩` and prove the remaining obligations. Establish `hq : q = (default : PrimeSpectrum ℂ)` using `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`. Rewrite using `[hq]`.

Conclude with `hpV`. Establish `hVW : V ≤ W` using `hVle.trans inf_le_left`. Establish `hVU : V ≤ U` using `hVle.trans inf_le_right`. Establish `hxV` using `hmem V hV0`. Set `ψ` to `evalPt (R := R) x.left V hxV`.

Establish `hL : ∀ f r, κ (r * ψ f) = ρ r * κ (ψ f) + ρ (ψ f) * κ r` using `fun f r => hκ ⟨⟨V, f⟩, hxV⟩ r`. Take `⟨v0, hv0, hv0e⟩` from `exists_evalPt_eq hVaff (jetOf ρ κ hκ1 ψ hL)`. Establish `hc : ∀ a : ℂ, ψ (constFn A.hom V a) = algebraMap ℂ R a`. Introduce `a`. Establish `hxw : x.left ≫ A.hom = spMap (algebraMap ℂ R)` using `Over.w x`.

Use `show evalPt (R := R) x.left V hxV (constFn A.hom V a) = _`. Rewrite using `[evalPt_constFn A.hom x.left V hxV a, evalPt_congr hxw ⊤ le_rfl le_rfl, evalPt_spMap]`. Establish `hv0w : v0 ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ))`. Apply `eq_spMap_of_evalPt` to reduce the goal to its premises. Introduce `a`.

Rewrite using `[← evalPt_constFn A.hom v0 V hv0 a, hv0e]`. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ρ (ψ (constFn A.hom V a)) = _`. Rewrite using `[hc, AlgHom.commutes]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `κ (ψ (constFn A.hom V a)) = _`. Rewrite using `[hc, Algebra.algebraMap_eq_smul_one, map_smul, hκ1, smul_zero]`. Both sides reduce to the same expression. Set `v : epsR ℂ ⟶ A` to `Over.homMk v0 hv0w`. Establish `hvt : IsTangent v` using `by show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v0 = η[A].left`.

Rewrite using `[← ex_zero_left u]`. Establish `hh : ⊤ ≤ (spMap fstC ≫ v0) ⁻¹ᵁ V` using `(top_le_preimage_iff v0 V).1 hv0`. Apply `ext_evalPt hVaff hh hV0` to reduce the goal to its premises. Use extensionality with `f`. Rewrite using `[evalPt_spMap_comp fstC v0 V hv0 hh, hv0e, ← valAt'_eq_evalPt _ _ hV0, ← hres V hxV f]`.

Both sides reduce to the same expression. Take `⟨wV, hwV, -⟩` from `(tangent_bijection A L g u ⟨U, t, hU, h0, huniq, ht⟩).1 v hvt`. Establish `hv0V : ⊤ ≤ v.left ⁻¹ᵁ V` using `hv0`. Establish `hjet` using `(isDiff_iff hvt hVaff hv0V hV0 wV).1 hwV`. Establish `hV : ∀ f' : Γ(A.left, V), κ (ψ f') = fderiv ℂ (fun z => valAt' (u.ex z).left V f') 0 wV`.

Introduce `f'`. Establish `e1 : (evalPt v0 V hv0 f').snd = κ (ψ f')`. Rewrite using `[hv0e]`. Both sides reduce to the same expression. Rewrite using `[← e1, show evalPt v0 V hv0 = evalPt v.left V hv0V from rfl, hjet, jet_snd]`.

Establish `hw : wV = w`. Use function extensionality and compare the values at `i`. Establish `e2` using `hV (resG A.left hVU (t i))`. Establish `e3 : ψ (resG A.left hVU (t i)) = evalPt (R` using `R) x.left U hxU (t i) := evalPt_res x.left hVU hxU hxV (t i)`. Rewrite `e2` using `[e3, fderiv_val_res u hVU h0 hV0 (t i)]`.

Establish `hd : HasFDerivAt (fun z => valAt' (u.ex z).left U (t i)) ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.id ℂ (Fin g → ℂ))) 0` using `hasFDerivAt_pi'.1 ht i`. Rewrite `e2` using `[hd.fderiv]`. Simplify using `using e2.symm`. Use `show κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w`. Rewrite using `[← evalPt_res x.left hVW h hxV f, ← fderiv_val_res u hVW hW0 hV0 f, ← hw]`.

Conclude with `hV _`. Use `⟨κ, w, hκ1, ?_, fun W h f => ⟨fun r => hκ ⟨⟨W, f⟩, h⟩ r, core W h f⟩⟩` and prove the remaining obligations. Introduce `hw0`. Take `⟨q, hq⟩` from `hκne`. Apply `hq` to reduce the goal to its premises.

Establish `h5` using `core q.1.1 q.2 q.1.2`. Rewrite `h5` using `[hw0, ContinuousLinearMap.map_zero]`. Conclude with `h5`.
-/
theorem exists_first_order (ρ : R →ₐ[ℂ] ℂ) (hρ : ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R)
    {U : A.left.Opens} {t : Fin g → Γ(A.left, U)} (hU : IsAffineOpen U) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U)
    (huniq : ∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) →
      (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) →
      (∀ i, D (t i) = 0) → D = 0)
    (ht : HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0)
    (x : spO R ⟶ A) (hx : resPt ρ ≫ x = u.ex 0) (hx1 : x ≠ 1) :
    ∃ (κ : R →ₗ[ℂ] ℂ) (w : Fin g → ℂ), κ 1 = 0 ∧ w ≠ 0 ∧
      ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
        (∀ r, κ (r * evalPt (R := R) x.left W h f) =
          ρ r * κ (evalPt (R := R) x.left W h f) + ρ (evalPt (R := R) x.left W h f) * κ r) ∧
        κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w := by
  classical
  have hsub := subsingleton_primeSpectrum (R := R)
  have hy : spMap ρ.toRingHom ≫ x.left = (u.ex 0).left := by
    rw [← resPt_left, ← Over.comp_left, hx]
  have hmem : ∀ W : A.left.Opens, ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W → ⊤ ≤ x.left ⁻¹ᵁ W := fun W hW =>
    (top_le_iff_residue ρ.toRingHom x.left _ hy W).2 hW
  have hres : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
      ρ (evalPt (R := R) x.left W h f) = valAt' (u.ex 0).left W f := fun W h f =>
    residue_evalPt ρ.toRingHom x.left _ hy W h f
  let J := {q : Σ W : A.left.Opens, Γ(A.left, W) // ⊤ ≤ x.left ⁻¹ᵁ q.1}
  let s : J → R := fun q => evalPt (R := R) x.left q.1.1 q.2 q.1.2
  have hxU := hmem U h0
  have hs : ∃ q : J, s q ≠ algebraMap ℂ R (ρ (s q)) := by
    by_contra hcon
    push Not at hcon
    apply hx1
    have e : evalPt (R := R) x.left U hxU =
        evalPt (R := R) (toUnit (spO R) ≫ u.ex 0).left U (top_le_const (R := R) (u.ex 0) U h0) := by
      ext f
      rw [evalPt_const (u.ex 0) U _ h0, ← hres U hxU f]
      exact hcon ⟨⟨U, f⟩, hxU⟩
    have e2 := ext_evalPt hU hxU _ e
    apply Over.OverMorphism.ext
    rw [e2, ex_zero u, MonObj.comp_one]
  obtain ⟨κ, hκ1, hκne, hκ⟩ := exists_derivation ρ hρ s hs
  let w : Fin g → ℂ := fun i => κ (evalPt (R := R) x.left U hxU (t i))
  have core : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
      κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w := by
    intro W h f
    have hW0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W := (top_le_iff_residue ρ.toRingHom x.left _ hy W).1 h
    obtain ⟨V, hVaff, hV0, hVle⟩ : ∃ V : A.left.Opens, IsAffineOpen V ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V ∧
        V ≤ W ⊓ U := by
      have hpt : (u.ex 0).left (default : PrimeSpectrum ℂ) ∈ W ⊓ U := ⟨hW0 trivial, h0 trivial⟩
      obtain ⟨V, hV, hpV, hVle⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens A.left)) hpt
      refine ⟨V, hV, fun q _ => ?_, hVle⟩
      have hq : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      rw [hq]
      exact hpV
    have hVW : V ≤ W := hVle.trans inf_le_left
    have hVU : V ≤ U := hVle.trans inf_le_right
    have hxV := hmem V hV0
    let ψ := evalPt (R := R) x.left V hxV
    have hL : ∀ f r, κ (r * ψ f) = ρ r * κ (ψ f) + ρ (ψ f) * κ r := fun f r => hκ ⟨⟨V, f⟩, hxV⟩ r
    obtain ⟨v0, hv0, hv0e⟩ := exists_evalPt_eq hVaff (jetOf ρ κ hκ1 ψ hL)
    have hc : ∀ a : ℂ, ψ (constFn A.hom V a) = algebraMap ℂ R a := by
      intro a
      have hxw : x.left ≫ A.hom = spMap (algebraMap ℂ R) := Over.w x
      show evalPt (R := R) x.left V hxV (constFn A.hom V a) = _
      rw [evalPt_constFn A.hom x.left V hxV a, evalPt_congr hxw ⊤ le_rfl le_rfl, evalPt_spMap]
    have hv0w : v0 ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
      apply eq_spMap_of_evalPt
      intro a
      rw [← evalPt_constFn A.hom v0 V hv0 a, hv0e]
      refine TrivSqZeroExt.ext ?_ ?_
      · change ρ (ψ (constFn A.hom V a)) = _
        rw [hc, AlgHom.commutes]
        rfl
      · change κ (ψ (constFn A.hom V a)) = _
        rw [hc, Algebra.algebraMap_eq_smul_one, map_smul, hκ1, smul_zero]
        rfl
    let v : epsR ℂ ⟶ A := Over.homMk v0 hv0w
    have hvt : IsTangent v := by
      show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v0 = η[A].left
      rw [← ex_zero_left u]
      have hh : ⊤ ≤ (spMap fstC ≫ v0) ⁻¹ᵁ V := (top_le_preimage_iff v0 V).1 hv0
      apply ext_evalPt hVaff hh hV0
      ext f
      rw [evalPt_spMap_comp fstC v0 V hv0 hh, hv0e, ← valAt'_eq_evalPt _ _ hV0, ← hres V hxV f]
      rfl
    obtain ⟨wV, hwV, -⟩ := (tangent_bijection A L g u ⟨U, t, hU, h0, huniq, ht⟩).1 v hvt
    have hv0V : ⊤ ≤ v.left ⁻¹ᵁ V := hv0
    have hjet := (isDiff_iff hvt hVaff hv0V hV0 wV).1 hwV
    have hV : ∀ f' : Γ(A.left, V), κ (ψ f') = fderiv ℂ (fun z => valAt' (u.ex z).left V f') 0 wV := by
      intro f'
      have e1 : (evalPt v0 V hv0 f').snd = κ (ψ f') := by
        rw [hv0e]
        rfl
      rw [← e1, show evalPt v0 V hv0 = evalPt v.left V hv0V from rfl, hjet, jet_snd]
    have hw : wV = w := by
      funext i
      have e2 := hV (resG A.left hVU (t i))
      have e3 : ψ (resG A.left hVU (t i)) = evalPt (R := R) x.left U hxU (t i) :=
        evalPt_res x.left hVU hxU hxV (t i)
      rw [e3, fderiv_val_res u hVU h0 hV0 (t i)] at e2
      have hd : HasFDerivAt (fun z => valAt' (u.ex z).left U (t i))
          ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.id ℂ (Fin g → ℂ))) 0 :=
        hasFDerivAt_pi'.1 ht i
      rw [hd.fderiv] at e2
      simpa using e2.symm
    show κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w
    rw [← evalPt_res x.left hVW h hxV f, ← fderiv_val_res u hVW hW0 hV0 f, ← hw]
    exact hV _
  refine ⟨κ, w, hκ1, ?_, fun W h f => ⟨fun r => hκ ⟨⟨W, f⟩, h⟩ r, core W h f⟩⟩
  intro hw0
  obtain ⟨q, hq⟩ := hκne
  apply hq
  have h5 := core q.1.1 q.2 q.1.2
  rw [hw0, ContinuousLinearMap.map_zero] at h5
  exact h5

/- English proof (translation)
Rewrite using `[u.ex_add, (u.ker l).2 hl, _root_.mul_one]`.
-/
theorem ex_add_lattice (z : Fin g → ℂ) {l : Fin g → ℂ} (hl : l ∈ u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]

/- English proof (translation)
Take `⟨cover, -, -⟩` from `hL`. Establish `hp : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⊤ : A.left.Opens)` using `trivial`. Rewrite `hp` using `[← cover, TopologicalSpace.Opens.mem_iSup]`. Take `⟨i, hi⟩` from `hp`. Use `⟨i, fun q _ => ?_⟩` and prove the remaining obligations.

Establish `hq : q = (default : PrimeSpectrum ℂ)` using `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`. Rewrite using `[hq]`. Conclude with `hi`.
-/
theorem exists_chart (hL : L.IsLB) (z : Fin g → ℂ) : ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  obtain ⟨cover, -, -⟩ := hL
  have hp : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⊤ : A.left.Opens) := trivial
  rw [← cover, TopologicalSpace.Opens.mem_iSup] at hp
  obtain ⟨i, hi⟩ := hp
  refine ⟨i, fun q _ => ?_⟩
  have hq : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [hq]
  exact hi

/- English proof (translation)
Use `set φ₀ := (lift (fst T A ≫ x) (snd T A) ≫ μ).left with hφ₀`. Use `set φ₁ := (snd T A).left with hφ₁`. Establish `hP0 : ∀ z, (lift p (u.ex z)).left ≫ φ₀ = (u.ex (w + z)).left`. Introduce `z`. Rewrite using `[hφ₀, ← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, ← Hom.mul_def, hw, ← u.ex_add]`.

Establish `hP1 : ∀ z, (lift p (u.ex z)).left ≫ φ₁ = (u.ex z).left`. Introduce `z`. Rewrite using `[hφ₁, ← Over.comp_left, lift_snd]`. Set `O : L.ι → Set (Fin g → ℂ)` to `fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}`. Establish `hO : ∀ i, IsOpen (O i)` using `fun i => (u.hol (L.U i) 0).1`.

Set `D : (Fin 2 → L.ι) → Set (Fin g → ℂ)` to `fun j => {z | ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j}`. Establish `hDmem : ∀ j z, z ∈ D j ↔ w + z ∈ O (j 0) ∧ z ∈ O (j 1)` using `fun j z => GlobalTheory.ThetaGroupFrame.top_le_wchart_two L φ₀ φ₁ j _ _ _ (hP0 z) (hP1 z)`. Establish `hD : ∀ j, IsOpen (D j)`. Introduce `j`. Establish `e : D j = (fun z => w + z) ⁻¹' O (j 0) ∩ O (j 1)`.

Use extensionality with `z`. Conclude with `hDmem j z`. Rewrite using `[e]`. Conclude with `((hO _).preimage (continuous_const.add continuous_id)).inter (hO _)`. Establish `hcov : ∀ z, ∃ j, z ∈ D j`.

Introduce `z`. Take `⟨i₀, h₀⟩` from `exists_chart u hL (w + z)`. Take `⟨i₁, h₁⟩` from `exists_chart u hL z`. Conclude with `⟨![i₀, i₁], (hDmem _ z).2 ⟨h₀, h₁⟩⟩`. Set `cv : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ` to `fun j z => valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val`.

Set `G : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ` to `fun j z => cv j z * u.fr (j 1) z / u.fr (j 0) (w + z)`. Establish `hG : ∀ j, DifferentiableOn ℂ (G j) (D j)`. Introduce `j`. Establish `h1 : DifferentiableOn ℂ (cv j) (D j)` using `hp _ _`. Establish `h2 : DifferentiableOn ℂ (u.fr (j 1)) (D j)` using `(u.fr_hol (j 1)).mono fun z hz => ((hDmem j z).1 hz).2`.

Establish `h3 : DifferentiableOn ℂ (fun z => u.fr (j 0) (w + z)) (D j)` using `(u.fr_hol (j 0)).comp ((differentiableOn_const w).add differentiableOn_id) fun z hz => ((hDmem j z).1 hz).1`. Establish `h4 : DifferentiableOn ℂ (fun z => cv j z * u.fr (j 1) z * (u.fr (j 0) (w + z))⁻¹) (D j)` using `(h1.mul h2).mul (h3.inv fun z hz => u.fr_ne _ _ ((hDmem j z).1 hz).1)`. Simplify `h4` using `only [G, div_eq_mul_inv]`. Establish `hc' : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z`. Introduce `j j' z hz hz'`.

Establish `hz0 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j` using `hz`. Establish `hz1 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j'` using `hz'`. Take `⟨a0, a1⟩` from `(hDmem j z).1 hz`. Take `⟨b0, b1⟩` from `(hDmem j' z).1 hz'`. Establish `i0 : ⊤ ≤ (u.ex (w + z)).left ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j' 0))` using `GlobalTheory.ThetaGroupFrame.top_le_inf _ a0 b0`.

Establish `i1 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j 1) ⊓ L.U (j' 1))` using `GlobalTheory.ThetaGroupFrame.top_le_inf _ a1 b1`. Establish `e : evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val * evalPt (u.ex z).left _ i1 (L.g (j 1) (j' 1)).val = evalPt (u.ex (w + z)).left _ i0 (L.g (j 0) (j' 0)).val * evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') hz1 (c.s j').val` using `evalPt_gen_two L φ₀ φ₁ c hc (lift p (u.ex z)).left _ _ (hP0 z) (hP1 z) j j' hz0 hz1 i0 i1`. Establish `f0` using `u.fr_compat (j 0) (j' 0) (w + z) i0`. Establish `f1` using `u.fr_compat (j 1) (j' 1) z i1`. Rewrite `f0` using `[valAt'_eq_evalPt _ _ i0]`.

Rewrite `f1` using `[valAt'_eq_evalPt _ _ i1]`. Establish `n0` using `u.fr_ne _ _ b0`. Establish `ng : evalPt (u.ex (w + z)).left _ i0 (L.g (j 0) (j' 0)).val ≠ 0`. Introduce `h0`. Establish `h5` using `u.fr_ne _ _ a0`.

Rewrite `h5` using `[f0, h0, zero_mul]`. Conclude with `h5 rfl`. Establish `v0 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val = evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val` using `valAt'_eq_evalPt _ _ hz0 _`. Establish `v1 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') (c.s j').val = evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') hz1 (c.s j').val` using `valAt'_eq_evalPt _ _ hz1 _`. Simplify using `only [G, cv]`.

Rewrite using `[v0, v1, f0, f1, div_eq_div_iff (mul_ne_zero ng n0) n0]`. Take the linear combination `(u.fr (j' 1) z * u.fr (j' 0) (w + z)) * e`. Take `⟨F, hF, hFG⟩` from `exists_glue D G hD hcov hG hc'`. Establish `hne : ∀ z, F z ≠ 0`. Introduce `z`.

Take `⟨j, hz⟩` from `hcov z`. Establish `hz0 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j` using `hz`. Take `⟨a0, a1⟩` from `(hDmem j z).1 hz`. Rewrite using `[hFG j z hz]`. Establish `v0 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val = evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val` using `valAt'_eq_evalPt _ _ hz0 _`.

Simplify using `only [G, cv]`. Rewrite using `[v0]`. Conclude with `div_ne_zero (mul_ne_zero ((c.s j).isUnit.map (evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0)).ne_zero (u.fr_ne _ _ a1)) (u.fr_ne _ _ a0)`. Establish `hper : ∀ (l : u.Λ) z, F (z + l) = cexp (B l w) * F z`. Introduce `l z`.

Take `⟨j, hz⟩` from `hcov z`. Take `⟨a0, a1⟩` from `(hDmem j z).1 hz`. Establish `hl : (l : Fin g → ℂ) ∈ u.Λ` using `l.2`. Establish `ez : u.ex (z + l) = u.ex z` using `ex_add_lattice u z hl`. Establish `ewz : u.ex (w + z + l) = u.ex (w + z)` using `ex_add_lattice u _ hl`.

Establish `hzl : z + l ∈ D j`. Rewrite using `[hDmem]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ⊤ ≤ (u.ex (w + (z + l))).left ⁻¹ᵁ _`. Rewrite using `[← add_assoc, ewz]`.

Conclude with `a0`. Use `show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ _`. Rewrite using `[ez]`. Conclude with `a1`. Establish `n0 : u.fr (j 0) (w + z + l) ≠ 0`.

Apply `u.fr_ne` to reduce the goal to its premises. Use `show ⊤ ≤ (u.ex (w + z + l)).left ⁻¹ᵁ _`. Rewrite using `[ewz]`. Conclude with `a0`. Rewrite using `[hFG j _ hzl, hFG j z hz]`.

Simplify using `only [G, cv]`. Rewrite using `[ez, ← add_assoc]`. Establish `h1` using `hfr l (j 1) z a1`. Establish `h0` using `hfr l (j 0) (w + z) a0`. Rewrite using `[h1, h0, map_add, Complex.exp_add]`.

Establish `hal` using `ha l`. Clear the denominators using the available nonvanishing facts. Take `⟨lam, hlam⟩` from `exists_linear_of_mul_period hF hne (S := (u.Λ : Set (Fin g → ℂ))) u.full (fun l => cexp (B ⟨l.1, l.2⟩ w)) (fun l z => hper ⟨l.1, l.2⟩ z)`. Conclude with `⟨lam, fun l => hlam ⟨l.1, l.2⟩⟩`.
-/
theorem exists_linear_of_gen (hL : L.IsLB) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ)) (ha : ∀ l, a l ≠ 0)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l))
    {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ A) (w : Fin g → ℂ) (hw : p ≫ x = u.ex w)
    (hp : ∀ (V : (T ⊗ A).left.Opens) (f : Γ((T ⊗ A).left, V)),
      DifferentiableOn ℂ (fun z => valAt' (lift p (u.ex z)).left V f) {z | ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ V})
    (c : LB.Gen (Out.translDiff A L x)) (hc : c.IsGen) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : u.Λ, cexp (B l w) = cexp (lam l) := by
  classical
  set φ₀ := (lift (fst T A ≫ x) (snd T A) ≫ μ).left with hφ₀
  set φ₁ := (snd T A).left with hφ₁
  have hP0 : ∀ z, (lift p (u.ex z)).left ≫ φ₀ = (u.ex (w + z)).left := by
    intro z
    rw [hφ₀, ← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, ← Hom.mul_def, hw,
      ← u.ex_add]
  have hP1 : ∀ z, (lift p (u.ex z)).left ≫ φ₁ = (u.ex z).left := by
    intro z
    rw [hφ₁, ← Over.comp_left, lift_snd]
  let O : L.ι → Set (Fin g → ℂ) := fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}
  have hO : ∀ i, IsOpen (O i) := fun i => (u.hol (L.U i) 0).1
  let D : (Fin 2 → L.ι) → Set (Fin g → ℂ) := fun j =>
    {z | ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j}
  have hDmem : ∀ j z, z ∈ D j ↔ w + z ∈ O (j 0) ∧ z ∈ O (j 1) := fun j z =>
    GlobalTheory.ThetaGroupFrame.top_le_wchart_two L φ₀ φ₁ j _ _ _ (hP0 z) (hP1 z)
  have hD : ∀ j, IsOpen (D j) := by
    intro j
    have e : D j = (fun z => w + z) ⁻¹' O (j 0) ∩ O (j 1) := by
      ext z
      exact hDmem j z
    rw [e]
    exact ((hO _).preimage (continuous_const.add continuous_id)).inter (hO _)
  have hcov : ∀ z, ∃ j, z ∈ D j := by
    intro z
    obtain ⟨i₀, h₀⟩ := exists_chart u hL (w + z)
    obtain ⟨i₁, h₁⟩ := exists_chart u hL z
    exact ⟨![i₀, i₁], (hDmem _ z).2 ⟨h₀, h₁⟩⟩
  let cv : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ := fun j z =>
    valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val
  let G : (Fin 2 → L.ι) → (Fin g → ℂ) → ℂ := fun j z => cv j z * u.fr (j 1) z / u.fr (j 0) (w + z)
  have hG : ∀ j, DifferentiableOn ℂ (G j) (D j) := by
    intro j
    have h1 : DifferentiableOn ℂ (cv j) (D j) := hp _ _
    have h2 : DifferentiableOn ℂ (u.fr (j 1)) (D j) :=
      (u.fr_hol (j 1)).mono fun z hz => ((hDmem j z).1 hz).2
    have h3 : DifferentiableOn ℂ (fun z => u.fr (j 0) (w + z)) (D j) :=
      (u.fr_hol (j 0)).comp ((differentiableOn_const w).add differentiableOn_id)
        fun z hz => ((hDmem j z).1 hz).1
    have h4 : DifferentiableOn ℂ (fun z => cv j z * u.fr (j 1) z * (u.fr (j 0) (w + z))⁻¹) (D j) :=
      (h1.mul h2).mul (h3.inv fun z hz => u.fr_ne _ _ ((hDmem j z).1 hz).1)
    simpa only [G, div_eq_mul_inv] using h4
  have hc' : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z := by
    intro j j' z hz hz'
    have hz0 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j := hz
    have hz1 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j' := hz'
    obtain ⟨a0, a1⟩ := (hDmem j z).1 hz
    obtain ⟨b0, b1⟩ := (hDmem j' z).1 hz'
    have i0 : ⊤ ≤ (u.ex (w + z)).left ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j' 0)) :=
      GlobalTheory.ThetaGroupFrame.top_le_inf _ a0 b0
    have i1 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j 1) ⊓ L.U (j' 1)) := GlobalTheory.ThetaGroupFrame.top_le_inf _ a1 b1
    have e : evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val *
          evalPt (u.ex z).left _ i1 (L.g (j 1) (j' 1)).val =
        evalPt (u.ex (w + z)).left _ i0 (L.g (j 0) (j' 0)).val *
          evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') hz1 (c.s j').val :=
      evalPt_gen_two L φ₀ φ₁ c hc (lift p (u.ex z)).left _ _ (hP0 z) (hP1 z) j j' hz0 hz1 i0 i1
    have f0 := u.fr_compat (j 0) (j' 0) (w + z) i0
    have f1 := u.fr_compat (j 1) (j' 1) z i1
    rw [valAt'_eq_evalPt _ _ i0] at f0
    rw [valAt'_eq_evalPt _ _ i1] at f1
    have n0 := u.fr_ne _ _ b0
    have ng : evalPt (u.ex (w + z)).left _ i0 (L.g (j 0) (j' 0)).val ≠ 0 := by
      intro h0
      have h5 := u.fr_ne _ _ a0
      rw [f0, h0, zero_mul] at h5
      exact h5 rfl
    have v0 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val =
        evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val := valAt'_eq_evalPt _ _ hz0 _
    have v1 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') (c.s j').val =
        evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j') hz1 (c.s j').val := valAt'_eq_evalPt _ _ hz1 _
    simp only [G, cv]
    rw [v0, v1, f0, f1, div_eq_div_iff (mul_ne_zero ng n0) n0]
    linear_combination (u.fr (j' 1) z * u.fr (j' 0) (w + z)) * e
  obtain ⟨F, hF, hFG⟩ := exists_glue D G hD hcov hG hc'
  have hne : ∀ z, F z ≠ 0 := by
    intro z
    obtain ⟨j, hz⟩ := hcov z
    have hz0 : ⊤ ≤ (lift p (u.ex z)).left ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j := hz
    obtain ⟨a0, a1⟩ := (hDmem j z).1 hz
    rw [hFG j z hz]
    have v0 : valAt' (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) (c.s j).val =
        evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0 (c.s j).val := valAt'_eq_evalPt _ _ hz0 _
    simp only [G, cv]
    rw [v0]
    exact div_ne_zero (mul_ne_zero ((c.s j).isUnit.map
      (evalPt (lift p (u.ex z)).left (LB.wchart L ![φ₀, φ₁] j) hz0)).ne_zero (u.fr_ne _ _ a1)) (u.fr_ne _ _ a0)
  have hper : ∀ (l : u.Λ) z, F (z + l) = cexp (B l w) * F z := by
    intro l z
    obtain ⟨j, hz⟩ := hcov z
    obtain ⟨a0, a1⟩ := (hDmem j z).1 hz
    have hl : (l : Fin g → ℂ) ∈ u.Λ := l.2
    have ez : u.ex (z + l) = u.ex z := ex_add_lattice u z hl
    have ewz : u.ex (w + z + l) = u.ex (w + z) := ex_add_lattice u _ hl
    have hzl : z + l ∈ D j := by
      rw [hDmem]
      refine ⟨?_, ?_⟩
      · show ⊤ ≤ (u.ex (w + (z + l))).left ⁻¹ᵁ _
        rw [← add_assoc, ewz]
        exact a0
      · show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ _
        rw [ez]
        exact a1
    have n0 : u.fr (j 0) (w + z + l) ≠ 0 := by
      apply u.fr_ne
      show ⊤ ≤ (u.ex (w + z + l)).left ⁻¹ᵁ _
      rw [ewz]
      exact a0
    rw [hFG j _ hzl, hFG j z hz]
    simp only [G, cv]
    rw [ez, ← add_assoc]
    have h1 := hfr l (j 1) z a1
    have h0 := hfr l (j 0) (w + z) a0
    rw [h1, h0, map_add, Complex.exp_add]
    have hal := ha l
    field_simp
  obtain ⟨lam, hlam⟩ := exists_linear_of_mul_period hF hne (S := (u.Λ : Set (Fin g → ℂ))) u.full
    (fun l => cexp (B ⟨l.1, l.2⟩ w)) (fun l z => hper ⟨l.1, l.2⟩ z)
  exact ⟨lam, fun l => hlam ⟨l.1, l.2⟩⟩

/- English proof (translation)
Set `O : L.ι → Set (Fin g → ℂ)` to `fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}`. Establish `hO : ∀ i, IsOpen (O i)` using `fun i => (u.hol (L.U i) 0).1`. Set `d : L.ι → (Fin g → ℂ) → ℂ` to `fun i z => fderiv ℂ (u.fr i) z w`. Establish `hd : ∀ i, DifferentiableOn ℂ (d i) (O i)` using `fun i => GlobalTheory.SCV.differentiableOn_fderiv_apply (hO i) (u.fr_hol i) w`. Set `G : L.ι → (Fin g → ℂ) → ℂ` to `fun i z => d i z / u.fr i z - K i z`.

Establish `hG : ∀ i, DifferentiableOn ℂ (G i) (O i)`. Introduce `i`. Establish `h4 : DifferentiableOn ℂ (fun z => d i z * (u.fr i z)⁻¹ - K i z) (O i)` using `((hd i).mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz)).sub (hK i)`. Simplify `h4` using `only [G, div_eq_mul_inv]`. Establish `hcov : ∀ z, ∃ i, z ∈ O i` using `fun z => exists_chart u hL z`.

Establish `hc : ∀ i i' z, z ∈ O i → z ∈ O i' → G i z = G i' z`. Introduce `i i' z hz hz'`. Set `Gv : (Fin g → ℂ) → ℂ` to `fun y => valAt' (u.ex y).left (L.U i ⊓ L.U i') (L.g i i').val`. Establish `hOii` using `(u.hol (L.U i ⊓ L.U i') (L.g i i').val).1`. Establish `hzii : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i')` using `GlobalTheory.ThetaGroupFrame.top_le_inf _ hz hz'`.

Establish `hGvd : DifferentiableAt ℂ Gv z` using `((u.hol (L.U i ⊓ L.U i') (L.g i i').val).2).differentiableAt (hOii.mem_nhds hzii)`. Establish `hfrd : DifferentiableAt ℂ (u.fr i') z` using `(u.fr_hol i').differentiableAt ((hO i').mem_nhds hz')`. Establish `hev : u.fr i =ᶠ[𝓝 z] fun y => Gv y * u.fr i' y` using `by filter_upwards [hOii.mem_nhds hzii] with y hy`. Conclude with `u.fr_compat i i' y hy`. Establish `hdi : d i z = Gv z * d i' z + u.fr i' z * fderiv ℂ Gv z w` using `by show fderiv ℂ (u.fr i) z w = _`.

Rewrite using `[hev.fderiv_eq, fderiv_fun_mul hGvd hfrd]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression. Establish `hfri : u.fr i z = Gv z * u.fr i' z` using `u.fr_compat i i' z hzii`. Establish `n1 : u.fr i' z ≠ 0` using `u.fr_ne i' z hz'`.

Establish `nG : Gv z ≠ 0`. Introduce `h0`. Establish `h5` using `u.fr_ne i z hz`. Rewrite `h5` using `[hfri, h0, zero_mul]`. Conclude with `h5 rfl`.

Establish `hKc' : Gv z * K i z = fderiv ℂ Gv z w + Gv z * K i' z` using `hKc i i' z hz hz'`. Establish `hKi : K i z = fderiv ℂ Gv z w / Gv z + K i' z`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hKc'`. Simplify using `only [G]`.

Rewrite using `[hdi, hfri, hKi]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨F, hF, hFG⟩` from `exists_glue O G hO hcov hG hc`. Establish `hper' : ∀ (l : u.Λ) z, F (z + l) = F z + -(B l w)`.

Introduce `l z`. Take `⟨i, hz⟩` from `hcov z`. Establish `hl : (l : Fin g → ℂ) ∈ u.Λ` using `l.2`. Establish `hzl : z + l ∈ O i` using `by show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ _`. Rewrite using `[ex_add_lattice u z hl]`.

Conclude with `hz`. Establish `hdl : DifferentiableAt ℂ (u.fr i) (z + l)` using `(u.fr_hol i).differentiableAt ((hO i).mem_nhds hzl)`. Establish `h1 : HasFDerivAt (fun y => a l * cexp (B l y)) ((a l * cexp (B l z)) • (B l).toContinuousLinearMap) z`. Establish `h7` using `((Complex.hasDerivAt_exp (B l z)).comp_hasFDerivAt z (B l).toContinuousLinearMap.hasFDerivAt).const_mul (a l)`. Simplify `h7` using `[smul_smul]`.

Establish `h2 : HasFDerivAt (fun y => u.fr i (y + l)) (fderiv ℂ (u.fr i) (z + l)) z` using `(hasFDerivAt_comp_add_right (l : Fin g → ℂ)).2 hdl.hasFDerivAt`. Establish `h3 : HasFDerivAt (fun y => a l * cexp (B l y) * u.fr i (y + l)) ((a l * cexp (B l z)) • fderiv ℂ (u.fr i) (z + l) + u.fr i (z + l) • ((a l * cexp (B l z)) • (B l).toContinuousLinearMap)) z` using `h1.mul h2`. Establish `hev : u.fr i =ᶠ[𝓝 z] fun y => a l * cexp (B l y) * u.fr i (y + l)` using `by filter_upwards [(hO i).mem_nhds hz] with y hy`. Conclude with `hfr l i y hy`. Establish `hdz : d i z = a l * cexp (B l z) * d i (z + l) + u.fr i (z + l) * (a l * cexp (B l z) * B l w)` using `by show fderiv ℂ (u.fr i) z w = _`.

Rewrite using `[hev.fderiv_eq, h3.fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, LinearMap.coe_toContinuousLinearMap']`. Both sides reduce to the same expression. Establish `n1 : u.fr i (z + l) ≠ 0` using `u.fr_ne i _ hzl`. Establish `hal` using `ha l`.

Rewrite using `[hFG i _ hzl, hFG i z hz]`. Simplify using `only [G]`. Rewrite using `[hdz, hfr l i z hz, ← hper i z l hl]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take `⟨lam, hlam⟩` from `exists_linear_of_add_period hF (S := (u.Λ : Set (Fin g → ℂ))) u.full (fun l => -(B ⟨l.1, l.2⟩ w)) (fun l z => hper' ⟨l.1, l.2⟩ z)`. Use `⟨-lam, fun l => ?_⟩` and prove the remaining obligations. Establish `h6 : -(B l w) = lam l` using `hlam ⟨l.1, l.2⟩`. Rewrite using `[LinearMap.neg_apply, ← h6, neg_neg]`.
-/
theorem exists_linear_of_log_deriv (hL : L.IsLB) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ))
    (ha : ∀ l, a l ≠ 0)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l))
    (w : Fin g → ℂ) (K : L.ι → (Fin g → ℂ) → ℂ)
    (hK : ∀ i, DifferentiableOn ℂ (K i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (hper : ∀ i z, ∀ l ∈ u.Λ, K i (z + l) = K i z)
    (hKc : ∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i' →
      valAt' (u.ex z).left _ (L.g i i').val * K i z =
        fderiv ℂ (fun y => valAt' (u.ex y).left (L.U i ⊓ L.U i') (L.g i i').val) z w +
          valAt' (u.ex z).left _ (L.g i i').val * K i' z) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : u.Λ, B l w = lam l := by
  classical
  let O : L.ι → Set (Fin g → ℂ) := fun i => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}
  have hO : ∀ i, IsOpen (O i) := fun i => (u.hol (L.U i) 0).1
  let d : L.ι → (Fin g → ℂ) → ℂ := fun i z => fderiv ℂ (u.fr i) z w
  have hd : ∀ i, DifferentiableOn ℂ (d i) (O i) := fun i =>
    GlobalTheory.SCV.differentiableOn_fderiv_apply (hO i) (u.fr_hol i) w
  let G : L.ι → (Fin g → ℂ) → ℂ := fun i z => d i z / u.fr i z - K i z
  have hG : ∀ i, DifferentiableOn ℂ (G i) (O i) := by
    intro i
    have h4 : DifferentiableOn ℂ (fun z => d i z * (u.fr i z)⁻¹ - K i z) (O i) :=
      ((hd i).mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz)).sub (hK i)
    simpa only [G, div_eq_mul_inv] using h4
  have hcov : ∀ z, ∃ i, z ∈ O i := fun z => exists_chart u hL z
  have hc : ∀ i i' z, z ∈ O i → z ∈ O i' → G i z = G i' z := by
    intro i i' z hz hz'
    let Gv : (Fin g → ℂ) → ℂ := fun y => valAt' (u.ex y).left (L.U i ⊓ L.U i') (L.g i i').val
    have hOii := (u.hol (L.U i ⊓ L.U i') (L.g i i').val).1
    have hzii : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i') := GlobalTheory.ThetaGroupFrame.top_le_inf _ hz hz'
    have hGvd : DifferentiableAt ℂ Gv z :=
      ((u.hol (L.U i ⊓ L.U i') (L.g i i').val).2).differentiableAt (hOii.mem_nhds hzii)
    have hfrd : DifferentiableAt ℂ (u.fr i') z := (u.fr_hol i').differentiableAt ((hO i').mem_nhds hz')
    have hev : u.fr i =ᶠ[𝓝 z] fun y => Gv y * u.fr i' y := by
      filter_upwards [hOii.mem_nhds hzii] with y hy
      exact u.fr_compat i i' y hy
    have hdi : d i z = Gv z * d i' z + u.fr i' z * fderiv ℂ Gv z w := by
      show fderiv ℂ (u.fr i) z w = _
      rw [hev.fderiv_eq, fderiv_fun_mul hGvd hfrd]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rfl
    have hfri : u.fr i z = Gv z * u.fr i' z := u.fr_compat i i' z hzii
    have n1 : u.fr i' z ≠ 0 := u.fr_ne i' z hz'
    have nG : Gv z ≠ 0 := by
      intro h0
      have h5 := u.fr_ne i z hz
      rw [hfri, h0, zero_mul] at h5
      exact h5 rfl
    have hKc' : Gv z * K i z = fderiv ℂ Gv z w + Gv z * K i' z := hKc i i' z hz hz'
    have hKi : K i z = fderiv ℂ Gv z w / Gv z + K i' z := by
      field_simp
      linear_combination hKc'
    simp only [G]
    rw [hdi, hfri, hKi]
    field_simp
    ring
  obtain ⟨F, hF, hFG⟩ := exists_glue O G hO hcov hG hc
  have hper' : ∀ (l : u.Λ) z, F (z + l) = F z + -(B l w) := by
    intro l z
    obtain ⟨i, hz⟩ := hcov z
    have hl : (l : Fin g → ℂ) ∈ u.Λ := l.2
    have hzl : z + l ∈ O i := by
      show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ _
      rw [ex_add_lattice u z hl]
      exact hz
    have hdl : DifferentiableAt ℂ (u.fr i) (z + l) := (u.fr_hol i).differentiableAt ((hO i).mem_nhds hzl)
    have h1 : HasFDerivAt (fun y => a l * cexp (B l y)) ((a l * cexp (B l z)) • (B l).toContinuousLinearMap) z := by
      have h7 := ((Complex.hasDerivAt_exp (B l z)).comp_hasFDerivAt z
        (B l).toContinuousLinearMap.hasFDerivAt).const_mul (a l)
      simpa [smul_smul] using h7
    have h2 : HasFDerivAt (fun y => u.fr i (y + l)) (fderiv ℂ (u.fr i) (z + l)) z :=
      (hasFDerivAt_comp_add_right (l : Fin g → ℂ)).2 hdl.hasFDerivAt
    have h3 : HasFDerivAt (fun y => a l * cexp (B l y) * u.fr i (y + l))
        ((a l * cexp (B l z)) • fderiv ℂ (u.fr i) (z + l) +
          u.fr i (z + l) • ((a l * cexp (B l z)) • (B l).toContinuousLinearMap)) z := h1.mul h2
    have hev : u.fr i =ᶠ[𝓝 z] fun y => a l * cexp (B l y) * u.fr i (y + l) := by
      filter_upwards [(hO i).mem_nhds hz] with y hy
      exact hfr l i y hy
    have hdz : d i z = a l * cexp (B l z) * d i (z + l) + u.fr i (z + l) * (a l * cexp (B l z) * B l w) := by
      show fderiv ℂ (u.fr i) z w = _
      rw [hev.fderiv_eq, h3.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        LinearMap.coe_toContinuousLinearMap']
      rfl
    have n1 : u.fr i (z + l) ≠ 0 := u.fr_ne i _ hzl
    have hal := ha l
    rw [hFG i _ hzl, hFG i z hz]
    simp only [G]
    rw [hdz, hfr l i z hz, ← hper i z l hl]
    field_simp
    ring
  obtain ⟨lam, hlam⟩ := exists_linear_of_add_period hF (S := (u.Λ : Set (Fin g → ℂ))) u.full
    (fun l => -(B ⟨l.1, l.2⟩ w)) (fun l z => hper' ⟨l.1, l.2⟩ z)
  refine ⟨-lam, fun l => ?_⟩
  have h6 : -(B l w) = lam l := hlam ⟨l.1, l.2⟩
  rw [LinearMap.neg_apply, ← h6, neg_neg]

def translBy (z : Fin g → ℂ) : A ⟶ A := 𝟙 A * (toUnit A ≫ u.ex z)

/- English proof (translation)
Rewrite using `[← Over.comp_left]`. Use `congr 1`. Simplify using `[translBy, comp_mul, u.ex_add]`.
-/
theorem ex_translBy (z y : Fin g → ℂ) : (u.ex y).left ≫ (translBy u z).left = (u.ex (y + z)).left := by
  rw [← Over.comp_left]
  congr 1
  simp [translBy, comp_mul, u.ex_add]

omit [IsLocalRing R] [Module.Finite ℂ R] in
/- English proof (translation)
Rewrite using `[← Over.comp_left]`. Use `congr 1`. Simplify using `only [famPt, translBy, Hom.mul_def]`. Rewrite using `[← Category.assoc, ← Category.assoc, comp_lift, comp_lift]`. Simplify using the standard rewrite rules.
-/
theorem famPt_transl (x : spO R ⟶ A) (z : Fin g → ℂ) :
    (famPt u R z).left ≫ (lift (fst (spO R) A ≫ x) (snd (spO R) A) ≫ μ[A]).left = (x ≫ translBy u z).left := by
  rw [← Over.comp_left]
  congr 1
  simp only [famPt, translBy, Hom.mul_def]
  rw [← Category.assoc, ← Category.assoc, comp_lift, comp_lift]
  simp

omit [IsLocalRing R] [Module.Finite ℂ R] in
/- English proof (translation)
Rewrite using `[← resPt_left, ← Over.comp_left, ← Category.assoc, hx]`. Use `congr 1`. Simplify using `[translBy, comp_mul]`.
-/
theorem residue_transl (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (hx : resPt ρ ≫ x = 1) (z : Fin g → ℂ) :
    spMap ρ.toRingHom ≫ (x ≫ translBy u z).left = (u.ex z).left := by
  rw [← resPt_left, ← Over.comp_left, ← Category.assoc, hx]
  congr 1
  simp [translBy, comp_mul]

/- English proof (translation)
Use `subsingleton_primeSpectrum (R := R)` as an intermediate fact. Establish `e1 : lift (toUnit A ≫ resPt ρ) (𝟙 A) ≫ lift (fst (spO R) A ≫ x) (snd (spO R) A) ≫ μ = 𝟙 A`. Rewrite using `[← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, Category.assoc, hx, MonObj.comp_one, ← Hom.mul_def, _root_.one_mul]`. Establish `e2 : lift (toUnit A ≫ resPt ρ) (𝟙 A) ≫ snd (spO R) A = 𝟙 A` using `lift_snd _ _`. Introduce `p hp`.

Take `⟨a, rfl⟩` from `surjective_residue_slice (A := A) ρ p`. Establish `q1 : (lift (fst (spO R) A ≫ x) (snd (spO R) A) ≫ μ).left ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) = a`. Establish `h1` using `congrArg (fun φ : A ⟶ A => φ.left a) e1`. Simplify using `using h1`. Establish `q2 : (snd (spO R) A).left ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) = a`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, e2]`. Both sides reduce to the same expression. Establish `ha : a ∈ L.U i`. Establish `h3 : (snd (spO R) A).left ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) ∈ L.U i` using `hp`. Rewrite `h3` using `[q2]`. Then use the resulting hypothesis.

Unfold `Out.translDiff LB.LinComb LB.wchart`. Rewrite using `[← SetLike.mem_coe]`. Simplify using `only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage]`. Introduce `k`. Use `fin_cases k`.

Simplify using `only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]`. Rewrite using `[q1]`. Conclude with `ha`. Simplify using `only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]`. Rewrite using `[q2]`.

Conclude with `ha`.
-/
theorem snd_preimage_le (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (hx : resPt ρ ≫ x = 1) (i : L.ι) :
    (snd (spO R) A).left ⁻¹ᵁ L.U i ≤ (Out.translDiff A L x).U (fun _ => i) := by
  have := subsingleton_primeSpectrum (R := R)
  have e1 : lift (toUnit A ≫ resPt ρ) (𝟙 A) ≫ lift (fst (spO R) A ≫ x) (snd (spO R) A) ≫ μ = 𝟙 A := by
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, Category.assoc, hx, MonObj.comp_one,
      ← Hom.mul_def, _root_.one_mul]
  have e2 : lift (toUnit A ≫ resPt ρ) (𝟙 A) ≫ snd (spO R) A = 𝟙 A := lift_snd _ _
  intro p hp
  obtain ⟨a, rfl⟩ := surjective_residue_slice (A := A) ρ p
  have q1 : (lift (fst (spO R) A ≫ x) (snd (spO R) A) ≫ μ).left
      ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) = a := by
    have h1 := congrArg (fun φ : A ⟶ A => φ.left a) e1
    simpa using h1
  have q2 : (snd (spO R) A).left ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) = a := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e2]
    rfl
  have ha : a ∈ L.U i := by
    have h3 : (snd (spO R) A).left ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) ∈ L.U i := hp
    rwa [q2] at h3
  unfold Out.translDiff LB.LinComb LB.wchart
  rw [← SetLike.mem_coe]
  simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage]
  intro k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [q1]
    exact ha
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [q2]
    exact ha

omit [IsLocalRing R] [Module.Finite ℂ R] in

/- English proof (translation)
Use `set T := (translBy u z).left with hT`. Establish `hcomp : (x ≫ translBy u z).left = x.left ≫ T` using `Over.comp_left ..`. Establish `h' : ⊤ ≤ x.left ⁻¹ᵁ (T ⁻¹ᵁ W)`. Establish `h0` using `h`. Rewrite `h0` using `[hcomp]`.

Conclude with `h0`. Set `f'` to `(T.appLE W (T ⁻¹ᵁ W) le_rfl).hom f`. Establish `hev : evalPt (R` using `R) x.left (T ⁻¹ᵁ W) h' f' = evalPt (R := R) (x ≫ translBy u z).left W h f := evalPt_appLE x.left T _ hcomp.symm W _ le_rfl h' h f`. Establish `hfun : (fun y => valAt' (u.ex y).left (T ⁻¹ᵁ W) f') = fun y => valAt' (u.ex (y + z)).left W f`. Use function extensionality and compare the values at `y`.

Establish `hy` using `ex_translBy u z y`. Distinguish the cases in `hm : ⊤ ≤ (u.ex y).left ⁻¹ᵁ (T ⁻¹ᵁ W)`. Establish `hm' : ⊤ ≤ (u.ex (y + z)).left ⁻¹ᵁ W` using `by rw [← hy]; exact hm`. Rewrite using `[valAt'_eq_evalPt _ _ hm, valAt'_eq_evalPt _ _ hm']`. Conclude with `evalPt_appLE _ T _ hy W _ le_rfl hm hm' f`.

Establish `hm' : ¬ ⊤ ≤ (u.ex (y + z)).left ⁻¹ᵁ W` using `by rw [← hy]; exact hm`. Simplify using `only [valAt', dif_neg hm, dif_neg hm']`. Establish `hsh` using `fderiv_comp_add_right (𝕜 := ℂ) (f := fun v => valAt' (u.ex v).left W f) (x := 0) z`. Simplify using `only [zero_add] at hsh`. Take `⟨h1, h2⟩` from `hκ (T ⁻¹ᵁ W) h' f'`.

Rewrite using `[← hev, h1 r, h2, hfun, hsh]`.
-/
theorem first_order_transl (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (κ : R →ₗ[ℂ] ℂ) (w : Fin g → ℂ)
    (hκ : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
        (∀ r, κ (r * evalPt (R := R) x.left W h f) =
          ρ r * κ (evalPt (R := R) x.left W h f) + ρ (evalPt (R := R) x.left W h f) * κ r) ∧
        κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)
    (z : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (x ≫ translBy u z).left ⁻¹ᵁ W) (f : Γ(A.left, W)) (r : R) :
    κ (r * evalPt (R := R) (x ≫ translBy u z).left W h f) =
      ρ r * fderiv ℂ (fun y => valAt' (u.ex y).left W f) z w +
        ρ (evalPt (R := R) (x ≫ translBy u z).left W h f) * κ r := by
  set T := (translBy u z).left with hT
  have hcomp : (x ≫ translBy u z).left = x.left ≫ T := Over.comp_left ..
  have h' : ⊤ ≤ x.left ⁻¹ᵁ (T ⁻¹ᵁ W) := by
    have h0 := h
    rw [hcomp] at h0
    exact h0
  let f' := (T.appLE W (T ⁻¹ᵁ W) le_rfl).hom f
  have hev : evalPt (R := R) x.left (T ⁻¹ᵁ W) h' f' = evalPt (R := R) (x ≫ translBy u z).left W h f :=
    evalPt_appLE x.left T _ hcomp.symm W _ le_rfl h' h f
  have hfun : (fun y => valAt' (u.ex y).left (T ⁻¹ᵁ W) f') = fun y => valAt' (u.ex (y + z)).left W f := by
    funext y
    have hy := ex_translBy u z y
    by_cases hm : ⊤ ≤ (u.ex y).left ⁻¹ᵁ (T ⁻¹ᵁ W)
    · have hm' : ⊤ ≤ (u.ex (y + z)).left ⁻¹ᵁ W := by rw [← hy]; exact hm
      rw [valAt'_eq_evalPt _ _ hm, valAt'_eq_evalPt _ _ hm']
      exact evalPt_appLE _ T _ hy W _ le_rfl hm hm' f
    · have hm' : ¬ ⊤ ≤ (u.ex (y + z)).left ⁻¹ᵁ W := by rw [← hy]; exact hm
      simp only [valAt', dif_neg hm, dif_neg hm']
  have hsh := fderiv_comp_add_right (𝕜 := ℂ) (f := fun v => valAt' (u.ex v).left W f) (x := 0) z
  simp only [zero_add] at hsh
  obtain ⟨h1, h2⟩ := hκ (T ⁻¹ᵁ W) h' f'
  rw [← hev, h1 r, h2, hfun, hsh]

end Main

end GlobalTheory.ArtinKernel
