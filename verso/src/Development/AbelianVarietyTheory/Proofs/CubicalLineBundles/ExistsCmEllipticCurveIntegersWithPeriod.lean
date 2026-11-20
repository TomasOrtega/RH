import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOActExtendDedekind
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConjAction
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmAdjoinActionOfEquationStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisationStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConjStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllExists

/- English proof (translation)
Substitute `hg hg'` using the available equality. Take `⟨a, ha⟩ : ∃ a : ℂ, ∀ z, F z = fun _ => a * z 0` from `⟨F (fun _ => 1) 0, fun z => by`. Establish `e : z = z 0 • fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `i`. Use `fin_cases i`.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Use `conv_lhs => rw [e, map_smul]`. Simplify using `[mul_comm]⟩`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Establish `ht : (Λ : Set (Fin 1 → ℂ)) = Set.univ` using `Set.eq_univ_of_forall fun z => (hF z).2 (by`. Rewrite using `[ha]`. Simplify using `only [zero_mul]`.

Conclude with `Λ'.zero_mem)`. Establish `h1 : IsDiscrete (Λ : Set (Fin 1 → ℂ))` using `⟨hd⟩`. Rewrite `h1` using `[ht, isDiscrete_univ_iff]`. Use `(isClopen_discrete ({0} : Set (Fin 1 → ℂ))).eq_univ ⟨0, rfl⟩` as an intermediate fact. Establish `h2 : (1 : Fin 1 → ℂ) ∈ ({0} : Set (Fin 1 → ℂ))` using `this ▸ Set.mem_univ _`.

Conclude with `one_ne_zero h2`. Use `⟨c / a, div_ne_zero hc ha0, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[hF, h, ha]`. Use `exists₂_congr fun m n => ⟨fun e => ?_, fun e => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i fin_cases i`.

Use `congrFun e 0` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Clear denominators, using `at this` for the nonvanishing conditions. Simplify `this` using `[mul_comm a]`. Use function extensionality and compare the values at `i`.

Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts.
-/
theorem isQuadLattice_of_linear {g g' : ℕ} (hg : g = 1) (hg' : g' = 1) {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} (hd : DiscreteTopology Λ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hF : ∀ z, z ∈ Λ ↔ F z ∈ Λ') {d : ℕ} {c : ℂ} (hc : c ≠ 0) (h : PureType.IsQuadLattice Λ' d c) :
    ∃ c' : ℂ, c' ≠ 0 ∧ PureType.IsQuadLattice Λ d c' := by
  subst hg hg'
  obtain ⟨a, ha⟩ : ∃ a : ℂ, ∀ z, F z = fun _ => a * z 0 := ⟨F (fun _ => 1) 0, fun z => by
    have e : z = z 0 • fun _ => (1 : ℂ) := by
      funext i
      fin_cases i
      simp
    funext i
    fin_cases i
    conv_lhs => rw [e, map_smul]
    simp [mul_comm]⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    have ht : (Λ : Set (Fin 1 → ℂ)) = Set.univ := Set.eq_univ_of_forall fun z => (hF z).2 (by
      rw [ha]
      simp only [zero_mul]
      exact Λ'.zero_mem)
    have h1 : IsDiscrete (Λ : Set (Fin 1 → ℂ)) := ⟨hd⟩
    rw [ht, isDiscrete_univ_iff] at h1
    have := (isClopen_discrete ({0} : Set (Fin 1 → ℂ))).eq_univ ⟨0, rfl⟩
    have h2 : (1 : Fin 1 → ℂ) ∈ ({0} : Set (Fin 1 → ℂ)) := this ▸ Set.mem_univ _
    exact one_ne_zero h2
  refine ⟨c / a, div_ne_zero hc ha0, fun z => ?_⟩
  rw [hF, h, ha]
  refine exists₂_congr fun m n => ⟨fun e => ?_, fun e => ?_⟩
  · funext i
    fin_cases i
    have := congrFun e 0
    field_simp
    field_simp at this
    simpa [mul_comm a] using this
  · funext i
    rw [e]
    field_simp

/- English proof (translation)
Take `⟨Q₀, φ₀, h₀⟩` from `exists_isPolFibre hL.polBaseChange σ P`. Take `⟨rig, hrig⟩` from `Q₀.rigid`. Take `⟨u₀, -, -, -, -, -, t₁, t₂, -⟩` from `hU Q₀ rig hrig`. Take `⟨c, hc, hΛ⟩` from `h Q₀ φ₀ h₀ u₀`. Take `⟨f, hf, ef⟩` from `NormHom.exists_monHom_lift hφ h₀.2.1 (𝟙 P.A)`.

Take `⟨F, hF, hF', -⟩` from `HomLinear.exists_linear_of_isMonHom Q.A Q₀.A Q.isAb Q₀.isAb Q.L Q₀.L Q.g Q₀.g u u₀ t₁ t₂ f hf`. Use `isQuadLattice_of_linear hQ (h₀.1.trans hg) u.discrete F (fun z => ⟨hF' z, fun hz => ?_⟩) hc hΛ` and prove the remaining obligations. Rewrite `hz` using `[← u₀.ker, hF]`. Rewrite using `[← u.ker]`. Apply `NormHom.push_inj hφ` to reduce the goal to its premises.

Establish `e` using `NormHom.push_comp hφ h₀.2.1 ef (u.ex z)`. Rewrite `e` using `[hz, map_one, Category.comp_id]`. Rewrite using `[map_one, e]`.
-/
theorem isQuadLattice_of_isGrpPullback (hU : ThetaUnifAV) (hL : Out.Laws) {R : Type} [CommRing R]
    (P : Out.PolAV (Sp R)) (hg : P.g = 1) (σ : R →+* ℂ) {d : ℕ}
    (h : ∀ (Q : Out.PolAV (Sp ℂ)) (φ : Q.A.left ⟶ P.A.left), IsPolFibre σ P Q φ → ∀ u : HolUnif Q.A Q.L Q.g,
      ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c)
    (Q : Out.PolAV (Sp ℂ)) (hQ : Q.g = 1) (φ : Q.A.left ⟶ P.A.left) (hφ : IsGrpPullback Q.A P.A (spMap σ) φ)
    (u : HolUnif Q.A Q.L Q.g) : ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c := by
  obtain ⟨Q₀, φ₀, h₀⟩ := exists_isPolFibre hL.polBaseChange σ P
  obtain ⟨rig, hrig⟩ := Q₀.rigid
  obtain ⟨u₀, -, -, -, -, -, t₁, t₂, -⟩ := hU Q₀ rig hrig
  obtain ⟨c, hc, hΛ⟩ := h Q₀ φ₀ h₀ u₀
  obtain ⟨f, hf, ef⟩ := NormHom.exists_monHom_lift hφ h₀.2.1 (𝟙 P.A)
  obtain ⟨F, hF, hF', -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q₀.A Q.isAb Q₀.isAb Q.L Q₀.L Q.g Q₀.g u u₀ t₁ t₂ f hf
  refine isQuadLattice_of_linear hQ (h₀.1.trans hg) u.discrete F (fun z => ⟨hF' z, fun hz => ?_⟩) hc hΛ
  rw [← u₀.ker, hF] at hz
  rw [← u.ker]
  apply NormHom.push_inj hφ
  have e := NormHom.push_comp hφ h₀.2.1 ef (u.ex z)
  rw [hz, map_one, Category.comp_id] at e
  rw [map_one, e]

/- English proof (translation)
Establish `hm` using `H.d_mod`. Take `⟨K, _, h2, hr⟩` from `exists_quadraticField_sq_eq_neg (d := H.d) (by omega)`. Take `⟨M, _, w, P, v, hw, hg, hv, ⟨P₀, φ, v₀, W, hφ, hv₀, hb₀, hW, hWW, hWv⟩, hΛ, n, hn0, hn, hx, -⟩` from `chowla_selberg_lie_lines hC (by omega) H.d_prime.squarefree (by omega) h2 hr hχ`. Use `P₀.isAb.comm` as an intermediate fact. Use `P.isAb.comm` as an intermediate fact.

Take `⟨a₀, ha₀, -⟩` from `GlobalTheory.T.exists_cmAdjoin_action_of_equation E H _ P₀.A W hW hWW`. Take `⟨a, ha⟩` from `exists_oAct_extend_dedekind hX (𝓞 M) M (OK H) P.A P₀.A φ P.isAb hφ.2.1 a₀`. Establish `hvt : IsTangent v` using `hv.1 0`. Use `a.hom (wK H)` as an intermediate fact. Take `⟨c, hc, -⟩` from `hv.2 _ (HomLinear.isTangent_comp (a.act (wK H)) hvt)`.

Take `⟨ω, rfl⟩ : ∃ ω, c = ![ω]` from `⟨c 0, by funext i; fin_cases i; rfl⟩`. Establish `hc₀` using `(lieComb_baseChange _ _ (algebraMap (𝓞 M) M) P.A P₀.A φ hφ.2.1 1 ![v] _ ![ω] ![v₀] (v₀ ≫ W) (fun j => by fin_cases j; exact hv₀) hc).1 (NormHom.isVecOver_comp hv₀ (ha₀ ▸ ha (wK H)))`. Establish `hω : (ω : M) = w` using `congrFun ((hb₀.2 _ (HomLinear.isTangent_comp W (hb₀.1 0))).unique hc₀ hWv) 0`. Establish `hσ : Function.Injective ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))` using `(algebraMap M ℂ).injective.comp (IsFractionRing.injective (𝓞 M) M)`. Take `⟨L', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩` from `GlobalTheory.T.exists_normalized_symmetric_ample_lb hL (𝓞 M) P (a.act (wK H)) (a.act (EllConj.barK H (wK H))) (a.hom _) (a.hom _) (by rw [← a.add, add_comm, EllConj.barK_wK_add, a.one]) (GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P a hσ hg _ _ rfl)`.

Set `P' : Out.PolAV (Sp (𝓞 M))` to `⟨P.A, P.isAb, P.g, P.smoothDim, L', h₁, h₂, h₃, h₄, h₅⟩`. Establish `key : ∀ (s : M →+* ℂ) r, IsLieNormSq P' v (s.comp (algebraMap (𝓞 M) M)) r → r = n s` using `fun s r h => by`. Establish `h1 : IsLieComb ![(1 : 𝓞 M)] ![v] (v ≫ 𝟙 P.A)`. Rewrite using `[LieComb.isLieComb_iff_tanExp, Category.comp_id]`. Establish `e : (![1] : Fin 1 → 𝓞 M) = Pi.single 0 1`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `(LieComb.tanExp_single hv.1 0).symm`.

Establish `e` using `NormHom.lieNormSq_comp hU hL (𝓞 M) P P' (𝟙 P.A) (𝟙 P.A) v 1 _ (n s) r inferInstance inferInstance h₆ hvt h1 ((hn s _).2 rfl) (by rwa [Category.comp_id])`. Simplify using `using e`. Use `⟨M, inferInstance, ω, ⟨P', hg, a, v, hv, hc, GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P' a hσ hg, h₇⟩, -meanLog M n, hω ▸ hw, fun Q ψ hψ u => ?_, ⟨n, fun s => ⟨hn0 s, fun r => ⟨key s r, fun e => ?_⟩⟩, rfl⟩, hx⟩` and prove the remaining obligations. Use `isQuadLattice_of_isGrpPullback hU hL P hg _ (fun Q ψ hψ u => ?_) Q (hψ.1.trans hg) ψ hψ.2.1 u` and prove the remaining obligations. Take `⟨c, hc, h⟩` from `hΛ Q ψ hψ u`.

Rewrite `h` using `[hw]`. Conclude with `⟨c, hc, h⟩`. Take `⟨r', hr'⟩` from `exists_isLieNormSq hU hL.polBaseChange P' hvt (s.comp (algebraMap (𝓞 M) M))`. Rewrite using `[e, ← key s r' hr']` and apply the resulting hypothesis.
-/
theorem exists_ell_pos (hC : CMCurve) (hU : ThetaUnifAV) (hL : Out.Laws) (hX : HomExtDvr) {E : Type} [Field E]
    [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (hχ : IsKroneckerChar χ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ),
      ((ω : M) : ℂ) = (1 + Complex.I * √H.d) / 2 ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧
      C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  have hm := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) (by omega)
  obtain ⟨M, _, w, P, v, hw, hg, hv, ⟨P₀, φ, v₀, W, hφ, hv₀, hb₀, hW, hWW, hWv⟩, hΛ, n, hn0, hn, hx, -⟩ :=
    chowla_selberg_lie_lines hC (by omega) H.d_prime.squarefree (by omega) h2 hr hχ
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨a₀, ha₀, -⟩ := GlobalTheory.T.exists_cmAdjoin_action_of_equation E H _ P₀.A W hW hWW
  obtain ⟨a, ha⟩ := exists_oAct_extend_dedekind hX (𝓞 M) M (OK H) P.A P₀.A φ P.isAb hφ.2.1 a₀
  have hvt : IsTangent v := hv.1 0
  have := a.hom (wK H)
  obtain ⟨c, hc, -⟩ := hv.2 _ (HomLinear.isTangent_comp (a.act (wK H)) hvt)
  obtain ⟨ω, rfl⟩ : ∃ ω, c = ![ω] := ⟨c 0, by funext i; fin_cases i; rfl⟩
  have hc₀ := (lieComb_baseChange _ _ (algebraMap (𝓞 M) M) P.A P₀.A φ hφ.2.1 1 ![v] _ ![ω] ![v₀] (v₀ ≫ W)
    (fun j => by fin_cases j; exact hv₀) hc).1 (NormHom.isVecOver_comp hv₀ (ha₀ ▸ ha (wK H)))
  have hω : (ω : M) = w := congrFun ((hb₀.2 _ (HomLinear.isTangent_comp W (hb₀.1 0))).unique hc₀ hWv) 0
  have hσ : Function.Injective ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) :=
    (algebraMap M ℂ).injective.comp (IsFractionRing.injective (𝓞 M) M)
  obtain ⟨L', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_normalized_symmetric_ample_lb hL (𝓞 M) P (a.act (wK H)) (a.act (EllConj.barK H (wK H)))
    (a.hom _) (a.hom _) (by rw [← a.add, add_comm, EllConj.barK_wK_add, a.one])
    (GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P a hσ hg _ _ rfl)
  let P' : Out.PolAV (Sp (𝓞 M)) := ⟨P.A, P.isAb, P.g, P.smoothDim, L', h₁, h₂, h₃, h₄, h₅⟩
  have key : ∀ (s : M →+* ℂ) r, IsLieNormSq P' v (s.comp (algebraMap (𝓞 M) M)) r → r = n s := fun s r h => by
    have h1 : IsLieComb ![(1 : 𝓞 M)] ![v] (v ≫ 𝟙 P.A) := by
      rw [LieComb.isLieComb_iff_tanExp, Category.comp_id]
      have e : (![1] : Fin 1 → 𝓞 M) = Pi.single 0 1 := by
        funext i
        fin_cases i
        simp
      rw [e]
      exact (LieComb.tanExp_single hv.1 0).symm
    have e := NormHom.lieNormSq_comp hU hL (𝓞 M) P P' (𝟙 P.A) (𝟙 P.A) v 1 _ (n s) r inferInstance inferInstance h₆ hvt
      h1 ((hn s _).2 rfl) (by rwa [Category.comp_id])
    simpa using e
  refine ⟨M, inferInstance, ω, ⟨P', hg, a, v, hv, hc, GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P' a hσ hg, h₇⟩, -meanLog M n,
    hω ▸ hw, fun Q ψ hψ u => ?_, ⟨n, fun s => ⟨hn0 s, fun r => ⟨key s r, fun e => ?_⟩⟩, rfl⟩, hx⟩
  · refine isQuadLattice_of_isGrpPullback hU hL P hg _ (fun Q ψ hψ u => ?_) Q (hψ.1.trans hg) ψ hψ.2.1 u
    obtain ⟨c, hc, h⟩ := hΛ Q ψ hψ u
    rw [hw] at h
    exact ⟨c, hc, h⟩
  · obtain ⟨r', hr'⟩ := exists_isLieNormSq hU hL.polBaseChange P' hvt (s.comp (algebraMap (𝓞 M) M))
    rwa [e, ← key s r' hr']

/- English proof (translation)
Introduce `hC hU hL hX E _ _ _ H _ χ hχ ρ hρ`. Take `⟨M, _, ω, C, x, hω, hp, hx, hv⟩` from `exists_ell_pos hC hU hL hX H hχ`. Establish `e : ρ ^ 2 = (Complex.I * √H.d) ^ 2`. Rewrite using `[hρ, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]`. Simplify using the standard rewrite rules.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 e with rfl | rfl` into its components or cases. Conclude with `⟨M, inferInstance, ω, C, x, by rw [hω]; ring, hp, hx, hv⟩`. Take `⟨a, -, h₁, h₂, h₃⟩` from `EllConj.exists_conj_action E H (𝓞 M) ω C`. Use `⟨M, inferInstance, 1 - ω, ⟨C.P, C.dim, a, C.v, C.basis, h₁, h₂, h₃⟩, x, ?_, hp, hx, hv⟩` and prove the remaining obligations. Establish `: (((1 - ω : 𝓞 M) : M) : ℂ) = 1 - ((ω : M) : ℂ)` using `by simp`.

Rewrite using `[this, hω]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_ell : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ), 2 * ((ω : M) : ℂ) - 1 = ρ ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧ C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro hC hU hL hX E _ _ _ H _ χ hχ ρ hρ
  obtain ⟨M, _, ω, C, x, hω, hp, hx, hv⟩ := exists_ell_pos hC hU hL hX H hχ
  have e : ρ ^ 2 = (Complex.I * √H.d) ^ 2 := by
    rw [hρ, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with rfl | rfl
  · exact ⟨M, inferInstance, ω, C, x, by rw [hω]; ring, hp, hx, hv⟩
  · obtain ⟨a, -, h₁, h₂, h₃⟩ := EllConj.exists_conj_action E H (𝓞 M) ω C
    refine ⟨M, inferInstance, 1 - ω, ⟨C.P, C.dim, a, C.v, C.basis, h₁, h₂, h₃⟩, x, ?_, hp, hx, hv⟩
    have : (((1 - ω : 𝓞 M) : M) : ℂ) = 1 - ((ω : M) : ℂ) := by simp
    rw [this, hω]
    ring

end GlobalTheory.CM.EllExists
end
