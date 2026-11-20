import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IntermediateField Polynomial

noncomputable section

namespace GroundTheory.Global

section Descent

variable {L : Type} [Field L] [CharZero L] [Algebra L ℂ] {W W' : WeierstrassCurve L} [W.IsElliptic]
  [W'.IsElliptic]

/- English proof (translation)
Establish `hxfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.x = ψ.x` using `fun g ↦ by rw [← Isogeny.conj_alt_bis, h g]`. Establish `hyfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.y = ψ.y` using `fun g ↦ by rw [← Isogeny.conj_y, h g]`. Take `⟨r, hr⟩` from `ψ.exists_ratEmb_eq_x`. Take `⟨a, b, ha, hb, hab⟩` from `exists_eq_add_mul_genY (W.baseChange ℂ) ψ.y`. Establish `ha'` using `ha`.

Establish `hb'` using `hb`. Rewrite `ha'`, `hb'` using `[← fieldRange_ratEmb]`. Take `⟨r₂, hr₂⟩` from `ha'`. Take `⟨r₃, hr₃⟩` from `hb'`. Express the relevant statement in the definitionally equal form `ratEmb (W.baseChange ℂ) r₂ = a at hr₂`.

Express the relevant statement in the definitionally equal form `ratEmb (W.baseChange ℂ) r₃ = b at hr₃`. Establish `hab_fix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g a = a ∧ galFF W g b = b`. Introduce `g`. Establish `e` using `hyfix g`. Rewrite `e` using `[hab, map_add, map_mul, galFF_genY]`.

Conclude with `eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX W _ ha) (galFF_mem_adjoin_genX W _ hb) ha hb e`. Establish `hlift : ∀ s : RatFunc ℂ, (∀ g : ℂ ≃ₐ[L] ℂ, galFF W g (ratEmb (W.baseChange ℂ) s) = ratEmb (W.baseChange ℂ) s) → (∃ p : L[X], p.map (algebraMap L ℂ) = s.num) ∧ ∃ q : L[X], q.map (algebraMap L ℂ) = s.denom`. Introduce `s hs`. Establish `hc : ∀ c ∈ s.num.coeffs ∪ s.denom.coeffs, c ∈ Set.range (algebraMap L ℂ)`. Introduce `c hc`.

Establish `hbot : c ∈ (⊥ : IntermediateField L ℂ)`. Use `(mem_bot_iff_forall_algEquiv_apply_eq (F := L)).2 fun g ↦ ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `map_eq_of_galFF_ratEmb W g (hs g)`. Break down `Finset.mem_union.mp hc with hc | hc` into its components or cases. Take `⟨n, -, rfl⟩` from `Polynomial.mem_coeffs_iff.mp hc`.

Use `congrArg (coeff · n) h1` as an intermediate fact. Simplify using `using this`. Take `⟨n, -, rfl⟩` from `Polynomial.mem_coeffs_iff.mp hc`. Use `congrArg (coeff · n) h2` as an intermediate fact. Simplify using `using this`.

Conclude with `IntermediateField.mem_bot.1 hbot`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Distinguish the cases in `hn : s.num.coeff n = 0`.

Conclude with `⟨0, by rw [hn, map_zero]⟩`. Conclude with `hc _ (Finset.mem_union_left _ (coeff_mem_coeffs hn))`. Rewrite using `[← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Distinguish the cases in `hn : s.denom.coeff n = 0`.

Conclude with `⟨0, by rw [hn, map_zero]⟩`. Conclude with `hc _ (Finset.mem_union_right _ (coeff_mem_coeffs hn))`. Take `⟨⟨n₁, hn₁⟩, ⟨d₁, hd₁⟩⟩` from `hlift r (fun g ↦ by rw [hr]; exact hxfix g)`. Take `⟨⟨n₂, hn₂⟩, ⟨d₂, hd₂⟩⟩` from `hlift r₂ (fun g ↦ by rw [hr₂]; exact (hab_fix g).1)`. Take `⟨⟨n₃, hn₃⟩, ⟨d₃, hd₃⟩⟩` from `hlift r₃ (fun g ↦ by rw [hr₃]; exact (hab_fix g).2)`.

Use `set X₁ := genX W`. Use `set x₁ : W.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁`. Use `set y₁ : W.toAffine.FunctionField := aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY W`. Establish `hrat : ∀ (s : RatFunc ℂ) (p q : L[X]), p.map (algebraMap L ℂ) = s.num → q.map (algebraMap L ℂ) = s.denom → ffMap (algebraMap L ℂ) W (aeval X₁ p / aeval X₁ q) = ratEmb (W.baseChange ℂ) s`. Introduce `s p q hp hq`.

Use `conv_rhs => rw [← RatFunc.num_div_denom s]`. Rewrite using `[ratEmb_div, map_div₀, ffMap_aeval, ffMap_aeval, ffMap_genX, hp, hq]`. Both sides reduce to the same expression. Establish `hx₁ : ffMap (algebraMap L ℂ) W x₁ = ψ.x`. Rewrite using `[← hr]`.

Conclude with `hrat r n₁ d₁ hn₁ hd₁`. Establish `hy₁ : ffMap (algebraMap L ℂ) W y₁ = ψ.y`. Rewrite using `[hab, map_add, map_mul, ← hr₂, ← hr₃, hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃, ffMap_genY]`. Both sides reduce to the same expression. Conclude with `⟨Isogeny.ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁, Isogeny.map_ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁⟩`.
-/
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.exists_map_eq_of_forall_conj_eq
    (ψ : Isogeny (W.baseChange ℂ) (W'.baseChange ℂ)) (h : ∀ g : ℂ ≃ₐ[L] ℂ, ψ.conj g = ψ) :
    ∃ φ : Isogeny W W', φ.map (algebraMap L ℂ) = ψ := by
  classical
  have hxfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.x = ψ.x := fun g ↦ by rw [← Isogeny.conj_alt_bis, h g]
  have hyfix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g ψ.y = ψ.y := fun g ↦ by rw [← Isogeny.conj_y, h g]
  obtain ⟨r, hr⟩ := ψ.exists_ratEmb_eq_x
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_add_mul_genY (W.baseChange ℂ) ψ.y
  have ha' := ha
  have hb' := hb
  rw [← fieldRange_ratEmb] at ha' hb'
  obtain ⟨r₂, hr₂⟩ := ha'
  obtain ⟨r₃, hr₃⟩ := hb'
  change ratEmb (W.baseChange ℂ) r₂ = a at hr₂
  change ratEmb (W.baseChange ℂ) r₃ = b at hr₃
  have hab_fix : ∀ g : ℂ ≃ₐ[L] ℂ, galFF W g a = a ∧ galFF W g b = b := by
    intro g
    have e := hyfix g
    rw [hab, map_add, map_mul, galFF_genY] at e
    exact eq_of_add_mul_genY_eq (galFF_mem_adjoin_genX W _ ha) (galFF_mem_adjoin_genX W _ hb)
      ha hb e
  have hlift : ∀ s : RatFunc ℂ, (∀ g : ℂ ≃ₐ[L] ℂ,
      galFF W g (ratEmb (W.baseChange ℂ) s) = ratEmb (W.baseChange ℂ) s) →
      (∃ p : L[X], p.map (algebraMap L ℂ) = s.num) ∧
        ∃ q : L[X], q.map (algebraMap L ℂ) = s.denom := by
    intro s hs
    have hc : ∀ c ∈ s.num.coeffs ∪ s.denom.coeffs, c ∈ Set.range (algebraMap L ℂ) := by
      intro c hc
      have hbot : c ∈ (⊥ : IntermediateField L ℂ) := by
        refine (mem_bot_iff_forall_algEquiv_apply_eq (F := L)).2 fun g ↦ ?_
        obtain ⟨h1, h2⟩ := map_eq_of_galFF_ratEmb W g (hs g)
        rcases Finset.mem_union.mp hc with hc | hc
        · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
          have := congrArg (coeff · n) h1
          simpa using this
        · obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
          have := congrArg (coeff · n) h2
          simpa using this
      exact IntermediateField.mem_bot.1 hbot
    constructor
    · rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : s.num.coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact hc _ (Finset.mem_union_left _ (coeff_mem_coeffs hn))
    · rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : s.denom.coeff n = 0
      · exact ⟨0, by rw [hn, map_zero]⟩
      · exact hc _ (Finset.mem_union_right _ (coeff_mem_coeffs hn))
  obtain ⟨⟨n₁, hn₁⟩, ⟨d₁, hd₁⟩⟩ := hlift r (fun g ↦ by rw [hr]; exact hxfix g)
  obtain ⟨⟨n₂, hn₂⟩, ⟨d₂, hd₂⟩⟩ := hlift r₂ (fun g ↦ by rw [hr₂]; exact (hab_fix g).1)
  obtain ⟨⟨n₃, hn₃⟩, ⟨d₃, hd₃⟩⟩ := hlift r₃ (fun g ↦ by rw [hr₃]; exact (hab_fix g).2)
  set X₁ := genX W
  set x₁ : W.toAffine.FunctionField := aeval X₁ n₁ / aeval X₁ d₁
  set y₁ : W.toAffine.FunctionField :=
    aeval X₁ n₂ / aeval X₁ d₂ + aeval X₁ n₃ / aeval X₁ d₃ * genY W
  have hrat : ∀ (s : RatFunc ℂ) (p q : L[X]), p.map (algebraMap L ℂ) = s.num →
      q.map (algebraMap L ℂ) = s.denom →
      ffMap (algebraMap L ℂ) W (aeval X₁ p / aeval X₁ q) = ratEmb (W.baseChange ℂ) s := by
    intro s p q hp hq
    conv_rhs => rw [← RatFunc.num_div_denom s]
    rw [ratEmb_div, map_div₀, ffMap_aeval, ffMap_aeval, ffMap_genX, hp, hq]
    rfl
  have hx₁ : ffMap (algebraMap L ℂ) W x₁ = ψ.x := by
    rw [← hr]
    exact hrat r n₁ d₁ hn₁ hd₁
  have hy₁ : ffMap (algebraMap L ℂ) W y₁ = ψ.y := by
    rw [hab, map_add, map_mul, ← hr₂, ← hr₃, hrat r₂ n₂ d₂ hn₂ hd₂, hrat r₃ n₃ d₃ hn₃ hd₃,
      ffMap_genY]
    rfl
  exact ⟨Isogeny.ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁,
    Isogeny.map_ofMap (algebraMap L ℂ) ψ x₁ y₁ hx₁ hy₁⟩

omit [CharZero L] [W.IsElliptic] [W'.IsElliptic] in
/- English proof (translation)
Substitute `hC hC'` using the available equality. Rewrite using `[Isogeny.congr_rfl]`.
-/
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.invConst_congr {F : Type} [Field F]
    {C D C' D' : WeierstrassCurve F} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
    [D'.IsElliptic] (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    invConst (φ.congr hC hC') = invConst φ := by
  subst hC hC'
  rw [Isogeny.congr_rfl]

omit [CharZero L] in

/- English proof (translation)
Rewrite using `[Isogeny.conj, Isogeny.mapOf, Isogeny.invConst_congr, invConst_map]`. Both sides reduce to the same expression.
-/
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.invConst_conj (g : ℂ ≃ₐ[L] ℂ)
    (ψ : Isogeny (W.baseChange ℂ) (W'.baseChange ℂ)) : invConst (ψ.conj g) = g (invConst ψ) := by
  rw [Isogeny.conj, Isogeny.mapOf, Isogeny.invConst_congr, invConst_map]
  rfl

end Descent

namespace Elliptic

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]
include hK

/- English proof (translation)
Use `ψ.exists_map_eq_of_forall_conj_eq fun g ↦ ?_` and prove the remaining obligations. Take `⟨Λ, C, hC⟩` from `exists_variableChange_eq_weierstrassCurve (W.baseChange ℂ)`. Establish `hΛ : latticeEnd Λ = cmRing (algebraMap K ℂ)` using `latticeEnd_eq_cmRing_of_ringEquiv (algebraMap K ℂ) hK Λ ((latticeEndEquiv Λ).trans ((vcEndEquiv C hC).symm.trans hW.some))`. Establish `hmem : endConst (W.baseChange ℂ) ψ.toHom ∈ cmRing (algebraMap K ℂ)`. Rewrite using `[← hΛ, ← range_endConst hC]`.

Conclude with `⟨_, rfl⟩`. Take `⟨a, ha⟩` from `(mem_cmRing (algebraMap K ℂ)).1 hmem`. Establish `hfix : g (endConst (W.baseChange ℂ) ψ.toHom) = endConst (W.baseChange ℂ) ψ.toHom`. Rewrite using `[← ha, IsScalarTower.algebraMap_apply K L ℂ]`. Conclude with `g.commutes _`.

Establish `hc : invConst (ψ.conj g) = invConst ψ`. Rewrite using `[Isogeny.invConst_conj]`. Rewrite `hfix` using `[endConst_apply, homConst_toHom]`. Conclude with `hfix`. Establish `e : endConst (W.baseChange ℂ) (ψ.conj g).toHom = endConst (W.baseChange ℂ) ψ.toHom`.

Rewrite using `[endConst_apply, endConst_apply, homConst_toHom, homConst_toHom, hc]`. Establish `e'` using `congrArg Subtype.val (endConst_injective e)`. Conclude with `Isogeny.ext' e'`.
-/
theorem exists_isogeny_map_eq_of_cm (L : IntermediateField K ℂ) (W : WeierstrassCurve L)
    [W.IsElliptic] (hW : Nonempty (isogEnd (W.baseChange ℂ) ≃+* 𝓞 K))
    (ψ : Isogeny (W.baseChange ℂ) (W.baseChange ℂ)) :
    ∃ φ : Isogeny W W, φ.map (algebraMap L ℂ) = ψ := by
  refine ψ.exists_map_eq_of_forall_conj_eq fun g ↦ ?_
  obtain ⟨Λ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve (W.baseChange ℂ)
  have hΛ : latticeEnd Λ = cmRing (algebraMap K ℂ) := latticeEnd_eq_cmRing_of_ringEquiv
    (algebraMap K ℂ) hK Λ ((latticeEndEquiv Λ).trans ((vcEndEquiv C hC).symm.trans hW.some))
  have hmem : endConst (W.baseChange ℂ) ψ.toHom ∈ cmRing (algebraMap K ℂ) := by
    rw [← hΛ, ← range_endConst hC]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := (mem_cmRing (algebraMap K ℂ)).1 hmem
  have hfix : g (endConst (W.baseChange ℂ) ψ.toHom) = endConst (W.baseChange ℂ) ψ.toHom := by
    rw [← ha, IsScalarTower.algebraMap_apply K L ℂ]
    exact g.commutes _
  have hc : invConst (ψ.conj g) = invConst ψ := by
    rw [Isogeny.invConst_conj]
    rw [endConst_apply, homConst_toHom] at hfix
    exact hfix
  have e : endConst (W.baseChange ℂ) (ψ.conj g).toHom = endConst (W.baseChange ℂ) ψ.toHom := by
    rw [endConst_apply, endConst_apply, homConst_toHom, homConst_toHom, hc]
  have e' := congrArg Subtype.val (endConst_injective e)
  exact Isogeny.ext' e'

/- English proof (translation)
Use `set W := WeierstrassCurve.ofJ (⟨E.curve.j, mem_adjoin_simple_self K _⟩ : K⟮E.curve.j⟯)`. Establish `hj : (W.baseChange ℂ).j = E.curve.j` using `by show (W.map (algebraMap K⟮E.curve.j⟯ ℂ)).j = _`. Rewrite using `[map_j, ofJ_j]`. Both sides reduce to the same expression. Take `⟨C, hC⟩` from `exists_variableChange_of_j_eq _ _ hj`.

Use `⟨W, inferInstance, C, hC, fun ψ ↦ ?_⟩` and prove the remaining obligations. Conclude with `exists_isogeny_map_eq_of_cm hK K⟮E.curve.j⟯ W ⟨(vcEndEquiv C hC).trans E.endIso.some⟩ ψ`.
-/
theorem CMCurve.exists_model_endomorphisms_defined (E : CMCurve K) :
    ∃ (W : WeierstrassCurve K⟮E.curve.j⟯) (_ : W.IsElliptic) (C : VariableChange ℂ),
      C • W.baseChange ℂ = E.curve ∧
        ∀ ψ : Isogeny (W.baseChange ℂ) (W.baseChange ℂ),
          ∃ φ : Isogeny W W, φ.map (algebraMap K⟮E.curve.j⟯ ℂ) = ψ := by
  classical
  set W := WeierstrassCurve.ofJ (⟨E.curve.j, mem_adjoin_simple_self K _⟩ : K⟮E.curve.j⟯)
  have hj : (W.baseChange ℂ).j = E.curve.j := by
    show (W.map (algebraMap K⟮E.curve.j⟯ ℂ)).j = _
    rw [map_j, ofJ_j]
    rfl
  obtain ⟨C, hC⟩ := exists_variableChange_of_j_eq _ _ hj
  refine ⟨W, inferInstance, C, hC, fun ψ ↦ ?_⟩
  exact exists_isogeny_map_eq_of_cm hK K⟮E.curve.j⟯ W ⟨(vcEndEquiv C hC).trans E.endIso.some⟩ ψ

end Elliptic

end GroundTheory.Global
