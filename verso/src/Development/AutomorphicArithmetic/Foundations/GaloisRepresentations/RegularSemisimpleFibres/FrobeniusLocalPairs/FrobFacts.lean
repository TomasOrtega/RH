import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
import GroundTheory.LocalFields.Uniqueness

noncomputable section

open ValuativeRel Matrix GlobalTheory.DZA

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `valuation K (s (x : K)) ≤ 1`. Rewrite using `[GroundTheory.LocalField.valuation_algEquiv_apply]`. Conclude with `x.2`.
-/
private theorem mem_int (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  change valuation K (s (x : K)) ≤ 1
  rw [GroundTheory.LocalField.valuation_algEquiv_apply]
  exact x.2

private def resO (s : K ≃ₐ[k] K) : 𝒪[K] →+* 𝒪[K] :=
  (s.toAlgHom.toRingHom.comp (algebraMap 𝒪[K] K)).codRestrict 𝒪[K] fun x => mem_int s x

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem resO_coe (s : K ≃ₐ[k] K) (x : 𝒪[K]) : ((resO s x : 𝒪[K]) : K) = s (x : K) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[resO_coe, resO_coe]`. Express the relevant statement in the definitionally equal form `s (s.symm (x : K)) = x`. Conclude with `s.apply_symm_apply _`.
-/
private theorem resO_inv (s : K ≃ₐ[k] K) (x : 𝒪[K]) : resO s (resO s⁻¹ x) = x := by
  apply Subtype.ext
  rw [resO_coe, resO_coe]
  change s (s.symm (x : K)) = x
  exact s.apply_symm_apply _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[GlobalTheory.LBC.galAct]`. Conclude with `resO_coe s _`.
-/
private theorem map_res (s : K ≃ₐ[k] K) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s) y) =
      GlobalTheory.LBC.galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) := by
  ext i j
  simp [GlobalTheory.LBC.galAct]
  exact resO_coe s _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[resO_inv]`.
-/
private theorem map_res_inv (s : K ≃ₐ[k] K) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map (resO s) (GeneralLinearGroup.map (resO s⁻¹) y) = y := by
  ext i j
  simp [resO_inv]

variable {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Algebra F₀ F₁]
    {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[GlobalTheory.LBC.galAct]`. Conclude with `h.gal _ _ (resO_coe s _)`.
-/
private theorem map_res_red (h : IsRes rk rK s sb) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map rK (GeneralLinearGroup.map (resO s) y) =
      GlobalTheory.LBC.galAct sb n (GeneralLinearGroup.map rK y) := by
  ext i j
  simp [GlobalTheory.LBC.galAct]
  exact h.gal _ _ (resO_coe s _)

/- English proof (translation)
Proceed by induction on `j generalizing x with`. Consider the case `zero`. Establish `hx : resO (s ^ 0) x = x` using `Subtype.ext (resO_coe _ x)`. Rewrite using `[hx]`. Both sides reduce to the same expression.

Consider the case `succ j ih`. Rewrite using `[pow_succ, AlgEquiv.mul_apply, ← h.gal x (resO s x) (resO_coe s x), ih]`. Use `congr 1`.
-/
private theorem pow_red (h : IsRes rk rK s sb) (j : ℕ) (x : 𝒪[K]) :
    (sb ^ j) (rK x) = rK (resO (s ^ j) x) := by
  induction j generalizing x with
  | zero =>
    have hx : resO (s ^ 0) x = x := Subtype.ext (resO_coe _ x)
    rw [hx]
    rfl
  | succ j ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ← h.gal x (resO s x) (resO_coe s x), ih]
    congr 1

/- English proof (translation)
Establish `hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁`. Use extensionality with `z`. Rewrite using `[h.frob z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]`. Establish `hpow : sb ^ orderOf s = 1`. Use extensionality with `z`.

Take `⟨x, rfl⟩` from `h.onto₁ z`. Rewrite using `[pow_red h, pow_orderOf_eq_one]`. Establish `hx : resO (1 : K ≃ₐ[k] K) x = x` using `Subtype.ext (resO_coe _ x)`. Rewrite using `[hx]`. Both sides reduce to the same expression.

Establish `hord : orderOf sb = Module.finrank F₀ F₁`. Rewrite using `[hsb]`. Conclude with `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁`. Rewrite using `[← h.deg, ← hord]`. Conclude with `orderOf_dvd_of_pow_eq_one hpow`.
-/
private theorem finrank_dvd [Fintype F₁] (h : IsRes rk rK s sb) :
    Module.finrank k K ∣ orderOf s := by
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [h.frob z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  have hpow : sb ^ orderOf s = 1 := by
    ext z
    obtain ⟨x, rfl⟩ := h.onto₁ z
    rw [pow_red h, pow_orderOf_eq_one]
    have hx : resO (1 : K ≃ₐ[k] K) x = x := Subtype.ext (resO_coe _ x)
    rw [hx]
    rfl
  have hord : orderOf sb = Module.finrank F₀ F₁ := by
    rw [hsb]
    exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁
  rw [← h.deg, ← hord]
  exact orderOf_dvd_of_pow_eq_one hpow

/- English proof (translation)
Establish `hdvd` using `finrank_dvd h`. Establish `hcard : Nat.card (K ≃ₐ[k] K) = Module.finrank k K` using `IsGalois.card_aut_eq_finrank k K`. Establish `hle : orderOf s ∣ Nat.card (K ≃ₐ[k] K)` using `orderOf_dvd_natCard s`. Establish `heq : Nat.card (Subgroup.zpowers s) = Nat.card (K ≃ₐ[k] K)`. Rewrite using `[Nat.card_zpowers]`.

Conclude with `Nat.dvd_antisymm hle (hcard ▸ hdvd)`. Rewrite using `[Subgroup.eq_top_of_card_eq _ heq]`. Conclude with `Subgroup.mem_top τ`.
-/
private theorem mem_zpowers_of_isRes [IsGalois k K] [Fintype F₁] (h : IsRes rk rK s sb)
    (τ : K ≃ₐ[k] K) : τ ∈ Subgroup.zpowers s := by
  have hdvd := finrank_dvd h
  have hcard : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
  have hle : orderOf s ∣ Nat.card (K ≃ₐ[k] K) := orderOf_dvd_natCard s
  have heq : Nat.card (Subgroup.zpowers s) = Nat.card (K ≃ₐ[k] K) := by
    rw [Nat.card_zpowers]
    exact Nat.dvd_antisymm hle (hcard ▸ hdvd)
  rw [Subgroup.eq_top_of_card_eq _ heq]
  exact Subgroup.mem_top τ

end

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
/- English proof (translation)
Introduce `k K _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h`. Establish `key : ∀ (n : ℕ) (z : GL (Fin n) F₁), GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n z) = z`. Introduce `n z`. Rewrite using `[← MonoidHom.comp_apply, ← GlobalTheory.LBC.galAct_mul, inv_mul_cancel, GlobalTheory.LBC.galAct_one]`. Both sides reduce to the same expression.

Use `⟨mem_zpowers_of_isRes h, fun n => ⟨?_, ?_, fun y => ⟨GeneralLinearGroup.map (resO s) y, map_res s n y, map_res_red h n y⟩⟩⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (GlobalTheory.LBC.galAct sb n)`. Introduce `a b hab`. Combine the equalities or inequalities in the displayed calculation. Unfold `GlobalTheory.LBC.IsStable K1`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Use `⟨GeneralLinearGroup.map (resO s) y, ?_, map_res s n y⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Rewrite using `[map_res_red h, hy, map_one]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y), ⟨GeneralLinearGroup.map (resO s⁻¹) y, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← map_res_red h, map_res_inv, hy, map_one]`.

Rewrite using `[← map_res, map_res_inv]`. Unfold `GlobalTheory.LBC.IsStable KO`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨y, rfl⟩, rfl⟩`. Conclude with `⟨GeneralLinearGroup.map (resO s) y, map_res s n y⟩`.

Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y), ⟨_, rfl⟩, by rw [← map_res, map_res_inv]⟩`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.frobFacts :
    UpperTheory.Gal.InertialTypesAlt.L.FrobFacts := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h
  have key : ∀ (n : ℕ) (z : GL (Fin n) F₁), GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n z) = z := by
    intro n z
    rw [← MonoidHom.comp_apply, ← GlobalTheory.LBC.galAct_mul, inv_mul_cancel, GlobalTheory.LBC.galAct_one]
    rfl
  refine ⟨mem_zpowers_of_isRes h, fun n => ⟨?_, ?_, fun y =>
    ⟨GeneralLinearGroup.map (resO s) y, map_res s n y, map_res_red h n y⟩⟩⟩
  · have hinj : Function.Injective (GlobalTheory.LBC.galAct sb n) := by
      intro a b hab
      calc a = GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n a) := (key n a).symm
        _ = GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n b) := by rw [hab]
        _ = b := key n b
    unfold GlobalTheory.LBC.IsStable K1
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨GeneralLinearGroup.map (resO s) y, ?_, map_res s n y⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
      rw [map_res_red h, hy, map_one]
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y),
        ⟨GeneralLinearGroup.map (resO s⁻¹) y, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
        apply hinj
        rw [← map_res_red h, map_res_inv, hy, map_one]
      · rw [← map_res, map_res_inv]
  · unfold GlobalTheory.LBC.IsStable KO
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨GeneralLinearGroup.map (resO s) y, map_res s n y⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y),
        ⟨_, rfl⟩, by rw [← map_res, map_res_inv]⟩
