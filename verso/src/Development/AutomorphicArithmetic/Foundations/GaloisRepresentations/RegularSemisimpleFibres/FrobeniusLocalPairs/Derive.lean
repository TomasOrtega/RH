import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import GroundTheory.LocalFields.Uniqueness

noncomputable section

open ValuativeRel

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

/- English proof (translation)
Establish `hx` using `x.2`. Rewrite `hx`, the goal using `[Valuation.mem_integer_iff]`. Rewrite using `[GroundTheory.LocalField.valuation_algEquiv_apply k K s (x : K)]` and apply the resulting hypothesis.
-/
private theorem mem_int' (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  have hx := x.2
  rw [Valuation.mem_integer_iff] at hx ⊢
  rwa [GroundTheory.LocalField.valuation_algEquiv_apply k K s (x : K)]

variable {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Algebra F₀ F₁]
    {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}

/- English proof (translation)
Proceed by induction on `j generalizing y with`. Consider the case `zero`. Establish `hyx : y = x` using `Subtype.ext (by simpa using hy)`. Substitute `hyx` using the available equality. Simplify using the standard rewrite rules.

Consider the case `succ j ih`. Set `z : 𝒪[K]` to `⟨(s ^ j) x, mem_int' (s ^ j) x⟩`. Establish `hz : rK z = (sb ^ j) (rK x)` using `ih z rfl`. Establish `hyz : (y : K) = s (z : K)`. Rewrite using `[hy, pow_succ']`.

Both sides reduce to the same expression. Rewrite using `[h.gal z y hyz, hz, pow_succ']`. Both sides reduce to the same expression.
-/
private theorem pow_red' (h : IsRes rk rK s sb) (j : ℕ) (x y : 𝒪[K]) (hy : (y : K) = (s ^ j) x) :
    rK y = (sb ^ j) (rK x) := by
  induction j generalizing y with
  | zero =>
    have hyx : y = x := Subtype.ext (by simpa using hy)
    subst hyx
    simp
  | succ j ih =>
    let z : 𝒪[K] := ⟨(s ^ j) x, mem_int' (s ^ j) x⟩
    have hz : rK z = (sb ^ j) (rK x) := ih z rfl
    have hyz : (y : K) = s (z : K) := by
      rw [hy, pow_succ']
      rfl
    rw [h.gal z y hyz, hz, pow_succ']
    rfl

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic F₀ F₁ := Algebra.IsAlgebraic.of_finite F₀ F₁`. Establish `hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁`. Use extensionality with `z`. Rewrite using `[h.frob z]`. Both sides reduce to the same expression.

Establish `hone : sb ^ orderOf s = 1`. Use extensionality with `w`. Take `⟨x, rfl⟩` from `h.onto₁ w`. Use `pow_red' h (orderOf s) x x (by rw [pow_orderOf_eq_one]; rfl)` as an intermediate fact. Rewrite using `[AlgEquiv.one_apply, ← this]`.

Rewrite using `[← h.deg, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁, ← hsb]`. Conclude with `orderOf_dvd_of_pow_eq_one hone`.
-/
private theorem finrank_dvd' [Fintype F₁] (h : IsRes rk rK s sb) :
    Module.finrank k K ∣ orderOf s := by
  classical
  haveI : Algebra.IsAlgebraic F₀ F₁ := Algebra.IsAlgebraic.of_finite F₀ F₁
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [h.frob z]
    rfl
  have hone : sb ^ orderOf s = 1 := by
    ext w
    obtain ⟨x, rfl⟩ := h.onto₁ w
    have := pow_red' h (orderOf s) x x (by rw [pow_orderOf_eq_one]; rfl)
    rw [AlgEquiv.one_apply, ← this]
  rw [← h.deg, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁, ← hsb]
  exact orderOf_dvd_of_pow_eq_one hone

/- English proof (translation)
Establish `hd` using `finrank_dvd' h`. Establish `hpos : 0 < orderOf s` using `orderOf_pos s`. Establish `hle1 : orderOf s ≤ Fintype.card (K ≃ₐ[k] K)` using `orderOf_le_card_univ`. Establish `hle2 : Fintype.card (K ≃ₐ[k] K) ≤ Module.finrank k K` using `AlgEquiv.card_le`. Establish `hle3 : Module.finrank k K ≤ orderOf s` using `Nat.le_of_dvd hpos hd`.

Apply `IsGalois.of_card_aut_eq_finrank` to reduce the goal to its premises. Rewrite using `[Nat.card_eq_fintype_card]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem isGalois_of_isRes [Fintype F₁] (h : IsRes rk rK s sb) : IsGalois k K := by
  classical
  have hd := finrank_dvd' h
  have hpos : 0 < orderOf s := orderOf_pos s
  have hle1 : orderOf s ≤ Fintype.card (K ≃ₐ[k] K) := orderOf_le_card_univ
  have hle2 : Fintype.card (K ≃ₐ[k] K) ≤ Module.finrank k K := AlgEquiv.card_le
  have hle3 : Module.finrank k K ≤ orderOf s := Nat.le_of_dvd hpos hd
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card]
  omega

end

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
/- English proof (translation)
Introduce `k K _ _ _ _ _ _ _ _ _ hc F₀ F₁ _ _ _ _ _ rk rK s sb h`. Use `haveI hv : ValuativeExtension k K := GlobalTheory.LBC.Inh.valuativeExtension hc`. Establish `hpos : 0 < Module.finrank k K`. Rewrite using `[← h.deg]`. Conclude with `Module.finrank_pos`.

Use `haveI hf : FiniteDimensional k K := Module.finite_of_finrank_pos hpos`. Conclude with `⟨hv, hf, isGalois_of_isRes h⟩`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.derive :
    UpperTheory.Gal.InertialTypesAlt.L.Derive := by
  intro k K _ _ _ _ _ _ _ _ _ hc F₀ F₁ _ _ _ _ _ rk rK s sb h
  haveI hv : ValuativeExtension k K := GlobalTheory.LBC.Inh.valuativeExtension hc
  have hpos : 0 < Module.finrank k K := by
    rw [← h.deg]
    exact Module.finrank_pos
  haveI hf : FiniteDimensional k K := Module.finite_of_finrank_pos hpos
  exact ⟨hv, hf, isGalois_of_isRes h⟩
