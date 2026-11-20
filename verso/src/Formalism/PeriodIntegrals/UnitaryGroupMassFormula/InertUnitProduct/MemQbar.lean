import Mathlib
import Formalism.PeriodIntegrals.ProdUnitInert
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertUnitProduct.NatCastNormLeOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertUnitProduct.ExistsRatCoords

noncomputable section

namespace PI.UnitaryGroupMassFormula.ProdUnitInert

open PI.ProdUnitInert

/- English proof (translation)
Rewrite using `[Qbar, mem_algebraicClosure_iff']`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℚ) e).map φ₀.toRatAlgHom`.
-/
lemma mem_Qbar {E : Type} [Field E] [NumberField E] (φ₀ : E →+* ℂ) (e : E) :
    φ₀ e ∈ Qbar := by
  rw [Qbar, mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) e).map φ₀.toRatAlgHom

/- English proof (translation)
Introduce `E _ _ K c φ₀ S _ emb hinj hagree hcard hc hK d p _ b hb hjac lam z hz`. Establish `hd0 : d ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : jacobiSym 0 p = 0` using `jacobiSym.zero_left (Fact.out : p.Prime).one_lt`. Simplify using `[h0] at hjac`.

Establish `hns : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))` using `(legendreSym.eq_neg_one_iff (p := p)).mp (by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hjac)`. Establish `hP` using `prod_emb_eq_norm K φ₀ S emb hinj hagree hcard z`. Take `⟨x, y, hw⟩` from `exists_rat_coords K hK d hd0 b hb (Algebra.norm K z)`. Establish `hβ : (φ₀ (b : E)) ^ 2 = -(d : ℂ)`. Establish `h` using `congrArg (fun t : K => φ₀ (t : E)) hb`.

Simplify using `using h`. Establish `hPxy : ∏ s, emb s z = (x : ℂ) + y * φ₀ (b : E)`. Rewrite using `[hP, hw]`. Simplify using the standard rewrite rules. Establish `hPP : (∏ s, emb s z) * (starRingEnd ℂ) (∏ s, emb s z) = 1`.

Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one (fun s _ => by rw [← hc, ← map_mul, hz, map_one])`. Rewrite `hPP` using `[hPxy]`. Establish `hconic` using `conic_of_norm_one d _ hβ x y hPP`. Establish `hβmem : φ₀ (b : E) ∈ Qbar` using `mem_Qbar φ₀ _`.

Establish `hPmem : (∏ s, emb s z) ∈ Qbar` using `by rw [hP]; exact mem_Qbar φ₀ _`. Unfold `PI.ProdUnitInert.lamC`. Rewrite using `[dif_pos hPmem]`. Establish `hsub : (⟨∏ s, emb s z, hPmem⟩ : Qbar) = (x : Qbar) + (y : Qbar) * ⟨φ₀ (b : E), hβmem⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[hPxy]`. Rewrite using `[hsub, map_add, map_mul, map_ratCast, map_ratCast]`. Apply `norm_conic_eq_one d hns x y hconic` to reduce the goal to its premises. Establish `hsq : (⟨φ₀ (b : E), hβmem⟩ : Qbar) ^ 2 = -(d : Qbar)`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[hβ]`. Rewrite using `[← map_pow, hsq, map_neg, map_natCast]`.
-/
theorem main : PI.ProdUnitInert := by
  intro E _ _ K c φ₀ S _ emb hinj hagree hcard hc hK d p _ b hb hjac lam z hz
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h0 : jacobiSym 0 p = 0 := jacobiSym.zero_left (Fact.out : p.Prime).one_lt
    simp [h0] at hjac
  have hns : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p)) :=
    (legendreSym.eq_neg_one_iff (p := p)).mp (by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hjac)
  have hP := prod_emb_eq_norm K φ₀ S emb hinj hagree hcard z
  obtain ⟨x, y, hw⟩ := exists_rat_coords K hK d hd0 b hb (Algebra.norm K z)
  have hβ : (φ₀ (b : E)) ^ 2 = -(d : ℂ) := by
    have h := congrArg (fun t : K => φ₀ (t : E)) hb
    simpa using h
  have hPxy : ∏ s, emb s z = (x : ℂ) + y * φ₀ (b : E) := by
    rw [hP, hw]
    simp
  have hPP : (∏ s, emb s z) * (starRingEnd ℂ) (∏ s, emb s z) = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun s _ => by rw [← hc, ← map_mul, hz, map_one])
  rw [hPxy] at hPP
  have hconic := conic_of_norm_one d _ hβ x y hPP
  have hβmem : φ₀ (b : E) ∈ Qbar := mem_Qbar φ₀ _
  have hPmem : (∏ s, emb s z) ∈ Qbar := by rw [hP]; exact mem_Qbar φ₀ _
  unfold PI.ProdUnitInert.lamC
  rw [dif_pos hPmem]
  have hsub : (⟨∏ s, emb s z, hPmem⟩ : Qbar) = (x : Qbar) + (y : Qbar) * ⟨φ₀ (b : E), hβmem⟩ := by
    apply Subtype.ext
    simp [hPxy]
  rw [hsub, map_add, map_mul, map_ratCast, map_ratCast]
  apply norm_conic_eq_one d hns x y hconic
  have hsq : (⟨φ₀ (b : E), hβmem⟩ : Qbar) ^ 2 = -(d : Qbar) := by
    apply Subtype.ext
    simp [hβ]
  rw [← map_pow, hsq, map_neg, map_natCast]

end PI.UnitaryGroupMassFormula.ProdUnitInert
