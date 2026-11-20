import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KaB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

/- English proof (translation)
Rewrite using `[← A.valuation_le_one_iff, map_inv₀, not_le]`. Establish `h0 : A.valuation x ≠ 0` using `by simpa using hx`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h⟩`.

Introduce `h`. Conclude with `(one_lt_inv_iff₀.mp h).2`.
-/
private theorem valuation_lt_one_iff_inv_not_mem {K : Type} [Field K] (A : ValuationSubring K) (x : K) (hx : x ≠ 0) :
    A.valuation x < 1 ↔ x⁻¹ ∉ A := by
  rw [← A.valuation_le_one_iff, map_inv₀, not_le]
  have h0 : A.valuation x ≠ 0 := by simpa using hx
  constructor
  · intro h
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h⟩
  · intro h
    exact (one_lt_inv_iff₀.mp h).2

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Establish `hfx : f x ≠ 0` using `(map_ne_zero f).mpr hx`. Rewrite using `[valuation_lt_one_iff_inv_not_mem _ x hx, valuation_lt_one_iff_inv_not_mem _ (f x) hfx, ← map_inv₀]`.

Conclude with `Iff.rfl`.
-/
private theorem comap_lt_one {K L : Type} [Field K] [Field L] (B : ValuationSubring L) (f : K →+* L) (x : K) :
    (B.comap f).valuation x < 1 ↔ B.valuation (f x) < 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hfx : f x ≠ 0 := (map_ne_zero f).mpr hx
  rw [valuation_lt_one_iff_inv_not_mem _ x hx, valuation_lt_one_iff_inv_not_mem _ (f x) hfx, ← map_inv₀]
  exact Iff.rfl

/- English proof (translation)
Introduce `Ω _ _ _ ε X m hm τ s hA σ hσ u v P hP`. Take `⟨-, -, -, -, -, hU, -, -⟩` from `admB Ω ε X`. Establish `ka1` using `(kaB Ω ε X m hm P.a u hP.hu.1 hP.ha).2.2.2.2.1 σ τ s hA hσ`. Establish `ka2` using `(kaB Ω ε X m hm P.b v hP.hv.1 hP.hb).2.2.2.2.1 σ τ s hA hσ`. Use `⟨(hU τ s hA).1 u hP.hu, (hU τ s hA).1 v hP.hv, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show σ P.a ^ m = _`. Rewrite using `[← map_pow, hP.ha, hσ]`. Use `show σ P.b ^ m = _`. Rewrite using `[← map_pow, hP.hb, hσ]`. Introduce `g h hg hh show ka X m (σ P.a) g * ka X m (σ P.b) h = cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) - cyc m s ^ 2 * P.η (σ⁻¹ * (g * h) * σ) + cyc m s ^ 2 * P.η (σ⁻¹ * g * σ)`.

Establish `e : σ⁻¹ * (g * h) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * h * σ)` using `by group`. Establish `c` using `hP.cob _ _ (ka1 g hg).1 (ka1 h hh).1`. Rewrite using `[(ka1 g hg).2, (ka2 h hh).2, e]`. Take the linear combination `(cyc m s) ^ 2 * c`. Take `⟨B, hB⟩` from `hP.lc`.

Use `⟨B.image σ, fun h h' hh hh' e => ?_⟩` and prove the remaining obligations. Use `show cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) = cyc m s ^ 2 * P.η (σ⁻¹ * h' * σ)`. Rewrite using `[hB _ _ (ka1 h hh).1 (ka1 h' hh').1]`. Introduce `b hb`. Use `show σ⁻¹ (h (σ b)) = σ⁻¹ (h' (σ b))`.

Rewrite using `[e _ (Finset.mem_image_of_mem _ hb)]`. Introduce `B h hB hh hz show cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) = 0`. Rewrite using `[hP.unr (B.comap (σ : Kb X →+* Kb X)) _ ?_ (ka1 h hh).1 ?_, mul_zero]`. Establish `e : (B.comap (σ : Kb X →+* Kb X)).comap (io X) = (B.comap (io X)).comap (τ : X.K →+* X.K)`. Use extensionality with `f`.

Simplify using `only [ValuationSubring.mem_comap, RingHom.coe_coe]`. Rewrite using `[hσ]`. Rewrite using `[e]`. Conclude with `(hA.2 _).1 hB`. Introduce `z h1`.

Rewrite `h1` using `[ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap, ← ValuationSubring.valuation_le_one_iff]`. Rewrite using `[comap_lt_one]`. Use `hz _ h1` as an intermediate fact. Establish `e : (σ : Kb X →+* Kb X) ((σ⁻¹ * h * σ) z - z) = h ((σ : Kb X →+* Kb X) z) - (σ : Kb X →+* Kb X) z`. Rewrite using `[map_sub]`.

Use `congr 1`. Conclude with `σ.apply_symm_apply _`. Rewrite using `[e]`. Conclude with `this`.
-/
theorem UpperTheory.V.Z.Kato.Sym.mvPt :
    UpperTheory.V.Z.Kato.Sym.MvPt := by
  classical
  intro Ω _ _ _ ε X m hm τ s hA σ hσ u v P hP
  obtain ⟨-, -, -, -, -, hU, -, -⟩ := admB Ω ε X
  have ka1 := (kaB Ω ε X m hm P.a u hP.hu.1 hP.ha).2.2.2.2.1 σ τ s hA hσ
  have ka2 := (kaB Ω ε X m hm P.b v hP.hv.1 hP.hb).2.2.2.2.1 σ τ s hA hσ
  refine ⟨(hU τ s hA).1 u hP.hu, (hU τ s hA).1 v hP.hv, ?_, ?_, ?_, ?_, ?_⟩
  · show σ P.a ^ m = _
    rw [← map_pow, hP.ha, hσ]
  · show σ P.b ^ m = _
    rw [← map_pow, hP.hb, hσ]
  · intro g h hg hh
    show ka X m (σ P.a) g * ka X m (σ P.b) h =
      cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) - cyc m s ^ 2 * P.η (σ⁻¹ * (g * h) * σ) + cyc m s ^ 2 * P.η (σ⁻¹ * g * σ)
    have e : σ⁻¹ * (g * h) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * h * σ) := by group
    have c := hP.cob _ _ (ka1 g hg).1 (ka1 h hh).1
    rw [(ka1 g hg).2, (ka2 h hh).2, e]
    linear_combination (cyc m s) ^ 2 * c
  · obtain ⟨B, hB⟩ := hP.lc
    refine ⟨B.image σ, fun h h' hh hh' e => ?_⟩
    show cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) = cyc m s ^ 2 * P.η (σ⁻¹ * h' * σ)
    rw [hB _ _ (ka1 h hh).1 (ka1 h' hh').1]
    intro b hb
    show σ⁻¹ (h (σ b)) = σ⁻¹ (h' (σ b))
    rw [e _ (Finset.mem_image_of_mem _ hb)]
  · intro B h hB hh hz
    show cyc m s ^ 2 * P.η (σ⁻¹ * h * σ) = 0
    rw [hP.unr (B.comap (σ : Kb X →+* Kb X)) _ ?_ (ka1 h hh).1 ?_, mul_zero]
    · have e : (B.comap (σ : Kb X →+* Kb X)).comap (io X) = (B.comap (io X)).comap (τ : X.K →+* X.K) := by
        ext f
        simp only [ValuationSubring.mem_comap, RingHom.coe_coe]
        rw [hσ]
      rw [e]
      exact (hA.2 _).1 hB
    · intro z h1
      rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap, ← ValuationSubring.valuation_le_one_iff] at h1
      rw [comap_lt_one]
      have := hz _ h1
      have e : (σ : Kb X →+* Kb X) ((σ⁻¹ * h * σ) z - z) = h ((σ : Kb X →+* Kb X) z) - (σ : Kb X →+* Kb X) z := by
        rw [map_sub]
        congr 1
        exact σ.apply_symm_apply _
      rw [e]
      exact this
