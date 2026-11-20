import Development.EtaleCohomology.EtaleSheaves.HZeroPf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace LateralTheory.E.RootAICPf

open LateralTheory.E.t_E2Cut

/- English proof (translation)
Rewrite using `[← map_cyclotomic q φ, Polynomial.eval_map, Polynomial.eval₂_hom]`.
-/
theorem evalMap {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) (q : ℕ) (a : R) :
    φ ((cyclotomic q R).eval a) = (cyclotomic q K).eval (φ a) := by
  rw [← map_cyclotomic q φ, Polynomial.eval_map, Polynomial.eval₂_hom]

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`.
-/
theorem aeval_eq {R : Type} [CommRing R] (q : ℕ) (a : R) :
    aeval a (cyclotomic q ℤ) = (cyclotomic q R).eval a := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

/- English proof (translation)
Establish `hA` using `hX.2 V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)`. Take `⟨a, ha⟩` from `hA (cyclotomic q Γ(X, V)) (cyclotomic.monic q _) (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `: NeZero ((q : ℕ) : X.functionField)` using `⟨hK⟩`. Rewrite using `[← isRoot_cyclotomic_iff]`.

Use `show (cyclotomic q _).eval _ = 0`. Rewrite using `[← evalMap, ha, map_zero]`.
-/
theorem localRoot {q : ℕ} {X : Scheme.{0}} [IsIntegral X] (hX : AICSch X) (hq : q ≠ 0)
    (hK : ((q : ℕ) : X.functionField) ≠ 0) (V : X.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ ζ : Γ(X, V), IsPrimitiveRoot (X.germToFunctionField V ζ) q := by
  have hA := hX.2 V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)
  obtain ⟨a, ha⟩ := hA (cyclotomic q Γ(X, V)) (cyclotomic.monic q _)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
  refine ⟨a, ?_⟩
  have : NeZero ((q : ℕ) : X.functionField) := ⟨hK⟩
  rw [← isRoot_cyclotomic_iff]
  show (cyclotomic q _).eval _ = 0
  rw [← evalMap, ha, map_zero]

/- English proof (translation)
Introduce `q X hX hq`. Use `haveI := hX.1`. Take `⟨x0⟩ : Nonempty X` from `inferInstance`. Use `haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x0, trivial⟩⟩`. Establish `hK : ((q : ℕ) : X.functionField) ≠ 0`.

Introduce `h`. Use `hq.map (X.germToFunctionField ⊤).hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Rewrite `this` using `[h]`. Conclude with `not_isUnit_zero this`.

Establish `hq0 : q ≠ 0` using `by rintro rfl; exact hK (by simp)`. Use `haveI : NeZero q := ⟨hq0⟩`. Establish `hnb : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V` using `fun x => by`. Take `⟨V, hV, hx, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)`. Conclude with `⟨V, hV, hx⟩`.

Take `⟨V0, hV0, hx0⟩` from `hnb x0`. Use `haveI : Nonempty V0 := ⟨⟨x0, hx0⟩⟩`. Take `⟨ζ0, hζ0⟩` from `localRoot hX hq0 hK V0 hV0`. Take `⟨s, hs⟩` from `GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally (⊤ : X.Opens) (X.germToFunctionField V0 ζ0) (fun x _ => by`. Take `⟨V, hV, hx⟩` from `hnb x`.

Use `haveI hne : Nonempty V := ⟨⟨x, hx⟩⟩`. Take `⟨ζ, hζ⟩` from `localRoot hX hq0 hK V hV`. Take `⟨k, -, hk⟩` from `hζ.eq_pow_of_pow_eq_one hζ0.pow_eq_one`. Conclude with `⟨V, hne, ζ ^ k, hx, le_top, by rw [map_pow]; exact hk⟩)`. Use `⟨⟨s, hq, ?_⟩⟩` and prove the remaining obligations.

Apply `Scheme.germToFunctionField_injective X ⊤` to reduce the goal to its premises. Establish `: NeZero ((q : ℕ) : X.functionField)` using `⟨hK⟩`. Rewrite using `[aeval_eq, map_zero]`. Use `show (X.germToFunctionField ⊤).hom _ = 0`. Rewrite using `[evalMap]`.

Use `show (cyclotomic q _).eval ((X.germToFunctionField ⊤) s) = 0`. Rewrite using `[hs]`. Conclude with `(isRoot_cyclotomic_iff.mpr hζ0)`.
-/
theorem RootAIC_of : LateralTheory.E.HZeroPf.RootAIC := by
  intro q X hX hq
  haveI := hX.1
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x0, trivial⟩⟩
  have hK : ((q : ℕ) : X.functionField) ≠ 0 := by
    intro h
    have := hq.map (X.germToFunctionField ⊤).hom
    rw [map_natCast] at this
    rw [h] at this
    exact not_isUnit_zero this
  have hq0 : q ≠ 0 := by rintro rfl; exact hK (by simp)
  haveI : NeZero q := ⟨hq0⟩
  have hnb : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hx⟩
  obtain ⟨V0, hV0, hx0⟩ := hnb x0
  haveI : Nonempty V0 := ⟨⟨x0, hx0⟩⟩
  obtain ⟨ζ0, hζ0⟩ := localRoot hX hq0 hK V0 hV0
  obtain ⟨s, hs⟩ := GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally (⊤ : X.Opens)
    (X.germToFunctionField V0 ζ0) (fun x _ => by
      obtain ⟨V, hV, hx⟩ := hnb x
      haveI hne : Nonempty V := ⟨⟨x, hx⟩⟩
      obtain ⟨ζ, hζ⟩ := localRoot hX hq0 hK V hV
      obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hζ0.pow_eq_one
      exact ⟨V, hne, ζ ^ k, hx, le_top, by rw [map_pow]; exact hk⟩)
  refine ⟨⟨s, hq, ?_⟩⟩
  apply Scheme.germToFunctionField_injective X ⊤
  have : NeZero ((q : ℕ) : X.functionField) := ⟨hK⟩
  rw [aeval_eq, map_zero]
  show (X.germToFunctionField ⊤).hom _ = 0
  rw [evalMap]
  show (cyclotomic q _).eval ((X.germToFunctionField ⊤) s) = 0
  rw [hs]
  exact (isRoot_cyclotomic_iff.mpr hζ0)

end LateralTheory.E.RootAICPf
