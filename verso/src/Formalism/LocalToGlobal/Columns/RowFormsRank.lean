import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

open Classical in

def GSD.orbFun (d : S.D) (v : S.V) (x : S.D) : S.V := if hx : ∃ g : S.G, g • d = x then S.ρ hx.choose v else 0

variable {S}

/- English proof (translation)
Establish `h1 : (g₂⁻¹ * g₁) • d = d` using `by rw [mul_smul, e, inv_smul_smul]`. Establish `h2 : S.ρ g₁ = S.ρ g₂ * S.ρ (g₂⁻¹ * g₁)` using `by rw [← map_mul, mul_inv_cancel_left]`. Rewrite using `[h2, Module.End.mul_apply, hv _ h1]`.
-/
theorem GSD.rho_eq_of_fixed {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) {g₁ g₂ : S.G}
    (e : g₁ • d = g₂ • d) : S.ρ g₁ v = S.ρ g₂ v := by
  have h1 : (g₂⁻¹ * g₁) • d = d := by rw [mul_smul, e, inv_smul_smul]
  have h2 : S.ρ g₁ = S.ρ g₂ * S.ρ (g₂⁻¹ * g₁) := by rw [← map_mul, mul_inv_cancel_left]
  rw [h2, Module.End.mul_apply, hv _ h1]

/- English proof (translation)
Establish `hx : ∃ g' : S.G, g' • d = g • d` using `⟨g, rfl⟩`. Unfold `GSD.orbFun`. Rewrite using `[dif_pos hx]`. Conclude with `GSD.rho_eq_of_fixed hv hx.choose_spec`.
-/
theorem GSD.orbFun_smul {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) (g : S.G) :
    S.orbFun d v (g • d) = S.ρ g v := by
  have hx : ∃ g' : S.G, g' • d = g • d := ⟨g, rfl⟩
  unfold GSD.orbFun
  rw [dif_pos hx]
  exact GSD.rho_eq_of_fixed hv hx.choose_spec

/- English proof (translation)
Introduce `g x`. Distinguish the cases in `hx : ∃ g' : S.G, g' • d = x`. Take `⟨g', rfl⟩` from `hx`. Rewrite using `[← mul_smul, GSD.orbFun_smul hv, GSD.orbFun_smul hv, map_mul, Module.End.mul_apply]`. Establish `hx' : ¬ ∃ g' : S.G, g' • d = g • x`.

Introduce and unpack `⟨g', e⟩`. Conclude with `hx ⟨g⁻¹ * g', by rw [mul_smul, e, inv_smul_smul]⟩`. Unfold `GSD.orbFun`. Rewrite using `[dif_neg hx, dif_neg hx', map_zero]`.
-/
theorem GSD.orbFun_mem {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) : S.orbFun d v ∈ S.EqFun := by
  intro g x
  by_cases hx : ∃ g' : S.G, g' • d = x
  · obtain ⟨g', rfl⟩ := hx
    rw [← mul_smul, GSD.orbFun_smul hv, GSD.orbFun_smul hv, map_mul, Module.End.mul_apply]
  · have hx' : ¬ ∃ g' : S.G, g' • d = g • x := by
      rintro ⟨g', e⟩
      exact hx ⟨g⁻¹ * g', by rw [mul_smul, e, inv_smul_smul]⟩
    unfold GSD.orbFun
    rw [dif_neg hx, dif_neg hx', map_zero]

/- English proof (translation)
Use `S.finiteDimensional_EqFun h` as an intermediate fact. Rewrite using `[Module.finrank_pos_iff_exists_ne_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ, hφ⟩`. Establish `: ∃ d, (φ : S.D → S.V) d ≠ 0`.

Assume the negation of the conclusion as `hc`. Conclude with `hφ (Subtype.ext (funext fun d => by`. Assume the negation of the conclusion as `hd`. Conclude with `hc ⟨d, hd⟩))`. Take `⟨d, hd⟩` from `this`.

Use `⟨d, _, hd, fun g hg => ?_⟩` and prove the remaining obligations. Use `φ.2 g d` as an intermediate fact. Rewrite `this` using `[hg]`. Conclude with `this.symm`. Introduce and unpack `⟨d, v, hv0, hv⟩`.

Use `⟨⟨S.orbFun d v, GSD.orbFun_mem hv⟩, fun e => hv0 ?_⟩` and prove the remaining obligations. Establish `h1 : S.orbFun d v ((1 : S.G) • d) = 0` using `congrFun (congrArg Subtype.val e) ((1 : S.G) • d)`. Rewrite `h1` using `[GSD.orbFun_smul hv, map_one]`. Conclude with `h1`.
-/
theorem GSD.finrank_pos_iff (h : S.Ok) :
    0 < finrank K S.EqFun ↔ ∃ (d : S.D) (v : S.V), v ≠ 0 ∧ ∀ g : S.G, g • d = d → S.ρ g v = v := by
  have := S.finiteDimensional_EqFun h
  rw [Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨φ, hφ⟩
    have : ∃ d, (φ : S.D → S.V) d ≠ 0 := by
      by_contra hc
      exact hφ (Subtype.ext (funext fun d => by
        by_contra hd
        exact hc ⟨d, hd⟩))
    obtain ⟨d, hd⟩ := this
    refine ⟨d, _, hd, fun g hg => ?_⟩
    have := φ.2 g d
    rw [hg] at this
    exact this.symm
  · rintro ⟨d, v, hv0, hv⟩
    refine ⟨⟨S.orbFun d v, GSD.orbFun_mem hv⟩, fun e => hv0 ?_⟩
    have h1 : S.orbFun d v ((1 : S.G) • d) = 0 := congrFun (congrArg Subtype.val e) ((1 : S.G) • d)
    rw [GSD.orbFun_smul hv, map_one] at h1
    exact h1

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def RowsNonzero (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  0 < finrank X.K (MtildeV W Ch sel mu P) ∧ ∀ j, 1 ≤ j → j ≤ R.m → 0 < finrank X.K (MtV W Ch sel mu P j)

end Rows

end Formalism.L2.Col
