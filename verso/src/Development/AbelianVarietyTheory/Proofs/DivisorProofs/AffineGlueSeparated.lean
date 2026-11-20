import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue

set_option autoImplicit false

namespace GlobalTheory.AffGlue

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem eq_zero_of_cover_zero : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ x : D.M V hV, (∀ i, D.ρ hV (hW i) (hWV i) x = 0) → x = 0 := by
  intro T D V hV ι W hW hWV hcov x hx
  let J : Ideal Γ(T, V) := LinearMap.ker (LinearMap.toSpanSingleton Γ(T, V) (D.M V hV) x)
  have hJ : ∀ a : Γ(T, V), a ∈ J ↔ a • x = 0 := fun a => by
    simp [J, LinearMap.toSpanSingleton_apply]
  let s : Set Γ(T, V) := {f | ∃ n : ℕ, f ^ n • x = 0}
  have hs : V ≤ ⨆ f : s, T.basicOpen f.1 := by
    intro y hy
    have hy' : y ∈ ⨆ i, W i := hcov hy
    rw [TopologicalSpace.Opens.mem_iSup] at hy'
    obtain ⟨i, hi⟩ := hy'
    obtain ⟨f, hfle, hyf⟩ := hV.exists_basicOpen_le (V := W i) ⟨y, hi⟩ hy
    have hD : IsAffineOpen (T.basicOpen f) := hV.basicOpen f
    have h0 : D.ρ hV hD (T.basicOpen_le f) x = 0 := by
      have := D.ρ_ρ hV (hW i) hD (hWV i) hfle x
      rw [hx i, map_zero] at this
      exact this.symm
    obtain ⟨n, hn⟩ := D.loc_inj hV f hD x h0
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨f, n, hn⟩, hyf⟩
  have hspan : Ideal.span s = ⊤ := (hV.self_le_iSup_basicOpen_iff).mp hs
  have hrad : J.radical = ⊤ := by
    rw [eq_top_iff, ← hspan, Ideal.span_le]
    rintro f ⟨n, hn⟩
    exact ⟨n, (hJ _).mpr hn⟩
  have h1 : (1 : Γ(T, V)) ∈ J := by
    rw [Ideal.radical_eq_top] at hrad
    rw [hrad]; trivial
  simpa using (hJ 1).mp h1

end GlobalTheory.AffGlue
