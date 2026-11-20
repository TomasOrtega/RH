import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue

set_option autoImplicit false

namespace GlobalTheory.AffGlue

/- English proof (translation)
Introduce `T D V hV ι W hW hWV hcov x hx`. Set `J : Ideal Γ(T, V)` to `LinearMap.ker (LinearMap.toSpanSingleton Γ(T, V) (D.M V hV) x)`. Establish `hJ : ∀ a : Γ(T, V), a ∈ J ↔ a • x = 0` using `fun a => by`. Simplify using `[J, LinearMap.toSpanSingleton_apply]`. Set `s : Set Γ(T, V)` to `{f | ∃ n : ℕ, f ^ n • x = 0}`.

Establish `hs : V ≤ ⨆ f : s, T.basicOpen f.1`. Introduce `y hy`. Establish `hy' : y ∈ ⨆ i, W i` using `hcov hy`. Rewrite `hy'` using `[TopologicalSpace.Opens.mem_iSup]`. Take `⟨i, hi⟩` from `hy'`.

Take `⟨f, hfle, hyf⟩` from `hV.exists_basicOpen_le (V := W i) ⟨y, hi⟩ hy`. Establish `hD : IsAffineOpen (T.basicOpen f)` using `hV.basicOpen f`. Establish `h0 : D.ρ hV hD (T.basicOpen_le f) x = 0`. Use `D.ρ_ρ hV (hW i) hD (hWV i) hfle x` as an intermediate fact. Rewrite `this` using `[hx i, map_zero]`.

Conclude with `this.symm`. Take `⟨n, hn⟩` from `D.loc_inj hV f hD x h0`. Rewrite using `[TopologicalSpace.Opens.mem_iSup]`. Conclude with `⟨⟨f, n, hn⟩, hyf⟩`. Establish `hspan : Ideal.span s = ⊤` using `(hV.self_le_iSup_basicOpen_iff).mp hs`.

Establish `hrad : J.radical = ⊤`. Rewrite using `[eq_top_iff, ← hspan, Ideal.span_le]`. Introduce and unpack `f ⟨n, hn⟩`. Conclude with `⟨n, (hJ _).mpr hn⟩`. Establish `h1 : (1 : Γ(T, V)) ∈ J`.

Rewrite `hrad` using `[Ideal.radical_eq_top]`. Rewrite using `[hrad]`. Discharge the goal by the elementary cases of `trivial`. Simplify using `using (hJ 1).mp h1`.
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
