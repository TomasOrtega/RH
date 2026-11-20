import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

universe u

namespace GlobalTheory

open Submodule

/- English proof (translation)
Introduce `R _ H _ _ O _ ρ bar φ e he hρe hbar hφρ hφe hbij hrefl G M hGM hGMr hGst E`. Establish `hee : ∀ x, e (e x) = e x` using `fun x => by`. Use `LinearMap.congr_fun he x` as an intermediate fact. Simplify using `using this`. Establish `hrange : ∀ r ∈ LinearMap.range e, e r = r`.

Introduce and unpack `r ⟨y, rfl⟩`. Conclude with `hee y`. Establish `hG : ∀ g ∈ G, e g = g` using `fun g hg => hrange g (hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg)`. Establish `hM : ∀ m ∈ M, e m = m` using `fun m hm => hrange m (hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm)`. Establish `hrr : ∀ x y, φ (e x) (e y) = 0` using `fun x y => by rw [hφe, hee, sub_self, map_zero]`.

Establish `hkk : ∀ k ∈ LinearMap.ker e, ∀ k' ∈ LinearMap.ker e, φ k k' = 0`. Introduce `k hk k' hk'`. Rewrite `hk`, `hk'` using `[LinearMap.mem_ker]`. Use `hφe k k'` as an intermediate fact. Rewrite `this` using `[hk, hk', sub_zero, map_zero, LinearMap.zero_apply]`.

Conclude with `this.symm`. Establish `memPerp : ∀ (S : Submodule R H) y, y ∈ (⨅ x ∈ S, LinearMap.ker (φ x)) ↔ ∀ x ∈ S, φ x y = 0`. Introduce `S y`. Simplify using `[Submodule.mem_iInf]`. Use `set S := LinearMap.range e with hS`.

Establish `hc : IsCompl (M.comap S.subtype) (G.comap S.subtype)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxM hxG`. Establish `: (x : H) ∈ G ⊓ M` using `⟨hxG, hxM⟩`.

Rewrite `this` using `[hGM, Submodule.mem_bot]`. Conclude with `Subtype.ext this`. Rewrite using `[codisjoint_iff, Submodule.eq_top_iff']`. Introduce `x`. Establish `hx : (x : H) ∈ G ⊔ M` using `by rw [hGMr]; exact x.2`.

Take `⟨g, hg, m, hm, hgm⟩` from `Submodule.mem_sup.1 hx`. Establish `hgS : g ∈ S` using `hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg`. Establish `hmS : m ∈ S` using `hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm`. Establish `: x = ⟨m, hmS⟩ + ⟨g, hgS⟩` using `Subtype.ext (by simp [← hgm, add_comm])`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem_sup (by simpa using hm) (by simpa using hg)`. Set `P : H →ₗ[R] H` to `S.subtype ∘ₗ (M.comap S.subtype).subtype ∘ₗ (Submodule.linearProjOfIsCompl _ _ hc) ∘ₗ e.rangeRestrict`. Establish `hPG : ∀ g ∈ G, P g = 0`. Introduce `g hg`. Establish `h1 : e.rangeRestrict g ∈ G.comap S.subtype` using `by show e g ∈ G; rw [hG g hg]; exact hg`.

Simplify using `only [P, LinearMap.coe_comp, Function.comp_apply]`. Establish `h2` using `Submodule.linearProjOfIsCompl_apply_right hc ⟨_, h1⟩`. Use `erw [h2]`. Simplify using the standard rewrite rules. Establish `hPM : ∀ m ∈ M, P m = m`.

Introduce `m hm`. Establish `h1 : e.rangeRestrict m ∈ M.comap S.subtype` using `by show e m ∈ M; rw [hM m hm]; exact hm`. Simplify using `only [P, LinearMap.coe_comp, Function.comp_apply]`. Establish `h2` using `Submodule.linearProjOfIsCompl_apply_left hc ⟨_, h1⟩`. Use `erw [h2]`.

Simplify using `[hM m hm]`. Use `set K := LinearMap.ker e with hK`. Establish `hker : ∀ x, x - e x ∈ K` using `fun x => by`. Rewrite using `[hK, LinearMap.mem_ker, map_sub, hee, sub_self]`. Establish `hdec : ∀ k ∈ K, ∃ k₂ ∈ K ⊓ (⨅ x ∈ G, LinearMap.ker (φ x)), k - k₂ ∈ K ⊓ (⨅ x ∈ M, LinearMap.ker (φ x))`.

Introduce `k hk`. Take `⟨x, hx⟩` from `hbij.2 ((φ k).comp P)`. Establish `hx' : ∀ r ∈ S, φ (x - e x) r = φ k (P r)`. Introduce `r hr`. Rewrite using `[map_sub, LinearMap.sub_apply, hφe, hrange r hr, sub_self, map_zero, sub_zero, hx]`.

Both sides reduce to the same expression. Use `⟨x - e x, ⟨hker x, ?_⟩, ⟨K.sub_mem hk (hker x), ?_⟩⟩` and prove the remaining obligations. Use `(memPerp _ _).2 ?_` and prove the remaining obligations. Introduce `g hg`. Apply `hrefl` to reduce the goal to its premises.

Rewrite using `[hx' g (hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg), hPG g hg, map_zero]`. Use `(memPerp _ _).2 ?_` and prove the remaining obligations. Introduce `m hm`. Apply `hrefl` to reduce the goal to its premises. Rewrite using `[map_sub, LinearMap.sub_apply, hx' m (hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm), hPM m hm, sub_self]`.

Establish `hzero : ∀ k ∈ K, k ∈ (⨅ x ∈ G, LinearMap.ker (φ x)) → k ∈ (⨅ x ∈ M, LinearMap.ker (φ x)) → k = 0`. Introduce `k hk hkG hkM`. Rewrite `hkG`, `hkM` using `[memPerp]`. Apply `hbij.1` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Use extensionality with `y`. Establish `hy : e y ∈ G ⊔ M` using `by rw [hGMr]; exact LinearMap.mem_range_self e y`. Take `⟨g, hg, m, hm, hgm⟩` from `Submodule.mem_sup.1 hy`. Establish `: y = g + m + (y - e y)` using `by rw [hgm]; abel`. Rewrite using `[this, map_add, map_add, hrefl _ _ (hkG g hg), hrefl _ _ (hkM m hm), hkk k hk _ (hker y)]`.

Simplify using the standard rewrite rules. Use `⟨⟨M ⊔ (K ⊓ ⨅ x ∈ M, LinearMap.ker (φ x)), ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxE hxN`. Take `⟨g, hg, k₁, hk₁, rfl⟩` from `Submodule.mem_sup.1 hxE`.

Take `⟨m, hm, k₂, hk₂, hmk⟩` from `Submodule.mem_sup.1 hxN`. Establish `he1 : e (g + k₁) = g` using `by rw [map_add, hG g hg, LinearMap.mem_ker.1 hk₁.1, add_zero]`. Establish `he2 : e (m + k₂) = m` using `by rw [map_add, hM m hm, LinearMap.mem_ker.1 hk₂.1, add_zero]`. Establish `hgm : g = m` using `by rw [← he1, ← he2, hmk]`. Establish `hg0 : g = 0`.

Establish `: g ∈ G ⊓ M` using `⟨hg, hgm ▸ hm⟩`. Rewrite `this` using `[hGM, Submodule.mem_bot]`. Then use the resulting hypothesis. Establish `hm0 : m = 0` using `hgm ▸ hg0`. Substitute `hg0` using the available equality. Substitute `hm0` using the available equality.

Rewrite `hmk`, the goal using `[zero_add]`. Rewrite `hmk` using `[zero_add]`. Conclude with `hzero k₁ hk₁.1 hk₁.2 (hmk ▸ hk₂.2)`. Rewrite using `[codisjoint_iff, Submodule.eq_top_iff']`. Introduce `h`.

Establish `hy : e h ∈ G ⊔ M` using `by rw [hGMr]; exact LinearMap.mem_range_self e h`. Take `⟨g, hg, m, hm, hgm⟩` from `Submodule.mem_sup.1 hy`. Take `⟨k₂, hk₂, hk₁⟩` from `hdec (h - e h) (hker h)`. Establish `: h = (g + k₂) + (m + (h - e h - k₂))` using `by rw [← sub_eq_zero, ← hgm]; abel`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem_sup (Submodule.add_mem_sup hg hk₂) (Submodule.add_mem_sup hm hk₁)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hxE, hxr⟩`. Take `⟨g, hg, k₁, hk₁, rfl⟩` from `Submodule.mem_sup.1 hxE`. Establish `h1` using `hrange _ hxr`.

Rewrite `h1` using `[map_add, hG g hg, LinearMap.mem_ker.1 hk₁.1, add_zero]`. Establish `: k₁ = 0`. Use `congrArg (· - g) h1` as an intermediate fact. Simplify using `using this.symm`. Rewrite using `[this, add_zero]`.

Conclude with `hg`. Conclude with `le_inf le_sup_left (hGMr ▸ le_sup_left)`. Introduce `x hx y hy`. Take `⟨g, hg, k, hk, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨g', hg', k', hk', rfl⟩` from `Submodule.mem_sup.1 hy`.

Establish `hkG` using `(memPerp G k).1 hk.2`. Establish `hk'G` using `(memPerp G k').1 hk'.2`. Establish `h1 : φ g g' = 0` using `by rw [← hG g hg, ← hG g' hg', hrr]`. Establish `h2 : φ g k' = 0` using `hk'G g hg`. Establish `h3 : φ k g' = 0` using `hrefl _ _ (hkG g' hg')`.

Establish `h4 : φ k k' = 0` using `hkk k hk.1 k' hk'.1`. Simplify using `[h1, h2, h3, h4]`. Introduce `a x hx`. Take `⟨g, hg, k, hk, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`.

Use `Submodule.add_mem_sup (hGst a g hg) ⟨?_, ?_⟩` and prove the remaining obligations. Use `show e (ρ a k) = 0`. Use `LinearMap.congr_fun (hρe a) k` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[← this, LinearMap.mem_ker.1 hk.1, map_zero]`.

Use `(memPerp _ _).2 ?_` and prove the remaining obligations. Introduce `g' hg'`. Use `hφρ (bar a) g' k` as an intermediate fact. Rewrite `this` using `[hbar]`. Rewrite using `[← this]`.

Conclude with `(memPerp G k).1 hk.2 _ (hGst _ g' hg')`.
-/
theorem lagrangian_of_idempotent_split_univ :
 ∀ (R : Type) [CommRing R] (H : Type u) [AddCommGroup H] [Module R H] (O : Type) [Ring O] (ρ : O →+* Module.End R H) (bar : O → O) (φ : LinearMap.BilinForm R H) (e : Module.End R H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → φ.IsRefl → ∀ G M : Submodule R H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → let E := G ⊔ (LinearMap.ker e ⊓ ⨅ x ∈ G, LinearMap.ker (φ x)); (∃ N : Submodule R H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ ∀ a, ∀ x ∈ E, ρ a x ∈ E := by
  intro R _ H _ _ O _ ρ bar φ e he hρe hbar hφρ hφe hbij hrefl G M hGM hGMr hGst E
  have hee : ∀ x, e (e x) = e x := fun x => by
    have := LinearMap.congr_fun he x
    simpa using this
  have hrange : ∀ r ∈ LinearMap.range e, e r = r := by
    rintro r ⟨y, rfl⟩; exact hee y
  have hG : ∀ g ∈ G, e g = g := fun g hg => hrange g (hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg)
  have hM : ∀ m ∈ M, e m = m := fun m hm => hrange m (hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm)
  have hrr : ∀ x y, φ (e x) (e y) = 0 := fun x y => by rw [hφe, hee, sub_self, map_zero]
  have hkk : ∀ k ∈ LinearMap.ker e, ∀ k' ∈ LinearMap.ker e, φ k k' = 0 := by
    intro k hk k' hk'
    rw [LinearMap.mem_ker] at hk hk'
    have := hφe k k'
    rw [hk, hk', sub_zero, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  have memPerp : ∀ (S : Submodule R H) y, y ∈ (⨅ x ∈ S, LinearMap.ker (φ x)) ↔ ∀ x ∈ S, φ x y = 0 := by
    intro S y; simp [Submodule.mem_iInf]

  set S := LinearMap.range e with hS
  have hc : IsCompl (M.comap S.subtype) (G.comap S.subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxM hxG
      have : (x : H) ∈ G ⊓ M := ⟨hxG, hxM⟩
      rw [hGM, Submodule.mem_bot] at this
      exact Subtype.ext this
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro x
      have hx : (x : H) ∈ G ⊔ M := by rw [hGMr]; exact x.2
      obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hx
      have hgS : g ∈ S := hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg
      have hmS : m ∈ S := hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm
      have : x = ⟨m, hmS⟩ + ⟨g, hgS⟩ := Subtype.ext (by simp [← hgm, add_comm])
      rw [this]
      exact Submodule.add_mem_sup (by simpa using hm) (by simpa using hg)
  let P : H →ₗ[R] H := S.subtype ∘ₗ (M.comap S.subtype).subtype ∘ₗ
    (Submodule.linearProjOfIsCompl _ _ hc) ∘ₗ e.rangeRestrict
  have hPG : ∀ g ∈ G, P g = 0 := by
    intro g hg
    have h1 : e.rangeRestrict g ∈ G.comap S.subtype := by
      show e g ∈ G; rw [hG g hg]; exact hg
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_right hc ⟨_, h1⟩
    erw [h2]
    simp
  have hPM : ∀ m ∈ M, P m = m := by
    intro m hm
    have h1 : e.rangeRestrict m ∈ M.comap S.subtype := by
      show e m ∈ M; rw [hM m hm]; exact hm
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_left hc ⟨_, h1⟩
    erw [h2]
    simp [hM m hm]

  set K := LinearMap.ker e with hK
  have hker : ∀ x, x - e x ∈ K := fun x => by
    rw [hK, LinearMap.mem_ker, map_sub, hee, sub_self]

  have hdec : ∀ k ∈ K, ∃ k₂ ∈ K ⊓ (⨅ x ∈ G, LinearMap.ker (φ x)),
      k - k₂ ∈ K ⊓ (⨅ x ∈ M, LinearMap.ker (φ x)) := by
    intro k hk
    obtain ⟨x, hx⟩ := hbij.2 ((φ k).comp P)
    have hx' : ∀ r ∈ S, φ (x - e x) r = φ k (P r) := by
      intro r hr
      rw [map_sub, LinearMap.sub_apply, hφe, hrange r hr, sub_self, map_zero, sub_zero, hx]
      rfl
    refine ⟨x - e x, ⟨hker x, ?_⟩, ⟨K.sub_mem hk (hker x), ?_⟩⟩
    · refine (memPerp _ _).2 ?_
      intro g hg
      apply hrefl
      rw [hx' g (hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg), hPG g hg, map_zero]
    · refine (memPerp _ _).2 ?_
      intro m hm
      apply hrefl
      rw [map_sub, LinearMap.sub_apply, hx' m (hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm), hPM m hm,
        sub_self]
  have hzero : ∀ k ∈ K, k ∈ (⨅ x ∈ G, LinearMap.ker (φ x)) → k ∈ (⨅ x ∈ M, LinearMap.ker (φ x)) → k = 0 := by
    intro k hk hkG hkM
    rw [memPerp] at hkG hkM
    apply hbij.1
    rw [map_zero]
    ext y
    have hy : e y ∈ G ⊔ M := by rw [hGMr]; exact LinearMap.mem_range_self e y
    obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hy
    have : y = g + m + (y - e y) := by rw [hgm]; abel
    rw [this, map_add, map_add, hrefl _ _ (hkG g hg), hrefl _ _ (hkM m hm),
      hkk k hk _ (hker y)]
    simp
  refine ⟨⟨M ⊔ (K ⊓ ⨅ x ∈ M, LinearMap.ker (φ x)), ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxE hxN
    obtain ⟨g, hg, k₁, hk₁, rfl⟩ := Submodule.mem_sup.1 hxE
    obtain ⟨m, hm, k₂, hk₂, hmk⟩ := Submodule.mem_sup.1 hxN
    have he1 : e (g + k₁) = g := by rw [map_add, hG g hg, LinearMap.mem_ker.1 hk₁.1, add_zero]
    have he2 : e (m + k₂) = m := by rw [map_add, hM m hm, LinearMap.mem_ker.1 hk₂.1, add_zero]
    have hgm : g = m := by rw [← he1, ← he2, hmk]
    have hg0 : g = 0 := by
      have : g ∈ G ⊓ M := ⟨hg, hgm ▸ hm⟩
      rwa [hGM, Submodule.mem_bot] at this
    have hm0 : m = 0 := hgm ▸ hg0
    subst hg0; subst hm0
    rw [zero_add] at hmk ⊢
    rw [zero_add] at hmk
    exact hzero k₁ hk₁.1 hk₁.2 (hmk ▸ hk₂.2)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro h
    have hy : e h ∈ G ⊔ M := by rw [hGMr]; exact LinearMap.mem_range_self e h
    obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hy
    obtain ⟨k₂, hk₂, hk₁⟩ := hdec (h - e h) (hker h)
    have : h = (g + k₂) + (m + (h - e h - k₂)) := by rw [← sub_eq_zero, ← hgm]; abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hg hk₂) (Submodule.add_mem_sup hm hk₁)
  · apply le_antisymm
    · rintro x ⟨hxE, hxr⟩
      obtain ⟨g, hg, k₁, hk₁, rfl⟩ := Submodule.mem_sup.1 hxE
      have h1 := hrange _ hxr
      rw [map_add, hG g hg, LinearMap.mem_ker.1 hk₁.1, add_zero] at h1
      have : k₁ = 0 := by
        have := congrArg (· - g) h1
        simpa using this.symm
      rw [this, add_zero]; exact hg
    · exact le_inf le_sup_left (hGMr ▸ le_sup_left)
  · intro x hx y hy
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨g', hg', k', hk', rfl⟩ := Submodule.mem_sup.1 hy
    have hkG := (memPerp G k).1 hk.2
    have hk'G := (memPerp G k').1 hk'.2
    have h1 : φ g g' = 0 := by rw [← hG g hg, ← hG g' hg', hrr]
    have h2 : φ g k' = 0 := hk'G g hg
    have h3 : φ k g' = 0 := hrefl _ _ (hkG g' hg')
    have h4 : φ k k' = 0 := hkk k hk.1 k' hk'.1
    simp [h1, h2, h3, h4]
  · intro a x hx
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    refine Submodule.add_mem_sup (hGst a g hg) ⟨?_, ?_⟩
    · show e (ρ a k) = 0
      have := LinearMap.congr_fun (hρe a) k
      simp only [Module.End.mul_apply] at this
      rw [← this, LinearMap.mem_ker.1 hk.1, map_zero]
    · refine (memPerp _ _).2 ?_
      intro g' hg'
      have := hφρ (bar a) g' k
      rw [hbar] at this
      rw [← this]
      exact (memPerp G k).1 hk.2 _ (hGst _ g' hg')

/- English proof (translation)
Introduce `C _ I H _ _ _ _ O _ ρ bar φ e he hρe hskew hbar hφρ hφe hbij F hIF hFiso hFlag hFe G M hGM hGMr hGst hGF`. Establish `hrefl : φ.IsRefl` using `fun x y h => by rw [hskew, h, neg_zero]`. Establish `key` using `lagrangian_of_idempotent_split_univ C H O ρ bar φ e he hρe hbar hφρ hφe hbij hrefl G M hGM hGMr hGst`. Simplify using `only at key`. Take `⟨hcompl, hEr, hiso, hEst⟩` from `key`.

Establish `hee : ∀ x, e (e x) = e x` using `fun x => by`. Use `LinearMap.congr_fun he x` as an intermediate fact. Simplify using `using this`. Establish `hker : ∀ x, e (x - e x) = 0` using `fun x => by rw [map_sub, hee, sub_self]`. Establish `hrange : ∀ r ∈ LinearMap.range e, e r = r`.

Introduce and unpack `r ⟨y, rfl⟩`. Conclude with `hee y`. Establish `hGr : G ≤ LinearMap.range e` using `hGMr ▸ (le_sup_left : G ≤ G ⊔ M)`. Establish `hG : ∀ g ∈ G, e g = g` using `fun g hg => hrange g (hGr hg)`. Establish `hkk : ∀ k k', e k = 0 → e k' = 0 → φ k k' = 0`.

Introduce `k k' hk hk'`. Use `hφe k k'` as an intermediate fact. Rewrite `this` using `[hk, hk', sub_zero, map_zero, LinearMap.zero_apply]`. Conclude with `this.symm`. Establish `hIfun : ∀ (f : H →ₗ[C] C), ∀ t ∈ (I • ⊤ : Submodule C H), f t ∈ I`.

Introduce `f t ht`. Establish `hle : (I • ⊤ : Submodule C H) ≤ Submodule.comap f (show Submodule C C from I)`. Use `Submodule.smul_le.2 ?_` and prove the remaining obligations. Introduce `r hr n _`. Use `show f (r • n) ∈ I`.

Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `I.mul_mem_right _ hr`. Conclude with `hle ht`. Establish `memPerp : ∀ y, y ∈ (⨅ x ∈ G, LinearMap.ker (φ x)) ↔ ∀ x ∈ G, φ x y = 0`. Introduce `y`.

Simplify using `[Submodule.mem_iInf]`. Establish `hGF' : G ≤ F` using `le_trans le_sup_left (hGF.le.trans inf_le_left)`. Establish `hdecomp : ∀ z ∈ F, ∃ g ∈ G, ∃ t ∈ (I • ⊤ : Submodule C H), g + t = e z`. Introduce `z hz`. Establish `h1 : e z ∈ F ⊓ LinearMap.range e` using `⟨hFe z hz, LinearMap.mem_range_self e z⟩`.

Rewrite `h1` using `[← hGF]`. Take `⟨g, hg, t, ht, hgt⟩` from `Submodule.mem_sup.1 h1`. Conclude with `⟨g, hg, t, ht.1, hgt⟩`. Use `set S := LinearMap.range e with hS`. Establish `hc : IsCompl (G.comap S.subtype) (M.comap S.subtype)`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxG hxM`. Establish `: (x : H) ∈ G ⊓ M` using `⟨hxG, hxM⟩`. Rewrite `this` using `[hGM, Submodule.mem_bot]`.

Conclude with `Subtype.ext this`. Rewrite using `[codisjoint_iff, Submodule.eq_top_iff']`. Introduce `x`. Establish `hx : (x : H) ∈ G ⊔ M` using `by rw [hGMr]; exact x.2`. Take `⟨g, hg, m, hm, hgm⟩` from `Submodule.mem_sup.1 hx`.

Establish `hgS : g ∈ S` using `hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg`. Establish `hmS : m ∈ S` using `hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm`. Establish `: x = ⟨g, hgS⟩ + ⟨m, hmS⟩` using `Subtype.ext (by simp [← hgm])`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup (by simpa using hg) (by simpa using hm)`.

Set `P : H →ₗ[C] H` to `S.subtype ∘ₗ (G.comap S.subtype).subtype ∘ₗ (Submodule.linearProjOfIsCompl _ _ hc) ∘ₗ e.rangeRestrict`. Establish `hPmem : ∀ x, P x ∈ G` using `fun x => (Submodule.linearProjOfIsCompl _ _ hc (e.rangeRestrict x)).2`. Establish `hPG : ∀ g ∈ G, P g = g`. Introduce `g hg`. Establish `h1 : e.rangeRestrict g ∈ G.comap S.subtype` using `by show e g ∈ G; rw [hG g hg]; exact hg`.

Simplify using `only [P, LinearMap.coe_comp, Function.comp_apply]`. Establish `h2` using `Submodule.linearProjOfIsCompl_apply_left hc ⟨_, h1⟩`. Use `erw [h2]`. Simplify using `[hG g hg]`. Take `⟨n, v, hv⟩` from `Module.Finite.exists_fin (R := C) (M := H)`.

Establish `hsurj : Function.Surjective (Fintype.linearCombination C v)`. Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]`. Take `⟨s, hs⟩` from `Module.projective_lifting_property (Fintype.linearCombination C v) LinearMap.id hsurj`. Establish `hexp : ∀ x, x = ∑ j, s x j • v j`. Introduce `x`.

Use `LinearMap.congr_fun hs x` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, Fintype.linearCombination_apply]`. Conclude with `this.symm`. Establish `hy : ∀ j : Fin n, ∃ y : H, ∀ x, φ x y = s x j`. Introduce `j`.

Take `⟨x₀, hx₀⟩` from `hbij.2 ((LinearMap.proj j) ∘ₗ s)`. Use `⟨-x₀, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, hskew, neg_neg, hx₀]`. Both sides reduce to the same expression. Use `choose y hy using hy`.

Establish `hmain : ∀ k ∈ F, e k = 0 → ∃ t ∈ (I • ⊤ : Submodule C H), e t = 0 ∧ ∀ g ∈ G, φ g (k - t) = 0`. Introduce `k hkF hke`. Set `f : H →ₗ[C] C` to `(φ.flip k) ∘ₗ P`. Establish `hf : ∀ x, f x = φ (P x) k` using `fun x => rfl`. Establish `hfI : ∀ x, f x ∈ I` using `fun x => by rw [hf]; exact hFiso _ (hGF' (hPmem x)) _ hkF`.

Use `⟨∑ j, f (v j) • (y j - e (y j)), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hfI _) Submodule.mem_top`. Simplify using `[map_sum, map_smul, hker]`. Introduce `g hg`. Establish `h1 : ∀ j, φ g (y j - e (y j)) = s g j`.

Introduce `j`. Use `hφe g (y j)` as an intermediate fact. Rewrite `this` using `[hG g hg]`. Rewrite using `[← this, hy]`. Establish `h2 : f g = ∑ j, f (v j) * s g j` using `by conv_lhs => rw [hexp g]`.

Simplify using `[map_sum, map_smul, mul_comm]`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_smul, h1, smul_eq_mul]`. Rewrite using `[← h2, hf, hPG g hg, sub_self]`. Use `⟨G ⊔ (LinearMap.ker e ⊓ ⨅ x ∈ G, LinearMap.ker (φ x)), hcompl, hEr, ?_, hiso, hEst, ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le (sup_le hGF' ?_) hIF` and prove the remaining obligations. Introduce and unpack `w ⟨hwk, hwp⟩`. Use `replace hwk : e w = 0 := hwk`. Establish `hwp'` using `(memPerp w).1 hwp`.

Apply `hFlag w` to reduce the goal to its premises. Introduce `z hz`. Take `⟨g, hg, t, ht, hgt⟩` from `hdecomp z hz`. Establish `hz' : z = g + t + (z - e z)` using `by rw [hgt]; abel`. Rewrite using `[hz', map_add, map_add, hskew w g, hwp' g hg, neg_zero, zero_add, hkk w _ hwk (hker z), add_zero]`.

Conclude with `hIfun (φ w) t ht`. Introduce `z hz`. Take `⟨g, hg, t, ht, hgt⟩` from `hdecomp z hz`. Take `⟨t', ht', ht'e, ht'p⟩` from `hmain (z - e z) (F.sub_mem hz (hFe z hz)) (hker z)`. Establish `hz' : z = (g + (z - e z - t')) + (t + t')` using `by rw [← hgt]; abel`.

Rewrite using `[hz']`. Use `Submodule.add_mem_sup (Submodule.add_mem_sup hg ⟨?_, ?_⟩) (Submodule.add_mem _ ht ht')` and prove the remaining obligations. Use `show e (z - e z - t') = 0`. Rewrite using `[map_sub, hker, ht'e, sub_zero]`. Conclude with `(memPerp _).2 ht'p`.

Introduce `x hx`. Take `⟨g, hg, k, hk, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add, hG g hg, LinearMap.mem_ker.1 hk.1, add_zero]`. Conclude with `le_sup_left (a := G) hg`.
-/
theorem lagrangian_completion_sup_smul_eq : ∀ (C : Type) [CommRing C] (I : Ideal C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (O : Type) [Ring O] (ρ : O →+* Module.End C H) (bar : O → O) (φ : LinearMap.BilinForm C H) (e : Module.End C H), e * e = e → (∀ a, ρ a * e = e * ρ a) → (∀ x y, φ x y = -φ y x) → (∀ a, bar (bar a) = a) → (∀ a x y, φ (ρ a x) y = φ x (ρ (bar a) y)) → (∀ x y, φ (e x) y = φ x (y - e y)) → Function.Bijective φ → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ x ∈ F, ∀ y ∈ F, φ x y ∈ I) → (∀ x, (∀ y ∈ F, φ x y ∈ I) → x ∈ F) → (∀ x ∈ F, e x ∈ F) → ∀ G M : Submodule C H, G ⊓ M = ⊥ → G ⊔ M = LinearMap.range e → (∀ a, ∀ x ∈ G, ρ a x ∈ G) → G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e → ∃ E : Submodule C H, (∃ N : Submodule C H, IsCompl E N) ∧ E ⊓ LinearMap.range e = G ∧ E ⊔ I • ⊤ = F ∧ (∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ a, ∀ x ∈ E, ρ a x ∈ E) ∧ ∀ x ∈ E, e x ∈ E := by
  intro C _ I H _ _ _ _ O _ ρ bar φ e he hρe hskew hbar hφρ hφe hbij F hIF hFiso hFlag hFe G M hGM hGMr hGst hGF
  have hrefl : φ.IsRefl := fun x y h => by rw [hskew, h, neg_zero]
  have key := lagrangian_of_idempotent_split_univ C H O ρ bar φ e he hρe hbar hφρ hφe hbij hrefl G M hGM hGMr hGst
  dsimp only at key
  obtain ⟨hcompl, hEr, hiso, hEst⟩ := key
  have hee : ∀ x, e (e x) = e x := fun x => by
    have := LinearMap.congr_fun he x
    simpa using this
  have hker : ∀ x, e (x - e x) = 0 := fun x => by rw [map_sub, hee, sub_self]
  have hrange : ∀ r ∈ LinearMap.range e, e r = r := by
    rintro r ⟨y, rfl⟩; exact hee y
  have hGr : G ≤ LinearMap.range e := hGMr ▸ (le_sup_left : G ≤ G ⊔ M)
  have hG : ∀ g ∈ G, e g = g := fun g hg => hrange g (hGr hg)
  have hkk : ∀ k k', e k = 0 → e k' = 0 → φ k k' = 0 := by
    intro k k' hk hk'
    have := hφe k k'
    rw [hk, hk', sub_zero, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  have hIfun : ∀ (f : H →ₗ[C] C), ∀ t ∈ (I • ⊤ : Submodule C H), f t ∈ I := by
    intro f t ht
    have hle : (I • ⊤ : Submodule C H) ≤ Submodule.comap f (show Submodule C C from I) := by
      refine Submodule.smul_le.2 ?_
      intro r hr n _
      show f (r • n) ∈ I
      rw [map_smul, smul_eq_mul]
      exact I.mul_mem_right _ hr
    exact hle ht
  have memPerp : ∀ y, y ∈ (⨅ x ∈ G, LinearMap.ker (φ x)) ↔ ∀ x ∈ G, φ x y = 0 := by
    intro y; simp [Submodule.mem_iInf]
  have hGF' : G ≤ F := le_trans le_sup_left (hGF.le.trans inf_le_left)
  have hdecomp : ∀ z ∈ F, ∃ g ∈ G, ∃ t ∈ (I • ⊤ : Submodule C H), g + t = e z := by
    intro z hz
    have h1 : e z ∈ F ⊓ LinearMap.range e := ⟨hFe z hz, LinearMap.mem_range_self e z⟩
    rw [← hGF] at h1
    obtain ⟨g, hg, t, ht, hgt⟩ := Submodule.mem_sup.1 h1
    exact ⟨g, hg, t, ht.1, hgt⟩

  set S := LinearMap.range e with hS
  have hc : IsCompl (G.comap S.subtype) (M.comap S.subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxG hxM
      have : (x : H) ∈ G ⊓ M := ⟨hxG, hxM⟩
      rw [hGM, Submodule.mem_bot] at this
      exact Subtype.ext this
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro x
      have hx : (x : H) ∈ G ⊔ M := by rw [hGMr]; exact x.2
      obtain ⟨g, hg, m, hm, hgm⟩ := Submodule.mem_sup.1 hx
      have hgS : g ∈ S := hGMr ▸ (le_sup_left : G ≤ G ⊔ M) hg
      have hmS : m ∈ S := hGMr ▸ (le_sup_right : M ≤ G ⊔ M) hm
      have : x = ⟨g, hgS⟩ + ⟨m, hmS⟩ := Subtype.ext (by simp [← hgm])
      rw [this]
      exact Submodule.add_mem_sup (by simpa using hg) (by simpa using hm)
  let P : H →ₗ[C] H := S.subtype ∘ₗ (G.comap S.subtype).subtype ∘ₗ
    (Submodule.linearProjOfIsCompl _ _ hc) ∘ₗ e.rangeRestrict
  have hPmem : ∀ x, P x ∈ G := fun x => (Submodule.linearProjOfIsCompl _ _ hc (e.rangeRestrict x)).2
  have hPG : ∀ g ∈ G, P g = g := by
    intro g hg
    have h1 : e.rangeRestrict g ∈ G.comap S.subtype := by
      show e g ∈ G; rw [hG g hg]; exact hg
    simp only [P, LinearMap.coe_comp, Function.comp_apply]
    have h2 := Submodule.linearProjOfIsCompl_apply_left hc ⟨_, h1⟩
    erw [h2]
    simp [hG g hg]

  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := C) (M := H)
  have hsurj : Function.Surjective (Fintype.linearCombination C v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Fintype.linearCombination C v) LinearMap.id hsurj
  have hexp : ∀ x, x = ∑ j, s x j • v j := by
    intro x
    have := LinearMap.congr_fun hs x
    rw [LinearMap.comp_apply, Fintype.linearCombination_apply] at this
    exact this.symm
  have hy : ∀ j : Fin n, ∃ y : H, ∀ x, φ x y = s x j := by
    intro j
    obtain ⟨x₀, hx₀⟩ := hbij.2 ((LinearMap.proj j) ∘ₗ s)
    refine ⟨-x₀, fun x => ?_⟩
    rw [map_neg, hskew, neg_neg, hx₀]
    rfl
  choose y hy using hy

  have hmain : ∀ k ∈ F, e k = 0 → ∃ t ∈ (I • ⊤ : Submodule C H), e t = 0 ∧ ∀ g ∈ G, φ g (k - t) = 0 := by
    intro k hkF hke
    let f : H →ₗ[C] C := (φ.flip k) ∘ₗ P
    have hf : ∀ x, f x = φ (P x) k := fun x => rfl
    have hfI : ∀ x, f x ∈ I := fun x => by rw [hf]; exact hFiso _ (hGF' (hPmem x)) _ hkF
    refine ⟨∑ j, f (v j) • (y j - e (y j)), ?_, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hfI _) Submodule.mem_top
    · simp [map_sum, map_smul, hker]
    · intro g hg
      have h1 : ∀ j, φ g (y j - e (y j)) = s g j := by
        intro j
        have := hφe g (y j)
        rw [hG g hg] at this
        rw [← this, hy]
      have h2 : f g = ∑ j, f (v j) * s g j := by
        conv_lhs => rw [hexp g]
        simp [map_sum, map_smul, mul_comm]
      rw [map_sub, map_sum]
      simp only [map_smul, h1, smul_eq_mul]
      rw [← h2, hf, hPG g hg, sub_self]
  refine ⟨G ⊔ (LinearMap.ker e ⊓ ⨅ x ∈ G, LinearMap.ker (φ x)), hcompl, hEr, ?_, hiso, hEst, ?_⟩
  · apply le_antisymm
    · refine sup_le (sup_le hGF' ?_) hIF
      rintro w ⟨hwk, hwp⟩
      replace hwk : e w = 0 := hwk
      have hwp' := (memPerp w).1 hwp
      apply hFlag w
      intro z hz
      obtain ⟨g, hg, t, ht, hgt⟩ := hdecomp z hz
      have hz' : z = g + t + (z - e z) := by rw [hgt]; abel
      rw [hz', map_add, map_add, hskew w g, hwp' g hg, neg_zero, zero_add,
        hkk w _ hwk (hker z), add_zero]
      exact hIfun (φ w) t ht
    · intro z hz
      obtain ⟨g, hg, t, ht, hgt⟩ := hdecomp z hz
      obtain ⟨t', ht', ht'e, ht'p⟩ := hmain (z - e z) (F.sub_mem hz (hFe z hz)) (hker z)
      have hz' : z = (g + (z - e z - t')) + (t + t') := by rw [← hgt]; abel
      rw [hz']
      refine Submodule.add_mem_sup (Submodule.add_mem_sup hg ⟨?_, ?_⟩) (Submodule.add_mem _ ht ht')
      · show e (z - e z - t') = 0
        rw [map_sub, hker, ht'e, sub_zero]
      · exact (memPerp _).2 ht'p
  · intro x hx
    obtain ⟨g, hg, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hG g hg, LinearMap.mem_ker.1 hk.1, add_zero]
    exact le_sup_left (a := G) hg

end GlobalTheory
