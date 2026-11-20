import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleGL1IsCharacterStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.Unique

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Unfold `segSum`. Use `congr 1`. Conclude with `List.map_congr_left fun Δ hΔ => by rw [H Δ hΔ]`.
-/
theorem segSum_congr (rc rc' : IrrGL (w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E)))
    (H : ∀ Δ ∈ l, rc Δ.first = rc' Δ.first) : segSum rc l = segSum rc' l := by
  unfold segSum
  congr 1
  exact List.map_congr_left fun Δ hΔ => by rw [H Δ hΔ]

/- English proof (translation)
Take `⟨_, xs, hd, ⟨Δs, ⟨hmap, -⟩, hLs⟩, -⟩` from `hL`. Rewrite `hΔ` using `[← hmap]`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hΔ`. Establish `h1` using `(hLs i).deg_eq`. Establish `h2 : (xs i).1 ≤ ∑ a, (xs a).1` using `Finset.single_le_sum (f := fun a => (xs a).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`.

Establish `h3 : (Δs i).d ≤ (Δs i).deg` using `Nat.le_mul_of_pos_left _ (Δs i).len_pos`. Use `show (Δs i).d ≤ N`. Use linear arithmetic over natural numbers and integers.
-/
theorem first_fst_le_of_isL {k V : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} {𝔪 : Multiset (Segment k)}
    (hL : IsL 𝔪 π) {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : Δ.first.1 ≤ N := by
  obtain ⟨_, xs, hd, ⟨Δs, ⟨hmap, -⟩, hLs⟩, -⟩ := hL
  rw [← hmap] at hΔ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΔ
  have h1 := (hLs i).deg_eq
  have h2 : (xs i).1 ≤ ∑ a, (xs a).1 := Finset.single_le_sum (f := fun a => (xs a).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : (Δs i).d ≤ (Δs i).deg := Nat.le_mul_of_pos_left _ (Δs i).len_pos
  show (Δs i).d ≤ N
  omega

/- English proof (translation)
Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective`. Take `⟨n, c⟩` from `x`. Take `⟨hn, hc⟩` from `hx`. Break down `n with _ | m` into its components or cases. Conclude with `absurd hn (lt_irrefl 0)`.

Break down `m with _ | m` into its components or cases. Take `⟨χ, hχ, hx⟩` from `GlobalTheory.T.irreducible_GL1_is_character hBZ _ ⟨1, c⟩ rfl`. Rewrite using `[hx, H.one, H'.one]`. Take `⟨x', hx'⟩` from `H'.bij.2 (rc ⟨m + 2, c⟩)`. Establish `hd : x'.1 = m + 2`.

Use `H'.dim x'` as an intermediate fact. Rewrite `this` using `[hx', H.dim]`. Conclude with `this.symm`. Establish `hcx' : x'.IsCusp` using `(H'.cusp x').2 (hx' ▸ (H.cusp _).1 ⟨hn, hc⟩)`. Take `⟨n', c'⟩` from `x'`.

Take `rfl : n' = m + 2` from `hd`. Establish `hcls : ∀ d : IrrCl (GL (Fin (m + 2)) (w.adicCompletion E)), cls d.rep = ⟨m + 2, d⟩` using `fun d => by`. Simplify using `[cls, IrrCl.cl_rep]`. Establish `key : c = c'`. Rewrite using `[← c.cl_rep, ← c'.cl_rep]`.

Use `IrrRep.cl_eq_iff.2 ?_` and prove the remaining obligations. Use `hLC _ ψ hψc hψ (m + 1) (Nat.succ_pos m) c.rep c'.rep hc hcx'.2 fun τ => ?_` and prove the remaining obligations. Establish `h2 : rc (cls τ) = rc' (cls τ)` using `ih _ (by show m + 1 < m + 2; omega)`. Use `⟨_, H.eps ψ hψc hψ (m + 1) c.rep τ hc, ?_⟩` and prove the remaining obligations. Establish `h1` using `H'.eps ψ hψc hψ (m + 1) c'.rep τ hcx'.2`.

Rewrite `h1`, the goal using `[hcls]`. Rewrite using `[he, ← hx', h2]`. Conclude with `h1`. Substitute `key` using the available equality. Conclude with `hx'.symm`.
-/
theorem eq_of_isCusp (hLC : LocalConverseGL) (hBZ : BernsteinZelevinskyFiniteness)
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc rc' : IrrGL (w.adicCompletion E) → WD h}
    {ψ : AddChar (w.adicCompletion E) Circle} (hψc : Continuous ψ) (hψ : ψ ≠ 1) (he : e ψ = e' ψ)
    (H : LawsMin a ha e rc) (H' : LawsMin a ha e' rc') (x : IrrGL (w.adicCompletion E)) (hx : x.IsCusp)
    (ih : ∀ y : IrrGL (w.adicCompletion E), y.1 < x.1 → rc y = rc' y) : rc x = rc' x := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨n, c⟩ := x
  obtain ⟨hn, hc⟩ := hx
  rcases n with _ | m
  · exact absurd hn (lt_irrefl 0)
  rcases m with _ | m
  · obtain ⟨χ, hχ, hx⟩ := GlobalTheory.T.irreducible_GL1_is_character hBZ _ ⟨1, c⟩ rfl
    rw [hx, H.one, H'.one]
  · obtain ⟨x', hx'⟩ := H'.bij.2 (rc ⟨m + 2, c⟩)
    have hd : x'.1 = m + 2 := by
      have := H'.dim x'
      rw [hx', H.dim] at this
      exact this.symm
    have hcx' : x'.IsCusp := (H'.cusp x').2 (hx' ▸ (H.cusp _).1 ⟨hn, hc⟩)
    obtain ⟨n', c'⟩ := x'
    obtain rfl : n' = m + 2 := hd
    have hcls : ∀ d : IrrCl (GL (Fin (m + 2)) (w.adicCompletion E)), cls d.rep = ⟨m + 2, d⟩ := fun d => by
      simp [cls, IrrCl.cl_rep]
    have key : c = c' := by
      rw [← c.cl_rep, ← c'.cl_rep]
      refine IrrRep.cl_eq_iff.2 ?_
      refine hLC _ ψ hψc hψ (m + 1) (Nat.succ_pos m) c.rep c'.rep hc hcx'.2 fun τ => ?_
      have h2 : rc (cls τ) = rc' (cls τ) := ih _ (by show m + 1 < m + 2; omega)
      refine ⟨_, H.eps ψ hψc hψ (m + 1) c.rep τ hc, ?_⟩
      have h1 := H'.eps ψ hψc hψ (m + 1) c'.rep τ hcx'.2
      rw [hcls] at h1 ⊢
      rw [he, ← hx', h2]
      exact h1
    subst key
    exact hx'.symm

/- English proof (translation)
Introduce `hLC hEx hBZ E Ω _ _ _ _ _ A w h a ha e rc rc' ψ e' hψc hψ he H H'`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective`. Establish `main : ∀ n, ∀ x : IrrGL (w.adicCompletion E), x.1 = n → rc x = rc' x`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`.

Consider the case `_ n ih`. Introduce `x hxn`. Take `⟨𝔪, h𝔪⟩` from `hEx _ x`. Establish `hL : IsL ((𝔪.toList : List _) : Multiset _) x.rep` using `by rwa [Multiset.coe_toList]`. Rewrite using `[H.langlands _ x hL, H'.langlands _ x hL]`.

Use `segSum_congr rc rc' _ fun Δ hΔ => ?_` and prove the remaining obligations. Establish `hle : Δ.first.1 ≤ n` using `hxn ▸ first_fst_le_of_isL h𝔪 (Multiset.mem_toList.1 hΔ)`. Conclude with `eq_of_isCusp hLC hBZ hψc hψ he H H' Δ.first Δ.isCusp_first fun y hy => ih y.1 (by omega) y rfl`. Use function extensionality and compare the values at `x`. Conclude with `main _ x rfl`.
-/
theorem eq_of_lawsMin : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  intro hLC hEx hBZ E Ω _ _ _ _ _ A w h a ha e rc rc' ψ e' hψc hψ he H H'
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have main : ∀ n, ∀ x : IrrGL (w.adicCompletion E), x.1 = n → rc x = rc' x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn
      obtain ⟨𝔪, h𝔪⟩ := hEx _ x
      have hL : IsL ((𝔪.toList : List _) : Multiset _) x.rep := by rwa [Multiset.coe_toList]
      rw [H.langlands _ x hL, H'.langlands _ x hL]
      refine segSum_congr rc rc' _ fun Δ hΔ => ?_
      have hle : Δ.first.1 ≤ n := hxn ▸ first_fst_le_of_isL h𝔪 (Multiset.mem_toList.1 hΔ)
      exact eq_of_isCusp hLC hBZ hψc hψ he H H' Δ.first Δ.isCusp_first
        fun y hy => ih y.1 (by omega) y rfl
  funext x
  exact main _ x rfl

end GlobalTheory.LocLanglands.Unique

end
