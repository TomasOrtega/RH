import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD
open GroundTheory.Automorphic.Whittaker

/- English proof (translation)
Introduce `hSt X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL D hD hsum U C x₀ hU hC hUC hHU hsU hsx₀ hvan f hf`. Take `⟨L, hLo, hL1⟩` from `hχL`. Take `⟨L₀, hL₀c, hL₀o, hL₀L, hL₀τ⟩` from `hSt H τ p hp hτ hτp L hLo`. Establish `hχL₀ : ∀ l ∈ L₀, χ l = 1` using `fun l hl => hL1 l (hL₀L hl)`. Establish `hsp' : ∀ y, s^[p - 1 + 1] y = y` using `fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y`.

Establish `toCc : ∀ g ∈ supportedIn U, g ∈ Cc X`. Introduce `g hg`. Take `⟨h1, -⟩` from `hg`. Conclude with `h1`. Set `e : X ≃ₜ X` to `{ toFun := s invFun := s^[p - 1] left_inv := fun y => by show s^[p - 1] (s y) = y`.

Rewrite using `[← Function.iterate_succ_apply s (p - 1) y]`. Conclude with `hsp' y`. Use `right_inv := fun y => by show s (s^[p - 1] y) = y`. Rewrite using `[← Function.iterate_succ_apply' s (p - 1) y]`. Conclude with `hsp' y`.

Use `continuous_toFun := hs`. Use `continuous_invFun := hs.iterate (p - 1) }`. Establish `hcomp : ∀ g ∈ supportedIn U, g ∘ s ∈ supportedIn U`. Introduce `g hg`. Take `⟨hg1, hsupp⟩` from `hg`.

Rewrite `hg1` using `[GroundTheory.Automorphic.mem_locallyConstantCompactSupport]`. Take `⟨hlc, hcs⟩` from `hg1`. Use `⟨GroundTheory.Automorphic.mem_locallyConstantCompactSupport.2 ⟨hlc.comp_continuous hs, hcs.comp_homeomorph e⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `(hsU x).1 (hsupp hx)`.

Establish `hiter : ∀ i, ∀ g ∈ supportedIn U, g ∘ s^[i] ∈ supportedIn U`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `g hg`.

Conclude with `hg`. Consider the case `succ i ih`. Introduce `g hg`. Conclude with `hcomp _ (ih g hg)`. Take `⟨f₀, hf₀U, hf₀eq⟩` from `exists_lift_orbit_piece hU hC hUC hL₀c hL₀o (y := x₀) (mem_orbit_self x₀)`.

Establish `hs_orb : ∀ y ∈ orbit H x₀, s y ∈ orbit H x₀`. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `⟨τ h, by show τ h • x₀ = s (h • x₀)`. Rewrite using `[hsτ, hsx₀]⟩`. Establish `hs_piece : ∀ z ∈ orbitPiece L₀ x₀, s z ∈ orbitPiece L₀ x₀`.

Introduce and unpack `_ ⟨l, hl, rfl⟩`. Conclude with `⟨τ l, (hL₀τ l).2 hl, by show τ l • x₀ = s (l • x₀)`. Rewrite using `[hsτ, hsx₀]⟩`. Establish `hpiece_iter : ∀ n, ∀ z ∈ orbitPiece L₀ x₀, s^[n] z ∈ orbitPiece L₀ x₀`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `z hz`. Conclude with `hz`. Consider the case `succ n ih`.

Introduce `z hz`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `hs_piece _ (ih z hz)`. Establish `hs_piece_iff : ∀ z, s z ∈ orbitPiece L₀ x₀ ↔ z ∈ orbitPiece L₀ x₀`. Introduce `z`.

Use `⟨fun hz => ?_, hs_piece z⟩` and prove the remaining obligations. Establish `h1` using `hpiece_iter (p - 1) _ hz`. Rewrite `h1` using `[← Function.iterate_succ_apply s (p - 1) z, hsp']`. Conclude with `h1`. Establish `hf₀s : ∀ x ∈ orbit H x₀, f₀ (s x) = f₀ x`.

Introduce `x hx`. Rewrite using `[hf₀eq _ (hs_orb x hx), hf₀eq x hx]`. Distinguish the cases in `hz : x ∈ orbitPiece L₀ x₀`. Rewrite using `[Set.indicator_of_mem hz, Set.indicator_of_mem ((hs_piece_iff x).2 hz)]`. Both sides reduce to the same expression.

Rewrite using `[Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hs_piece_iff x).1 h))]`. Establish `hf₀i : ∀ i, ∀ x ∈ orbit H x₀, f₀ (s^[i] x) = f₀ x`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `x _`. Both sides reduce to the same expression. Consider the case `succ i ih`. Introduce `x hx`. Rewrite using `[Function.iterate_succ_apply, ih _ (hs_orb x hx)]`.

Conclude with `hf₀s x hx`. Establish `hDi : ∀ i, D (f₀ ∘ s^[i]) = D f₀`. Introduce `i`. Establish `hm` using `sub_mem_of_eqOn_orbit hUC (hiter i f₀ hf₀U) hf₀U (fun x hx => hf₀i i x hx)`. Establish `h0` using `hvan _ hm`.

Rewrite `h0` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hD0 : D f₀ = 0`. Establish `h0` using `hsum f₀ (toCc f₀ hf₀U)`. Simplify using `only [hDi, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases.

Conclude with `absurd h (Nat.cast_ne_zero.mpr hp.ne')`. Conclude with `h`. Set `W : Submodule ℂ (X → ℂ)` to `supportedIn U ⊓ LinearMap.ker D`. Establish `hrel : relSpan χ U ≤ W`. Use `le_inf (relSpan_le_supportedIn χ hHU) (Submodule.span_le.mpr ?_)` and prove the remaining obligations.

Introduce and unpack `g ⟨h, f', hf'U, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]`. Rewrite using `[hD h f' (toCc f' hf'U)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : f₀ ∈ W ⊔ supportedIn U ⊓ vanishingOn C` using `Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hf₀U, LinearMap.mem_ker.mpr hD0⟩)`.

Establish `hle` using `supportedIn_le_of_base hU hC hUC hHU χ (W := W) inf_le_left hrel L₀ hL₀c hL₀o hχL₀ f₀ hf₀eq hmem`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp (hle hf)`. Rewrite using `[map_add, LinearMap.mem_ker.mp (Submodule.mem_inf.mp ha).2, hvan b hb, add_zero]`.
-/
theorem UpperTheory.Gal.LocD.cellStep :
    StabSub → CellStep := by
  intro hSt X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL D hD hsum U C x₀ hU hC hUC hHU hsU hsx₀ hvan f hf
  obtain ⟨L, hLo, hL1⟩ := hχL
  obtain ⟨L₀, hL₀c, hL₀o, hL₀L, hL₀τ⟩ := hSt H τ p hp hτ hτp L hLo
  have hχL₀ : ∀ l ∈ L₀, χ l = 1 := fun l hl => hL1 l (hL₀L hl)
  have hsp' : ∀ y, s^[p - 1 + 1] y = y := fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y
  have toCc : ∀ g ∈ supportedIn U, g ∈ Cc X := by
    intro g hg
    obtain ⟨h1, -⟩ := hg
    exact h1
  let e : X ≃ₜ X :=
    { toFun := s
      invFun := s^[p - 1]
      left_inv := fun y => by
        show s^[p - 1] (s y) = y
        rw [← Function.iterate_succ_apply s (p - 1) y]
        exact hsp' y
      right_inv := fun y => by
        show s (s^[p - 1] y) = y
        rw [← Function.iterate_succ_apply' s (p - 1) y]
        exact hsp' y
      continuous_toFun := hs
      continuous_invFun := hs.iterate (p - 1) }
  have hcomp : ∀ g ∈ supportedIn U, g ∘ s ∈ supportedIn U := by
    intro g hg
    obtain ⟨hg1, hsupp⟩ := hg
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hg1
    obtain ⟨hlc, hcs⟩ := hg1
    refine ⟨GroundTheory.Automorphic.mem_locallyConstantCompactSupport.2
      ⟨hlc.comp_continuous hs, hcs.comp_homeomorph e⟩, ?_⟩
    intro x hx
    exact (hsU x).1 (hsupp hx)
  have hiter : ∀ i, ∀ g ∈ supportedIn U, g ∘ s^[i] ∈ supportedIn U := by
    intro i
    induction i with
    | zero =>
      intro g hg
      exact hg
    | succ i ih =>
      intro g hg
      exact hcomp _ (ih g hg)
  obtain ⟨f₀, hf₀U, hf₀eq⟩ :=
    exists_lift_orbit_piece hU hC hUC hL₀c hL₀o (y := x₀) (mem_orbit_self x₀)
  have hs_orb : ∀ y ∈ orbit H x₀, s y ∈ orbit H x₀ := by
    rintro _ ⟨h, rfl⟩
    exact ⟨τ h, by
      show τ h • x₀ = s (h • x₀)
      rw [hsτ, hsx₀]⟩
  have hs_piece : ∀ z ∈ orbitPiece L₀ x₀, s z ∈ orbitPiece L₀ x₀ := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨τ l, (hL₀τ l).2 hl, by
      show τ l • x₀ = s (l • x₀)
      rw [hsτ, hsx₀]⟩
  have hpiece_iter : ∀ n, ∀ z ∈ orbitPiece L₀ x₀, s^[n] z ∈ orbitPiece L₀ x₀ := by
    intro n
    induction n with
    | zero =>
      intro z hz
      exact hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact hs_piece _ (ih z hz)
  have hs_piece_iff : ∀ z, s z ∈ orbitPiece L₀ x₀ ↔ z ∈ orbitPiece L₀ x₀ := by
    intro z
    refine ⟨fun hz => ?_, hs_piece z⟩
    have h1 := hpiece_iter (p - 1) _ hz
    rw [← Function.iterate_succ_apply s (p - 1) z, hsp'] at h1
    exact h1
  have hf₀s : ∀ x ∈ orbit H x₀, f₀ (s x) = f₀ x := by
    intro x hx
    rw [hf₀eq _ (hs_orb x hx), hf₀eq x hx]
    by_cases hz : x ∈ orbitPiece L₀ x₀
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hs_piece_iff x).2 hz)]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hs_piece_iff x).1 h))]
  have hf₀i : ∀ i, ∀ x ∈ orbit H x₀, f₀ (s^[i] x) = f₀ x := by
    intro i
    induction i with
    | zero =>
      intro x _
      rfl
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply, ih _ (hs_orb x hx)]
      exact hf₀s x hx
  have hDi : ∀ i, D (f₀ ∘ s^[i]) = D f₀ := by
    intro i
    have hm := sub_mem_of_eqOn_orbit hUC (hiter i f₀ hf₀U) hf₀U (fun x hx => hf₀i i x hx)
    have h0 := hvan _ hm
    rwa [map_sub, sub_eq_zero] at h0
  have hD0 : D f₀ = 0 := by
    have h0 := hsum f₀ (toCc f₀ hf₀U)
    simp only [hDi, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr hp.ne')
    · exact h
  let W : Submodule ℂ (X → ℂ) := supportedIn U ⊓ LinearMap.ker D
  have hrel : relSpan χ U ≤ W := by
    refine le_inf (relSpan_le_supportedIn χ hHU) (Submodule.span_le.mpr ?_)
    rintro g ⟨h, f', hf'U, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
    rw [hD h f' (toCc f' hf'U)]
    ring
  have hmem : f₀ ∈ W ⊔ supportedIn U ⊓ vanishingOn C :=
    Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hf₀U, LinearMap.mem_ker.mpr hD0⟩)
  have hle := supportedIn_le_of_base hU hC hUC hHU χ (W := W) inf_le_left hrel L₀ hL₀c hL₀o
    hχL₀ f₀ hf₀eq hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hle hf)
  rw [map_add, LinearMap.mem_ker.mp (Submodule.mem_inf.mp ha).2, hvan b hb, add_zero]
