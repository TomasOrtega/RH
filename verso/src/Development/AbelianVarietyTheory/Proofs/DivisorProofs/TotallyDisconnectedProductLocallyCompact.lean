import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
open scoped TensorProduct
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac

noncomputable section
namespace GlobalTheory.SBProdExt

def comapEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    SB Y ≃ₗ[ℂ] SB X :=
  LinearEquiv.ofLinear (comapH e) (comapH e.symm)
    (LinearMap.ext fun F => Subtype.ext (funext fun x => by simp))
    (LinearMap.ext fun F => Subtype.ext (funext fun y => by simp))

def restrictEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (hf : Set.BijOn f (SB X : Set (X → ℂ)) (SB Y : Set (Y → ℂ))) :
    SB X ≃ₗ[ℂ] SB Y :=
  LinearEquiv.ofBijective (f.restrict (p := SB X) (q := SB Y) fun x hx => hf.mapsTo hx)
    ⟨fun a b hab => Subtype.ext (hf.injOn a.2 b.2 (congrArg Subtype.val hab)),
     fun y => by
       obtain ⟨x, hx, hxy⟩ := hf.surjOn y.2
       exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

/- English proof (translation)
Take `⟨l, hl⟩` from `exists_linear_of_bilinear_prodSB P Q (SB (P' × Q')) ((prodSBBil P' Q').compl₁₂ eP.toLinearMap eQ.toLinearMap)`. Take `⟨l', hl'⟩` from `exists_linear_of_bilinear_prodSB P' Q' (SB (P × Q)) ((prodSBBil P Q).compl₁₂ eP.symm.toLinearMap eQ.symm.toLinearMap)`. Establish `h1 : l.comp l' = LinearMap.id`. Use `LinearMap.ext_on_range (Span.span_prodSB_eq_top P' Q') fun q => ?_` and prove the remaining obligations. Simplify using `[hl, hl', prodSBBil]`.

Establish `h2 : l'.comp l = LinearMap.id`. Use `LinearMap.ext_on_range (Span.span_prodSB_eq_top P Q) fun q => ?_` and prove the remaining obligations. Simplify using `[hl, hl', prodSBBil]`. Use `⟨LinearEquiv.ofLinear l l' h1 h2, fun a b => ?_⟩` and prove the remaining obligations. Simplify using `[hl, prodSBBil]`.
-/
theorem exists_prod_equiv {P Q P' Q' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q]
    [TotallyDisconnectedSpace Q] [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P']
    [TotallyDisconnectedSpace P'] [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q']
    [TotallyDisconnectedSpace Q'] (eP : SB P ≃ₗ[ℂ] SB P') (eQ : SB Q ≃ₗ[ℂ] SB Q') :
    ∃ L : SB (P × Q) ≃ₗ[ℂ] SB (P' × Q'), ∀ a b, L (prodSB a b) = prodSB (eP a) (eQ b) := by
  obtain ⟨l, hl⟩ := exists_linear_of_bilinear_prodSB P Q (SB (P' × Q'))
    ((prodSBBil P' Q').compl₁₂ eP.toLinearMap eQ.toLinearMap)
  obtain ⟨l', hl'⟩ := exists_linear_of_bilinear_prodSB P' Q' (SB (P × Q))
    ((prodSBBil P Q).compl₁₂ eP.symm.toLinearMap eQ.symm.toLinearMap)
  have h1 : l.comp l' = LinearMap.id := by
    refine LinearMap.ext_on_range (Span.span_prodSB_eq_top P' Q') fun q => ?_
    simp [hl, hl', prodSBBil]
  have h2 : l'.comp l = LinearMap.id := by
    refine LinearMap.ext_on_range (Span.span_prodSB_eq_top P Q) fun q => ?_
    simp [hl, hl', prodSBBil]
  refine ⟨LinearEquiv.ofLinear l l' h1 h2, fun a b => ?_⟩
  simp [hl, prodSBBil]

/- English proof (translation)
Introduce `P Q P' Q' Z Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eZ eZ' f g hf hg`. Simplify using `only [GlobalTheory.WeilM.SB_eq] at hf hg ⊢`. Take `⟨L, hL⟩` from `exists_prod_equiv (restrictEquiv f hf) (restrictEquiv g hg)`. Set `E : SB Z ≃ₗ[ℂ] SB Z'` to `((comapEquiv eZ).symm.trans L).trans (comapEquiv eZ')`. Take `⟨h, hh⟩` from `LinearMap.exists_extend ((SB Z').subtype.comp E.toLinearMap)`.

Establish `happ : ∀ F : SB Z, h F.1 = (E F).1` using `fun F => LinearMap.congr_fun hh F`. Use `⟨h, ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun a ha b hb => ?_⟩` and prove the remaining obligations. Rewrite using `[happ ⟨x, hx⟩]`. Conclude with `(E _).2`. Rewrite `hxy` using `[happ ⟨x, hx⟩, happ ⟨y, hy⟩]`.

Conclude with `congrArg Subtype.val (E.injective (Subtype.ext hxy))`. Use `⟨(E.symm ⟨y, hy⟩).1, (E.symm ⟨y, hy⟩).2, ?_⟩` and prove the remaining obligations. Rewrite using `[happ]`. Simplify using the standard rewrite rules. Establish `hF : (fun z => a (eZ z).1 * b (eZ z).2) = (comapEquiv eZ (prodSB ⟨a, ha⟩ ⟨b, hb⟩)).1` using `rfl`.

Rewrite using `[hF, happ]`. Use function extensionality and compare the values at `z'`. Simplify using `only [E, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hL]`. Both sides reduce to the same expression.
-/
theorem exists_linear_bijOn_prod : ∀ {P Q P' Q' Z Z' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q] [TotallyDisconnectedSpace Q]
    [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P'] [TotallyDisconnectedSpace P']
    [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q'] [TotallyDisconnectedSpace Q']
    [TopologicalSpace Z] [TopologicalSpace Z'] (eZ : Z ≃ₜ P × Q) (eZ' : Z' ≃ₜ P' × Q')
    (f : (P → ℂ) →ₗ[ℂ] (P' → ℂ)) (g : (Q → ℂ) →ₗ[ℂ] (Q' → ℂ)),
    Set.BijOn f (GlobalTheory.WeilM.SB P : Set (P → ℂ)) (GlobalTheory.WeilM.SB P' : Set (P' → ℂ)) →
    Set.BijOn g (GlobalTheory.WeilM.SB Q : Set (Q → ℂ)) (GlobalTheory.WeilM.SB Q' : Set (Q' → ℂ)) →
    ∃ h : (Z → ℂ) →ₗ[ℂ] (Z' → ℂ), Set.BijOn h (GlobalTheory.WeilM.SB Z : Set (Z → ℂ)) (GlobalTheory.WeilM.SB Z' : Set (Z' → ℂ)) ∧
      ∀ a ∈ GlobalTheory.WeilM.SB P, ∀ b ∈ GlobalTheory.WeilM.SB Q,
        h (fun z => a (eZ z).1 * b (eZ z).2) = fun z' => f a (eZ' z').1 * g b (eZ' z').2 := by
  intro P Q P' Q' Z Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eZ eZ' f g hf hg
  simp only [GlobalTheory.WeilM.SB_eq] at hf hg ⊢
  obtain ⟨L, hL⟩ := exists_prod_equiv (restrictEquiv f hf) (restrictEquiv g hg)
  let E : SB Z ≃ₗ[ℂ] SB Z' := ((comapEquiv eZ).symm.trans L).trans (comapEquiv eZ')
  obtain ⟨h, hh⟩ := LinearMap.exists_extend ((SB Z').subtype.comp E.toLinearMap)
  have happ : ∀ F : SB Z, h F.1 = (E F).1 := fun F => LinearMap.congr_fun hh F
  refine ⟨h, ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun a ha b hb => ?_⟩
  · rw [happ ⟨x, hx⟩]; exact (E _).2
  · rw [happ ⟨x, hx⟩, happ ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (E.injective (Subtype.ext hxy))
  · refine ⟨(E.symm ⟨y, hy⟩).1, (E.symm ⟨y, hy⟩).2, ?_⟩
    rw [happ]; simp
  · have hF : (fun z => a (eZ z).1 * b (eZ z).2) = (comapEquiv eZ (prodSB ⟨a, ha⟩ ⟨b, hb⟩)).1 := rfl
    rw [hF, happ]
    funext z'
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hL]
    rfl

end GlobalTheory.SBProdExt
