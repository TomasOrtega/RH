import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

namespace LX

section Fam
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {N : ℕ} {D : E.LineData X}
  (i : X ⟶ PSpace K N) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (s : ℕ)
  (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D)

def vV (k : Fin m) (V : ObjectProperty (Thick (smFun X q))) (hV : V ≤ wU q i y s) (hk : ∀ T, V T → InU (uy i y k) T) :
    ∀ c : V.FullSubcategory, ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c).Bˣ :=
  fun c => vv i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).obj c) (hk _ c.property)

/- English proof (translation)
The claim follows from `eps_mem i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).map φ) (hk _ c.property) (hk _ c'.property)`.
-/
theorem vV_eps (k : Fin m) (V : ObjectProperty (Thick (smFun X q))) (hV : V ≤ wU q i y s)
    (hk : ∀ T, V T → InU (uy i y k) T) {c c' : V.FullSubcategory} (φ : c ⟶ c') :
    ((epsE (Λ.precomp (ObjectProperty.ιOfLE hV)) (vV i y hy s hD Λ k V hV hk) e φ :
        ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').Bˣ) : ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').B) - 1 ∈
      ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').J :=
  eps_mem i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).map φ) (hk _ c.property) (hk _ c'.property)

end Fam

/- English proof (translation)
Unfold `GlobalTheory.Cris.evalAt`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE x f U (f ⁻¹ᵁ U) ⊤ le_rfl h]`. Both sides reduce to the same expression.
-/
theorem evalAt_comp_appLE {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Spec (CommRingCat.of A) ⟶ Y) (f : Y ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ U)) (h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (a : Γ(Z, U)) :
    GlobalTheory.Cris.evalAt (x ≫ f) U h' a = GlobalTheory.Cris.evalAt x (f ⁻¹ᵁ U) h (f.appLE U (f ⁻¹ᵁ U) le_rfl a) := by
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE x f U (f ⁻¹ᵁ U) ⊤ le_rfl h]
  rfl

/- English proof (translation)
Establish `h` using `dpow_mem_pdP δ 1 hx`. Rewrite `h` using `[δ.dpow_one hx]`. Then use the resulting hypothesis.
-/
theorem mem_pdP_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have h := dpow_mem_pdP δ 1 hx
  rwa [δ.dpow_one hx] at h

/- English proof (translation)
The claim follows from `mem_pdP_one T.δ hx`.
-/
theorem mem_thFil_one {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {T : Thick (smFun X q)} {x : T.B} (hx : x ∈ T.J) :
    (show (thA (smFun X q)).obj T from x) ∈ (thFil (smFun X q) 1).S T :=
  mem_pdP_one T.δ hx

end LX

open LX

/- English proof (translation)
Establish `hsk : ∀ k (c : (wK q i y s k).FullSubcategory), c.obj.pdPow s = ⊥` using `fun k c => (wK_tf i y s c.property).1`. Use `⟨fun k => bE (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k))) (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k σ`. Conclude with `mem_thFil_one (bE_mem (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k))) (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) σ)`. Introduce `k`.

Conclude with `zK_smul_eq_d (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k))) (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s (hsk k) (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h))`. Introduce `k k'`. Establish `hkk : k ∈ ({k, k'} : Finset (Fin m))` using `by simp`. Establish `hkk' : k' ∈ ({k, k'} : Finset (Fin m))` using `by simp`. Establish `hcU : capS (wK q i y s) {k, k'} ≤ wU q i y s` using `fun T h => wK_le_wU i y s k T (h k hkk)`.

Establish `hc1 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k) T` using `fun T h => wK_uy i y s (h k hkk)`. Establish `hc2 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k') T` using `fun T h => wK_uy i y s (h k' hkk')`. Use `⟨fun T => (show T.obj.B from ((vV i y hy s hD Λ k _ hcU hc1 T * (vV i y hy s hD Λ k' _ hcU hc2 T)⁻¹ : ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).Bˣ) : ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).B)), ?_, ?_⟩` and prove the remaining obligations. Introduce `T h set c : (wU q i y s).FullSubcategory := (ObjectProperty.ιOfLE hcU).obj T`. Establish `h1` using `vv_spec i y hy s hD Λ k c (hc1 _ T.property)`.

Establish `h2` using `vv_spec i y hy s hD Λ k' c (hc2 _ T.property)`. Establish `hq : lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k) = lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') * ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k'))`. Use `(liftA_yx_quot (pt c.obj ≫ i) y hy (jc i y s c) k k' (hjc i y s c) h).trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `evalAt_comp_appLE (pt c.obj) i _ h h _`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k c (hc1 _ T.property) * (vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) = _`. Rewrite using `[Units.val_mul, map_mul, h1]`. Establish `h3 : Ideal.Quotient.mk c.obj.J ((vv i y hy s hD Λ k' c (hc2 _ T.property) : c.obj.Bˣ) : c.obj.B) * Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Rewrite `h3` using `[h2]`.

Unfold `μ at h3 ⊢`. Rewrite using `[hq]`. Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `τ`. Conclude with `bE_sub (Λ.precomp (ObjectProperty.ιOfLE hcU)) (vV i y hy s hD Λ k _ hcU hc1) (vV i y hy s hD Λ k' _ hcU hc2) e s (fun c => (wK_tf i y s (c.property k hkk)).1) (vV_eps i y hy s hD Λ k _ hcU hc1) (vV_eps i y hy s hD Λ k' _ hcU hc2) τ`.
-/
theorem firstChern_local_exact [CharZero K] (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (i : X ⟶ PSpace K N)
    (hD : IsTautologicalLineAt D N i) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e)
    (s : ℕ) (Λ : CLiftK (ObjectProperty.ι fun T : Thick (smFun X q) => ∃ k, wK q i y s k T) D) :
    ∃ b : ∀ k, CH.Cn (CH.modF ((wK q i y s k).ι ⋙ thA (smFun X q))) 1,
      (∀ k σ, b k σ ∈ (thFil (smFun X q) 1).S _) ∧
      (∀ k, resB (thA (smFun X q)) (fun T h => ⟨k, h⟩ : wK q i y s k ≤ fun T : Thick (smFun X q) => ∃ k', wK q i y s k' T)
        (e • zK Λ s) = CH.d _ 1 (b k)) ∧
      ∀ k k', ∃ ĝ : ∀ T : (capS (wK q i y s) {k, k'}).FullSubcategory, T.obj.B,
        (∀ T (h : InU (uy i y k') T.obj),
          Ideal.Quotient.mk _ (ĝ T) = ev T.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k'))) ∧
        resB (thA (smFun X q)) (fun T h => h k (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k) (b k) -
          resB (thA (smFun X q)) (fun T h => h k' (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k') (b k') =
          dlogC (capS (wK q i y s) {k, k'}) s ĝ := by
  classical
  have hsk : ∀ k (c : (wK q i y s k).FullSubcategory), c.obj.pdPow s = ⊥ := fun k c => (wK_tf i y s c.property).1
  refine ⟨fun k => bE (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s, ?_, ?_, ?_⟩
  · intro k σ
    exact mem_thFil_one (bE_mem (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s
      (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) σ)
  · intro k
    exact zK_smul_eq_d (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s (hsk k)
      (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h))
  · intro k k'
    have hkk : k ∈ ({k, k'} : Finset (Fin m)) := by simp
    have hkk' : k' ∈ ({k, k'} : Finset (Fin m)) := by simp
    have hcU : capS (wK q i y s) {k, k'} ≤ wU q i y s := fun T h => wK_le_wU i y s k T (h k hkk)
    have hc1 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k) T := fun T h => wK_uy i y s (h k hkk)
    have hc2 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k') T := fun T h => wK_uy i y s (h k' hkk')
    refine ⟨fun T => (show T.obj.B from ((vV i y hy s hD Λ k _ hcU hc1 T * (vV i y hy s hD Λ k' _ hcU hc2 T)⁻¹ :
        ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).Bˣ) : ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).B)),
      ?_, ?_⟩
    · intro T h
      set c : (wU q i y s).FullSubcategory := (ObjectProperty.ιOfLE hcU).obj T
      have h1 := vv_spec i y hy s hD Λ k c (hc1 _ T.property)
      have h2 := vv_spec i y hy s hD Λ k' c (hc2 _ T.property)
      have hq : lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k) =
          lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
            ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) := by
        refine (liftA_yx_quot (pt c.obj ≫ i) y hy (jc i y s c) k k' (hjc i y s c) h).trans ?_
        congr 1
        exact evalAt_comp_appLE (pt c.obj) i _ h h _
      change Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k c (hc1 _ T.property) *
        (vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) = _
      rw [Units.val_mul, map_mul, h1]
      have h3 : Ideal.Quotient.mk c.obj.J ((vv i y hy s hD Λ k' c (hc2 _ T.property) : c.obj.Bˣ) : c.obj.B) *
          Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [h2] at h3
      unfold μ at h3 ⊢
      rw [hq]
      calc lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
              ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) *
              (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J) *
            Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)
          = ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) *
            (lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
              (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J) *
            Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) := by ring
        _ = _ := by rw [h3, mul_one]; rfl
    · funext τ
      exact bE_sub (Λ.precomp (ObjectProperty.ιOfLE hcU)) (vV i y hy s hD Λ k _ hcU hc1) (vV i y hy s hD Λ k' _ hcU hc2)
        e s (fun c => (wK_tf i y s (c.property k hkk)).1)
        (vV_eps i y hy s hD Λ k _ hcU hc1) (vV_eps i y hy s hD Λ k' _ hcU hc2) τ

end CrystallineSemistableComparison.Pb
