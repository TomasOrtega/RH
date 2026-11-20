import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open GlobalTheory.CompanionTheory.Ar.HodgeCpt (rootIdx rootSgn)

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx hv r a a₀ e e₀ A₀ T hβ hcz hy hGen hNorm hVal hCoord hInt he hA hT hR hH z w hw hI t ν hg`. Use `haveI := hcz`. Substitute `hA` using the available equality. Establish `hsp : genPt 𝔐₀.ξ ⤳ centre (z ≫ h)` using `𝔐₀.all _`. Establish `hw₀` using `hCoord z w hw`.

Establish `hI₀` using `hInt z hI`. Take `⟨t₀, ht₀⟩` from `Flag.gr_gen_of_isFlagVBOn (Fl₀.sub (rootIdx D r).1) (p := ⟨centre (z ≫ h), 𝔐₀.all _⟩) (Set.mem_univ _) (rootIdx D r).2`. Take `⟨ν₀, -, hn₀⟩` from `GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ Fl₀ hβ (z ≫ h) hI₀ _ _ t₀ ht₀`. Establish `hgr₀` using `(hn₀ t₀ ν₀).2 ⟨1, one_ne_zero, by rw [div_self ht₀.1]; exact CxVal.one hsp, by simp⟩`. Establish `ecp : pushCpt hd ⟨centre z, 𝔐.all _⟩ = ⟨centre (z ≫ h), 𝔐₀.all _⟩` using `Subtype.ext (by show h (z _) = (z ≫ h) _`.

Conclude with `(Scheme.Hom.comp_apply z h _).symm)`. Establish `hgen` using `hGen ⟨centre z, 𝔐.all _⟩ (fun p hp => not_inFibre 𝔐.ξ z (𝔐.all _) hp) _ _ t₀ (ecp ▸ ht₀)`. Take `⟨ν₁, -, hn₁⟩` from `GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S Ω K J y 𝔐 Fl hβ z hI _ _ (i t₀) hgen`. Establish `hit : i t₀ ≠ 0` using `hgen.1`. Take `⟨u', -, hu', e'⟩` from `(hn₁ _ _).1 (hNorm z _ _ t₀ ν₀ hgr₀)`.

Establish `hu1 : u' = 1` using `CxVal.unique hu' (by rw [div_self hit]; exact CxVal.one (𝔐.all _))`. Take `⟨u₁, hu₁0, hu₁, eν⟩` from `(hn₁ _ _).1 hg`. Rewrite `e'` using `[hu1, norm_one, _root_.one_mul]`. Substitute `e'` using the available equality. Establish `hsec` using `hH (z ≫ h) _ hw₀ hI₀ t₀ ν₀ hgr₀`.

Use `choose c₀ hc₀ using hw₀.1`. Use `choose c hc using hw.1`. Establish `hc₀' : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0` using `fun k => (hc₀ k).ne_zero`. Establish `hc' : ∀ k, w ⟨k, c k⟩ ≠ 0` using `fun k => (hc k).ne_zero`. Take `⟨u₀, hu₀, en₀⟩` from `hsec.2.2 c₀ hc₀'`.

Take `⟨u, -, hu, eT⟩` from `hR z w hw c c₀ hc' hc₀'`. Establish `ha : ((pullHerm hv A₀).tensor T).a = a` using `by show pullDeg bk A₀.a + T.a = a`. Rewrite using `[hT]`. Normalize the expressions using the abelian group laws. Establish `hM₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k (c₀ k) (hc₀ k)).1`.

Establish `hM : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (hc k)).1`. Establish `hm₀ : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) ≠ 0` using `(map_ne_zero i).2 (mul_ne_zero hM₀ hsec.1)`. Use `(secNorm_iff_chart he hw c hc').2 ⟨u₁ ^ rootSgn D r * u₀ * u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`. Use `CxVal.mul (CxVal.mul (CxVal.zpow hu₁ hu₁0 (rootSgn D r)) (hVal z _ _ hu₀)) hu using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_div₀, map_zpow₀, div_zpow]`. Generalize the expression as in `i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) = m at hm₀`. Generalize the expression as in `(∏ k, y ⟨k, c k⟩ ^ a k) * e = n`. Establish `hz : i t₀ ^ rootSgn D r ≠ 0` using `zpow_ne_zero _ hit`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[ha, eν] show (‖u₁‖ * ν₀) ^ rootSgn D r * (A₀.h (fun p => w (blkV bk bx p)) * T.h w) = _`. Rewrite using `[mul_zpow, norm_mul, norm_mul, norm_zpow]`. Take the linear combination `(‖u₁‖ ^ rootSgn D r * T.h w) * en₀ + (‖u₁‖ ^ rootSgn D r * ‖u₀‖) * eT`.
-/
theorem isHodgeLine_pull_tensor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx hv r a a₀ e e₀ A₀ T
    hβ hcz hy hGen hNorm hVal hCoord hInt he hA hT hR hH z w hw hI t ν hg
  haveI := hcz
  subst hA
  have hsp : genPt 𝔐₀.ξ ⤳ centre (z ≫ h) := 𝔐₀.all _
  have hw₀ := hCoord z w hw
  have hI₀ := hInt z hI

  obtain ⟨t₀, ht₀⟩ := Flag.gr_gen_of_isFlagVBOn (Fl₀.sub (rootIdx D r).1)
    (p := ⟨centre (z ≫ h), 𝔐₀.all _⟩) (Set.mem_univ _) (rootIdx D r).2
  obtain ⟨ν₀, -, hn₀⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ Fl₀ hβ (z ≫ h) hI₀ _ _ t₀ ht₀
  have hgr₀ := (hn₀ t₀ ν₀).2 ⟨1, one_ne_zero, by rw [div_self ht₀.1]; exact CxVal.one hsp, by simp⟩

  have ecp : pushCpt hd ⟨centre z, 𝔐.all _⟩ = ⟨centre (z ≫ h), 𝔐₀.all _⟩ := Subtype.ext (by
    show h (z _) = (z ≫ h) _
    exact (Scheme.Hom.comp_apply z h _).symm)
  have hgen := hGen ⟨centre z, 𝔐.all _⟩ (fun p hp => not_inFibre 𝔐.ξ z (𝔐.all _) hp) _ _ t₀ (ecp ▸ ht₀)
  obtain ⟨ν₁, -, hn₁⟩ := GlobalTheory.T.hodge_cpt_interior_flag E H D l Xo c O β Y S Ω K J y 𝔐 Fl hβ z hI _ _ (i t₀) hgen
  have hit : i t₀ ≠ 0 := hgen.1
  obtain ⟨u', -, hu', e'⟩ := (hn₁ _ _).1 (hNorm z _ _ t₀ ν₀ hgr₀)
  have hu1 : u' = 1 := CxVal.unique hu' (by rw [div_self hit]; exact CxVal.one (𝔐.all _))
  obtain ⟨u₁, hu₁0, hu₁, eν⟩ := (hn₁ _ _).1 hg
  rw [hu1, norm_one, _root_.one_mul] at e'
  subst e'

  have hsec := hH (z ≫ h) _ hw₀ hI₀ t₀ ν₀ hgr₀
  choose c₀ hc₀ using hw₀.1
  choose c hc using hw.1
  have hc₀' : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := fun k => (hc₀ k).ne_zero
  have hc' : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  obtain ⟨u₀, hu₀, en₀⟩ := hsec.2.2 c₀ hc₀'
  obtain ⟨u, -, hu, eT⟩ := hR z w hw c c₀ hc' hc₀'
  have ha : ((pullHerm hv A₀).tensor T).a = a := by
    show pullDeg bk A₀.a + T.a = a
    rw [hT]
    abel
  have hM₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k (c₀ k) (hc₀ k)).1
  have hM : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (hc k)).1
  have hm₀ : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) ≠ 0 :=
    (map_ne_zero i).2 (mul_ne_zero hM₀ hsec.1)
  refine (secNorm_iff_chart he hw c hc').2 ⟨u₁ ^ rootSgn D r * u₀ * u, ?_, ?_⟩
  · rw [ha]
    convert CxVal.mul (CxVal.mul (CxVal.zpow hu₁ hu₁0 (rootSgn D r)) (hVal z _ _ hu₀)) hu using 1
    rw [map_div₀, map_zpow₀, div_zpow]
    generalize i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) = m at hm₀
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) * e = n
    have hz : i t₀ ^ rootSgn D r ≠ 0 := zpow_ne_zero _ hit
    field_simp
  · rw [ha, eν]
    show (‖u₁‖ * ν₀) ^ rootSgn D r * (A₀.h (fun p => w (blkV bk bx p)) * T.h w) = _
    rw [mul_zpow, norm_mul, norm_mul, norm_zpow]
    linear_combination (‖u₁‖ ^ rootSgn D r * T.h w) * en₀ + (‖u₁‖ ^ rootSgn D r * ‖u₀‖) * eT

end GlobalTheory.CompanionTheory.Ar.Chg
