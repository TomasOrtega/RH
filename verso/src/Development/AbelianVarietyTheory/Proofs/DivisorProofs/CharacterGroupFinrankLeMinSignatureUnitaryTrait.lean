import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UTrait

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c T`. Take `⟨hdvr, -, hch⟩` from `T.cdvr`. Use `haveI := hdvr`. Use `haveI := hch`. Take `⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩` from `T.gen`.

Set `K` to `AlgebraicClosure (FractionRing T.V)`. Set `g : FractionRing T.V →+* K` to `algebraMap (FractionRing T.V) K`. Set `f : T.V →+* K` to `g.comp (algebraMap T.V (FractionRing T.V))`. Establish `hf : Function.Injective f` using `(algebraMap (FractionRing T.V) K).injective.comp (IsFractionRing.injective T.V (FractionRing T.V))`. Use `haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := T.V) (hf (by simpa using h))⟩`.

Set `x' : Sp K ⟶ Xo.X` to `spMap g ≫ T.y ≫ pullback.fst _ _`. Take `⟨β₀, hβ₀⟩` from `Spec.map_surjective (x' ≫ Xo.s)`. Establish `hβ : x' ≫ Xo.s = spMap β₀.hom` using `hβ₀.symm`. Establish `hdet` using `(Xo.univ.geom K x' β₀.hom hβ).1`. Establish `hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K)`.

Rewrite using `[← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]`. Establish `hjK : spMap g ≫ jK T.V = spMap f` using `by show Spec.map _ ≫ Spec.map _ = _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N → Module.finrank (𝓞 E) T.P.D.toPre.X ≤ N`.

Introduce `τ N hN`. Establish `h₅` using `(GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN`. Establish `h₆` using `(GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act T.t.act m₁.act (spMap g) τ N).1 h₅`. Rewrite `h₆` using `[hjK]`. Take `⟨n, -, hn⟩` from `GlobalTheory.CharRank.lieMult_unif_loc H T.V T.t T.P K f hf τ N h₆`.

Use linear arithmetic over natural numbers and integers. Take `⟨τ₁, τ₂, h₁, h₂⟩` from `GlobalTheory.CharRank.exists_chars H K _ hr`. Conclude with `le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))`.
-/
theorem finrank_le_min : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c),
    Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := by
  intro E _ _ _ H Dw l Xo c T
  obtain ⟨hdvr, -, hch⟩ := T.cdvr
  haveI := hdvr
  haveI := hch
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  let K := AlgebraicClosure (FractionRing T.V)
  let g : FractionRing T.V →+* K := algebraMap (FractionRing T.V) K
  let f : T.V →+* K := g.comp (algebraMap T.V (FractionRing T.V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing T.V) K).injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := T.V) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.X := spMap g ≫ T.y ≫ pullback.fst _ _
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (x' ≫ Xo.s)
  have hβ : x' ≫ Xo.s = spMap β₀.hom := hβ₀.symm
  have hdet := (Xo.univ.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hjK : spMap g ≫ jK T.V = spMap f := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N →
      Module.finrank (𝓞 E) T.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act T.t.act m₁.act (spMap g) τ N).1 h₅
    rw [hjK] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H T.V T.t T.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.UPoinc.UTrait
