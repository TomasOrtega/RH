import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

open GlobalTheory.CompanionTheory.Ar.TiePrimes (dh mem_coord_iff homog_X eval₂_eq_dh_mul exists_form aeval_eq_dh_mul adjoin_eq
  mem_Wp_iff regAt_iff)

/- English proof (translation)
Introduce `Sc Ω _ ξ K _ J _ y tie W hWp hPW c hcX`. Establish `hc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k h0 => hcX k (hPW ((mem_coord_iff y (homog_X _)).2 (by simpa using h0)))`. Establish `hx : seg y c ≠ 0` using `GlobalTheory.CompanionTheory.Ar.TiePrimes.seg_ne hc`. Use `haveI : IsDomain (MRing J ⧸ W) := Ideal.Quotient.isDomain W`. Set `F` to `FractionRing (MRing J ⧸ W)`.

Set `y' : (Σ k, J k) → F` to `fun q => algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W (MvPolynomial.X q))`. Establish `ae : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f = algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W f)`. Introduce `f`. Establish `e : MvPolynomial.eval₂Hom (Int.castRingHom F) y' = (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W)` using `MvPolynomial.ringHom_ext (fun a => by simp) (fun q => by simp [y'])`. Conclude with `RingHom.congr_fun e f`.

Establish `hzero : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f = 0 ↔ f ∈ W`. Introduce `f`. Rewrite using `[ae, map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F), Ideal.Quotient.eq_zero_iff_mem]`. Establish `hc' : ∀ k, y' ⟨k, c k⟩ ≠ 0` using `fun k h0 => hcX k ((hzero _).1 (by simpa using h0))`. Establish `memW : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → (g ∈ W ↔ dh y' c g = 0)`.

Introduce `g d hg`. Establish `h0 : (∏ k, y' ⟨k, c k⟩ ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)`. Rewrite using `[← hzero, eval₂_eq_dh_mul y' c hc' hg, mul_eq_zero, or_iff_left h0]`. Set `A` to `Algebra.adjoin ℤ (Set.range fun j => seg y j / seg y c)`. Establish `hdhA : ∀ f, dh y c f ∈ A` using `fun f => by show dh y c f ∈ Algebra.adjoin ℤ _`.

Rewrite using `[adjoin_eq hc]`. Conclude with `⟨f, rfl⟩`. Set `φ : MRing J →+* A` to `((dh y c).codRestrict A hdhA : MRing J →ₐ[ℤ] A).toRingHom`. Establish `hφ : ∀ f, ((φ f : A) : Ω) = dh y c f` using `fun f => rfl`. Establish `hsurj : Function.Surjective φ`.

Introduce and unpack `⟨a, ha⟩`. Establish `ha' : a ∈ (dh y c).range`. Rewrite using `[← adjoin_eq hc]`. Conclude with `ha`. Take `⟨f, rfl⟩` from `ha'`.

Conclude with `⟨f, Subtype.ext rfl⟩`. Set `Q : Ideal (MRing J)` to `RingHom.ker (dh y' c : MRing J →+* F)`. Use `haveI hQ : Q.IsPrime := RingHom.ker_isPrime _`. Establish `hker : RingHom.ker φ ≤ Q`. Introduce `f hf`.

Establish `hf0 : dh y c f = 0`. Rewrite using `[← hφ, RingHom.mem_ker.1 hf]`. Both sides reduce to the same expression. Take `⟨D, G, hG, e⟩` from `exists_form c f`. Establish `e₁ : dh y c G = dh y c f` using `e Ω _ fun k => div_self (hc k)`.

Establish `e₂ : dh y' c G = dh y' c f` using `e F _ fun k => div_self (hc' k)`. Establish `hGP : G ∈ W` using `hPW ((mem_coord_iff y hG).2 (by`. Rewrite using `[aeval_eq_dh_mul y c hc hG, e₁, hf0, zero_mul]))`. Use `show dh y' c f = 0`. Rewrite using `[← e₂]`.

Conclude with `(memW G D hG).1 hGP`. Set `I : Ideal A` to `Q.map φ`. Establish `hI : I.IsPrime` using `Ideal.map_isPrime_of_surjective hsurj hker`. Take `⟨p, ⟨hin, hunit⟩, -⟩` from `GlobalTheory.T.prime_chart_existsUnique_point Sc Ω ξ ℤ _ (seg y) tie c hx I hI`. Establish `hI' : ∀ g : MRing J, φ g ∈ I ↔ g ∈ Q`.

Introduce `g`. Use `⟨fun h => ?_, Ideal.mem_map_of_mem φ⟩` and prove the remaining obligations. Take `⟨x, hx', e⟩` from `(Ideal.mem_map_iff_of_surjective φ hsurj).1 h`. Establish `: g - x ∈ RingHom.ker φ`. Rewrite using `[RingHom.mem_ker, map_sub, e, sub_self]`.

Establish `h2` using `Q.add_mem (hker this) hx'`. Simplify using `using h2`. Establish `key : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → (g ∈ GlobalTheory.CompanionTheory.Ar.TiePrimes.Wp tie p ↔ g ∈ W)`. Introduce `g d hg`. Rewrite using `[mem_Wp_iff tie hin hg, memW g d hg, ← hφ, ← hunit (φ g), not_not, hI' g]`.

Both sides reduce to the same expression. Use `⟨p, hin, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨d, g, h, hg, hh, hW, e⟩` from `(regAt_iff tie p a).1 ha`. Conclude with `⟨d, g, h, hg, hh, fun hm => hW ((key h d hh).2 hm), e⟩`.
-/
theorem exists_point_of_prime : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (tie : CoordTie ℤ ξ (seg y)) (Q : Ideal (MRing J))
    (hQ : Q.IsPrime) (hle : mCoordIdeal y ≤ Q) (c : ∀ k, J k)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ Q),
    ∃ P : Cpt ξ, InChart ξ (seg y) c P ∧ ∀ a ∈ regAt ξ P, RegAt y Q a := by
  intro Sc Ω _ ξ K _ J _ y tie W hWp hPW c hcX
  classical
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 =>
    hcX k (hPW ((mem_coord_iff y (homog_X _)).2 (by simpa using h0)))
  have hx : seg y c ≠ 0 := GlobalTheory.CompanionTheory.Ar.TiePrimes.seg_ne hc
  haveI : IsDomain (MRing J ⧸ W) := Ideal.Quotient.isDomain W
  let F := FractionRing (MRing J ⧸ W)
  let y' : (Σ k, J k) → F := fun q => algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W (MvPolynomial.X q))
  have ae : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f =
      algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W f) := by
    intro f
    have e : MvPolynomial.eval₂Hom (Int.castRingHom F) y' =
        (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W) :=
      MvPolynomial.ringHom_ext (fun a => by simp) (fun q => by simp [y'])
    exact RingHom.congr_fun e f
  have hzero : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f = 0 ↔ f ∈ W := by
    intro f
    rw [ae, map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F), Ideal.Quotient.eq_zero_iff_mem]
  have hc' : ∀ k, y' ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k ((hzero _).1 (by simpa using h0))
  have memW : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → (g ∈ W ↔ dh y' c g = 0) := by
    intro g d hg
    have h0 : (∏ k, y' ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
    rw [← hzero, eval₂_eq_dh_mul y' c hc' hg, mul_eq_zero, or_iff_left h0]
  let A := Algebra.adjoin ℤ (Set.range fun j => seg y j / seg y c)
  have hdhA : ∀ f, dh y c f ∈ A := fun f => by
    show dh y c f ∈ Algebra.adjoin ℤ _
    rw [adjoin_eq hc]
    exact ⟨f, rfl⟩
  let φ : MRing J →+* A := ((dh y c).codRestrict A hdhA : MRing J →ₐ[ℤ] A).toRingHom
  have hφ : ∀ f, ((φ f : A) : Ω) = dh y c f := fun f => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ (dh y c).range := by
      rw [← adjoin_eq hc]
      exact ha
    obtain ⟨f, rfl⟩ := ha'
    exact ⟨f, Subtype.ext rfl⟩
  let Q : Ideal (MRing J) := RingHom.ker (dh y' c : MRing J →+* F)
  haveI hQ : Q.IsPrime := RingHom.ker_isPrime _
  have hker : RingHom.ker φ ≤ Q := by
    intro f hf
    have hf0 : dh y c f = 0 := by
      rw [← hφ, RingHom.mem_ker.1 hf]
      rfl
    obtain ⟨D, G, hG, e⟩ := exists_form c f
    have e₁ : dh y c G = dh y c f := e Ω _ fun k => div_self (hc k)
    have e₂ : dh y' c G = dh y' c f := e F _ fun k => div_self (hc' k)
    have hGP : G ∈ W := hPW ((mem_coord_iff y hG).2 (by
      rw [aeval_eq_dh_mul y c hc hG, e₁, hf0, zero_mul]))
    show dh y' c f = 0
    rw [← e₂]
    exact (memW G D hG).1 hGP
  let I : Ideal A := Q.map φ
  have hI : I.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  obtain ⟨p, ⟨hin, hunit⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point Sc Ω ξ ℤ _ (seg y) tie c hx I hI
  have hI' : ∀ g : MRing J, φ g ∈ I ↔ g ∈ Q := by
    intro g
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem φ⟩
    obtain ⟨x, hx', e⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).1 h
    have : g - x ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 := Q.add_mem (hker this) hx'
    simpa using h2
  have key : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d →
      (g ∈ GlobalTheory.CompanionTheory.Ar.TiePrimes.Wp tie p ↔ g ∈ W) := by
    intro g d hg
    rw [mem_Wp_iff tie hin hg, memW g d hg, ← hφ, ← hunit (φ g), not_not, hI' g]
    rfl
  refine ⟨p, hin, fun a ha => ?_⟩
  obtain ⟨d, g, h, hg, hh, hW, e⟩ := (regAt_iff tie p a).1 ha
  exact ⟨d, g, h, hg, hh, fun hm => hW ((key h d hh).2 hm), e⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
