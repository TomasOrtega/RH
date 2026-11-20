import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu UpperTheory.Zero.LLC

open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx α hα`. Rewrite `hα` using `[WD.eig, hx, ← C_1, roots_pow, roots_X_sub_C]`. Simplify using `using Multiset.mem_of_mem_nsmul hα`. Introduce `hx`.

Rewrite using `[WD.charPol_eq_prod, Multiset.eq_replicate_of_mem hx, Multiset.map_replicate, Multiset.prod_replicate, WD.card_eig, C_1]`.
-/
private theorem pow_iff (x : WD h) (σ : Weil h) :
    x.charPol σ = (X - 1) ^ x.lpDim ↔ ∀ α ∈ x.eig σ, α = 1 := by
  constructor
  · intro hx α hα
    rw [WD.eig, hx, ← C_1, roots_pow, roots_X_sub_C] at hα
    simpa using Multiset.mem_of_mem_nsmul hα
  · intro hx
    rw [WD.charPol_eq_prod, Multiset.eq_replicate_of_mem hx, Multiset.map_replicate,
      Multiset.prod_replicate, WD.card_eig, C_1]

/- English proof (translation)
Rewrite using `[WD.eig, WD.eig, WD.eig, WD.charPol_lpSum, roots_mul]`. Conclude with `mul_ne_zero (WD.charPol_monic x σ).ne_zero (WD.charPol_monic y σ).ne_zero`.
-/
private theorem eig_sum (x y : WD h) (σ : Weil h) : (x.lpSum y).eig σ = x.eig σ + y.eig σ := by
  rw [WD.eig, WD.eig, WD.eig, WD.charPol_lpSum, roots_mul]
  exact mul_ne_zero (WD.charPol_monic x σ).ne_zero (WD.charPol_monic y σ).ne_zero

/- English proof (translation)
The claim follows from `forall_congr' fun s => forall_congr' fun t => pow_iff x ⁅s, t⁆`.
-/
private theorem tor_iff (x : WD h) :
    UpperTheory.GalStar.Tor x ↔ ∀ s t : ↥(Weil h), ∀ α ∈ x.eig ⁅s, t⁆, α = 1 :=
  forall_congr' fun s => forall_congr' fun t => pow_iff x ⁅s, t⁆

/- English proof (translation)
Establish `ht : UpperTheory.GalStar.Tor (x.lpSum y) ↔ UpperTheory.GalStar.Tor x ∧ UpperTheory.GalStar.Tor y`. Simplify using `only [tor_iff, eig_sum, Multiset.mem_add]`. Conclude with `⟨fun H => ⟨fun s t α hα => H s t α (Or.inl hα), fun s t α hα => H s t α (Or.inr hα)⟩, fun H s t α hα => hα.elim (H.1 s t α) (H.2 s t α)⟩`. Unfold `Gd`. Rewrite using `[ht, WD.monomial_sum_iff]`.

The claim follows by propositional logic.
-/
private theorem gd_sum (x y : WD h) : Gd (x.lpSum y) ↔ Gd x ∧ Gd y := by
  have ht : UpperTheory.GalStar.Tor (x.lpSum y) ↔ UpperTheory.GalStar.Tor x ∧ UpperTheory.GalStar.Tor y := by
    simp only [tor_iff, eig_sum, Multiset.mem_add]
    exact ⟨fun H => ⟨fun s t α hα => H s t α (Or.inl hα), fun s t α hα => H s t α (Or.inr hα)⟩,
      fun H s t α hα => hα.elim (H.1 s t α) (H.2 s t α)⟩
  unfold Gd
  rw [ht, WD.monomial_sum_iff]
  tauto

/- English proof (translation)
Establish `ht : UpperTheory.GalStar.Tor (x.lpTw t) ↔ UpperTheory.GalStar.Tor x`. Simplify using `only [tor_iff]`. Use `forall_congr' fun s => forall_congr' fun u => ?_` and prove the remaining obligations. Establish `hc : (unrChar h (qPow w t)) ⁅s, u⁆ = 1`. Rewrite using `[map_commutatorElement]`.

Conclude with `(Commute.all _ _).commutator_eq`. Establish `he : (x.lpTw t).charPol ⁅s, u⁆ = x.charPol ⁅s, u⁆`. Rewrite using `[GlobalTheory.GalCut.AwayMono.charPol_lpTw, hc]`. Simplify using the standard rewrite rules. Rewrite using `[WD.eig, WD.eig, he]`.

Unfold `Gd`. Rewrite using `[ht, WD.monomial_twist_iff]`.
-/
private theorem gd_tw (x : WD h) (t : ℝ) : Gd (x.lpTw t) ↔ Gd x := by
  have ht : UpperTheory.GalStar.Tor (x.lpTw t) ↔ UpperTheory.GalStar.Tor x := by
    simp only [tor_iff]
    refine forall_congr' fun s => forall_congr' fun u => ?_
    have hc : (unrChar h (qPow w t)) ⁅s, u⁆ = 1 := by
      rw [map_commutatorElement]
      exact (Commute.all _ _).commutator_eq
    have he : (x.lpTw t).charPol ⁅s, u⁆ = x.charPol ⁅s, u⁆ := by
      rw [GlobalTheory.GalCut.AwayMono.charPol_lpTw, hc]
      simp
    rw [WD.eig, WD.eig, he]
  unfold Gd
  rw [ht, WD.monomial_twist_iff]

/- English proof (translation)
Use `⟨(tor_iff _).2 fun s t α hα => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hα` using `[WD.eig, GlobalTheory.LocLanglands.CuspExt.charPol_lpZero]`. Simplify using `at hα`. Rewrite using `[WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff]`. Both sides reduce to the same expression.
-/
private theorem gd_zero : Gd (WD.lpZero h) := by
  refine ⟨(tor_iff _).2 fun s t α hα => ?_, ?_⟩
  · rw [WD.eig, GlobalTheory.LocLanglands.CuspExt.charPol_lpZero] at hα
    simp at hα
  · rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    rfl

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact ⟨fun _ x hx => absurd hx (by simp), fun _ => gd_zero⟩`. Consider the case `cons b L ih => show Gd (WD.lpSum b (sumList L)) ↔ _`. Rewrite using `[gd_sum, ih, List.forall_mem_cons]`.
-/
private theorem gd_list (L : List (WD h)) : Gd (sumList L) ↔ ∀ x ∈ L, Gd x := by
  induction L with
  | nil => exact ⟨fun _ x hx => absurd hx (by simp), fun _ => gd_zero⟩
  | cons b L ih =>
    show Gd (WD.lpSum b (sumList L)) ↔ _
    rw [gd_sum, ih, List.forall_mem_cons]

/- English proof (translation)
Rewrite using `[commutatorElement_def]`. Simplify using `only [deg_mul, deg_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem deg_comm (s t : ↥(Weil h)) : deg ⁅s, t⁆ = 0 := by
  rw [commutatorElement_def]
  simp only [deg_mul, deg_inv]
  ring

/- English proof (translation)
Use `⟨fun s t => ?_, WD.unr_mono0 _ hx⟩` and prove the remaining obligations. Establish `hi : ((⁅s, t⁆ : ↥(Weil h)) : G E Ω) ∈ Ine (F` using `E) A := actsAs_zero_iff.mp (actsAs_of_deg (a := 0) (b := 0) (by simpa using deg_comm s t))`. Take `⟨n, a, rfl⟩` from `x.exists_rep`. Establish `h1 : a.ρ ⁅s, t⁆ = 1` using `((WD.unr_mk a).mp hx).2 ⟨_, hi⟩`. Use `show WD.charPol _ _ = _`.

Rewrite using `[WD.charPol_mk, h1, LinearMap.charpoly_one, WD.lpDim_mk]`.
-/
private theorem gd_unr {x : WD h} (hx : x.unr) : Gd x := by
  refine ⟨fun s t => ?_, WD.unr_mono0 _ hx⟩
  have hi : ((⁅s, t⁆ : ↥(Weil h)) : G E Ω) ∈ Ine (F := E) A :=
    actsAs_zero_iff.mp (actsAs_of_deg (a := 0) (b := 0) (by simpa using deg_comm s t))
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  have h1 : a.ρ ⁅s, t⁆ = 1 := ((WD.unr_mk a).mp hx).2 ⟨_, hi⟩
  show WD.charPol _ _ = _
  rw [WD.charPol_mk, h1, LinearMap.charpoly_one, WD.lpDim_mk]

end UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist

open UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist in
/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h`. Conclude with `⟨gd_sum, gd_tw, gd_list, fun _ => gd_unr⟩`.
-/
theorem UpperTheory.V.Z.Win.Gu.gdLaws :
    GdLaws := by
  intro E Ω _ _ _ _ _ A w h
  exact ⟨gd_sum, gd_tw, gd_list, fun _ => gd_unr⟩
