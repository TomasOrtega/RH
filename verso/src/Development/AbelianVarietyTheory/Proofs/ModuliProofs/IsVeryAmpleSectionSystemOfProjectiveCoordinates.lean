import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroCoordinateAffineChartStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.CoordEmbed
open GlobalTheory.ZM.RepBC

/- English proof (translation)
Take `rfl : W = x ⁻¹ᵁ V` from `le_antisymm e e'`. Establish `hiso : IsIso (x.app V)` using `x.isIso_app V hV`. Rewrite using `[← x.app_eq_appLE]`. Use `first`. Consider the case `exact (asIso (x.app V)).commRingCatIsoToRingEquiv.bijective`.
-/
theorem appLE_bijective {X Y : Scheme.{0}} (x : Y ⟶ X) [IsOpenImmersion x] {V : X.Opens} {W : Y.Opens}
    (hV : V ≤ x.opensRange) (e : W ≤ x ⁻¹ᵁ V) (e' : x ⁻¹ᵁ V ≤ W) :
    Function.Bijective (x.appLE V W e).hom := by
  obtain rfl : W = x ⁻¹ᵁ V := le_antisymm e e'
  have hiso : IsIso (x.app V) := x.isIso_app V hV
  rw [← x.app_eq_appLE]
  first
    | exact (asIso (x.app V)).commRingCatIsoToRingEquiv.bijective

/- English proof (translation)
Take `⟨hLB, hpt, -⟩` from `h`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Take `⟨R, _, x, v, -, ⟨q, rfl⟩, hv⟩` from `(GlobalTheory.T.sectionCoordinateVector_exists_locally Z M σ th hLB).2.2 z`. Establish `hβ : x ≫ p = spMap (Spec.preimage (x ≫ p)).hom`.

Unfold `spMap`. Simplify using the standard rewrite rules. Establish `hspan` using `(hpt R _ x v hβ hv).1`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, v i ∉ q.asIdeal := by`. Assume the negation of the conclusion as `hno`.

Simplify using `only [not_exists, not_not] at hno`. Apply `q.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← hspan, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hno i`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, ((GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus Z M σ th hLB).2.2 R x v i q hv).2 hi⟩`.
-/
theorem cover {K σ : Type} [CommRing K] {I : Ideal (MvPolynomial σ K)} {Z : Scheme.{0}} {p : Z ⟶ Sp K} {M : LB Z}
    {th : σ → M.Sec} (h : ProjRep I p M th) : ⨆ i, Out.nonzeroLocus (th i) = ⊤ := by
  obtain ⟨hLB, hpt, -⟩ := h
  rw [eq_top_iff]
  rintro z -
  obtain ⟨R, _, x, v, -, ⟨q, rfl⟩, hv⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Z M σ th hLB).2.2 z
  have hβ : x ≫ p = spMap (Spec.preimage (x ≫ p)).hom := by
    unfold spMap
    simp
  have hspan := (hpt R _ x v hβ hv).1
  obtain ⟨i, hi⟩ : ∃ i, v i ∉ q.asIdeal := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    apply q.isPrime.ne_top
    rw [eq_top_iff, ← hspan, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hno i
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ((GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus Z M σ th hLB).2.2 R x v i q hv).2 hi⟩

/- English proof (translation)
Take `⟨τ, -, hvτ⟩` from `hv`. Establish `hU : ∀ k, (M.pull x).U (fun _ => k) = x ⁻¹ᵁ M.U k` using `fun k => by ext1`. Simplify using `only [LB.pull, LB.LinComb, LB.wchart, Scheme.Hom.coe_preimage]`. Use `first`. Consider the case `exact Set.iInter_const _`.

Consider the case `simp`. Establish `hxD : x ⁻¹ᵁ D = ⊤`. Rewrite using `[← hD]`. Conclude with `Scheme.Hom.preimage_opensRange x`. Establish `hDle : D ≤ x.opensRange` using `hD.ge`.

Establish `hres : ∀ (A B : Z.Opens) (hAB : A ≤ B) (W : (Sp S).Opens) (hW : W ≤ x ⁻¹ᵁ A) (a : Γ(Z, B)), (x.appLE A W hW).hom (resG Z hAB a) = (x.appLE B W (hW.trans fun _ hz => hAB hz)).hom a`. Introduce `A B hAB W hW a`. Unfold `resG`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`. Establish `hres' : ∀ (A : Z.Opens) (W W' : (Sp S).Opens) (hW : W ≤ x ⁻¹ᵁ A) (hW' : W' ≤ W) (a : Γ(Z, A)), resG (Sp S) hW' ((x.appLE A W hW).hom a) = (x.appLE A W' (hW'.trans hW)).hom a`.

Introduce `A W W' hW hW' a`. Unfold `resG`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_map]`. Establish `hcomp : ∀ (W₁ W₂ W₃ : (Sp S).Opens) (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂) (a : Γ(Sp S, W₁)), resG (Sp S) h₂ (resG (Sp S) h₁ a) = resG (Sp S) (h₂.trans h₁) a`. Introduce `W₁ W₂ W₃ h₁ h₂ a`.

Unfold `resG`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression. Establish `hbij` using `appLE_bijective x hDle hxD.ge le_top`. Take `⟨r, hr⟩ : ∃ r : σ → Γ(Z, D), ∀ j, (x.appLE D ⊤ hxD.ge).hom (r j) = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v j)` from `⟨fun j => (hbij.2 _).choose, fun j => (hbij.2 _).choose_spec⟩`.

Use `⟨r, fun j k => ?_, fun f => ?_⟩` and prove the remaining obligations. Establish `hk : x ⁻¹ᵁ (D ⊓ M.U k) ≤ (M.pull x).U (fun _ => k)`. Rewrite using `[hU]`. Conclude with `fun _ hz => hz.2`. Establish `key : ∀ (l : σ) (h' : x ⁻¹ᵁ (D ⊓ M.U k) ≤ x ⁻¹ᵁ M.U k), (x.appLE (M.U k) (x ⁻¹ᵁ (D ⊓ M.U k)) h').hom ((th l).f k) = resG (Sp S) hk (resG (Sp S) (le_top : (M.pull x).U (fun _ => k) ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v l)) * ((τ.s fun _ => k).val : Γ(Sp S, (M.pull …`.

Introduce `l h'`. Rewrite using `[← hvτ l (fun _ => k) (hU k).le, hres']`. Establish `hrj : ∀ (h' : x ⁻¹ᵁ (D ⊓ M.U k) ≤ x ⁻¹ᵁ D), (x.appLE D (x ⁻¹ᵁ (D ⊓ M.U k)) h').hom (r j) = resG (Sp S) le_top ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v j))`. Introduce `h'`. Rewrite using `[← hr j, hres']`.

Apply `(appLE_bijective x (inf_le_left.trans hDle) le_rfl le_rfl).1` to reduce the goal to its premises. Rewrite using `[map_mul, hres, hres, hres, key j, key i, hrj, hi]`. Simplify using `only [map_one, _root_.one_mul, map_mul, hcomp]`. Take `⟨F, hF⟩` from `hgen ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((x.appLE D ⊤ hxD.ge).hom f))`. Use `⟨F, hbij.1 ?_⟩` and prove the remaining obligations.

Establish `hbase : ∀ (g : Sp S ⟶ Sp K) (hg : g = spMap β) (e : (⊤ : (Sp S).Opens) ≤ g ⁻¹ᵁ ⊤) (c : K), (g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (β c)`. Introduce and unpack `g rfl e c`. Conclude with `GlobalTheory.ZM.Coord.appLE_spec β e c`. Establish `h₁ : (x.appLE D ⊤ hxD.ge).hom.comp (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp β`. Use extensionality with `c`.

Use `show (x.appLE D ⊤ hxD.ge).hom ((p.appLE ⊤ D le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (β c)`. Establish `hcc` using `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) (Scheme.Hom.appLE_comp_appLE x p ⊤ D ⊤ le_top hxD.ge)`. Conclude with `hcc.trans (hbase _ hx _ c)`. Establish `h₂ : (x.appLE D ⊤ hxD.ge).hom ∘ r = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ∘ v` using `funext hr`. Rewrite using `[MvPolynomial.eval₂_comp_left, h₁, h₂, ← MvPolynomial.eval₂_comp_left, ← hF, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]`.
-/
theorem ratios {K σ S : Type} [CommRing K] [CommRing S] {Z : Scheme.{0}} {p : Z ⟶ Sp K} {M : LB Z}
    {th : σ → M.Sec} (i : σ) (D : Z.Opens) (x : Sp S ⟶ Z) [IsOpenImmersion x] (hD : x.opensRange = D)
    (β : K →+* S) (hx : x ≫ p = spMap β) (v : σ → S) (hv : SecCoord M th x v) (hi : v i = 1)
    (hgen : ∀ a : S, ∃ F : MvPolynomial σ K, a = MvPolynomial.eval₂ β v F) :
    ∃ r : σ → Γ(Z, D),
      (∀ j k, resG Z (inf_le_right : D ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG Z (inf_le_left : D ⊓ M.U k ≤ D) (r j) * resG Z (inf_le_right : D ⊓ M.U k ≤ M.U k) ((th i).f k)) ∧
      ∀ f : Γ(Z, D), ∃ F : MvPolynomial σ K,
        f = MvPolynomial.eval₂ (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F := by
  obtain ⟨τ, -, hvτ⟩ := hv
  have hU : ∀ k, (M.pull x).U (fun _ => k) = x ⁻¹ᵁ M.U k := fun k => by
    ext1
    simp only [LB.pull, LB.LinComb, LB.wchart, Scheme.Hom.coe_preimage]
    first
      | exact Set.iInter_const _
      | simp
  have hxD : x ⁻¹ᵁ D = ⊤ := by
    rw [← hD]
    exact Scheme.Hom.preimage_opensRange x
  have hDle : D ≤ x.opensRange := hD.ge

  have hres : ∀ (A B : Z.Opens) (hAB : A ≤ B) (W : (Sp S).Opens) (hW : W ≤ x ⁻¹ᵁ A) (a : Γ(Z, B)),
      (x.appLE A W hW).hom (resG Z hAB a) = (x.appLE B W (hW.trans fun _ hz => hAB hz)).hom a := by
    intro A B hAB W hW a
    unfold resG
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

  have hres' : ∀ (A : Z.Opens) (W W' : (Sp S).Opens) (hW : W ≤ x ⁻¹ᵁ A) (hW' : W' ≤ W) (a : Γ(Z, A)),
      resG (Sp S) hW' ((x.appLE A W hW).hom a) = (x.appLE A W' (hW'.trans hW)).hom a := by
    intro A W W' hW hW' a
    unfold resG
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hcomp : ∀ (W₁ W₂ W₃ : (Sp S).Opens) (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂) (a : Γ(Sp S, W₁)),
      resG (Sp S) h₂ (resG (Sp S) h₁ a) = resG (Sp S) (h₂.trans h₁) a := by
    intro W₁ W₂ W₃ h₁ h₂ a
    unfold resG
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hbij := appLE_bijective x hDle hxD.ge le_top

  obtain ⟨r, hr⟩ : ∃ r : σ → Γ(Z, D),
      ∀ j, (x.appLE D ⊤ hxD.ge).hom (r j) = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v j) :=
    ⟨fun j => (hbij.2 _).choose, fun j => (hbij.2 _).choose_spec⟩
  refine ⟨r, fun j k => ?_, fun f => ?_⟩
  · have hk : x ⁻¹ᵁ (D ⊓ M.U k) ≤ (M.pull x).U (fun _ => k) := by
      rw [hU]
      exact fun _ hz => hz.2
    have key : ∀ (l : σ) (h' : x ⁻¹ᵁ (D ⊓ M.U k) ≤ x ⁻¹ᵁ M.U k),
        (x.appLE (M.U k) (x ⁻¹ᵁ (D ⊓ M.U k)) h').hom ((th l).f k) =
          resG (Sp S) hk (resG (Sp S) (le_top : (M.pull x).U (fun _ => k) ≤ ⊤)
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v l)) *
            ((τ.s fun _ => k).val : Γ(Sp S, (M.pull x).U fun _ => k))) := by
      intro l h'
      rw [← hvτ l (fun _ => k) (hU k).le, hres']
    have hrj : ∀ (h' : x ⁻¹ᵁ (D ⊓ M.U k) ≤ x ⁻¹ᵁ D),
        (x.appLE D (x ⁻¹ᵁ (D ⊓ M.U k)) h').hom (r j) =
          resG (Sp S) le_top ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v j)) := by
      intro h'
      rw [← hr j, hres']
    apply (appLE_bijective x (inf_le_left.trans hDle) le_rfl le_rfl).1
    rw [map_mul, hres, hres, hres, key j, key i, hrj, hi]
    simp only [map_one, _root_.one_mul, map_mul, hcomp]
  · obtain ⟨F, hF⟩ := hgen ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((x.appLE D ⊤ hxD.ge).hom f))
    refine ⟨F, hbij.1 ?_⟩
    have hbase : ∀ (g : Sp S ⟶ Sp K) (hg : g = spMap β) (e : (⊤ : (Sp S).Opens) ≤ g ⁻¹ᵁ ⊤) (c : K),
        (g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) =
          (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (β c) := by
      rintro g rfl e c
      exact GlobalTheory.ZM.Coord.appLE_spec β e c
    have h₁ : (x.appLE D ⊤ hxD.ge).hom.comp
        (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp β := by
      ext c
      show (x.appLE D ⊤ hxD.ge).hom ((p.appLE ⊤ D le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (β c)
      have hcc := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))
        (Scheme.Hom.appLE_comp_appLE x p ⊤ D ⊤ le_top hxD.ge)
      exact hcc.trans (hbase _ hx _ c)
    have h₂ : (x.appLE D ⊤ hxD.ge).hom ∘ r = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ∘ v := funext hr
    rw [MvPolynomial.eval₂_comp_left, h₁, h₂, ← MvPolynomial.eval₂_comp_left, ← hF,
      ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

/- English proof (translation)
Introduce `K σ _ _ I Z p M th h`. Use `⟨cover h, fun i => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hrange, hxs, hsc⟩` from `GlobalTheory.T.exists_nonzeroCoordinate_affineChart K σ I Z p M th i h`. Establish `hD : x.opensRange = Out.nonzeroLocus (th i)` using `TopologicalSpace.Opens.ext hrange`. Use `⟨hD ▸ isAffineOpen_opensRange x, ?_⟩` and prove the remaining obligations.

Use `ratios i _ x hD _ hxs _ hsc ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span rfl)`. Introduce `a`. Take `⟨F, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Use `⟨F, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← MvPolynomial.eval₂_eta F]`. Conclude with `MvPolynomial.eval₂_comp_left _ _ _ _`.
-/
theorem vAmp_of_projRep : ∀ (K σ : Type) [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (Z : Scheme.{0}) (p : Z ⟶ Sp K) (M : LB Z) (th : σ → M.Sec), ProjRep I p M th → VAmp p M th := by
  intro K σ _ _ I Z p M th h
  refine ⟨cover h, fun i => ?_⟩
  obtain ⟨x, hx, hrange, hxs, hsc⟩ := GlobalTheory.T.exists_nonzeroCoordinate_affineChart K σ I Z p M th i h
  have hD : x.opensRange = Out.nonzeroLocus (th i) := TopologicalSpace.Opens.ext hrange
  refine ⟨hD ▸ isAffineOpen_opensRange x, ?_⟩
  refine ratios i _ x hD _ hxs _ hsc ?_ ?_
  · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  · intro a
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨F, ?_⟩
    conv_lhs => rw [← MvPolynomial.eval₂_eta F]
    exact MvPolynomial.eval₂_comp_left _ _ _ _

end GlobalTheory.ZV.CoordEmbed
end
