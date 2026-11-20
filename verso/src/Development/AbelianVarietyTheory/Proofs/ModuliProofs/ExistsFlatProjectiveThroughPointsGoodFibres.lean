import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousComponentMemVanIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FlatFamily

open MvPolynomial in

/- English proof (translation)
Use `letI : GradedAlgebra (homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra`. Establish `hh : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R)`. Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations. Introduce and unpack `G ⟨hG, -⟩`. Conclude with `⟨d, (mem_homogeneousSubmodule d G).2 hG⟩`.

Conclude with `(MvPolynomial.mem_iff_homogeneousComponent_mem (h := hh) (p := F)).1 hF e`.
-/
theorem homogeneousComponent_mem_vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI : GradedAlgebra (homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
  have hh : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) := by
    refine Ideal.homogeneous_span _ _ ?_
    rintro G ⟨hG, -⟩
    exact ⟨d, (mem_homogeneousSubmodule d G).2 hG⟩
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem (h := hh) (p := F)).1 hF e

open MvPolynomial in

/- English proof (translation)
Establish `key : ∀ n e (F : MvPolynomial σ K), F.IsHomogeneous e → d ≤ e + n → F ∈ I → eval₂ β v F = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `e F hFe hd hFI`.

Conclude with `hJ F (hle e (by omega) F hFe hFI)`. Consider the case `succ n ih`. Introduce `e F hFe hd hFI`. Establish `hmul : ∀ i, v i * eval₂ β v F = 0`. Introduce `i`.

Establish `h` using `ih (1 + e) (X i * F) ((isHomogeneous_X K i).mul hFe) (by omega) (I.mul_mem_left _ hFI)`. Simplify `h` using `[eval₂_mul, eval₂_X]`. Establish `hall : ∀ y ∈ Ideal.span (Set.range v), y * eval₂ β v F = 0`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Conclude with `hmul i`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]`.

Consider the case `smul a b _ hb => rw [smul_eq_mul, _root_.mul_assoc, hb, mul_zero]`. Establish `h1 : (1 : T) ∈ Ideal.span (Set.range v)` using `by rw [hv]; exact Submodule.mem_top`. Simplify using `using hall 1 h1`. Introduce `F hF`. Use `conv_lhs => rw [← sum_homogeneousComponent F]`.

Rewrite using `[eval₂_sum]`. Conclude with `Finset.sum_eq_zero fun e _ => key d e _ (homogeneousComponent_isHomogeneous e F) (by omega) (hI F hF e)`.
-/
theorem eval₂_eq_zero_of_forms_le {K σ : Type} [CommRing K] {I J : Ideal (MvPolynomial σ K)} {d : ℕ}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (hle : ∀ e ≥ d, ∀ F : MvPolynomial σ K, F.IsHomogeneous e → F ∈ I → F ∈ J)
    {T : Type} [CommRing T] (β : K →+* T) (v : σ → T) (hv : Ideal.span (Set.range v) = ⊤)
    (hJ : ∀ F ∈ J, eval₂ β v F = 0) : ∀ F ∈ I, eval₂ β v F = 0 := by
  classical
  have key : ∀ n e (F : MvPolynomial σ K), F.IsHomogeneous e → d ≤ e + n → F ∈ I → eval₂ β v F = 0 := by
    intro n
    induction n with
    | zero =>
      intro e F hFe hd hFI
      exact hJ F (hle e (by omega) F hFe hFI)
    | succ n ih =>
      intro e F hFe hd hFI
      have hmul : ∀ i, v i * eval₂ β v F = 0 := by
        intro i
        have h := ih (1 + e) (X i * F) ((isHomogeneous_X K i).mul hFe) (by omega) (I.mul_mem_left _ hFI)
        simpa [eval₂_mul, eval₂_X] using h
      have hall : ∀ y ∈ Ideal.span (Set.range v), y * eval₂ β v F = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact hmul i
        | zero => simp
        | add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]
        | smul a b _ hb => rw [smul_eq_mul, _root_.mul_assoc, hb, mul_zero]
      have h1 : (1 : T) ∈ Ideal.span (Set.range v) := by rw [hv]; exact Submodule.mem_top
      simpa using hall 1 h1
  intro F hF
  conv_lhs => rw [← sum_homogeneousComponent F]
  rw [eval₂_sum]
  exact Finset.sum_eq_zero fun e _ => key d e _ (homogeneousComponent_isHomogeneous e F) (by omega) (hI F hF e)

/- English proof (translation)
Introduce `R σ Hh _ _ _ _ p Q d G hG hVD`. Establish `bc : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.m …` using `fun R R' σ _ _ φ I Z Z' s s' π M th h hpb => RepBC.projRep_baseChange R R' σ φ I Z Z' s s' π M th h hpb`. Take `⟨hproj, hfg, hbase⟩` from `GlobalTheory.FamAlg.forms_through_points R σ Hh p Q d _ hVD (by`. Introduce and unpack `q ⟨K, _, x, I, rfl, hGx⟩`. Conclude with `⟨K, _, x, I, rfl, (hG K x I hGx).2⟩)`.

Establish `hhom : ∀ F ∈ vanIdeal d p, ∀ e, MvPolynomial.homogeneousComponent e F ∈ vanIdeal d p` using `fun F hF e => homogeneousComponent_mem_vanIdeal d p F hF e`. Take `⟨Z₀, s, M, th, -, hrep, hlfp, hflat⟩` from `GlobalTheory.ProjFlat.exists_projRep_flat R σ (vanIdeal d p) d hhom`. Establish `hZ` using `GlobalTheory.ZM.projRep_projective_ample R σ (vanIdeal d p) (Over.mk s) M th hrep`. Use `⟨Over.mk s, M, th, hrep, hZ.1, hflat (fun e he => by haveI := hproj e he; infer_instance), hlfp hfg, ?_⟩` and prove the remaining obligations. Introduce `K _ x I' X s' M' th' hGx hrep'`.

Take `⟨hI'hom, hcut⟩` from `hG K x I' hGx`. Establish `hpb` using `IsPullback.of_hasPullback s (spMap x)`. Take `⟨th₁, hrep₁, hsec₁⟩` from `bc R K σ x (vanIdeal d p) Z₀ (pullback s (spMap x)) s (pullback.snd s (spMap x)) (pullback.fst s (spMap x)) M th hrep hpb`. Rewrite `hrep₁` using `[hbase K x]`. Establish `heqv : ∀ (R' : Type) [CommRing R'] (β : K →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ → ((∀ F ∈ I', MvPolynomial.eval₂ β v F = 0) ↔ ∀ F ∈ vanIdeal d (fun h i => x (p h i)), MvPolynomial.eval₂ β v F = 0)`.

Introduce `R' _ β v hv`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `eval₂_eq_zero_of_forms_le (fun F hF e => homogeneousComponent_mem_vanIdeal d _ F hF e) (fun e he F hFe hF => ((hcut e he).2 F hFe).2 hF) β v hv h`. Introduce `h`.

Conclude with `eval₂_eq_zero_of_forms_le hI'hom (fun e he F hFe hF => ((hcut e he).2 F hFe).1 hF) β v hv h`. Take `⟨e, hes, hlb, hsc⟩` from `GlobalTheory.RepUniq.exists_iso_of_projRep K σ I' _ X _ s' _ M' _ th' th₁ hrep' hrep₁ heqv`. Establish `hsc' : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ e.hom ≫ pullback.fst s (spMap x)) w`. Introduce `T _ y w`. Rewrite using `[hsc, hsec₁, Category.assoc]`.

Establish `hsame : GlobalTheory.RepUniq.Same M' th' (𝟙 X) M th (e.hom ≫ pullback.fst s (spMap x))`. Use `GlobalTheory.RepUniq.same_of_local fun t => ?_` and prove the remaining obligations. Take `⟨W, hW, j, hj, htW, hW'⟩` from `GlobalTheory.RepUniq.exists_affine_secCoord hrep'.1 th' (𝟙 X) t`. Use `⟨W, htW, ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.RepUniq.locCoord_of_secCoord hrep'.1 hW'`.

Establish `h2` using `GlobalTheory.RepUniq.locCoord_of_secCoord hrep.1 ((hsc' _ _ _).1 hW')`. Establish `h3` using `(h1.same h2).comp hW.isoSpec.hom`. Establish `h4 : hW.isoSpec.hom ≫ hW.fromSpec = W.ι` using `GlobalTheory.RepUniq.isoSpec_hom_fromSpec hW`. Simplify using `only [Category.comp_id, ← Category.assoc, h4] at h3 ⊢`. Conclude with `h3`.

Use `⟨e.hom ≫ pullback.fst s (spMap x), ?_, GlobalTheory.RepUniq.lbIso_of_same hrep' hsame, hsc'⟩` and prove the remaining obligations. Establish `sq1 : IsPullback e.hom s' (pullback.snd s (spMap x)) (𝟙 _)` using `IsPullback.of_horiz_isIso ⟨by rw [hes, Category.comp_id]⟩`. Simplify using `using sq1.paste_horiz hpb`.
-/
theorem exists_flat_projRep_vanIdeal : ∀ (R σ Hh : Type) [CommRing R] [IsReduced R] [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), Ideal (MvPolynomial σ K) → Prop), (∀ (K : Type) [Field K] (x : R →+* K) I, G K x I → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧ CutBy I Q d (fun h i => x (p h i))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : _), RingHom.ker x = q ∧ G K x I} → ∃ (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep (vanIdeal d p) Z.hom M th ∧ IsProjOver Z.hom ∧ Flat Z.hom ∧ LocallyOfFinitePresentation Z.hom ∧ ∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial σ K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : σ → M'.Sec), G K x I → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w := by
  intro R σ Hh _ _ _ _ p Q d G hG hVD
  classical
  have bc : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := fun R R' σ _ _ φ I Z Z' s s' π M th h hpb => RepBC.projRep_baseChange R R' σ φ I Z Z' s s' π M th h hpb
  obtain ⟨hproj, hfg, hbase⟩ := GlobalTheory.FamAlg.forms_through_points R σ Hh p Q d _ hVD (by
    rintro q ⟨K, _, x, I, rfl, hGx⟩
    exact ⟨K, _, x, I, rfl, (hG K x I hGx).2⟩)
  have hhom : ∀ F ∈ vanIdeal d p, ∀ e, MvPolynomial.homogeneousComponent e F ∈ vanIdeal d p :=
    fun F hF e => homogeneousComponent_mem_vanIdeal d p F hF e
  obtain ⟨Z₀, s, M, th, -, hrep, hlfp, hflat⟩ := GlobalTheory.ProjFlat.exists_projRep_flat R σ (vanIdeal d p) d hhom
  have hZ := GlobalTheory.ZM.projRep_projective_ample R σ (vanIdeal d p) (Over.mk s) M th hrep
  refine ⟨Over.mk s, M, th, hrep, hZ.1, hflat (fun e he => by haveI := hproj e he; infer_instance), hlfp hfg, ?_⟩
  intro K _ x I' X s' M' th' hGx hrep'
  obtain ⟨hI'hom, hcut⟩ := hG K x I' hGx
  have hpb := IsPullback.of_hasPullback s (spMap x)
  obtain ⟨th₁, hrep₁, hsec₁⟩ := bc R K σ x (vanIdeal d p) Z₀ (pullback s (spMap x)) s
    (pullback.snd s (spMap x)) (pullback.fst s (spMap x)) M th hrep hpb
  rw [hbase K x] at hrep₁
  have heqv : ∀ (R' : Type) [CommRing R'] (β : K →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ →
      ((∀ F ∈ I', MvPolynomial.eval₂ β v F = 0) ↔
        ∀ F ∈ vanIdeal d (fun h i => x (p h i)), MvPolynomial.eval₂ β v F = 0) := by
    intro R' _ β v hv
    constructor
    · intro h
      exact eval₂_eq_zero_of_forms_le (fun F hF e => homogeneousComponent_mem_vanIdeal d _ F hF e)
        (fun e he F hFe hF => ((hcut e he).2 F hFe).2 hF) β v hv h
    · intro h
      exact eval₂_eq_zero_of_forms_le hI'hom (fun e he F hFe hF => ((hcut e he).2 F hFe).1 hF) β v hv h
  obtain ⟨e, hes, hlb, hsc⟩ := GlobalTheory.RepUniq.exists_iso_of_projRep K σ I' _ X _ s' _ M' _ th' th₁ hrep' hrep₁ heqv
  have hsc' : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T),
      SecCoord M' th' y w ↔ SecCoord M th (y ≫ e.hom ≫ pullback.fst s (spMap x)) w := by
    intro T _ y w
    rw [hsc, hsec₁, Category.assoc]
  have hsame : GlobalTheory.RepUniq.Same M' th' (𝟙 X) M th (e.hom ≫ pullback.fst s (spMap x)) := by
    refine GlobalTheory.RepUniq.same_of_local fun t => ?_
    obtain ⟨W, hW, j, hj, htW, hW'⟩ := GlobalTheory.RepUniq.exists_affine_secCoord hrep'.1 th' (𝟙 X) t
    refine ⟨W, htW, ?_⟩
    have h1 := GlobalTheory.RepUniq.locCoord_of_secCoord hrep'.1 hW'
    have h2 := GlobalTheory.RepUniq.locCoord_of_secCoord hrep.1 ((hsc' _ _ _).1 hW')
    have h3 := (h1.same h2).comp hW.isoSpec.hom
    have h4 : hW.isoSpec.hom ≫ hW.fromSpec = W.ι := GlobalTheory.RepUniq.isoSpec_hom_fromSpec hW
    simp only [Category.comp_id, ← Category.assoc, h4] at h3 ⊢
    exact h3
  refine ⟨e.hom ≫ pullback.fst s (spMap x), ?_, GlobalTheory.RepUniq.lbIso_of_same hrep' hsame, hsc'⟩
  · have sq1 : IsPullback e.hom s' (pullback.snd s (spMap x)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hes, Category.comp_id]⟩
    simpa using sq1.paste_horiz hpb

end GlobalTheory.ZM.FlatFamily
