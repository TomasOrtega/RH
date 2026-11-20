import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

/- English proof (translation)
Take `⟨S, hS⟩` from `(IsNoetherian.noetherian (RingHom.ker (algebraMap A L)) : (RingHom.ker (algebraMap A L)).FG)`. Establish `hm : ∀ a : S, ∃ m : p.primeCompl, (m : A) * a = 0` using `fun a => by`. Establish `ha : (a : A) ∈ RingHom.ker (algebraMap A L)` using `hS ▸ Submodule.subset_span a.2`. Conclude with `(IsLocalization.map_eq_zero_iff p.primeCompl L _).1 ha`. Use `choose m hm using hm`.

Set `f : A` to `∏ a ∈ S.attach, (m a : A)`. Establish `hfc : f ∈ p.primeCompl` using `Submonoid.prod_mem _ fun a _ => (m a).2`. Establish `hkill : ∀ a ∈ RingHom.ker (algebraMap A L), f * a = 0`. Introduce `a ha`. Rewrite `ha` using `[← hS]`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨c, hc⟩ : (m ⟨b, hb⟩ : A) ∣ f` from `Finset.dvd_prod_of_mem _ (Finset.mem_attach _ _)`. Rewrite using `[hc, mul_comm (m ⟨b, hb⟩ : A) c, mul_assoc, hm ⟨b, hb⟩, mul_zero]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]`. Use `⟨f, hfc, fun B _ _ _ => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap A L f)` using `(IsLocalization.AtPrime.isUnit_to_map_iff L p f).2 hfc`. Set `g : B →+* L` to `IsLocalization.Away.lift f hu`.

Establish `hg : ∀ a : A, g (algebraMap A B a) = algebraMap A L a` using `fun a => IsLocalization.lift_eq _ _`. Establish `hfB : IsUnit (algebraMap A B f)` using `IsLocalization.Away.algebraMap_isUnit f`. Establish `hinj : Function.Injective g`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `b hb`.

Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers f) b`. Establish `h1` using `IsLocalization.mk'_spec B a s`. Establish `h2 : algebraMap A L a = 0` using `by rw [← hg, ← h1, map_mul, hb, zero_mul]`. Establish `h3 : algebraMap A B a = 0`. Use `congrArg (algebraMap A B) (hkill a h2)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_zero]`. Conclude with `(hfB.mul_right_eq_zero).1 this`. Establish `hsB : IsUnit (algebraMap A B s)` using `IsLocalization.map_units B s`. Rewrite `h1` using `[h3]`. Conclude with `(hsB.mul_left_eq_zero).1 h1`.

Conclude with `hinj.isDomain g`.
-/
theorem exists_notMem_away_isDomain {A L : Type} [CommRing A] [IsNoetherianRing A] [CommRing L]
    [IsDomain L] [Algebra A L] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime L p] :
    ∃ f : A, f ∉ p ∧ ∀ (B : Type) [CommRing B] [Algebra A B] [IsLocalization.Away f B],
      IsDomain B := by
  classical
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap A L)) :
    (RingHom.ker (algebraMap A L)).FG)
  have hm : ∀ a : S, ∃ m : p.primeCompl, (m : A) * a = 0 := fun a => by
    have ha : (a : A) ∈ RingHom.ker (algebraMap A L) := hS ▸ Submodule.subset_span a.2
    exact (IsLocalization.map_eq_zero_iff p.primeCompl L _).1 ha
  choose m hm using hm
  let f : A := ∏ a ∈ S.attach, (m a : A)
  have hfc : f ∈ p.primeCompl := Submonoid.prod_mem _ fun a _ => (m a).2
  have hkill : ∀ a ∈ RingHom.ker (algebraMap A L), f * a = 0 := by
    intro a ha
    rw [← hS] at ha
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨c, hc⟩ : (m ⟨b, hb⟩ : A) ∣ f := Finset.dvd_prod_of_mem _ (Finset.mem_attach _ _)
      rw [hc, mul_comm (m ⟨b, hb⟩ : A) c, mul_assoc, hm ⟨b, hb⟩, mul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  refine ⟨f, hfc, fun B _ _ _ => ?_⟩
  have hu : IsUnit (algebraMap A L f) := (IsLocalization.AtPrime.isUnit_to_map_iff L p f).2 hfc
  let g : B →+* L := IsLocalization.Away.lift f hu
  have hg : ∀ a : A, g (algebraMap A B a) = algebraMap A L a := fun a =>
    IsLocalization.lift_eq _ _
  have hfB : IsUnit (algebraMap A B f) := IsLocalization.Away.algebraMap_isUnit f
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) b
    have h1 := IsLocalization.mk'_spec B a s
    have h2 : algebraMap A L a = 0 := by rw [← hg, ← h1, map_mul, hb, zero_mul]
    have h3 : algebraMap A B a = 0 := by
      have := congrArg (algebraMap A B) (hkill a h2)
      rw [map_mul, map_zero] at this
      exact (hfB.mul_right_eq_zero).1 this
    have hsB : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
    rw [h3] at h1
    exact (hsB.mul_left_eq_zero).1 h1
  exact hinj.isDomain g

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ hX V x hx`. Take `⟨W, hW, hxW, hWV⟩` from `exists_isAffineOpen_mem_and_subset hx`. Establish `: IsNoetherianRing Γ(X, W)` using `IsLocallyNoetherian.component_noetherian ⟨W, hW⟩`. Set `: Algebra Γ(X, W) (X.presheaf.stalk x)` to `X.presheaf.algebra_section_stalk ⟨x, hxW⟩`. Establish `hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal` using `hW.isLocalization_stalk ⟨x, hxW⟩`.

Use `haveI := (hX x).1`. Take `⟨f, hf, hB⟩` from `exists_notMem_away_isDomain (L := X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal`. Use `hW.isLocalization_basicOpen f` as an intermediate fact. Use `⟨X.basicOpen f, (X.basicOpen_le f).trans hWV, ?_, hW.basicOpen f, hB _⟩` and prove the remaining obligations. Rewrite using `[Scheme.mem_basicOpen X f x hxW]`.

Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) _ f).2 hf`.
-/
theorem exists_isAffineOpen_isDomain_of_isNormalScheme :
    ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
      ∀ (V : X.Opens) (x : X), x ∈ V →
        ∃ U : X.Opens, U ≤ V ∧ x ∈ U ∧ IsAffineOpen U ∧ IsDomain Γ(X, U) := by
  intro X _ hX V x hx
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  haveI := (hX x).1
  obtain ⟨f, hf, hB⟩ := exists_notMem_away_isDomain (L := X.presheaf.stalk x)
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  have := hW.isLocalization_basicOpen f
  refine ⟨X.basicOpen f, (X.basicOpen_le f).trans hWV, ?_, hW.basicOpen f, hB _⟩
  rw [Scheme.mem_basicOpen X f x hxW]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) _ f).2 hf

end GlobalTheory
