import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsVeryGeneralPointOfHolomorphicFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨h1, h2, fun p => ?_⟩` and prove the remaining obligations. Take `⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩` from `h3 p`. Establish `hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))` using `(hc.map _).map _`. Take `⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T` from `Over.mk x) V).left, ⊤)ˣ, u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu`.

Use `⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩` and prove the remaining obligations. Establish `e` using `k8 i`. Establish `e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i))`. Rewrite using `[map_mul]`. Conclude with `map_mul _ _ _`.

Use `e1.trans ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, _root_.mul_assoc, hu']`. Conclude with `congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e`.
-/
theorem TObj.HasTh.unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 p
  have hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
    (hc.map _).map _
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)ˣ,
      u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e := k8 i
  have e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
        V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) := by
    rw [map_mul]
    exact map_mul _ _ _
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e

/- English proof (translation)
Introduce `o _ g N' J b em C Mat κ w w' d hL hL2 h3 _ _ hG 𝔭 h𝔭`. Take `⟨r, B, θ, hB, hC⟩` from `hG.fam`. Establish `: NeZero (N' ^ 2)` using `⟨pow_ne_zero _ (by omega)⟩`. Establish `hvg` using `fun i : {i : Fin r // (B i).Nonempty} => GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em (Ix g (N' ^ 2)) d (B i) (θ i) (hB i).1 (hB i).2.1 i.2 (hB i).2.2.1`. Use `choose z hz c hc hgen using hvg`.

Set `p : {i : Fin r // (B i).Nonempty} → Ideal (MvPolynomial (Ix g (N' ^ 2)) o)` to `fun i => RingHom.ker (MvPolynomial.eval₂Hom em (c i • θ i (z i)))`. Establish `hobj : ∀ i, ∃ t, C t ∧ t.HasTh (𝟙 _) (c i • θ i (z i))`. Introduce `i`. Take `⟨t, ht, hth⟩` from `((hB i).2.2.2 (z i) (hz i)).1`. Conclude with `⟨t, ht, hth.unit_mul (c i) (hc i).isUnit⟩`.

Establish `hle : ∀ i, thIdeal em C ≤ p i`. Introduce `i`. Take `⟨t, ht⟩` from `hobj i`. Conclude with `iInf_le_of_le t (iInf_le_of_le _ (iInf_le_of_le ht le_rfl))`. Establish `hge : Finset.univ.inf p ≤ thIdeal em C`.

Use `le_iInf fun t => le_iInf fun v => le_iInf fun htv => ?_` and prove the remaining obligations. Take `⟨i, z', hz', hth⟩` from `hC t htv.1`. Establish `hspan : Ideal.span (Set.range (θ i z')) = ⊤`. Take `⟨a, ha⟩` from `GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ t N' ℂ (𝟙 _) (θ i z') ⊥ (by omega) dvd_rfl hth Ideal.isPrime_bot 0`. Rewrite `ha` using `[Ideal.mem_bot]`.

Conclude with `Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)`. Take `⟨u, hu⟩` from `GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b _ _ t ℂ (𝟙 _) (θ i z') v hth htv.2 hspan`. Establish `hv : v = (u : ℂ) • θ i z'` using `funext fun a => hu a`. Introduce `F hF`. Establish `hF' : F ∈ p ⟨i, z', hz'⟩` using `Finset.inf_le (f := p) (Finset.mem_univ _) hF`.

Rewrite using `[RingHom.mem_ker, hv]`. Conclude with `hgen ⟨i, z', hz'⟩ F hF' z' hz' u u.ne_zero`. Establish `hp : 𝔭.IsPrime` using `h𝔭.1.1`. Take `⟨i, -, hi⟩` from `hp.inf_le'.mp (hge.trans h𝔭.1.2)`. Take `⟨t, ht, hth⟩` from `hobj i`.

Use `⟨t, _, ht, hth, le_antisymm hi ?_⟩` and prove the remaining obligations. Conclude with `h𝔭.2 ⟨RingHom.ker_isPrime _, hle i⟩ hi`.
-/
theorem exists_object_at_minimalPrime :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ w w' d, Out.Laws → Out.Laws2 → 3 ≤ N' → Odd N' → Countable o → GoodClass em C Mat κ w w' d → ∀ 𝔭 ∈ (thIdeal em C).minimalPrimes, ∃ t v, C t ∧ t.HasTh (𝟙 _) v ∧ RingHom.ker (MvPolynomial.eval₂Hom em v) = 𝔭 := by
  intro o _ g N' J b em C Mat κ w w' d hL hL2 h3 _ _ hG 𝔭 h𝔭
  classical
  obtain ⟨r, B, θ, hB, hC⟩ := hG.fam
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ (by omega)⟩
  have hvg := fun i : {i : Fin r // (B i).Nonempty} =>
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em (Ix g (N' ^ 2)) d (B i) (θ i)
      (hB i).1 (hB i).2.1 i.2 (hB i).2.2.1
  choose z hz c hc hgen using hvg
  let p : {i : Fin r // (B i).Nonempty} → Ideal (MvPolynomial (Ix g (N' ^ 2)) o) := fun i =>
    RingHom.ker (MvPolynomial.eval₂Hom em (c i • θ i (z i)))
  have hobj : ∀ i, ∃ t, C t ∧ t.HasTh (𝟙 _) (c i • θ i (z i)) := by
    intro i
    obtain ⟨t, ht, hth⟩ := ((hB i).2.2.2 (z i) (hz i)).1
    exact ⟨t, ht, hth.unit_mul (c i) (hc i).isUnit⟩
  have hle : ∀ i, thIdeal em C ≤ p i := by
    intro i
    obtain ⟨t, ht⟩ := hobj i
    exact iInf_le_of_le t (iInf_le_of_le _ (iInf_le_of_le ht le_rfl))
  have hge : Finset.univ.inf p ≤ thIdeal em C := by
    refine le_iInf fun t => le_iInf fun v => le_iInf fun htv => ?_
    obtain ⟨i, z', hz', hth⟩ := hC t htv.1
    have hspan : Ideal.span (Set.range (θ i z')) = ⊤ := by
      obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ t N' ℂ (𝟙 _) (θ i z') ⊥ (by omega)
        dvd_rfl hth Ideal.isPrime_bot 0
      rw [Ideal.mem_bot] at ha
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)
    obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b _ _ t ℂ (𝟙 _) (θ i z') v hth htv.2 hspan
    have hv : v = (u : ℂ) • θ i z' := funext fun a => hu a
    intro F hF
    have hF' : F ∈ p ⟨i, z', hz'⟩ := Finset.inf_le (f := p) (Finset.mem_univ _) hF
    rw [RingHom.mem_ker, hv]
    exact hgen ⟨i, z', hz'⟩ F hF' z' hz' u u.ne_zero
  have hp : 𝔭.IsPrime := h𝔭.1.1
  obtain ⟨i, -, hi⟩ := hp.inf_le'.mp (hge.trans h𝔭.1.2)
  obtain ⟨t, ht, hth⟩ := hobj i
  refine ⟨t, _, ht, hth, le_antisymm hi ?_⟩
  exact h𝔭.2 ⟨RingHom.ker_isPrime _, hle i⟩ hi

end GlobalTheory.ZM
