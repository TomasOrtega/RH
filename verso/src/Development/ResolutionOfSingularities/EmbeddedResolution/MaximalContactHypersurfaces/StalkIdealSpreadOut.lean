import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartFiberProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.TaylorExpansion
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.TaylorExpansionComparison
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Use `hM` as an intermediate fact. Take `⟨G, hG⟩` from `hA`. Establish `key : ∀ a : R, ∃ u : R, u ∈ M ∧ (a ∈ A → u * a ∈ B)`. Introduce `a`. Distinguish the cases in `ha : a ∈ A`.

Establish `h1 : algebraMap R S a ∈ Ideal.map (algebraMap R S) B` using `hAB (Ideal.mem_map_of_mem _ ha)`. Rewrite `h1` using `[IsLocalization.mem_map_algebraMap_iff (M := M) (S := S)]`. Take `⟨⟨b, s⟩, hEq⟩` from `h1`. Rewrite `hEq` using `[← map_mul]`. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists (M := M) (S := S)).mp hEq`.

Use `⟨(c : R) * (s : R), M.mul_mem c.2 s.2, fun _ => ?_⟩` and prove the remaining obligations. Establish `hcalc : (c : R) * (s : R) * a = (c : R) * (b : R)` using `by linear_combination hc`. Rewrite using `[hcalc]`. Conclude with `Ideal.mul_mem_left B _ b.2`. Conclude with `⟨1, M.one_mem, fun hmem => absurd hmem ha⟩`.

Use `choose u huM huB using key`. Use `⟨∏ g ∈ G, u g, (Submonoid.prod_mem M fun g _ => huM g), ?_⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite `ha` using `[← hG]`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem z hz`. Establish `hzG : z ∈ G` using `Finset.mem_coe.mp hz`. Establish `hzA : z ∈ A` using `by rw [← hG]; exact Submodule.subset_span hz`. Rewrite using `[← Finset.mul_prod_erase G u hzG]`. Establish `hre : u z * (∏ g ∈ G.erase z, u g) * z = (∏ g ∈ G.erase z, u g) * (u z * z)` using `by ring`.

Rewrite using `[hre]`. Conclude with `Ideal.mul_mem_left B _ (huB z hzA)`. Consider the case `zero => rw [mul_zero]`. Conclude with `B.zero_mem`. Consider the case `add y z _ _ hy hz => rw [mul_add]`.

Conclude with `B.add_mem hy hz`. Consider the case `smul c y _ hy`. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `Ideal.mul_mem_left B c hy`.
-/
private theorem exists_mem_mul_mem_of_map_le {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) (hM : IsLocalization M S) (A B : Ideal R)
    (hA : Submodule.FG A)
    (hAB : Ideal.map (algebraMap R S) A ≤ Ideal.map (algebraMap R S) B) :
    ∃ u : R, u ∈ M ∧ ∀ a ∈ A, u * a ∈ B := by
  classical
  have := hM
  obtain ⟨G, hG⟩ := hA
  have key : ∀ a : R, ∃ u : R, u ∈ M ∧ (a ∈ A → u * a ∈ B) := by
    intro a
    by_cases ha : a ∈ A
    · have h1 : algebraMap R S a ∈ Ideal.map (algebraMap R S) B :=
        hAB (Ideal.mem_map_of_mem _ ha)
      rw [IsLocalization.mem_map_algebraMap_iff (M := M) (S := S)] at h1
      obtain ⟨⟨b, s⟩, hEq⟩ := h1
      rw [← map_mul] at hEq
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := S)).mp hEq
      refine ⟨(c : R) * (s : R), M.mul_mem c.2 s.2, fun _ => ?_⟩
      have hcalc : (c : R) * (s : R) * a = (c : R) * (b : R) := by linear_combination hc
      rw [hcalc]
      exact Ideal.mul_mem_left B _ b.2
    · exact ⟨1, M.one_mem, fun hmem => absurd hmem ha⟩
  choose u huM huB using key
  refine ⟨∏ g ∈ G, u g, (Submonoid.prod_mem M fun g _ => huM g), ?_⟩
  intro a ha
  rw [← hG] at ha
  induction ha using Submodule.span_induction with
  | mem z hz =>
      have hzG : z ∈ G := Finset.mem_coe.mp hz
      have hzA : z ∈ A := by rw [← hG]; exact Submodule.subset_span hz
      rw [← Finset.mul_prod_erase G u hzG]
      have hre : u z * (∏ g ∈ G.erase z, u g) * z
          = (∏ g ∈ G.erase z, u g) * (u z * z) := by ring
      rw [hre]
      exact Ideal.mul_mem_left B _ (huB z hzA)
  | zero => rw [mul_zero]; exact B.zero_mem
  | add y z _ _ hy hz => rw [mul_add]; exact B.add_mem hy hz
  | smul c y _ hy =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left B c hy

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Take `⟨t, ht⟩` from `hw.exists_right_inv`. Establish `h1 : φ (w * a) ∈ Ideal.map φ B` using `Ideal.mem_map_of_mem φ (hAB a ha)`. Establish `h4 : t * φ (w * a) ∈ Ideal.map φ B` using `Ideal.mul_mem_left _ _ h1`.

Rewrite `h4` using `[map_mul, ← mul_assoc, mul_comm t (φ w), ht, one_mul]`. Conclude with `Ideal.mem_comap.mpr h4`.
-/
private theorem map_le_map_of_isUnit_mul_mem {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (w : R) (hw : IsUnit (φ w)) (A B : Ideal R)
    (hAB : ∀ a ∈ A, w * a ∈ B) :
    Ideal.map φ A ≤ Ideal.map φ B := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  obtain ⟨t, ht⟩ := hw.exists_right_inv
  have h1 : φ (w * a) ∈ Ideal.map φ B := Ideal.mem_map_of_mem φ (hAB a ha)
  have h4 : t * φ (w * a) ∈ Ideal.map φ B := Ideal.mul_mem_left _ _ h1
  rw [map_mul, ← mul_assoc, mul_comm t (φ w), ht, one_mul] at h4
  exact Ideal.mem_comap.mpr h4

/- English proof (translation)
Take `⟨U, hxU, hU⟩` from `Scheme.exists_isAffineOpen_mem x`. Establish `hUaff : IsAffineOpen U` using `hU`. Establish `: IsNoetherianRing Γ(X, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Set `instAlg : Algebra Γ(X, U) ↑(X.presheaf.stalk x)` to `(X.presheaf.germ U x hxU).hom.toAlgebra`. Establish `halg : (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) = (X.presheaf.germ U x hxU).hom` using `rfl`.

Establish `hloc : IsLocalization (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ↑(X.presheaf.stalk x)` using `hUaff.isLocalization_stalk ⟨x, hxU⟩`. Establish `hmapeq : Ideal.map (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) (I.ideal ⟨U, hU⟩) = Ideal.map (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) (J.ideal ⟨U, hU⟩)`. Establish `h1` using `stalkIdeal_eq_map_germ I x ⟨U, hU⟩ hxU`. Establish `h2` using `stalkIdeal_eq_map_germ J x ⟨U, hU⟩ hxU`. Rewrite `h` using `[h1, h2]`.

Rewrite using `[halg]`. Conclude with `h`. Take `⟨u₁, hu₁M, hu₁⟩` from `exists_mem_mul_mem_of_map_le _ hloc (I.ideal ⟨U, hU⟩) (J.ideal ⟨U, hU⟩) (IsNoetherian.noetherian _) (le_of_eq hmapeq)`. Take `⟨u₂, hu₂M, hu₂⟩` from `exists_mem_mul_mem_of_map_le _ hloc (J.ideal ⟨U, hU⟩) (I.ideal ⟨U, hU⟩) (IsNoetherian.noetherian _) (le_of_eq hmapeq.symm)`. Establish `hmb : ∀ (z : ↥X) (hz : z ∈ U), z ∈ X.basicOpen (u₁ * u₂) ↔ IsUnit ((X.presheaf.germ U z hz).hom (u₁ * u₂))`.

Introduce `z hz`. Conclude with `X.mem_basicOpen (u₁ * u₂) z hz`. Establish `hxunit : IsUnit ((X.presheaf.germ U x hxU).hom (u₁ * u₂))`. Establish `hmem : u₁ * u₂ ∈ (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl` using `Submonoid.mul_mem _ hu₁M hu₂M`. Establish `hone` using `IsLocalization.map_units (M := (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) (S := ↑(X.presheaf.stalk x)) ⟨u₁ * u₂, hmem⟩`.

Rewrite `hone` using `[halg]`. Conclude with `hone`. Use `⟨X.basicOpen (u₁ * u₂), (hmb x hxU).mpr hxunit, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hyU : y ∈ U` using `X.basicOpen_le (u₁ * u₂) hy`.

Establish `hyunit : IsUnit ((X.presheaf.germ U y hyU).hom (u₁ * u₂))` using `(hmb y hyU).mp hy`. Establish `hv1 : ∀ a ∈ I.ideal ⟨U, hU⟩, u₁ * u₂ * a ∈ J.ideal ⟨U, hU⟩`. Introduce `a ha`. Establish `he : u₁ * u₂ * a = u₂ * (u₁ * a)` using `by ring`. Rewrite using `[he]`.

Conclude with `Ideal.mul_mem_left _ _ (hu₁ a ha)`. Establish `hv2 : ∀ a ∈ J.ideal ⟨U, hU⟩, u₁ * u₂ * a ∈ I.ideal ⟨U, hU⟩`. Introduce `a ha`. Establish `he : u₁ * u₂ * a = u₁ * (u₂ * a)` using `by ring`. Rewrite using `[he]`.

Conclude with `Ideal.mul_mem_left _ _ (hu₂ a ha)`. Rewrite using `[stalkIdeal_eq_map_germ I y ⟨U, hU⟩ hyU, stalkIdeal_eq_map_germ J y ⟨U, hU⟩ hyU]`. Conclude with `le_antisymm (map_le_map_of_isUnit_mul_mem (X.presheaf.germ U y hyU).hom (u₁ * u₂) hyunit _ _ hv1) (map_le_map_of_isUnit_mul_mem (X.presheaf.germ U y hyU).hom (u₁ * u₂) hyunit _ _ hv2)`.
-/
theorem exists_opens_stalkIdeal_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (x : X) (h : stalkIdeal I x = stalkIdeal J x) :
    ∃ W : X.Opens, x ∈ W ∧ ∀ y : X, y ∈ W → stalkIdeal I y = stalkIdeal J y := by
  obtain ⟨U, hxU, hU⟩ := Scheme.exists_isAffineOpen_mem x
  have hUaff : IsAffineOpen U := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let instAlg : Algebra Γ(X, U) ↑(X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have halg : (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) = (X.presheaf.germ U x hxU).hom := rfl
  have hloc : IsLocalization (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      ↑(X.presheaf.stalk x) := hUaff.isLocalization_stalk ⟨x, hxU⟩
  have hmapeq : Ideal.map (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) (I.ideal ⟨U, hU⟩)
      = Ideal.map (algebraMap Γ(X, U) ↑(X.presheaf.stalk x)) (J.ideal ⟨U, hU⟩) := by
    have h1 := stalkIdeal_eq_map_germ I x ⟨U, hU⟩ hxU
    have h2 := stalkIdeal_eq_map_germ J x ⟨U, hU⟩ hxU
    rw [h1, h2] at h
    rw [halg]
    exact h
  obtain ⟨u₁, hu₁M, hu₁⟩ := exists_mem_mul_mem_of_map_le _ hloc (I.ideal ⟨U, hU⟩)
    (J.ideal ⟨U, hU⟩) (IsNoetherian.noetherian _) (le_of_eq hmapeq)
  obtain ⟨u₂, hu₂M, hu₂⟩ := exists_mem_mul_mem_of_map_le _ hloc (J.ideal ⟨U, hU⟩)
    (I.ideal ⟨U, hU⟩) (IsNoetherian.noetherian _) (le_of_eq hmapeq.symm)
  have hmb : ∀ (z : ↥X) (hz : z ∈ U),
      z ∈ X.basicOpen (u₁ * u₂) ↔ IsUnit ((X.presheaf.germ U z hz).hom (u₁ * u₂)) := by
    intro z hz
    exact X.mem_basicOpen (u₁ * u₂) z hz
  have hxunit : IsUnit ((X.presheaf.germ U x hxU).hom (u₁ * u₂)) := by
    have hmem : u₁ * u₂ ∈ (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl :=
      Submonoid.mul_mem _ hu₁M hu₂M
    have hone := IsLocalization.map_units
      (M := (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
      (S := ↑(X.presheaf.stalk x)) ⟨u₁ * u₂, hmem⟩
    rw [halg] at hone
    exact hone
  refine ⟨X.basicOpen (u₁ * u₂), (hmb x hxU).mpr hxunit, ?_⟩
  intro y hy
  have hyU : y ∈ U := X.basicOpen_le (u₁ * u₂) hy
  have hyunit : IsUnit ((X.presheaf.germ U y hyU).hom (u₁ * u₂)) := (hmb y hyU).mp hy
  have hv1 : ∀ a ∈ I.ideal ⟨U, hU⟩, u₁ * u₂ * a ∈ J.ideal ⟨U, hU⟩ := by
    intro a ha
    have he : u₁ * u₂ * a = u₂ * (u₁ * a) := by ring
    rw [he]
    exact Ideal.mul_mem_left _ _ (hu₁ a ha)
  have hv2 : ∀ a ∈ J.ideal ⟨U, hU⟩, u₁ * u₂ * a ∈ I.ideal ⟨U, hU⟩ := by
    intro a ha
    have he : u₁ * u₂ * a = u₁ * (u₂ * a) := by ring
    rw [he]
    exact Ideal.mul_mem_left _ _ (hu₂ a ha)
  rw [stalkIdeal_eq_map_germ I y ⟨U, hU⟩ hyU, stalkIdeal_eq_map_germ J y ⟨U, hU⟩ hyU]
  exact le_antisymm
    (map_le_map_of_isUnit_mul_mem (X.presheaf.germ U y hyU).hom (u₁ * u₂) hyunit _ _ hv1)
    (map_le_map_of_isUnit_mul_mem (X.presheaf.germ U y hyU).hom (u₁ * u₂) hyunit _ _ hv2)

/- English proof (translation)
The claim follows from `hx`.
-/
private theorem notMem_of_mem_primeCompl {R : Type*} [CommRing R] {m : Ideal R} [m.IsPrime]
    {x : R} (hx : x ∈ m.primeCompl) : x ∉ m := hx

/- English proof (translation)
Establish `hmem : algebraMap R S a ∈ Ideal.map (algebraMap R S) B` using `hAB (Ideal.mem_map_of_mem _ ha)`. Take `⟨⟨b, s⟩, hbs⟩` from `(IsLocalization.mem_map_algebraMap_iff m.primeCompl S).mp hmem`. Establish `hbs' : algebraMap R S (a * (s : R)) = algebraMap R S (b : R)`. Rewrite using `[map_mul]`. Conclude with `hbs`.

Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists m.primeCompl S).mp hbs'`. Establish `hc2 : (c : R) ∉ m` using `notMem_of_mem_primeCompl c.2`. Establish `hs2 : (s : R) ∉ m` using `notMem_of_mem_primeCompl s.2`. Use `⟨(c : R) * (s : R), ?_, ?_⟩` and prove the remaining obligations. Introduce `hcs`.

Break down `hmp.mem_or_mem hcs with h1 | h1` into its components or cases. Conclude with `hc2 h1`. Conclude with `hs2 h1`. Establish `hEq : ((c : R) * (s : R)) * a = (c : R) * (b : R)`. Rewrite using `[← hc]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hEq]`. Conclude with `Ideal.mul_mem_left _ _ b.2`.
-/
private theorem exists_notMem_mul_mem_of_map_le {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] (m : Ideal R) [hmp : m.IsPrime] [IsLocalization m.primeCompl S]
    {A B : Ideal R} (hAB : Ideal.map (algebraMap R S) A ≤ Ideal.map (algebraMap R S) B)
    {a : R} (ha : a ∈ A) : ∃ t : R, t ∉ m ∧ t * a ∈ B := by
  have hmem : algebraMap R S a ∈ Ideal.map (algebraMap R S) B :=
    hAB (Ideal.mem_map_of_mem _ ha)
  obtain ⟨⟨b, s⟩, hbs⟩ := (IsLocalization.mem_map_algebraMap_iff m.primeCompl S).mp hmem
  have hbs' : algebraMap R S (a * (s : R)) = algebraMap R S (b : R) := by
    rw [map_mul]
    exact hbs
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists m.primeCompl S).mp hbs'
  have hc2 : (c : R) ∉ m := notMem_of_mem_primeCompl c.2
  have hs2 : (s : R) ∉ m := notMem_of_mem_primeCompl s.2
  refine ⟨(c : R) * (s : R), ?_, ?_⟩
  · intro hcs
    rcases hmp.mem_or_mem hcs with h1 | h1
    · exact hc2 h1
    · exact hs2 h1
  · have hEq : ((c : R) * (s : R)) * a = (c : R) * (b : R) := by
      rw [← hc]
      ring
    rw [hEq]
    exact Ideal.mul_mem_left _ _ b.2

/- English proof (translation)
Introduce `a ha`. Assume the negation of the conclusion as `hab`. Choose the witnesses or unpack the hypotheses as in `⟨C, hCmem⟩ : ∃ C : Ideal R, ∀ r : R, r ∈ C ↔ r * a ∈ B := by`. Use `⟨{ carrier := {r : R | r * a ∈ B} add_mem' := ?_ zero_mem' := ?_ smul_mem' := ?_ }, fun r => Iff.rfl⟩` and prove the remaining obligations. Introduce `x y hx hy show (x + y) * a ∈ B`.

Rewrite using `[add_mul]`. Conclude with `B.add_mem hx hy`. Use `show (0 : R) * a ∈ B`. Rewrite using `[zero_mul]`. Conclude with `B.zero_mem`.

Introduce `c x hx show (c • x) * a ∈ B`. Rewrite using `[smul_eq_mul, mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ hx`. Establish `hCne : C ≠ ⊤`. Introduce `hCtop`.

Establish `h1 : (1 : R) ∈ C`. Rewrite using `[hCtop]`. Conclude with `Submodule.mem_top`. Establish `h2` using `(hCmem 1).mp h1`. Rewrite `h2` using `[one_mul]`.

Conclude with `hab h2`. Take `⟨m, hm, hCm⟩` from `Ideal.exists_le_maximal C hCne`. Take `⟨t, htm, htB⟩` from `h m hm a ha`. Conclude with `htm (hCm ((hCmem t).mpr htB))`.
-/
private theorem le_of_forall_isMaximal_exists_mul_mem {R : Type*} [CommRing R] {A B : Ideal R}
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ a ∈ A, ∃ t : R, t ∉ m ∧ t * a ∈ B) : A ≤ B := by
  intro a ha
  by_contra hab
  obtain ⟨C, hCmem⟩ : ∃ C : Ideal R, ∀ r : R, r ∈ C ↔ r * a ∈ B := by
    refine ⟨{ carrier := {r : R | r * a ∈ B}
              add_mem' := ?_
              zero_mem' := ?_
              smul_mem' := ?_ }, fun r => Iff.rfl⟩
    · intro x y hx hy
      show (x + y) * a ∈ B
      rw [add_mul]
      exact B.add_mem hx hy
    · show (0 : R) * a ∈ B
      rw [zero_mul]
      exact B.zero_mem
    · intro c x hx
      show (c • x) * a ∈ B
      rw [smul_eq_mul, mul_assoc]
      exact Ideal.mul_mem_left _ _ hx
  have hCne : C ≠ ⊤ := by
    intro hCtop
    have h1 : (1 : R) ∈ C := by
      rw [hCtop]
      exact Submodule.mem_top
    have h2 := (hCmem 1).mp h1
    rw [one_mul] at h2
    exact hab h2
  obtain ⟨m, hm, hCm⟩ := Ideal.exists_le_maximal C hCne
  obtain ⟨t, htm, htB⟩ := h m hm a ha
  exact htm (hCm ((hCmem t).mpr htB))

/- English proof (translation)
Use `le_of_forall_isMaximal_exists_mul_mem ?_` and prove the remaining obligations. Introduce `m hm a ha`. Establish `hmp : m.IsPrime` using `hm.isPrime`. Use `set y : PrimeSpectrum Γ(Y, W.1) := ⟨m, hmp⟩ with hydef`. Use `set x : ↥Y := W.2.fromSpec.base y with hxdef`.

Establish `hy : x ∈ W.1`. Establish `hmem : x ∈ Set.range (W.2.fromSpec.base)` using `⟨y, rfl⟩`. Rewrite `hmem` using `[W.2.range_fromSpec]`. Conclude with `hmem`. Set `algI : Algebra Γ(Y, W.1) ↑(Y.presheaf.stalk x)` to `(Y.presheaf.germ W.1 x hy).hom.toAlgebra`.

Establish `hloc : IsLocalization m.primeCompl ↑(Y.presheaf.stalk x)` using `W.2.isLocalization_stalk' y hy`. Use `exists_notMem_mul_mem_of_map_le (↑(Y.presheaf.stalk x)) m ?_ ha` and prove the remaining obligations. Establish `halg : (algebraMap Γ(Y, W.1) ↑(Y.presheaf.stalk x)) = (Y.presheaf.germ W.1 x hy).hom` using `rfl`. Rewrite using `[halg, ← stalkIdeal_eq_map_germ A x W hy, ← stalkIdeal_eq_map_germ B x W hy]`. Conclude with `h x hy`.
-/
private theorem ideal_le_of_stalkIdeal_le {Y : Scheme.{u}} (A B : Y.IdealSheafData)
    (W : Y.affineOpens) (h : ∀ x : ↥Y, x ∈ W.1 → stalkIdeal A x ≤ stalkIdeal B x) :
    A.ideal W ≤ B.ideal W := by
  refine le_of_forall_isMaximal_exists_mul_mem ?_
  intro m hm a ha
  have hmp : m.IsPrime := hm.isPrime
  set y : PrimeSpectrum Γ(Y, W.1) := ⟨m, hmp⟩ with hydef
  set x : ↥Y := W.2.fromSpec.base y with hxdef
  have hy : x ∈ W.1 := by
    have hmem : x ∈ Set.range (W.2.fromSpec.base) := ⟨y, rfl⟩
    rw [W.2.range_fromSpec] at hmem
    exact hmem
  let algI : Algebra Γ(Y, W.1) ↑(Y.presheaf.stalk x) :=
    (Y.presheaf.germ W.1 x hy).hom.toAlgebra
  have hloc : IsLocalization m.primeCompl ↑(Y.presheaf.stalk x) :=
    W.2.isLocalization_stalk' y hy
  refine exists_notMem_mul_mem_of_map_le (↑(Y.presheaf.stalk x)) m ?_ ha
  have halg : (algebraMap Γ(Y, W.1) ↑(Y.presheaf.stalk x))
      = (Y.presheaf.germ W.1 x hy).hom := rfl
  rw [halg, ← stalkIdeal_eq_map_germ A x W hy, ← stalkIdeal_eq_map_germ B x W hy]
  exact h x hy

/- English proof (translation)
The claim follows from `le_antisymm (ideal_le_of_stalkIdeal_le A B W fun x hx => le_of_eq (h x hx)) (ideal_le_of_stalkIdeal_le B A W fun x hx => le_of_eq (h x hx).symm)`.
-/
private theorem ideal_eq_of_stalkIdeal_eq {Y : Scheme.{u}} (A B : Y.IdealSheafData)
    (W : Y.affineOpens) (h : ∀ x : ↥Y, x ∈ W.1 → stalkIdeal A x = stalkIdeal B x) :
    A.ideal W = B.ideal W :=
  le_antisymm (ideal_le_of_stalkIdeal_le A B W fun x hx => le_of_eq (h x hx))
    (ideal_le_of_stalkIdeal_le B A W fun x hx => le_of_eq (h x hx).symm)

/- English proof (translation)
Establish `key : ∀ V : U.toScheme.affineOpens, (restrictIdeal I U).ideal V = (restrictIdeal J U).ideal V`. Introduce `V`. Establish `hWaff : IsAffineOpen (U.ι ''ᵁ V.1)` using `V.2.image_of_isOpenImmersion U.ι`. Establish `hWU : (U.ι ''ᵁ V.1) ≤ U`. Introduce `z hz`.

Establish `hz' : z ∈ (fun w => U.ι.base w) '' (↑V.1 : Set U.toScheme)` using `hz`. Take `⟨v, -, rfl⟩` from `hz'`. Conclude with `v.2`. Establish `e : V.1 ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V.1)`. Introduce `v hv`.

Establish `h2 : U.ι.base v ∈ (fun w => U.ι.base w) '' (↑V.1 : Set U.toScheme)` using `⟨v, hv, rfl⟩`. Conclude with `h2`. Establish `hIJ : I.ideal ⟨U.ι ''ᵁ V.1, hWaff⟩ = J.ideal ⟨U.ι ''ᵁ V.1, hWaff⟩`. Use `ideal_eq_of_stalkIdeal_eq I J ⟨U.ι ''ᵁ V.1, hWaff⟩ ?_` and prove the remaining obligations. Introduce `z hz`.

Conclude with `h z (hWU hz)`. Use `show (I.comap U.ι).ideal V = (J.comap U.ι).ideal V`. Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.ι ⟨U.ι ''ᵁ V.1, hWaff⟩ V e, Scheme.IdealSheafData.comap_ideal_eq_map_appLE J U.ι ⟨U.ι ''ᵁ V.1, hWaff⟩ V e, hIJ]`. Establish `h1 : ∀ V : U.toScheme.affineOpens, (restrictIdeal I U).ideal V ≤ (restrictIdeal J U).ideal V` using `fun V => le_of_eq (key V)`. Establish `h2 : ∀ V : U.toScheme.affineOpens, (restrictIdeal J U).ideal V ≤ (restrictIdeal I U).ideal V` using `fun V => le_of_eq (key V).symm`.

Conclude with `le_antisymm h1 h2`.
-/
theorem restrictIdeal_eq_of_stalkIdeal_eq {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.Opens)
    (h : ∀ y : X, y ∈ U → stalkIdeal I y = stalkIdeal J y) :
    restrictIdeal I U = restrictIdeal J U := by
  have key : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal I U).ideal V = (restrictIdeal J U).ideal V := by
    intro V
    have hWaff : IsAffineOpen (U.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion U.ι
    have hWU : (U.ι ''ᵁ V.1) ≤ U := by
      intro z hz
      have hz' : z ∈ (fun w => U.ι.base w) '' (↑V.1 : Set U.toScheme) := hz
      obtain ⟨v, -, rfl⟩ := hz'
      exact v.2
    have e : V.1 ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V.1) := by
      intro v hv
      have h2 : U.ι.base v ∈ (fun w => U.ι.base w) '' (↑V.1 : Set U.toScheme) := ⟨v, hv, rfl⟩
      exact h2
    have hIJ : I.ideal ⟨U.ι ''ᵁ V.1, hWaff⟩ = J.ideal ⟨U.ι ''ᵁ V.1, hWaff⟩ := by
      refine ideal_eq_of_stalkIdeal_eq I J ⟨U.ι ''ᵁ V.1, hWaff⟩ ?_
      intro z hz
      exact h z (hWU hz)
    show (I.comap U.ι).ideal V = (J.comap U.ι).ideal V
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.ι ⟨U.ι ''ᵁ V.1, hWaff⟩ V e,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE J U.ι ⟨U.ι ''ᵁ V.1, hWaff⟩ V e, hIJ]
  have h1 : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal I U).ideal V ≤ (restrictIdeal J U).ideal V := fun V => le_of_eq (key V)
  have h2 : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal J U).ideal V ≤ (restrictIdeal I U).ideal V := fun V => le_of_eq (key V).symm
  exact le_antisymm h1 h2

end FunctorialResolution.EmbeddedResolution
