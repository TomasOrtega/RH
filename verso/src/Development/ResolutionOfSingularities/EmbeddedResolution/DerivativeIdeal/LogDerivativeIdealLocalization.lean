import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DerivationLocalization

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']

/- English proof (translation)
Introduce `x hx`. Establish `hx' : x ∈ Ideal.span ((algebraMap A B) '' (P : Set A))` using `hx`. Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨p, hp, rfl⟩` from `hy`. Conclude with `hgen p hp`. Consider the case `zero => simp`. Consider the case `add y z hy hz ihy ihz`. Establish `h : D' (y + z) = D' y + D' z` using `by simp`.

Rewrite using `[h]`. Conclude with `Ideal.add_mem _ ihy ihz`. Consider the case `smul a y hy ih`. Establish `hy' : y ∈ P.map (algebraMap A B)` using `hy`. Rewrite using `[smul_eq_mul, D'.leibniz]`.

Simplify using `only [smul_eq_mul]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hy')`.
-/
private theorem derivation_mem_map_of_forall_mem {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra R B]
    (D' : Derivation R B B) {P : Ideal A}
    (hgen : ∀ p ∈ P, D' (algebraMap A B p) ∈ P.map (algebraMap A B)) :
    ∀ x ∈ P.map (algebraMap A B), D' x ∈ P.map (algebraMap A B) := by
  intro x hx
  have hx' : x ∈ Ideal.span ((algebraMap A B) '' (P : Set A)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact hgen p hp
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D' (y + z) = D' y + D' z := by simp
      rw [h]
      exact Ideal.add_mem _ ihy ihz
  | smul a y hy ih =>
      have hy' : y ∈ P.map (algebraMap A B) := hy
      rw [smul_eq_mul, D'.leibniz]
      simp only [smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hy')

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem derivation_smul_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (c : A) (D₀ : Derivation R A A) (x : A) : (c • D₀) x = c * D₀ x := rfl

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[← hP]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem g hg => exact hG g hg`. Consider the case `zero => simp`.

Consider the case `add y z hy hz ihy ihz`. Establish `h : D₀ (y + z) = D₀ y + D₀ z` using `by simp`. Rewrite using `[h, mul_add]`. Conclude with `P.add_mem ihy ihz`. Consider the case `smul a y hy ih`.

Establish `hyP : y ∈ P` using `by rw [← hP]; exact hy`. Rewrite using `[smul_eq_mul, D₀.leibniz]`. Simplify using `only [smul_eq_mul, mul_add]`. Use `P.add_mem ?_ ?_` and prove the remaining obligations. Establish `h1 : c * (a * D₀ y) = a * (c * D₀ y)` using `by ring`.

Rewrite using `[h1]`. Conclude with `P.mul_mem_left a ih`. Conclude with `P.mul_mem_left c (P.mul_mem_right (D₀ a) hyP)`.
-/
private theorem mul_derivation_mem_of_span_eq {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {G : Set A} {P : Ideal A} (hP : Ideal.span G = P) (D₀ : Derivation R A A)
    (c : A) (hG : ∀ g ∈ G, c * D₀ g ∈ P) : ∀ x ∈ P, c * D₀ x ∈ P := by
  intro x hx
  rw [← hP] at hx
  induction hx using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D₀ (y + z) = D₀ y + D₀ z := by simp
      rw [h, mul_add]
      exact P.add_mem ihy ihz
  | smul a y hy ih =>
      have hyP : y ∈ P := by rw [← hP]; exact hy
      rw [smul_eq_mul, D₀.leibniz]
      simp only [smul_eq_mul, mul_add]
      refine P.add_mem ?_ ?_
      · have h1 : c * (a * D₀ y) = a * (c * D₀ y) := by ring
        rw [h1]
        exact P.mul_mem_left a ih
      · exact P.mul_mem_left c (P.mul_mem_right (D₀ a) hyP)

/- English proof (translation)
Take `⟨u, hu⟩` from `(IsLocalization.mem_map_algebraMap_iff (M := M) (S := B)).mp hx`. Conclude with `⟨u.1, u.2, u.1.2, hu⟩`.
-/
private theorem exists_mem_mul_algebraMap_eq_of_mem_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (J : Ideal A) {x : B}
    (hx : x ∈ J.map (algebraMap A B)) :
    ∃ (y : A) (t : M), y ∈ J ∧ x * algebraMap A B (t : A) = algebraMap A B y := by
  obtain ⟨u, hu⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := B)).mp hx
  exact ⟨u.1, u.2, u.1.2, hu⟩

/- English proof (translation)
Take `⟨p, t, hp, h⟩` from `exists_mem_mul_algebraMap_eq_of_mem_map M P hy`. Establish `h2 : algebraMap A B (y * (t : A)) = algebraMap A B p`. Rewrite using `[map_mul]`. Take the linear combination `h`. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists (M := M) (S := B)).mp h2`.

Use `⟨c * t, ?_⟩` and prove the remaining obligations. Establish `heq : ((c * t : M) : A) * y = (c : A) * p`. Use `push_cast`. Take the linear combination `hc`. Rewrite using `[heq]`.

Conclude with `P.mul_mem_left _ hp`.
-/
private theorem exists_mul_mem_of_algebraMap_mem_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (P : Ideal A) {y : A}
    (hy : algebraMap A B y ∈ P.map (algebraMap A B)) :
    ∃ m : M, (m : A) * y ∈ P := by
  obtain ⟨p, t, hp, h⟩ := exists_mem_mul_algebraMap_eq_of_mem_map M P hy
  have h2 : algebraMap A B (y * (t : A)) = algebraMap A B p := by
    rw [map_mul]; linear_combination h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := B)).mp h2
  refine ⟨c * t, ?_⟩
  have heq : ((c * t : M) : A) * y = (c : A) * p := by
    push_cast
    linear_combination hc
  rw [heq]
  exact P.mul_mem_left _ hp

/- English proof (translation)
Establish `hD'` using `(mem_tangentDerivations k P D).mp hD`. Rewrite using `[mem_tangentDerivations]`. Use `derivation_mem_map_of_forall_mem (D.mapToLocalization (S' := S') M) ?_` and prove the remaining obligations. Introduce `p hp`. Rewrite using `[Derivation.mapToLocalization_algebraMap]`.

Conclude with `Ideal.mem_map_of_mem _ (hD' p hp)`.
-/
theorem mapToLocalization_mem_tangentDerivations (M : Submonoid S) [IsLocalization M S']
    {P : Ideal S} {D : Derivation k S S} (hD : D ∈ tangentDerivations k P) :
    (D.mapToLocalization (S' := S') M) ∈
      tangentDerivations k (P.map (algebraMap S S')) := by
  have hD' := (mem_tangentDerivations k P D).mp hD
  rw [mem_tangentDerivations]
  refine derivation_mem_map_of_forall_mem (D.mapToLocalization (S' := S') M) ?_
  intro p hp
  rw [Derivation.mapToLocalization_algebraMap]
  exact Ideal.mem_map_of_mem _ (hD' p hp)

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Rewrite using `[Ideal.mem_comap]`. Conclude with `le_logDerivIdeal k _ _ (Ideal.mem_map_of_mem _ hx)`.

Introduce `D hD x hx`. Rewrite using `[Ideal.mem_comap]`. Establish `h : algebraMap S S' (D x) = (D.mapToLocalization (S'` using `S') M) (algebraMap S S' x) := by`. Rewrite using `[Derivation.mapToLocalization_algebraMap]`. Rewrite using `[h]`.

Conclude with `derivation_apply_mem_logDerivIdeal k _ _ _ (mapToLocalization_mem_tangentDerivations (S' := S') k M hD) (Ideal.mem_map_of_mem _ hx)`.
-/
theorem map_logDerivIdeal_le (M : Submonoid S) [IsLocalization M S'] (P J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') ≤
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_logDerivIdeal k _ _ (Ideal.mem_map_of_mem _ hx)
  · intro D hD x hx
    rw [Ideal.mem_comap]
    have h : algebraMap S S' (D x) =
        (D.mapToLocalization (S' := S') M) (algebraMap S S' x) := by
      rw [Derivation.mapToLocalization_algebraMap]
    rw [h]
    exact derivation_apply_mem_logDerivIdeal k _ _ _
      (mapToLocalization_mem_tangentDerivations (S' := S') k M hD)
      (Ideal.mem_map_of_mem _ hx)

/- English proof (translation)
Establish `hDt` using `(mem_tangentDerivations k (P.map (algebraMap S S')) D).mp hD`. Take `⟨m₀, D₀, hD₀⟩` from `Derivation.exists_derivation_mul_eq_of_isLocalization (S' := S') M D`. Take `⟨G, hG⟩` from `hP`. Establish `key : ∀ g : S, ∃ n : M, g ∈ G → (n : S) * D₀ g ∈ P`. Introduce `g`.

Distinguish the cases in `hg : g ∈ G`. Establish `hgP : g ∈ P`. Rewrite using `[← hG]`. Conclude with `Ideal.subset_span (Finset.mem_coe.mpr hg)`. Establish `h1 : algebraMap S S' g ∈ P.map (algebraMap S S')` using `Ideal.mem_map_of_mem _ hgP`.

Establish `h2 : D (algebraMap S S' g) ∈ P.map (algebraMap S S')` using `hDt _ h1`. Establish `h3 : algebraMap S S' (D₀ g) ∈ P.map (algebraMap S S')`. Rewrite using `[← hD₀ g]`. Conclude with `Ideal.mul_mem_left _ _ h2`. Take `⟨n, hn⟩` from `exists_mul_mem_of_algebraMap_mem_map M P h3`.

Conclude with `⟨n, fun _ => hn⟩`. Conclude with `⟨1, fun h => absurd h hg⟩`. Use `choose f hf using key`. Choose the witnesses or unpack the hypotheses as in `⟨c, hcM, hcP⟩ : ∃ c : S, c ∈ M ∧ ∀ g ∈ G, c * D₀ g ∈ P := by`. Use `⟨Finset.prod G (fun g => ((f g : S))), Submonoid.prod_mem M (fun g _ => (f g).2), ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Take `⟨r, hr⟩` from `Finset.dvd_prod_of_mem (fun g => ((f g : S))) hg`. Establish `h4 : ((f g : S)) * r * D₀ g = r * (((f g : S)) * D₀ g)` using `by ring`. Rewrite using `[hr, h4]`. Conclude with `P.mul_mem_left _ (hf g hg)`.

Use `⟨⟨c * (m₀ : S), M.mul_mem hcM m₀.2⟩, c • D₀, ?_, ?_⟩` and prove the remaining obligations. Establish `hgen : ∀ g ∈ (↑G : Set S), c * D₀ g ∈ P` using `fun g hg => hcP g (Finset.mem_coe.mp hg)`. Rewrite using `[mem_tangentDerivations]`. Introduce `x hx`. Establish `h` using `mul_derivation_mem_of_span_eq hG D₀ c hgen x hx`.

Rewrite using `[derivation_smul_apply]`. Conclude with `h`. Introduce `s show algebraMap S S' (c * (m₀ : S)) * D (algebraMap S S' s) = algebraMap S S' ((c • D₀) s)`. Rewrite using `[derivation_smul_apply, map_mul, map_mul, mul_assoc, hD₀ s]`.
-/
theorem exists_mem_tangentDerivations_mul_eq (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (D : Derivation k S' S')
    (hD : D ∈ tangentDerivations k (P.map (algebraMap S S'))) :
    ∃ (m : M) (D₁ : Derivation k S S), D₁ ∈ tangentDerivations k P ∧
      ∀ s : S, algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₁ s) := by
  have hDt := (mem_tangentDerivations k (P.map (algebraMap S S')) D).mp hD
  obtain ⟨m₀, D₀, hD₀⟩ :=
    Derivation.exists_derivation_mul_eq_of_isLocalization (S' := S') M D
  obtain ⟨G, hG⟩ := hP
  have key : ∀ g : S, ∃ n : M, g ∈ G → (n : S) * D₀ g ∈ P := by
    intro g
    by_cases hg : g ∈ G
    · have hgP : g ∈ P := by
        rw [← hG]
        exact Ideal.subset_span (Finset.mem_coe.mpr hg)
      have h1 : algebraMap S S' g ∈ P.map (algebraMap S S') := Ideal.mem_map_of_mem _ hgP
      have h2 : D (algebraMap S S' g) ∈ P.map (algebraMap S S') := hDt _ h1
      have h3 : algebraMap S S' (D₀ g) ∈ P.map (algebraMap S S') := by
        rw [← hD₀ g]
        exact Ideal.mul_mem_left _ _ h2
      obtain ⟨n, hn⟩ := exists_mul_mem_of_algebraMap_mem_map M P h3
      exact ⟨n, fun _ => hn⟩
    · exact ⟨1, fun h => absurd h hg⟩
  choose f hf using key
  obtain ⟨c, hcM, hcP⟩ : ∃ c : S, c ∈ M ∧ ∀ g ∈ G, c * D₀ g ∈ P := by
    refine ⟨Finset.prod G (fun g => ((f g : S))),
      Submonoid.prod_mem M (fun g _ => (f g).2), ?_⟩
    intro g hg
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun g => ((f g : S))) hg
    have h4 : ((f g : S)) * r * D₀ g = r * (((f g : S)) * D₀ g) := by ring
    rw [hr, h4]
    exact P.mul_mem_left _ (hf g hg)
  refine ⟨⟨c * (m₀ : S), M.mul_mem hcM m₀.2⟩, c • D₀, ?_, ?_⟩
  · have hgen : ∀ g ∈ (↑G : Set S), c * D₀ g ∈ P := fun g hg => hcP g (Finset.mem_coe.mp hg)
    rw [mem_tangentDerivations]
    intro x hx
    have h := mul_derivation_mem_of_span_eq hG D₀ c hgen x hx
    rw [derivation_smul_apply]
    exact h
  · intro s
    show algebraMap S S' (c * (m₀ : S)) * D (algebraMap S S' s)
        = algebraMap S S' ((c • D₀) s)
    rw [derivation_smul_apply, map_mul, map_mul, mul_assoc, hD₀ s]

/- English proof (translation)
Rewrite using `[logDerivIdeal_le_iff]`. Use `⟨Ideal.map_mono (le_logDerivIdeal k P J), ?_⟩` and prove the remaining obligations. Introduce `D hD x hx`. Take `⟨m, D₁, hD₁, hm⟩` from `exists_mem_tangentDerivations_mul_eq k M hP D hD`. Take `⟨y, t, hy, hxt⟩` from `exists_mem_mul_algebraMap_eq_of_mem_map M J hx`.

Establish `hxL : x ∈ (logDerivIdeal k P J).map (algebraMap S S')` using `Ideal.map_mono (le_logDerivIdeal k P J) hx`. Establish `h1 : D (x * algebraMap S S' (t : S)) = D (algebraMap S S' y)` using `by rw [hxt]`. Rewrite `h1` using `[D.leibniz]`. Simplify using `only [smul_eq_mul] at h1`. Establish `e1` using `hm y`.

Establish `e2` using `hm (t : S)`. Establish `hmul : algebraMap S S' ((m : S) * (t : S)) * D x = algebraMap S S' (D₁ y) - x * algebraMap S S' (D₁ (t : S))`. Rewrite using `[map_mul]`. Take the linear combination `algebraMap S S' (m : S) * h1 + e1 - x * e2`. Establish `hmem : algebraMap S S' ((m : S) * (t : S)) * D x ∈ (logDerivIdeal k P J).map (algebraMap S S')`.

Rewrite using `[hmul]`. Use `sub_mem ?_ ?_` and prove the remaining obligations. Conclude with `Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivIdeal k P J D₁ hD₁ hy)`. Conclude with `Ideal.mul_mem_right _ _ hxL`. Establish `hu : IsUnit (algebraMap S S' ((m : S) * (t : S)))`.

Rewrite using `[map_mul]`. Conclude with `(IsLocalization.map_units (M := M) (S := S') m).mul (IsLocalization.map_units (M := M) (S := S') t)`. Take `⟨u, hu'⟩` from `hu`. Establish `hrw : D x = (↑u⁻¹ : S') * (algebraMap S S' ((m : S) * (t : S)) * D x)`. Rewrite using `[← hu', ← mul_assoc, Units.inv_mul, one_mul]`.

Rewrite using `[hrw]`. Conclude with `Ideal.mul_mem_left _ _ hmem`.
-/
theorem logDerivIdeal_map_le_map_logDerivIdeal (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) ≤
      (logDerivIdeal k P J).map (algebraMap S S') := by
  rw [logDerivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_logDerivIdeal k P J), ?_⟩
  intro D hD x hx
  obtain ⟨m, D₁, hD₁, hm⟩ := exists_mem_tangentDerivations_mul_eq k M hP D hD
  obtain ⟨y, t, hy, hxt⟩ := exists_mem_mul_algebraMap_eq_of_mem_map M J hx
  have hxL : x ∈ (logDerivIdeal k P J).map (algebraMap S S') :=
    Ideal.map_mono (le_logDerivIdeal k P J) hx
  have h1 : D (x * algebraMap S S' (t : S)) = D (algebraMap S S' y) := by rw [hxt]
  rw [D.leibniz] at h1
  simp only [smul_eq_mul] at h1
  have e1 := hm y
  have e2 := hm (t : S)
  have hmul : algebraMap S S' ((m : S) * (t : S)) * D x
      = algebraMap S S' (D₁ y) - x * algebraMap S S' (D₁ (t : S)) := by
    rw [map_mul]
    linear_combination algebraMap S S' (m : S) * h1 + e1 - x * e2
  have hmem : algebraMap S S' ((m : S) * (t : S)) * D x ∈
      (logDerivIdeal k P J).map (algebraMap S S') := by
    rw [hmul]
    refine sub_mem ?_ ?_
    · exact Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivIdeal k P J D₁ hD₁ hy)
    · exact Ideal.mul_mem_right _ _ hxL
  have hu : IsUnit (algebraMap S S' ((m : S) * (t : S))) := by
    rw [map_mul]
    exact (IsLocalization.map_units (M := M) (S := S') m).mul
      (IsLocalization.map_units (M := M) (S := S') t)
  obtain ⟨u, hu'⟩ := hu
  have hrw : D x = (↑u⁻¹ : S') * (algebraMap S S' ((m : S) * (t : S)) * D x) := by
    rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
  rw [hrw]
  exact Ideal.mul_mem_left _ _ hmem

/- English proof (translation)
The claim follows from `le_antisymm (map_logDerivIdeal_le k M P J) (logDerivIdeal_map_le_map_logDerivIdeal k M hP J)`.
-/
theorem logDerivIdeal_map (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  le_antisymm (map_logDerivIdeal_le k M P J) (logDerivIdeal_map_le_map_logDerivIdeal k M hP J)

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]`. Consider the case `succ r ih`. Rewrite using `[logDerivIdealIterate_succ, logDerivIdealIterate_succ, logDerivIdeal_map k M hP, ih]`.
-/
theorem logDerivIdealIterate_map (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ, logDerivIdeal_map k M hP, ih]

/- English proof (translation)
The claim follows from `logDerivIdeal_map k (Submonoid.powers g) hP J`.
-/
theorem logDerivIdeal_map_away (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  logDerivIdeal_map k (Submonoid.powers g) hP J

/- English proof (translation)
The claim follows from `logDerivIdealIterate_map k (Submonoid.powers g) hP r J`.
-/
theorem logDerivIdealIterate_map_away (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) :=
  logDerivIdealIterate_map k (Submonoid.powers g) hP r J

end FunctorialResolution.EmbeddedResolution
