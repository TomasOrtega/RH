import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Distinguish the cases in `hi : (N.U i : Set X).Nonempty`. Establish `hij : ((N.U i ⊓ N.U j : X.Opens) : Set X).Nonempty` using `nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen hi ⟨x, hx⟩`. Establish `: Nonempty (N.U i ⊓ N.U j : X.Opens)` using `hij.to_subtype`. Establish `h` using `s.compat i j`. Rewrite `h` using `[hj, map_zero, mul_zero]`.

Apply `map_injective_of_isIntegral X (homOfLE (inf_le_left : N.U i ⊓ N.U j ≤ N.U i))` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h`. Establish `: N.U i = ⊥` using `by ext1`. Simplify using `using Set.not_nonempty_iff_eq_empty.1 hi`.

Establish `: Subsingleton Γ(X, N.U i)` using `by rw [this]; infer_instance`. Conclude with `Subsingleton.elim _ _`.
-/
theorem sec_eq_zero_of_chart {X : Scheme.{0}} [IsIntegral X] (N : LB X) (s : LB.Sec N)
    (j : N.ι) (x : X) (hx : x ∈ N.U j) (hj : s.f j = 0) (i : N.ι) : s.f i = 0 := by
  by_cases hi : (N.U i : Set X).Nonempty
  · have hij : ((N.U i ⊓ N.U j : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen hi ⟨x, hx⟩
    have : Nonempty (N.U i ⊓ N.U j : X.Opens) := hij.to_subtype
    have h := s.compat i j
    rw [hj, map_zero, mul_zero] at h
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : N.U i ⊓ N.U j ≤ N.U i))
    rw [map_zero]
    exact h
  · have : N.U i = ⊥ := by
      ext1
      simpa using Set.not_nonempty_iff_eq_empty.1 hi
    have : Subsingleton Γ(X, N.U i) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _

/- English proof (translation)
Apply `germ_injective_of_isIntegral X x hx` to reduce the goal to its premises. Rewrite using `[map_zero]`. Rewrite `ha` using `[X.mem_basicOpen a x hx]`. Establish `hI : Ideal.span {(X.presheaf.germ U x hx).hom a} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]` and apply the resulting hypothesis.

Establish `h` using `Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI`. Rewrite using `[← Ideal.mem_bot, ← h, Ideal.mem_iInf]`. Introduce `e`. Use `Ideal.mem_map_of_mem (X.presheaf.germ U x hx).hom (hb e)` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow, Ideal.map_span, Set.image_singleton]`. Then use the resulting hypothesis.
-/
theorem eq_zero_of_mem_pow_span {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (x : X) (hx : x ∈ U) (a b : Γ(X, U)) (ha : x ∉ X.basicOpen a)
    (hb : ∀ e : ℕ, b ∈ Ideal.span {a} ^ e) : b = 0 := by
  apply germ_injective_of_isIntegral X x hx
  rw [map_zero]
  rw [X.mem_basicOpen a x hx] at ha
  have hI : Ideal.span {(X.presheaf.germ U x hx).hom a} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  have h := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro e
  have := Ideal.mem_map_of_mem (X.presheaf.germ U x hx).hom (hb e)
  rwa [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at this

/- English proof (translation)
Introduce `H V _ _ _ G _ _ _ _ _ _ N hN s π hπ hs`. Establish `: GeometricallyIntegral G.hom` using `H _ _ _ inferInstance inferInstance`. Establish `: IsIntegral G.left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom`. Establish `: IsLocallyNoetherian G.left` using `LocallyOfFiniteType.isLocallyNoetherian G.hom`. Take `⟨x, hx⟩` from `G.hom.surjective (IsLocalRing.closedPoint V)`.

Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, x ∈ N.U j := by`. Establish `: x ∈ ⨆ i, N.U i` using `by rw [hN.cover]; trivial`. Conclude with `Opens.mem_iSup.1 this`. Use `sec_eq_zero_of_chart N s j x hj ?_` and prove the remaining obligations. Use `eq_zero_of_mem_pow_span (N.U j) x hj _ _ ?_ (hs j)` and prove the remaining obligations.

Introduce `h`. Establish `h2` using `((Scheme.basicOpen_res G.left _ (homOfLE (le_top : N.U j ≤ G.hom ⁻¹ᵁ ⊤)).op).le h).2`. Establish `h3 : x ∈ G.hom ⁻¹ᵁ (Spec (CommRingCat.of V)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv π)`. Rewrite using `[Scheme.preimage_basicOpen]`. Conclude with `h2`.

Rewrite `h3` using `[basicOpen_eq_of_affine]`. Establish `h4 : G.hom x ∈ PrimeSpectrum.basicOpen π` using `h3`. Rewrite `h4` using `[hx]`. Conclude with `h4 ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)`.
-/
theorem sec_eq_zero_of_dvd_pow_uniformiser :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) → Semi.lemmaBSt.{0} := by
  intro H V _ _ _ G _ _ _ _ _ _ N hN s π hπ hs
  have : GeometricallyIntegral G.hom := H _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨x, hx⟩ := G.hom.surjective (IsLocalRing.closedPoint V)
  obtain ⟨j, hj⟩ : ∃ j, x ∈ N.U j := by
    have : x ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact Opens.mem_iSup.1 this
  refine sec_eq_zero_of_chart N s j x hj ?_
  refine eq_zero_of_mem_pow_span (N.U j) x hj _ _ ?_ (hs j)
  intro h
  have h2 := ((Scheme.basicOpen_res G.left _ (homOfLE (le_top :
    N.U j ≤ G.hom ⁻¹ᵁ ⊤)).op).le h).2
  have h3 : x ∈ G.hom ⁻¹ᵁ (Spec (CommRingCat.of V)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv π) := by
    rw [Scheme.preimage_basicOpen]
    exact h2
  rw [basicOpen_eq_of_affine] at h3
  have h4 : G.hom x ∈ PrimeSpectrum.basicOpen π := h3
  rw [hx] at h4
  exact h4 ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)

end GlobalTheory
