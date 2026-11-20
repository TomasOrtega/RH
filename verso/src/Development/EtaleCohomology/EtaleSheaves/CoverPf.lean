import Development.EtaleCohomology.EtaleSheaves.AcycQAPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.CoverPf

def EmptyVan : Prop := A1 → ∀ (q : ℕ) [NeZero q] (i n : ℤ) (S : Type) [CommRing S], Subsingleton S →
  ∀ x : Ht q (sp S) (n + 1) i, x = 0

/- English proof (translation)
Establish `: spMap (g.comp f) = spMap g ≫ spMap f` using `by simp [spMap]`. Rewrite using `[this, pull_comp]`.
-/
theorem pull_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (q : ℕ) (m i : ℤ)
    (x : Ht q (sp A) m i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  have : spMap (g.comp f) = spMap g ≫ spMap f := by simp [spMap]
  rw [this, pull_comp]

/- English proof (translation)
Establish `e : φ = (IsLocalization.Away.lift f (S` using `Localization.Away f) hu).comp (algebraMap S (Localization.Away f)) := (IsLocalization.Away.lift_comp f (S := Localization.Away f) hu).symm`. Rewrite using `[e, pull_comp', hx, map_zero]`.
-/
theorem dies_of_factor {S : Type} [CommRing S] {q : ℕ} {m i : ℤ} (x : Ht q (sp S) m i) (f : S)
    (hx : pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0)
    {T : Type} [CommRing T] (φ : S →+* T) (hu : IsUnit (φ f)) : pull _ (spMap φ) _ _ x = 0 := by
  have e : φ = (IsLocalization.Away.lift f (S := Localization.Away f) hu).comp (algebraMap S (Localization.Away f)) :=
    (IsLocalization.Away.lift_comp f (S := Localization.Away f) hu).symm
  rw [e, pull_comp', hx, map_zero]

/- English proof (translation)
Use `set T := Localization.Away (f + g)`. Use `set φ := algebraMap S T`. Establish `hT : QA T` using `(hQ S hS).2.1 (f + g)`. Establish `hqT : IsUnit (q : T)` using `by simpa using hq.map φ`. Establish `hspan : Ideal.span {φ f, φ g} = ⊤`.

Rewrite using `[Ideal.eq_top_iff_one]`. Take `⟨u, hu⟩` from `IsLocalization.Away.algebraMap_isUnit (S := T) (f + g)`. Establish `hmem : φ (f + g) ∈ Ideal.span {φ f, φ g}`. Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))`.

Establish `: (1 : T) = ((u⁻¹ : Tˣ) : T) * φ (f + g)`. Express the relevant statement in the definitionally equal form `(1 : T) = ((u⁻¹ : Tˣ) : T) * algebraMap S T (f + g)`. Rewrite using `[← hu]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_left _ _ hmem`. Establish `key` using `hM h1 (ZMod q) (tw q i) T (φ f) (φ g) hspan n (hk T hT hqT (φ f) (φ g) hspan) (pull _ (spMap φ) _ _ x)`. Apply `key` to reduce the goal to its premises. Rewrite using `[← pull_comp']`. Conclude with `dies_of_factor x f hf _ (by`.

Simplify using `using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ f)) (φ f))`. Rewrite using `[← pull_comp']`. Conclude with `dies_of_factor x g hg _ (by`. Simplify using `using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ g)) (φ g))`.
-/
theorem dies_add (hQ : QAClosed) (hM : MV) (h1 : A1) {q : ℕ} {i n : ℤ} (hk : MVHyp q i n)
    {S : Type} [CommRing S] (hS : QA S) (hq : IsUnit (q : S)) (x : Ht q (sp S) (n + 1) i) (f g : S)
    (hf : pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0)
    (hg : pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0) :
    pull _ (spMap (algebraMap S (Localization.Away (f + g)))) _ _ x = 0 := by
  set T := Localization.Away (f + g)
  set φ := algebraMap S T
  have hT : QA T := (hQ S hS).2.1 (f + g)
  have hqT : IsUnit (q : T) := by simpa using hq.map φ
  have hspan : Ideal.span {φ f, φ g} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := T) (f + g)
    have hmem : φ (f + g) ∈ Ideal.span {φ f, φ g} := by
      rw [map_add]
      exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    have : (1 : T) = ((u⁻¹ : Tˣ) : T) * φ (f + g) := by
      change (1 : T) = ((u⁻¹ : Tˣ) : T) * algebraMap S T (f + g)
      rw [← hu]; simp
    rw [this]; exact Ideal.mul_mem_left _ _ hmem
  have key := hM h1 (ZMod q) (tw q i) T (φ f) (φ g) hspan n (hk T hT hqT (φ f) (φ g) hspan)
    (pull _ (spMap φ) _ _ x)
  apply key
  · rw [← pull_comp']
    exact dies_of_factor x f hf _ (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ f)) (φ f))
  · rw [← pull_comp']
    exact dies_of_factor x g hg _ (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ g)) (φ g))

/- English proof (translation)
Introduce `hQ hM h1 q _ i n hk S _ hS hq x hloc`. Set `I : Set S` to `{g | pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0}`. Establish `hmul : ∀ a g, g ∈ I → a * g ∈ I`. Introduce `a g hg`. Use `dies_of_factor x g hg _ ?_` and prove the remaining obligations.

Conclude with `isUnit_of_mul_isUnit_right (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a * g)) (a * g) |>.map (RingHom.id _) |> fun h => by simpa [map_mul] using h)`. Establish `hadd : ∀ f g, f ∈ I → g ∈ I → f + g ∈ I` using `fun f g hf hg => dies_add hQ hM h1 hk hS hq x f g hf hg`. Establish `hspan : Ideal.span I = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM', hle⟩` from `Ideal.exists_le_maximal _ hne`.

Take `⟨f, hfM, hf⟩` from `hloc ⟨M, hM'.isPrime⟩`. Conclude with `hfM (hle (Ideal.subset_span hf))`. Establish `hP : ∀ y ∈ Ideal.span I, y ∈ I ∨ y = 0`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy => exact Or.inl hy`. Consider the case `zero => exact Or.inr rfl`. Consider the case `add a b _ _ ha hb`. Apply the tactic sequence `rcases ha with ha | ha <;> rcases hb with hb | hb`. Conclude with `Or.inl (hadd a b ha hb)`.

Substitute `hb` using the available equality. Simplify using `using Or.inl ha`. Substitute `ha` using the available equality. Simplify using `using Or.inl hb`. Substitute `ha` using the available equality.

Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Consider the case `smul a b _ hb`. Break down `hb with hb | hb` into its components or cases. Conclude with `Or.inl (hmul a b hb)`.

Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Break down `hP 1 (by rw [hspan]; trivial) with h | h` into its components or cases. Use `dies_of_factor x 1 h (RingHom.id S) isUnit_one` as an intermediate fact. Establish `e : spMap (RingHom.id S) = 𝟙 _` using `by simp [spMap]`.

Rewrite `this` using `[e, pull_id]`. Then use the resulting hypothesis. Establish `: Subsingleton S` using `subsingleton_of_zero_eq_one h.symm`. Conclude with `hE h1 q i n S inferInstance x`.
-/
theorem Cover_of (hE : EmptyVan) : LateralTheory.E.AcycQAPf.Cover := by
  intro hQ hM h1 q _ i n hk S _ hS hq x hloc
  let I : Set S := {g | pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0}
  have hmul : ∀ a g, g ∈ I → a * g ∈ I := by
    intro a g hg
    refine dies_of_factor x g hg _ ?_
    exact isUnit_of_mul_isUnit_right (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a * g)) (a * g)
      |>.map (RingHom.id _) |> fun h => by simpa [map_mul] using h)
  have hadd : ∀ f g, f ∈ I → g ∈ I → f + g ∈ I := fun f g hf hg => dies_add hQ hM h1 hk hS hq x f g hf hg
  have hspan : Ideal.span I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM', hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hfM, hf⟩ := hloc ⟨M, hM'.isPrime⟩
    exact hfM (hle (Ideal.subset_span hf))
  have hP : ∀ y ∈ Ideal.span I, y ∈ I ∨ y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Or.inl hy
    | zero => exact Or.inr rfl
    | add a b _ _ ha hb =>
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (hadd a b ha hb)
      · subst hb; simpa using Or.inl ha
      · subst ha; simpa using Or.inl hb
      · subst ha; subst hb; simp
    | smul a b _ hb =>
      rcases hb with hb | hb
      · exact Or.inl (hmul a b hb)
      · subst hb; simp
  rcases hP 1 (by rw [hspan]; trivial) with h | h
  · have := dies_of_factor x 1 h (RingHom.id S) isUnit_one
    have e : spMap (RingHom.id S) = 𝟙 _ := by simp [spMap]
    rwa [e, pull_id] at this
  · have : Subsingleton S := subsingleton_of_zero_eq_one h.symm
    exact hE h1 q i n S inferInstance x

end LateralTheory.E.CoverPf
