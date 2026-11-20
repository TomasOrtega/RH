import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot

open UpperTheory.Et

namespace UpperTheory.IntegralSubring

variable {A D B : Type} [CommRing A] [CommRing D] [Algebra A D] [CommRing B]

private def sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) : Subalgebra A D :=
  { φ.range with
    algebraMap_mem' := fun r => ⟨α r, by rw [← h]; rfl⟩ }

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) (x : D) :
    x ∈ sub φ α h ↔ ∃ y, φ y = x := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) :
    ((sub φ α h : Subalgebra A D) : Set D) = Set.range φ := rfl

/- English proof (translation)
Introduce and unpack `x ⟨y, rfl⟩`. Establish `hle : Subring.closure (Set.range α ∪ {t}) ≤ (Algebra.adjoin A {φ t}).toSubring.comap φ`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `z (⟨r, rfl⟩ | hz)`. Establish `: φ (α r) = algebraMap A D r` using `by rw [← h]; rfl`.

Express the relevant statement in the definitionally equal form `φ (α r) ∈ Algebra.adjoin A {φ t}`. Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ r`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality.

Conclude with `Algebra.subset_adjoin (Set.mem_singleton _)`. Set `f : Subring.closure (Set.range α ∪ {t}) →+* Algebra.adjoin A {φ t}` to `(φ.comp (Subring.closure (Set.range α ∪ {t})).subtype).codRestrict (Algebra.adjoin A {φ t}) (fun r => hle r.2)`. Conclude with `IsIntegral.map_of_comp_eq f φ (by ext r; rfl) (hint y)`.
-/
private theorem int_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) (t : B)
    (hint : ∀ x : B, IsIntegral (Subring.closure (Set.range α ∪ {t})) x) :
    ∀ x ∈ sub φ α h, IsIntegral (Algebra.adjoin A {φ t}) x := by
  rintro x ⟨y, rfl⟩
  have hle : Subring.closure (Set.range α ∪ {t}) ≤
      (Algebra.adjoin A {φ t}).toSubring.comap φ := by
    rw [Subring.closure_le]
    rintro z (⟨r, rfl⟩ | hz)
    · have : φ (α r) = algebraMap A D r := by rw [← h]; rfl
      change φ (α r) ∈ Algebra.adjoin A {φ t}
      rw [this]
      exact Subalgebra.algebraMap_mem _ r
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Algebra.subset_adjoin (Set.mem_singleton _)
  let f : Subring.closure (Set.range α ∪ {t}) →+* Algebra.adjoin A {φ t} :=
    (φ.comp (Subring.closure (Set.range α ∪ {t})).subtype).codRestrict
      (Algebra.adjoin A {φ t}) (fun r => hle r.2)
  exact IsIntegral.map_of_comp_eq f φ (by ext r; rfl) (hint y)

/- English proof (translation)
Introduce `p hp hd`. Set `g : B →+* sub φ α h` to `φ.codRestrict (sub φ α h) (fun y => (mem_sub φ α h _).2 ⟨y, rfl⟩)`. Establish `hg : Function.Bijective g`. Use `⟨fun a b hab => hφ (congrArg Subtype.val hab), ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`.

Take `⟨y, rfl⟩` from `(mem_sub φ α h x).1 hx`. Conclude with `⟨y, rfl⟩`. Set `e` to `RingEquiv.ofBijective g hg`. Take `⟨a, ha⟩` from `hr (p.map (e.symm : sub φ α h →+* B)) (hp.map _) (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])`. Use `⟨e a, ?_⟩` and prove the remaining obligations.

Establish `hpm : (p.map (e.symm : sub φ α h →+* B)).map (e : B →+* sub φ α h) = p`. Rewrite using `[Polynomial.map_map]`. Use `Polynomial.map_id` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[← hpm, Polynomial.eval_map]`. Use `Polynomial.eval₂_hom (e : B →+* sub φ α h) a (p := p.map (e.symm : sub φ α h →+* B))` as an intermediate fact. Rewrite `this` using `[ha, map_zero]`. Conclude with `this`.
-/
private theorem roots_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D)
    (hφ : Function.Injective φ)
    (hr : ∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) :
    Roots (sub φ α h) := by
  intro p hp hd
  let g : B →+* sub φ α h := φ.codRestrict (sub φ α h) (fun y => (mem_sub φ α h _).2 ⟨y, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => hφ (congrArg Subtype.val hab), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (mem_sub φ α h x).1 hx
    exact ⟨y, rfl⟩
  let e := RingEquiv.ofBijective g hg
  obtain ⟨a, ha⟩ := hr (p.map (e.symm : sub φ α h →+* B)) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hpm : (p.map (e.symm : sub φ α h →+* B)).map (e : B →+* sub φ α h) = p := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext x
    simp
  rw [← hpm, Polynomial.eval_map]
  have := Polynomial.eval₂_hom (e : B →+* sub φ α h) a (p := p.map (e.symm : sub φ α h →+* B))
  rw [ha, map_zero] at this
  exact this

end UpperTheory.IntegralSubring

open UpperTheory.IntegralSubring in
/- English proof (translation)
Introduce `A D B C _ _ _ _ _ φ ψ α β hα hβ hφ hψ t s hts hlB hlC hiB hiC hrB hrC`. Use `⟨⟨sub φ α hα, sub ψ β hβ, φ t, ψ s, hts, (mem_sub φ α hα _).2 ⟨t, rfl⟩, (mem_sub ψ β hβ _).2 ⟨s, rfl⟩, ?_, ?_⟩, ⟨int_sub φ α hα t hiB, int_sub ψ β hβ s hiC⟩, roots_sub φ α hα hφ hrB, roots_sub ψ β hβ hψ hrC, coe_sub φ α hα, coe_sub ψ β hβ⟩` and prove the remaining obligations. Introduce `x`. Take `⟨k, y, hy⟩` from `hlB x`. Conclude with `⟨k, (mem_sub φ α hα _).2 ⟨y, hy.symm⟩⟩`.

Introduce `x`. Take `⟨k, y, hy⟩` from `hlC x`. Conclude with `⟨k, (mem_sub ψ β hβ _).2 ⟨y, hy.symm⟩⟩`.
-/
theorem UpperTheory.isIntegral_of_localization_cover_unit_product :
    ∀ {A D B C : Type} [CommRing A] [CommRing D] [Algebra A D] [CommRing B] [CommRing C]
        (φ : B →+* D) (ψ : C →+* D) (α : A →+* B) (β : A →+* C),
        φ.comp α = algebraMap A D → ψ.comp β = algebraMap A D → Function.Injective φ → Function.Injective ψ →
        ∀ (t : B) (s : C), φ t * ψ s = 1 → (∀ x : D, ∃ (k : ℕ) (y : B), φ t ^ k * x = φ y) →
        (∀ x : D, ∃ (k : ℕ) (y : C), ψ s ^ k * x = ψ y) →
        (∀ x : B, IsIntegral (Subring.closure (Set.range α ∪ {t})) x) →
        (∀ x : C, IsIntegral (Subring.closure (Set.range β ∪ {s})) x) →
        (∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) →
        (∀ p : Polynomial C, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) →
        ∃ T : TC A D, T.Int ∧ Roots T.B ∧ Roots T.C ∧ (T.B : Set D) = Set.range φ ∧ (T.C : Set D) = Set.range ψ := by
  intro A D B C _ _ _ _ _ φ ψ α β hα hβ hφ hψ t s hts hlB hlC hiB hiC hrB hrC
  refine ⟨⟨sub φ α hα, sub ψ β hβ, φ t, ψ s, hts, (mem_sub φ α hα _).2 ⟨t, rfl⟩,
    (mem_sub ψ β hβ _).2 ⟨s, rfl⟩, ?_, ?_⟩, ⟨int_sub φ α hα t hiB, int_sub ψ β hβ s hiC⟩,
    roots_sub φ α hα hφ hrB, roots_sub ψ β hβ hψ hrC, coe_sub φ α hα, coe_sub ψ β hβ⟩
  · intro x
    obtain ⟨k, y, hy⟩ := hlB x
    exact ⟨k, (mem_sub φ α hα _).2 ⟨y, hy.symm⟩⟩
  · intro x
    obtain ⟨k, y, hy⟩ := hlC x
    exact ⟨k, (mem_sub ψ β hβ _).2 ⟨y, hy.symm⟩⟩
