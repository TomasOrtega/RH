import Development.EtaleCohomology.EtaleSheaves.SysFMPf

namespace LateralTheory.E.SysFMPfAlg

open LateralTheory.E.BuildCut

/- English proof (translation)
Establish `h1 : (1 : W) ∈ F`. Break down `hu 0 IsIdempotentElem.zero with h | h` into its components or cases. Conclude with `absurd h h0`. Simplify using `using h`. Set `I : Ideal W` to `{ carrier := {a | ∃ f ∈ F, a * f = 0} add_mem' := by`.

Introduce and unpack `a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩`. Conclude with `⟨f * g, hm f hf g hg, by linear_combination g * ha + f * hb⟩`. Use the proof step `zero_mem' := ⟨1, h1, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨f, hf, ha⟩`.

Conclude with `⟨f, hf, by simp only [smul_eq_mul]; linear_combination c * ha⟩ }`. Establish `key : ∀ e, IsIdempotentElem e → (e ∈ I ↔ e ∉ F)`. Introduce `e he`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, hef⟩ heF`.

Conclude with `h0 (hef ▸ hm e heF f hf)`. Introduce `heF`. Break down `hu e he with h | h` into its components or cases. Conclude with `absurd h heF`. Conclude with `⟨1 - e, h, by rw [mul_sub, mul_one, he.eq, sub_self]⟩`.

Establish `hI : I.IsPrime`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.eq_top_iff_one]`. Introduce and unpack `⟨f, hf, h⟩`. Rewrite `h` using `[one_mul]`.

Conclude with `h0 (h ▸ hf)`. Introduce `a b hab`. Take `⟨e, u, he, hu', rfl⟩` from `hW.2 a`. Take `⟨e', u', he', hu'', rfl⟩` from `hW.2 b`. Assume the negation of the conclusion as `hn`.

Use `push Not at hn`. Establish `ha : e ∈ F`. Assume the negation of the conclusion as `h`. Conclude with `hn.1 ⟨1 - e, (hu e he).resolve_left h, by`. Rewrite using `[mul_assoc, mul_comm u, ← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]⟩`.

Establish `hb : e' ∈ F`. Assume the negation of the conclusion as `h`. Conclude with `hn.2 ⟨1 - e', (hu e' he').resolve_left h, by`. Rewrite using `[mul_assoc, mul_comm u', ← mul_assoc, mul_sub, mul_one, he'.eq, sub_self, zero_mul]⟩`. Take `⟨f, hf, h⟩` from `hab`.

Establish `hz : e * e' * f = 0`. Take `⟨v, hv⟩` from `hu'.exists_left_inv`. Take `⟨v', hv'⟩` from `hu''.exists_left_inv`. Take the linear combination `(v * v') * h - (e * e' * f) * hv - (e * e' * f * v * u) * hv'`. Conclude with `h0 (hz ▸ hm _ (hm e ha e' hb) f hf)`.

Use `⟨⟨I, hI⟩, fun e he => ?_⟩` and prove the remaining obligations. Rewrite using `[show (⟨I, hI⟩ : PrimeSpectrum W).asIdeal = I from rfl, key e he, not_not]`.
-/
theorem prime_of_filter {W : Type} [CommRing W] (hW : ProdACF W) (F : Set W) (hF : ∀ e ∈ F, IsIdempotentElem e)
    (h0 : (0 : W) ∉ F) (hu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F) (hm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F) :
    ∃ q : PrimeSpectrum W, ∀ e, IsIdempotentElem e → (e ∉ q.asIdeal ↔ e ∈ F) := by
  have h1 : (1 : W) ∈ F := by
    rcases hu 0 IsIdempotentElem.zero with h | h
    · exact absurd h h0
    · simpa using h
  let I : Ideal W :=
    { carrier := {a | ∃ f ∈ F, a * f = 0}
      add_mem' := by
        rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
        exact ⟨f * g, hm f hf g hg, by linear_combination g * ha + f * hb⟩
      zero_mem' := ⟨1, h1, by simp⟩
      smul_mem' := by
        rintro c a ⟨f, hf, ha⟩
        exact ⟨f, hf, by simp only [smul_eq_mul]; linear_combination c * ha⟩ }
  have key : ∀ e, IsIdempotentElem e → (e ∈ I ↔ e ∉ F) := by
    intro e he
    constructor
    · rintro ⟨f, hf, hef⟩ heF
      exact h0 (hef ▸ hm e heF f hf)
    · intro heF
      rcases hu e he with h | h
      · exact absurd h heF
      · exact ⟨1 - e, h, by rw [mul_sub, mul_one, he.eq, sub_self]⟩
  have hI : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      rintro ⟨f, hf, h⟩
      rw [one_mul] at h
      exact h0 (h ▸ hf)
    · intro a b hab
      obtain ⟨e, u, he, hu', rfl⟩ := hW.2 a
      obtain ⟨e', u', he', hu'', rfl⟩ := hW.2 b
      by_contra hn
      push Not at hn
      have ha : e ∈ F := by
        by_contra h
        exact hn.1 ⟨1 - e, (hu e he).resolve_left h, by
          rw [mul_assoc, mul_comm u, ← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]⟩
      have hb : e' ∈ F := by
        by_contra h
        exact hn.2 ⟨1 - e', (hu e' he').resolve_left h, by
          rw [mul_assoc, mul_comm u', ← mul_assoc, mul_sub, mul_one, he'.eq, sub_self, zero_mul]⟩
      obtain ⟨f, hf, h⟩ := hab
      have hz : e * e' * f = 0 := by
        obtain ⟨v, hv⟩ := hu'.exists_left_inv
        obtain ⟨v', hv'⟩ := hu''.exists_left_inv
        linear_combination (v * v') * h - (e * e' * f) * hv - (e * e' * f * v * u) * hv'
      exact h0 (hz ▸ hm _ (hm e ha e' hb) f hf)
  refine ⟨⟨I, hI⟩, fun e he => ?_⟩
  rw [show (⟨I, hI⟩ : PrimeSpectrum W).asIdeal = I from rfl, key e he, not_not]

open AlgebraicGeometry in

/- English proof (translation)
Establish `: (X.basicOpen s : Set X)ᶜ = (X.basicOpen (1 - s) : Set X)`. Use extensionality with `x`. Simplify using `only [Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen_top, map_sub, map_one]`. Establish `he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s)` using `hs.map _`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `(IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h`. Introduce `h h'`. Establish `hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0`. Rewrite using `[mul_sub, mul_one, he.eq, sub_self]`.

Conclude with `not_isUnit_zero (hz ▸ h'.mul h)`. Rewrite using `[← isOpen_compl_iff, this]`. Conclude with `(X.basicOpen (1 - s)).isOpen`.
-/
theorem isClosed_basicOpen_idem {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) :
    IsClosed (X.basicOpen s : Set X) := by
  have : (X.basicOpen s : Set X)ᶜ = (X.basicOpen (1 - s) : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen_top, map_sub, map_one]
    have he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s) := hs.map _
    constructor
    · intro h
      exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h
    · intro h h'
      have hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0 := by
        rw [mul_sub, mul_one, he.eq, sub_self]
      exact not_isUnit_zero (hz ▸ h'.mul h)
  rw [← isOpen_compl_iff, this]
  exact (X.basicOpen (1 - s)).isOpen

open AlgebraicGeometry in
/- English proof (translation)
The claim follows from `IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact isClosed_basicOpen_idem hs)`.
-/
theorem isClosedImmersion_basicOpen_idem {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) :
    IsClosedImmersion (X.basicOpen s).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact isClosed_basicOpen_idem hs)

end LateralTheory.E.SysFMPfAlg
