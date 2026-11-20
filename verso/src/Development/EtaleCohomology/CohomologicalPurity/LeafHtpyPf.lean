import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafHtpyZero : Prop := A1 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A]
  (h : off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A ⊥) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafHtpyOne : Prop := A1 → C4 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (x : A), IsUnit (q : A) →
  ∀ (h : off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {x})) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafHtpyMV : Prop := A4 → ∀ (R : Type) [CommRing R] (F : Shv R) {X' X : Scheme.{0}} (p : X' ⟶ X)
  (U V : X.Opens) (U' V' : X'.Opens) (hU : U' ≤ p ⁻¹ᵁ U) (hV : V' ≤ p ⁻¹ᵁ V) (hI : U' ⊓ V' ≤ p ⁻¹ᵁ (U ⊓ V))
  (hS : U' ⊔ V' ≤ p ⁻¹ᵁ (U ⊔ V)),
  Eqv R (sch.map (p.resLE U U' hU)) F → Eqv R (sch.map (p.resLE V V' hV)) F →
  Eqv R (sch.map (p.resLE (U ⊓ V) (U' ⊓ V') hI)) F → Eqv R (sch.map (p.resLE (U ⊔ V) (U' ⊔ V') hS)) F

namespace HtpyPf

/- English proof (translation)
Introduce `p hp hz`. Apply `hp` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((I.map Polynomial.C : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal`. Express the relevant statement in the definitionally equal form `(I : Set A) ⊆ (PrimeSpectrum.comap Polynomial.C p).asIdeal at hz`. Conclude with `SetLike.coe_subset_coe.2 (Ideal.map_le_iff_le_comap.2 hz)`.
-/
theorem offle (A : Type) [CommRing A] (I : Ideal A) : off (Polynomial A) (I.map Polynomial.C) ≤
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I := by
  intro p hp hz
  apply hp
  change ((I.map Polynomial.C : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal
  change (I : Set A) ⊆ (PrimeSpectrum.comap Polynomial.C p).asIdeal at hz
  exact SetLike.coe_subset_coe.2 (Ideal.map_le_iff_le_comap.2 hz)

/- English proof (translation)
Substitute `e e'` using the available equality. Both sides reduce to the same expression.
-/
theorem eqv_congr {X' X : Scheme.{0}} (p : X' ⟶ X) {R : Type} [CommRing R] (F : Shv R) {U U₁ : X.Opens}
    {U' U₁' : X'.Opens} (e : U = U₁) (e' : U' = U₁') (h : U' ≤ p ⁻¹ᵁ U) (h₁ : U₁' ≤ p ⁻¹ᵁ U₁) :
    Eqv R (sch.map (p.resLE U U' h)) F ↔ Eqv R (sch.map (p.resLE U₁ U₁' h₁)) F := by
  subst e e'; rfl

/- English proof (translation)
Apply `TopologicalSpace.Opens.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A))ᶜ = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ∪ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ`. Rewrite using `[PrimeSpectrum.zeroLocus_sup, Set.compl_inter]`.
-/
theorem off_sup (A : Type) [CommRing A] (I J : Ideal A) : off A (I ⊔ J) = off A I ⊔ off A J := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ∪ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_sup, Set.compl_inter]

/- English proof (translation)
Apply `TopologicalSpace.Opens.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(PrimeSpectrum.zeroLocus ((I * J : Ideal A) : Set A))ᶜ = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ∩ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ`. Rewrite using `[PrimeSpectrum.zeroLocus_mul, Set.compl_union]`.
-/
theorem off_mul (A : Type) [CommRing A] (I J : Ideal A) : off A (I * J) = off A I ⊓ off A J := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((I * J : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ∩ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_mul, Set.compl_union]

end HtpyPf

namespace HtpyPf

/- English proof (translation)
Rewrite using `[← Ideal.span_insert]`. Use `congr 1`. Use extensionality with `a`. Simplify using the standard rewrite rules.
-/
theorem span_cons {A : Type} [CommRing A] (x : A) (t : List A) :
    Ideal.span {a | a ∈ x :: t} = Ideal.span {x} ⊔ Ideal.span {a | a ∈ t} := by
  rw [← Ideal.span_insert]; congr 1; ext a; simp

/- English proof (translation)
Rewrite using `[Ideal.span_mul_span']`. Use `congr 1`. Use extensionality with `a`. Simplify using `[Set.singleton_mul]`.
-/
theorem span_mul {A : Type} [CommRing A] (x : A) (t : List A) :
    Ideal.span {x} * Ideal.span {a | a ∈ t} = Ideal.span {a | a ∈ t.map (x * ·)} := by
  rw [Ideal.span_mul_span']; congr 1; ext a; simp [Set.singleton_mul]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `s hs h`. Take `rfl : s = []` from `List.length_eq_zero_iff.1 hs`.

Establish `e : Ideal.span {a | a ∈ ([] : List A)} = ⊥` using `by simp`. Establish `e1 : off A (Ideal.span {a | a ∈ ([] : List A)}) = off A ⊥` using `by rw [e]`. Establish `e2 : off (Polynomial A) ((Ideal.span {a | a ∈ ([] : List A)}).map Polynomial.C) = off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C)` using `by rw [e]`. Conclude with `(eqv_congr (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (tw q i) e1 e2 h (offle A ⊥)).2 (hZ a1 q A (offle A ⊥) i)`. Consider the case `succ n ih`.

Introduce `s hs h`. Choose the witnesses or unpack the hypotheses as in `⟨x, t, rfl⟩ : ∃ x t, s = x :: t := by`. Consider the cases of `s with`. Consider the case `nil => simp at hs`. Consider the case `cons x t => exact ⟨x, t, rfl⟩`.

Establish `ht : t.length = n` using `by simpa using hs`. Use `set I := Ideal.span ({x} : Set A)`. Use `set J := Ideal.span {a | a ∈ t}`. Use `set P := Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))`. Establish `hU` using `offle A I`.

Establish `hV` using `offle A J`. Establish `hI : off (Polynomial A) (I.map Polynomial.C) ⊓ off (Polynomial A) (J.map Polynomial.C) ≤ P ⁻¹ᵁ (off A I ⊓ off A J)` using `fun p hp => ⟨hU hp.1, hV hp.2⟩`. Establish `hS : off (Polynomial A) (I.map Polynomial.C) ⊔ off (Polynomial A) (J.map Polynomial.C) ≤ P ⁻¹ᵁ (off A I ⊔ off A J)`. Rewrite using `[← off_sup, ← off_sup, ← Ideal.map_sup]`. Conclude with `offle A (I ⊔ J)`.

Establish `e1 : off A (Ideal.span {a | a ∈ x :: t}) = off A I ⊔ off A J` using `by rw [span_cons, off_sup]`. Establish `e2 : off (Polynomial A) ((Ideal.span {a | a ∈ x :: t}).map Polynomial.C) = off (Polynomial A) (I.map Polynomial.C) ⊔ off (Polynomial A) (J.map Polynomial.C)`. Rewrite using `[span_cons, Ideal.map_sup, off_sup]`. Use `(eqv_congr P (tw q i) e1 e2 h hS).2 (hMV a4 _ _ P _ _ _ _ hU hV hI hS (hO a1 c4 q A x hq hU i) (ih t ht hV) ?_)` and prove the remaining obligations. Establish `e3 : off A (Ideal.span {a | a ∈ t.map (x * ·)}) = off A I ⊓ off A J` using `by rw [← span_mul, off_mul]`.

Establish `e4 : off (Polynomial A) ((Ideal.span {a | a ∈ t.map (x * ·)}).map Polynomial.C) = off (Polynomial A) (I.map Polynomial.C) ⊓ off (Polynomial A) (J.map Polynomial.C)`. Rewrite using `[← span_mul, Ideal.map_mul, off_mul]`. Conclude with `(eqv_congr P (tw q i) e3 e4 (offle A _) hI).1 (ih _ (by simpa using ht) _)`.
-/
theorem main (hZ : LeafHtpyZero) (hO : LeafHtpyOne) (hMV : LeafHtpyMV) (a1 : A1) (a4 : A4) (c4 : C4)
    (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hq : IsUnit (q : A)) (i : ℤ) :
    ∀ (n : ℕ) (s : List A), s.length = n →
    ∀ h : off (Polynomial A) ((Ideal.span {a | a ∈ s}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {a | a ∈ s}),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i) := by
  intro n
  induction n with
  | zero =>
    intro s hs h
    obtain rfl : s = [] := List.length_eq_zero_iff.1 hs
    have e : Ideal.span {a | a ∈ ([] : List A)} = ⊥ := by simp
    have e1 : off A (Ideal.span {a | a ∈ ([] : List A)}) = off A ⊥ := by rw [e]
    have e2 : off (Polynomial A) ((Ideal.span {a | a ∈ ([] : List A)}).map Polynomial.C) =
        off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C) := by rw [e]
    exact (eqv_congr (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (tw q i) e1 e2 h
      (offle A ⊥)).2 (hZ a1 q A (offle A ⊥) i)
  | succ n ih =>
    intro s hs h
    obtain ⟨x, t, rfl⟩ : ∃ x t, s = x :: t := by
      cases s with
      | nil => simp at hs
      | cons x t => exact ⟨x, t, rfl⟩
    have ht : t.length = n := by simpa using hs
    set I := Ideal.span ({x} : Set A)
    set J := Ideal.span {a | a ∈ t}
    set P := Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))
    have hU := offle A I
    have hV := offle A J
    have hI : off (Polynomial A) (I.map Polynomial.C) ⊓ off (Polynomial A) (J.map Polynomial.C) ≤
        P ⁻¹ᵁ (off A I ⊓ off A J) := fun p hp => ⟨hU hp.1, hV hp.2⟩
    have hS : off (Polynomial A) (I.map Polynomial.C) ⊔ off (Polynomial A) (J.map Polynomial.C) ≤
        P ⁻¹ᵁ (off A I ⊔ off A J) := by
      rw [← off_sup, ← off_sup, ← Ideal.map_sup]; exact offle A (I ⊔ J)
    have e1 : off A (Ideal.span {a | a ∈ x :: t}) = off A I ⊔ off A J := by rw [span_cons, off_sup]
    have e2 : off (Polynomial A) ((Ideal.span {a | a ∈ x :: t}).map Polynomial.C) =
        off (Polynomial A) (I.map Polynomial.C) ⊔ off (Polynomial A) (J.map Polynomial.C) := by
      rw [span_cons, Ideal.map_sup, off_sup]
    refine (eqv_congr P (tw q i) e1 e2 h hS).2 (hMV a4 _ _ P _ _ _ _ hU hV hI hS (hO a1 c4 q A x hq hU i) (ih t ht hV) ?_)
    have e3 : off A (Ideal.span {a | a ∈ t.map (x * ·)}) = off A I ⊓ off A J := by rw [← span_mul, off_mul]
    have e4 : off (Polynomial A) ((Ideal.span {a | a ∈ t.map (x * ·)}).map Polynomial.C) =
        off (Polynomial A) (I.map Polynomial.C) ⊓ off (Polynomial A) (J.map Polynomial.C) := by
      rw [← span_mul, Ideal.map_mul, off_mul]
    exact (eqv_congr P (tw q i) e3 e4 (offle A _) hI).1 (ih _ (by simpa using ht) _)

end HtpyPf

/- English proof (translation)
Introduce `a1 a4 c4 q _ A _ I hI hq h i`. Take `⟨S, rfl⟩` from `hI`. Establish `e : ({a | a ∈ S.toList} : Set A) = (S : Set A)` using `by ext a; simp`. Use `HtpyPf.main hZ hO hMV a1 a4 c4 q A hq i _ S.toList rfl (by rw [e]; exact HtpyPf.offle A _)` as an intermediate fact. Conclude with `(HtpyPf.eqv_congr (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (tw q i) (by rw [e]) (by rw [e]) _ h).1 this`.
-/
theorem LeafHtpy_of (hZ : LeafHtpyZero) (hO : LeafHtpyOne) (hMV : LeafHtpyMV) : LeafHtpy := by
  intro a1 a4 c4 q _ A _ I hI hq h i
  obtain ⟨S, rfl⟩ := hI
  have e : ({a | a ∈ S.toList} : Set A) = (S : Set A) := by ext a; simp
  have := HtpyPf.main hZ hO hMV a1 a4 c4 q A hq i _ S.toList rfl (by rw [e]; exact HtpyPf.offle A _)
  exact (HtpyPf.eqv_congr (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (tw q i)
    (by rw [e]) (by rw [e]) _ h).1 this

end LateralTheory.CohomologicalPurity.Thom
