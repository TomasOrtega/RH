import Development.EtaleCohomology.CohomologicalPurity.LeafHsContPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def OffContN (r : ℕ) : Prop := ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (x : Fin r → A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span (Set.range x)) D s t n i

def OffContBasic : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (f : A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span {f}) D s t n i

def OffContStep : Prop := A1 → A4 → B1 → LeafBd → LeafExc → OffContBasic → ∀ r : ℕ, OffContN r → OffContN (r + 1)

/- English proof (translation)
Introduce `q A B _ _ φ x hq J _ _ D s t hc he n i`. Establish `hx : Ideal.span (Set.range x) = Ideal.span {(0 : A)}`. Rewrite using `[Set.range_eq_empty, Ideal.span_empty, Ideal.span_singleton_eq_bot.mpr rfl]`. Rewrite using `[hx]`. Conclude with `hb a1 a4 b1 q φ 0 hq J D s t hc he n i`.
-/
theorem offContN_zero (hb : OffContBasic) (a1 : A1) (a4 : A4) (b1 : B1) : OffContN 0 := by
  intro q A B _ _ φ x hq J _ _ D s t hc he n i
  have hx : Ideal.span (Set.range x) = Ideal.span {(0 : A)} := by
    rw [Set.range_eq_empty, Ideal.span_empty, Ideal.span_singleton_eq_bot.mpr rfl]
  rw [hx]
  exact hb a1 a4 b1 q φ 0 hq J D s t hc he n i

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => exact offContN_zero hb a1 a4 b1`. Consider the case `succ r ih => exact hs a1 a4 b1 bd ex hb r ih`.
-/
theorem offContN_all (hb : OffContBasic) (hs : OffContStep) (a1 : A1) (a4 : A4) (b1 : B1) (bd : LeafBd)
    (ex : LeafExc) : ∀ r, OffContN r := by
  intro r
  induction r with
  | zero => exact offContN_zero hb a1 a4 b1
  | succ r ih => exact hs a1 a4 b1 bd ex hb r ih

/- English proof (translation)
Introduce `a1 a4 b1 bd ex q A B _ _ φ I hI hq J _ _ D s t hc he n i`. Take `⟨S, hS⟩` from `hI`. Establish `h` using `offContN_all hb hs a1 a4 b1 bd ex S.card q φ (fun k => (S.equivFin.symm k : A)) hq J D s t hc he n i`. Establish `hr : Set.range (fun k => (S.equivFin.symm k : A)) = (S : Set A)`. Use extensionality with `a`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Conclude with `(S.equivFin.symm k).2`. Introduce `ha; exact ⟨S.equivFin ⟨a, ha⟩, by simp⟩`. Rewrite `h` using `[hr, hS]`.

Conclude with `h`.
-/
theorem leafOffCont_of (hb : OffContBasic) (hs : OffContStep) : LeafOffCont := by
  intro a1 a4 b1 bd ex q A B _ _ φ I hI hq J _ _ D s t hc he n i
  obtain ⟨S, hS⟩ := hI
  have h := offContN_all hb hs a1 a4 b1 bd ex S.card q φ (fun k => (S.equivFin.symm k : A)) hq J D s t hc he n i
  have hr : Set.range (fun k => (S.equivFin.symm k : A)) = (S : Set A) := by
    ext a; constructor
    · rintro ⟨k, rfl⟩; exact (S.equivFin.symm k).2
    · intro ha; exact ⟨S.equivFin ⟨a, ha⟩, by simp⟩
  rw [hr, hS] at h
  exact h

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A))ᶜ = _`. Rewrite using `[PrimeSpectrum.zeroLocus_span, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]`.
-/
theorem off_span_singleton (A : Type) [CommRing A] (f : A) :
    ((off A (Ideal.span {f}) : Set (Spec (CommRingCat.of A))) =
      ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A))) := by
  change (PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]

/- English proof (translation)
Apply `TopologicalSpace.Opens.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(PrimeSpectrum.zeroLocus ((Ideal.span (u ∪ v) : Ideal A) : Set A))ᶜ = (PrimeSpectrum.zeroLocus ((Ideal.span u : Ideal A) : Set A))ᶜ ∪ (PrimeSpectrum.zeroLocus ((Ideal.span v : Ideal A) : Set A))ᶜ`. Rewrite using `[PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_union, Set.compl_inter]`.
-/
theorem off_span_union (A : Type) [CommRing A] (u v : Set A) :
    off A (Ideal.span (u ∪ v)) = off A (Ideal.span u) ⊔ off A (Ideal.span v) := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((Ideal.span (u ∪ v) : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus ((Ideal.span u : Ideal A) : Set A))ᶜ ∪
      (PrimeSpectrum.zeroLocus ((Ideal.span v : Ideal A) : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span,
    PrimeSpectrum.zeroLocus_union, Set.compl_inter]

/- English proof (translation)
Rewrite using `[Set.union_singleton]`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Break down `Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl` into its components or cases.

Conclude with `Set.mem_insert_of_mem _ ⟨k', rfl⟩`. Conclude with `Set.mem_insert _ _`. Introduce and unpack `(rfl | ⟨k, rfl⟩)`. Conclude with `⟨_, rfl⟩`. Conclude with `⟨_, rfl⟩`.
-/
theorem range_fin_succ {A : Type} {r : ℕ} (x : Fin (r + 1) → A) :
    Set.range x = Set.range (fun k : Fin r => x k.castSucc) ∪ {x (Fin.last r)} := by
  rw [Set.union_singleton]
  ext a; constructor
  · rintro ⟨k, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · exact Set.mem_insert_of_mem _ ⟨k', rfl⟩
    · exact Set.mem_insert _ _
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

end LateralTheory.CohomologicalPurity
