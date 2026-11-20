import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}} {k : Type u} [Field k]

noncomputable def filterNeTop (E : List X.IdealSheafData) : List X.IdealSheafData :=
  E.filter (fun D => @decide (D ≠ ⊤) (Classical.propDecidable _))

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem filterNeTop_nil : filterNeTop ([] : List X.IdealSheafData) = [] := rfl

/- English proof (translation)
Simplify using `[filterNeTop, h]`.
-/
private theorem filterNeTop_cons_of_ne_top (D : X.IdealSheafData) (T : List X.IdealSheafData)
    (h : D ≠ ⊤) : filterNeTop (D :: T) = D :: filterNeTop T := by
  simp [filterNeTop, h]

/- English proof (translation)
Simplify using `[filterNeTop]`.
-/
private theorem filterNeTop_cons_top (T : List X.IdealSheafData) :
    filterNeTop ((⊤ : X.IdealSheafData) :: T) = filterNeTop T := by
  simp [filterNeTop]

/- English proof (translation)
Simplify using `only [filterNeTop, List.mem_filter] at h`. Conclude with `h.1`.
-/
private theorem mem_of_mem_filterNeTop {D : X.IdealSheafData} {E : List X.IdealSheafData}
    (h : D ∈ filterNeTop E) : D ∈ E := by
  simp only [filterNeTop, List.mem_filter] at h
  exact h.1

/- English proof (translation)
Simplify using `only [filterNeTop, List.mem_filter]`. Conclude with `⟨hD, by simpa using h⟩`.
-/
private theorem mem_filterNeTop {D : X.IdealSheafData} {E : List X.IdealSheafData}
    (hD : D ∈ E) (h : D ≠ ⊤) : D ∈ filterNeTop E := by
  simp only [filterNeTop, List.mem_filter]
  exact ⟨hD, by simpa using h⟩

private def unshiftIndex (g₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => g₀ i

private def shiftIndex (g₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => g₀ i + 1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `E E' hlen _`. Establish `h0 : E'.length = 0` using `by omega`. Conclude with `⟨id, fun i hi _ => absurd hi (by omega), fun i j hi _ _ _ _ => absurd hi (by omega)⟩`.

Consider the case `succ n ih`. Introduce `E E' hlen hfilt`. Consider the cases of `E' with`. Consider the case `nil`. Conclude with `⟨id, fun i hi _ => absurd hi (by simp), fun i j hi _ _ _ _ => absurd hi (by simp)⟩`.

Consider the case `cons D T'`. Distinguish the cases in `hD : D = ⊤`. Substitute `hD` using the available equality. Rewrite `hfilt` using `[filterNeTop_cons_top]`. Establish `hlen' : E.length + T'.length ≤ n`.

Simplify using `only [List.length_cons] at hlen`. Use linear arithmetic over natural numbers and integers. Take `⟨g₀, h1, h2⟩` from `ih E T' hlen' hfilt`. Use `⟨unshiftIndex g₀, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi hne`.

Consider the cases of `i with`. Consider the case `zero => simp at hne`. Consider the case `succ i`. Simplify using `only [List.getElem?_cons_succ] at hne`. Simplify using `only [List.length_cons] at hi`.

Simplify using `only [unshiftIndex, List.getElem?_cons_succ]`. Conclude with `h1 i (by omega) hne`. Introduce `i j hi hj hni hnj hgij`. Consider the cases of `i with`. Consider the case `zero => simp at hni`.

Consider the case `succ i`. Consider the cases of `j with`. Consider the case `zero => simp at hnj`. Consider the case `succ j`. Establish `e1 : unshiftIndex g₀ (i + 1) = g₀ i` using `rfl`.

Establish `e2 : unshiftIndex g₀ (j + 1) = g₀ j` using `rfl`. Establish `hij : g₀ i = g₀ j` using `by omega`. Simplify using `only [List.getElem?_cons_succ] at hni hnj`. Simplify using `only [List.length_cons] at hi hj`. Use `h2 i j (by omega) (by omega) hni hnj hij` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite `hfilt` using `[filterNeTop_cons_of_ne_top D T' hD]`. Consider the cases of `E with`. Consider the case `nil`. Rewrite `hfilt` using `[filterNeTop_nil]`.

Conclude with `absurd hfilt (List.cons_ne_nil _ _)`. Consider the case `cons C T`. Distinguish the cases in `hC : C = ⊤`. Substitute `hC` using the available equality. Rewrite `hfilt` using `[filterNeTop_cons_top]`.

Establish `hlen' : T.length + (D :: T').length ≤ n`. Simplify using `only [List.length_cons] at hlen ⊢`. Use linear arithmetic over natural numbers and integers. Establish `hfilt' : filterNeTop (D :: T') = filterNeTop T`. Rewrite using `[filterNeTop_cons_of_ne_top D T' hD]`.

Conclude with `hfilt`. Take `⟨g₀, h1, h2⟩` from `ih T (D :: T') hlen' hfilt'`. Use `⟨fun i => g₀ i + 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi hne`. Take `⟨ha, hb⟩` from `h1 i hi hne`.

Use `⟨by simp only [List.length_cons]; omega, ?_⟩` and prove the remaining obligations. Simplify using `using hb`. Introduce `i j hi hj hni hnj hgij`. Establish `hgij' : g₀ i + 1 = g₀ j + 1` using `hgij`. Conclude with `h2 i j hi hj hni hnj (by omega)`.

Rewrite `hfilt` using `[filterNeTop_cons_of_ne_top C T hC]`. Simplify using `only [List.cons.injEq] at hfilt`. Take `⟨hcond, hTT⟩` from `hfilt`. Establish `hlen' : T.length + T'.length ≤ n`. Simplify using `only [List.length_cons] at hlen`.

Use linear arithmetic over natural numbers and integers. Take `⟨g₀, h1, h2⟩` from `ih T T' hlen' hTT`. Use `⟨shiftIndex g₀, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi hne`. Consider the cases of `i with`.

Consider the case `zero`. Simplify using `only [shiftIndex]`. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Simplify using `[hcond]`. Consider the case `succ i`.

Simplify using `only [List.getElem?_cons_succ] at hne`. Simplify using `only [List.length_cons] at hi`. Take `⟨ha, hb⟩` from `h1 i (by omega) hne`. Simplify using `only [shiftIndex, List.getElem?_cons_succ]`. Conclude with `⟨by simp only [List.length_cons]; omega, hb⟩`.

Introduce `i j hi hj hni hnj hgij`. Consider the cases of `i with`. Consider the case `zero`. Consider the cases of `j with`. Consider the case `zero => rfl`.

Consider the case `succ j`. Establish `e1 : shiftIndex g₀ 0 = 0` using `rfl`. Establish `e2 : shiftIndex g₀ (j + 1) = g₀ j + 1` using `rfl`. Use linear arithmetic over natural numbers and integers. Consider the case `succ i`.

Consider the cases of `j with`. Consider the case `zero`. Establish `e1 : shiftIndex g₀ 0 = 0` using `rfl`. Establish `e2 : shiftIndex g₀ (i + 1) = g₀ i + 1` using `rfl`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ j`. Establish `e1 : shiftIndex g₀ (i + 1) = g₀ i + 1` using `rfl`. Establish `e2 : shiftIndex g₀ (j + 1) = g₀ j + 1` using `rfl`. Establish `hij : g₀ i = g₀ j` using `by omega`. Simplify using `only [List.getElem?_cons_succ] at hni hnj`.

Simplify using `only [List.length_cons] at hi hj`. Use `h2 i j (by omega) (by omega) hni hnj hij` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_index_map_of_filterNeTop_eq (n : ℕ) :
    ∀ (E E' : List X.IdealSheafData),
    E.length + E'.length ≤ n → filterNeTop E' = filterNeTop E →
    ∃ g : ℕ → ℕ,
      (∀ i, i < E'.length → E'[i]? ≠ some ⊤ → g i < E.length ∧ E[g i]? = E'[i]?) ∧
      (∀ i j, i < E'.length → j < E'.length → E'[i]? ≠ some ⊤ → E'[j]? ≠ some ⊤ →
        g i = g j → i = j) := by
  induction n with
  | zero =>
    intro E E' hlen _
    have h0 : E'.length = 0 := by omega
    exact ⟨id, fun i hi _ => absurd hi (by omega), fun i j hi _ _ _ _ => absurd hi (by omega)⟩
  | succ n ih =>
    intro E E' hlen hfilt
    cases E' with
    | nil =>
      exact ⟨id, fun i hi _ => absurd hi (by simp), fun i j hi _ _ _ _ => absurd hi (by simp)⟩
    | cons D T' =>
      by_cases hD : D = ⊤
      · subst hD
        rw [filterNeTop_cons_top] at hfilt
        have hlen' : E.length + T'.length ≤ n := by
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨g₀, h1, h2⟩ := ih E T' hlen' hfilt
        refine ⟨unshiftIndex g₀, ?_, ?_⟩
        · intro i hi hne
          cases i with
          | zero => simp at hne
          | succ i =>
            simp only [List.getElem?_cons_succ] at hne
            simp only [List.length_cons] at hi
            simp only [unshiftIndex, List.getElem?_cons_succ]
            exact h1 i (by omega) hne
        · intro i j hi hj hni hnj hgij
          cases i with
          | zero => simp at hni
          | succ i =>
            cases j with
            | zero => simp at hnj
            | succ j =>
              have e1 : unshiftIndex g₀ (i + 1) = g₀ i := rfl
              have e2 : unshiftIndex g₀ (j + 1) = g₀ j := rfl
              have hij : g₀ i = g₀ j := by omega
              simp only [List.getElem?_cons_succ] at hni hnj
              simp only [List.length_cons] at hi hj
              have := h2 i j (by omega) (by omega) hni hnj hij
              omega
      · rw [filterNeTop_cons_of_ne_top D T' hD] at hfilt
        cases E with
        | nil =>
          rw [filterNeTop_nil] at hfilt
          exact absurd hfilt (List.cons_ne_nil _ _)
        | cons C T =>
          by_cases hC : C = ⊤
          · subst hC
            rw [filterNeTop_cons_top] at hfilt
            have hlen' : T.length + (D :: T').length ≤ n := by
              simp only [List.length_cons] at hlen ⊢
              omega
            have hfilt' : filterNeTop (D :: T') = filterNeTop T := by
              rw [filterNeTop_cons_of_ne_top D T' hD]
              exact hfilt
            obtain ⟨g₀, h1, h2⟩ := ih T (D :: T') hlen' hfilt'
            refine ⟨fun i => g₀ i + 1, ?_, ?_⟩
            · intro i hi hne
              obtain ⟨ha, hb⟩ := h1 i hi hne
              refine ⟨by simp only [List.length_cons]; omega, ?_⟩
              simpa using hb
            · intro i j hi hj hni hnj hgij
              have hgij' : g₀ i + 1 = g₀ j + 1 := hgij
              exact h2 i j hi hj hni hnj (by omega)
          · rw [filterNeTop_cons_of_ne_top C T hC] at hfilt
            simp only [List.cons.injEq] at hfilt
            obtain ⟨hcond, hTT⟩ := hfilt
            have hlen' : T.length + T'.length ≤ n := by
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨g₀, h1, h2⟩ := ih T T' hlen' hTT
            refine ⟨shiftIndex g₀, ?_, ?_⟩
            · intro i hi hne
              cases i with
              | zero =>
                simp only [shiftIndex]
                refine ⟨by simp, ?_⟩
                simp [hcond]
              | succ i =>
                simp only [List.getElem?_cons_succ] at hne
                simp only [List.length_cons] at hi
                obtain ⟨ha, hb⟩ := h1 i (by omega) hne
                simp only [shiftIndex, List.getElem?_cons_succ]
                exact ⟨by simp only [List.length_cons]; omega, hb⟩
            · intro i j hi hj hni hnj hgij
              cases i with
              | zero =>
                cases j with
                | zero => rfl
                | succ j =>
                  have e1 : shiftIndex g₀ 0 = 0 := rfl
                  have e2 : shiftIndex g₀ (j + 1) = g₀ j + 1 := rfl
                  omega
              | succ i =>
                cases j with
                | zero =>
                  have e1 : shiftIndex g₀ 0 = 0 := rfl
                  have e2 : shiftIndex g₀ (i + 1) = g₀ i + 1 := rfl
                  omega
                | succ j =>
                  have e1 : shiftIndex g₀ (i + 1) = g₀ i + 1 := rfl
                  have e2 : shiftIndex g₀ (j + 1) = g₀ j + 1 := rfl
                  have hij : g₀ i = g₀ j := by omega
                  simp only [List.getElem?_cons_succ] at hni hnj
                  simp only [List.length_cons] at hi hj
                  have := h2 i j (by omega) (by omega) hni hnj hij
                  omega

open Classical in
private def transportAssignment {m : ℕ} (E' : List X.IdealSheafData) (a : ℕ → Option (Fin m))
    (g : ℕ → ℕ) : ℕ → Option (Fin m) :=
  fun i => if E'[i]? = some ⊤ then none else a (g i)

/- English proof (translation)
Simplify using `[transportAssignment, h]`.
-/
private theorem transportAssignment_of_eq_top {m : ℕ} (E' : List X.IdealSheafData)
    (a : ℕ → Option (Fin m)) (g : ℕ → ℕ) (i : ℕ) (h : E'[i]? = some ⊤) :
    transportAssignment E' a g i = none := by
  simp [transportAssignment, h]

/- English proof (translation)
Simplify using `[transportAssignment, h]`.
-/
private theorem transportAssignment_of_ne_top {m : ℕ} (E' : List X.IdealSheafData)
    (a : ℕ → Option (Fin m)) (g : ℕ → ℕ) (i : ℕ) (h : E'[i]? ≠ some ⊤) :
    transportAssignment E' a g i = a (g i) := by
  simp [transportAssignment, h]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi j hj t hti htj`. Establish `hni : E'[i]? ≠ some ⊤`. Introduce `hc`. Rewrite `hti` using `[transportAssignment_of_eq_top E' a g i hc]`.

Simplify using `at hti`. Establish `hnj : E'[j]? ≠ some ⊤`. Introduce `hc`. Rewrite `htj` using `[transportAssignment_of_eq_top E' a g j hc]`. Simplify using `at htj`.

Rewrite `hti` using `[transportAssignment_of_ne_top E' a g i hni]`. Rewrite `htj` using `[transportAssignment_of_ne_top E' a g j hnj]`. Take `⟨hgi, -⟩` from `hg1 i hi hni`. Take `⟨hgj, -⟩` from `hg1 j hj hnj`. Conclude with `hg2 i j hi hj hni hnj (hinj (g i) hgi (g j) hgj t hti htj)`.

Introduce `i hi hn`. Distinguish the cases in `hc : E'[i]? = some ⊤`. Establish `he : E'[i] = ⊤`. Rewrite `hc` using `[List.getElem?_eq_getElem hi]`. Conclude with `Option.some_inj.mp hc`.

Rewrite using `[he]`. Conclude with `Scheme.IdealSheafData.comap_top U.ι`. Rewrite `hn` using `[transportAssignment_of_ne_top E' a g i hc]`. Take `⟨hgi, hb⟩` from `hg1 i hi hc`. Establish `he : E[g i] = E'[i]`.

Rewrite `hb` using `[List.getElem?_eq_getElem hgi, List.getElem?_eq_getElem hi]`. Conclude with `Option.some_inj.mp hb`. Rewrite using `[← he]`. Conclude with `hnone (g i) hgi hn`. Introduce `i hi t hti`.

Establish `hc : E'[i]? ≠ some ⊤`. Introduce `hc`. Rewrite `hti` using `[transportAssignment_of_eq_top E' a g i hc]`. Simplify using `at hti`. Rewrite `hti` using `[transportAssignment_of_ne_top E' a g i hc]`.

Take `⟨hgi, hb⟩` from `hg1 i hi hc`. Establish `he : E[g i] = E'[i]`. Rewrite `hb` using `[List.getElem?_eq_getElem hgi, List.getElem?_eq_getElem hi]`. Conclude with `Option.some_inj.mp hb`. Rewrite using `[← he]`.

Conclude with `hsome (g i) hgi t hti`.
-/
private theorem transportAssignment_injective_and_coordIdeal {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (E E' : List X.IdealSheafData) (a : ℕ → Option (Fin m)) (g : ℕ → ℕ)
    (hg1 : ∀ i, i < E'.length → E'[i]? ≠ some ⊤ → g i < E.length ∧ E[g i]? = E'[i]?)
    (hg2 : ∀ i j, i < E'.length → j < E'.length → E'[i]? ≠ some ⊤ → E'[j]? ≠ some ⊤ →
      g i = g j → i = j)
    (hinj : ∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal E[i] U = ⊤)
    (hsome : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t →
      restrictIdeal E[i] U = c.coordIdeal {t}) :
    (∀ i < E'.length, ∀ j < E'.length, ∀ t : Fin m,
        transportAssignment E' a g i = some t → transportAssignment E' a g j = some t → i = j) ∧
      (∀ (i : ℕ) (hi : i < E'.length), transportAssignment E' a g i = none →
        restrictIdeal E'[i] U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < E'.length) (t : Fin m), transportAssignment E' a g i = some t →
        restrictIdeal E'[i] U = c.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    have hni : E'[i]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top E' a g i hc] at hti
      simp at hti
    have hnj : E'[j]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top E' a g j hc] at htj
      simp at htj
    rw [transportAssignment_of_ne_top E' a g i hni] at hti
    rw [transportAssignment_of_ne_top E' a g j hnj] at htj
    obtain ⟨hgi, -⟩ := hg1 i hi hni
    obtain ⟨hgj, -⟩ := hg1 j hj hnj
    exact hg2 i j hi hj hni hnj (hinj (g i) hgi (g j) hgj t hti htj)
  · intro i hi hn
    by_cases hc : E'[i]? = some ⊤
    · have he : E'[i] = ⊤ := by
        rw [List.getElem?_eq_getElem hi] at hc
        exact Option.some_inj.mp hc
      rw [he]
      exact Scheme.IdealSheafData.comap_top U.ι
    · rw [transportAssignment_of_ne_top E' a g i hc] at hn
      obtain ⟨hgi, hb⟩ := hg1 i hi hc
      have he : E[g i] = E'[i] := by
        rw [List.getElem?_eq_getElem hgi, List.getElem?_eq_getElem hi] at hb
        exact Option.some_inj.mp hb
      rw [← he]
      exact hnone (g i) hgi hn
  · intro i hi t hti
    have hc : E'[i]? ≠ some ⊤ := by
      intro hc
      rw [transportAssignment_of_eq_top E' a g i hc] at hti
      simp at hti
    rw [transportAssignment_of_ne_top E' a g i hc] at hti
    obtain ⟨hgi, hb⟩ := hg1 i hi hc
    have he : E[g i] = E'[i] := by
      rw [List.getElem?_eq_getElem hgi, List.getElem?_eq_getElem hi] at hb
      exact Option.some_inj.mp hb
    rw [← he]
    exact hsome (g i) hgi t hti

/- English proof (translation)
Use `isSmoothDivisor_of_locally_coordIdeal (p := p) ⊤ ?_` and prove the remaining obligations. Introduce `x`. Take `⟨U, m, hxU, hU, ⟨c⟩⟩` from `exists_etaleChart p x`. Conclude with `⟨U, hxU, m, c, Or.inl (Scheme.IdealSheafData.comap_top U.ι)⟩`.
-/
theorem isSmoothDivisor_top (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] :
    IsSmoothDivisor p (⊤ : X.IdealSheafData) := by
  refine isSmoothDivisor_of_locally_coordIdeal (p := p) ⊤ ?_
  intro x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  exact ⟨U, hxU, m, c, Or.inl (Scheme.IdealSheafData.comap_top U.ι)⟩

/- English proof (translation)
Take `⟨U, hxU, m, c, a, hinj, hnone, hsome⟩` from `hE.exists_etaleChart`. Take `⟨g, hg1, hg2⟩` from `exists_index_map_of_filterNeTop_eq (E.length + E'.length) E E' le_rfl h.symm`. Take `⟨k1, k2, k3⟩` from `transportAssignment_injective_and_coordIdeal c E E' a g hg1 hg2 hinj hnone hsome`. Conclude with `inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, c, transportAssignment E' a g, k1, k2, k3⟩`.
-/
theorem inStrictNormalCrossingPositionAt_of_filterNeTop_eq (p : X ⟶ Spec (CommRingCat.of k))
    (E E' : List X.IdealSheafData) (h : filterNeTop E = filterNeTop E') (x : X)
    (hE : InStrictNormalCrossingPositionAt p E x) : InStrictNormalCrossingPositionAt p E' x := by
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := hE.exists_etaleChart
  obtain ⟨g, hg1, hg2⟩ :=
    exists_index_map_of_filterNeTop_eq (E.length + E'.length) E E' le_rfl h.symm
  obtain ⟨k1, k2, k3⟩ := transportAssignment_injective_and_coordIdeal c E E' a g hg1 hg2 hinj hnone hsome
  exact inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, c, transportAssignment E' a g, k1, k2, k3⟩

/- English proof (translation)
Rewrite `hE`, the goal using `[inStrictNormalCrossingPosition_iff]`. Take `⟨hsm, hpos⟩` from `hE`. Use `⟨?_, fun x => inStrictNormalCrossingPositionAt_of_filterNeTop_eq p E E' h x (hpos x)⟩` and prove the remaining obligations. Introduce `D hD`. Distinguish the cases in `hDt : D = ⊤`.

Rewrite using `[hDt]`. Conclude with `isSmoothDivisor_top p`. Establish `h1 : D ∈ filterNeTop E'` using `mem_filterNeTop hD hDt`. Rewrite `h1` using `[← h]`. Conclude with `hsm D (mem_of_mem_filterNeTop h1)`.
-/
theorem inStrictNormalCrossingPosition_of_filterNeTop_eq (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (E E' : List X.IdealSheafData)
    (h : filterNeTop E = filterNeTop E') (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p E' := by
  rw [inStrictNormalCrossingPosition_iff] at hE ⊢
  obtain ⟨hsm, hpos⟩ := hE
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_of_filterNeTop_eq p E E' h x (hpos x)⟩
  intro D hD
  by_cases hDt : D = ⊤
  · rw [hDt]
    exact isSmoothDivisor_top p
  · have h1 : D ∈ filterNeTop E' := mem_filterNeTop hD hDt
    rw [← h] at h1
    exact hsm D (mem_of_mem_filterNeTop h1)

/- English proof (translation)
Take `⟨g, hg1, hg2⟩` from `exists_index_map_of_filterNeTop_eq (E.length + E'.length) E E' le_rfl h.symm`. Use `hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZ⟩` from `hE.exists_etaleChart hx`. Take `⟨k1, k2, k3⟩` from `transportAssignment_injective_and_coordIdeal c E E' a g hg1 hg2 hinj hnone hsome`.

Conclude with `⟨U, hxU, m, c, transportAssignment E' a g, S, k1, k2, k3, hZ⟩`.
-/
theorem hasStrictNormalCrossingsWith_of_filterNeTop_eq (p : X ⟶ Spec (CommRingCat.of k))
    (Z : X.IdealSheafData) (E E' : List X.IdealSheafData)
    (h : filterNeTop E = filterNeTop E') (hE : HasStrictNormalCrossingsWith p Z E) :
    HasStrictNormalCrossingsWith p Z E' := by
  obtain ⟨g, hg1, hg2⟩ :=
    exists_index_map_of_filterNeTop_eq (E.length + E'.length) E E' le_rfl h.symm
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZ⟩ := hE.exists_etaleChart hx
  obtain ⟨k1, k2, k3⟩ := transportAssignment_injective_and_coordIdeal c E E' a g hg1 hg2 hinj hnone hsome
  exact ⟨U, hxU, m, c, transportAssignment E' a g, S, k1, k2, k3, hZ⟩

end FunctorialResolution.EmbeddedResolution
