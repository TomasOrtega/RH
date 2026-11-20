import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

open Classical in
/- English proof (translation)
Establish `hs : {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y} = ↑(AF.filter (fun s => s ≫ c.f = y))`. Use extensionality with `z`. Simplify using `[hAF]`. Use `show (∑ᶠ (z : gp Ω ⟶ c.Z) (_ : z ∈ {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y}), c.w Ω z) = _`. Rewrite using `[hs, finsum_mem_coe_finset]`.
-/
private lemma cyc_eq_sum {S Y : Scheme.{0}} (c : Corr S Y) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y) (AF : Finset (gp Ω ⟶ c.Z)) (hAF : ∀ s, s ∈ AF ↔ s ≫ c.p = x) :
    c.cyc Ω x y = ∑ s ∈ AF with s ≫ c.f = y, c.w Ω s := by
  have hs : {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y} = ↑(AF.filter (fun s => s ≫ c.f = y)) := by
    ext z
    simp [hAF]
  show (∑ᶠ (z : gp Ω ⟶ c.Z) (_ : z ∈ {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y}), c.w Ω z) = _
  rw [hs, finsum_mem_coe_finset]

/- English proof (translation)
Introduce `hF S Y X c d e a b pb hp hf hw Ω _ _ x y`. Use `haveI := c.fin`. Use `haveI := d.fin`. Use `haveI := e.fin`. Set `A` to `(hF c.p Ω x).toFinset`.

Establish `hAm : ∀ s, s ∈ A ↔ s ≫ c.p = x` using `fun s => by simp [A, fib]`. Set `B : (gp Ω ⟶ Y) → Finset (gp Ω ⟶ d.Z)` to `fun t => (hF d.p Ω t).toFinset`. Establish `hBm : ∀ t u, u ∈ B t ↔ u ≫ d.p = t` using `fun t u => by simp [B, fib]`. Set `E` to `(hF e.p Ω x).toFinset`. Establish `hEm : ∀ z, z ∈ E ↔ z ≫ e.p = x` using `fun z => by simp [E, fib]`.

Establish `hR : (∑ᶠ t : gp Ω ⟶ Y, c.cyc Ω x t * d.cyc Ω t y) = ∑ s ∈ A, c.w Ω s * d.cyc Ω (s ≫ c.f) y`. Rewrite using `[finsum_eq_sum_of_support_subset (s := A.image (· ≫ c.f))]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := A) (t := A.image (· ≫ c.f)) (g := (· ≫ c.f)) (fun s hs => Finset.mem_image_of_mem _ hs)]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[cyc_eq_sum c Ω x t A hAm, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hs).2]`. Introduce `t ht`. Rewrite `ht` using `[Function.mem_support]`. Assume the negation of the conclusion as `hn`.

Apply `ht` to reduce the goal to its premises. Rewrite using `[cyc_eq_sum c Ω x t A hAm, Finset.sum_eq_zero, zero_mul]`. Introduce `s hs`. Conclude with `absurd (Finset.mem_coe.2 (Finset.mem_image.2 ⟨s, (Finset.mem_filter.1 hs).1, (Finset.mem_filter.1 hs).2⟩)) hn`. Establish `hmaps : ∀ z ∈ E.filter (fun z => z ≫ e.f = y), z ≫ b ∈ A`.

Introduce `z hz`. Rewrite using `[hAm, Category.assoc, ← hp]`. Conclude with `(hEm z).1 (Finset.mem_filter.1 hz).1`. Rewrite using `[hR, cyc_eq_sum e Ω x y E hEm, ← Finset.sum_fiberwise_of_maps_to hmaps]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations.

Rewrite using `[cyc_eq_sum d Ω (s ≫ c.f) y (B (s ≫ c.f)) (hBm _), Finset.mul_sum]`. Use `Finset.sum_bij' (fun z _ => z ≫ a) (fun u hu => pb.lift u s ((hBm _ u).1 (Finset.mem_filter.1 hu).1)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [Finset.mem_filter, hEm, hBm] at hz ⊢`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, pb.w, ← Category.assoc, hz.2]`. Rewrite using `[Category.assoc, ← hf, hz.1.2]`. Introduce `u hu`. Establish `hu'` using `Finset.mem_filter.1 hu`. Simplify using `only [Finset.mem_filter, hEm]`.

Use `⟨⟨?_, ?_⟩, pb.lift_snd _ _ _⟩` and prove the remaining obligations. Rewrite using `[hp, ← Category.assoc, pb.lift_snd]`. Conclude with `(hAm s).1 hs`. Rewrite using `[hf, ← Category.assoc, pb.lift_fst]`. Conclude with `hu'.2`.

Introduce `z hz`. Establish `hz'` using `Finset.mem_filter.1 hz`. Apply `pb.hom_ext` to reduce the goal to its premises. Rewrite using `[pb.lift_fst]`. Rewrite using `[pb.lift_snd, hz'.2]`.

Introduce `u hu`. Conclude with `pb.lift_fst _ _ _`. Introduce `z hz`. Establish `hz'` using `Finset.mem_filter.1 hz`. Rewrite using `[hw]`.

Use `show d.w Ω (z ≫ a) * c.w Ω (z ≫ b) = c.w Ω s * d.w Ω (z ≫ a)`. Rewrite using `[hz'.2, mul_comm]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.cycComp_of :
    FibFin → CycComp := by
  classical
  intro hF S Y X c d e a b pb hp hf hw Ω _ _ x y
  haveI := c.fin
  haveI := d.fin
  haveI := e.fin
  let A := (hF c.p Ω x).toFinset
  have hAm : ∀ s, s ∈ A ↔ s ≫ c.p = x := fun s => by simp [A, fib]
  let B : (gp Ω ⟶ Y) → Finset (gp Ω ⟶ d.Z) := fun t => (hF d.p Ω t).toFinset
  have hBm : ∀ t u, u ∈ B t ↔ u ≫ d.p = t := fun t u => by simp [B, fib]
  let E := (hF e.p Ω x).toFinset
  have hEm : ∀ z, z ∈ E ↔ z ≫ e.p = x := fun z => by simp [E, fib]
  have hR : (∑ᶠ t : gp Ω ⟶ Y, c.cyc Ω x t * d.cyc Ω t y) =
      ∑ s ∈ A, c.w Ω s * d.cyc Ω (s ≫ c.f) y := by
    rw [finsum_eq_sum_of_support_subset (s := A.image (· ≫ c.f))]
    · rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := A.image (· ≫ c.f)) (g := (· ≫ c.f))
          (fun s hs => Finset.mem_image_of_mem _ hs)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [(Finset.mem_filter.1 hs).2]
    · intro t ht
      rw [Function.mem_support] at ht
      by_contra hn
      apply ht
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_eq_zero, zero_mul]
      intro s hs
      exact absurd (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨s, (Finset.mem_filter.1 hs).1, (Finset.mem_filter.1 hs).2⟩)) hn
  have hmaps : ∀ z ∈ E.filter (fun z => z ≫ e.f = y), z ≫ b ∈ A := by
    intro z hz
    rw [hAm, Category.assoc, ← hp]
    exact (hEm z).1 (Finset.mem_filter.1 hz).1
  rw [hR, cyc_eq_sum e Ω x y E hEm, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [cyc_eq_sum d Ω (s ≫ c.f) y (B (s ≫ c.f)) (hBm _), Finset.mul_sum]
  refine Finset.sum_bij' (fun z _ => z ≫ a)
    (fun u hu => pb.lift u s ((hBm _ u).1 (Finset.mem_filter.1 hu).1)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, hEm, hBm] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pb.w, ← Category.assoc, hz.2]
    · rw [Category.assoc, ← hf, hz.1.2]
  · intro u hu
    have hu' := Finset.mem_filter.1 hu
    simp only [Finset.mem_filter, hEm]
    refine ⟨⟨?_, ?_⟩, pb.lift_snd _ _ _⟩
    · rw [hp, ← Category.assoc, pb.lift_snd]
      exact (hAm s).1 hs
    · rw [hf, ← Category.assoc, pb.lift_fst]
      exact hu'.2
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    apply pb.hom_ext
    · rw [pb.lift_fst]
    · rw [pb.lift_snd, hz'.2]
  · intro u hu
    exact pb.lift_fst _ _ _
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    rw [hw]
    show d.w Ω (z ≫ a) * c.w Ω (z ≫ b) = c.w Ω s * d.w Ω (z ≫ a)
    rw [hz'.2, mul_comm]
