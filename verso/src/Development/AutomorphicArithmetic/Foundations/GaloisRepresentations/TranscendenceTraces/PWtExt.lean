import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Rewrite using `[finsum_eq_single (fun x => ∑ᶠ (_ : x ∈ s), f x) a]`. Simplify using `[ha]`. Introduce `x hx`. Distinguish the cases in `hs : x ∈ s`. Establish `h0 : f x = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `hx (h x hs h0)`. Simplify using `[h0]`. Simplify using `[hs]`.
-/
private theorem fsum_single {α : Type*} (s : Set α) (f : α → ℤ) (a : α) (ha : a ∈ s)
    (h : ∀ x ∈ s, f x ≠ 0 → x = a) : ∑ᶠ x ∈ s, f x = f a := by
  classical
  rw [finsum_eq_single (fun x => ∑ᶠ (_ : x ∈ s), f x) a]
  · simp [ha]
  · intro x hx
    by_cases hs : x ∈ s
    · have h0 : f x = 0 := by
        by_contra h0
        exact hx (h x hs h0)
      simp [h0]
    · simp [hs]

/- English proof (translation)
Take `⟨B, _, _, v, hfin, hpb⟩` from `hChart r Ω (𝟙 _)`. Use `haveI : IsIso v := hpb.isIso_fst_of_isIso`. Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B`. Use `haveI : DiscreteTopology (Spec (CommRingCat.of B)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum B))`. Conclude with `(Scheme.homeoOfIso (asIso v)).symm.isEmbedding.discreteTopology`.
-/
private theorem discrete_of_chart (hChart : Chart) {V : Scheme.{0}} (Ω : Type) [Field Ω] (r : V ⟶ gp Ω) [IsFinite r] :
    DiscreteTopology V := by
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hChart r Ω (𝟙 _)
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : DiscreteTopology (Spec (CommRingCat.of B)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum B))
  exact (Scheme.homeoOfIso (asIso v)).symm.isEmbedding.discreteTopology

/- English proof (translation)
Introduce `hOne hChart Z S p _ w hw Ω L _ _ _ _ z a`. Use `haveI hr : IsFinite (pullback.snd p (z ≫ p)) := Sq.finite (Sq.of p (z ≫ p))`. Use `haveI := discrete_of_chart hChart Ω (pullback.snd p (z ≫ p))`. Set `z0 : gp Ω ⟶ pullback p (z ≫ p)` to `pullback.lift z (𝟙 _) (by simp)`. Establish `hf : z0 ≫ pullback.fst p (z ≫ p) = z` using `pullback.lift_fst _ _ _`.

Establish `hs : z0 ≫ pullback.snd p (z ≫ p) = 𝟙 _` using `pullback.lift_snd _ _ _`. Set `φ : (pullback p (z ≫ p) : Scheme.{0}) → ℤ` to `fun y => if y = pt z0 then 1 else 0`. Take `⟨ψ, -, hψ⟩` from `hw (Sq.of p (z ≫ p)) φ (IsLocallyConstant.of_discrete φ)`. Establish `h1 : ψ (pt (𝟙 (gp Ω))) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)), w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y)` using `hψ Ω (𝟙 _)`. Establish `h2 : ψ (pt a) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a, w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y)` using `hψ L a`.

Establish `hpt : pt (a ≫ z0) = pt z0` using `by rw [pt_comp, pt_eq]`. Establish `hφ : φ (pt z0) = 1` using `if_pos rfl`. Establish `hne : ∀ y : (pullback p (z ≫ p) : Scheme.{0}), φ y ≠ 0 → y = pt z0`. Introduce `y hy`. Assume the negation of the conclusion as `h`.

Conclude with `hy (if_neg h)`. Establish `e1 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)), w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w Ω z`. Rewrite using `[fsum_single _ _ z0 hs, hf, hφ, mul_one]`. Introduce `y hy h0`. Conclude with `hOne Ω (pullback.snd p (z ≫ p)) Ω (𝟙 _) y z0 hy hs (hne _ (right_ne_zero_of_mul h0))`.

Establish `hs' : (a ≫ z0) ≫ pullback.snd p (z ≫ p) = a`. Rewrite using `[Category.assoc, hs, Category.comp_id]`. Establish `e2 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a, w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w L (a ≫ z)`. Rewrite using `[fsum_single _ _ (a ≫ z0) hs', Category.assoc, hf, hpt, hφ, mul_one]`. Introduce `y hy h0`.

Conclude with `hOne Ω (pullback.snd p (z ≫ p)) L a y (a ≫ z0) hy hs' ((hne _ (right_ne_zero_of_mul h0)).trans hpt.symm)`. Establish `hU : pt a = pt (𝟙 (gp Ω))` using `Subsingleton.elim (α := PrimeSpectrum Ω) _ _`. Rewrite using `[← e2, ← e1, ← h2, ← h1]`. Conclude with `congrArg ψ hU`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtExt_of :
    PtOne → Chart → WtExt := by
  intro hOne hChart Z S p _ w hw Ω L _ _ _ _ z a
  classical
  haveI hr : IsFinite (pullback.snd p (z ≫ p)) := Sq.finite (Sq.of p (z ≫ p))
  haveI := discrete_of_chart hChart Ω (pullback.snd p (z ≫ p))
  let z0 : gp Ω ⟶ pullback p (z ≫ p) := pullback.lift z (𝟙 _) (by simp)
  have hf : z0 ≫ pullback.fst p (z ≫ p) = z := pullback.lift_fst _ _ _
  have hs : z0 ≫ pullback.snd p (z ≫ p) = 𝟙 _ := pullback.lift_snd _ _ _
  let φ : (pullback p (z ≫ p) : Scheme.{0}) → ℤ := fun y => if y = pt z0 then 1 else 0
  obtain ⟨ψ, -, hψ⟩ := hw (Sq.of p (z ≫ p)) φ (IsLocallyConstant.of_discrete φ)
  have h1 : ψ (pt (𝟙 (gp Ω))) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)),
      w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) := hψ Ω (𝟙 _)
  have h2 : ψ (pt a) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a,
      w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) := hψ L a
  have hpt : pt (a ≫ z0) = pt z0 := by rw [pt_comp, pt_eq]
  have hφ : φ (pt z0) = 1 := if_pos rfl
  have hne : ∀ y : (pullback p (z ≫ p) : Scheme.{0}), φ y ≠ 0 → y = pt z0 := by
    intro y hy
    by_contra h
    exact hy (if_neg h)
  have e1 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)),
      w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w Ω z := by
    rw [fsum_single _ _ z0 hs, hf, hφ, mul_one]
    intro y hy h0
    exact hOne Ω (pullback.snd p (z ≫ p)) Ω (𝟙 _) y z0 hy hs (hne _ (right_ne_zero_of_mul h0))
  have hs' : (a ≫ z0) ≫ pullback.snd p (z ≫ p) = a := by
    rw [Category.assoc, hs, Category.comp_id]
  have e2 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a,
      w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w L (a ≫ z) := by
    rw [fsum_single _ _ (a ≫ z0) hs', Category.assoc, hf, hpt, hφ, mul_one]
    intro y hy h0
    exact hOne Ω (pullback.snd p (z ≫ p)) L a y (a ≫ z0) hy hs'
      ((hne _ (right_ne_zero_of_mul h0)).trans hpt.symm)
  have hU : pt a = pt (𝟙 (gp Ω)) := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  rw [← e2, ← e1, ← h2, ← h1]
  exact congrArg ψ hU
