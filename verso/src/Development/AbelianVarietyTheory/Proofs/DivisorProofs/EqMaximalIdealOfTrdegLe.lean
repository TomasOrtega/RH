import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hle : p ≤ maximalIdeal A` using `le_maximalIdeal hp.ne_top`. Choose the witnesses or unpack the hypotheses as in `⟨a, ham, hap⟩ : ∃ a ∈ maximalIdeal A, a ∉ p := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hne (le_antisymm hle h)`. Use `haveI := hA`. Use `haveI : Algebra.EssFiniteType F (ResidueField A) := Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom F A (ResidueField A)) (IsLocalRing.residue_surjective)`. Take `⟨s, hs⟩` from `exists_isTranscendenceBasis F (ResidueField A)`. Use `haveI : Finite s := finite_of_isTranscendenceBasis hs`.

Set `f : A ⧸ p →ₐ[F] ResidueField A` to `Ideal.Quotient.liftₐ p (IsScalarTower.toAlgHom F A (ResidueField A)) (fun x hx => by`. Simplify `hle hx)` using `[IsLocalRing.residue_eq_zero_iff]`. Establish `hfmk : ∀ x : A, f (Ideal.Quotient.mk p x) = IsLocalRing.residue A x` using `fun x => rfl`. Use `choose y hy using fun i : s => IsLocalRing.residue_surjective (R := A) i.1`. Set `z : s → A ⧸ p` to `fun i => Ideal.Quotient.mk p (y i)`.

Establish `hfz : f ∘ z = ((↑) : s → ResidueField A)`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, z, hfmk, hy]`. Establish `hz : AlgebraicIndependent F z`. Establish `h1` using `hs.1`.

Rewrite `h1` using `[← hfz]`. Conclude with `h1.of_comp f`. Use `set b : A ⧸ p := Ideal.Quotient.mk p a with hbdef`. Establish `hb0 : b ≠ 0`. Rewrite using `[hbdef, Ne, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hap`. Establish `hbk : b ∈ RingHom.ker f.toRingHom`. Rewrite using `[RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `f (Ideal.Quotient.mk p a) = 0`. Rewrite using `[hfmk, IsLocalRing.residue_eq_zero_iff]`.

Conclude with `ham`. Establish `hinj` using `algebraicIndependent_iff_injective_aeval.mp hs.1`. Establish `htrans : Transcendental (Algebra.adjoin F (Set.range z)) b`. Introduce `halg`. Apply `Ideal.comap_ne_bot_of_algebraic_mem hb0 hbk halg` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `c hc`. Rewrite `hc` using `[Ideal.mem_comap, RingHom.mem_ker]`. Establish `hc2 : (c : A ⧸ p) ∈ (MvPolynomial.aeval (R` using `F) z).range := by`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval]`.

Conclude with `c.2`. Take `⟨g, hg⟩` from `hc2`. Establish `h0 : MvPolynomial.aeval ((↑) : s → ResidueField A) g = 0`. Rewrite using `[← hfz]`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval (fun i => f (z i)) g = 0`.

Rewrite using `[← MvPolynomial.comp_aeval_apply]`. Express the relevant statement in the definitionally equal form `f ((MvPolynomial.aeval z).toRingHom g) = 0`. Rewrite using `[hg]`. Conclude with `hc`. Establish `hg0 : g = 0` using `hinj (by rw [h0, map_zero])`.

Rewrite using `[Ideal.mem_bot]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hg, hg0, map_zero]`. Both sides reduce to the same expression. Establish `hopt : AlgebraicIndependent F (fun o : Option s => o.elim b z)` using `AlgebraicIndependent.option_iff.mpr ⟨hz, htrans⟩`.

Establish `hopt'` using `hopt.map' (f := IsScalarTower.toAlgHom F (A ⧸ p) (FractionRing (A ⧸ p))) (IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p)))`. Establish `hc1` using `hopt'.cardinalMk_le_trdeg`. Rewrite `htr` using `[← hs.cardinalMk_eq_trdeg]`. Establish `hle2 : Cardinal.mk (Option s) ≤ Cardinal.mk s` using `hc1.trans htr`. Take `⟨e⟩` from `Cardinal.le_def _ _ |>.mp hle2`.

Use `haveI := Fintype.ofFinite s`. Use `Fintype.card_le_of_embedding e` as an intermediate fact. Rewrite `this` using `[Fintype.card_option]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_maximalIdeal_of_trdeg_le (F A : Type) [Field F] [CommRing A] [IsDomain A]
    [IsLocalRing A] [Algebra F A] (hA : Algebra.EssFiniteType F A) (p : Ideal A)
    (hp : p.IsPrime)
    (htr : Algebra.trdeg F (FractionRing (A ⧸ p)) ≤ Algebra.trdeg F (ResidueField A)) :
    p = maximalIdeal A := by
  classical
  by_contra hne
  have hle : p ≤ maximalIdeal A := le_maximalIdeal hp.ne_top
  obtain ⟨a, ham, hap⟩ : ∃ a ∈ maximalIdeal A, a ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  haveI := hA
  haveI : Algebra.EssFiniteType F (ResidueField A) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom F A (ResidueField A))
      (IsLocalRing.residue_surjective)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (ResidueField A)
  haveI : Finite s := finite_of_isTranscendenceBasis hs
  let f : A ⧸ p →ₐ[F] ResidueField A :=
    Ideal.Quotient.liftₐ p (IsScalarTower.toAlgHom F A (ResidueField A)) (fun x hx => by
      simpa [IsLocalRing.residue_eq_zero_iff] using hle hx)
  have hfmk : ∀ x : A, f (Ideal.Quotient.mk p x) = IsLocalRing.residue A x := fun x => rfl
  choose y hy using fun i : s => IsLocalRing.residue_surjective (R := A) i.1
  let z : s → A ⧸ p := fun i => Ideal.Quotient.mk p (y i)
  have hfz : f ∘ z = ((↑) : s → ResidueField A) := by
    funext i
    simp only [Function.comp_apply, z, hfmk, hy]
  have hz : AlgebraicIndependent F z := by
    have h1 := hs.1
    rw [← hfz] at h1
    exact h1.of_comp f
  set b : A ⧸ p := Ideal.Quotient.mk p a with hbdef
  have hb0 : b ≠ 0 := by
    rw [hbdef, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hap
  have hbk : b ∈ RingHom.ker f.toRingHom := by
    rw [RingHom.mem_ker]
    change f (Ideal.Quotient.mk p a) = 0
    rw [hfmk, IsLocalRing.residue_eq_zero_iff]
    exact ham
  have hinj := algebraicIndependent_iff_injective_aeval.mp hs.1
  have htrans : Transcendental (Algebra.adjoin F (Set.range z)) b := by
    intro halg
    apply Ideal.comap_ne_bot_of_algebraic_mem hb0 hbk halg
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker] at hc
    have hc2 : (c : A ⧸ p) ∈ (MvPolynomial.aeval (R := F) z).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨g, hg⟩ := hc2
    have h0 : MvPolynomial.aeval ((↑) : s → ResidueField A) g = 0 := by
      rw [← hfz]
      change MvPolynomial.aeval (fun i => f (z i)) g = 0
      rw [← MvPolynomial.comp_aeval_apply]
      change f ((MvPolynomial.aeval z).toRingHom g) = 0
      rw [hg]
      exact hc
    have hg0 : g = 0 := hinj (by rw [h0, map_zero])
    rw [Ideal.mem_bot]
    apply Subtype.ext
    rw [← hg, hg0, map_zero]
    rfl
  have hopt : AlgebraicIndependent F (fun o : Option s => o.elim b z) :=
    AlgebraicIndependent.option_iff.mpr ⟨hz, htrans⟩
  have hopt' := hopt.map' (f := IsScalarTower.toAlgHom F (A ⧸ p) (FractionRing (A ⧸ p)))
    (IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p)))
  have hc1 := hopt'.cardinalMk_le_trdeg
  rw [← hs.cardinalMk_eq_trdeg] at htr
  have hle2 : Cardinal.mk (Option s) ≤ Cardinal.mk s := hc1.trans htr
  obtain ⟨e⟩ := Cardinal.le_def _ _ |>.mp hle2
  haveI := Fintype.ofFinite s
  have := Fintype.card_le_of_embedding e
  rw [Fintype.card_option] at this
  omega

end GlobalTheory
