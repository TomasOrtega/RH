import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.AvgRes

/- English proof (translation)
Use `haveI : Fintype (G ⧸ N) := Fintype.ofFinite _`. Use `set φ : G ⧸ N →* H := QuotientGroup.lift N r hN with hφdef`. Establish `hφ : Function.Surjective φ`. Introduce `h`. Take `⟨g, rfl⟩` from `hr h`.

Conclude with `⟨(g : G ⧸ N), QuotientGroup.lift_mk N hN g⟩`. Use `haveI : Finite H := Finite.of_surjective φ hφ`. Use `haveI : Fintype H := Fintype.ofFinite _`. Establish `hout : ∀ u : G ⧸ N, r (Quotient.out u) = φ u`. Introduce `u`.

Use `conv_rhs => rw [← Quotient.out_eq u]`. Conclude with `(QuotientGroup.lift_mk N hN _).symm`. Repeatedly rewrite using `[hout]`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_comp f φ, Finset.image_univ_of_surjective hφ]`. Use `set c := (Finset.univ.filter fun u : G ⧸ N => φ u = 1).card with hc`.

Establish `hfib : ∀ b : H, (Finset.univ.filter fun u : G ⧸ N => φ u = b).card = c` using `fun b => MonoidHom.card_fiber_eq_of_mem_range φ (hφ b) (hφ 1)`. Establish `hcard : Fintype.card (G ⧸ N) = Fintype.card H * c`. Rewrite using `[← Finset.card_univ, Finset.card_eq_sum_card_image φ Finset.univ, Finset.image_univ_of_surjective hφ]`. Simplify using `[hfib]`. Establish `hc0 : (c : ℂ) ≠ 0`.

Rewrite using `[hc]`. Conclude with `Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, by simp⟩)`. Establish `hH : (Fintype.card H : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Repeatedly rewrite using `[hfib]`. Rewrite using `[← Finset.smul_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem avg_of_surjective {G H : Type*} [Group G] [Group H] (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] (r : G →* H)
    (hr : Function.Surjective r) (hN : N ≤ r.ker) (f : H → ℂ) :
    (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, f (r (Quotient.out u)) = (∑ᶠ g, f g) / (Nat.card H : ℂ) := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set φ : G ⧸ N →* H := QuotientGroup.lift N r hN with hφdef
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨g, rfl⟩ := hr h
    exact ⟨(g : G ⧸ N), QuotientGroup.lift_mk N hN g⟩
  haveI : Finite H := Finite.of_surjective φ hφ
  haveI : Fintype H := Fintype.ofFinite _
  have hout : ∀ u : G ⧸ N, r (Quotient.out u) = φ u := by
    intro u
    conv_rhs => rw [← Quotient.out_eq u]
    exact (QuotientGroup.lift_mk N hN _).symm
  simp_rw [hout]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_comp f φ,
    Finset.image_univ_of_surjective hφ]
  set c := (Finset.univ.filter fun u : G ⧸ N => φ u = 1).card with hc
  have hfib : ∀ b : H, (Finset.univ.filter fun u : G ⧸ N => φ u = b).card = c := fun b =>
    MonoidHom.card_fiber_eq_of_mem_range φ (hφ b) (hφ 1)
  have hcard : Fintype.card (G ⧸ N) = Fintype.card H * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_image φ Finset.univ,
      Finset.image_univ_of_surjective hφ]
    simp [hfib]
  have hc0 : (c : ℂ) ≠ 0 := by
    rw [hc]
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, by simp⟩)
  have hH : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp_rw [hfib]
  rw [← Finset.smul_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard,
    nsmul_eq_mul]
  push_cast
  field_simp

variable {O : Type} [CommRing O] [IsLocalRing O]

/- English proof (translation)
Introduce `M`. Establish `hs` using `IsLocalRing.residue_surjective (R := O)`. Set `A : Matrix (Ix n) (Ix n) O` to `(M : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)).map (Function.surjInv hs)`. Establish `hA : (IsLocalRing.residue O).mapMatrix A = (M : Matrix (Ix n) (Ix n) _)`. Use extensionality with `i j`.

Conclude with `Function.surjInv_eq hs _`. Establish `hdet : IsUnit A.det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hA]`. Conclude with `(Matrix.isUnits_det_units M).ne_zero`. Use `⟨Matrix.nonsingInvUnit A hdet, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Conclude with `Function.surjInv_eq hs _`.
-/
theorem resK_surjective (n : ℕ) : Function.Surjective (resK (n := n) (O := O)) := by
  intro M
  classical
  have hs := IsLocalRing.residue_surjective (R := O)
  let A : Matrix (Ix n) (Ix n) O :=
    (M : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)).map (Function.surjInv hs)
  have hA : (IsLocalRing.residue O).mapMatrix A = (M : Matrix (Ix n) (Ix n) _) := by
    ext i j
    exact Function.surjInv_eq hs _
  have hdet : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hA]
    exact (Matrix.isUnits_det_units M).ne_zero
  refine ⟨Matrix.nonsingInvUnit A hdet, ?_⟩
  ext i j
  exact Function.surjInv_eq hs _

/- English proof (translation)
Introduce `g hg`. Establish `hg'` using `MonoidHom.mem_ker.mp hg`. Rewrite using `[MonoidHom.mem_ker]`. Establish `hle : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O` using `Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_of_mem _ hϖ 2 two_pos))`. Use extensionality with `i j`.

Establish `h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((g : Matrix (Ix n) (Ix n) O) i j) = Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 : Matrix (Ix n) (Ix n) O) i j)`. Establish `h0` using `congrArg (fun x : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => (x : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j) hg'`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ ((g : Matrix (Ix n) (Ix n) O) i j) = (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j at h0`. Rewrite using `[h0, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h2` using `Ideal.Quotient.eq.mpr (hle (Ideal.Quotient.eq.mp h1))`. Express the relevant statement in the definitionally equal form `IsLocalRing.residue O ((g : Matrix (Ix n) (Ix n) O) i j) = (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j`. Rewrite using `[show (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j = IsLocalRing.residue O ((1 : Matrix (Ix n) (Ix n) O) i j) by`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp]`.

Conclude with `h2`.
-/
theorem level_square_congruence_le_reduction_ker (n : ℕ) {ϖ : O} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal O) :
    Gam2 (n := n) ϖ ≤ (resK (n := n) (O := O)).ker := by
  intro g hg
  have hg' := MonoidHom.mem_ker.mp hg
  rw [MonoidHom.mem_ker]
  have hle : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_of_mem _ hϖ 2 two_pos))
  ext i j
  have h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((g : Matrix (Ix n) (Ix n) O) i j) =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 : Matrix (Ix n) (Ix n) O) i j) := by
    have h0 := congrArg
      (fun x : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => (x : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j) hg'
    change Ideal.Quotient.mk _ ((g : Matrix (Ix n) (Ix n) O) i j) =
      (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) i j at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 := Ideal.Quotient.eq.mpr (hle (Ideal.Quotient.eq.mp h1))
  change IsLocalRing.residue O ((g : Matrix (Ix n) (Ix n) O) i j) =
    (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j
  rw [show (1 : Matrix (Ix n) (Ix n) (IsLocalRing.ResidueField O)) i j =
      IsLocalRing.residue O ((1 : Matrix (Ix n) (Ix n) O) i j) by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp]
  exact h2

/- English proof (translation)
Introduce `O _ _ _ _ n ϖ hϖ f`. Establish `hm : ϖ ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit`. Use `haveI : (Gam2 (n := n) ϖ).Normal := MonoidHom.normal_ker _`. Use `haveI : Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := GlobalTheory.CompanionTheory.Jp.Unif.finite_quotient_level_square_congruence n hϖ`. Conclude with `avg_of_surjective (Gam2 ϖ) resK (resK_surjective n) (level_square_congruence_le_reduction_ker n hm) f`.
-/
theorem avgK_res : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
  intro O _ _ _ _ n ϖ hϖ f
  have hm : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  haveI : (Gam2 (n := n) ϖ).Normal := MonoidHom.normal_ker _
  haveI : Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := GlobalTheory.CompanionTheory.Jp.Unif.finite_quotient_level_square_congruence n hϖ
  exact avg_of_surjective (Gam2 ϖ) resK (resK_surjective n) (level_square_congruence_le_reduction_ker n hm) f

end GlobalTheory.CompanionTheory.Jp.AvgRes

end
