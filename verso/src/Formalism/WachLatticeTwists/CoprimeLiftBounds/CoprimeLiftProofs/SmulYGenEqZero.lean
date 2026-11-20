import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.ImportsAlt

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

section SlopeTestRemainingChoices
variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

def cobZ (ρ : Representation O G M) (v : M) : coZ1s ρ :=
  ⟨coD0 ρ v, fun g h => by
    show ρ (g * h) v - v = (ρ g v - v) + ρ g (ρ h v - v)
    rw [map_mul, map_sub, Module.End.mul_apply]; abel⟩

/- English proof (translation)
Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `LinearMap.mem_range_self (coD0 ρ) v`.
-/
lemma mkQ_cobZ (ρ : Representation O G M) (v : M) :
    (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype) (cobZ ρ v) : H1z ρ) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self (coD0 ρ) v

/- English proof (translation)
Establish `hz : z = cobZ ρ v` using `Subtype.ext (funext h)`. Rewrite using `[hz]`. Conclude with `mkQ_cobZ ρ v`.
-/
lemma mkQ_eq_zero_of (ρ : Representation O G M) (z : coZ1s ρ) (v : M)
    (h : ∀ g, (z : G → M) g = ρ g v - v) :
    (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype) z : H1z ρ) = 0 := by
  have hz : z = cobZ ρ v := Subtype.ext (funext h)
  rw [hz]
  exact mkQ_cobZ ρ v

end SlopeTestRemainingChoices

section Y
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]

/- English proof (translation)
Use `show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = _`. Rewrite using `[sub_mul, sub_mul, smul_sub, one_mul, smul_mul_assoc, Algebra.smul_def (((χ g)⁻¹ : T'ˣ) : T') (algebraMap T' A ((χ g : T'ˣ) : T') * E), ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]`.
-/
lemma ycoc_eq (r : G →* A) (χ : G →* T'ˣ) (E : A) (g : G) :
    ycoc r χ E g =
      (((χ g)⁻¹ : T'ˣ) : T') • ((r g - algebraMap T' A ((χ g : T'ˣ) : T')) * E) := by
  show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = _
  rw [sub_mul, sub_mul, smul_sub, one_mul, smul_mul_assoc,
    Algebra.smul_def (((χ g)⁻¹ : T'ˣ) : T') (algebraMap T' A ((χ g : T'ˣ) : T') * E), ← mul_assoc,
    ← map_mul, Units.inv_mul, map_one, one_mul]

/- English proof (translation)
Unfold `yGen`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Conclude with `Prod.ext (Subtype.ext h) (smul_zero _)`.
-/
lemma smul_yGen_eq_zero (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) (a : A) (g : G)
    (h : a * ycoc r χ E g = 0) : a • yGen r χ E e₁ δ D j Kc k0 g = 0 := by
  unfold yGen
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  convert Submodule.zero_mem _ using 1
  exact Prod.ext (Subtype.ext h) (smul_zero _)

end Y

/- English proof (translation)
Introduce `A T' G _ _ _ _ r χ E γ ζ h hζ`. Rewrite using `[ycoc_eq, mul_smul_comm, hζ, ← mul_assoc, h, zero_mul, smul_zero]`.
-/
theorem qAlg : StatQAlg := by
  intro A T' G _ _ _ _ r χ E γ ζ h hζ
  rw [ycoc_eq, mul_smul_comm, hζ, ← mul_assoc, h, zero_mul, smul_zero]

/- English proof (translation)
Introduce `O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 he hE hk φ l`. Take `⟨_, hsig, _, hy⟩` from `rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l`. Establish `hs : ∀ a, φ (sigGen r χ E e₁ δ D j Kc k0 l a) = 0` using `fun a => by rw [← hsig a, he]`. Use `show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) = (0 : H1z (resRep (uRep O (M := M) r χ) (D l)))`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Use `show ((restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) : coZ1s (resRep (uRep O (M := M) r χ) (D l))) : D l → M) ∈ LinearMap.range (coD0 (resRep (uRep O (M := M) r χ) (D l)))`. Rewrite using `[LinearMap.mem_range]`. Use `⟨-φ (nuGen r χ E e₁ δ D j Kc k0 l), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Use `show uElt r χ (g : G) • -φ (nuGen r χ E e₁ δ D j Kc k0 l) - -φ (nuGen r χ E e₁ δ D j Kc k0 l) = φ (yGen r χ E e₁ δ D j Kc k0 (g : G))`.

Take `⟨a0, ha0⟩` from `hk l g`. Establish `h` using `hy g g.2`. Simplify using `only [hs, smul_zero, Finset.sum_const_zero, zero_add, ha0, mul_smul, hE] at h`. Rewrite using `[eq_neg_of_add_eq_zero_left h, smul_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem colChiC : StatColChiC := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 he hE hk φ l
  obtain ⟨_, hsig, _, hy⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  have hs : ∀ a, φ (sigGen r χ E e₁ δ D j Kc k0 l a) = 0 := fun a => by rw [← hsig a, he]
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) (D l)
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) (D l)))
  rw [Submodule.Quotient.mk_eq_zero]
  show ((restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) :
      coZ1s (resRep (uRep O (M := M) r χ) (D l))) : D l → M) ∈
    LinearMap.range (coD0 (resRep (uRep O (M := M) r χ) (D l)))
  rw [LinearMap.mem_range]
  refine ⟨-φ (nuGen r χ E e₁ δ D j Kc k0 l), ?_⟩
  funext g
  show uElt r χ (g : G) • -φ (nuGen r χ E e₁ δ D j Kc k0 l) - -φ (nuGen r χ E e₁ δ D j Kc k0 l) =
    φ (yGen r χ E e₁ δ D j Kc k0 (g : G))
  obtain ⟨a0, ha0⟩ := hk l g
  have h := hy g g.2
  simp only [hs, smul_zero, Finset.sum_const_zero, zero_add, ha0, mul_smul, hE] at h
  rw [eq_neg_of_add_eq_zero_left h, smul_neg]
  abel

/- English proof (translation)
Introduce `O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 ℓ e' u hu he hE hδ hk φ l`. Take `⟨hnu, hsig, _, hy⟩` from `rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l`. Establish `hs : ∀ a, φ (sigGen r χ E e₁ δ D j Kc k0 l a) = 0` using `fun a => by rw [← hsig a, he]`. Establish `h2 : ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) = (δO * δO * (ℓ : O) ^ e' l * u l g) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l)`. Introduce `g hg`.

Establish `h` using `hy g hg`. Simplify using `only [hs, smul_zero, Finset.sum_const_zero, zero_add, hu, sub_self, add_zero, hk l g hg, hδ] at h`. Rewrite using `[h, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨by rw [← hE]; exact hnu, h2, fun I hI => ?_⟩` and prove the remaining obligations. Apply `LinearMap.mem_ker.mpr` to reduce the goal to its premises. Use `show Submodule.Quotient.mk (restrictCocycles1 (resRep (uRep O (M := M) r χ) (D l)) I (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ))) = (0 : H1z (resRep (resRep (uRep O (M := M) r χ) (D l)) I))`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Establish `hz : restrictCocycles1 (resRep (uRep O (M` using `M) r χ) (D l)) I (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) = 0 := by`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show φ (yGen r χ E e₁ δ D j Kc k0 ((g : D l) : G)) = 0`. Rewrite using `[h2 _ (g : D l).2, hI g g.2, mul_zero, zero_smul]`. Rewrite using `[hz]`.

Conclude with `Submodule.zero_mem _`.
-/
theorem colChiOne : StatColChiOne := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 ℓ e' u hu he hE hδ hk φ l
  obtain ⟨hnu, hsig, _, hy⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  have hs : ∀ a, φ (sigGen r χ E e₁ δ D j Kc k0 l a) = 0 := fun a => by rw [← hsig a, he]
  have h2 : ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) =
      (δO * δO * (ℓ : O) ^ e' l * u l g) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l) := by
    intro g hg
    have h := hy g hg
    simp only [hs, smul_zero, Finset.sum_const_zero, zero_add, hu, sub_self, add_zero, hk l g hg,
      hδ] at h
    rw [h, smul_smul]
    congr 1
    ring
  refine ⟨by rw [← hE]; exact hnu, h2, fun I hI => ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (resRep (uRep O (M := M) r χ) (D l)) I
      (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ))) =
    (0 : H1z (resRep (resRep (uRep O (M := M) r χ) (D l)) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (resRep (uRep O (M := M) r χ) (D l)) I
      (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 ((g : D l) : G)) = 0
    rw [h2 _ (g : D l).2, hI g g.2, mul_zero, zero_smul]
  rw [hz]
  exact Submodule.zero_mem _

/- English proof (translation)
Introduce `O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 I hI`. Establish `hy : ∀ g ∈ I, ycoc r χ E g = 0`. Introduce `g hg`. Take `⟨h1, h2⟩` from `hI g hg`. Use `show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = 0`.

Rewrite using `[h1, h2, inv_one, Units.val_one, one_smul, sub_self, zero_mul]`. Use `⟨hy, fun φ => ?_⟩` and prove the remaining obligations. Apply `LinearMap.mem_ker.mpr` to reduce the goal to its premises. Use `show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) = (0 : H1z (resRep (uRep O (M := M) r χ) I))`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Establish `hz : restrictCocycles1 (uRep O (M` using `M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) = 0 := by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show φ (yGen r χ E e₁ δ D j Kc k0 (g : G)) = 0`. Establish `h0` using `smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 (1 : A) (g : G) (by rw [one_mul]; exact hy g g.2)`.

Rewrite `h0` using `[one_smul]`. Rewrite using `[h0, map_zero]`. Rewrite using `[hz]`. Conclude with `Submodule.zero_mem _`.
-/
theorem unrOutside : StatUnrOutside := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 I hI
  have hy : ∀ g ∈ I, ycoc r χ E g = 0 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hI g hg
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = 0
    rw [h1, h2, inv_one, Units.val_one, one_smul, sub_self, zero_mul]
  refine ⟨hy, fun φ => ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) I
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (uRep O (M := M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 (g : G)) = 0
    have h0 := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 (1 : A) (g : G)
      (by rw [one_mul]; exact hy g g.2)
    rw [one_smul] at h0
    rw [h0, map_zero]
  rw [hz]
  exact Submodule.zero_mem _

/- English proof (translation)
Introduce `O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 I hI φ`. Establish `hy0 : ∀ g ∈ I, φ (yGen r χ E e₁ δ D j Kc k0 g) = 0`. Introduce `g hg`. Take `⟨a, ha, hinj⟩` from `hI g hg`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← map_smul, smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 a g (by rw [ycoc_eq, mul_smul_comm, ha, smul_zero]), map_zero]`. Use `⟨hy0, ?_⟩` and prove the remaining obligations. Apply `LinearMap.mem_ker.mpr` to reduce the goal to its premises. Use `show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) = (0 : H1z (resRep (uRep O (M := M) r χ) I))`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Establish `hz : restrictCocycles1 (uRep O (M` using `M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) = 0 := by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show φ (yGen r χ E e₁ δ D j Kc k0 (g : G)) = 0`. Conclude with `hy0 g g.2`.

Rewrite using `[hz]`. Conclude with `Submodule.zero_mem _`.
-/
theorem unrS : StatUnrS := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 I hI φ
  have hy0 : ∀ g ∈ I, φ (yGen r χ E e₁ δ D j Kc k0 g) = 0 := by
    intro g hg
    obtain ⟨a, ha, hinj⟩ := hI g hg
    apply hinj
    rw [← map_smul, smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 a g
      (by rw [ycoc_eq, mul_smul_comm, ha, smul_zero]), map_zero]
  refine ⟨hy0, ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) I
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (uRep O (M := M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 (g : G)) = 0
    exact hy0 g g.2
  rw [hz]
  exact Submodule.zero_mem _

end Formalism.RepresentationBoundsCohomology.BR
