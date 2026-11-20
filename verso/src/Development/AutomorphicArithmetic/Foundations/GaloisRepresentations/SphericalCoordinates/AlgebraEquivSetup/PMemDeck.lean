import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

/- English proof (translation)
Introduce `hSum hCen X M _ _ T K hT k hk hnorm`. Establish `hconj : ∀ a ∈ T.K₀, ∀ u ∈ T.K₀, a * u * a⁻¹ ∈ T.K₀` using `fun a ha u hu => T.K₀.mul_mem (T.K₀.mul_mem ha hu) (T.K₀.inv_mem ha)`. Establish `hmem` using `hSum X T.K₀ T.K₀ T.K₀ k le_rfl (by simp) hconj (fun a ha u hu => by`. Establish `h1` using `hnorm (a * u * a⁻¹) (hconj a ha u hu)`. Simplify `h1)` using `[mul_assoc, _root_.mul_inv_rev]`.

Use `⟨hmem.1, map_one _, ?_⟩` and prove the remaining obligations. Introduce `V _ _ Φ hΦ`. Use function extensionality and compare the values at `g`. Establish `hc : T.Cen 1` using `⟨fun g => by simp, map_one _⟩`. Rewrite using `[one_smul, hCen X M T 1 hc V Φ hΦ g, mul_one]`.

Establish `hinv0 : ∀ k' ∈ T.K₀, ∀ g, Φ (g * k') = Φ g` using `fun k' hk' g => by`. Rewrite using `[hΦ k' (T.le hk') g, T.ker k' hk' _]`. Simplify using the standard rewrite rules. Rewrite using `[hmem.2.2 V Φ hinv0 g]`. Establish `hall : ∀ a b : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀, a = b`.

Introduce `a b`. Proceed by induction on `a using QuotientGroup.induction_on`. Proceed by induction on `b using QuotientGroup.induction_on`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Conclude with `SetLike.coe_mem _`.

Use `letI : Unique (↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀) := ⟨⟨QuotientGroup.mk (1 : ↥T.K₀)⟩, fun a => hall a _⟩`. Rewrite using `[finsum_unique]`. Establish `hx : (↑(Quotient.out (default : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀)) : X) ∈ T.K₀` using `SetLike.coe_mem _`. Rewrite using `[_root_.mul_inv_rev, ← mul_assoc, hΦ k⁻¹ (hT.1 (K.inv_mem hk)) _, hT.2 k⁻¹ (K.inv_mem hk) _]`. Simplify using `only [Units.val_one, one_smul]`.

Conclude with `hinv0 _ (T.K₀.inv_mem hx) g`.
-/
theorem UpperTheory.Gal.W2.Seed.pMemDeck :
    MemSum → TfCen → MemDeck := by
  intro hSum hCen X M _ _ T K hT k hk hnorm
  have hconj : ∀ a ∈ T.K₀, ∀ u ∈ T.K₀, a * u * a⁻¹ ∈ T.K₀ := fun a ha u hu =>
    T.K₀.mul_mem (T.K₀.mul_mem ha hu) (T.K₀.inv_mem ha)
  have hmem := hSum X T.K₀ T.K₀ T.K₀ k le_rfl (by simp) hconj (fun a ha u hu => by
    have h1 := hnorm (a * u * a⁻¹) (hconj a ha u hu)
    simpa [mul_assoc, _root_.mul_inv_rev] using h1)
  refine ⟨hmem.1, map_one _, ?_⟩
  intro V _ _ Φ hΦ
  funext g
  have hc : T.Cen 1 := ⟨fun g => by simp, map_one _⟩
  rw [one_smul, hCen X M T 1 hc V Φ hΦ g, mul_one]
  have hinv0 : ∀ k' ∈ T.K₀, ∀ g, Φ (g * k') = Φ g := fun k' hk' g => by
    rw [hΦ k' (T.le hk') g, T.ker k' hk' _]
    simp
  rw [hmem.2.2 V Φ hinv0 g]
  have hall : ∀ a b : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀, a = b := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact SetLike.coe_mem _
  letI : Unique (↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀) :=
    ⟨⟨QuotientGroup.mk (1 : ↥T.K₀)⟩, fun a => hall a _⟩
  rw [finsum_unique]
  have hx : (↑(Quotient.out (default : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀)) : X) ∈ T.K₀ :=
    SetLike.coe_mem _
  rw [_root_.mul_inv_rev, ← mul_assoc, hΦ k⁻¹ (hT.1 (K.inv_mem hk)) _,
    hT.2 k⁻¹ (K.inv_mem hk) _]
  simp only [Units.val_one, one_smul]
  exact hinv0 _ (T.K₀.inv_mem hx) g
