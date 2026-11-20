import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GmaKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinEGma
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Introduce `n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hred hmf hn y`. Take `⟨DE, π, e, hpull, hgma, -, -, -, -, -⟩` from `finE_gma D χ hc hred hmf ∅ (by simp)`. Establish `hsurj : Function.Surjective (D.toQuot ∅)` using `RingCon.mkₐ_surjective _`. Establish `htq : ∀ w, DE.tr (D.toQuot ∅ w) = D.tr w`. Introduce `w`.

Rewrite using `[← (d_toDet D w).2.2.1]`. Use `show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (D.toDet.chi w).coeff (n - 1)`. Rewrite using `[← hpull, (d_pull DE (D.toQuot ∅)).1 w]`. Take `⟨t, ht⟩` from `(d_tr D.toDet).1 hn`. Rewrite using `[← (d_toDet D y).2.2.2, ← (d_ker _ y).1]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy g`. Establish `hk : D.toQuot ∅ y ∈ DE.ker`. Rewrite `hy` using `[← hpull]`. Conclude with `((d_pull DE _).2.2.2 hsurj).1 y hy`.

Rewrite using `[← htq, map_mul]`. Conclude with `(gma_kills DE e hn hgma _).1 hk _`. Introduce `H`. Establish `hk : D.toQuot ∅ y ∈ DE.ker`. Rewrite using `[gma_kills DE e hn hgma]`.

Introduce `q`. Take `⟨w, rfl⟩` from `hsurj q`. Rewrite using `[← map_mul, htq, ← (d_toDet D _).2.2.1, ← ht]`. Use `MonoidAlgebra.induction_on (motive := fun w => t (w * y) = 0) w ?_ ?_ ?_` and prove the remaining obligations. Introduce `m`.

Rewrite using `[ht, (d_toDet D _).2.2.1]`. Conclude with `H m`. Introduce `a b ha hb`. Rewrite using `[add_mul, map_add, ha, hb, add_zero]`. Introduce `r a ha`.

Rewrite using `[smul_mul_assoc, map_smul, ha, smul_zero]`. Rewrite using `[← hpull]`. Conclude with `(d_pull DE _).2.1 y hk`.
-/
theorem UpperTheory.V.CA.g_kills_tr :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → 1 ≤ n → ∀ y : MonoidAlgebra B G, D.Kills y ↔ ∀ g : G, D.tr (MonoidAlgebra.single g 1 * y) = 0 := by
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hred hmf hn y
  obtain ⟨DE, π, e, hpull, hgma, -, -, -, -, -⟩ := finE_gma D χ hc hred hmf ∅ (by simp)
  have hsurj : Function.Surjective (D.toQuot ∅) := RingCon.mkₐ_surjective _
  have htq : ∀ w, DE.tr (D.toQuot ∅ w) = D.tr w := by
    intro w
    rw [← (d_toDet D w).2.2.1]
    show (-1) ^ 1 * (DE.chi _).coeff (n - 1) = (-1) ^ 1 * (D.toDet.chi w).coeff (n - 1)
    rw [← hpull, (d_pull DE (D.toQuot ∅)).1 w]
  obtain ⟨t, ht⟩ := (d_tr D.toDet).1 hn
  rw [← (d_toDet D y).2.2.2, ← (d_ker _ y).1]
  constructor
  · intro hy g
    have hk : D.toQuot ∅ y ∈ DE.ker := by
      rw [← hpull] at hy
      exact ((d_pull DE _).2.2.2 hsurj).1 y hy
    rw [← htq, map_mul]
    exact (gma_kills DE e hn hgma _).1 hk _
  · intro H
    have hk : D.toQuot ∅ y ∈ DE.ker := by
      rw [gma_kills DE e hn hgma]
      intro q
      obtain ⟨w, rfl⟩ := hsurj q
      rw [← map_mul, htq, ← (d_toDet D _).2.2.1, ← ht]
      refine MonoidAlgebra.induction_on (motive := fun w => t (w * y) = 0) w ?_ ?_ ?_
      · intro m
        rw [ht, (d_toDet D _).2.2.1]
        exact H m
      · intro a b ha hb
        rw [add_mul, map_add, ha, hb, add_zero]
      · intro r a ha
        rw [smul_mul_assoc, map_smul, ha, smul_zero]
    rw [← hpull]
    exact (d_pull DE _).2.1 y hk
