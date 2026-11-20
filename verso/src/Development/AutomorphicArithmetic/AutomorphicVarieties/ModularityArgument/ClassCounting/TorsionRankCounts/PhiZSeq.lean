import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => exact ⟨0, fun x => by simp only [pow_zero, mul_zero, sub_zero, mul_one, one_smul]; rfl⟩`. Consider the case `succ t ih`. Take `⟨c, hc⟩` from `ih`. Use `⟨c + (l : ℤ) ^ t - l * c * (l : ℤ) ^ t, fun x => ?_⟩` and prove the remaining obligations.

Establish `h : φ (lev l n (t + 1)) (zSeq R hl x (t + 1)) = φ (l * lev l n t) ((grpHMap (psi R l (lev l n t)) m).hom (zSeq R hl x t) - l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m).hom (zSeq R hl x t))` using `rfl`. Rewrite using `[h, map_sub, map_nsmul, hφ.psi, hφ.stab, hc, ← natCast_zsmul, ← natCast_zsmul, ← sub_smul, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.V.ZK.Up.phi_zSeq {R B : Type} [CommRing R] [AddCommGroup B] {m l : ℕ} (hl : 0 < l)
    (φ : ∀ n : ℕ, grpH (GL (Fin n) R) m →+ B) (hφ : IsPrimH φ) (n t : ℕ) :
    ∃ c : ℤ, ∀ x : grpH (GL (Fin n) R) m,
      φ (lev l n t) (zSeq R hl x t) = ((l : ℤ) ^ t * (1 - l * c)) • φ n x := by
  induction t with
  | zero => exact ⟨0, fun x => by simp only [pow_zero, mul_zero, sub_zero, mul_one, one_smul]; rfl⟩
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (l : ℤ) ^ t - l * c * (l : ℤ) ^ t, fun x => ?_⟩
    have h : φ (lev l n (t + 1)) (zSeq R hl x (t + 1)) =
        φ (l * lev l n t) ((grpHMap (psi R l (lev l n t)) m).hom (zSeq R hl x t) -
          l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m).hom
            (zSeq R hl x t)) := rfl
    rw [h, map_sub, map_nsmul, hφ.psi, hφ.stab, hc, ← natCast_zsmul, ← natCast_zsmul, ← sub_smul, smul_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Introduce `R B _ _ m l ν hl hB φ hφ n t`. Take `⟨c, hc⟩` from `UpperTheory.V.ZK.Up.phi_zSeq hl φ hφ n t`. Use `⟨∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i, fun x => ?_⟩` and prove the remaining obligations. Establish `hg : (∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i) * ((l : ℤ) ^ t * (1 - l * c)) = (l : ℤ) ^ t - ((l : ℤ) ^ t * c ^ ν) * ((l ^ ν : ℕ) : ℤ)`. Use `geom_sum_mul_neg ((l : ℤ) * c) ν` as an intermediate fact.

Use `push_cast`. Rewrite using `[mul_left_comm, this, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_zsmul, hc, smul_smul, hg, sub_smul, mul_smul _ ((l ^ ν : ℕ) : ℤ), natCast_zsmul, hB, smul_zero, sub_zero, ← natCast_zsmul, Nat.cast_pow]`.
-/
theorem UpperTheory.V.ZK.Up.zVal :
    UpperTheory.V.ZK.Up.ZVal := by
  intro R B _ _ m l ν hl hB φ hφ n t
  obtain ⟨c, hc⟩ := UpperTheory.V.ZK.Up.phi_zSeq hl φ hφ n t
  refine ⟨∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i, fun x => ?_⟩
  have hg : (∑ i ∈ Finset.range ν, ((l : ℤ) * c) ^ i) * ((l : ℤ) ^ t * (1 - l * c)) =
      (l : ℤ) ^ t - ((l : ℤ) ^ t * c ^ ν) * ((l ^ ν : ℕ) : ℤ) := by
    have := geom_sum_mul_neg ((l : ℤ) * c) ν
    push_cast
    rw [mul_left_comm, this, mul_pow]
    ring
  rw [map_zsmul, hc, smul_smul, hg, sub_smul, mul_smul _ ((l ^ ν : ℕ) : ℤ), natCast_zsmul, hB, smul_zero, sub_zero,
    ← natCast_zsmul, Nat.cast_pow]
