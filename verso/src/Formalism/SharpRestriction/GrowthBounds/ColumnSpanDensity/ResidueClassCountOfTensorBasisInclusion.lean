import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeLatRS

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[Finset.mem_filter, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`. Conclude with `Fin.ext (by simpa using Nat.lt_one_iff.1 h)`.

Introduce and unpack `rfl`. Conclude with `⟨Finset.mem_univ _, by simp⟩`.
-/
theorem filter_lt_one (m : ℕ) : (Finset.univ.filter fun a : Fin (m + 1) => a.val < 1) = {0} := by
  ext a
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    exact Fin.ext (by simpa using Nat.lt_one_iff.1 h)
  · rintro rfl
    exact ⟨Finset.mem_univ _, by simp⟩

/- English proof (translation)
Unfold `lamAt`. Use `split_ifs`. Conclude with `h s i`. Rewrite using `[abs_neg]`. Conclude with `h s _`.
-/
theorem lamAt_abs {n' m : ℕ} (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ) (h : ∀ s i, |lamO s i| ≤ c) (s : Fin n')
    (i : Fin (m + 1)) : |lamAt lamO s i| ≤ c := by
  unfold lamAt
  split_ifs
  · exact h s i
  · rw [abs_neg]; exact h s _

section

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

def Elast (lamO : Fin n' → Fin (m + 1) → ℤ) : ℤ := ∑ s, lamAt lamO s (Fin.last m)

/- English proof (translation)
Unfold `Ar Elast`. Rewrite using `[← Finset.sum_sub_distrib]`. Establish `h1 : ∀ s ∈ (Finset.univ : Finset (Fin n')), (∑ i : Fin (m + 1) with i.val < 1, lamAt lamO s i) - lamAt lamO s (Fin.last m) ≤ 2 * (c : ℤ)`. Introduce `s _`. Rewrite using `[filter_lt_one, Finset.sum_singleton]`.

Establish `h2` using `abs_le.1 (lamAt_abs lamO c h s 0)`. Establish `h3` using `abs_le.1 (lamAt_abs lamO c h s (Fin.last m))`. Combine the linear relations using `[h2.2, h3.1]`. Establish `h4` using `Finset.sum_le_sum h1`. Rewrite `h4` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin]`.

Use `le_trans h4 ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[nsmul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Ar_sub_le (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ) (h : ∀ s i, |lamO s i| ≤ c) :
    Ar 1 lamO - Elast lamO ≤ ((2 * n' * c : ℕ) : ℤ) := by
  unfold Ar Elast
  rw [← Finset.sum_sub_distrib]
  have h1 : ∀ s ∈ (Finset.univ : Finset (Fin n')),
      (∑ i : Fin (m + 1) with i.val < 1, lamAt lamO s i) - lamAt lamO s (Fin.last m) ≤ 2 * (c : ℤ) := by
    intro s _
    rw [filter_lt_one, Finset.sum_singleton]
    have h2 := abs_le.1 (lamAt_abs lamO c h s 0)
    have h3 := abs_le.1 (lamAt_abs lamO c h s (Fin.last m))
    linarith [h2.2, h3.1]
  have h4 := Finset.sum_le_sum h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h4
  refine le_trans h4 ?_
  push_cast
  rw [nsmul_eq_mul]
  linarith

/- English proof (translation)
Take `⟨gs, hgs, h1, h2, h3⟩` from `edgeLat_RS R e he`. Establish `hw` using `R.w_ne`. Establish `hinj : Function.Injective (algebraMap R.O R.Kf)`. Establish `hfr : IsFractionRing R.O R.Kf` using `R.std.1.frac_O`. Conclude with `IsFractionRing.injective R.O R.Kf`.

Establish `hA : ∏ s : Fin n', algebraMap R.O R.Kf R.w ^ (-lamAt lamO s (Fin.last m)) = algebraMap R.O R.Kf R.w ^ (-Elast lamO)`. Rewrite using `[lb_zpow_sum _ hw, Elast, Finset.sum_neg_distrib]`. Establish `hgD : ∀ s, IsUnit (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w)).det`. Introduce `s`. Rewrite using `[Matrix.det_mul]`.

Conclude with `(hgs s).mul (lb_D_det _ _ _ hw)`. Establish `hone : ∀ z : ℤ, -(((Finset.univ.filter fun a : Fin (m + 1) => a.val < 1).card : ℤ) * z) = -z`. Introduce `z`. Rewrite using `[filter_lt_one]`. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Introduce `P hP`. Rewrite using `[← hA]`. Use `lb_tensor R.O R.Kf _ _ _ (fun s F hF => ?_) P hP` and prove the remaining obligations. Use `beta_reduce at hF ⊢`.

Rewrite `hF` using `[h2]`. Rewrite using `[h1]`. Use `zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul R.O R.Kf hinj m 1 _ (kp_lamAt_antitone _ hdom s) R.w hw _ (hgs _) F hF` as an intermediate fact. Rewrite `this` using `[hone]`. Then use the resulting hypothesis. Introduce `P hP`.

Rewrite using `[← hA]`. Use `lb_tensor R.O R.Kf _ _ _ (fun s F hF => ?_) P hP` and prove the remaining obligations. Use `beta_reduce at hF ⊢`. Rewrite `hF` using `[h3]`. Rewrite using `[h2]`.

Use `zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul R.O R.Kf hinj m 1 _ (kp_lamAt_antitone _ hdom s) R.w hw _ (hgD _) F hF` as an intermediate fact. Rewrite `this` using `[hone]`. Then use the resulting hypothesis.
-/
theorem steps_rev (lamO : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lamO) (e : Edge R.W R.Qq (m + 1))
    (he : IsEdge p n' 1 e) :
    (∀ P ∈ Hten R.O lamO (fun s => LeAt p R.ι R.σ R.w s.val e),
      (algebraMap R.O R.Kf R.w ^ (-Elast lamO)) • P ∈ Hten R.O lamO (fun s => extO R.O R.ι R.σ s.val e.src)) ∧
    (∀ P ∈ Hten R.O lamO (fun s => extO R.O R.ι R.σ s.val e.tgt),
      (algebraMap R.O R.Kf R.w ^ (-Elast lamO)) • P ∈ Hten R.O lamO (fun s => LeAt p R.ι R.σ R.w s.val e)) := by
  obtain ⟨gs, hgs, h1, h2, h3⟩ := edgeLat_RS R e he
  have hw := R.w_ne
  have hinj : Function.Injective (algebraMap R.O R.Kf) := by
    have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  have hA : ∏ s : Fin n', algebraMap R.O R.Kf R.w ^ (-lamAt lamO s (Fin.last m)) =
      algebraMap R.O R.Kf R.w ^ (-Elast lamO) := by
    rw [lb_zpow_sum _ hw, Elast, Finset.sum_neg_distrib]
  have hgD : ∀ s, IsUnit (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w)).det := by
    intro s
    rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hw)
  have hone : ∀ z : ℤ, -(((Finset.univ.filter fun a : Fin (m + 1) => a.val < 1).card : ℤ) * z) = -z := by
    intro z
    rw [filter_lt_one]
    simp
  constructor
  · intro P hP
    rw [← hA]
    refine lb_tensor R.O R.Kf _ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [h2] at hF
    rw [h1]
    have := zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul R.O R.Kf hinj m 1 _ (kp_lamAt_antitone _ hdom s) R.w hw _ (hgs _) F hF
    rwa [hone] at this
  · intro P hP
    rw [← hA]
    refine lb_tensor R.O R.Kf _ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [h3] at hF
    rw [h2]
    have := zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul R.O R.Kf hinj m 1 _ (kp_lamAt_antitone _ hdom s) R.w hw _ (hgD _) F hF
    rwa [hone] at this

end

/- English proof (translation)
Introduce `p n' R m lamO c hdom hsmall e he`. Take `⟨hs1, hs2⟩` from `steps_rev R lamO hdom e he`. Establish `hw` using `R.w_ne`. Use `set wK : R.Kf := algebraMap R.O R.Kf R.w with hwK`. Establish `hle` using `Ar_sub_le lamO c hsmall`.

Take `⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (k₀ : ℤ) = ((2 * n' * c : ℕ) : ℤ) - (Ar 1 lamO - Elast lamO)` from `⟨(((2 * n' * c : ℕ) : ℤ) - (Ar 1 lamO - Elast lamO)).toNat, Int.toNat_of_nonneg (by linarith)⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `_ ⟨h, hh, rfl⟩`. Establish `h1 : wK ^ (-Elast lamO) • h ∈ HL (O` using `R.O) R.ι R.σ lamO e.src := hs1 _ hh`. Use `⟨R.w ^ k₀ • (wK ^ (-Elast lamO) • h), Submodule.smul_mem _ _ h1, ?_⟩` and prove the remaining obligations.

Use `show wK ^ (-((2 * n' * c : ℕ) : ℤ)) • (R.w ^ k₀ • (wK ^ (-Elast lamO) • h)) = wK ^ (-Ar 1 lamO) • h`. Rewrite using `[← algebraMap_smul R.Kf (R.w ^ k₀), map_pow, ← hwK, smul_smul, smul_smul, ← zpow_natCast wK k₀, hk₀, ← zpow_add₀ hw, ← zpow_add₀ hw]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`.

Use `⟨wK ^ (((2 * n' * c : ℕ) : ℤ) - Ar 1 lamO) • φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `h hh`. Establish `h1 : wK ^ (-Elast lamO) • h ∈ HLe p R.ι R.σ R.w lamO e` using `hs2 _ hh`. Take `⟨a, ha⟩` from `hφ _ h1`. Use `⟨R.w ^ k₀ * a, ?_⟩` and prove the remaining obligations.

Rewrite `ha` using `[map_smul, smul_eq_mul]`. Rewrite using `[map_mul, ha, map_pow, ← hwK, LinearMap.smul_apply, smul_eq_mul, ← zpow_natCast wK k₀, hk₀, ← mul_assoc, ← zpow_add₀ hw]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Use `show wK ^ (-((2 * n' * c : ℕ) : ℤ)) • (wK ^ (((2 * n' * c : ℕ) : ℤ) - Ar 1 lamO) • φ) = wK ^ (-Ar 1 lamO) • φ`.

Rewrite using `[smul_smul, ← zpow_add₀ hw]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem restOrdBound : RestOrdBound := by
  intro p n' R m lamO c hdom hsmall e he
  obtain ⟨hs1, hs2⟩ := steps_rev R lamO hdom e he
  have hw := R.w_ne
  set wK : R.Kf := algebraMap R.O R.Kf R.w with hwK
  have hle := Ar_sub_le lamO c hsmall
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (k₀ : ℤ) = ((2 * n' * c : ℕ) : ℤ) - (Ar 1 lamO - Elast lamO) :=
    ⟨(((2 * n' * c : ℕ) : ℤ) - (Ar 1 lamO - Elast lamO)).toNat, Int.toNat_of_nonneg (by linarith)⟩
  constructor
  · rintro _ ⟨h, hh, rfl⟩
    have h1 : wK ^ (-Elast lamO) • h ∈ HL (O := R.O) R.ι R.σ lamO e.src := hs1 _ hh
    refine ⟨R.w ^ k₀ • (wK ^ (-Elast lamO) • h), Submodule.smul_mem _ _ h1, ?_⟩
    show wK ^ (-((2 * n' * c : ℕ) : ℤ)) • (R.w ^ k₀ • (wK ^ (-Elast lamO) • h)) = wK ^ (-Ar 1 lamO) • h
    rw [← algebraMap_smul R.Kf (R.w ^ k₀), map_pow, ← hwK, smul_smul, smul_smul, ← zpow_natCast wK k₀, hk₀,
      ← zpow_add₀ hw, ← zpow_add₀ hw]
    congr 2
    ring
  · rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨wK ^ (((2 * n' * c : ℕ) : ℤ) - Ar 1 lamO) • φ, ?_, ?_⟩
    · intro h hh
      have h1 : wK ^ (-Elast lamO) • h ∈ HLe p R.ι R.σ R.w lamO e := hs2 _ hh
      obtain ⟨a, ha⟩ := hφ _ h1
      refine ⟨R.w ^ k₀ * a, ?_⟩
      rw [map_smul, smul_eq_mul] at ha
      rw [map_mul, ha, map_pow, ← hwK, LinearMap.smul_apply, smul_eq_mul, ← zpow_natCast wK k₀, hk₀, ← mul_assoc,
        ← zpow_add₀ hw]
      congr 2
      ring
    · show wK ^ (-((2 * n' * c : ℕ) : ℤ)) • (wK ^ (((2 * n' * c : ℕ) : ℤ) - Ar 1 lamO) • φ) = wK ^ (-Ar 1 lamO) • φ
      rw [smul_smul, ← zpow_add₀ hw]
      congr 2
      ring

/- English proof (translation)
The claim follows from `tensor_bound_of_order_bound hTen restOrdBound hD3 hIncl`.
-/
theorem residueClassCount_of_tensor_basis_inclusion (hTen : RestTensor) (hD3 : DualHeightBasis) (hIncl : DualHeightInclusion) : ResidueClassCount :=
  tensor_bound_of_order_bound hTen restOrdBound hD3 hIncl

end Formalism.MainNotions.flipOneThree.Pf

end
