import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ExistsKmat

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

/- English proof (translation)
Rewrite using `[HE_apply, WithLp.ofLp_toLp]`. Both sides reduce to the same expression.
-/
theorem pe_eq (a : Fin (r + 1)) :
    (WithLp.toLp 2 (phiV' k r a) : EE k r) = HE k r (WithLp.toLp 2 (phiV k r a)) := by
  rw [HE_apply, WithLp.ofLp_toLp]; rfl

/- English proof (translation)
Establish `h` using `qe_orth (k := k) (r := r) hk`. Rewrite `h`, the goal using `[orthonormal_iff_ite]`. Introduce `a b`. Simplify using `only [pe_eq, HE_adj, HE_HE]`. Conclude with `h a b`.
-/
theorem pe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV' k r a) : EE k r)) := by
  have h := qe_orth (k := k) (r := r) hk
  rw [orthonormal_iff_ite] at h ⊢
  intro a b; simp only [pe_eq, HE_adj, HE_HE]; exact h a b

/- English proof (translation)
Rewrite using `[pe_eq, pe_eq, HE_HE, HE_adj, HE_apply, WithLp.ofLp_toLp, toLp_phiV a]`. Distinguish the cases in `ha : a.val < r`. Rewrite using `[if_pos ha, inner_bvec, hpk_mulVec, phiV_apply]`. Simplify using `only [sigI_val, sgnI]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | simp`.

Rewrite using `[if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, hpk_mulVec, hpk_mulVec, phiV_apply, phiV_apply]`. Simplify using `only [sigI_val, sgnI, starRingEnd_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | ring | simp`.
-/
theorem pe_iso (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    inner ℂ (WithLp.toLp 2 (phiV' k r a) : EE k r) (HE k r (WithLp.toLp 2 (phiV' k r b))) = 0 := by
  rw [pe_eq, pe_eq, HE_HE, HE_adj, HE_apply, WithLp.ofLp_toLp, toLp_phiV a]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, hpk_mulVec, phiV_apply]
    simp only [sigI_val, sgnI]
    split_ifs <;> first | rfl | (exfalso; omega) | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, hpk_mulVec, hpk_mulVec,
      phiV_apply, phiV_apply]
    simp only [sigI_val, sgnI, starRingEnd_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | ring | simp

/- English proof (translation)
The claim follows from `(pe_orth hk).linearIndependent.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap (LinearEquiv.ker _)`.
-/
theorem phiV'_linInd' (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) :=
  (pe_orth hk).linearIndependent.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap
    (LinearEquiv.ker _)

/- English proof (translation)
Rewrite using `[herm_eq]`. Conclude with `pe_iso hk b a`.
-/
theorem phiV'_iso' (hk : 1 ≤ k) (a b : Fin (r + 1)) : herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by
  rw [herm_eq]; exact pe_iso hk b a

/- English proof (translation)
Rewrite using `[show (∑ b : Fin (l + 1), f (Fin.castLE h b)) = ∑ b ∈ Finset.univ.map (Fin.castLEEmb h), f b by rw [Finset.sum_map]; rfl]`. Use `(Finset.sum_subset (Finset.subset_univ _) fun b _ hb => hf b ?_).symm` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Conclude with `hb (Finset.mem_map.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
theorem sum_castLE {M : Type*} [AddCommMonoid M] {l : ℕ} (h : l + 1 ≤ r + 1) (f : Fin (r + 1) → M)
    (hf : ∀ b : Fin (r + 1), l < b.val → f b = 0) :
    ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by
  rw [show (∑ b : Fin (l + 1), f (Fin.castLE h b)) = ∑ b ∈ Finset.univ.map (Fin.castLEEmb h), f b by rw [Finset.sum_map]; rfl]
  refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => hf b ?_).symm
  by_contra hcon
  exact hb (Finset.mem_map.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/- English proof (translation)
Rewrite using `[show (∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j)) = ∏ j ∈ Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)), g j by`. Rewrite using `[Finset.prod_map]`. Use the proof step `rfl]`. Use `congr 1`. Use extensionality with `j`.

Simplify using `only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce `hj; exact ⟨⟨j.val, by rw [Fin.le_def] at hj; omega⟩, Fin.ext rfl⟩`. Introduce and unpack `⟨b, rfl⟩`. Rewrite using `[Fin.le_def]`.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem prod_Iic_castLE (l : Fin (r + 1)) (g : Fin (r + 1) → ℝ) :
    ∏ j ∈ Finset.Iic l, g j = ∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j) := by
  rw [show (∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j)) =
      ∏ j ∈ Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)), g j by
    rw [Finset.prod_map]; rfl]
  congr 1
  ext j
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hj; exact ⟨⟨j.val, by rw [Fin.le_def] at hj; omega⟩, Fin.ext rfl⟩
  · rintro ⟨b, rfl⟩; rw [Fin.le_def]; simp; omega

/- English proof (translation)
Take `⟨u, τ, hu, hτ, hd, hwe, hspan⟩` from `gs_fac (fun a => (WithLp.toLp 2 (Y a) : EE k r)) (linInd_toLp Y hY)`. Establish `hwi : ∀ a b, inner ℂ (WithLp.toLp 2 (Y a) : EE k r) (HE k r (WithLp.toLp 2 (Y b))) = 0` using `fun a b => by rw [← herm_eq]; exact hiso b a`. Establish `hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0`. Introduce `a b`. Take `⟨ca, hca⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan a)`.

Take `⟨cb, hcb⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan b)`. Rewrite using `[← hca, ← hcb, map_sum, sum_inner]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_sum]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, inner_smul_left, inner_smul_right, hwi, mul_zero, mul_zero]`. Take `⟨κ, hκK, hκ⟩` from `exists_Kmat hk _ u (pe_orth hk) hu (fun a b => pe_iso hk a b) hui`. Establish `hκ' : ∀ b, u b = WithLp.toLp 2 (κ *ᵥ phiV' k r b)` using `fun b => (hκ b).symm`. Use `⟨κ, hκK, τ, hτ, hd, fun a => ?_, fun l => ?_⟩` and prove the remaining obligations. Establish `h1 : (WithLp.toLp 2 (Y a) : EE k r) = ∑ b, τ b a • (WithLp.toLp 2 (κ *ᵥ phiV' k r b) : EE k r)`.

Rewrite using `[hwe a]`. Simplify using `only [hκ']`. Establish `h2` using `congrArg (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)) h1`. Rewrite `h2` using `[map_sum]`. Simplify using `using h2`.

Rewrite using `[ga_eq]`. Establish `hle : l.val + 1 ≤ r + 1` using `by omega`. Establish `hsub : ∀ a : Fin (l.val + 1), (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r) = ∑ b : Fin (l.val + 1), (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)) b a • u (Fin.castLE hle b)`. Introduce `a`. Rewrite using `[hwe (Fin.castLE hle a)]`.

Use `sum_castLE hle _ fun b hb => ?_` and prove the remaining obligations. Establish `hlt : Fin.castLE hle a < b`. Rewrite using `[Fin.lt_def, Fin.val_castLE]`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[show τ b (Fin.castLE hle a) = 0 from hτ hlt, zero_smul]`. Establish `hτl : (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)).BlockTriangular id` using `fun i j hij => hτ (show Fin.castLE hle j < Fin.castLE hle i from hij)`. Establish `hdet` using `det_gram_of (fun a : Fin (l.val + 1) => (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r)) (fun b => u (Fin.castLE hle b)) (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)) (hu.comp _ (Fin.castLE_injective hle)) hτl hsub`. Rewrite using `[hdet, Complex.ofReal_re, prod_Iic_castLE]`. Both sides reduce to the same expression.
-/
theorem iw_core (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (hk : 1 ≤ k)
    (hY : LinearIndependent ℂ Y) (hiso : ∀ a b, herm (Hpk k r) (Y a) (Y b) = 0) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ j, τ j j ≠ 0) ∧ (∀ a, Y a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l Y := by
  obtain ⟨u, τ, hu, hτ, hd, hwe, hspan⟩ := gs_fac (fun a => (WithLp.toLp 2 (Y a) : EE k r)) (linInd_toLp Y hY)
  have hwi : ∀ a b, inner ℂ (WithLp.toLp 2 (Y a) : EE k r) (HE k r (WithLp.toLp 2 (Y b))) = 0 :=
    fun a b => by rw [← herm_eq]; exact hiso b a
  have hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0 := by
    intro a b
    obtain ⟨ca, hca⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan a)
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan b)
    rw [← hca, ← hcb, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right, hwi, mul_zero, mul_zero]
  obtain ⟨κ, hκK, hκ⟩ := exists_Kmat hk _ u (pe_orth hk) hu (fun a b => pe_iso hk a b) hui
  have hκ' : ∀ b, u b = WithLp.toLp 2 (κ *ᵥ phiV' k r b) := fun b => (hκ b).symm
  refine ⟨κ, hκK, τ, hτ, hd, fun a => ?_, fun l => ?_⟩
  · have h1 : (WithLp.toLp 2 (Y a) : EE k r) = ∑ b, τ b a • (WithLp.toLp 2 (κ *ᵥ phiV' k r b) : EE k r) := by
      rw [hwe a]; simp only [hκ']
    have h2 := congrArg (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)) h1
    rw [map_sum] at h2
    simpa using h2
  · rw [ga_eq]
    have hle : l.val + 1 ≤ r + 1 := by omega
    have hsub : ∀ a : Fin (l.val + 1), (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r) =
        ∑ b : Fin (l.val + 1), (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)) b a • u (Fin.castLE hle b) := by
      intro a
      rw [hwe (Fin.castLE hle a)]
      refine sum_castLE hle _ fun b hb => ?_
      have hlt : Fin.castLE hle a < b := by
        rw [Fin.lt_def, Fin.val_castLE]; have := a.isLt; omega
      rw [show τ b (Fin.castLE hle a) = 0 from hτ hlt, zero_smul]
    have hτl : (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)).BlockTriangular id :=
      fun i j hij => hτ (show Fin.castLE hle j < Fin.castLE hle i from hij)
    have hdet := det_gram_of (fun a : Fin (l.val + 1) => (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r))
      (fun b => u (Fin.castLE hle b)) (τ.submatrix (Fin.castLE hle) (Fin.castLE hle))
      (hu.comp _ (Fin.castLE_injective hle)) hτl hsub
    rw [hdet, Complex.ofReal_re, prod_Iic_castLE]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Xi.GS

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

/- English proof (translation)
The claim follows from `GS.phiV'_linInd' hk`.
-/
theorem phiV'_linInd (k r : ℕ) (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := GS.phiV'_linInd' hk

/- English proof (translation)
The claim follows from `GS.phiV'_iso' hk a b`.
-/
theorem phiV'_iso (k r : ℕ) (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := GS.phiV'_iso' hk a b

/- English proof (translation)
Introduce `k r Y hk hY hiso` and use `by obtain ⟨κ, hκ, τ, h1, -, h3, h4⟩ := GS.iw_core Y hk hY hiso exact ⟨κ, hκ, τ, h1, h3, h4⟩`.
-/
theorem iwB : IW := fun k r Y hk hY hiso => by
  obtain ⟨κ, hκ, τ, h1, -, h3, h4⟩ := GS.iw_core Y hk hY hiso
  exact ⟨κ, hκ, τ, h1, h3, h4⟩

end ReciprocityTheory.ChartRestriction.DS.Xi
