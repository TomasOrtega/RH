import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedDualVectorPairingBoundedMajorant
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.NfComp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NfOff

/- English proof (translation)
Take `⟨d, hd, hmax⟩` from `Finset.exists_max_image (Finset.univ.filter fun i : Fin r => β i ≤ β c) id ⟨c, by simp⟩`. Use `⟨d.val + 1, d.2, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Conclude with `(hβ (show i ≤ d from Nat.le_of_lt_succ h)).trans (Finset.mem_filter.1 hd).2`. Conclude with `Nat.lt_succ_of_le (hmax i (by simpa using h))`.
-/
lemma exists_blockEnd {r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (c : Fin r) :
    ∃ l, l ≤ r ∧ ∀ i : Fin r, i.val < l ↔ β i ≤ β c := by
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i : Fin r => β i ≤ β c) id
    ⟨c, by simp⟩
  refine ⟨d.val + 1, d.2, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (hβ (show i ≤ d from Nat.le_of_lt_succ h)).trans (Finset.mem_filter.1 hd).2
  · exact Nat.lt_succ_of_le (hmax i (by simpa using h))

/- English proof (translation)
Rewrite `hZ` using `[Matrix.twoBlockTriangular_det Z (fun i => i.val < l) h]`. Establish `h1` using `left_ne_zero_of_mul hZ`. Set `e : Fin l ≃ {i : Fin r // i.val < l}` to `⟨fun i => ⟨Fin.castLE hl i, i.2⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩`. Rewrite `h1` using `[← Matrix.det_submatrix_equiv_self e]`. Conclude with `h1`.
-/
lemma minor_ne_zero {r l : ℕ} (hl : l ≤ r) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : Z.det ≠ 0)
    (h : ∀ i : Fin r, ¬ i.val < l → ∀ j : Fin r, j.val < l → Z i j = 0) :
    (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
  rw [Matrix.twoBlockTriangular_det Z (fun i => i.val < l) h] at hZ
  have h1 := left_ne_zero_of_mul hZ
  let e : Fin l ≃ {i : Fin r // i.val < l} :=
    ⟨fun i => ⟨Fin.castLE hl i, i.2⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← Matrix.det_submatrix_equiv_self e] at h1
  exact h1

/- English proof (translation)
Use extensionality with `a b`. Establish `h` using `((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1 b`. Establish `h2 : Zr k r (g * uEmb k r u) a b = (g *ᵥ (uEmb k r u *ᵥ bvec (eI k r b))) (esI k r a)`. Rewrite using `[Matrix.mulVec_mulVec]`. Simplify using `[bvec, Zr]`.

Rewrite using `[h2, h, Matrix.mulVec_sum, Finset.sum_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `[bvec, Zr, Matrix.mulVec_smul, mul_comm]`.
-/
lemma Zr_mul_uEmb {k r : ℕ} (g : Mat k r) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) :
    Zr k r (g * uEmb k r u) = Zr k r g * u := by
  ext a b
  have h := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1 b
  have h2 : Zr k r (g * uEmb k r u) a b = (g *ᵥ (uEmb k r u *ᵥ bvec (eI k r b))) (esI k r a) := by
    rw [Matrix.mulVec_mulVec]; simp [bvec, Zr]
  rw [h2, h, Matrix.mulVec_sum, Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [bvec, Zr, Matrix.mulVec_smul, mul_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, ⟨(uHGroup _ _ (Hunit k r)).1, by simp, by simp⟩, _, hn, (one_mul _).symm⟩`.
-/
lemma N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ (Hunit k r)).1, by simp, by simp⟩, _, hn, (one_mul _).symm⟩

/- English proof (translation)
Introduce `k r z z' g₀ β De R₀ hT hN hDe hR m hm y q a ha hS' hS p`. Take `⟨hz, hz', -⟩` from `hT`. Take `⟨hg, -, hβ, hdet, hblk, -⟩` from `hN`. Take `⟨⟨⟨c, b⟩, hcb⟩, hβcb⟩` from `p`. Simplify using `only at hcb hβcb`.

Take `⟨hg1, he⟩` from `levi_diag_middle_mem_bessel_unitary_eucl (r := r) hm a ha`. Establish `hU1 : (upperOff β y).det = 1` using `((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).1`. Establish `hUu : IsUnit (upperOff β y).det` using `by rw [hU1]; exact isUnit_one`. Establish `hUN : uEmb k r (upperOff β y) ∈ Nset k r` using `((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).2`. Establish `hPN : pOf k r q ∈ Nset k r` using `(((GlobalTheory.Amp.Rad.radical k r).1 _ _).2.2.2 ((GlobalTheory.Amp.Rad.radical k r).2.1 _ _)).1`.

Establish `hPe : ∀ d : Fin r, pOf k r q *ᵥ bvec (eI k r d) = bvec (eI k r d)` using `((GlobalTheory.Amp.Rad.radical k r).1 _ _).1`. Establish `hs : uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r` using `(nSubgroup k r).2.1 _ hUN _ hPN`. Rewrite `hS`, `hS'` using `[Matrix.mul_assoc (uEmb k r (upperOff β y) * pOf k r q)]`. Establish `hlen : ∀ d : Fin r, (a d)⁻¹ ≤ R₀`. Introduce `d`.

Establish `h1` using `(((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 _ hg1 _ (N_sub_S z' hs) 1 ⟨(uHGroup _ _ (Hunit k r)).1, one_mem _⟩).1 d.castSucc)`. Rewrite `h1` using `[mul_one, (GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.1 a ha m hm]`. Rewrite using `[← h1]`. Conclude with `((((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2).trans hS'`. Use `set g₁ := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg₁`.

Use `set U := upperOff β y with hU`. Take `⟨l, hl, hlβ⟩` from `exists_blockEnd hβ c`. Establish `hcl : c.val < l` using `(hlβ c).2 le_rfl`. Establish `hZ0 : ∀ i j : Fin r, (i.val < l ↔ ¬ j.val < l) → Zr k r g₀ i j = 0`. Introduce `i j hij`.

Assume the negation of the conclusion as `h`. Use `hblk i j h` as an intermediate fact. Rewrite `hij` using `[hlβ, hlβ, this]`. The claim follows by propositional logic. Establish `hcr` using `Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.cramerUpper ℂ r l hl 1 (Zr k r g₀) U (by simp) (fun i j h => Matrix.one_apply_ne h.ne) (fun i => by simp [hU, upperOff, upper]) (fun i j h => by`.

Simplify using `only [hU, upperOff, upper]`. Rewrite using `[dif_neg (not_lt.2 h.le), if_neg h.ne'])`. Use the proof step `(fun i j hi hj => hZ0 i j ⟨fun _ => not_lt.2 hj, fun _ => hi⟩) ⟨c.val, hcl⟩ b`. Use the proof step `(fun c' hc' => by`. Assume the negation of the conclusion as `h`.

Break down `upperOff_ne hβ y _ _ h with h' | h'` into its components or cases. Conclude with `hc'.ne (Fin.castLE_injective hl h')`. Conclude with `absurd ((hlβ (Fin.castLE hl c')).1 c'.2) (not_le.2 h'))`. Establish `hUcb : U (Fin.castLE hl ⟨c.val, hcl⟩) b = y ⟨⟨(c, b), hcb⟩, hβcb⟩` using `by show upperOff β y c b = _`. Simplify using `only [upperOff, upper]`.

Rewrite using `[dif_pos hcb, dif_pos hβcb]`. Rewrite `hcr` using `[Matrix.one_mul, hUcb, ← Zr_mul_uEmb g₀ U hUu]`. Establish `hD1 : ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) (Fin.castLE hl)).det = Dmin k r z z' g₀ ⟨l, by omega⟩`. Establish `h1` using `dInv k r z z' hz hz' 1 (N_sub_S z (nSubgroup k r).1) _ (N_sub_S z' hUN) g₀ ⟨l, by omega⟩`. Rewrite `h1` using `[Matrix.one_mul]`.

Rewrite using `[← h1, Dmin_eq le_rfl z z' _ l hl]`. Both sides reduce to the same expression. Establish `hD0 : Dmin k r z z' g₀ ⟨l, by omega⟩ ≠ 0`. Rewrite using `[Dmin_eq le_rfl z z' _ l hl]`. Conclude with `minor_ne_zero hl _ hdet fun i hi j hj => hZ0 i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩`.

Establish `hDb` using `hDe.2 ⟨l, by omega⟩ hl hD0`. Rewrite `hcr` using `[hD1]`. Use `set σ : Fin l → Fin r := fun j => if j = ⟨c.val, hcl⟩ then b else Fin.castLE hl j with hσ`. Establish `hx` using `G_mul hg (G_mul hs.1 hg1)`. Establish `hp` using `pluck_flag hl z hz _ hx R₀ hS (fun i => g₁⁻¹ *ᵥ bvec (eI k r (σ i))) (fun i => by`.

Rewrite using `[he]`. Conclude with `hlen _)`. Establish `hmat : (Matrix.of fun i i' : Fin l => herm (Hpk k r) ((g₀ * (uEmb k r U * pOf k r q * g₁))⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl i'))) (g₁⁻¹ *ᵥ bvec (eI k r (σ i)))) = ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) σ)ᴴ`. Use extensionality with `i i'`. Rewrite using `[Matrix.of_apply, herm_inv_left hx, herm_symm, herm_e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (G_unit hg1), Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hPe]`.

Simplify using `[bvec, Zr]`. Rewrite `hp` using `[hmat, Matrix.det_conjTranspose, norm_star, hcr, norm_mul]`. Establish `hP0 : 0 < ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖` using `norm_pos_iff.2 hD0`. Establish `hpow : R₀ ^ l * R₀ ^ l ≤ R₀ ^ (2 * r)`. Rewrite using `[← pow_add]; exact pow_le_pow_right₀ hR (by omega)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← div_eq_mul_inv, le_div_iff₀' hP0]`. Conclude with `hp.trans hpow`. Use `_ ≤ _ := mul_le_mul_of_nonneg_left hDb (by positivity)`.
-/
theorem offBlock_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  intro k r z z' g₀ β De R₀ hT hN hDe hR m hm y q a ha hS' hS p
  obtain ⟨hz, hz', -⟩ := hT
  obtain ⟨hg, -, hβ, hdet, hblk, -⟩ := hN
  obtain ⟨⟨⟨c, b⟩, hcb⟩, hβcb⟩ := p
  simp only at hcb hβcb
  obtain ⟨hg1, he⟩ := levi_diag_middle_mem_bessel_unitary_eucl (r := r) hm a ha
  have hU1 : (upperOff β y).det = 1 := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).1
  have hUu : IsUnit (upperOff β y).det := by rw [hU1]; exact isUnit_one
  have hUN : uEmb k r (upperOff β y) ∈ Nset k r := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).2
  have hPN : pOf k r q ∈ Nset k r :=
    (((GlobalTheory.Amp.Rad.radical k r).1 _ _).2.2.2 ((GlobalTheory.Amp.Rad.radical k r).2.1 _ _)).1
  have hPe : ∀ d : Fin r, pOf k r q *ᵥ bvec (eI k r d) = bvec (eI k r d) := ((GlobalTheory.Amp.Rad.radical k r).1 _ _).1
  have hs : uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := (nSubgroup k r).2.1 _ hUN _ hPN
  rw [Matrix.mul_assoc (uEmb k r (upperOff β y) * pOf k r q)] at hS hS'
  have hlen : ∀ d : Fin r, (a d)⁻¹ ≤ R₀ := by
    intro d
    have h1 := (((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 _ hg1 _ (N_sub_S z' hs) 1
      ⟨(uHGroup _ _ (Hunit k r)).1, one_mem _⟩).1 d.castSucc)
    rw [mul_one, (GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.1 a ha m hm] at h1
    rw [← h1]
    exact ((((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2).trans hS'
  set g₁ := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg₁
  set U := upperOff β y with hU
  obtain ⟨l, hl, hlβ⟩ := exists_blockEnd hβ c
  have hcl : c.val < l := (hlβ c).2 le_rfl
  have hZ0 : ∀ i j : Fin r, (i.val < l ↔ ¬ j.val < l) → Zr k r g₀ i j = 0 := by
    intro i j hij
    by_contra h
    have := hblk i j h
    rw [hlβ, hlβ, this] at hij
    tauto
  have hcr := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.cramerUpper ℂ r l hl 1 (Zr k r g₀) U (by simp)
    (fun i j h => Matrix.one_apply_ne h.ne) (fun i => by simp [hU, upperOff, upper])
    (fun i j h => by
      simp only [hU, upperOff, upper]
      rw [dif_neg (not_lt.2 h.le), if_neg h.ne'])
    (fun i j hi hj => hZ0 i j ⟨fun _ => not_lt.2 hj, fun _ => hi⟩) ⟨c.val, hcl⟩ b
    (fun c' hc' => by
      by_contra h
      rcases upperOff_ne hβ y _ _ h with h' | h'
      · exact hc'.ne (Fin.castLE_injective hl h')
      · exact absurd ((hlβ (Fin.castLE hl c')).1 c'.2) (not_le.2 h'))
  have hUcb : U (Fin.castLE hl ⟨c.val, hcl⟩) b = y ⟨⟨(c, b), hcb⟩, hβcb⟩ := by
    show upperOff β y c b = _
    simp only [upperOff, upper]
    rw [dif_pos hcb, dif_pos hβcb]
  rw [Matrix.one_mul, hUcb, ← Zr_mul_uEmb g₀ U hUu] at hcr
  have hD1 : ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      Dmin k r z z' g₀ ⟨l, by omega⟩ := by
    have h1 := dInv k r z z' hz hz' 1 (N_sub_S z (nSubgroup k r).1) _ (N_sub_S z' hUN) g₀ ⟨l, by omega⟩
    rw [Matrix.one_mul] at h1
    rw [← h1, Dmin_eq le_rfl z z' _ l hl]
    rfl
  have hD0 : Dmin k r z z' g₀ ⟨l, by omega⟩ ≠ 0 := by
    rw [Dmin_eq le_rfl z z' _ l hl]
    exact minor_ne_zero hl _ hdet fun i hi j hj => hZ0 i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩
  have hDb := hDe.2 ⟨l, by omega⟩ hl hD0
  rw [hD1] at hcr
  set σ : Fin l → Fin r := fun j => if j = ⟨c.val, hcl⟩ then b else Fin.castLE hl j with hσ
  have hx := G_mul hg (G_mul hs.1 hg1)
  have hp := pluck_flag hl z hz _ hx R₀ hS (fun i => g₁⁻¹ *ᵥ bvec (eI k r (σ i))) (fun i => by
    rw [he]; exact hlen _)
  have hmat : (Matrix.of fun i i' : Fin l =>
      herm (Hpk k r) ((g₀ * (uEmb k r U * pOf k r q * g₁))⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl i')))
        (g₁⁻¹ *ᵥ bvec (eI k r (σ i)))) = ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) σ)ᴴ := by
    ext i i'
    rw [Matrix.of_apply, herm_inv_left hx, herm_symm, herm_e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (G_unit hg1), Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hPe]
    simp [bvec, Zr]
  rw [hmat, Matrix.det_conjTranspose, norm_star, hcr, norm_mul] at hp
  have hP0 : 0 < ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖ := norm_pos_iff.2 hD0
  have hpow : R₀ ^ l * R₀ ^ l ≤ R₀ ^ (2 * r) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hR (by omega)
  calc _ ≤ R₀ ^ (2 * r) * ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀' hP0]; exact hp.trans hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left hDb (by positivity)

end GlobalTheory.Amp.NfOff
