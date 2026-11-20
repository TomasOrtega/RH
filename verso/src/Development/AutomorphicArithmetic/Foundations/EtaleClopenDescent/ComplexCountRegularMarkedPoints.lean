import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MarkWeightedFixedPointEqDefinitePairOdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSummandEqTermOfAOne

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.RootSumWeights GlobalTheory.CxUnfold
open scoped TensorProduct Classical

namespace UpperTheory.Cb.Mark

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ}

/- English proof (translation)
Establish `hF : FixL G v β y z` using `⟨μ, h⟩`. Unfold `eigL`. Rewrite using `[dif_pos hF]`. Establish `hc : hF.choose • z = μ • z` using `hF.choose_spec.symm.trans h`. Conclude with `smul_left_injective ℂ hz hc`.
-/
theorem eigL_of_eq {y : grp G β} {z : Fin G.n → ℂ} {μ : ℂ} (hz : z ≠ 0)
    (h : (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = μ • z) : eigL G v β y z = μ := by
  have hF : FixL G v β y z := ⟨μ, h⟩
  unfold eigL
  rw [dif_pos hF]
  have hc : hF.choose • z = μ • z := hF.choose_spec.symm.trans h
  exact smul_left_injective ℂ hz hc

/- English proof (translation)
Distinguish the cases in `hF : FixL G v β y z`. Take `⟨c, hc⟩` from `hF`. Establish `hc' : (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ (u • z) = c • (u • z)`. Rewrite using `[Matrix.mulVec_smul, hc, smul_comm]`. Rewrite using `[eigL_of_eq hz hc, eigL_of_eq (smul_ne_zero hu hz) hc']`.

Establish `hF' : ¬ FixL G v β y (u • z)`. Introduce and unpack `⟨c, hc⟩`. Apply `hF` to reduce the goal to its premises. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[Matrix.mulVec_smul, smul_comm c u z]`.

Conclude with `smul_right_injective _ hu hc`. Simplify using `only [eigL, dif_neg hF, dif_neg hF']`.
-/
theorem eigL_smul (y : grp G β) {z : Fin G.n → ℂ} (hz : z ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    eigL G v β y (u • z) = eigL G v β y z := by
  by_cases hF : FixL G v β y z
  · obtain ⟨c, hc⟩ := hF
    have hc' : (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ (u • z) = c • (u • z) := by
      rw [Matrix.mulVec_smul, hc, smul_comm]
    rw [eigL_of_eq hz hc, eigL_of_eq (smul_ne_zero hu hz) hc']
  · have hF' : ¬ FixL G v β y (u • z) := by
      rintro ⟨c, hc⟩
      apply hF
      refine ⟨c, ?_⟩
      rw [Matrix.mulVec_smul, smul_comm c u z] at hc
      exact smul_right_injective _ hu hc
    simp only [eigL, dif_neg hF, dif_neg hF']

/- English proof (translation)
Introduce `h0`. Apply `hz` to reduce the goal to its premises. Apply `toV_injective G v β η` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, h0, Matrix.mulVec_zero]`.
-/
theorem toV_ne_zero (η : grp G β) {z : Fin G.n → ℂ} (hz : z ≠ 0) :
    (toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z ≠ 0 := by
  intro h0
  apply hz
  apply toV_injective G v β η
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h0, Matrix.mulVec_zero]

/- English proof (translation)
Establish `conjFix : ∀ (g y' : grp G β) (z' : Fin G.n → ℂ) (c : ℂ), (toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z' = c • z' → (toV G v β (g * y' * g⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z') = c • ((toV G v β g : Matrix (Fin G.n) (Fin G. …`. Introduce `g y' z' c hc`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.mul_one, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]`.

Distinguish the cases in `hF : FixL G v β y z`. Take `⟨c, hc⟩` from `hF`. Rewrite using `[eigL_of_eq hz hc, eigL_of_eq (toV_ne_zero η hz) (conjFix η y z c hc)]`. Establish `hF' : ¬ FixL G v β (η * y * η⁻¹) ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)`. Introduce and unpack `⟨c, hc⟩`.

Apply `hF` to reduce the goal to its premises. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h2` using `conjFix η⁻¹ (η * y * η⁻¹) _ c hc`. Establish `e1 : η⁻¹ * (η * y * η⁻¹) * η⁻¹⁻¹ = y` using `by group`. Establish `e2 : (toV G v β η⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]`. Rewrite `h2` using `[e1, e2]`. Then use the resulting hypothesis. Simplify using `only [eigL, dif_neg hF, dif_neg hF']`.
-/
theorem eigL_conj (η y : grp G β) {z : Fin G.n → ℂ} (hz : z ≠ 0) :
    eigL G v β (η * y * η⁻¹) ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = eigL G v β y z := by
  have conjFix : ∀ (g y' : grp G β) (z' : Fin G.n → ℂ) (c : ℂ),
      (toV G v β y' : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z' = c • z' →
      (toV G v β (g * y' * g⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
        ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z') =
        c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z') := by
    intro g y' z' c hc
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]
  by_cases hF : FixL G v β y z
  · obtain ⟨c, hc⟩ := hF
    rw [eigL_of_eq hz hc, eigL_of_eq (toV_ne_zero η hz) (conjFix η y z c hc)]
  · have hF' : ¬ FixL G v β (η * y * η⁻¹) ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
      rintro ⟨c, hc⟩
      apply hF
      refine ⟨c, ?_⟩
      have h2 := conjFix η⁻¹ (η * y * η⁻¹) _ c hc
      have e1 : η⁻¹ * (η * y * η⁻¹) * η⁻¹⁻¹ = y := by group
      have e2 : (toV G v β η⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
          ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) = z := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
      rwa [e1, e2] at h2
    simp only [eigL, dif_neg hF, dif_neg hF']

def cxM (w : Polynomial G.F → ℂ → ℂ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t)
    (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (a : Ys G v β x t hx Kf K') (y : grp G β) : ℂ :=
  cxF G v (fun P => w P (eigL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))))
    β x t hx Kf f K' f' a y

section Inv

variable (w : Polynomial G.F → ℂ → ℂ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t)
  (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
  (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g)

include hf hf' in
/- English proof (translation)
Establish `hr` using `Projectivization.rep_nonzero a.2`. Take `⟨c, hc0, hc⟩` from `rep_smul G v β η a.2`. Establish `he : eigL G v β (η * y * η⁻¹) (Projectivization.rep (η • a).2) = eigL G v β y (Projectivization.rep a.2)` using `by show eigL G v β (η * y * η⁻¹) (Projectivization.rep (η • a.2)) = _`. Rewrite using `[hc, eigL_smul _ (toV_ne_zero η hr) hc0, eigL_conj η y hr]`. Unfold `cxM`.

Rewrite using `[he]`. Conclude with `GlobalTheory.T.pairWeight_invariant_form_group_conj p G v _ Kf f hf K' f' hf' β x t hx η a y`.
-/
theorem cxM_smul_conj (η : grp G β) (a : Ys G v β x t hx Kf K') (y : grp G β) :
    cxM w x t hx Kf f K' f' (η • a) (η * y * η⁻¹) = cxM w x t hx Kf f K' f' a y := by
  have hr := Projectivization.rep_nonzero a.2
  obtain ⟨c, hc0, hc⟩ := rep_smul G v β η a.2
  have he : eigL G v β (η * y * η⁻¹) (Projectivization.rep (η • a).2) =
      eigL G v β y (Projectivization.rep a.2) := by
    show eigL G v β (η * y * η⁻¹) (Projectivization.rep (η • a.2)) = _
    rw [hc, eigL_smul _ (toV_ne_zero η hr) hc0, eigL_conj η y hr]
  unfold cxM
  rw [he]
  exact GlobalTheory.T.pairWeight_invariant_form_group_conj p G v _ Kf f hf K' f' hf' β x t hx η a y

/- English proof (translation)
Unfold `cxF at h ⊢`. Use `split_ifs at h ⊢ with hc`. Rewrite using `[_root_.mul_one]`. Introduce `h0`. Apply `h` to reduce the goal to its premises.

Rewrite using `[h0, zero_mul]`. Conclude with `absurd rfl h`.
-/
theorem cxF_one_ne (wt : Polynomial G.F → ℂ) (a : Ys G v β x t hx Kf K') (y : grp G β)
    (h : cxF G v wt β x t hx Kf f K' f' a y ≠ 0) :
    cxF G v (fun _ => 1) β x t hx Kf f K' f' a y ≠ 0 := by
  unfold cxF at h ⊢
  split_ifs at h ⊢ with hc
  · rw [_root_.mul_one]
    intro h0
    apply h
    rw [h0, zero_mul]
  · exact absurd rfl h

include hf hf' in
/- English proof (translation)
Establish `hz` using `OrbitSumGen.posV_ne_zero G v β d.2`. Take `⟨c, hc⟩` from `Projectivization.exists_smul_eq_mk_rep ℂ d.2.1 hz`. Establish `he : eigL G v β y (Projectivization.rep (OrbitSumGen.pairOfDat G v β x t hx Kf K' d).2) = eigL G v β y d.2.1` using `by show eigL G v β y (Projectivization.mk ℂ d.2.1 hz).rep = _`. Rewrite using `[← hc, Units.smul_def, eigL_smul y hz c.ne_zero]`. Unfold `cxM`.

Rewrite using `[OrbitSumGen.cxF_pairOfDat G v β x t hx Kf K' _ f hf f' hf' d y, he]`.
-/
theorem cxM_dat (d : Dat G v β) (y : grp G β) :
    cxM w x t hx Kf f K' f' (OrbitSumGen.pairOfDat G v β x t hx Kf K' d) y =
      if FixL G v β y d.2.1 then
        f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) *
          w (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (eigL G v β y d.2.1)
      else 0 := by
  have hz := OrbitSumGen.posV_ne_zero G v β d.2
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ d.2.1 hz
  have he : eigL G v β y (Projectivization.rep (OrbitSumGen.pairOfDat G v β x t hx Kf K' d).2) =
      eigL G v β y d.2.1 := by
    show eigL G v β y (Projectivization.mk ℂ d.2.1 hz).rep = _
    rw [← hc, Units.smul_def, eigL_smul y hz c.ne_zero]
  unfold cxM
  rw [OrbitSumGen.cxF_pairOfDat G v β x t hx Kf K' _ f hf f' hf' d y, he]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Set.univ_inter, Set.inter_eq_right.mpr hsub]`. Use `_ = ∑ᶠ i ∈ Set.range π, W i := finsum_mem_inter_support _ _`. Use `_ = ∑ᶠ a, W (π a) := finsum_mem_range hπ`.
-/
private theorem finsum_eq_finsum_comp_of_injective_support {α ι : Type} (W : ι → ℂ) (π : α → ι) (hπ : Function.Injective π)
    (hsub : Function.support W ⊆ Set.range π) : ∑ᶠ i, W i = ∑ᶠ a, W (π a) := by
  calc ∑ᶠ i, W i = ∑ᶠ i ∈ Set.univ, W i := (finsum_mem_univ _).symm
    _ = ∑ᶠ i ∈ Set.univ ∩ Function.support W, W i := (finsum_mem_inter_support _ _).symm
    _ = ∑ᶠ i ∈ Set.range π ∩ Function.support W, W i := by
      rw [Set.univ_inter, Set.inter_eq_right.mpr hsub]
    _ = ∑ᶠ i ∈ Set.range π, W i := finsum_mem_inter_support _ _
    _ = ∑ᶠ a, W (π a) := finsum_mem_range hπ

include hf hf' in
/- English proof (translation)
Establish `hconj : ∀ (η : grp G β) (a : Ys G v β x t hx Kf K'), ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' (η • a) y = ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' a y`. Introduce `η a`. Rewrite using `[← finsum_comp_equiv (MulAut.conj η).toEquiv]`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `y`.

Conclude with `cxM_smul_conj w x t hx Kf f K' f' hf hf' η a y`. Establish `hcard : ∀ (η : grp G β) (a : Ys G v β x t hx Kf K'), Nat.card (MulAction.stabilizer (grp G β) (η • a)) = Nat.card (MulAction.stabilizer (grp G β) a)`. Introduce `η a`. Rewrite using `[MulAction.stabilizer_smul_eq_stabilizer_map_conj]`. Conclude with `Subgroup.card_map_of_injective (MulEquiv.injective _)`.

Establish `horb : ∀ a : Ys G v β x t hx Kf K', ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out (⟦a⟧ : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K')))) : ℕ) : ℂ)⁻¹ * ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' (Quotient.out (⟦a⟧ : MulAction.orbitRel.Quotient (grp G β) (Y …`. Introduce `a`. Take `⟨η, hη⟩ : ∃ η : grp G β, η • a = Quotient.out (⟦a⟧ : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K'))` from `Quotient.mk_out (s := MulAction.orbitRel (grp G β) (Ys G v β x t hx Kf K')) a`. Rewrite using `[← hη, hcard, hconj]`. Establish `hsub : Function.support (fun o : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') => ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' (Quotient.out o) y) ⊆ Set.range (OrbitSumGen.ptsToOrbit G v β x t h …`.

Introduce `o ho`. Rewrite `ho` using `[Function.mem_support]`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, cxM w x t hx Kf f K' f' (Quotient.out o) y ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Apply `ho` to reduce the goal to its premises. Simplify using `[hne]`. Unfold `cxM cxF at hy`. Use `split_ifs at hy with hc`. Establish `hp : OrbitSumGen.pairOfDat G v β x t hx Kf K' ((LeftCosets.rep _ _ (Quotient.out o).1, ⟨Projectivization.rep (Quotient.out o).2, hc.1⟩) : Dat G v β) = Quotient.out o`.

Unfold `OrbitSumGen.pairOfDat OrbitSumGen.lineOf`. Rewrite using `[LeftCosets.mk_rep]`. Conclude with `Prod.ext rfl (Projectivization.mk_rep _)`. Use `⟨Quot.mk _ ((LeftCosets.rep _ _ (Quotient.out o).1, ⟨Projectivization.rep (Quotient.out o).2, hc.1⟩) : Dat G v β), ?_⟩` and prove the remaining obligations. Use `show (⟦OrbitSumGen.pairOfDat G v β x t hx Kf K' _⟧ : MulAction.orbitRel.Quotient _ _) = o`.

Rewrite using `[hp]`. Conclude with `Quotient.out_eq o`. Conclude with `absurd rfl hy`. Unfold `cxSumAtM`. Rewrite using `[finsum_eq_finsum_comp_of_injective_support _ _ (OrbitSumGen.ptsToOrbit_injective G v β x t hx Kf K') hsub]`.

Apply `finsum_congr` to reduce the goal to its premises. Introduce `q`. Use `beta_reduce`. Rewrite using `[OrbitSumGen.ptsToOrbit_eq, horb, ← OrbitSumGen.card_stab_eq]`. Use `congr 1`.

Apply `finsum_congr` to reduce the goal to its premises. Introduce `y`. Rewrite using `[cxM_dat w x t hx Kf f K' f' hf hf']`.
-/
theorem cxSumAtM_orbit :
    cxSumAtM G v w β x t hx Kf f K' f' =
      ∑ᶠ o : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K'),
        ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o)) : ℕ) : ℂ)⁻¹ *
          ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' (Quotient.out o) y := by
  have hconj : ∀ (η : grp G β) (a : Ys G v β x t hx Kf K'),
      ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' (η • a) y = ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' a y := by
    intro η a
    rw [← finsum_comp_equiv (MulAut.conj η).toEquiv]
    apply finsum_congr
    intro y
    exact cxM_smul_conj w x t hx Kf f K' f' hf hf' η a y
  have hcard : ∀ (η : grp G β) (a : Ys G v β x t hx Kf K'),
      Nat.card (MulAction.stabilizer (grp G β) (η • a)) = Nat.card (MulAction.stabilizer (grp G β) a) := by
    intro η a
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  have horb : ∀ a : Ys G v β x t hx Kf K',
      ((Nat.card (MulAction.stabilizer (grp G β)
          (Quotient.out (⟦a⟧ : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K')))) : ℕ) : ℂ)⁻¹ *
        ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f'
          (Quotient.out (⟦a⟧ : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K'))) y =
      ((Nat.card (MulAction.stabilizer (grp G β) a) : ℕ) : ℂ)⁻¹ *
        ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' a y := by
    intro a
    obtain ⟨η, hη⟩ : ∃ η : grp G β,
        η • a = Quotient.out (⟦a⟧ : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K')) :=
      Quotient.mk_out (s := MulAction.orbitRel (grp G β) (Ys G v β x t hx Kf K')) a
    rw [← hη, hcard, hconj]
  have hsub : Function.support (fun o : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') =>
      ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o)) : ℕ) : ℂ)⁻¹ *
        ∑ᶠ y : grp G β, cxM w x t hx Kf f K' f' (Quotient.out o) y) ⊆
      Set.range (OrbitSumGen.ptsToOrbit G v β x t hx Kf K') := by
    intro o ho
    rw [Function.mem_support] at ho
    obtain ⟨y, hy⟩ : ∃ y, cxM w x t hx Kf f K' f' (Quotient.out o) y ≠ 0 := by
      by_contra hne
      push_neg at hne
      apply ho
      simp [hne]
    unfold cxM cxF at hy
    split_ifs at hy with hc
    · have hp : OrbitSumGen.pairOfDat G v β x t hx Kf K'
          ((LeftCosets.rep _ _ (Quotient.out o).1, ⟨Projectivization.rep (Quotient.out o).2, hc.1⟩) : Dat G v β) =
          Quotient.out o := by
        unfold OrbitSumGen.pairOfDat OrbitSumGen.lineOf
        rw [LeftCosets.mk_rep]
        exact Prod.ext rfl (Projectivization.mk_rep _)
      refine ⟨Quot.mk _ ((LeftCosets.rep _ _ (Quotient.out o).1,
        ⟨Projectivization.rep (Quotient.out o).2, hc.1⟩) : Dat G v β), ?_⟩
      show (⟦OrbitSumGen.pairOfDat G v β x t hx Kf K' _⟧ : MulAction.orbitRel.Quotient _ _) = o
      rw [hp]
      exact Quotient.out_eq o
    · exact absurd rfl hy
  unfold cxSumAtM
  rw [finsum_eq_finsum_comp_of_injective_support _ _ (OrbitSumGen.ptsToOrbit_injective G v β x t hx Kf K') hsub]
  apply finsum_congr
  intro q
  beta_reduce
  rw [OrbitSumGen.ptsToOrbit_eq, horb, ← OrbitSumGen.card_stab_eq]
  congr 1
  apply finsum_congr
  intro y
  rw [cxM_dat w x t hx Kf f K' f' hf hf']

def muOf (y : grp G β) : ℂ :=
  if h : ∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z then
    eigL G v β y h.choose else 0

def clsW (y : grp G β) : ℂ :=
  if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) then
    w (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (muOf (v := v) y) *
      pointSum ((toAfF G β x t hx).comp (Subgroup.centralizer {y}).subtype)
        ((toP1 G β).comp (Subgroup.centralizer {y}).subtype) (MonoidHom.id (Gr G 1)) Kf K'
        (toAfF G β x t hx y) (toP1 G β y) f f'
  else 0

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `at hz`.
-/
theorem posV_ne {z : Fin G.n → ℂ} (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) : z ≠ 0 := by
  rintro rfl
  simp at hz

include hf hf' in
/- English proof (translation)
Establish `hpt : ∀ a : Ys G v β x t hx Kf K', cxM w x t hx Kf f K' f' a y₀ = cxF G v (fun P => w P (muOf (v` using `v) y₀)) β x t hx Kf f K' f' a y₀ := by`. Introduce `a`. Unfold `cxM cxF`. Use `split_ifs with hc`. Distinguish the cases in `hfz : f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ * toAfF G β x t hx y₀ * (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1) = 0`.

Rewrite using `[hfz]`. Simplify using the standard rewrite rules. Establish `hex : ∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z` using `⟨_, hc⟩`. Establish `hmu : muOf (v` using `v) y₀ = eigL G v β y₀ hex.choose := by`. Unfold `muOf`.

Rewrite using `[dif_pos hex]`. Take `⟨c, hcz⟩` from `hu y₀ _ hfz _ _ hc.1 hex.choose_spec.1 hc.2 hex.choose_spec.2`. Establish `hz0 : Projectivization.rep a.2 ≠ 0` using `Projectivization.rep_nonzero _`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hcz` using `[zero_smul]`. Conclude with `posV_ne hex.choose_spec.1 hcz`. Rewrite using `[hmu, hcz, eigL_smul y₀ hz0 hc0]`. Both sides reduce to the same expression. Simplify using `only [hpt]`.

Rewrite using `[GlobalTheory.T.conjugacyClassPart_eq_weight_mul_kottwitzPointSum p G v _ Kf f hf K' f' hf' β x t hx hu y₀]`. Both sides reduce to the same expression.
-/
theorem cls_part
    (hu : ∀ (y₀ : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∀ z z' : Fin G.n → ℂ,
      0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re →
      FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z) (y₀ : grp G β) :
    ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (Ys G v β x t hx Kf K'),
      ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o) ⊓ Subgroup.centralizer {y₀} :
        Subgroup (grp G β)) : ℕ) : ℂ)⁻¹ * cxM w x t hx Kf f K' f' (Quotient.out o) y₀ =
      clsW (v := v) w x t hx Kf f K' f' y₀ := by
  have hpt : ∀ a : Ys G v β x t hx Kf K', cxM w x t hx Kf f K' f' a y₀ =
      cxF G v (fun P => w P (muOf (v := v) y₀)) β x t hx Kf f K' f' a y₀ := by
    intro a
    unfold cxM cxF
    split_ifs with hc
    · by_cases hfz : f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
          toAfF G β x t hx y₀ * (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1) = 0
      · rw [hfz]
        simp
      · have hex : ∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z := ⟨_, hc⟩
        have hmu : muOf (v := v) y₀ = eigL G v β y₀ hex.choose := by
          unfold muOf
          rw [dif_pos hex]
        obtain ⟨c, hcz⟩ := hu y₀ _ hfz _ _ hc.1 hex.choose_spec.1 hc.2 hex.choose_spec.2
        have hz0 : Projectivization.rep a.2 ≠ 0 := Projectivization.rep_nonzero _
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hcz
          exact posV_ne hex.choose_spec.1 hcz
        rw [hmu, hcz, eigL_smul y₀ hz0 hc0]
    · rfl
  simp only [hpt]
  rw [GlobalTheory.T.conjugacyClassPart_eq_weight_mul_kottwitzPointSum p G v _ Kf f hf K' f' hf' β x t hx hu y₀]
  rfl

include hf hf' in

/- English proof (translation)
Rewrite using `[cxSumAtM_orbit w x t hx Kf f K' f' hf hf']`. Establish `hinv : ∀ (η : grp G β) (a : Ys G v β x t hx Kf K') (γ : grp G β), cxM w x t hx Kf f K' f' (η • a) (η * γ * η⁻¹) = cxM w x t hx Kf f K' f' a γ` using `fun η a γ => cxM_smul_conj w x t hx Kf f K' f' hf hf' η a γ`. Establish `hsupp : ∀ a : Ys G v β x t hx Kf K', (Function.support (cxM w x t hx Kf f K' f' a)).Finite`. Introduce `a`. Use `(GlobalTheory.T.pairWeight_support_finite_of_finite_fixing p G v (fun _ => 1) Kf f hf K' f' hf' β x t hx hA a).subset ?_` and prove the remaining obligations.

Introduce `y hy`. Conclude with `cxF_one_ne x t hx Kf f K' f' (fun P => w P (eigL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))))) a y hy`. Establish `hfin : {o : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') | ∃ γ, cxM w x t hx Kf f K' f' (Quotient.out o) γ ≠ 0}.Finite`. Use `(GlobalTheory.T.finite_weightedPairOrbits_of_finite_weightedFixedPoints p G v (fun _ => 1) Kf f hf K' f' hf' β x t hx hB).subset ?_` and prove the remaining obligations. Introduce and unpack `o ⟨γ, hγ⟩`.

Conclude with `⟨γ, cxF_one_ne x t hx Kf f K' f' (fun P => w P (eigL G v β γ (Projectivization.rep ((Quotient.out o).2 : Projectivization ℂ (Fin G.n → ℂ))))) _ γ hγ⟩`. Rewrite using `[GlobalTheory.T.orbit_sum_conj_classes _ hinv hsupp hfin]`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `c`. Establish `hc : IsConj (Quotient.out c) (Classical.choose (ConjClasses.exists_rep c))`.

Rewrite using `[← ConjClasses.mk_eq_mk_iff_isConj, Classical.choose_spec (ConjClasses.exists_rep c)]`. Conclude with `Quotient.out_eq c`. Take `⟨g, hg⟩` from `isConj_iff.mp hc`. Rewrite using `[GlobalTheory.T.centralizer_orbit_sum_conjugate _ hinv (Quotient.out c) g, hg]`. Conclude with `cls_part w x t hx Kf f K' f' hf hf' hu _`.
-/
theorem cxSumAtM_unfold
    (hA : ∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re →
      Set.Finite {y : grp G β | FixL G v β y z ∧
        f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0})
    (hB : Set.Finite {q : Pts G v β x t hx Kf K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧
      f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
        f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0})
    (hu : ∀ (y₀ : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∀ z z' : Fin G.n → ℂ,
      0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re →
      FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z) :
    cxSumAtM G v w β x t hx Kf f K' f' =
      ∑ᶠ c : ConjClasses (grp G β),
        clsW (v := v) w x t hx Kf f K' f' (Classical.choose (ConjClasses.exists_rep c)) := by
  rw [cxSumAtM_orbit w x t hx Kf f K' f' hf hf']
  have hinv : ∀ (η : grp G β) (a : Ys G v β x t hx Kf K') (γ : grp G β),
      cxM w x t hx Kf f K' f' (η • a) (η * γ * η⁻¹) = cxM w x t hx Kf f K' f' a γ :=
    fun η a γ => cxM_smul_conj w x t hx Kf f K' f' hf hf' η a γ
  have hsupp : ∀ a : Ys G v β x t hx Kf K', (Function.support (cxM w x t hx Kf f K' f' a)).Finite := by
    intro a
    refine (GlobalTheory.T.pairWeight_support_finite_of_finite_fixing p G v (fun _ => 1) Kf f hf K' f' hf' β x t hx hA a).subset ?_
    intro y hy
    exact cxF_one_ne x t hx Kf f K' f'
      (fun P => w P (eigL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))))) a y hy
  have hfin : {o : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') |
      ∃ γ, cxM w x t hx Kf f K' f' (Quotient.out o) γ ≠ 0}.Finite := by
    refine (GlobalTheory.T.finite_weightedPairOrbits_of_finite_weightedFixedPoints p G v (fun _ => 1) Kf f hf K' f' hf' β x t hx hB).subset ?_
    rintro o ⟨γ, hγ⟩
    exact ⟨γ, cxF_one_ne x t hx Kf f K' f'
      (fun P => w P (eigL G v β γ (Projectivization.rep ((Quotient.out o).2 : Projectivization ℂ (Fin G.n → ℂ)))))
      _ γ hγ⟩
  rw [GlobalTheory.T.orbit_sum_conj_classes _ hinv hsupp hfin]
  apply finsum_congr
  intro c
  have hc : IsConj (Quotient.out c) (Classical.choose (ConjClasses.exists_rep c)) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, Classical.choose_spec (ConjClasses.exists_rep c)]
    exact Quotient.out_eq c
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  rw [GlobalTheory.T.centralizer_orbit_sum_conjugate _ hinv (Quotient.out c) g, hg]
  exact cls_part w x t hx Kf f K' f' hf hf' hu _

end Inv

open GlobalTheory.LKCx.Regroup

/- English proof (translation)
The claim follows from `cent_sim_pos p G P μ ha h _ P.self.2`.
-/
theorem pair_sim_pos (ha : G.a = 1) (P : Pair G) {μ : ℂ} (h : P.Mark μ) : 0 < ((P.c : ℚˣ) : ℚ) :=
  cent_sim_pos p G P μ ha h _ P.self.2

/- English proof (translation)
Take `⟨v', hv', x, hx, hpos⟩` from `h`. Establish `hvv : v' = v`. Establish `hcard : Fintype.card {u : InfinitePlace G.F // sigPosH (G.gram_herm u) = 1} = 1` using `ha`. Take `⟨e, he⟩` from `Fintype.card_eq_one_iff.mp hcard`. Establish `h1` using `he ⟨v', hv'⟩`.

Establish `h2` using `he ⟨v, hv⟩`. Conclude with `congrArg Subtype.val (h1.trans h2.symm)`. Rewrite `hx`, `hpos` using `[hvv]`. Establish `hr1 : (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P.γ` using `by rw [hr]`. Establish `hxv : (toV G v P.β r : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x = μ • x` using `by show (G.psi v (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *ᵥ x = μ • x`.

Rewrite using `[hr1]`. Conclude with `hx`. Establish `hpos' : 0 < (star x ⬝ᵥ (herm G v P.β *ᵥ x)).re` using `hpos`. Establish `hx0 : x ≠ 0` using `posV_ne hpos'`. Establish `hex : ∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z` using `⟨x, hpos', μ, hxv⟩`.

Unfold `muOf`. Rewrite using `[dif_pos hex]`. Take `⟨hz1, hz2⟩` from `hex.choose_spec`. Establish `hreg : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable`. Rewrite using `[hr1]`.

Conclude with `P.reg`. Take `⟨c, hc⟩` from `GlobalTheory.T.separable_formGroup_element_fixes_unique_positive_line p G v hv P.β P.sym P.trivR r hreg.1 hreg.2 x _ hpos' hz1 ⟨μ, hxv⟩ hz2`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[zero_smul]`.

Conclude with `posV_ne hz1 hc`. Rewrite using `[hc, eigL_smul r hx0 hc0, eigL_of_eq hx0 hxv]`.
-/
theorem muOf_eq_mark (ha : G.a = 1) (hv : sigPosH (G.gram_herm v) = 1) (P : Pair G) (r : grp G P.β)
    (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) {μ : ℂ} (h : P.Mark μ) : muOf (v := v) r = μ := by
  obtain ⟨v', hv', x, hx, hpos⟩ := h
  have hvv : v' = v := by
    have hcard : Fintype.card {u : InfinitePlace G.F // sigPosH (G.gram_herm u) = 1} = 1 := ha
    obtain ⟨e, he⟩ := Fintype.card_eq_one_iff.mp hcard
    have h1 := he ⟨v', hv'⟩
    have h2 := he ⟨v, hv⟩
    exact congrArg Subtype.val (h1.trans h2.symm)
  rw [hvv] at hx hpos
  have hr1 : (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P.γ := by rw [hr]
  have hxv : (toV G v P.β r : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x = μ • x := by
    show (G.psi v (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *ᵥ x = μ • x
    rw [hr1]
    exact hx
  have hpos' : 0 < (star x ⬝ᵥ (herm G v P.β *ᵥ x)).re := hpos
  have hx0 : x ≠ 0 := posV_ne hpos'
  have hex : ∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z :=
    ⟨x, hpos', μ, hxv⟩
  unfold muOf
  rw [dif_pos hex]
  obtain ⟨hz1, hz2⟩ := hex.choose_spec
  have hreg : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
    rw [hr1]
    exact P.reg
  obtain ⟨c, hc⟩ := GlobalTheory.T.separable_formGroup_element_fixes_unique_positive_line p G v hv P.β P.sym P.trivR r hreg.1 hreg.2 x _ hpos' hz1 ⟨μ, hxv⟩ hz2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact posV_ne hz1 hc
  rw [hc, eigL_smul r hx0 hc0, eigL_of_eq hx0 hxv]

/- English proof (translation)
Establish `hm : ((1 : G.Cˣ)⁻¹ * P.γ * 1, P.c) ∈ grp G P.β` using `GlobalTheory.T.conj_by_carrying_unit_mem_positiveSimilitudeFormGroup p G P P.β 1 1 one_pos (pair_sim_pos ha P h) (by simp [sh_one_eq])`. Simplify using `only [inv_one, _root_.one_mul, _root_.mul_one] at hm`. Rewrite using `[← muOf_eq_mark (v := v) ha hv P ⟨_, hm⟩ rfl h, muOf_eq_mark (v := v) ha hv P ⟨_, hm⟩ rfl h']`.
-/
theorem mark_unique (ha : G.a = 1) (hv : sigPosH (G.gram_herm v) = 1) (P : Pair G) {μ μ' : ℂ}
    (h : P.Mark μ) (h' : P.Mark μ') : μ = μ' := by
  have hm : ((1 : G.Cˣ)⁻¹ * P.γ * 1, P.c) ∈ grp G P.β :=
    GlobalTheory.T.conj_by_carrying_unit_mem_positiveSimilitudeFormGroup p G P P.β 1 1 one_pos (pair_sim_pos ha P h) (by simp [sh_one_eq])
  simp only [inv_one, _root_.one_mul, _root_.mul_one] at hm
  rw [← muOf_eq_mark (v := v) ha hv P ⟨_, hm⟩ rfl h, muOf_eq_mark (v := v) ha hv P ⟨_, hm⟩ rfl h']

def markTerm (w : Polynomial G.F → ℂ → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1))
    (f' : Gr G 1 → ℂ) (P : Pair G) : ℂ :=
  if h : ∃ μ, P.Mark μ then w P.pol h.choose * P.term Kf f 1 K' f' else 0

section Terms

variable (w : Polynomial G.F → ℂ → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1))
  (f' : Gr G 1 → ℂ) (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
  (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g)

include hf hf' in
/- English proof (translation)
Unfold `markTerm`. Establish `hiff : (∃ μ, P.Mark μ) ↔ (∃ μ, P'.Mark μ)` using `⟨fun ⟨μ, hμ⟩ => ⟨μ, (Pair.mark_iff_of_rel p G P P' μ h).mp hμ⟩, fun ⟨μ, hμ⟩ => ⟨μ, (Pair.mark_iff_of_rel p G P P' μ h).mpr hμ⟩⟩`. Distinguish the cases in `hM : ∃ μ, P.Mark μ`. Establish `hM'` using `hiff.mp hM`. Rewrite using `[dif_pos hM, dif_pos hM', (Pair.rel_pol_c p G P P' h).1, GlobalTheory.T.term_eq_of_similitude_rel p G P P' Kf f 1 K' f' one_pos hf hf' h]`.

Use `congr 2`. Conclude with `mark_unique ha hv P' hM'.choose_spec ((Pair.mark_iff_of_rel p G P P' _ h).mp hM.choose_spec)`. Rewrite using `[dif_neg hM, dif_neg (fun h' => hM (hiff.mpr h'))]`.
-/
theorem markTerm_rel (ha : G.a = 1) (hv : sigPosH (G.gram_herm v) = 1) {P P' : Pair G} (h : P.Rel P') :
    markTerm w Kf f K' f' P' = markTerm w Kf f K' f' P := by
  unfold markTerm
  have hiff : (∃ μ, P.Mark μ) ↔ (∃ μ, P'.Mark μ) :=
    ⟨fun ⟨μ, hμ⟩ => ⟨μ, (Pair.mark_iff_of_rel p G P P' μ h).mp hμ⟩,
      fun ⟨μ, hμ⟩ => ⟨μ, (Pair.mark_iff_of_rel p G P P' μ h).mpr hμ⟩⟩
  by_cases hM : ∃ μ, P.Mark μ
  · have hM' := hiff.mp hM
    rw [dif_pos hM, dif_pos hM', (Pair.rel_pol_c p G P P' h).1,
      GlobalTheory.T.term_eq_of_similitude_rel p G P P' Kf f 1 K' f' one_pos hf hf' h]
    congr 2
    exact mark_unique ha hv P' hM'.choose_spec ((Pair.mark_iff_of_rel p G P P' _ h).mp hM.choose_spec)
  · rw [dif_neg hM, dif_neg (fun h' => hM (hiff.mpr h'))]

include hf hf' in
/- English proof (translation)
Establish `key` using `CxReg.class_summand_eq_term_of_a_one p G ha v hv (fun q => w q (muOf (v := v) r)) Kf f K' f' hf hf' P x t hx r hr`. Unfold `clsW markTerm`. Rewrite using `[key]`. Use `split_ifs with hM`. Rewrite using `[muOf_eq_mark ha hv P r hr hM.choose_spec]`.

Both sides reduce to the same expression.
-/
theorem clsW_eq_markTerm (ha : G.a = 1) (hv : sigPosH (G.gram_herm v) = 1) (P : Pair G)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : grp G P.β)
    (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    clsW (v := v) w x t hx Kf f K' f' r = markTerm w Kf f K' f' P := by
  have key := CxReg.class_summand_eq_term_of_a_one p G ha v hv (fun q => w q (muOf (v := v) r)) Kf f K' f'
    hf hf' P x t hx r hr
  unfold clsW markTerm
  rw [key]
  split_ifs with hM
  · rw [muOf_eq_mark ha hv P r hr hM.choose_spec]
  · rfl

end Terms

def formCls (Q : Cls G) : FCls G := Quot.mk _ (formOf (Quot.out Q))

/- English proof (translation)
Establish `h1 : Quot.mk Form.Rel (Quot.out q) = Quot.mk Form.Rel (formOf (Quot.out Q))` using `(Quot.out_eq q).trans h.symm`. Take `⟨y, s, hs, he⟩` from `(GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic p G _ _).mp h1`. Conclude with `⟨y, s, hs, he⟩`.
-/
theorem carry_of_formCls {Q : Cls G} {q : FCls G} (h : formCls Q = q) :
    ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y) := by
  have h1 : Quot.mk Form.Rel (Quot.out q) = Quot.mk Form.Rel (formOf (Quot.out Q)) :=
    (Quot.out_eq q).trans h.symm
  obtain ⟨y, s, hs, he⟩ := (GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic p G _ _).mp h1
  exact ⟨y, s, hs, he⟩

/- English proof (translation)
Take `⟨y, s, hs, hβ⟩` from `carry_of_formCls h`. Conclude with `phi_spec q Q y s hs hβ (GlobalTheory.T.conj_by_carrying_unit_mem_positiveSimilitudeFormGroup p G _ _ y s hs hc hβ)`.
-/
theorem phi_of_formCls {Q : Cls G} {q : FCls G} (h : formCls Q = q) (hc : 0 < (((Quot.out Q).c : ℚˣ) : ℚ)) :
    ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧
      ((Quot.out Q).β : G.C) = algebraMap ℚ G.C s * (y * (Quot.out q).β * sh G y) ∧
      ∃ hm : ((y⁻¹ * (Quot.out Q).γ * y, (Quot.out Q).c) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out q).β,
        phi q Q = ConjClasses.mk ⟨_, hm⟩ := by
  obtain ⟨y, s, hs, hβ⟩ := carry_of_formCls h
  exact phi_spec q Q y s hs hβ (GlobalTheory.T.conj_by_carrying_unit_mem_positiveSimilitudeFormGroup p G _ _ y s hs hc hβ)

/- English proof (translation)
Establish `h1` using `congrArg (fun u : G.Cˣ => minpoly G.F (u : G.C)) e`. Simplify using `only [Units.val_mul, minpoly_units_conj] at h1`. Establish `h2` using `minpoly_units_conj (F := G.F) y⁻¹ (P.γ : G.C)`. Rewrite `h2` using `[inv_inv]`. Rewrite using `[h1, h2]`.

Conclude with `P.reg`.
-/
theorem reg_of_conj {B : G.Cˣ} (r g : grp G B) (P : Pair G) (y : G.Cˣ)
    (e : (g : G.Cˣ × ℚˣ).1 * (r : G.Cˣ × ℚˣ).1 * (g : G.Cˣ × ℚˣ).1⁻¹ = y⁻¹ * P.γ * y) :
    (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
  have h1 := congrArg (fun u : G.Cˣ => minpoly G.F (u : G.C)) e
  simp only [Units.val_mul, minpoly_units_conj] at h1
  have h2 := minpoly_units_conj (F := G.F) y⁻¹ (P.γ : G.C)
  rw [inv_inv] at h2
  rw [h1, h2]
  exact P.reg

/- English proof (translation)
Take `⟨hg1, hg2⟩` from `g.2`. Use `GlobalTheory.T.rel_of_conj_in_group_of_common_form p G (ofGrp F r hrg) P F.β 1 y (g : G.Cˣ × ℚˣ).1 1 s ((g : G.Cˣ × ℚˣ).2 : ℚ) one_pos hs hg2 ?_ hβ hg1 ?_` and prove the remaining obligations. Use `show (F.β : G.C) = _`. Simplify using `[sh_one_eq]`. Use `show _ * (1⁻¹ * (r : G.Cˣ × ℚˣ).1 * 1) * _ = _`.

Simplify using `using e`.
-/
theorem ofGrp_rel (F : Form G) (r g : grp G F.β)
    (hrg : (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable)
    (P : Pair G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : (P.β : G.C) = algebraMap ℚ G.C s * (y * F.β * sh G y))
    (e : (g : G.Cˣ × ℚˣ).1 * (r : G.Cˣ × ℚˣ).1 * (g : G.Cˣ × ℚˣ).1⁻¹ = y⁻¹ * P.γ * y) :
    (ofGrp F r hrg).Rel P := by
  obtain ⟨hg1, hg2⟩ := g.2
  refine GlobalTheory.T.rel_of_conj_in_group_of_common_form p G (ofGrp F r hrg) P F.β 1 y (g : G.Cˣ × ℚˣ).1 1 s ((g : G.Cˣ × ℚˣ).2 : ℚ)
    one_pos hs hg2 ?_ hβ hg1 ?_
  · show (F.β : G.C) = _
    simp [sh_one_eq]
  · show _ * (1⁻¹ * (r : G.Cˣ × ℚˣ).1 * 1) * _ = _
    simpa using e

/- English proof (translation)
Establish `e` using `congrArg (fun q : grp G B => (q : G.Cˣ × ℚˣ).1) h`. Simplify using `using e`.
-/
theorem conj_comp {B : G.Cˣ} {a b g : grp G B} (h : g * a * g⁻¹ = b) :
    (g : G.Cˣ × ℚˣ).1 * (a : G.Cˣ × ℚˣ).1 * (g : G.Cˣ × ℚˣ).1⁻¹ = (b : G.Cˣ × ℚˣ).1 := by
  have e := congrArg (fun q : grp G B => (q : G.Cˣ × ℚˣ).1) h
  simpa using e

/- English proof (translation)
Take `⟨y, s, hs, hβ, hm, hphi⟩` from `phi_of_formCls h hc`. Rewrite `hr` using `[hphi, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]`. Take `⟨g, hg⟩` from `hr`. Establish `e : (g : G.Cˣ × ℚˣ).1 * (r : G.Cˣ × ℚˣ).1 * (g : G.Cˣ × ℚˣ).1⁻¹ = y⁻¹ * (Quot.out Q).γ * y` using `conj_comp hg`. Establish `hrg` using `reg_of_conj r g (Quot.out Q) y e`.

Use `(clsW_eq_markTerm w Kf f K' f' hf hf' ha hv (ofGrp (Quot.out q) r hrg) _ _ (Quot.out q).trivAf.choose_spec.choose_spec r rfl).trans ?_` and prove the remaining obligations. Conclude with `(markTerm_rel w Kf f K' f' hf hf' ha hv (ofGrp_rel (Quot.out q) r g hrg (Quot.out Q) y s hs hβ e)).symm`.
-/
private theorem clsW_regroup_of_conj_invariant (ha : G.a = 1) (hv : sigPosH (G.gram_herm v) = 1)
    (w : Polynomial G.F → ℂ → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1))
    (f' : Gr G 1 → ℂ) (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) (Q : Cls G) (q : FCls G)
    (h : formCls Q = q) (hc : 0 < (((Quot.out Q).c : ℚˣ) : ℚ)) (r : grp G (Quot.out q).β)
    (hr : ConjClasses.mk r = phi q Q) :
    clsW (v := v) w (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
      (Quot.out q).trivAf.choose_spec.choose_spec Kf f K' f' r = markTerm w Kf f K' f' (Quot.out Q) := by
  obtain ⟨y, s, hs, hβ, hm, hphi⟩ := phi_of_formCls h hc
  rw [hphi, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hr
  obtain ⟨g, hg⟩ := hr
  have e : (g : G.Cˣ × ℚˣ).1 * (r : G.Cˣ × ℚˣ).1 * (g : G.Cˣ × ℚˣ).1⁻¹ = y⁻¹ * (Quot.out Q).γ * y :=
    conj_comp hg
  have hrg := reg_of_conj r g (Quot.out Q) y e
  refine (clsW_eq_markTerm w Kf f K' f' hf hf' ha hv (ofGrp (Quot.out q) r hrg) _ _
    (Quot.out q).trivAf.choose_spec.choose_spec r rfl).trans ?_
  exact (markTerm_rel w Kf f K' f' hf hf' ha hv
    (ofGrp_rel (Quot.out q) r g hrg (Quot.out Q) y s hs hβ e)).symm

/- English proof (translation)
Establish `hf0` using `hf.2.2.1`. Establish `hf'0` using `hf'.2.2.1`. Establish `hfK : ∀ k ∈ L.K.toSubgroup, ∀ g, f (k⁻¹ * g * k) = f g` using `fun k hk g => by simpa using hf0 k hk g`. Establish `hcpos : ∀ Q : Cls G, markTerm w L.K.toSubgroup f K' f' (Quot.out Q) ≠ 0 → 0 < (((Quot.out Q).c : ℚˣ) : ℚ)`. Introduce `Q hQ`.

Unfold `markTerm at hQ`. Use `split_ifs at hQ with hμ`. Conclude with `pair_sim_pos ha _ hμ.choose_spec`. Conclude with `absurd rfl hQ`. Use `show ∑ᶠ Q : Cls G, markTerm w L.K.toSubgroup f K' f' (Quot.out Q) = _`.

Use `GlobalTheory.T.finsum_eq_finsum_finsum_of_fibre_bij (κ := fun q : FCls G => ConjClasses (grp G (Quot.out q).β)) (fun Q : Cls G => markTerm w L.K.toSubgroup f K' f' (Quot.out Q)) (fun q c => clsW (v := v) w (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose (Quot.ou …` and prove the remaining obligations. Apply `(GlobalTheory.T.finite_markedPairClasses_degreeOne_term_ne_zero p G ha L f hf hreg K' f' hf').subset` to reduce the goal to its premises. Introduce `Q hQ`. Rewrite `hQ` using `[Function.mem_support]`. Unfold `markTerm at hQ`.

Use `split_ifs at hQ with hμ`. Conclude with `⟨hμ, right_ne_zero_of_mul hQ⟩`. Conclude with `absurd rfl hQ`. Introduce `Q hQ`. Conclude with `clsW_regroup_of_conj_invariant ha hv w _ f K' f' hfK hf'0 Q (formCls Q) rfl (hcpos Q hQ) _ (Classical.choose_spec (ConjClasses.exists_rep _))`.

Introduce `a a' ha0 ha'0 hπ hΦ`. Take `⟨y, s, hs, hβ, hm, hphi⟩` from `phi_of_formCls (rfl : formCls a = formCls a) (hcpos a ha0)`. Take `⟨y', s', hs', hβ', hm', hphi'⟩` from `phi_of_formCls hπ (hcpos a' ha'0)`. Establish `hΦ' : phi (formCls a) a = phi (formCls a) a'` using `hΦ`. Rewrite `hΦ'` using `[hphi, hphi', ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]`.

Take `⟨g, hg⟩` from `hΦ'`. Establish `e : (g : G.Cˣ × ℚˣ).1 * (y⁻¹ * (Quot.out a).γ * y) * (g : G.Cˣ × ℚˣ).1⁻¹ = y'⁻¹ * (Quot.out a').γ * y'` using `conj_comp hg`. Take `⟨hg1, hg2⟩` from `g.2`. Establish `hrel` using `GlobalTheory.T.rel_of_conj_in_group_of_common_form p G (Quot.out a) (Quot.out a') _ y y' _ s s' _ hs hs' hg2 hβ hβ' hg1 e`. Establish `hq : Quot.mk Pair.Rel (Quot.out a) = Quot.mk Pair.Rel (Quot.out a')` using `((Pair.mk_eq_iff_rel_and_out_rel p G _ _).1).mpr hrel`.

Conclude with `(Quot.out_eq a).symm.trans (hq.trans (Quot.out_eq a'))`. Introduce `i c hW`. Establish `hrc : ConjClasses.mk (Classical.choose (ConjClasses.exists_rep c)) = c` using `Classical.choose_spec (ConjClasses.exists_rep c)`. Use `set r := Classical.choose (ConjClasses.exists_rep c) with hr_def`. Establish `hW'` using `hW`.

Unfold `clsW at hW'`. Use `split_ifs at hW' with hz`. Use `swap`. Conclude with `absurd rfl hW'`. Take `⟨z, hzpos, hzfix⟩` from `hz`.

Establish `hps` using `right_ne_zero_of_mul hW'`. Unfold `pointSum at hps`. Establish `hps'` using `mt finsum_eq_zero_of_forall_eq_zero hps`. Use `push_neg at hps'`. Take `⟨qq, hqq⟩` from `hps'`.

Establish `hfne` using `left_ne_zero_of_mul (right_ne_zero_of_mul hqq)`. Establish `hrg` using `minpoly_of_regAf_of_fixL p G v hv (Quot.out i).β (Quot.out i).sym (Quot.out i).trivR _ _ (Quot.out i).trivAf.choose_spec.choose_spec r _ ⟨z, hzpos⟩ hzfix (hreg _ hfne)`. Use `set P := ofGrp (Quot.out i) r hrg with hP_def`. Establish `hrel0 : (Quot.out (Quot.mk Pair.Rel P : Cls G)).Rel P` using `(Pair.mk_eq_iff_rel_and_out_rel p G P P).2`. Use `set a : Cls G := Quot.mk Pair.Rel P with ha_def`.

Establish `hform : formCls a = i`. Take `⟨y, s, hs, hβ, -⟩` from `hrel0`. Establish `hR : (formOf (Quot.out a)).Rel (Quot.out i)` using `⟨y, s, hs, hβ⟩`. Conclude with `((GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic p G _ _).mpr hR).trans (Quot.out_eq i)`. Establish `hr2 : 0 < (((r : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)` using `r.2.2`.

Establish `hPc : P.c = (Quot.out a).c` using `(Pair.rel_pol_c p G _ _ hrel0).2`. Establish `hca : 0 < (((Quot.out a).c : ℚˣ) : ℚ)`. Rewrite using `[← hPc]`. Conclude with `hr2`. Take `⟨y₁, s₁, hs₁, hβ₁, hm₁, hphi₁⟩` from `phi_of_formCls hform hca`.

Take `⟨g, sg, hsg, hg, hγ⟩` from `GlobalTheory.T.exists_conj_of_rel_similitude_pairs_same_form p G (Quot.out a) P (Quot.out i).β y₁ 1 s₁ 1 hs₁ one_pos hβ₁ (by show ((Quot.out i).β : G.C) = _`. Simplify using `[sh_one_eq]) hrel0`. Establish `hmem : ((g, Units.mk0 sg (ne_of_gt hsg)) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out i).β` using `⟨by simpa using hg, by simpa using hsg⟩`. Establish `hphi_r : phi i a = ConjClasses.mk r`. Rewrite using `[hphi₁, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]`.

Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Rewrite using `[← show P.γ = (r : G.Cˣ × ℚˣ).1 from rfl]`. Simplify using `using hγ`.

Rewrite using `[← show P.c = (r : G.Cˣ × ℚˣ).2 from rfl, hPc]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv]`. Conclude with `mul_inv_cancel_comm _ _`. Use `⟨a, hform, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← clsW_regroup_of_conj_invariant ha hv w _ f K' f' hfK hf'0 a i hform hca r hphi_r.symm]`.

Conclude with `hW`. Use `show phi i a = c`. Rewrite using `[hphi_r, hrc]`.
-/
theorem markSumC_regroup (ha : G.a = 1) (hv : sigPosH (G.gram_herm v) = 1) (w : Polynomial G.F → ℂ → ℂ)
    (L : G.Level) (f : G.GAf → ℂ) (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f') :
    markSumC G w L.K.toSubgroup f K' f' =
      ∑ᶠ q : FCls G, ∑ᶠ c : ConjClasses (grp G (Quot.out q).β),
        clsW (v := v) w (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
          (Quot.out q).trivAf.choose_spec.choose_spec L.K.toSubgroup f K' f'
          (Classical.choose (ConjClasses.exists_rep c)) := by
  have hf0 := hf.2.2.1
  have hf'0 := hf'.2.2.1
  have hfK : ∀ k ∈ L.K.toSubgroup, ∀ g, f (k⁻¹ * g * k) = f g := fun k hk g => by simpa using hf0 k hk g
  have hcpos : ∀ Q : Cls G, markTerm w L.K.toSubgroup f K' f' (Quot.out Q) ≠ 0 →
      0 < (((Quot.out Q).c : ℚˣ) : ℚ) := by
    intro Q hQ
    unfold markTerm at hQ
    split_ifs at hQ with hμ
    · exact pair_sim_pos ha _ hμ.choose_spec
    · exact absurd rfl hQ
  show ∑ᶠ Q : Cls G, markTerm w L.K.toSubgroup f K' f' (Quot.out Q) = _
  refine GlobalTheory.T.finsum_eq_finsum_finsum_of_fibre_bij (κ := fun q : FCls G => ConjClasses (grp G (Quot.out q).β))
    (fun Q : Cls G => markTerm w L.K.toSubgroup f K' f' (Quot.out Q))
    (fun q c => clsW (v := v) w (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
      (Quot.out q).trivAf.choose_spec.choose_spec L.K.toSubgroup f K' f'
      (Classical.choose (ConjClasses.exists_rep c)))
    formCls (fun q Q => phi q Q) ?_ ?_ ?_ ?_
  · apply (GlobalTheory.T.finite_markedPairClasses_degreeOne_term_ne_zero p G ha L f hf hreg K' f' hf').subset
    intro Q hQ
    rw [Function.mem_support] at hQ
    unfold markTerm at hQ
    split_ifs at hQ with hμ
    · exact ⟨hμ, right_ne_zero_of_mul hQ⟩
    · exact absurd rfl hQ
  · intro Q hQ
    exact clsW_regroup_of_conj_invariant ha hv w _ f K' f' hfK hf'0 Q (formCls Q) rfl (hcpos Q hQ) _
      (Classical.choose_spec (ConjClasses.exists_rep _))
  · intro a a' ha0 ha'0 hπ hΦ
    obtain ⟨y, s, hs, hβ, hm, hphi⟩ := phi_of_formCls (rfl : formCls a = formCls a) (hcpos a ha0)
    obtain ⟨y', s', hs', hβ', hm', hphi'⟩ := phi_of_formCls hπ (hcpos a' ha'0)
    have hΦ' : phi (formCls a) a = phi (formCls a) a' := hΦ
    rw [hphi, hphi', ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hΦ'
    obtain ⟨g, hg⟩ := hΦ'
    have e : (g : G.Cˣ × ℚˣ).1 * (y⁻¹ * (Quot.out a).γ * y) * (g : G.Cˣ × ℚˣ).1⁻¹ =
        y'⁻¹ * (Quot.out a').γ * y' := conj_comp hg
    obtain ⟨hg1, hg2⟩ := g.2
    have hrel := GlobalTheory.T.rel_of_conj_in_group_of_common_form p G (Quot.out a) (Quot.out a') _ y y' _ s s' _ hs hs' hg2 hβ hβ' hg1 e
    have hq : Quot.mk Pair.Rel (Quot.out a) = Quot.mk Pair.Rel (Quot.out a') :=
      ((Pair.mk_eq_iff_rel_and_out_rel p G _ _).1).mpr hrel
    exact (Quot.out_eq a).symm.trans (hq.trans (Quot.out_eq a'))
  · intro i c hW
    have hrc : ConjClasses.mk (Classical.choose (ConjClasses.exists_rep c)) = c :=
      Classical.choose_spec (ConjClasses.exists_rep c)
    set r := Classical.choose (ConjClasses.exists_rep c) with hr_def
    have hW' := hW
    unfold clsW at hW'
    split_ifs at hW' with hz
    swap
    · exact absurd rfl hW'
    obtain ⟨z, hzpos, hzfix⟩ := hz
    have hps := right_ne_zero_of_mul hW'
    unfold pointSum at hps
    have hps' := mt finsum_eq_zero_of_forall_eq_zero hps
    push_neg at hps'
    obtain ⟨qq, hqq⟩ := hps'
    have hfne := left_ne_zero_of_mul (right_ne_zero_of_mul hqq)
    have hrg := minpoly_of_regAf_of_fixL p G v hv (Quot.out i).β (Quot.out i).sym (Quot.out i).trivR _ _
      (Quot.out i).trivAf.choose_spec.choose_spec r _ ⟨z, hzpos⟩ hzfix (hreg _ hfne)
    set P := ofGrp (Quot.out i) r hrg with hP_def
    have hrel0 : (Quot.out (Quot.mk Pair.Rel P : Cls G)).Rel P :=
      (Pair.mk_eq_iff_rel_and_out_rel p G P P).2
    set a : Cls G := Quot.mk Pair.Rel P with ha_def
    have hform : formCls a = i := by
      obtain ⟨y, s, hs, hβ, -⟩ := hrel0
      have hR : (formOf (Quot.out a)).Rel (Quot.out i) := ⟨y, s, hs, hβ⟩
      exact ((GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic p G _ _).mpr hR).trans (Quot.out_eq i)
    have hr2 : 0 < (((r : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := r.2.2
    have hPc : P.c = (Quot.out a).c := (Pair.rel_pol_c p G _ _ hrel0).2
    have hca : 0 < (((Quot.out a).c : ℚˣ) : ℚ) := by
      rw [← hPc]
      exact hr2
    obtain ⟨y₁, s₁, hs₁, hβ₁, hm₁, hphi₁⟩ := phi_of_formCls hform hca
    obtain ⟨g, sg, hsg, hg, hγ⟩ := GlobalTheory.T.exists_conj_of_rel_similitude_pairs_same_form p G (Quot.out a) P (Quot.out i).β y₁ 1 s₁ 1 hs₁ one_pos hβ₁
      (by
        show ((Quot.out i).β : G.C) = _
        simp [sh_one_eq]) hrel0
    have hmem : ((g, Units.mk0 sg (ne_of_gt hsg)) : G.Cˣ × ℚˣ) ∈ grp G (Quot.out i).β :=
      ⟨by simpa using hg, by simpa using hsg⟩
    have hphi_r : phi i a = ConjClasses.mk r := by
      rw [hphi₁, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      refine ⟨⟨_, hmem⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rw [← show P.γ = (r : G.Cˣ × ℚˣ).1 from rfl]
        simpa using hγ
      · rw [← show P.c = (r : G.Cˣ × ℚˣ).2 from rfl, hPc]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv]
        exact mul_inv_cancel_comm _ _
    refine ⟨a, hform, ?_, ?_⟩
    · rw [← clsW_regroup_of_conj_invariant ha hv w _ f K' f' hfK hf'0 a i hform hca r hphi_r.symm]
      exact hW
    · show phi i a = c
      rw [hphi_r, hrc]

end UpperTheory.Cb.Mark

open UpperTheory.Cb.Mark in
/- English proof (translation)
Introduce `p _ G ha v hv c L f hf hreg K' f' hf'`. Unfold `cxTotalM`. Rewrite using `[markSumC_regroup (v := v) ha hv c L f hf hreg K' f' hf']`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `q`.

Establish `hfK : ∀ k ∈ (L.K : Subgroup G.GAf), ∀ g, f (k⁻¹ * g * k) = f g`. Introduce `k hk g`. Simplify using `using hf.2.2.1 k hk g`. Establish `hfK' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g`. Introduce `k hk g`.

Simplify `hf'.2.2.1 k hk g` using `[sigG_one]`. Unfold `cxSumM`. Conclude with `cxSumAtM_unfold c _ _ _ (L.K : Subgroup G.GAf) f K' f' hfK hfK' (fun h z hz => GlobalTheory.FinFix.finite_fix_core G ha v hv L f hf K' f' hf' _ _ _ _ (Quot.out q).sym (Quot.out q).trivR h z hz) (CxReg.finite_pts_reg G ha v hv L f hf hreg K' f' hf' _ _ _ _ (Quot.out q).sym (Quot.o …`. Take `⟨hd, hs⟩` from `CxReg.sep_of_regAf G v hv f hreg _ _ _ _ (Quot.out q).sym (Quot.out q).trivR y₀ h hne ⟨z, hz, hF⟩`. Conclude with `GlobalTheory.T.separable_formGroup_element_fixes_unique_positive_line p G v hv _ (Quot.out q).sym (Quot.out q).trivR y₀ hd hs z z' hz hz' hF hF')`.
-/
theorem UpperTheory.Cb.complex_count_regular_marked_points :
    GlobalTheory.RootSumWeights.CxCountRegMark := by
  intro p _ G ha v hv c L f hf hreg K' f' hf'
  unfold cxTotalM
  rw [markSumC_regroup (v := v) ha hv c L f hf hreg K' f' hf']
  apply finsum_congr
  intro q
  have hfK : ∀ k ∈ (L.K : Subgroup G.GAf), ∀ g, f (k⁻¹ * g * k) = f g := by
    intro k hk g
    simpa using hf.2.2.1 k hk g
  have hfK' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g := by
    intro k hk g
    simpa [sigG_one] using hf'.2.2.1 k hk g
  unfold cxSumM
  exact cxSumAtM_unfold c _ _ _ (L.K : Subgroup G.GAf) f K' f' hfK hfK'
    (fun h z hz => GlobalTheory.FinFix.finite_fix_core G ha v hv L f hf K' f' hf' _ _ _ _ (Quot.out q).sym (Quot.out q).trivR h z hz)
    (CxReg.finite_pts_reg G ha v hv L f hf hreg K' f' hf' _ _ _ _ (Quot.out q).sym (Quot.out q).trivR)
    (fun y₀ h hne z z' hz hz' hF hF' => by
      obtain ⟨hd, hs⟩ := CxReg.sep_of_regAf G v hv f hreg _ _ _ _ (Quot.out q).sym (Quot.out q).trivR y₀ h hne ⟨z, hz, hF⟩
      exact GlobalTheory.T.separable_formGroup_element_fixes_unique_positive_line p G v hv _ (Quot.out q).sym (Quot.out q).trivR y₀ hd hs z z' hz hz' hF hF')
