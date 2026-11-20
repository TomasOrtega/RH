import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedFrameProperty
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormBasics

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace FixedPointsGramVector

open C2x5 C2x6 C2x7 HermitianProjections

variable {k r : ℕ}

def phiL (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) where
  toFun y a := if h : a.val < r then y (eI k r ⟨a.val, h⟩) - y (esI k r ⟨a.val, h⟩) else y ⟨r + k, by omega⟩
  map_add' y y' := by
    funext a; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c y := by
    funext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/- English proof (translation)
Establish `hsw : ∀ a : Fin r, y (eI k r a) = y (esI k r a)`. Introduce `a`. Establish `h` using `congrFun hy ⟨a.val, by omega⟩`. Simplify using `only [phiL, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, a.isLt, dif_pos] at h`. Conclude with `sub_eq_zero.1 h`.

Establish `hw : y ⟨r + k, by omega⟩ = 0`. Establish `h` using `congrFun hy ⟨r, by omega⟩`. Simplify `h` using `[phiL]`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Break down `Nat.lt_or_ge i.val r with hi | hi` into its components or cases. Rewrite using `[Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]`. Establish `e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1`. Simplify using `only [Hpk]`. Rewrite using `[if_pos ⟨hi, by show (i : ℕ) + (2 * r + k - i) = 2 * r + k; omega⟩]`.

Rewrite using `[e, one_mul]`. Use `hsw ⟨i.val, hi⟩` as an intermediate fact. Simplify using `only [eI, esI] at this`. Rewrite using `[← this]`. Introduce `b _ hb`.

Establish `hb' : b.val ≠ 2 * r + k - i.val` using `fun h => hb (Fin.ext h)`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Break down `Nat.lt_or_ge i.val (r + k) with hi2 | hi2` into its components or cases. Rewrite using `[Finset.sum_eq_single i]`. Establish `e : Hpk k r i i = 1`. Simplify using `only [Hpk]`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨hi, by omega, trivial⟩, if_neg (by omega)]`.

Rewrite using `[e, one_mul]`. Introduce `b _ hb`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Break down `eq_or_lt_of_le hi2 with hi3 | hi3` into its components or cases. Establish `hi4 : i = ⟨r + k, by omega⟩` using `Fin.ext hi3.symm`. Rewrite using `[hi4, hw, Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]`. Rewrite using `[hw, mul_zero]`.

Introduce `b _ hb`. Establish `hb' : b.val ≠ r + k` using `fun h => hb (Fin.ext h)`. Simplify using `only [Hpk, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs with h1 h2 h3 <;> first | omega | simp`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Establish `hlt : 2 * r + k - i.val < r` using `by omega`. Rewrite using `[Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]`. Establish `e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1`. Simplify using `only [Hpk]`.

Rewrite using `[if_neg (by omega), if_pos ⟨hlt, by show (i : ℕ) + (2 * r + k - i) = 2 * r + k; omega⟩]`. Rewrite using `[e, one_mul]`. Use `hsw ⟨2 * r + k - i.val, hlt⟩` as an intermediate fact. Simplify using `only [eI, esI] at this`. Rewrite using `[this]`.

Use `congr 1`. Use `ext`. Use `show 2 * r + k - (2 * r + k - i.val) = i.val`. Use linear arithmetic over natural numbers and integers. Introduce `b _ hb`.

Establish `hb' : b.val ≠ 2 * r + k - i.val` using `fun h => hb (Fin.ext h)`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma Hpk_fix_of_phi (y : Fin (2 * r + k + 1) → ℂ) (hy : phiL k r y = 0) : Hpk k r *ᵥ y = y := by
  have hsw : ∀ a : Fin r, y (eI k r a) = y (esI k r a) := by
    intro a
    have h := congrFun hy ⟨a.val, by omega⟩
    simp only [phiL, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, a.isLt, dif_pos] at h
    exact sub_eq_zero.1 h
  have hw : y ⟨r + k, by omega⟩ = 0 := by
    have h := congrFun hy ⟨r, by omega⟩
    simpa [phiL] using h
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rcases Nat.lt_or_ge i.val r with hi | hi
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        simp only [Hpk]
        rw [if_pos ⟨hi, by show (i : ℕ) + (2 * r + k - i) = 2 * r + k; omega⟩]
      rw [e, one_mul]
      have := hsw ⟨i.val, hi⟩
      simp only [eI, esI] at this
      rw [← this]
    · intro b _ hb
      have hb' : b.val ≠ 2 * r + k - i.val := fun h => hb (Fin.ext h)
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h
  rcases Nat.lt_or_ge i.val (r + k) with hi2 | hi2
  · rw [Finset.sum_eq_single i]
    · have e : Hpk k r i i = 1 := by
        simp only [Hpk]
        rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hi, by omega, trivial⟩, if_neg (by omega)]
      rw [e, one_mul]
    · intro b _ hb
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h
  rcases eq_or_lt_of_le hi2 with hi3 | hi3
  · have hi4 : i = ⟨r + k, by omega⟩ := Fin.ext hi3.symm
    rw [hi4, hw, Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]
    · rw [hw, mul_zero]
    · intro b _ hb
      have hb' : b.val ≠ r + k := fun h => hb (Fin.ext h)
      simp only [Hpk, Fin.ext_iff, Fin.val_mk]
      split_ifs with h1 h2 h3 <;> first | omega | simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hlt : 2 * r + k - i.val < r := by omega
    rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        simp only [Hpk]
        rw [if_neg (by omega), if_pos ⟨hlt, by show (i : ℕ) + (2 * r + k - i) = 2 * r + k; omega⟩]
      rw [e, one_mul]
      have := hsw ⟨2 * r + k - i.val, hlt⟩
      simp only [eI, esI] at this
      rw [this]
      congr 1
      ext
      show 2 * r + k - (2 * r + k - i.val) = i.val
      omega
    · intro b _ hb
      have hb' : b.val ≠ 2 * r + k - i.val := fun h => hb (Fin.ext h)
      simp only [Hpk]
      split_ifs with h1 h2 h3 <;> simp_all [Fin.ext_iff] <;> omega
    · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `herm`. Rewrite using `[hy]`. Simplify using `only [dotProduct, Pi.star_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression.
-/
lemma herm_self_of_fix (y : Fin (2 * r + k + 1) → ℂ) (hy : Hpk k r *ᵥ y = y) :
    herm (Hpk k r) y y = ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) := by
  unfold herm
  rw [hy]
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/- English proof (translation)
Establish `hnn : ∀ j ∈ Finset.univ, 0 ≤ Complex.normSq (y j)` using `fun j _ => Complex.normSq_nonneg _`. Establish `h0 : ∑ i, Complex.normSq (y i) = 0` using `le_antisymm h (Finset.sum_nonneg hnn)`. Use function extensionality and compare the values at `i`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ _)`. Simplify using `using Complex.normSq_eq_zero.1 h1`.
-/
lemma eq_zero_of_sum_normSq_nonpos {n : ℕ} (y : Fin n → ℂ) (h : ∑ i, Complex.normSq (y i) ≤ 0) : y = 0 := by
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ Complex.normSq (y j) := fun j _ => Complex.normSq_nonneg _
  have h0 : ∑ i, Complex.normSq (y i) = 0 := le_antisymm h (Finset.sum_nonneg hnn)
  funext i
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (Finset.mem_univ _)
  simpa using Complex.normSq_eq_zero.1 h1

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gnB, Matrix.conjTranspose_apply]`.
-/
lemma of_star_gramVec (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (Matrix.of fun i j => star (gramVec k r z z' γ i j)) = (gnB k r z z' γ)ᴴ := by
  ext i j
  simp [gnB, Matrix.conjTranspose_apply]

/- English proof (translation)
Simplify using `only [C2.Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, of_star_gramVec]`.
-/
lemma mem_Uperp (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ C2.Uperp k r z z' γ ↔ ((gnB k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
  simp only [C2.Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, of_star_gramVec]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, gnB, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl (fun j _ => mul_comm _ _)`.
-/
lemma gnB_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    gnB k r z z' γ *ᵥ c = ∑ i, c i • gramVec k r z z' γ i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, gnB, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/- English proof (translation)
Rewrite using `[← gn_gramM_eq]`. Establish `h` using `group_gram_holds k r z z' hstd.2.1.1 hstd.2.2.1 γ hpos.1`. Apply `isUnit_iff_ne_zero.mpr` to reduce the goal to its premises. Introduce `h0`. Rewrite `h` using `[h0, mul_zero]`.

Use `hpos.2` as an intermediate fact. Establish `h' : (Gf k r z z' γ : ℂ) ≠ 0` using `by exact_mod_cast this.ne'`. Conclude with `h' h`.
-/
lemma gram_det (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hstd : C2.Std k r z z')
    (hpos : C2.PosPt k r z z' γ) : IsUnit ((gnB k r z z' γ)ᴴ * Hpk k r * gnB k r z z' γ).det := by
  rw [← gn_gramM_eq]
  have h := group_gram_holds k r z z' hstd.2.1.1 hstd.2.2.1 γ hpos.1
  apply isUnit_iff_ne_zero.mpr
  intro h0
  rw [h0, mul_zero] at h
  have := hpos.2
  have h' : (Gf k r z z' γ : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  exact h' h

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r` using `(hpkFacts k r).1`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]`.
-/
lemma gram_herm (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    ((gnB k r z z' γ)ᴴ * Hpk k r * gnB k r z z' γ)ᴴ = (gnB k r z z' γ)ᴴ * Hpk k r * gnB k r z z' γ := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]

end FixedPointsGramVector

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector

/- English proof (translation)
Introduce `k r z z' γ hstd hpos`. Use `set V := gnB k r z z' γ with hVd`. Use `set H := Hpk k r with hHd`. Use `set Γ := Vᴴ * H * V with hΓd`. Establish `hΓ : IsUnit Γ.det` using `gram_det z z' γ hstd hpos`.

Establish `hΓh : Γᴴ = Γ` using `gram_herm z z' γ`. Establish `hHh : Hᴴ = H` using `GBasic.Hpk_herm k r`. Establish `hgram : gramM k r z z' γ = Γ` using `gn_gramM_eq k r z z' γ`. Establish `hform : ∀ a b, herm H (V *ᵥ a) (V *ᵥ b) = star b ⬝ᵥ (Γ *ᵥ a)`. Introduce `a b`.

Rewrite using `[herm_mulVec]`. Establish `hli : LinearIndependent ℂ (gramVec k r z z' γ)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h1 : V *ᵥ g = 0` using `by rw [hVd, gnB_mulVec]; exact hg`.

Establish `h2 : Γ *ᵥ g = 0` using `by rw [hΓd, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]`. Establish `h3 : g = Γ⁻¹ *ᵥ (Γ *ᵥ g)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_mulVec]`. Rewrite using `[h3, h2, Matrix.mulVec_zero]`. Both sides reduce to the same expression.

Establish `hGB` using `gram_block_form k r z z' hstd.2.1 hstd.2.2 γ hpos.1`. Establish `h₁ : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ, LinearMap.funLeft ℂ ℂ Sum.inr c = 0 → (star c ⬝ᵥ (Γ *ᵥ c)).re ≤ 0`. Introduce `c hc`. Establish `hc' : ∀ b, c (Sum.inr b) = 0` using `fun b => congrFun hc b`. Rewrite using `[← hgram, hGB]`.

Establish `e : star c ⬝ᵥ (Matrix.fromBlocks (C2.Adiag k r z) (Zhat k r z z' γ) (Zhat k r z z' γ)ᴴ (C2.Adiag k r z') *ᵥ c) = ∑ a, star (c (Sum.inl a)) * (((if a = Fin.last r then -(Tz k r z) else 0 : ℝ) : ℂ) * c (Sum.inl a))`. Simplify using `only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hc', mul_zero, Finset.sum_const_zero, add_zero, Pi.star_apply, star_zero, zero_mul, C2.Adiag, Matrix.diagonal_apply]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[Finset.sum_eq_single a]`.

Apply the tactic sequence `simp only [if_true]; congr 1; split_ifs <;> simp`. Introduce `b _ hb`. Rewrite using `[if_neg (Ne.symm hb), zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[e, Complex.re_sum]`.

Apply `Finset.sum_nonpos` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[star_mul_real]`. Apply `mul_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)` to reduce the goal to its premises. Use `split_ifs`.

Combine the linear relations using `[hstd.2.1.2]`. Conclude with `le_refl _`. Establish `h₂ : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ, (phiL k r ∘ₗ Matrix.mulVecLin V) c = 0 → 0 ≤ (star c ⬝ᵥ (Γ *ᵥ c)).re`. Introduce `c hc`. Establish `hfix` using `Hpk_fix_of_phi (V *ᵥ c) hc`.

Rewrite using `[← hform, herm_self_of_fix _ hfix, Complex.ofReal_re]`. Conclude with `Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _`. Take `⟨Q, hQu, hQ⟩` from `sig_split Γ hΓh (isUnit_iff_ne_zero.mp hΓ) (LinearMap.funLeft ℂ ℂ Sum.inr) h₁ (phiL k r ∘ₗ Matrix.mulVecLin V) h₂`. Use `⟨hli, ⟨Q, hQu, by rw [hgram]; exact hQ⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv hv0`.

Rewrite `hv` using `[mem_Uperp]`. Assume the negation of the conclusion as `hneg`. Establish `hneg' : (herm H v v).re ≤ 0` using `not_lt.mp hneg`. Establish `hperp1 : ∀ d, herm H v (V *ᵥ d) = 0`. Introduce `d`.

Rewrite using `[herm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hv, dotProduct_zero]`. Establish `hperp2 : ∀ d, herm H (V *ᵥ d) v = 0`. Introduce `d`. Rewrite using `[ggHerm_swap H hHh, hperp1, star_zero]`. Apply the tactic sequence `set emb : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) ⊕ Fin (r + 1) → ℂ) := { toFun := fun c => Sum.elim 0 c map_add' := by intro a b; funext x; cases x <;> simp map_smul' := by intro a b; funext x; cases x <;> simp }`.

Use `set L : (Option (Fin (r + 1)) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) := phiL k r ∘ₗ (Matrix.mulVecLin (V * Q) ∘ₗ emb ∘ₗ LinearMap.funLeft ℂ ℂ some + LinearMap.smulRight (LinearMap.proj none) v)`. Establish `hne : LinearMap.ker L ≠ ⊥` using `LinearMap.ker_ne_bot_of_finrank_lt (by`. Rewrite using `[Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_option, Fintype.card_fin]`. Use the proof step `omega)`. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`.

Use `set c : Fin (r + 1) → ℂ := fun j => w (some j) with hcd`. Use `set t := w none with htd`. Use `set ct : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := Sum.elim 0 c with hctd`. Use `set x := (V * Q) *ᵥ ct + t • v with hxd`. Establish `hx : L w = phiL k r x`.

Simplify using `only [L, x, ct, c, t, emb, LinearMap.comp_apply, LinearMap.add_apply, Matrix.mulVecLin_apply, LinearMap.funLeft_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smulRight_apply, LinearMap.proj_apply]`. Both sides reduce to the same expression. Establish `hLx : phiL k r x = 0` using `by rw [← hx]; exact hw`. Establish `hfix` using `Hpk_fix_of_phi x hLx`. Establish `hVQ : (V * Q)ᴴ * H * (V * Q) = fromBlocks 1 0 0 (-1)`.

Rewrite using `[← hQ, Matrix.conjTranspose_mul, hΓd]`. Simplify using `only [Matrix.mul_assoc]`. Establish `haa : herm H ((V * Q) *ᵥ ct) ((V * Q) *ᵥ ct) = -∑ j, star (c j) * c j`. Rewrite using `[herm_mulVec, hVQ]`. Simplify using `[dotProduct, Matrix.mulVec, Fintype.sum_sum_type, ct, Matrix.one_apply, Matrix.neg_apply, Finset.sum_neg_distrib]`.

Establish `hp1 : herm H ((V * Q) *ᵥ ct) v = 0` using `by rw [← Matrix.mulVec_mulVec]; exact hperp2 _`. Establish `hp2 : herm H v ((V * Q) *ᵥ ct) = 0` using `by rw [← Matrix.mulVec_mulVec]; exact hperp1 _`. Establish `hxx : herm H x x = -∑ j, star (c j) * c j + t * conj t * herm H v v`. Rewrite using `[hxd, herm_add_left, herm_add_right, herm_add_right, haa, herm_smul_right, hp1, herm_smul_left, hp2, herm_smul_left, herm_smul_right]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hre` using `congrArg Complex.re hxx`. Rewrite `hre` using `[herm_self_of_fix _ hfix, Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.re_sum, Complex.mul_conj, Complex.re_ofReal_mul]`. Establish `hcs : ∀ j, (star (c j) * c j).re = Complex.normSq (c j)`. Introduce `j`. Rewrite using `[mul_comm, Complex.star_def, Complex.mul_conj]`.

Conclude with `Complex.ofReal_re _`. Simplify using `only [hcs] at hre`. Establish `hx0 : 0 ≤ ∑ i, Complex.normSq (x i)` using `Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _`. Establish `ht0 : Complex.normSq t * (herm H v v).re ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hneg'`. Establish `hc0 : c = 0` using `eq_zero_of_sum_normSq_nonpos c (by linarith)`.

Establish `hxz : x = 0` using `eq_zero_of_sum_normSq_nonpos x (by`. Establish `: ∑ j, Complex.normSq (c j) = 0` using `by rw [hc0]; simp`. Use the proof step `linarith)`. Apply the tactic sequence `have hct : ct = 0 := by rw [hctd, hc0]; funext y; cases y <;> rfl`. Rewrite `hxz` using `[hxd, hct, Matrix.mulVec_zero, zero_add]`.

Establish `ht : t = 0` using `(smul_eq_zero.mp hxz).resolve_right hv0`. Apply `hw0` to reduce the goal to its premises. Use function extensionality and compare the values at `o`. Consider the cases of `o with`. Consider the case `none => exact ht`.

Consider the case `some j => exact congrFun hc0 j`. Establish `hsurj : LinearMap.range (Matrix.mulVecLin (Vᴴ * H)) = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `c`. Use `⟨V *ᵥ (Γ⁻¹ *ᵥ c), ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, show Vᴴ * H * V * Γ⁻¹ = 1 from Matrix.mul_nonsing_inv _ hΓ, Matrix.one_mulVec]`. Establish `hrk` using `LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (Vᴴ * H))`. Rewrite `hrk` using `[hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]`. Unfold `C2.Uperp`. Rewrite using `[of_star_gramVec]`.

Use `show Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (Vᴴ * H))) = k - 1`. Establish `hk` using `hstd.1`. Use linear arithmetic over natural numbers and integers.
-/
theorem gram_independent_signature' : C2.GramIndependentSignature := by
  intro k r z z' γ hstd hpos
  set V := gnB k r z z' γ with hVd
  set H := Hpk k r with hHd
  set Γ := Vᴴ * H * V with hΓd
  have hΓ : IsUnit Γ.det := gram_det z z' γ hstd hpos
  have hΓh : Γᴴ = Γ := gram_herm z z' γ
  have hHh : Hᴴ = H := GBasic.Hpk_herm k r
  have hgram : gramM k r z z' γ = Γ := gn_gramM_eq k r z z' γ
  have hform : ∀ a b, herm H (V *ᵥ a) (V *ᵥ b) = star b ⬝ᵥ (Γ *ᵥ a) := by
    intro a b; rw [herm_mulVec]

  have hli : LinearIndependent ℂ (gramVec k r z z' γ) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : V *ᵥ g = 0 := by rw [hVd, gnB_mulVec]; exact hg
    have h2 : Γ *ᵥ g = 0 := by rw [hΓd, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    have h3 : g = Γ⁻¹ *ᵥ (Γ *ᵥ g) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hΓ, Matrix.one_mulVec]
    rw [h3, h2, Matrix.mulVec_zero]; rfl

  have hGB := gram_block_form k r z z' hstd.2.1 hstd.2.2 γ hpos.1
  have h₁ : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ, LinearMap.funLeft ℂ ℂ Sum.inr c = 0 →
      (star c ⬝ᵥ (Γ *ᵥ c)).re ≤ 0 := by
    intro c hc
    have hc' : ∀ b, c (Sum.inr b) = 0 := fun b => congrFun hc b
    rw [← hgram, hGB]
    have e : star c ⬝ᵥ (Matrix.fromBlocks (C2.Adiag k r z) (Zhat k r z z' γ) (Zhat k r z z' γ)ᴴ (C2.Adiag k r z') *ᵥ c) =
        ∑ a, star (c (Sum.inl a)) * (((if a = Fin.last r then -(Tz k r z) else 0 : ℝ) : ℂ) * c (Sum.inl a)) := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hc', mul_zero, Finset.sum_const_zero, add_zero,
        Pi.star_apply, star_zero, zero_mul, C2.Adiag, Matrix.diagonal_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single a]
      · simp only [if_true]; congr 1; split_ifs <;> simp
      · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
      · simp
    rw [e, Complex.re_sum]
    apply Finset.sum_nonpos
    intro a _
    rw [star_mul_real]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)
    split_ifs
    · linarith [hstd.2.1.2]
    · exact le_refl _
  have h₂ : ∀ c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ, (phiL k r ∘ₗ Matrix.mulVecLin V) c = 0 →
      0 ≤ (star c ⬝ᵥ (Γ *ᵥ c)).re := by
    intro c hc
    have hfix := Hpk_fix_of_phi (V *ᵥ c) hc
    rw [← hform, herm_self_of_fix _ hfix, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  obtain ⟨Q, hQu, hQ⟩ := sig_split Γ hΓh (isUnit_iff_ne_zero.mp hΓ) (LinearMap.funLeft ℂ ℂ Sum.inr) h₁
    (phiL k r ∘ₗ Matrix.mulVecLin V) h₂
  refine ⟨hli, ⟨Q, hQu, by rw [hgram]; exact hQ⟩, ?_, ?_⟩
  ·
    intro v hv hv0
    rw [mem_Uperp] at hv
    by_contra hneg
    have hneg' : (herm H v v).re ≤ 0 := not_lt.mp hneg
    have hperp1 : ∀ d, herm H v (V *ᵥ d) = 0 := by
      intro d
      rw [herm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hv, dotProduct_zero]
    have hperp2 : ∀ d, herm H (V *ᵥ d) v = 0 := by
      intro d
      rw [ggHerm_swap H hHh, hperp1, star_zero]
    set emb : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :=
      { toFun := fun c => Sum.elim 0 c
        map_add' := by intro a b; funext x; cases x <;> simp
        map_smul' := by intro a b; funext x; cases x <;> simp }
    set L : (Option (Fin (r + 1)) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
      phiL k r ∘ₗ (Matrix.mulVecLin (V * Q) ∘ₗ emb ∘ₗ LinearMap.funLeft ℂ ℂ some +
        LinearMap.smulRight (LinearMap.proj none) v)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
        Fintype.card_option, Fintype.card_fin]; omega)
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set c : Fin (r + 1) → ℂ := fun j => w (some j) with hcd
    set t := w none with htd
    set ct : Fin (r + 1) ⊕ Fin (r + 1) → ℂ := Sum.elim 0 c with hctd
    set x := (V * Q) *ᵥ ct + t • v with hxd
    have hx : L w = phiL k r x := by
      simp only [L, x, ct, c, t, emb, LinearMap.comp_apply, LinearMap.add_apply, Matrix.mulVecLin_apply,
        LinearMap.funLeft_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smulRight_apply, LinearMap.proj_apply]
      rfl
    have hLx : phiL k r x = 0 := by rw [← hx]; exact hw
    have hfix := Hpk_fix_of_phi x hLx
    have hVQ : (V * Q)ᴴ * H * (V * Q) = fromBlocks 1 0 0 (-1) := by
      rw [← hQ, Matrix.conjTranspose_mul, hΓd]; simp only [Matrix.mul_assoc]
    have haa : herm H ((V * Q) *ᵥ ct) ((V * Q) *ᵥ ct) = -∑ j, star (c j) * c j := by
      rw [herm_mulVec, hVQ]
      simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, ct, Matrix.one_apply, Matrix.neg_apply,
        Finset.sum_neg_distrib]
    have hp1 : herm H ((V * Q) *ᵥ ct) v = 0 := by rw [← Matrix.mulVec_mulVec]; exact hperp2 _
    have hp2 : herm H v ((V * Q) *ᵥ ct) = 0 := by rw [← Matrix.mulVec_mulVec]; exact hperp1 _
    have hxx : herm H x x = -∑ j, star (c j) * c j + t * conj t * herm H v v := by
      rw [hxd, herm_add_left, herm_add_right, herm_add_right, haa, herm_smul_right, hp1, herm_smul_left, hp2,
        herm_smul_left, herm_smul_right]
      ring
    have hre := congrArg Complex.re hxx
    rw [herm_self_of_fix _ hfix, Complex.ofReal_re, Complex.add_re, Complex.neg_re, Complex.re_sum,
      Complex.mul_conj, Complex.re_ofReal_mul] at hre
    have hcs : ∀ j, (star (c j) * c j).re = Complex.normSq (c j) := by
      intro j; rw [mul_comm, Complex.star_def, Complex.mul_conj]; exact Complex.ofReal_re _
    simp only [hcs] at hre
    have hx0 : 0 ≤ ∑ i, Complex.normSq (x i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have ht0 : Complex.normSq t * (herm H v v).re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hneg'
    have hc0 : c = 0 := eq_zero_of_sum_normSq_nonpos c (by linarith)
    have hxz : x = 0 := eq_zero_of_sum_normSq_nonpos x (by
      have : ∑ j, Complex.normSq (c j) = 0 := by rw [hc0]; simp
      linarith)
    have hct : ct = 0 := by rw [hctd, hc0]; funext y; cases y <;> rfl
    rw [hxd, hct, Matrix.mulVec_zero, zero_add] at hxz
    have ht : t = 0 := (smul_eq_zero.mp hxz).resolve_right hv0
    apply hw0
    funext o
    cases o with
    | none => exact ht
    | some j => exact congrFun hc0 j
  ·
    have hsurj : LinearMap.range (Matrix.mulVecLin (Vᴴ * H)) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      refine ⟨V *ᵥ (Γ⁻¹ *ᵥ c), ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        show Vᴴ * H * V * Γ⁻¹ = 1 from Matrix.mul_nonsing_inv _ hΓ, Matrix.one_mulVec]
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (Vᴴ * H))
    rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hrk
    unfold C2.Uperp
    rw [of_star_gramVec]
    show Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (Vᴴ * H))) = k - 1
    have hk := hstd.1
    omega

end Formalism.FourierDecayAlt.P
