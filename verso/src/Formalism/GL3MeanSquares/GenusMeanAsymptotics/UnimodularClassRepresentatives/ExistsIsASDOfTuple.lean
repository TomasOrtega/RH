import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTuple

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA Module

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

/- English proof (translation)
Establish `hg : (gram h fun i => d i • y i) = Matrix.diagonal fun i => star (d i) * d i * h (y i) (y i)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[gram]`.

Simplify using `only [starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]`. Rewrite using `[hg, Matrix.det_diagonal, Finset.prod_mul_distrib]`.
-/
theorem gram_det_smul_orth {n : ℕ} {y : Fin n → V} (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0)
    (d : Fin n → K) :
    (gram h fun i => d i • y i).det = (∏ i, star (d i) * d i) * ∏ i, h (y i) (y i) := by
  have hg : (gram h fun i => d i • y i) =
      Matrix.diagonal fun i => star (d i) * d i * h (y i) (y i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gram]
      simp only [starRingEnd_apply]
      ring
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hg, Matrix.det_diagonal, Finset.prod_mul_distrib]

/- English proof (translation)
Establish `hg : gram h y = Matrix.diagonal fun i => h (y i) (y i)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[gram]`.

Simplify using `[gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]`. Rewrite using `[hg, Matrix.det_diagonal]`.
-/
theorem gram_det_orth {n : ℕ} {y : Fin n → V} (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) :
    (gram h y).det = ∏ i, h (y i) (y i) := by
  have hg : gram h y = Matrix.diagonal fun i => h (y i) (y i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gram]
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hg, Matrix.det_diagonal]

/- English proof (translation)
Establish `hli : LinearIndependent K y`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`. Establish `hj` using `congrArg (h (y j)) hg`. Simplify using `only [map_sum, map_smul, smul_eq_mul, map_zero] at hj`.

Rewrite `hj` using `[Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero]) (by simp)]`. Conclude with `(mul_eq_zero.mp hj).resolve_right (hne j)`. Distinguish the cases in `h0 : finrank K V = 0`. Use `haveI : Subsingleton V := Module.finrank_zero_iff.mp h0`. Conclude with `Subsingleton.elim _ _`.

Use `haveI : Nonempty (Fin (finrank K V)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩`. Use `set b := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _) with hb`. Establish `hbi : ∀ i, b i = y i` using `fun i => by`. Rewrite using `[hb, coe_basisOfLinearIndependentOfCardEqFinrank]`. Establish `hv : ∑ i, b.repr v i • y i = v`.

Repeatedly rewrite using `[← hbi]`. Conclude with `b.sum_repr v`. Establish `hc : ∀ j, b.repr v j = h (y j) v * (h (y j) (y j))⁻¹`. Introduce `j`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ (hne j)]`.

Establish `hj` using `congrArg (h (y j)) hv`. Simplify using `only [map_sum, map_smul, smul_eq_mul] at hj`. Rewrite `hj` using `[Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero]) (by simp)]`. Conclude with `hj`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem expand_orth [FiniteDimensional K V] {y : Fin (finrank K V) → V}
    (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) (hne : ∀ i, h (y i) (y i) ≠ 0) (v : V) :
    v = ∑ i, (h (y i) v * (h (y i) (y i))⁻¹) • y i := by
  have hli : LinearIndependent K y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hj := congrArg (h (y j)) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact (mul_eq_zero.mp hj).resolve_right (hne j)
  by_cases h0 : finrank K V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact Subsingleton.elim _ _
  haveI : Nonempty (Fin (finrank K V)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
  set b := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _) with hb
  have hbi : ∀ i, b i = y i := fun i => by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hv : ∑ i, b.repr v i • y i = v := by
    simp_rw [← hbi]
    exact b.sum_repr v
  have hc : ∀ j, b.repr v j = h (y j) v * (h (y j) (y j))⁻¹ := by
    intro j
    rw [eq_mul_inv_iff_mul_eq₀ (hne j)]
    have hj := congrArg (h (y j)) hv
    simp only [map_sum, map_smul, smul_eq_mul] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact hj
  calc v = ∑ i, b.repr v i • y i := hv.symm
    _ = _ := Finset.sum_congr rfl fun i _ => by rw [hc i]

/- English proof (translation)
Take `⟨y, horth, hspan⟩` from `exists_orth_tuple hS hπ hs _ x (fun i j => hM.int _ (hx i) _ (hx j)) hdet`. Establish `hyM : ∀ i, y i ∈ M`. Introduce `i`. Establish `h1 : y i ∈ spanS S x` using `by rw [← hspan]; exact mem_spanS y i`. Conclude with `spanS_induction (p := fun v => v ∈ M) M.zero_mem (fun a b => M.add_mem) (fun c hc a ha => hM.smul_mem c hc a ha) hx _ h1`.

Establish `haS : ∀ i, h (y i) (y i) ∈ S` using `fun i => hM.int _ (hyM i) _ (hyM i)`. Take `⟨c, hcS, hcdet⟩` from `gram_det_of_le (h := h) hS (fun i => by rw [hspan]; exact mem_spanS x i : ∀ i, x i ∈ spanS S y)`. Rewrite `hcdet` using `[gram_det_orth horth]`. Establish `hPd : Dv S π (∏ i, h (y i) (y i))`. Rewrite using `[← gram_det_orth horth]`.

Conclude with `hall y hyM horth`. Establish `hPn : ¬ Dv S π ((∏ i, h (y i) (y i)) * π⁻¹)`. Introduce `hdv`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[hcdet, mul_assoc]`.

Conclude with `hdv.mul_left hcS`. Establish `hPf : star ((∏ i, h (y i) (y i)) * π⁻¹) = (∏ i, h (y i) (y i)) * π⁻¹`. Rewrite using `[star_mul', star_inv₀, hπ.fix, ← starRingEnd_apply, map_prod]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun i _ => hs.eq _ _`.

Establish `hPu : IsUnitIn S ((∏ i, h (y i) (y i)) * π⁻¹)` using `unit_of_not_dv hπ hPd hPf hPn`. Choose the witnesses or unpack the hypotheses as in `⟨i₁, hi₁⟩ : ∃ i₁, ¬ IsUnitIn S (h (y i₁) (y i₁)) := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `unit_not_dv hπ (LocF.isUnitIn_prod Finset.univ _ fun i _ => hcon i) hPd`.

Establish `hd₁ : Dv S π (h (y i₁) (y i₁))` using `dv_of_not_unit hπ (haS i₁) (hs.eq _ _) hi₁`. Establish `hQS : ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) ∈ S` using `S.prod_mem fun i _ => haS i`. Establish `hsplit : (∏ i, h (y i) (y i)) * π⁻¹ = h (y i₁) (y i₁) * π⁻¹ * ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i)`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hQu : IsUnitIn S (∏ i ∈ Finset.univ.erase i₁, h (y i) (y i))` using `isUnitIn_of_mul hd₁ hQS (hsplit ▸ hPu)`. Establish `hzu : IsUnitIn S (h (y i₁) (y i₁) * π⁻¹)` using `isUnitIn_of_mul hQS hd₁ (by rw [mul_comm, ← hsplit]; exact hPu)`. Establish `hau : ∀ i, i ≠ i₁ → IsUnitIn S (h (y i) (y i))`. Introduce `i hi`. Establish `hmem : i ∈ Finset.univ.erase i₁` using `Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩`.

Establish `e` using `Finset.mul_prod_erase (Finset.univ.erase i₁) (fun i => h (y i) (y i)) hmem`. Use `isUnitIn_of_mul (S.prod_mem fun j _ => haS j : ∏ j ∈ (Finset.univ.erase i₁).erase i, h (y j) (y j) ∈ S) (haS i) ?_` and prove the remaining obligations. Rewrite using `[mul_comm, e]`. Conclude with `hQu`. Establish `hne : ∀ i, h (y i) (y i) ≠ 0`.

Introduce `i`. Distinguish the cases in `hi : i = i₁`. Rewrite using `[hi]`. Conclude with `left_ne_zero_of_mul hzu.1`. Conclude with `(hau i hi).1`.

Establish `hexp` using `expand_orth horth hne`. Establish `hprim : ∀ c : K, c • y i₁ ∈ M → c ∈ S`. Establish `hy0 : y i₁ ≠ 0`. Introduce `h0`. Apply `hne i₁` to reduce the goal to its premises.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Take `⟨l, hl0, hl, hdiv⟩` from `exists_primitive hS hd hM (Submodule.mem_top : y i₁ ∈ ⊤) hy0`. Establish `hli : l⁻¹ ∈ S`. Use `hdiv 1 (by rw [one_smul]; exact hyM i₁)` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Establish `hNl : star l * l ∈ S`. Establish `h1` using `hall (fun i => (if i = i₁ then l else 1) • y i) (by`. Introduce `i`. Distinguish the cases in `hi : i = i₁`.

Simplify using `only [hi, if_true]`. Conclude with `hl`. Simplify using `only [hi, if_false, one_smul]; exact hyM i) (by`. Introduce `i j hij`. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero])`.

Rewrite `h1` using `[gram_det_smul_orth horth]`. Establish `e : (∏ i, star (if i = i₁ then l else 1) * (if i = i₁ then l else 1)) = star l * l`. Rewrite using `[Finset.prod_eq_single i₁]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[hj]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i₁) hi`. Rewrite `h1` using `[e]`. Unfold `Dv at h1`.

Establish `h2` using `S.mul_mem h1 hPu.2.2`. Establish `h0` using `hPu.1`. Establish `e2 : star l * l * (∏ i, h (y i) (y i)) * π⁻¹ * ((∏ i, h (y i) (y i)) * π⁻¹)⁻¹ = star l * l`. Rewrite using `[mul_assoc (star l * l), mul_assoc, mul_inv_cancel₀ h0, mul_one]`. Rewrite `h2` using `[e2]`. Then use the resulting hypothesis.

Establish `hlS : l ∈ S`. Establish `hu : IsUnitIn S (star l⁻¹ * l⁻¹)`. Use `⟨mul_ne_zero (star_ne_zero.mpr (inv_ne_zero hl0)) (inv_ne_zero hl0), S.mul_mem (hS.star_mem _ hli) hli, ?_⟩` and prove the remaining obligations. Rewrite using `[star_inv₀, mul_inv, inv_inv, inv_inv]`. Conclude with `hNl`.

Use `(isUnitIn_of_mul (hS.star_mem _ hli) hli hu).2.2` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Introduce `c hc`. Use `S.mul_mem (hdiv c hc) hlS` as an intermediate fact. Rewrite `this` using `[mul_assoc, inv_mul_cancel₀ hl0, mul_one]`. Then use the resulting hypothesis.

Use `⟨y i₁, hM, hyM i₁, hzu, ?_, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Establish `hcS : ∀ i, i ≠ i₁ → h (y i) m * (h (y i) (y i))⁻¹ ∈ S` using `fun i hi => S.mul_mem (hM.int _ (hyM i) _ hm) (hau i hi).2.2`. Establish `h1 : (h (y i₁) m * (h (y i₁) (y i₁))⁻¹) • y i₁ ∈ M`. Establish `e` using `Finset.add_sum_erase Finset.univ (fun i => (h (y i) m * (h (y i) (y i))⁻¹) • y i) (Finset.mem_univ i₁)`.

Rewrite `e` using `[← hexp m]`. Rewrite using `[eq_sub_of_add_eq e]`. Conclude with `M.sub_mem hm (M.sum_mem fun i hi => hM.smul_mem _ (hcS i (Finset.mem_erase.mp hi).1) _ (hyM i))`. Establish `h2` using `hd₁.mul_left (hprim _ h1)`. Rewrite `h2` using `[mul_assoc, inv_mul_cancel₀ (hne i₁), mul_one]`. Then use the resulting hypothesis.

Introduce `v _ hzv hv`. Rewrite using `[hexp v]`. Use `M.sum_mem fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = i₁`. Rewrite using `[hi, hzv, zero_mul, zero_smul]`.

Conclude with `M.zero_mem`. Conclude with `hM.smul_mem _ (S.mul_mem (hv _ (hyM i)) (hau i hi).2.2) _ (hyM i)`.
-/
theorem exists_isASD_of_tuple [FiniteDimensional K V] (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {M : AddSubgroup V} (hM : IsLatIn S h ⊤ M)
    (x : Fin (finrank K V) → V) (hx : ∀ i, x i ∈ M)
    (hdet : ¬ Dv S π ((gram h x).det * π⁻¹))
    (hall : ∀ t : Fin (finrank K V) → V, (∀ i, t i ∈ M) → (∀ i j, i ≠ j → h (t i) (t j) = 0) →
      Dv S π (gram h t).det) :
    ∃ z, IsASD S π h ⊤ M z := by
  obtain ⟨y, horth, hspan⟩ := exists_orth_tuple hS hπ hs _ x
    (fun i j => hM.int _ (hx i) _ (hx j)) hdet
  have hyM : ∀ i, y i ∈ M := by
    intro i
    have h1 : y i ∈ spanS S x := by rw [← hspan]; exact mem_spanS y i
    exact spanS_induction (p := fun v => v ∈ M) M.zero_mem (fun a b => M.add_mem)
      (fun c hc a ha => hM.smul_mem c hc a ha) hx _ h1
  have haS : ∀ i, h (y i) (y i) ∈ S := fun i => hM.int _ (hyM i) _ (hyM i)
  obtain ⟨c, hcS, hcdet⟩ := gram_det_of_le (h := h) hS
    (fun i => by rw [hspan]; exact mem_spanS x i : ∀ i, x i ∈ spanS S y)
  rw [gram_det_orth horth] at hcdet
  have hPd : Dv S π (∏ i, h (y i) (y i)) := by
    rw [← gram_det_orth horth]; exact hall y hyM horth
  have hPn : ¬ Dv S π ((∏ i, h (y i) (y i)) * π⁻¹) := by
    intro hdv
    apply hdet
    rw [hcdet, mul_assoc]
    exact hdv.mul_left hcS
  have hPf : star ((∏ i, h (y i) (y i)) * π⁻¹) = (∏ i, h (y i) (y i)) * π⁻¹ := by
    rw [star_mul', star_inv₀, hπ.fix, ← starRingEnd_apply, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun i _ => hs.eq _ _
  have hPu : IsUnitIn S ((∏ i, h (y i) (y i)) * π⁻¹) := unit_of_not_dv hπ hPd hPf hPn
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, ¬ IsUnitIn S (h (y i₁) (y i₁)) := by
    by_contra hcon
    push Not at hcon
    exact unit_not_dv hπ (LocF.isUnitIn_prod Finset.univ _ fun i _ => hcon i) hPd
  have hd₁ : Dv S π (h (y i₁) (y i₁)) := dv_of_not_unit hπ (haS i₁) (hs.eq _ _) hi₁
  have hQS : ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) ∈ S := S.prod_mem fun i _ => haS i
  have hsplit : (∏ i, h (y i) (y i)) * π⁻¹ =
      h (y i₁) (y i₁) * π⁻¹ * ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁)]
    ring
  have hQu : IsUnitIn S (∏ i ∈ Finset.univ.erase i₁, h (y i) (y i)) :=
    isUnitIn_of_mul hd₁ hQS (hsplit ▸ hPu)
  have hzu : IsUnitIn S (h (y i₁) (y i₁) * π⁻¹) :=
    isUnitIn_of_mul hQS hd₁ (by rw [mul_comm, ← hsplit]; exact hPu)
  have hau : ∀ i, i ≠ i₁ → IsUnitIn S (h (y i) (y i)) := by
    intro i hi
    have hmem : i ∈ Finset.univ.erase i₁ := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have e := Finset.mul_prod_erase (Finset.univ.erase i₁) (fun i => h (y i) (y i)) hmem
    refine isUnitIn_of_mul (S.prod_mem fun j _ => haS j :
      ∏ j ∈ (Finset.univ.erase i₁).erase i, h (y j) (y j) ∈ S) (haS i) ?_
    rw [mul_comm, e]
    exact hQu
  have hne : ∀ i, h (y i) (y i) ≠ 0 := by
    intro i
    by_cases hi : i = i₁
    · rw [hi]; exact left_ne_zero_of_mul hzu.1
    · exact (hau i hi).1
  have hexp := expand_orth horth hne

  have hprim : ∀ c : K, c • y i₁ ∈ M → c ∈ S := by
    have hy0 : y i₁ ≠ 0 := by
      intro h0
      apply hne i₁
      rw [h0]; simp
    obtain ⟨l, hl0, hl, hdiv⟩ := exists_primitive hS hd hM (Submodule.mem_top : y i₁ ∈ ⊤) hy0
    have hli : l⁻¹ ∈ S := by
      have := hdiv 1 (by rw [one_smul]; exact hyM i₁)
      rwa [one_mul] at this
    have hNl : star l * l ∈ S := by
      have h1 := hall (fun i => (if i = i₁ then l else 1) • y i) (by
        intro i
        by_cases hi : i = i₁
        · simp only [hi, if_true]; exact hl
        · simp only [hi, if_false, one_smul]; exact hyM i) (by
        intro i j hij
        simp only [map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero])
      rw [gram_det_smul_orth horth] at h1
      have e : (∏ i, star (if i = i₁ then l else 1) * (if i = i₁ then l else 1)) = star l * l := by
        rw [Finset.prod_eq_single i₁]
        · simp
        · intro j _ hj; simp [hj]
        · intro hi; exact absurd (Finset.mem_univ i₁) hi
      rw [e] at h1
      unfold Dv at h1
      have h2 := S.mul_mem h1 hPu.2.2
      have h0 := hPu.1
      have e2 : star l * l * (∏ i, h (y i) (y i)) * π⁻¹ * ((∏ i, h (y i) (y i)) * π⁻¹)⁻¹ =
          star l * l := by
        rw [mul_assoc (star l * l), mul_assoc, mul_inv_cancel₀ h0, mul_one]
      rwa [e2] at h2
    have hlS : l ∈ S := by
      have hu : IsUnitIn S (star l⁻¹ * l⁻¹) := by
        refine ⟨mul_ne_zero (star_ne_zero.mpr (inv_ne_zero hl0)) (inv_ne_zero hl0),
          S.mul_mem (hS.star_mem _ hli) hli, ?_⟩
        rw [star_inv₀, mul_inv, inv_inv, inv_inv]
        exact hNl
      have := (isUnitIn_of_mul (hS.star_mem _ hli) hli hu).2.2
      rwa [inv_inv] at this
    intro c hc
    have := S.mul_mem (hdiv c hc) hlS
    rwa [mul_assoc, inv_mul_cancel₀ hl0, mul_one] at this
  refine ⟨y i₁, hM, hyM i₁, hzu, ?_, ?_⟩
  · intro m hm
    have hcS : ∀ i, i ≠ i₁ → h (y i) m * (h (y i) (y i))⁻¹ ∈ S := fun i hi =>
      S.mul_mem (hM.int _ (hyM i) _ hm) (hau i hi).2.2
    have h1 : (h (y i₁) m * (h (y i₁) (y i₁))⁻¹) • y i₁ ∈ M := by
      have e := Finset.add_sum_erase Finset.univ
        (fun i => (h (y i) m * (h (y i) (y i))⁻¹) • y i) (Finset.mem_univ i₁)
      rw [← hexp m] at e
      rw [eq_sub_of_add_eq e]
      exact M.sub_mem hm (M.sum_mem fun i hi =>
        hM.smul_mem _ (hcS i (Finset.mem_erase.mp hi).1) _ (hyM i))
    have h2 := hd₁.mul_left (hprim _ h1)
    rwa [mul_assoc, inv_mul_cancel₀ (hne i₁), mul_one] at h2
  · intro v _ hzv hv
    rw [hexp v]
    refine M.sum_mem fun i _ => ?_
    by_cases hi : i = i₁
    · rw [hi, hzv, zero_mul, zero_smul]; exact M.zero_mem
    · exact hM.smul_mem _ (S.mul_mem (hv _ (hyM i)) (hau i hi).2.2) _ (hyM i)

end Formalism.HermitianLattices.Ext.L3.U0
