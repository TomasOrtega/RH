import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementC
import Formalism.SubspaceCounting.SubspaceCountingProofs.QVandermonde
import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

namespace CSym

section gen

variable {K σ : Type} [CommRing K] [Fintype σ]

def genE (x : σ → K) : PowerSeries K := ∏ i, (1 + PowerSeries.C (x i) * PowerSeries.X)

/- English proof (translation)
Unfold `eF`. Simplify using `[MvPolynomial.esymm, map_sum, map_prod]`.
-/
lemma eF_eq_sum (x : σ → K) (l : ℕ) :
    eF x l = ∑ s ∈ powersetCard l univ, ∏ i ∈ s, x i := by
  unfold eF
  simp [MvPolynomial.esymm, map_sum, map_prod]

/- English proof (translation)
Rewrite using `[eF_eq_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]`. Unfold `genE`. Establish `hc : ∀ i, (1 + PowerSeries.C (x i) * PowerSeries.X : PowerSeries K) = PowerSeries.C (x i) * PowerSeries.X + 1` using `fun i => add_comm _ _`. Repeatedly rewrite using `[hc]`. Rewrite using `[Finset.prod_add, map_sum]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, PowerSeries.coeff_C_mul_X_pow]`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> first | rfl | omega`.
-/
lemma coeff_genE (x : σ → K) (l : ℕ) : PowerSeries.coeff l (genE x) = eF x l := by
  classical
  rw [eF_eq_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  unfold genE
  have hc : ∀ i, (1 + PowerSeries.C (x i) * PowerSeries.X : PowerSeries K) =
      PowerSeries.C (x i) * PowerSeries.X + 1 := fun i => add_comm _ _
  simp_rw [hc]
  rw [Finset.prod_add, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod,
    PowerSeries.coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

/- English proof (translation)
Simplify using `[eF, MvPolynomial.esymm_zero]`.
-/
lemma eF_zero (x : σ → K) : eF x 0 = 1 := by
  simp [eF, MvPolynomial.esymm_zero]

/- English proof (translation)
Simplify using `only [eF_eq_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_powersetCard.1 hs).2]`.
-/
lemma eF_smul (c : K) (x : σ → K) (l : ℕ) : eF (fun i => c * x i) l = c ^ l * eF x l := by
  simp only [eF_eq_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_powersetCard.1 hs).2]

/- English proof (translation)
Rewrite using `[eF_eq_sum, Finset.powersetCard_eq_empty.2 (by simpa using h), Finset.sum_empty]`.
-/
lemma eF_of_card_lt (x : σ → K) (l : ℕ) (h : Fintype.card σ < l) : eF x l = 0 := by
  rw [eF_eq_sum, Finset.powersetCard_eq_empty.2 (by simpa using h), Finset.sum_empty]

/- English proof (translation)
Rewrite using `[← coeff_genE, h, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using `only [coeff_genE]`.
-/
lemma eF_of_genE_mul {τ ρ : Type} [Fintype τ] [Fintype ρ] (z : σ → K) (x : τ → K) (y : ρ → K)
    (h : genE z = genE x * genE y) (n : ℕ) :
    eF z n = ∑ a ∈ range (n + 1), eF x a * eF y (n - a) := by
  rw [← coeff_genE, h, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_genE]

/- English proof (translation)
Use `split_ifs with hl`. Substitute `hl` using the available equality. Conclude with `eF_zero x`. Conclude with `eF_of_card_lt x l (by rw [Fintype.card_eq_zero]; omega)`.
-/
lemma eF_isEmpty [IsEmpty σ] (x : σ → K) (l : ℕ) : eF x l = if l = 0 then 1 else 0 := by
  split_ifs with hl
  · subst hl
    exact eF_zero x
  · exact eF_of_card_lt x l (by rw [Fintype.card_eq_zero]; omega)

/- English proof (translation)
Establish `hg : genE x = genE (fun i : Fin g => x i.castSucc) * (1 + PowerSeries.C (x (Fin.last g)) * PowerSeries.X)`. Unfold `genE`. Rewrite using `[Fin.prod_univ_castSucc]`. Rewrite using `[← coeff_genE, hg, mul_add, mul_one, map_add, show genE (fun i : Fin g => x i.castSucc) * (PowerSeries.C (x (Fin.last g)) * PowerSeries.X) = PowerSeries.C (x (Fin.last g)) * genE (fun i : Fin g => x i.castSucc) * PowerSeries.X by ring, PowerSeries.coeff_succ_mul_X, PowerSeries.co …`.
-/
lemma eF_fin_succ {g : ℕ} (x : Fin (g + 1) → K) (l : ℕ) :
    eF x (l + 1) = eF (fun i : Fin g => x i.castSucc) (l + 1) +
      x (Fin.last g) * eF (fun i : Fin g => x i.castSucc) l := by
  have hg : genE x = genE (fun i : Fin g => x i.castSucc) *
      (1 + PowerSeries.C (x (Fin.last g)) * PowerSeries.X) := by
    unfold genE
    rw [Fin.prod_univ_castSucc]
  rw [← coeff_genE, hg, mul_add, mul_one, map_add,
    show genE (fun i : Fin g => x i.castSucc) * (PowerSeries.C (x (Fin.last g)) * PowerSeries.X) =
      PowerSeries.C (x (Fin.last g)) * genE (fun i : Fin g => x i.castSucc) * PowerSeries.X by ring,
    PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul, coeff_genE, coeff_genE]

end gen

/- English proof (translation)
Repeatedly rewrite using `[Finset.smul_sum, smul_smul, Finset.sum_smul]`. Establish `hin : ∀ l ∈ range (i + 1), ∑ l' ∈ range (i - l + 1), (f l * g l') • E (i - l - l') = ∑ n ∈ Ico l (i + 1), (f l * g (n - l)) • E (i - n)`. Introduce `l hl`. Simplify using `only [Finset.mem_range] at hl`. Rewrite using `[Finset.sum_Ico_eq_sum_range, show i + 1 - l = i - l + 1 by omega]`.

Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[show l + l' - l = l' by omega, show i - (l + l') = i - l - l' by omega]`. Rewrite using `[Finset.sum_congr rfl hin]`. Conclude with `Finset.sum_comm' (fun l n => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)`.
-/
lemma conv_smul {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] (f g : ℕ → K) (E : ℕ → V)
    (i : ℕ) :
    ∑ l ∈ range (i + 1), f l • ∑ l' ∈ range (i - l + 1), g l' • E (i - l - l') =
      ∑ n ∈ range (i + 1), (∑ a ∈ range (n + 1), f a * g (n - a)) • E (i - n) := by
  simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
  have hin : ∀ l ∈ range (i + 1), ∑ l' ∈ range (i - l + 1), (f l * g l') • E (i - l - l') =
      ∑ n ∈ Ico l (i + 1), (f l * g (n - l)) • E (i - n) := by
    intro l hl
    simp only [Finset.mem_range] at hl
    rw [Finset.sum_Ico_eq_sum_range, show i + 1 - l = i - l + 1 by omega]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [show l + l' - l = l' by omega, show i - (l + l') = i - l - l' by omega]
  rw [Finset.sum_congr rfl hin]
  exact Finset.sum_comm' (fun l n => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)

/- English proof (translation)
Use extensionality with `a`. Simplify using `[LinearMap.sum_apply]`.
-/
lemma sum_comp {K A B C ι : Type} [CommRing K] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] (s : Finset ι) (f : ι → B →ₗ[K] C) (g : A →ₗ[K] B) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by
  ext a
  simp [LinearMap.sum_apply]

/- English proof (translation)
Use extensionality with `a`. Simplify using `[LinearMap.sum_apply, map_sum]`.
-/
lemma comp_sum {K A B C ι : Type} [CommRing K] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] (s : Finset ι) (f : ι → A →ₗ[K] B) (g : B →ₗ[K] C) :
    g.comp (∑ i ∈ s, f i) = ∑ i ∈ s, g.comp (f i) := by
  ext a
  simp [LinearMap.sum_apply, map_sum]

section gauss

variable {K : Type} [Field K]

/- English proof (translation)
Unfold `beFam`. Rewrite using `[show ((g + 1 : ℕ) : ℤ) - 1 - 2 * ((i.castSucc : Fin (g + 1)).val : ℤ) = ((g : ℤ) - 1 - 2 * (i.val : ℤ)) + 1 by simp; ring, zpow_add_one₀ hQ, mul_comm]`.
-/
lemma beFam_castSucc (Q : K) (hQ : Q ≠ 0) (g : ℕ) (i : Fin g) :
    beFam Q (g + 1) i.castSucc = Q * beFam Q g i := by
  unfold beFam
  rw [show ((g + 1 : ℕ) : ℤ) - 1 - 2 * ((i.castSucc : Fin (g + 1)).val : ℤ) =
      ((g : ℤ) - 1 - 2 * (i.val : ℤ)) + 1 by simp; ring, zpow_add_one₀ hQ, mul_comm]

/- English proof (translation)
Unfold `beFam`. Use `congr 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma beFam_last (Q : K) (g : ℕ) : beFam Q (g + 1) (Fin.last g) = Q ^ (-(g : ℤ)) := by
  unfold beFam
  congr 1
  simp
  ring

/- English proof (translation)
Rewrite using `[eF_fin_succ]`. Repeatedly rewrite using `[beFam_castSucc Q hQ]`. Rewrite using `[eF_smul, eF_smul, beFam_last]`.
-/
lemma eF_beFam_succ (Q : K) (hQ : Q ≠ 0) (g l : ℕ) :
    eF (beFam Q (g + 1)) (l + 1) =
      Q ^ (l + 1) * eF (beFam Q g) (l + 1) + Q ^ (-(g : ℤ)) * (Q ^ l * eF (beFam Q g) l) := by
  rw [eF_fin_succ]
  simp_rw [beFam_castSucc Q hQ]
  rw [eF_smul, eF_smul, beFam_last]

/- English proof (translation)
The claim follows from `| g, 0 => by rw [Formalism.G0.QVandermondeP.gb_zero_right, eF_zero]; simp | 0, l + 1 => by rw [Formalism.G0.QVandermondeP.gb_zero_succ, eF_of_card_lt _ _ (by simp)]; simp | g + 1, l + 1 => by rw [Formalism.G0.QVandermondeP.gb_succ_succ, eF_beFam_succ _ hQ] push_cast rw [gauss_zpo …`.
-/
lemma gauss_zpow (Q : ℕ) (hQ : (Q : K) ≠ 0) : ∀ g l : ℕ,
    ((Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) =
      (Q : K) ^ ((l : ℤ) * ((g : ℤ) - l)) * eF (beFam (Q : K) g) l
  | g, 0 => by
    rw [Formalism.G0.QVandermondeP.gb_zero_right, eF_zero]; simp
  | 0, l + 1 => by
    rw [Formalism.G0.QVandermondeP.gb_zero_succ, eF_of_card_lt _ _ (by simp)]; simp
  | g + 1, l + 1 => by
    rw [Formalism.G0.QVandermondeP.gb_succ_succ, eF_beFam_succ _ hQ]
    push_cast
    rw [gauss_zpow Q hQ g l, gauss_zpow Q hQ g (l + 1)]
    push_cast
    generalize eF (beFam (Q : K) g) l = E0
    generalize eF (beFam (Q : K) g) (l + 1) = E1
    have h1 : (Q : K) ^ ((l : ℤ) * ((g : ℤ) - l)) =
        (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) + 1 - ((l : ℤ) + 1))) * (Q : K) ^ (-(g : ℤ)) *
          (Q : K) ^ l := by
      rw [← zpow_natCast, ← zpow_add₀ hQ, ← zpow_add₀ hQ]
      congr 1
      ring
    have h2 : ((Q : K) ^ 2) ^ (l + 1) * (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) - ((l : ℤ) + 1))) =
        (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) + 1 - ((l : ℤ) + 1))) * (Q : K) ^ (l + 1) := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast (Q : K) (l + 1), ← zpow_add₀ hQ,
        ← zpow_add₀ hQ]
      congr 1
      push_cast
      ring
    linear_combination E0 * h1 + E1 * h2

end gauss

end CSym

open CSym

/- English proof (translation)
Introduce `K _ Q g l hQ`. Rewrite using `[gauss_zpow Q hQ g l]`. Break down `le_or_gt l g with h | h` into its components or cases. Rewrite using `[show ((l : ℤ) * ((g : ℤ) - l)) = ((l * (g - l) : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring, zpow_natCast]`. Rewrite using `[eF_of_card_lt _ _ (by simpa using h)]`.

Simplify using the standard rewrite rules.
-/
theorem gauss_elementary_symmetric : GaussEsymm := by
  intro K _ Q g l hQ
  rw [gauss_zpow Q hQ g l]
  rcases le_or_gt l g with h | h
  · rw [show ((l : ℤ) * ((g : ℤ) - l)) = ((l * (g - l) : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring,
      zpow_natCast]
  · rw [eF_of_card_lt _ _ (by simpa using h)]
    simp

/- English proof (translation)
Introduce `K σ _ _ _ x n hn`. Establish `h` using `Formalism.FT.SymmetricSeries.esymm_hsymm_rel (σ := σ) (R := K) n hn`. Establish `h2` using `congrArg (MvPolynomial.eval x) h`. Simplify using `only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at h2`. Rewrite using `[← Finset.sum_range_reflect]`.

Establish `hterm : ∀ j ∈ range (n + 1), (-1 : K) ^ (n + 1 - 1 - j) * hF x (n + 1 - 1 - j) * eF x (n - (n + 1 - 1 - j)) = (-1) ^ n * ((-1) ^ j * MvPolynomial.eval x (MvPolynomial.esymm σ K j) * MvPolynomial.eval x (MvPolynomial.hsymm σ K (n - j)))`. Introduce `j hj`. Simplify using `only [Finset.mem_range] at hj`. Rewrite using `[show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]`. Establish `e : (-1 : K) ^ n = (-1) ^ (n - j) * (-1) ^ j`.

Rewrite using `[← pow_add, Nat.sub_add_cancel (by omega)]`. Establish `e2 : (-1 : K) ^ (n - j) = (-1) ^ n * (-1) ^ j`. Rewrite using `[e, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]`. Unfold `hF eF`. Rewrite using `[e2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.mul_sum, h2, mul_zero]`.
-/
theorem hecke_convolution : HEConvolution := by
  intro K σ _ _ _ x n hn
  have h := Formalism.FT.SymmetricSeries.esymm_hsymm_rel (σ := σ) (R := K) n hn
  have h2 := congrArg (MvPolynomial.eval x) h
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at h2
  rw [← Finset.sum_range_reflect]
  have hterm : ∀ j ∈ range (n + 1), (-1 : K) ^ (n + 1 - 1 - j) * hF x (n + 1 - 1 - j) * eF x (n - (n + 1 - 1 - j)) =
      (-1) ^ n * ((-1) ^ j * MvPolynomial.eval x (MvPolynomial.esymm σ K j) *
        MvPolynomial.eval x (MvPolynomial.hsymm σ K (n - j))) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
    have e : (-1 : K) ^ n = (-1) ^ (n - j) * (-1) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have e2 : (-1 : K) ^ (n - j) = (-1) ^ n * (-1) ^ j := by
      rw [e, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
    unfold hF eF
    rw [e2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, h2, mul_zero]

namespace CSym

/- English proof (translation)
Unfold `genE`. Rewrite using `[Fintype.prod_prod_type, Fintype.prod_prod_type, Fin.prod_univ_castSucc, mul_comm]`. Both sides reduce to the same expression.
-/
lemma genE_FFam_succ {K : Type} [Field K] (Q : K) (t : ℕ) (m : ℕ → K) (j : ℕ) :
    genE (FFam Q t m (j + 1)) =
      genE (fun x => m (j + 1) * beFam Q (t + 1) x) * genE (FFam Q t m j) := by
  unfold genE
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Fin.prod_univ_castSucc, mul_comm]
  rfl

end CSym

/- English proof (translation)
Introduce `K _ M _ _ Kk e Q t m J hI j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ i`. Simplify using `only [Kc, LinearMap.comp_id, LinearMap.id_comp]`.

Rewrite using `[Finset.sum_eq_single 0 (fun l _ hl => by rw [eF_isEmpty, if_neg hl, zero_smul]) (by simp), eF_isEmpty, if_pos rfl, one_smul, Nat.sub_zero]`. Consider the case `succ j ih`. Introduce `hj i`. Establish `ih'` using `ih (by omega)`. Use `show (e (j + 1) i).comp ((Kk j).comp (Kc Kk j)) = ((Kk j).comp (Kc Kk j)).comp (∑ l ∈ range (i + 1), eF (FFam Q t m (j + 1)) l • e 0 (i - l))`.

Rewrite using `[← LinearMap.comp_assoc, hI j (by omega) i, LinearMap.comp_assoc, CSym.sum_comp]`. Repeatedly rewrite using `[LinearMap.smul_comp, ih', ← LinearMap.comp_smul, ← CSym.comp_sum]`. Rewrite using `[← LinearMap.comp_assoc]`. Use `congr 1`. Rewrite using `[conv_smul]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[eF_of_genE_mul _ _ _ (genE_FFam_succ Q t m j) n]`.
-/
theorem iterate_statement : Iterate := by
  intro K _ M _ _ Kk e Q t m J hI j
  induction j with
  | zero =>
    intro _ i
    simp only [Kc, LinearMap.comp_id, LinearMap.id_comp]
    rw [Finset.sum_eq_single 0 (fun l _ hl => by rw [eF_isEmpty, if_neg hl, zero_smul])
      (by simp), eF_isEmpty, if_pos rfl, one_smul, Nat.sub_zero]
  | succ j ih =>
    intro hj i
    have ih' := ih (by omega)
    show (e (j + 1) i).comp ((Kk j).comp (Kc Kk j)) =
      ((Kk j).comp (Kc Kk j)).comp (∑ l ∈ range (i + 1), eF (FFam Q t m (j + 1)) l • e 0 (i - l))
    rw [← LinearMap.comp_assoc, hI j (by omega) i, LinearMap.comp_assoc, CSym.sum_comp]
    simp_rw [LinearMap.smul_comp, ih', ← LinearMap.comp_smul, ← CSym.comp_sum]
    rw [← LinearMap.comp_assoc]
    congr 1
    rw [conv_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [eF_of_genE_mul _ _ _ (genE_FFam_succ Q t m j) n]

/- English proof (translation)
Introduce `K _ M _ _ Kk e Q t m J hI j hj r`. Establish `hit` using `iterate_statement K M Kk e Q t m J hI j hj`. Rewrite using `[CSym.sum_comp]`. Repeatedly rewrite using `[LinearMap.smul_comp, hit, ← LinearMap.comp_smul, ← CSym.comp_sum]`. Use `congr 1`.

Rewrite using `[conv_smul, Finset.sum_eq_single 0]`. Simplify using `[hF, eF_zero, MvPolynomial.hsymm_zero]`. Introduce `n _ hn0`. Rewrite using `[hecke_convolution K _ (FFam Q t m j) n (by omega), zero_smul]`. Introduce `h`.

Simplify using `at h`.
-/
theorem inversion_formula : Inversion := by
  intro K _ M _ _ Kk e Q t m J hI j hj r
  have hit := iterate_statement K M Kk e Q t m J hI j hj
  rw [CSym.sum_comp]
  simp_rw [LinearMap.smul_comp, hit, ← LinearMap.comp_smul, ← CSym.comp_sum]
  congr 1
  rw [conv_smul, Finset.sum_eq_single 0]
  · simp [hF, eF_zero, MvPolynomial.hsymm_zero]
  · intro n _ hn0
    rw [hecke_convolution K _ (FFam Q t m j) n (by omega), zero_smul]
  · intro h
    simp at h

/- English proof (translation)
Introduce `K ι _ M _ _ Kk Tm pp ν k t r j Ev Od lam w m hpp hrk hI`. Use `set Q := pp ^ ν with hQdef`. Establish `hQ : Q ≠ 0` using `pow_ne_zero _ hpp`. Establish `hinv` using `inversion_formula K M Kk (fun a i => (Q ^ (-((i : ℤ) * ((NN k t a : ℤ) - i)))) • Tm a i) Q t m j hI j le_rfl r`. Establish `hZ : Zop pp ν Ev Od lam w m k t r j (Tm j) = (pp ^ (NprimeZ Ev Od lam (w j) r) * Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r))) • ∑ l ∈ range (r + 1), ((-1 : K) ^ l * hF (FFam Q t m j) l) • ((Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ))))) • Tm j (r - l))`.

Unfold `Zop`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hlr : l ≤ r` using `by simp only [Finset.mem_range] at hl; omega`. Unfold `cCoef Ttil`.

Simplify using `only [smul_smul]`. Use `congr 1`. Establish `h1 : pp ^ (NprimeZ Ev Od lam (w j) r - NprimeZ Ev Od lam (w j) (r - l)) * pp ^ (NprimeZ Ev Od lam (w j) (r - l)) = pp ^ (NprimeZ Ev Od lam (w j) r)`. Rewrite using `[← zpow_add₀ hpp]`. Put the polynomial expressions in normal form.

Establish `h2 : Q ^ ((l : ℤ) * ((NN k t j : ℤ) - 2 * r + l)) = Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r)) * Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ))))`. Rewrite using `[← zpow_add₀ hQ]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub hlr]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2]`. Take the linear combination `((-1 : K) ^ l * Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r)) * Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ)))) * hF (FFam Q t m j) l) * h1`. Rewrite using `[hZ, LinearMap.smul_comp, hinv]`. Simplify using `only [LinearMap.comp_smul, smul_smul]`. Use `congr 1`.

Establish `hQz : ∀ z : ℤ, Q ^ z = pp ^ ((ν : ℤ) * z)` using `fun z => by rw [zpow_mul, zpow_natCast]`. Rewrite using `[hQz, hQz, ← zpow_add₀ hpp, ← zpow_add₀ hpp, ← zpow_add₀ hpp]`. Use `congr 1`. Unfold `NprimeZ PrZ ArZ NN`. Use `push_cast`.

Rewrite using `[Finset.sum_add_distrib, Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theorem_c_i : ThmCi := by
  intro K ι _ M _ _ Kk Tm pp ν k t r j Ev Od lam w m hpp hrk hI
  set Q := pp ^ ν with hQdef
  have hQ : Q ≠ 0 := pow_ne_zero _ hpp
  have hinv := inversion_formula K M Kk (fun a i => (Q ^ (-((i : ℤ) * ((NN k t a : ℤ) - i)))) • Tm a i)
    Q t m j hI j le_rfl r
  have hZ : Zop pp ν Ev Od lam w m k t r j (Tm j) =
      (pp ^ (NprimeZ Ev Od lam (w j) r) * Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r))) •
        ∑ l ∈ range (r + 1), ((-1 : K) ^ l * hF (FFam Q t m j) l) •
          ((Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ))))) • Tm j (r - l)) := by
    unfold Zop
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlr : l ≤ r := by simp only [Finset.mem_range] at hl; omega
    unfold cCoef Ttil
    simp only [smul_smul]
    congr 1
    have h1 : pp ^ (NprimeZ Ev Od lam (w j) r - NprimeZ Ev Od lam (w j) (r - l)) *
        pp ^ (NprimeZ Ev Od lam (w j) (r - l)) = pp ^ (NprimeZ Ev Od lam (w j) r) := by
      rw [← zpow_add₀ hpp]
      ring_nf
    have h2 : Q ^ ((l : ℤ) * ((NN k t j : ℤ) - 2 * r + l)) =
        Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r)) *
          Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ)))) := by
      rw [← zpow_add₀ hQ]
      congr 1
      push_cast [Nat.cast_sub hlr]
      ring
    rw [h2]
    linear_combination ((-1 : K) ^ l * Q ^ ((r : ℤ) * ((NN k t j : ℤ) - r)) *
      Q ^ (-(((r - l : ℕ) : ℤ) * ((NN k t j : ℤ) - ((r - l : ℕ) : ℤ)))) * hF (FFam Q t m j) l) * h1
  rw [hZ, LinearMap.smul_comp, hinv]
  simp only [LinearMap.comp_smul, smul_smul]
  congr 1
  have hQz : ∀ z : ℤ, Q ^ z = pp ^ ((ν : ℤ) * z) := fun z => by rw [zpow_mul, zpow_natCast]
  rw [hQz, hQz, ← zpow_add₀ hpp, ← zpow_add₀ hpp, ← zpow_add₀ hpp]
  congr 1
  unfold NprimeZ PrZ ArZ NN
  push_cast
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring

end Formalism.InvariantFactorPaths.G7
