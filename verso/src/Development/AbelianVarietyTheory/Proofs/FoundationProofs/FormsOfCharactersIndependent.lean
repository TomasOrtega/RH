import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructure
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.EisM.Indep

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using GlobalTheory.EisM.Lin.qs_zero`. Consider the case `insert i s hi ih`. Establish `hp : PolyB (∑ j ∈ s, a j)` using `by clear ih hi`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simpa using GlobalTheory.EisM.Lin.polyB_zero`. Consider the case `insert j t hj ih2`. Rewrite using `[Finset.sum_insert hj]`. Conclude with `GlobalTheory.EisM.Lin.polyB_add _ _ (ha j) ih2`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, GlobalTheory.EisM.Lin.qs_add _ _ (ha i) hp, ih]`.
-/
theorem qs_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℂ) (ha : ∀ i, PolyB (a i)) :
    qs (∑ i ∈ s, a i) = ∑ i ∈ s, qs (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.EisM.Lin.qs_zero
  | insert i s hi ih =>
    have hp : PolyB (∑ j ∈ s, a j) := by
      clear ih hi
      induction s using Finset.induction_on with
      | empty => simpa using GlobalTheory.EisM.Lin.polyB_zero
      | insert j t hj ih2 =>
        rw [Finset.sum_insert hj]; exact GlobalTheory.EisM.Lin.polyB_add _ _ (ha j) ih2
    rw [Finset.sum_insert hi, Finset.sum_insert hi, GlobalTheory.EisM.Lin.qs_add _ _ (ha i) hp, ih]

/- English proof (translation)
Use `haveI : NeZero L := ⟨hL.ne'⟩`. Take `⟨v, hv⟩` from `ZMod.unitsMap_surjective hNL u`. Establish `hc : Nat.Coprime (v : ZMod L).val L` using `ZMod.val_coe_unit_coprime v`. Establish `hc' : IsCoprime (((v : ZMod L).val : ℕ) : ℤ) (L : ℤ)` using `Nat.isCoprime_iff_coprime.mpr hc`. Take `⟨x, y, hxy⟩` from `hc'`.

Use `⟨⟨!![x, -y; (L : ℤ), (((v : ZMod L).val : ℕ) : ℤ)], ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_fin_two_of]`. Take the linear combination `hxy`. Simplify using the standard rewrite rules. Simplify using `only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]`.

Rewrite using `[← hv, ZMod.unitsMap_val, ZMod.cast_eq_val, Int.cast_natCast]`.
-/
theorem exists_gamma (L N : ℕ) (hL : 0 < L) (hNL : N ∣ L) (u : (ZMod N)ˣ) :
    ∃ γ : SL(2, ℤ), γ 1 0 = (L : ℤ) ∧ ((γ 1 1 : ℤ) : ZMod N) = u := by
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hNL u
  have hc : Nat.Coprime (v : ZMod L).val L := ZMod.val_coe_unit_coprime v
  have hc' : IsCoprime (((v : ZMod L).val : ℕ) : ℤ) (L : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
  obtain ⟨x, y, hxy⟩ := hc'
  refine ⟨⟨!![x, -y; (L : ℤ), (((v : ZMod L).val : ℕ) : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hxy
  · simp
  · simp only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← hv, ZMod.unitsMap_val, ZMod.cast_eq_val, Int.cast_natCast]

/- English proof (translation)
Introduce `k L N a hL hNL hmf hsum ε₀`. Establish `hN : N ≠ 0` using `by rintro rfl; exact hL.ne' (Nat.eq_zero_of_zero_dvd hNL)`. Use `haveI : NeZero N := ⟨hN⟩`. Use `set f : DirichletCharacter ℂ N → ℍ → ℂ := fun ε => qs (a ε) with hf`. Establish `hfs : ∑ ε, f ε = 0`.

Rewrite using `[hf, ← qs_finset_sum _ _ (fun ε => (hmf ε).1), hsum]`. Conclude with `GlobalTheory.EisM.Lin.qs_zero`. Establish `key : ∀ (b : ZMod N) (τ : ℍ), ∑ ε, ε b * f ε τ = 0`. Introduce `b τ`. Distinguish the cases in `hb : IsUnit b`.

Take `⟨u, rfl⟩` from `hb`. Take `⟨γ, h10, h11⟩` from `exists_gamma L N hL hNL u`. Establish `hdiv : (L : ℤ) ∣ γ 1 0` using `by rw [h10]`. Establish `hj : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) ≠ 0`. Apply `pow_ne_zero` to reduce the goal to its premises.

Introduce `h0`. Establish `him` using `congrArg Complex.im h0`. Simplify using `only [h10, Int.cast_natCast, Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, Complex.intCast_im, zero_mul, add_zero, Complex.zero_im] at him`. Establish `: (0 : ℝ) < (L : ℝ) * (τ : ℂ).im` using `mul_pos (by exact_mod_cast hL) τ.im_pos`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : ∀ ε, f ε (γ • τ) = ε (u : ZMod N) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * f ε τ`. Introduce `ε`. Rewrite using `[hf]`. Simplify using `only`. Rewrite using `[(hmf ε).2 γ hdiv τ, ch, h11]`.

Establish `h0 : ∑ ε, f ε (γ • τ) = 0`. Use `congrFun hfs (γ • τ)` as an intermediate fact. Simplify `this` using `[Finset.sum_apply]`. Simplify using `only [e] at h0`. Establish `h1 : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * ∑ ε, ε (u : ZMod N) * f ε τ = 0`.

Rewrite using `[Finset.mul_sum, ← h0]; exact Finset.sum_congr rfl (fun ε _ => by ring)`. Conclude with `(mul_eq_zero.mp h1).resolve_left hj`. Conclude with `Finset.sum_eq_zero (fun ε _ => by rw [MulChar.map_nonunit ε hb, zero_mul])`. Use function extensionality and compare the values at `n`. Establish `hq : f ε₀ = 0`.

Use function extensionality and compare the values at `τ`. Establish `hT : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = 0` using `Finset.sum_eq_zero (fun b _ => by rw [key b τ, mul_zero])`. Establish `hT' : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = ∑ ε, f ε τ * ∑ b : ZMod N, (ε₀⁻¹ * ε) b`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Rewrite using `[MulChar.coeToFun_mul, Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hT` using `[hT']`. Rewrite `hT` using `[Finset.sum_eq_single ε₀]`.

Rewrite `hT` using `[inv_mul_cancel, MulChar.sum_one_eq_card_units]`. Establish `hc : ((Fintype.card (ZMod N)ˣ : ℕ) : ℂ) ≠ 0`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions. Simplify `hT` using `[hc, hN]`. Introduce `ε _ hne`.

Rewrite using `[MulChar.sum_eq_zero_of_ne_one, mul_zero]`. Introduce `h1`. Apply `hne` to reduce the goal to its premises. Use `congrArg (ε₀ * ·) h1` as an intermediate fact. Simplify using `using this`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `qs_injective (a ε₀) 0 (hmf ε₀).1 GlobalTheory.EisM.Lin.polyB_zero (by rw [GlobalTheory.EisM.Lin.qs_zero]; exact hq)` as an intermediate fact. Simplify using `using congrFun this n`.
-/
theorem forms_of_characters_independent : ∀ (k L N : ℕ) (a : DirichletCharacter ℂ N → ℕ → ℂ), 0 < L → N ∣ L →
    (∀ ε, MF k L (ch ε) (a ε)) → (∑ ε, a ε) = 0 → ∀ ε, a ε = 0 := by
  intro k L N a hL hNL hmf hsum ε₀
  have hN : N ≠ 0 := by rintro rfl; exact hL.ne' (Nat.eq_zero_of_zero_dvd hNL)
  haveI : NeZero N := ⟨hN⟩
  set f : DirichletCharacter ℂ N → ℍ → ℂ := fun ε => qs (a ε) with hf
  have hfs : ∑ ε, f ε = 0 := by
    rw [hf, ← qs_finset_sum _ _ (fun ε => (hmf ε).1), hsum]; exact GlobalTheory.EisM.Lin.qs_zero

  have key : ∀ (b : ZMod N) (τ : ℍ), ∑ ε, ε b * f ε τ = 0 := by
    intro b τ
    by_cases hb : IsUnit b
    · obtain ⟨u, rfl⟩ := hb
      obtain ⟨γ, h10, h11⟩ := exists_gamma L N hL hNL u
      have hdiv : (L : ℤ) ∣ γ 1 0 := by rw [h10]
      have hj : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) ≠ 0 := by
        apply pow_ne_zero
        intro h0
        have him := congrArg Complex.im h0
        simp only [h10, Int.cast_natCast, Complex.add_im, Complex.mul_im, Complex.natCast_re,
          Complex.natCast_im, Complex.intCast_im, zero_mul, add_zero, Complex.zero_im] at him
        have : (0 : ℝ) < (L : ℝ) * (τ : ℂ).im := mul_pos (by exact_mod_cast hL) τ.im_pos
        linarith
      have e : ∀ ε, f ε (γ • τ) = ε (u : ZMod N) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * f ε τ := by
        intro ε
        rw [hf]; dsimp only
        rw [(hmf ε).2 γ hdiv τ, ch, h11]
      have h0 : ∑ ε, f ε (γ • τ) = 0 := by
        have := congrFun hfs (γ • τ); simpa [Finset.sum_apply] using this
      simp only [e] at h0
      have h1 : ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k) * ∑ ε, ε (u : ZMod N) * f ε τ = 0 := by
        rw [Finset.mul_sum, ← h0]; exact Finset.sum_congr rfl (fun ε _ => by ring)
      exact (mul_eq_zero.mp h1).resolve_left hj
    · exact Finset.sum_eq_zero (fun ε _ => by rw [MulChar.map_nonunit ε hb, zero_mul])
  funext n
  have hq : f ε₀ = 0 := by
    funext τ
    have hT : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = 0 :=
      Finset.sum_eq_zero (fun b _ => by rw [key b τ, mul_zero])
    have hT' : ∑ b : ZMod N, ε₀⁻¹ b * ∑ ε, ε b * f ε τ = ∑ ε, f ε τ * ∑ b : ZMod N, (ε₀⁻¹ * ε) b := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ε _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [MulChar.coeToFun_mul, Pi.mul_apply]; ring
    rw [hT'] at hT
    rw [Finset.sum_eq_single ε₀] at hT
    · rw [inv_mul_cancel, MulChar.sum_one_eq_card_units] at hT
      have hc : ((Fintype.card (ZMod N)ˣ : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simpa [hc, hN] using hT
    · intro ε _ hne
      rw [MulChar.sum_eq_zero_of_ne_one, mul_zero]
      intro h1; apply hne
      have := congrArg (ε₀ * ·) h1
      simpa using this
    · intro h; exact absurd (Finset.mem_univ _) h
  have := qs_injective (a ε₀) 0 (hmf ε₀).1 GlobalTheory.EisM.Lin.polyB_zero (by rw [GlobalTheory.EisM.Lin.qs_zero]; exact hq)
  simpa using congrFun this n

end GlobalTheory.EisM.Indep
