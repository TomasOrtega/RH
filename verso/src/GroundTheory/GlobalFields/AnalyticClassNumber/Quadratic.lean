import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.Artin.OneDimL
import GroundTheory.GlobalFields.Artin.OneDimExistence
import GroundTheory.GlobalFields.Artin.AbelianHecke
import GroundTheory.GlobalFields.Artin.Regular
import GroundTheory.GlobalFields.AnalyticClassNumber.ClassNumberFormula
import GroundTheory.LocalFields.ArtinConductor
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Filter Topology Complex NumberField.InfinitePlace NumberField.Units
open scoped Real

namespace GroundTheory.Global

namespace Quadratic

section Two

variable {G : Type*} [Group G] [Finite G]

/- English proof (translation)
Use `Fintype.ofFinite G` as an intermediate fact. Assume the negation of the conclusion as `h`. Establish `hcard : ({1, σ, τ} : Finset G).card = 3`. Rewrite using `[Finset.card_insert_of_notMem, Finset.card_pair h]`. Simplify using `[Ne.symm hσ, Ne.symm hτ]`.

Establish `hle` using `Finset.card_le_univ ({1, σ, τ} : Finset G)`. Rewrite `hle` using `[hcard, Fintype.card_eq_nat_card, hG]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_of_ne_one_of_card_eq_two (hG : Nat.card G = 2) {σ τ : G} (hσ : σ ≠ 1) (hτ : τ ≠ 1) :
    σ = τ := by
  classical
  have := Fintype.ofFinite G
  by_contra h
  have hcard : ({1, σ, τ} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h]
    simp [Ne.symm hσ, Ne.symm hτ]
  have hle := Finset.card_le_univ ({1, σ, τ} : Finset G)
  rw [hcard, Fintype.card_eq_nat_card, hG] at hle
  omega

omit [Finite G] in

/- English proof (translation)
Establish `h` using `pow_card_eq_one' (G := G) (x := σ)`. Rewrite `h` using `[hG, pow_two]`. Then use the resulting hypothesis.
-/
theorem mul_self_eq_one_of_card_eq_two (hG : Nat.card G = 2) (σ : G) : σ * σ = 1 := by
  have h := pow_card_eq_one' (G := G) (x := σ)
  rwa [hG, pow_two] at h

/- English proof (translation)
Establish `: Nontrivial G` using `Finite.one_lt_card_iff_nontrivial.1 (by omega)`. Conclude with `exists_ne 1`.
-/
theorem exists_ne_one_of_card_eq_two (hG : Nat.card G = 2) : ∃ σ : G, σ ≠ 1 := by
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  exact exists_ne 1

open Classical in

def signChar (hG : Nat.card G = 2) : G →* ℂˣ where
  toFun σ := if σ = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' σ τ := by
    by_cases hσ : σ = 1
    · subst hσ
      simp
    by_cases hτ : τ = 1
    · subst hτ
      simp
    obtain rfl := eq_of_ne_one_of_card_eq_two hG hσ hτ
    simp [mul_self_eq_one_of_card_eq_two hG, hσ]

/- English proof (translation)
Simplify using `[signChar, hσ]`.
-/
theorem signChar_apply_of_ne_one (hG : Nat.card G = 2) {σ : G} (hσ : σ ≠ 1) :
    signChar hG σ = -1 := by
  classical
  simp [signChar, hσ]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_ne_one_of_card_eq_two hG`. Introduce `h`. Establish `h1` using `signChar_apply_of_ne_one hG hσ`. Rewrite `h1` using `[h, MonoidHom.one_apply]`. Establish `h2` using `congrArg (fun u : ℂˣ ↦ (u : ℂ)) h1`.

Evaluate the numerical expressions using `at h2`.
-/
theorem signChar_ne_one (hG : Nat.card G = 2) : signChar hG ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_ne_one_of_card_eq_two hG
  intro h
  have h1 := signChar_apply_of_ne_one hG hσ
  rw [h, MonoidHom.one_apply] at h1
  have h2 := congrArg (fun u : ℂˣ ↦ (u : ℂ)) h1
  norm_num at h2

end Two

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

/- English proof (translation)
Rewrite using `[IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]`.
-/
theorem card_gal : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]

def galChar : Gal(K/ℚ) →* ℂˣ :=
  signChar (card_gal K)

/- English proof (translation)
The claim follows from `signChar_apply_of_ne_one (card_gal K) hσ`.
-/
theorem galChar_apply_of_ne_one {σ : Gal(K/ℚ)} (hσ : σ ≠ 1) : galChar K σ = -1 :=
  signChar_apply_of_ne_one (card_gal K) hσ

/- English proof (translation)
The claim follows from `map_one _`.
-/
theorem galChar_one_apply : galChar K 1 = 1 :=
  map_one _

/- English proof (translation)
The claim follows from `signChar_ne_one (card_gal K)`.
-/
theorem galChar_ne_one : galChar K ≠ 1 :=
  signChar_ne_one (card_gal K)

def heckeChar : HeckeCharacter ℚ :=
  heckeCharacterOfChar (galChar K)

/- English proof (translation)
The claim follows from `isOfFinOrder_heckeCharacterOfChar _`.
-/
theorem isOfFinOrder_heckeChar : IsOfFinOrder (heckeChar K) :=
  isOfFinOrder_heckeCharacterOfChar _

/- English proof (translation)
The claim follows from `fun h ↦ galChar_ne_one K (eq_one_of_heckeCharacterOfChar_eq_one _ h)`.
-/
theorem heckeChar_ne_one : heckeChar K ≠ 1 := fun h ↦
  galChar_ne_one K (eq_one_of_heckeCharacterOfChar_eq_one _ h)

def kroneckerData : DirichletHecke.PrimitiveDirichletCharacter :=
  DirichletHecke.finiteOrderEquiv.symm ⟨heckeChar K, isOfFinOrder_heckeChar K⟩

def level : ℕ :=
  ((kroneckerData K).1 : ℕ)

instance : NeZero (level K) :=
  ⟨(kroneckerData K).1.ne_zero⟩

def kronecker : DirichletCharacter ℂ (level K) :=
  (kroneckerData K).2.1

/- English proof (translation)
The claim follows from `(kroneckerData K).2.2`.
-/
theorem isPrimitive_kronecker : (kronecker K).IsPrimitive :=
  (kroneckerData K).2.2

/- English proof (translation)
Establish `h` using `DirichletHecke.coe_finiteOrderEquiv_apply (kroneckerData K)`. Establish `h2 : DirichletHecke.finiteOrderEquiv (kroneckerData K) = ⟨heckeChar K, isOfFinOrder_heckeChar K⟩` using `Equiv.apply_symm_apply _ _`. Rewrite `h` using `[h2]`. Conclude with `h.symm`.
-/
theorem heckeCharacter_kronecker : DirichletHecke.heckeCharacter (kronecker K) = heckeChar K := by
  have h := DirichletHecke.coe_finiteOrderEquiv_apply (kroneckerData K)
  have h2 : DirichletHecke.finiteOrderEquiv (kroneckerData K) =
      ⟨heckeChar K, isOfFinOrder_heckeChar K⟩ :=
    Equiv.apply_symm_apply _ _
  rw [h2] at h
  exact h.symm

/- English proof (translation)
Introduce `h`. Apply `heckeChar_ne_one K` to reduce the goal to its premises. Rewrite using `[← heckeCharacter_kronecker K, h]`. Use extensionality with `x`. Rewrite using `[DirichletHecke.coe_heckeCharacter_apply]`.

Use `(MulChar.one_apply ((Units.isUnit _).map _)).trans ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem kronecker_ne_one : kronecker K ≠ 1 := by
  intro h
  apply heckeChar_ne_one K
  rw [← heckeCharacter_kronecker K, h]
  ext x
  rw [DirichletHecke.coe_heckeCharacter_apply]
  refine (MulChar.one_apply ((Units.isUnit _).map _)).trans ?_
  rfl

/- English proof (translation)
Rewrite using `[← LSeries_one_eq_riemannZeta hs, dedekindZeta]`. Use `LSeries_congr (fun {n} _ ↦ ?_) s` and prove the remaining obligations. Rewrite using `[Pi.one_apply, Nat.cast_eq_one, Nat.card_eq_one_iff_exists]`. Use `⟨⟨Ideal.span {(n : 𝓞 ℚ)}, DirichletHecke.absNorm_span_natCast n⟩, fun I ↦ ?_⟩` and prove the remaining obligations. Conclude with `Subtype.ext (DirichletHecke.eq_span_of_absNorm_eq I.2)`.
-/
theorem dedekindZeta_rat {s : ℂ} (hs : 1 < s.re) : dedekindZeta ℚ s = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs, dedekindZeta]
  refine LSeries_congr (fun {n} _ ↦ ?_) s
  rw [Pi.one_apply, Nat.cast_eq_one, Nat.card_eq_one_iff_exists]
  refine ⟨⟨Ideal.span {(n : 𝓞 ℚ)}, DirichletHecke.absNorm_span_natCast n⟩, fun I ↦ ?_⟩
  exact Subtype.ext (DirichletHecke.eq_span_of_absNorm_eq I.2)

/- English proof (translation)
Use `Fintype.ofFinite Gal(K/ℚ)` as an intermediate fact. Use function extensionality and compare the values at `σ`. Rewrite using `[GroundTheory.LocalField.character_leftRegular, Fintype.card_eq_nat_card, card_gal, Pi.add_apply, Pi.one_apply]`. Distinguish the cases in `hσ : σ = 1`. Substitute `hσ` using the available equality.

Rewrite using `[if_pos rfl, galChar_one_apply]`. Evaluate the numerical expressions. Rewrite using `[if_neg hσ, galChar_apply_of_ne_one K hσ]`. Evaluate the numerical expressions.
-/
theorem character_leftRegular :
    (Representation.leftRegular ℂ Gal(K/ℚ)).character =
      1 + fun σ ↦ ((galChar K σ : ℂˣ) : ℂ) := by
  classical
  have := Fintype.ofFinite Gal(K/ℚ)
  funext σ
  rw [GroundTheory.LocalField.character_leftRegular, Fintype.card_eq_nat_card, card_gal, Pi.add_apply,
    Pi.one_apply]
  by_cases hσ : σ = 1
  · subst hσ
    rw [if_pos rfl, galChar_one_apply]
    norm_num
  · rw [if_neg hσ, galChar_apply_of_ne_one K hσ]
    norm_num

/- English proof (translation)
Use `Fintype.ofFinite Gal(K/ℚ)` as an intermediate fact. Rewrite using `[← Artin.artinL_leftRegular (K := ℚ) hs, character_leftRegular, artinL_add _ _ hs, artinL_one hs, artinL_eq_LFunction _ hs, dedekindZeta_rat hs, show heckeCharacterOfChar (galChar K) = DirichletHecke.heckeCharacter (kronecker K) from (heckeCharacter_kronecker K).symm, DirichletHe …`.
-/
theorem dedekindZeta_eq_mul {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction (kronecker K) s := by
  have := Fintype.ofFinite Gal(K/ℚ)
  rw [← Artin.artinL_leftRegular (K := ℚ) hs, character_leftRegular, artinL_add _ _ hs,
    artinL_one hs, artinL_eq_LFunction _ hs, dedekindZeta_rat hs,
    show heckeCharacterOfChar (galChar K) = DirichletHecke.heckeCharacter (kronecker K) from
      (heckeCharacter_kronecker K).symm,
    DirichletHecke.LFunction_heckeCharacter _ (isPrimitive_kronecker K) hs]

/- English proof (translation)
Establish `hU : IsOpen ({1}ᶜ : Set ℂ)` using `isOpen_compl_singleton`. Establish `hpc : IsPreconnected ({1}ᶜ : Set ℂ)` using `DirichletHecke.isPreconnected_compl_of_countable (Set.countable_singleton 1)`. Establish `hf : AnalyticOnNhd ℂ (continuedDedekindZeta K) {1}ᶜ` using `(differentiableOn_continuedDedekindZeta K).analyticOnNhd hU`. Establish `hg : AnalyticOnNhd ℂ (fun z ↦ riemannZeta z * DirichletCharacter.LFunction (kronecker K) z) {1}ᶜ` using `(DifferentiableOn.mul (fun z hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt) (DirichletCharacter.differentiable_LFunction (kronecker_ne_one K)).differentiableOn).analyticOnNhd hU`. Use `hf.eqOn_of_preconnected_of_eventuallyEq hg hpc (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) ?_ hs` and prove the remaining obligations.

Use `filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz`. Rewrite using `[continuedDedekindZeta_eq K hz, dedekindZeta_eq_mul K hz]`.
-/
theorem continuedDedekindZeta_eq_mul {s : ℂ} (hs : s ≠ 1) :
    continuedDedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction (kronecker K) s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    DirichletHecke.isPreconnected_compl_of_countable (Set.countable_singleton 1)
  have hf : AnalyticOnNhd ℂ (continuedDedekindZeta K) {1}ᶜ :=
    (differentiableOn_continuedDedekindZeta K).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun z ↦ riemannZeta z * DirichletCharacter.LFunction (kronecker K) z)
      {1}ᶜ :=
    (DifferentiableOn.mul (fun z hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (DirichletCharacter.differentiable_LFunction (kronecker_ne_one K)).differentiableOn).analyticOnNhd
      hU
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hpc (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  rw [continuedDedekindZeta_eq K hz, dedekindZeta_eq_mul K hz]

/- English proof (translation)
Use `tendsto_nhds_unique ?_ (tendsto_sub_one_mul_continuedDedekindZeta K)` and prove the remaining obligations. Establish `hc` using `(DirichletCharacter.differentiable_LFunction (kronecker_ne_one K)).continuous.continuousAt (x := 1)`. Establish `h` using `riemannZeta_residue_one.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)`. Rewrite `h` using `[one_mul]`. Use `h.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)` and prove the remaining obligations.

Use `show _ = (s - 1) * continuedDedekindZeta K s`. Rewrite using `[continuedDedekindZeta_eq_mul K hs, mul_assoc]`.
-/
theorem LFunction_kronecker_one :
    DirichletCharacter.LFunction (kronecker K) 1 = (dedekindZeta_residue K : ℂ) := by
  refine tendsto_nhds_unique ?_ (tendsto_sub_one_mul_continuedDedekindZeta K)
  have hc := (DirichletCharacter.differentiable_LFunction (kronecker_ne_one K)).continuous.continuousAt
    (x := 1)
  have h := riemannZeta_residue_one.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  rw [one_mul] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
  show _ = (s - 1) * continuedDedekindZeta K s
  rw [continuedDedekindZeta_eq_mul K hs, mul_assoc]

/- English proof (translation)
Rewrite using `[LFunction_kronecker_one, Complex.ofReal_re, Complex.ofReal_im]`. Conclude with `⟨dedekindZeta_residue_pos K, rfl⟩`.
-/
theorem LFunction_kronecker_one_pos :
    0 < (DirichletCharacter.LFunction (kronecker K) 1).re ∧
      (DirichletCharacter.LFunction (kronecker K) 1).im = 0 := by
  rw [LFunction_kronecker_one, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨dedekindZeta_residue_pos K, rfl⟩

/- English proof (translation)
Rewrite using `[card_add_two_mul_card_eq_rank, Algebra.IsQuadraticExtension.finrank_eq_two]`.
-/
theorem nrRealPlaces_add_two_mul : nrRealPlaces K + 2 * nrComplexPlaces K = 2 := by
  rw [card_add_two_mul_card_eq_rank, Algebra.IsQuadraticExtension.finrank_eq_two]

/- English proof (translation)
Establish `h2` using `nrRealPlaces_add_two_mul K`. Establish `hs` using `sign_discr K`. Rewrite `hs` using `[Int.sign_eq_neg_one_of_neg hd]`. Break down `(by omega : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1) with h | h` into its components or cases. Rewrite `hs` using `[h, pow_zero]`.

Evaluate the numerical expressions using `at hs`. Use linear arithmetic over natural numbers and integers.
-/
theorem places_of_discr_neg (hd : discr K < 0) : nrRealPlaces K = 0 ∧ nrComplexPlaces K = 1 := by
  have h2 := nrRealPlaces_add_two_mul K
  have hs := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg hd] at hs
  rcases (by omega : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1) with h | h
  · rw [h, pow_zero] at hs
    norm_num at hs
  · omega

/- English proof (translation)
Establish `h2` using `nrRealPlaces_add_two_mul K`. Establish `hs` using `sign_discr K`. Rewrite `hs` using `[Int.sign_eq_one_of_pos hd]`. Break down `(by omega : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1) with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers.

Rewrite `hs` using `[h, pow_one]`. Evaluate the numerical expressions using `at hs`.
-/
theorem places_of_discr_pos (hd : 0 < discr K) : nrRealPlaces K = 2 ∧ nrComplexPlaces K = 0 := by
  have h2 := nrRealPlaces_add_two_mul K
  have hs := sign_discr K
  rw [Int.sign_eq_one_of_pos hd] at hs
  rcases (by omega : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1) with h | h
  · omega
  · rw [h, pow_one] at hs
    norm_num at hs

/- English proof (translation)
Establish `hcard : Fintype.card (InfinitePlace F) = 1`. Rewrite using `[card_eq_nrRealPlaces_add_nrComplexPlaces, h]`. Establish `hrank : rank F = 0`. Rewrite using `[rank, hcard]`. Establish `: IsEmpty (Fin (rank F))`.

Rewrite using `[hrank]`. Use `infer_instance`. Establish `: IsEmpty {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀}` using `⟨fun w ↦ w.2 (Fintype.card_le_one_iff.1 hcard.le _ _)⟩`. Rewrite using `[regulator_eq_det', Matrix.det_isEmpty, abs_one]`.
-/
theorem regulator_eq_one_of_card_eq_one {F : Type*} [Field F] [NumberField F]
    (h : nrRealPlaces F + nrComplexPlaces F = 1) : regulator F = 1 := by
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, h]
  have hrank : rank F = 0 := by
    rw [rank, hcard]
  classical
  have : IsEmpty (Fin (rank F)) := by
    rw [hrank]
    infer_instance
  have : IsEmpty {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀} :=
    ⟨fun w ↦ w.2 (Fintype.card_le_one_iff.1 hcard.le _ _)⟩
  rw [regulator_eq_det', Matrix.det_isEmpty, abs_one]

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Set `` to `Fintype.ofFinite (torsion F)`. Rewrite using `[torsionOrder, Nat.card_eq_fintype_card]`. Use `Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩, by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]`. Use `by_cases! hc : 2 < orderOf (x : (𝓞 F)ˣ)`.

Rewrite `hc` using `[← orderOf_units, ← orderOf_submonoid]`. Combine the linear relations using `[IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : F))]`. Use `interval_cases hi : orderOf (x : (𝓞 F)ˣ)`. Combine the linear relations using `[orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]`. Conclude with `Or.intro_left _ (orderOf_eq_one_iff.1 hi)`.

Rewrite `hi` using `[← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)]`. Simplify using `[← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]`.
-/
theorem torsionOrder_eq_two_of_nrRealPlaces_pos {F : Type*} [Field F] [NumberField F]
    (h : 0 < nrRealPlaces F) : torsionOrder F = 2 := by
  classical
  let := Fintype.ofFinite (torsion F)
  rw [torsionOrder, Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  by_cases! hc : 2 < orderOf (x : (𝓞 F)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : F))]
  · interval_cases hi : orderOf (x : (𝓞 F)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]

/- English proof (translation)
Take `⟨h1, h2⟩` from `places_of_discr_neg K hd`. Establish `hR : regulator K = 1` using `regulator_eq_one_of_card_eq_one (by omega)`. Rewrite using `[LFunction_kronecker_one, dedekindZeta_residue_def, h1, h2, hR]`. Establish `hd0 : ((Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))).ne'`. Establish `hw : (torsionOrder K : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (torsionOrder_ne_zero K)`.

Establish `hπ : (π : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 Real.pi_ne_zero`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem classNumber_eq_of_discr_neg (hd : discr K < 0) :
    (classNumber K : ℂ) = torsionOrder K * Real.sqrt |(discr K : ℝ)| *
      DirichletCharacter.LFunction (kronecker K) 1 / (2 * π) := by
  obtain ⟨h1, h2⟩ := places_of_discr_neg K hd
  have hR : regulator K = 1 := regulator_eq_one_of_card_eq_one (by omega)
  rw [LFunction_kronecker_one, dedekindZeta_residue_def, h1, h2, hR]
  have hd0 : ((Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
    (Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))).ne'
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_ne_zero K)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

/- English proof (translation)
Take `⟨h1, h2⟩` from `places_of_discr_pos K hd`. Establish `hw : torsionOrder K = 2` using `torsionOrder_eq_two_of_nrRealPlaces_pos (by omega)`. Establish `hd' : (0 : ℝ) < discr K` using `Int.cast_pos.2 hd`. Rewrite using `[LFunction_kronecker_one, dedekindZeta_residue_def, h1, h2, hw, abs_of_pos hd']`. Establish `hd0 : ((Real.sqrt (discr K : ℝ) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hd').ne'`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem classNumber_mul_regulator_eq_of_discr_pos (hd : 0 < discr K) :
    ((classNumber K * regulator K : ℝ) : ℂ) = Real.sqrt (discr K : ℝ) *
      DirichletCharacter.LFunction (kronecker K) 1 / 2 := by
  obtain ⟨h1, h2⟩ := places_of_discr_pos K hd
  have hw : torsionOrder K = 2 := torsionOrder_eq_two_of_nrRealPlaces_pos (by omega)
  have hd' : (0 : ℝ) < discr K := Int.cast_pos.2 hd
  rw [LFunction_kronecker_one, dedekindZeta_residue_def, h1, h2, hw, abs_of_pos hd']
  have hd0 : ((Real.sqrt (discr K : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hd').ne'
  push_cast
  field_simp

end Quadratic

end GroundTheory.Global
