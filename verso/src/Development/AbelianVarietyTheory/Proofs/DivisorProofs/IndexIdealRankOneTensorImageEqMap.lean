import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantIndexIdealMapInjectiveEqColonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantSpanSpanEqGeneratorDetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneFgLatticeEqFractionalIdealSmulVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentImagesOfRankOneLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonPowMulCancelFgFractionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonOneSpanImageEqMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanScaledMappedRowDetsEqPowMulSpanStatement

set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor
/- English proof (translation)
The claim follows from `GlobalTheory.T.latticeDeterminantIndexIdeal_map_injective_eq_colon`.
-/
theorem cut_idxmap : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := GlobalTheory.T.latticeDeterminantIndexIdeal_map_injective_eq_colon

/- English proof (translation)
The claim follows from `GlobalTheory.T.latticeDeterminantSpan_span_eq_generator_dets`.
-/
theorem cut_detsspan : ∀ {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)),
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := GlobalTheory.T.latticeDeterminantSpan_span_eq_generator_dets

/- English proof (translation)
The claim follows from `GlobalTheory.T.rankOne_fg_lattice_eq_fractionalIdeal_smul_vector`.
-/
theorem cut_rankone : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (ell : Submodule (𝓞 K) (Fin m → K)),
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := GlobalTheory.T.rankOne_fg_lattice_eq_fractionalIdeal_smul_vector

/- English proof (translation)
The claim follows from `GlobalTheory.T.linearIndependent_images_of_iSupIndep_rankOne`.
-/
theorem cut_linindep : ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := GlobalTheory.T.linearIndependent_images_of_iSupIndep_rankOne

/- English proof (translation)
The claim follows from `GlobalTheory.T.colon_pow_mul_cancel_fg_fractional`.
-/
theorem cut_cancel : ∀ {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K), 𝔟.FG → 𝔟 ≠ ⊥ →
    ∀ (p : ℕ) (A N : Submodule (𝓞 K) K),
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := GlobalTheory.T.colon_pow_mul_cancel_fg_fractional

/- English proof (translation)
The claim follows from `GlobalTheory.T.colon_one_span_image_eq_map_colon`.
-/
theorem cut_extend : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
    ∀ (A : Submodule (𝓞 E) E), A.FG → (1 : E) ∈ A →
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := GlobalTheory.T.colon_one_span_image_eq_map_colon

/- English proof (translation)
The claim follows from `GlobalTheory.T.span_scaled_mapped_row_dets_eq_pow_mul_span`.
-/
theorem cut_twistgens : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)),
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := GlobalTheory.T.span_scaled_mapped_row_dets_eq_pow_mul_span

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨y, hy, rfl⟩`. Take `⟨z, rfl⟩` from `Submodule.mem_one.1 hy`. Conclude with `Submodule.mem_one.2 ⟨τ z, (hτ z).symm⟩`.

Rewrite using `[Submodule.one_le]`. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, map_one τE⟩`.
-/
theorem span_image_one {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) :
    Submodule.span (𝓞 K) (τE '' (1 : Submodule (𝓞 E) E)) = 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_one.1 hy
    exact Submodule.mem_one.2 ⟨τ z, (hτ z).symm⟩
  · rw [Submodule.one_le]
    apply Submodule.subset_span
    exact ⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, map_one τE⟩

/- English proof (translation)
Unfold `dets`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun a => Pi.single a 1, h, ?_⟩` and prove the remaining obligations. Establish `hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1`. Use extensionality with `i j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]`. Rewrite using `[hI, Matrix.det_one]`.
-/
theorem one_mem_dets {F : Type} [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F))
    (h : ∀ a, (Pi.single a (1 : F) : Fin p → F) ∈ L) : (1 : F) ∈ dets F p L := by
  unfold dets
  apply Submodule.subset_span
  refine ⟨fun a => Pi.single a 1, h, ?_⟩
  have hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]
  rw [hI, Matrix.det_one]

/- English proof (translation)
Rewrite using `[cut_detsspan]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `d ⟨y, hy, rfl⟩`. Use `choose f hf using fun i => Set.mem_range.1 (hy i)`.

Establish `hM : Matrix.of y = (Matrix.of fun i j => (Pi.single (f i) (1 : 𝓞 F) : Fin p → 𝓞 F) j).map (algebraMap (𝓞 F) F)`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.map_apply]`. Rewrite using `[← hf i]`. Distinguish the cases in `hij : j = f i`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hij]`. Rewrite using `[hM]`. Conclude with `Submodule.mem_one.2 ⟨_, RingHom.map_det _ _⟩`.

Rewrite using `[Submodule.one_le]`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun a => Pi.single a 1, fun i => ⟨i, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1`. Use extensionality with `i j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]`. Rewrite using `[hI, Matrix.det_one]`.
-/
theorem dets_std {F : Type} [Field F] [NumberField F] (p : ℕ) :
    dets F p (Submodule.span (𝓞 F) (Set.range fun a => (Pi.single a (1 : F) : Fin p → F))) = 1 := by
  rw [cut_detsspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    choose f hf using fun i => Set.mem_range.1 (hy i)
    have hM : Matrix.of y =
        (Matrix.of fun i j => (Pi.single (f i) (1 : 𝓞 F) : Fin p → 𝓞 F) j).map (algebraMap (𝓞 F) F) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.map_apply]
      rw [← hf i]
      by_cases hij : j = f i
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    rw [hM]
    exact Submodule.mem_one.2 ⟨_, RingHom.map_det _ _⟩
  · rw [Submodule.one_le]
    apply Submodule.subset_span
    refine ⟨fun a => Pi.single a 1, fun i => ⟨i, rfl⟩, ?_⟩
    have hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]
    rw [hI, Matrix.det_one]

/- English proof (translation)
Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, e, he, rfl⟩`.

Take `⟨β, hβ, rfl⟩` from `(hell e).1 he`. Use `⟨β • fun a => τE (c a), ⟨β, hβ, c, hc, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]`.

Introduce and unpack `⟨x, ⟨β, hβ, c, hc, rfl⟩, rfl⟩`. Use `⟨c, hc, β • v, (hell _).2 ⟨β, hβ, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]`.
-/
theorem big_eq_map {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (τE : E →+* K) {p m n : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K)))
    (Λ : Submodule (𝓞 E) (Fin p → E)) (v : Fin m → K) (𝔟 : Submodule (𝓞 K) K)
    (hell : ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) :
    Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e} =
      (Submodule.span (𝓞 K) {x | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}).map
        ((Fintype.linearCombination K (fun a => M a v)).restrictScalars (𝓞 K)) := by
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, e, he, rfl⟩
    obtain ⟨β, hβ, rfl⟩ := (hell e).1 he
    refine ⟨β • fun a => τE (c a), ⟨β, hβ, c, hc, rfl⟩, ?_⟩
    rw [LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]
  · rintro ⟨x, ⟨β, hβ, c, hc, rfl⟩, rfl⟩
    refine ⟨c, hc, β • v, (hell _).2 ⟨β, hβ, rfl⟩, ?_⟩
    rw [LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `a _ hab`. Simplify using `[Pi.single_apply, hab]`. Simplify using the standard rewrite rules.
-/
private lemma sum_single_smul_eq_apply {E K : Type} [Field E] [Field K] (τE : E →+* K) {p m n : ℕ}
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (b : Fin p) (e : Fin m → K) :
    ∑ a, τE ((Pi.single b (1 : E) : Fin p → E) a) • M a e = M b e := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Pi.single_apply, hab]
  · simp

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun b => ?_` and prove the remaining obligations. Introduce and unpack `w ⟨e, he, rfl⟩`. Conclude with `Submodule.subset_span ⟨Pi.single b 1, Submodule.subset_span ⟨b, rfl⟩, e, he, (sum_single_smul_eq_apply τE M b e).symm⟩`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `w ⟨c, hc, e, he, rfl⟩`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`. Use `beta_reduce`.

Rewrite using `[sum_single_smul_eq_apply τE M b e]`. Conclude with `Submodule.mem_iSup_of_mem b ⟨e, he, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]`.

Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx`. Establish `key : ∀ a, τE ((r • x) a) • M a e = τ r • (τE (x a) • M a e)`. Introduce `a`. Rewrite using `[Pi.smul_apply, Algebra.smul_def r (x a), map_mul, mul_smul, ← algebraMap_smul K (τ r)]`.

Use `congr 1`. Conclude with `hτ r`. Rewrite using `[Finset.sum_congr rfl (fun a _ => key a), ← Finset.smul_sum]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem small_eq_big_std {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) {p m n : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) :
    (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      Submodule.span (𝓞 K) {w | ∃ c ∈ Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)),
        ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e} := by
  apply le_antisymm
  · refine iSup_le fun b => ?_
    rintro w ⟨e, he, rfl⟩
    exact Submodule.subset_span
      ⟨Pi.single b 1, Submodule.subset_span ⟨b, rfl⟩, e, he, (sum_single_smul_eq_apply τE M b e).symm⟩
  · rw [Submodule.span_le]
    rintro w ⟨c, hc, e, he, rfl⟩
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      beta_reduce
      rw [sum_single_smul_eq_apply τE M b e]
      exact Submodule.mem_iSup_of_mem b ⟨e, he, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul r x _ hx =>
      have key : ∀ a, τE ((r • x) a) • M a e = τ r • (τE (x a) • M a e) := by
        intro a
        rw [Pi.smul_apply, Algebra.smul_def r (x a), map_mul, mul_smul, ← algebraMap_smul K (τ r)]
        congr 1
        exact hτ r
      rw [Finset.sum_congr rfl (fun a _ => key a), ← Finset.smul_sum]
      exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Take `⟨S, rfl⟩` from `h`. Rewrite using `[cut_detsspan]`. Apply `Submodule.fg_span` to reduce the goal to its premises. Use `((Set.Finite.pi (fun _ : Fin p => S.finite_toSet)).image (fun y : Fin p → Fin p → F => (Matrix.of y).det)).subset ?_` and prove the remaining obligations. Introduce and unpack `d ⟨y, hy, rfl⟩`.

Conclude with `⟨y, fun i _ => hy i, rfl⟩`.
-/
theorem dets_fg {F : Type} [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) (h : L.FG) :
    (dets F p L).FG := by
  obtain ⟨S, rfl⟩ := h
  rw [cut_detsspan]
  apply Submodule.fg_span
  refine ((Set.Finite.pi (fun _ : Fin p => S.finite_toSet)).image
    (fun y : Fin p → Fin p → F => (Matrix.of y).det)).subset ?_
  rintro d ⟨y, hy, rfl⟩
  exact ⟨y, fun i _ => hy i, rfl⟩

/- English proof (translation)
Rewrite using `[cut_detsspan]`. Conclude with `cut_twistgens τ τE hτ p 𝔟 Λ`.
-/
theorem dets_twist {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)) :
    dets K p (Submodule.span (𝓞 K) {x | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' dets E p Λ) := by
  rw [cut_detsspan]
  exact cut_twistgens τ τE hτ p 𝔟 Λ

/- English proof (translation)
Introduce `E K _ _ _ _ τ τE hτ p m n ell M Λ hfg hrk hinj hind hΛfg hΛ`. Take `⟨v, hv, 𝔟, h𝔟fg, h𝔟, hell⟩` from `cut_rankone ell hrk hfg`. Establish `hφ : Function.Injective (Fintype.linearCombination K (fun a => M a v))` using `(cut_linindep ell M v hv 𝔟 h𝔟 hell hinj hind).fintypeLinearCombination_injective`. Establish `hsing : ∀ a, (Pi.single a (1 : E) : Fin p → E) ∈ Λ`. Introduce `a`.

Establish `h1` using `hΛ (Pi.single a 1)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `b`. Distinguish the cases in `hab : b = a`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hab]`. Establish `hD1 : (1 : E) ∈ GlobalTheory.IdxTensor.dets E p Λ` using `one_mem_dets p Λ hsing`. Establish `hDfg : (GlobalTheory.IdxTensor.dets E p Λ).FG` using `dets_fg p Λ hΛfg`. Establish `hR` using `cut_idxmap (V := Fin p → E) p (LinearMap.id) Function.injective_id Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))`.

Establish `hmapid : ∀ L : Submodule (𝓞 E) (Fin p → E), L.map ((LinearMap.id : (Fin p → E) →ₗ[E] (Fin p → E)).restrictScalars (𝓞 E)) = L`. Introduce `L`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite `hR` using `[hmapid, hmapid]`.

Rewrite using `[hR, small_eq_big_std τ τE hτ ell M, big_eq_map τE ell M Λ v 𝔟 hell, big_eq_map τE ell M _ v 𝔟 hell, cut_idxmap p _ hφ, dets_twist τ τE hτ, dets_twist τ τE hτ, dets_std, span_image_one τ τE hτ, cut_cancel 𝔟 h𝔟fg h𝔟 p _ 1]`. Conclude with `cut_extend τ τE hτ _ hDfg hD1`.
-/
theorem idx_image_eq_map : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K),
    (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p m n : ℕ) (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (Λ : Submodule (𝓞 E) (Fin p → E)),
    ell.FG → ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    GlobalTheory.FlatCM.idx K p (Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e})
                 (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map τ := by
  intro E K _ _ _ _ τ τE hτ p m n ell M Λ hfg hrk hinj hind hΛfg hΛ
  obtain ⟨v, hv, 𝔟, h𝔟fg, h𝔟, hell⟩ := cut_rankone ell hrk hfg
  have hφ : Function.Injective (Fintype.linearCombination K (fun a => M a v)) :=
    (cut_linindep ell M v hv 𝔟 h𝔟 hell hinj hind).fintypeLinearCombination_injective
  have hsing : ∀ a, (Pi.single a (1 : E) : Fin p → E) ∈ Λ := by
    intro a
    have h1 := hΛ (Pi.single a 1)
    convert h1 using 1
    funext b
    by_cases hab : b = a
    · subst hab; simp
    · simp [Pi.single_apply, hab]
  have hD1 : (1 : E) ∈ GlobalTheory.IdxTensor.dets E p Λ := one_mem_dets p Λ hsing
  have hDfg : (GlobalTheory.IdxTensor.dets E p Λ).FG := dets_fg p Λ hΛfg
  have hR := cut_idxmap (V := Fin p → E) p (LinearMap.id) Function.injective_id Λ
    (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))
  have hmapid : ∀ L : Submodule (𝓞 E) (Fin p → E),
      L.map ((LinearMap.id : (Fin p → E) →ₗ[E] (Fin p → E)).restrictScalars (𝓞 E)) = L := by
    intro L
    ext x
    simp
  rw [hmapid, hmapid] at hR
  rw [hR, small_eq_big_std τ τE hτ ell M, big_eq_map τE ell M Λ v 𝔟 hell, big_eq_map τE ell M _ v 𝔟 hell,
    cut_idxmap p _ hφ, dets_twist τ τE hτ, dets_twist τ τE hτ, dets_std, span_image_one τ τE hτ,
    cut_cancel 𝔟 h𝔟fg h𝔟 p _ 1]
  exact cut_extend τ τE hτ _ hDfg hD1

end GlobalTheory.IdxTensor

end
