import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RealFormBasis

variable {n : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Rewrite using `[Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private theorem Jm_mul_self_eq_one' {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Rewrite using `[Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases h : ε a <;> simp [h]`.
-/
private theorem Jm_conjTransposeFlagMeasures {n : ℕ} (ε : Fin n → Bool) :
    (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, Jm_mul_self_eq_one', Matrix.one_mul]`.
-/
private theorem Jm_mul_Jm_mul' {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_mul_self_eq_one', Matrix.one_mul]

/- English proof (translation)
Unfold `Formalism.REAL.inG`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `congrArg (fun M => Formalism.REAL.Jm ε * M) h`. Simplify using `only [Matrix.mul_add, Matrix.mul_zero, Jm_mul_Jm_mul'] at h'`.

Rewrite `h'` using `[← Matrix.mul_assoc]`. Conclude with `eq_neg_of_add_eq_zero_left h'`. Introduce `h`. Establish `h'` using `congrArg (fun M => Formalism.REAL.Jm ε * M) h`. Simplify using `only [Matrix.mul_assoc, Jm_mul_Jm_mul', Matrix.mul_neg] at h'`.

Rewrite using `[h', neg_add_cancel]`.
-/
theorem inG_iff_adj (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε X ↔ Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε = -X := by
  unfold Formalism.REAL.inG
  constructor
  · intro h

    have h' := congrArg (fun M => Formalism.REAL.Jm ε * M) h
    simp only [Matrix.mul_add, Matrix.mul_zero, Jm_mul_Jm_mul'] at h'
    rw [← Matrix.mul_assoc] at h'
    exact eq_neg_of_add_eq_zero_left h'
  · intro h
    have h' := congrArg (fun M => Formalism.REAL.Jm ε * M) h
    simp only [Matrix.mul_assoc, Jm_mul_Jm_mul', Matrix.mul_neg] at h'
    rw [h', neg_add_cancel]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTransposeFlagMeasures]`. Simplify using `only [Matrix.mul_assoc, Jm_mul_Jm_mul', Jm_mul_self_eq_one', Matrix.mul_one]`.
-/
theorem adj_adj (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε = X := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Jm_conjTransposeFlagMeasures]
  simp only [Matrix.mul_assoc, Jm_mul_Jm_mul', Jm_mul_self_eq_one', Matrix.mul_one]

/- English proof (translation)
Establish `hS_add : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X + Y)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε`. Introduce `X Y`. Rewrite using `[Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]`. Establish `hS_sub : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X - Y)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε - Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε`. Introduce `X Y`.

Rewrite using `[Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]`. Establish `hS_smul : ∀ (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.Jm ε * (c • X)ᴴ * Formalism.REAL.Jm ε = star c • (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)`. Introduce `c X`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hS_sum : ∀ g : Fin d → ℂ, Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε = ∑ i, star (g i) • (Formalism.REAL.Jm ε * (E i)ᴴ * Formalism.REAL.Jm ε)`.

Introduce `g`. Rewrite using `[Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `hS_smul (g i) (E i)`. Establish `hEmem : ∀ k, E k ∈ N ∧ Formalism.REAL.inG ε (E k)` using `fun k => (hs (E k)).2 (Submodule.subset_span ⟨k, rfl⟩)`.

Establish `hEadj : ∀ k, Formalism.REAL.Jm ε * (E k)ᴴ * Formalism.REAL.Jm ε = -E k` using `fun k => (inG_iff_adj ε (E k)).1 (hEmem k).2`. Establish `hLI : LinearIndependent ℂ E`. Rewrite `hE`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h1 : ∑ i, star (g i) • E i = 0`.

Establish `h : Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε` using `by rw [hg]`. Rewrite `h` using `[hS_sum, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul]`. Simplify `h` using `only [hEadj, smul_neg, Finset.sum_neg_distrib, neg_eq_zero]`. Establish `hre : ∑ i, (2 * (g i).re) • E i = 0`. Establish `h2 : ∑ i, (2 * (g i).re) • E i = (∑ i, g i • E i) + ∑ i, star (g i) • E i`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← add_smul, ← Complex.coe_smul]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.

Rewrite using `[h2, hg, h1, add_zero]`. Establish `him : ∑ i, (2 * (g i).im) • E i = 0`. Establish `h2 : ∑ i, (2 * (g i).im) • E i = (-Complex.I) • ((∑ i, g i • E i) - ∑ i, star (g i) • E i)`. Rewrite using `[← Finset.sum_sub_distrib, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← sub_smul, smul_smul, ← Complex.coe_smul]`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Rewrite using `[h2, hg, h1, sub_zero, smul_zero]`. Establish `a` using `hE _ hre i`.

Establish `b` using `hE _ him i`. Apply the tactic sequence `apply Complex.ext <;> simp <;> linarith`. Establish `hspan : N = Submodule.span ℂ (Set.range E)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `X hX`.

Establish `hSX : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N` using `hN X hX`. Establish `hSS` using `adj_adj ε X`. Establish `hA : (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈ Submodule.span ℝ (Set.range E)`. Use `(hs _).1 ⟨N.smul_mem _ (N.sub_mem hX hSX), ?_⟩` and prove the remaining obligations. Rewrite using `[inG_iff_adj, hS_smul, hS_sub, hSS, ← smul_neg, neg_sub]`.

Use `congr 1`. Simplify using the standard rewrite rules. Establish `hB : (-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈ Submodule.span ℝ (Set.range E)`. Use `(hs _).1 ⟨N.smul_mem _ (N.add_mem hX hSX), ?_⟩` and prove the remaining obligations. Rewrite using `[inG_iff_adj, hS_smul, hS_add, hSS, add_comm (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) X, ← neg_smul]`.

Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp <;> norm_num`. Establish `hA'` using `Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hA`. Establish `hB'` using `Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hB`. Establish `hX_eq : X = (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) + Complex.I • ((-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε))`.

Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hX_eq]`. Conclude with `Submodule.add_mem _ hA' (Submodule.smul_mem _ _ hB')`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `(hEmem k).1`.

Establish `hfin : Module.finrank ℂ N = d`. Rewrite using `[hspan, finrank_span_eq_card hLI, Fintype.card_fin]`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Introduce `φ L hφ`. Set `E' : Fin d → N` to `fun k => ⟨E k, (hEmem k).1⟩`.

Establish `hLI' : LinearIndependent ℂ E'` using `LinearIndependent.of_comp N.subtype hLI`. Establish `hsp : ⊤ ≤ Submodule.span ℂ (Set.range E')`. Introduce and unpack `⟨X, hX⟩ -`. Establish `hX' : X ∈ Submodule.span ℂ (Set.range E)` using `by rw [← hspan]; exact hX`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hX'`.

Establish `hXc : (⟨X, hX⟩ : N) = ∑ i, c i • E' i`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[E', ← hc]`. Rewrite using `[hXc]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Set `b` to `Module.Basis.mk hLI' hsp`. Rewrite using `[← LinearMap.det_toMatrix b]`. Establish `hM : LinearMap.toMatrix b b φ = L.map (fun r : ℝ => (r : ℂ))`. Use extensionality with `i k`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.map_apply]`.

Establish `hφk : φ (b k) = ∑ j, ((L j k : ℝ) : ℂ) • b j`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `hφ k (hEmem k).1`. Simplify using `only [b, Module.Basis.mk_apply, E', Submodule.coe_sum, Submodule.coe_smul] at h ⊢`. Rewrite using `[h]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.coe_smul]`. Rewrite using `[hφk]`. Establish `hc : ∑ j, ((L j k : ℝ) : ℂ) • b j = b.equivFun.symm (fun j => ((L j k : ℝ) : ℂ))`. Rewrite using `[Module.Basis.equivFun_symm_apply]`.

Rewrite using `[hc, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[hM]`. Conclude with `(RingHom.map_det Complex.ofRealHom L).symm`.
-/
theorem finrank_and_det (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) (hE : LinearIndependent ℝ E)
    (hs : ∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) :
    Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ),
      (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) →
      LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  classical

  have hS_add : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X + Y)ᴴ * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    intro X Y
    rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  have hS_sub : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X - Y)ᴴ * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε - Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    intro X Y
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hS_smul : ∀ (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.Jm ε * (c • X)ᴴ * Formalism.REAL.Jm ε =
      star c • (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) := by
    intro c X
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hS_sum : ∀ g : Fin d → ℂ, Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε =
      ∑ i, star (g i) • (Formalism.REAL.Jm ε * (E i)ᴴ * Formalism.REAL.Jm ε) := by
    intro g
    rw [Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hS_smul (g i) (E i)

  have hEmem : ∀ k, E k ∈ N ∧ Formalism.REAL.inG ε (E k) := fun k =>
    (hs (E k)).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hEadj : ∀ k, Formalism.REAL.Jm ε * (E k)ᴴ * Formalism.REAL.Jm ε = -E k := fun k =>
    (inG_iff_adj ε (E k)).1 (hEmem k).2

  have hLI : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff] at hE ⊢
    intro g hg i
    have h1 : ∑ i, star (g i) • E i = 0 := by
      have h : Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε =
          Formalism.REAL.Jm ε * (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε := by rw [hg]
      rw [hS_sum, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul] at h
      simpa only [hEadj, smul_neg, Finset.sum_neg_distrib, neg_eq_zero] using h
    have hre : ∑ i, (2 * (g i).re) • E i = 0 := by
      have h2 : ∑ i, (2 * (g i).re) • E i = (∑ i, g i • E i) + ∑ i, star (g i) • E i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_smul, ← Complex.coe_smul]
        congr 1
        apply Complex.ext <;> simp <;> ring
      rw [h2, hg, h1, add_zero]
    have him : ∑ i, (2 * (g i).im) • E i = 0 := by
      have h2 : ∑ i, (2 * (g i).im) • E i =
          (-Complex.I) • ((∑ i, g i • E i) - ∑ i, star (g i) • E i) := by
        rw [← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, smul_smul, ← Complex.coe_smul]
        congr 1
        apply Complex.ext <;> simp <;> ring
      rw [h2, hg, h1, sub_zero, smul_zero]
    have a := hE _ hre i
    have b := hE _ him i
    apply Complex.ext <;> simp <;> linarith

  have hspan : N = Submodule.span ℂ (Set.range E) := by
    apply le_antisymm
    · intro X hX
      have hSX : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N := hN X hX
      have hSS := adj_adj ε X
      have hA : (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈
          Submodule.span ℝ (Set.range E) := by
        refine (hs _).1 ⟨N.smul_mem _ (N.sub_mem hX hSX), ?_⟩
        rw [inG_iff_adj, hS_smul, hS_sub, hSS, ← smul_neg, neg_sub]
        congr 1
        simp
      have hB : (-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈
          Submodule.span ℝ (Set.range E) := by
        refine (hs _).1 ⟨N.smul_mem _ (N.add_mem hX hSX), ?_⟩
        rw [inG_iff_adj, hS_smul, hS_add, hSS, add_comm (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) X,
          ← neg_smul]
        congr 1
        apply Complex.ext <;> simp <;> norm_num
      have hA' := Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hA
      have hB' := Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hB
      have hX_eq : X = (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) +
          Complex.I • ((-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hX_eq]
      exact Submodule.add_mem _ hA' (Submodule.smul_mem _ _ hB')
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact (hEmem k).1
  have hfin : Module.finrank ℂ N = d := by
    rw [hspan, finrank_span_eq_card hLI, Fintype.card_fin]
  refine ⟨hfin, ?_⟩
  intro φ L hφ

  let E' : Fin d → N := fun k => ⟨E k, (hEmem k).1⟩
  have hLI' : LinearIndependent ℂ E' := LinearIndependent.of_comp N.subtype hLI
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range E') := by
    rintro ⟨X, hX⟩ -
    have hX' : X ∈ Submodule.span ℂ (Set.range E) := by rw [← hspan]; exact hX
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hX'
    have hXc : (⟨X, hX⟩ : N) = ∑ i, c i • E' i := by
      apply Subtype.ext
      simp [E', ← hc]
    rw [hXc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b := Module.Basis.mk hLI' hsp
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b φ = L.map (fun r : ℝ => (r : ℂ)) := by
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    have hφk : φ (b k) = ∑ j, ((L j k : ℝ) : ℂ) • b j := by
      apply Subtype.ext
      have h := hφ k (hEmem k).1
      simp only [b, Module.Basis.mk_apply, E', Submodule.coe_sum, Submodule.coe_smul] at h ⊢
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.coe_smul]
    rw [hφk]
    have hc : ∑ j, ((L j k : ℝ) : ℂ) • b j = b.equivFun.symm (fun j => ((L j k : ℝ) : ℂ)) := by
      rw [Module.Basis.equivFun_symm_apply]
    rw [hc, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [hM]
  exact (RingHom.map_det Complex.ofRealHom L).symm

end GlobalTheory.RealFormBasis
