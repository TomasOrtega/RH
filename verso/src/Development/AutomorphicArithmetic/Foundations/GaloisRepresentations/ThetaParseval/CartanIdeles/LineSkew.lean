import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf

noncomputable section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ δ 𝔞 hl B hpos hP d`. Use `⟨?skew, ?sig, ?lat, ?dual, ?cartan, ?bas⟩` and prove the remaining obligations. Use `case skew =>`. Introduce `i j`. Simplify using `only [skewSpc, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[hl.skew]`. Simplify using `[h, Ne.symm h]`. Use `case bas =>`.

Introduce `v`. Conclude with `absurd v.2 (by simp [hP])`. Use `case lat =>`. Establish `hl'` using `hl.lat`. Use `⟨Submodule.fg_pi (fun _ => hl'.fg), ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Rewrite using `[← Finset.univ_sum_single v]`. Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Establish `hv : v i ∈ Submodule.span E (𝔞 : Set E)` using `by rw [hl'.span_eq_top]; trivial`.

Establish `hm : Pi.single i (v i) ∈ (Submodule.span E (𝔞 : Set E)).map (LinearMap.single E (fun _ : Fin d => E) i)` using `⟨v i, hv, rfl⟩`. Rewrite `hm` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ hm` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `show _ ∈ Submodule.pi Set.univ (fun _ : Fin d => 𝔞)`.

Rewrite using `[Submodule.mem_pi]`. Introduce `j _`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `using ha`.

Simplify using `[h]`. Use `case dual =>`. Introduce `y`. Establish `hform : ∀ x : Fin d → E, form σ (skewSpc F δ 𝔞 d).J y x = ∑ i, y i * (δ * σ (x i))`. Introduce `x`.

Simplify using `[form, skewSpc, Matrix.smul_mulVec, dotProduct, smul_eq_mul]`. Establish `hmem : ∀ z : Fin d → E, z ∈ (skewSpc F δ 𝔞 d).L ↔ ∀ i, z i ∈ 𝔞`. Introduce `z`. Use `show z ∈ Submodule.pi Set.univ (fun _ : Fin d => 𝔞) ↔ _`. Simplify using `[Submodule.mem_pi]`.

Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx o`. Rewrite `hx` using `[hmem]`. Rewrite using `[hform, Finset.mul_sum, map_sum]`.

Conclude with `IsIntegral.sum _ (fun i _ => (hl.dual (y i)).1 (hy i) (x i) (hx i) o)`. Introduce `h i`. Rewrite using `[hl.dual]`. Introduce `x hx o`. Establish `hs : Pi.single i x ∈ (skewSpc F δ 𝔞 d).L`.

Rewrite using `[hmem]`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hx`.

Simplify using `[hj]`. Use `h _ hs o` as an intermediate fact. Rewrite `this` using `[hform, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]`. Simplify using `using this`. Use `case cartan =>`.

Introduce `w`. Take `⟨c, hc, he⟩` from `hpos w`. Establish `hM : Complex.I • (skewSpc F δ 𝔞 d).J.map ⇑(B.emb w : E →+* ℂ) = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[skewSpc, he]`. Simplify using `[skewSpc, h]`. Establish `hθ : (skewSpc F δ 𝔞 d).θ w = 1` using `rfl`. Rewrite using `[hM, hθ]`.

Use `⟨by simp, by simp, fun x hx => ?_⟩` and prove the remaining obligations. Establish `key : (1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ x ⬝ᵥ ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ star x = ((c * ∑ i, Complex.normSq (x i) : ℝ) : ℂ)`. Simplify using `[Matrix.smul_mulVec, dotProduct, Finset.mul_sum, Complex.mul_conj]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[← Complex.mul_conj]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, Complex.ofReal_re]`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hx`. Conclude with `mul_pos hc (Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩)`. Use `case sig =>`.

Introduce `w`. Take `⟨c, hc, he⟩` from `hpos w`. Establish `hM : Complex.I • (skewSpc F δ 𝔞 d).J.map ⇑(B.emb w : E →+* ℂ) = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[skewSpc, he]`. Simplify using `[skewSpc, h]`. Rewrite using `[hM]`. Use `⟨by simp, Matrix.of fun (k : Fin d) (p : Fin d ⊕ Fin 0) => Sum.elim (fun i => if k = i then (((Real.sqrt c)⁻¹ : ℝ) : ℂ) else 0) (fun z => z.elim0) p, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]`. Use extensionality with `(i | i) (j | j)`. Simplify using `[Matrix.mul_apply, Matrix.one_apply] split_ifs with h`. Rewrite using `[map_inv₀, Complex.conj_ofReal, ← mul_inv]`. Establish `hs : ((√c : ℝ) : ℂ) * (√c : ℂ) = c` using `by rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]`.

Rewrite using `[hs, mul_inv_cancel₀ (by exact_mod_cast hc.ne')]`. Simplify using the standard rewrite rules. Apply the tactic sequence `all_goals (first | exact i.elim0 | exact j.elim0)`.
-/
theorem lineSkew : LineSkew := by
  intro F E _ _ _ _ _ σ δ 𝔞 hl B hpos hP d
  refine ⟨?skew, ?sig, ?lat, ?dual, ?cartan, ?bas⟩
  case skew =>
    intro i j
    simp only [skewSpc, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : j = i
    · subst h; simp [hl.skew]
    · simp [h, Ne.symm h]
  case bas =>
    intro v
    exact absurd v.2 (by simp [hP])
  case lat =>
    have hl' := hl.lat
    refine ⟨Submodule.fg_pi (fun _ => hl'.fg), ?_⟩
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have hv : v i ∈ Submodule.span E (𝔞 : Set E) := by rw [hl'.span_eq_top]; trivial
    have hm : Pi.single i (v i) ∈ (Submodule.span E (𝔞 : Set E)).map (LinearMap.single E (fun _ : Fin d => E) i) := ⟨v i, hv, rfl⟩
    rw [Submodule.map_span] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨a, ha, rfl⟩
    show _ ∈ Submodule.pi Set.univ (fun _ : Fin d => 𝔞)
    rw [Submodule.mem_pi]
    intro j _
    by_cases h : j = i
    · subst h; simpa using ha
    · simp [h]
  case dual =>
    intro y
    have hform : ∀ x : Fin d → E, form σ (skewSpc F δ 𝔞 d).J y x = ∑ i, y i * (δ * σ (x i)) := by
      intro x
      simp [form, skewSpc, Matrix.smul_mulVec, dotProduct, smul_eq_mul]
    have hmem : ∀ z : Fin d → E, z ∈ (skewSpc F δ 𝔞 d).L ↔ ∀ i, z i ∈ 𝔞 := by
      intro z
      show z ∈ Submodule.pi Set.univ (fun _ : Fin d => 𝔞) ↔ _
      simp [Submodule.mem_pi]
    rw [hmem]
    constructor
    · intro hy x hx o
      rw [hmem] at hx
      rw [hform, Finset.mul_sum, map_sum]
      exact IsIntegral.sum _ (fun i _ => (hl.dual (y i)).1 (hy i) (x i) (hx i) o)
    · intro h i
      rw [hl.dual]
      intro x hx o
      have hs : Pi.single i x ∈ (skewSpc F δ 𝔞 d).L := by
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simpa using hx
        · simp [hj]
      have := h _ hs o
      rw [hform, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at this
      simpa using this
  case cartan =>
    intro w
    obtain ⟨c, hc, he⟩ := hpos w
    have hM : Complex.I • (skewSpc F δ 𝔞 d).J.map ⇑(B.emb w : E →+* ℂ) = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [skewSpc, he]
      · simp [skewSpc, h]
    have hθ : (skewSpc F δ 𝔞 d).θ w = 1 := rfl
    rw [hM, hθ]
    refine ⟨by simp, by simp, fun x hx => ?_⟩
    have key : (1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ x ⬝ᵥ ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ star x = ((c * ∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
      simp [Matrix.smul_mulVec, dotProduct, Finset.mul_sum, Complex.mul_conj]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Complex.mul_conj]
      ring
    rw [key, Complex.ofReal_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    exact mul_pos hc (Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩)
  case sig =>
    intro w
    obtain ⟨c, hc, he⟩ := hpos w
    have hM : Complex.I • (skewSpc F δ 𝔞 d).J.map ⇑(B.emb w : E →+* ℂ) = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [skewSpc, he]
      · simp [skewSpc, h]
    rw [hM]
    refine ⟨by simp, Matrix.of fun (k : Fin d) (p : Fin d ⊕ Fin 0) => Sum.elim (fun i => if k = i then (((Real.sqrt c)⁻¹ : ℝ) : ℂ) else 0) (fun z => z.elim0) p, ?_⟩
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    ext (i | i) (j | j)
    · simp [Matrix.mul_apply, Matrix.one_apply]
      split_ifs with h
      · rw [map_inv₀, Complex.conj_ofReal, ← mul_inv]
        have hs : ((√c : ℝ) : ℂ) * (√c : ℂ) = c := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
        rw [hs, mul_inv_cancel₀ (by exact_mod_cast hc.ne')]
      · simp
    all_goals (first | exact i.elim0 | exact j.elim0)

end UpperTheory.Gal.TP.Skew

end
