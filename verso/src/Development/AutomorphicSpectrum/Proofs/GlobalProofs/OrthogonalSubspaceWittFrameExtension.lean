import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameConjugateGramInv
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis

/- English proof (translation)
Use `set P : Matrix (Fin m ⊕ Fin m) (Fin n) E := Matrix.fromRows A B with hP`. Establish `hPQ : P * Matrix.fromCols X Y = 1`. Rewrite using `[hP, Matrix.fromRows_mul_fromCols, hAX, hAY, hBX, hBY, Matrix.fromBlocks_one]`. Establish `hsurj : Function.Surjective P.mulVecLin` using `fun u => ⟨Matrix.fromCols X Y *ᵥ u, by`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]⟩`.

Establish `hrk` using `LinearMap.finrank_range_add_finrank_ker P.mulVecLin`. Rewrite `hrk` using `[LinearMap.range_eq_top.2 hsurj, finrank_top]`. Simplify using `only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hrk`. Establish `hmem : ∀ k, k ∈ LinearMap.ker P.mulVecLin ↔ A *ᵥ k = 0 ∧ B *ᵥ k = 0`. Introduce `k`.

Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, hP, Matrix.fromRows_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> simp [h1, h2]`. Use `set K := LinearMap.ker P.mulVecLin with hK`. Set `b` to `Module.finBasis E K`. Establish `hle : 2 * m ≤ n` using `by omega`.

Use `⟨hle, ?_⟩` and prove the remaining obligations. Set `col : Fin n → Fin n → E` to `fun i => if h1 : i.val < m then fun k => X k ⟨i.val, h1⟩ else if h2 : i.val + m < n then (b ⟨i.val - m, by have := i.2; omega⟩ : K).1 else fun k => Y k ⟨n - 1 - i.val, by have := i.2; omega⟩`. Set `C0 : Matrix (Fin n) (Fin n) E` to `Matrix.of fun k i => col i k`. Establish `hcol : ∀ i, col i ∈ LinearMap.range C0.mulVecLin` using `fun i => ⟨Pi.single i 1, by`. Use function extensionality and compare the values at `k`.

Simplify using `[Matrix.mulVecLin_apply, C0]⟩`. Establish `hX : ∀ (j : Fin m), (fun k => X k j) ∈ LinearMap.range C0.mulVecLin`. Introduce `j`. Establish `hi : j.val < n` using `by have := j.2; omega`. Use `hcol ⟨j.val, hi⟩` as an intermediate fact.

Simplify `this` using `[col]`. Establish `hY : ∀ (j : Fin m), (fun k => Y k j) ∈ LinearMap.range C0.mulVecLin`. Introduce `j`. Establish `hj` using `j.2`. Establish `hi : n - 1 - j.val < n` using `by omega`.

Use `hcol ⟨n - 1 - j.val, hi⟩` as an intermediate fact. Establish `e1 : ¬ (n - 1 - j.val < m)` using `by omega`. Establish `e2 : ¬ (n - 1 - j.val + m < n)` using `by omega`. Establish `e3 : n - 1 - (n - 1 - j.val) = j.val` using `by omega`. Simplify `this` using `[col, e1, e2, e3]`.

Establish `hb : ∀ (t : Fin (Module.finrank E K)), (b t : K).1 ∈ LinearMap.range C0.mulVecLin`. Introduce `t`. Establish `ht` using `t.2`. Establish `hi : t.val + m < n` using `by omega`. Use `hcol ⟨t.val + m, hi⟩` as an intermediate fact.

Establish `e1 : ¬ (t.val + m < m)` using `by omega`. Establish `e2 : t.val + m + m < n` using `by omega`. Simplify `this` using `[col, e1, e2]`. Establish `hKr : ∀ k : K, k.1 ∈ LinearMap.range C0.mulVecLin`. Introduce `k`.

Rewrite using `[← b.sum_repr k]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul]`. Conclude with `Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hb t)`. Establish `hmv : ∀ (Z : Matrix (Fin n) (Fin m) E), (∀ j : Fin m, (fun k => Z k j) ∈ LinearMap.range C0.mulVecLin) → ∀ u, Z *ᵥ u ∈ LinearMap.range C0.mulVecLin`. Introduce `Z hZ u`.

Establish `: Z *ᵥ u = ∑ j, u j • (fun k => Z k j)`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t)`.

Establish `hs : Function.Surjective C0.mulVec`. Introduce `v`. Establish `hk : v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v) ∈ K`. Establish `eAX : ∀ w, A *ᵥ (X *ᵥ w) = w` using `fun w => by rw [Matrix.mulVec_mulVec, hAX, Matrix.one_mulVec]`. Establish `eAY : ∀ w, A *ᵥ (Y *ᵥ w) = 0` using `fun w => by rw [Matrix.mulVec_mulVec, hAY, Matrix.zero_mulVec]`.

Establish `eBX : ∀ w, B *ᵥ (X *ᵥ w) = 0` using `fun w => by rw [Matrix.mulVec_mulVec, hBX, Matrix.zero_mulVec]`. Establish `eBY : ∀ w, B *ᵥ (Y *ᵥ w) = w` using `fun w => by rw [Matrix.mulVec_mulVec, hBY, Matrix.one_mulVec]`. Rewrite using `[hK, hmem]`. Prove the components needed by the constructor for the conclusion. Simplify using `only [Matrix.mulVec_sub, eAX, eAY, sub_self, sub_zero]`.

Simplify using `only [Matrix.mulVec_sub, eBX, eBY, sub_self, sub_zero]`. Establish `h3` using `hKr ⟨_, hk⟩`. Establish `h1` using `hmv X hX (A *ᵥ v)`. Establish `h2` using `hmv Y hY (B *ᵥ v)`. Establish `: v = (v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v)) + X *ᵥ (A *ᵥ v) + Y *ᵥ (B *ᵥ v)` using `by abel`.

Establish `h4` using `Submodule.add_mem _ (Submodule.add_mem _ h3 h1) h2`. Simplify using `only at h4`. Rewrite `h4` using `[← this]`. Conclude with `h4`. Establish `hu : IsUnit C0` using `Matrix.mulVec_surjective_iff_isUnit.1 hs`.

Take `⟨C, hC⟩` from `hu`. Establish `hCk : ∀ k i, C.1 k i = col i k` using `fun k i => by rw [hC]; rfl`. Use `⟨C, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j h k`. Establish `h1 : i.val < m` using `h ▸ j.2`.

Rewrite using `[hCk]`. Simplify using `only [col, dif_pos h1]`. Use `congr 1`. Conclude with `Fin.ext h`. Introduce `i j h k`.

Establish `hj` using `j.2`. Establish `e1 : ¬ (i.val < m)` using `by omega`. Establish `e2 : ¬ (i.val + m < n)` using `by omega`. Rewrite using `[hCk]`. Simplify using `only [col, dif_neg e1, dif_neg e2]`.

Use `congr 1`. Conclude with `Fin.ext (by simp; omega)`. Introduce `i h1 h2`. Establish `e1 : ¬ (i.val < m)` using `by omega`. Establish `: (fun k => C.1 k i) = (b ⟨i.val - m, by have` using `i.2; omega⟩ : K).1 := by`.

Use function extensionality and compare the values at `k`. Rewrite using `[hCk]`. Simplify using `only [col, dif_neg e1, dif_pos h2]`. Rewrite using `[this]`. Conclude with `(hmem _).1 (b _).2`.
-/
theorem exists_basis_of_duality {E : Type} [Field E] {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) E)
    (A B : Matrix (Fin m) (Fin n) E) (hAX : A * X = 1) (hAY : A * Y = 0) (hBX : B * X = 0) (hBY : B * Y = 1) :
    2 * m ≤ n ∧ ∃ C : GL (Fin n) E,
      (∀ (i : Fin n) (j : Fin m), i.val = j.val → ∀ k, C.1 k i = X k j) ∧
      (∀ (i : Fin n) (j : Fin m), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j) ∧
      (∀ i : Fin n, m ≤ i.val → i.val + m < n →
        A *ᵥ (fun k => C.1 k i) = 0 ∧ B *ᵥ (fun k => C.1 k i) = 0) := by
  classical
  set P : Matrix (Fin m ⊕ Fin m) (Fin n) E := Matrix.fromRows A B with hP
  have hPQ : P * Matrix.fromCols X Y = 1 := by
    rw [hP, Matrix.fromRows_mul_fromCols, hAX, hAY, hBX, hBY, Matrix.fromBlocks_one]
  have hsurj : Function.Surjective P.mulVecLin := fun u => ⟨Matrix.fromCols X Y *ᵥ u, by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hrk
  have hmem : ∀ k, k ∈ LinearMap.ker P.mulVecLin ↔ A *ᵥ k = 0 ∧ B *ᵥ k = 0 := by
    intro k
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hP, Matrix.fromRows_mulVec]
    constructor
    · intro h
      exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩
    · rintro ⟨h1, h2⟩
      funext i
      cases i <;> simp [h1, h2]
  set K := LinearMap.ker P.mulVecLin with hK
  let b := Module.finBasis E K
  have hle : 2 * m ≤ n := by omega
  refine ⟨hle, ?_⟩
  let col : Fin n → Fin n → E := fun i =>
    if h1 : i.val < m then fun k => X k ⟨i.val, h1⟩
    else if h2 : i.val + m < n then (b ⟨i.val - m, by have := i.2; omega⟩ : K).1
    else fun k => Y k ⟨n - 1 - i.val, by have := i.2; omega⟩
  let C0 : Matrix (Fin n) (Fin n) E := Matrix.of fun k i => col i k
  have hcol : ∀ i, col i ∈ LinearMap.range C0.mulVecLin := fun i =>
    ⟨Pi.single i 1, by
      funext k
      simp [Matrix.mulVecLin_apply, C0]⟩
  have hX : ∀ (j : Fin m), (fun k => X k j) ∈ LinearMap.range C0.mulVecLin := by
    intro j
    have hi : j.val < n := by have := j.2; omega
    have := hcol ⟨j.val, hi⟩
    simpa [col] using this
  have hY : ∀ (j : Fin m), (fun k => Y k j) ∈ LinearMap.range C0.mulVecLin := by
    intro j
    have hj := j.2
    have hi : n - 1 - j.val < n := by omega
    have := hcol ⟨n - 1 - j.val, hi⟩
    have e1 : ¬ (n - 1 - j.val < m) := by omega
    have e2 : ¬ (n - 1 - j.val + m < n) := by omega
    have e3 : n - 1 - (n - 1 - j.val) = j.val := by omega
    simpa [col, e1, e2, e3] using this
  have hb : ∀ (t : Fin (Module.finrank E K)), (b t : K).1 ∈ LinearMap.range C0.mulVecLin := by
    intro t
    have ht := t.2
    have hi : t.val + m < n := by omega
    have := hcol ⟨t.val + m, hi⟩
    have e1 : ¬ (t.val + m < m) := by omega
    have e2 : t.val + m + m < n := by omega
    simpa [col, e1, e2] using this
  have hKr : ∀ k : K, k.1 ∈ LinearMap.range C0.mulVecLin := by
    intro k
    rw [← b.sum_repr k]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hb t)
  have hmv : ∀ (Z : Matrix (Fin n) (Fin m) E), (∀ j : Fin m, (fun k => Z k j) ∈ LinearMap.range C0.mulVecLin) →
      ∀ u, Z *ᵥ u ∈ LinearMap.range C0.mulVecLin := by
    intro Z hZ u
    have : Z *ᵥ u = ∑ j, u j • (fun k => Z k j) := by
      funext k
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t)
  have hs : Function.Surjective C0.mulVec := by
    intro v
    have hk : v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v) ∈ K := by
      have eAX : ∀ w, A *ᵥ (X *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hAX, Matrix.one_mulVec]
      have eAY : ∀ w, A *ᵥ (Y *ᵥ w) = 0 := fun w => by rw [Matrix.mulVec_mulVec, hAY, Matrix.zero_mulVec]
      have eBX : ∀ w, B *ᵥ (X *ᵥ w) = 0 := fun w => by rw [Matrix.mulVec_mulVec, hBX, Matrix.zero_mulVec]
      have eBY : ∀ w, B *ᵥ (Y *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hBY, Matrix.one_mulVec]
      rw [hK, hmem]
      constructor
      · simp only [Matrix.mulVec_sub, eAX, eAY, sub_self, sub_zero]
      · simp only [Matrix.mulVec_sub, eBX, eBY, sub_self, sub_zero]
    have h3 := hKr ⟨_, hk⟩
    have h1 := hmv X hX (A *ᵥ v)
    have h2 := hmv Y hY (B *ᵥ v)
    have : v = (v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v)) + X *ᵥ (A *ᵥ v) + Y *ᵥ (B *ᵥ v) := by abel
    have h4 := Submodule.add_mem _ (Submodule.add_mem _ h3 h1) h2
    simp only at h4
    rw [← this] at h4
    exact h4
  have hu : IsUnit C0 := Matrix.mulVec_surjective_iff_isUnit.1 hs
  obtain ⟨C, hC⟩ := hu
  have hCk : ∀ k i, C.1 k i = col i k := fun k i => by rw [hC]; rfl
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i j h k
    have h1 : i.val < m := h ▸ j.2
    rw [hCk]
    simp only [col, dif_pos h1]
    congr 1
    exact Fin.ext h
  · intro i j h k
    have hj := j.2
    have e1 : ¬ (i.val < m) := by omega
    have e2 : ¬ (i.val + m < n) := by omega
    rw [hCk]
    simp only [col, dif_neg e1, dif_neg e2]
    congr 1
    exact Fin.ext (by simp; omega)
  · intro i h1 h2
    have e1 : ¬ (i.val < m) := by omega
    have : (fun k => C.1 k i) = (b ⟨i.val - m, by have := i.2; omega⟩ : K).1 := by
      funext k
      rw [hCk]
      simp only [col, dif_neg e1, dif_pos h2]
    rw [this]
    exact (hmem _).1 (b _).2

/- English proof (translation)
Introduce `D V m X Y hW`. Establish `hyx` using `GlobalTheory.WittFrame.yx_eq_one D V m X Y hW`. Establish `hxx` using `hW.xx`. Establish `hyy` using `hW.yy`. Establish `hxy` using `hW.xy`.

Take `⟨hle, C, h1, h2, h3⟩` from `exists_basis_of_duality X Y (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) hyx hyy hxx hxy`. Conclude with `⟨C, ⟨hle, h1, h2, fun i a b => (h3 i a b).2, fun i a b => (h3 i a b).1⟩⟩`.
-/
theorem exists_isAdapted : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∃ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C := by
  intro D V m X Y hW
  have hyx := GlobalTheory.WittFrame.yx_eq_one D V m X Y hW
  have hxx := hW.xx
  have hyy := hW.yy
  have hxy := hW.xy
  obtain ⟨hle, C, h1, h2, h3⟩ := exists_basis_of_duality X Y
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram)
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) hyx hyy hxx hxy
  exact ⟨C, ⟨hle, h1, h2, fun i a b => (h3 i a b).2, fun i a b => (h3 i a b).1⟩⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis
