import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [mulVec, dotProduct, ratM, Matrix.map_apply]`. Rewrite using `[TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem ratM_mulVec_tmul (γ : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    ratM F γ *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (γ *ᵥ x) i := by
  ext i
  simp only [mulVec, dotProduct, ratM, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
The claim follows from `ratM_mulVec_tmul γ 1 x`.
-/
theorem ratM_mulVec_fv (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratM F γ *ᵥ fv F x = fv F (γ *ᵥ x) :=
  ratM_mulVec_tmul γ 1 x

/- English proof (translation)
Establish `h : ∀ ε : Matrix (Fin n) (Fin n) E, ratM F ε = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.mapMatrix ε`. Introduce `ε`. Use extensionality with `i j`. Simplify using `[ratM]`. Rewrite using `[h, h, h, map_mul]`.
-/
theorem ratM_mul (γ δ : Matrix (Fin n) (Fin n) E) : ratM F (γ * δ) = ratM F γ * ratM F δ := by
  have h : ∀ ε : Matrix (Fin n) (Fin n) E,
      ratM F ε = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.mapMatrix ε := by
    intro ε; ext i j; simp [ratM]
  rw [h, h, h, map_mul]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [ratM, Matrix.one_apply, h, Algebra.TensorProduct.one_def]`.
-/
theorem ratM_one : ratM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [ratM, Matrix.one_apply, h, Algebra.TensorProduct.one_def]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[fv, TensorProduct.tmul_sub]`.
-/
theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  ext i; simp [fv, TensorProduct.tmul_sub]

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [fv, Pi.smul_apply]`. Conclude with `map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E 1) M (x i)`.
-/
theorem fv_nsmul (M : ℕ) (x : Fin n → E) : fv F (M • x) = M • fv F x := by
  ext i
  simp only [fv, Pi.smul_apply]
  exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E 1) M (x i)

/- English proof (translation)
Establish `h0 : (M : F) ≠ 0` using `by exact_mod_cast (by omega : M ≠ 0)`. Rewrite `h` using `[← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F]`. Simplify `congrArg (fun z => (M : F)⁻¹ • z) h` using `[h0]`.
-/
theorem nsmul_cancel {V : Type} [AddCommGroup V] [Module F V] {M : ℕ} (hM : 1 ≤ M) {u w : V}
    (h : M • u = M • w) : u = w := by
  have h0 : (M : F) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  simpa [h0] using congrArg (fun z => (M : F)⁻¹ • z) h

/- English proof (translation)
Use `set B : Matrix (Fin n) (Fin n) E := (β : Matrix (Fin n) (Fin n) E) with hB`. Use `set C : Matrix (Fin n) (Fin n) E := ((β⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hC`. Establish `hBC : B * C = 1` using `Units.mul_inv β`. Establish `hCB : C * B = 1` using `Units.inv_mul β`. Establish `hRBC : ∀ z, ratM F B *ᵥ (ratM F C *ᵥ z) = z`.

Introduce `z`. Rewrite using `[mulVec_mulVec, ← ratM_mul, hBC, ratM_one, one_mulVec]`. Establish `hRCB : ∀ z, ratM F C *ᵥ (ratM F B *ᵥ z) = z`. Introduce `z`. Rewrite using `[mulVec_mulVec, ← ratM_mul, hCB, ratM_one, one_mulVec]`.

Establish `gen : ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ, (fun i => a ⊗ₜ[F] x i) ∈ hat F (Λ : Set (Fin n → E))` using `fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hstab, hcong⟩`. Use `⟨fun z hz => ?_, fun z hz => ⟨ratM F C *ᵥ z, ?_, hRBC z⟩⟩` and prove the remaining obligations. Proceed by induction on `hz using AddSubgroup.closure_induction with`.

Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Take `⟨y, hy, hxy⟩` from `hcong x hx`. Use `⟨fun i => a ⊗ₜ[F] y i, gen a ha y hy, ?_⟩` and prove the remaining obligations. Rewrite using `[ratM_mulVec_tmul]`.

Use extensionality with `i`. Use `congrFun hxy i` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.smul_apply] at this ⊢`. Rewrite using `[← TensorProduct.tmul_sub, this]`. Conclude with `map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) M (y i)`.

Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add z w _ _ h1 h2`. Take `⟨y1, hy1, e1⟩` from `h1`. Take `⟨y2, hy2, e2⟩` from `h2`. Use `⟨y1 + y2, add_mem hy1 hy2, ?_⟩` and prove the remaining obligations.

Rewrite using `[mulVec_add, smul_add, ← e1, ← e2]`. Normalize the expressions using the abelian group laws. Consider the case `neg z _ h`. Take `⟨y, hy, e⟩` from `h`. Use `⟨-y, neg_mem hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[mulVec_neg, smul_neg, ← e]`. Normalize the expressions using the abelian group laws. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`.

Rewrite using `[ratM_mulVec_tmul]`. Use `gen a ha _ ((hstab _).2 ?_)` and prove the remaining obligations. Rewrite using `[mulVec_mulVec, hBC, one_mulVec]`. Conclude with `hx`. Consider the case `zero => simp`.

Consider the case `add z w _ _ h1 h2 => rw [mulVec_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg z _ h => rw [mulVec_neg]`. Conclude with `neg_mem h`. Introduce and unpack `⟨hcong, hsurj⟩`.

Establish `himg : ∀ x ∈ Λ, B *ᵥ x ∈ Λ`. Introduce `x hx`. Take `⟨y, hy, e⟩` from `hcong _ ((hrat x).2 hx)`. Rewrite using `[← hrat, ← ratM_mulVec_fv, sub_eq_iff_eq_add.mp e]`. Conclude with `add_mem (nsmul_mem hy M) ((hrat x).2 hx)`.

Use `⟨fun x => ⟨himg x, fun hx => ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `hsurj _ ((hrat _).2 hx)`. Rewrite `e` using `[← ratM_mulVec_fv]`. Establish `hyx : y = fv F x`. Use `congrArg (fun z => ratM F C *ᵥ z) e` as an intermediate fact.

Simplify `this` using `only [hRCB]`. Rewrite using `[← hrat, ← hyx]`. Conclude with `hy`. Take `⟨y, hy, e⟩` from `hcong _ ((hrat x).2 hx)`. Establish `hM0 : (M : E) ≠ 0` using `by exact_mod_cast (by omega : M ≠ 0)`.

Use `set w : Fin n → E := (M : E)⁻¹ • (B *ᵥ x - x) with hw`. Establish `hMw : M • w = B *ᵥ x - x`. Rewrite using `[hw, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hM0]`. Establish `hfw : fv F w = y`. Apply `nsmul_cancel (F := F) hM` to reduce the goal to its premises.

Rewrite using `[← fv_nsmul, hMw, fv_sub, ← ratM_mulVec_fv, e]`. Conclude with `⟨w, (hrat w).1 (hfw ▸ hy), hMw.symm⟩`.
-/
theorem stab_cong_iff_hat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E) (hM : 1 ≤ M)
    (hrat : ∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) :
    ((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧
        ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔
      ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧
        ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x) := by
  set B : Matrix (Fin n) (Fin n) E := (β : Matrix (Fin n) (Fin n) E) with hB
  set C : Matrix (Fin n) (Fin n) E := ((β⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hC
  have hBC : B * C = 1 := Units.mul_inv β
  have hCB : C * B = 1 := Units.inv_mul β
  have hRBC : ∀ z, ratM F B *ᵥ (ratM F C *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hBC, ratM_one, one_mulVec]
  have hRCB : ∀ z, ratM F C *ᵥ (ratM F B *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hCB, ratM_one, one_mulVec]
  have gen : ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ,
      (fun i => a ⊗ₜ[F] x i) ∈ hat F (Λ : Set (Fin n → E)) :=
    fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩
  constructor
  · rintro ⟨hstab, hcong⟩
    refine ⟨fun z hz => ?_, fun z hz => ⟨ratM F C *ᵥ z, ?_, hRBC z⟩⟩
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨y, hy, hxy⟩ := hcong x hx
        refine ⟨fun i => a ⊗ₜ[F] y i, gen a ha y hy, ?_⟩
        rw [ratM_mulVec_tmul]
        ext i
        have := congrFun hxy i
        simp only [Pi.sub_apply, Pi.smul_apply] at this ⊢
        rw [← TensorProduct.tmul_sub, this]
        exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) M (y i)
      | zero => exact ⟨0, zero_mem _, by simp⟩
      | add z w _ _ h1 h2 =>
        obtain ⟨y1, hy1, e1⟩ := h1
        obtain ⟨y2, hy2, e2⟩ := h2
        refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
        rw [mulVec_add, smul_add, ← e1, ← e2]; abel
      | neg z _ h =>
        obtain ⟨y, hy, e⟩ := h
        refine ⟨-y, neg_mem hy, ?_⟩
        rw [mulVec_neg, smul_neg, ← e]; abel
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        rw [ratM_mulVec_tmul]
        refine gen a ha _ ((hstab _).2 ?_)
        rw [mulVec_mulVec, hBC, one_mulVec]; exact hx
      | zero => simp
      | add z w _ _ h1 h2 => rw [mulVec_add]; exact add_mem h1 h2
      | neg z _ h => rw [mulVec_neg]; exact neg_mem h
  · rintro ⟨hcong, hsurj⟩
    have himg : ∀ x ∈ Λ, B *ᵥ x ∈ Λ := by
      intro x hx
      obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      rw [← hrat, ← ratM_mulVec_fv, sub_eq_iff_eq_add.mp e]
      exact add_mem (nsmul_mem hy M) ((hrat x).2 hx)
    refine ⟨fun x => ⟨himg x, fun hx => ?_⟩, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := hsurj _ ((hrat _).2 hx)
      rw [← ratM_mulVec_fv] at e
      have hyx : y = fv F x := by
        have := congrArg (fun z => ratM F C *ᵥ z) e
        simpa only [hRCB] using this
      rw [← hrat, ← hyx]; exact hy
    · obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      set w : Fin n → E := (M : E)⁻¹ • (B *ᵥ x - x) with hw
      have hMw : M • w = B *ᵥ x - x := by
        rw [hw, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hM0]
      have hfw : fv F w = y := by
        apply nsmul_cancel (F := F) hM
        rw [← fv_nsmul, hMw, fv_sub, ← ratM_mulVec_fv, e]
      exact ⟨w, (hrat w).1 (hfw ▸ hy), hMw.symm⟩

end GlobalTheory.LocGlob
