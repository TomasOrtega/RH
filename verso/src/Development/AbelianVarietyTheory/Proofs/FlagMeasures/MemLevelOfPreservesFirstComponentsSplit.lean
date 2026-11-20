import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponentsStatement
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ cm n J v sp hsig hdiag L hsd κ hκ hfirst`. Establish `hint : ∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F` using `split_integral_local F E v sp hdiag`. Establish `pair1 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).1 = ∑ i, ∑ j, (sp (z i)).2 * (sp (inclE (F` using `F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by`. Introduce `z y`. Unfold `hR hform`.

Rewrite using `[map_sum, Prod.fst_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Prod.fst_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hsig]`.

Both sides reduce to the same expression. Establish `pair2 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).2 = ∑ i, ∑ j, (sp (z i)).1 * (sp (inclE (F` using `F) (v.adicCompletion F) (J i j))).2 * (sp (y j)).2 := by`. Introduce `z y`. Unfold `hR hform`. Rewrite using `[map_sum, Prod.snd_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Prod.snd_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hsig]`. Both sides reduce to the same expression.

Establish `hprod : ∀ y : Fin n → E ⊗[F] v.adicCompletion F, y ∈ loc v L ↔ (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2`. Introduce `y`. Use `⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩`. Establish `ha : sp.symm (1, 0) ∈ intV E v`.

Rewrite using `[hint, sp.apply_symm_apply]`. Conclude with `⟨one_mem _, zero_mem _⟩`. Establish `hb : sp.symm (0, 1) ∈ intV E v`. Rewrite using `[hint, sp.apply_symm_apply]`. Conclude with `⟨zero_mem _, one_mem _⟩`.

Establish `hm` using `(loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)`. Establish `hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂`. Use function extensionality and compare the values at `b`. Apply `sp.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)`.

Rewrite using `[map_add, map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]`. Use `ext`. Simplify using `[e₁ b]`. Simplify using `[e₂ b]`. Rewrite using `[hy]`.

Conclude with `hm`. Use `set Kv := v.adicCompletion F with hKv`. Use `set φ1 : E ⊗[F] Kv →+* Kv := (RingHom.fst _ _).comp sp.toRingHom with hφ1`. Use `set φ2 : E ⊗[F] Kv →+* Kv := (RingHom.snd _ _).comp sp.toRingHom with hφ2`. Establish `e1 : ∀ a, φ1 a = (sp a).1` using `fun _ => rfl`.

Establish `e2 : ∀ a, φ2 a = (sp a).2` using `fun _ => rfl`. Use `set K1 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ1 with hK1`. Use `set K2 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ2 with hK2`. Use `set J2 : Matrix (Fin n) (Fin n) Kv := (J.map (inclE (F := F) Kv)).map φ2 with hJ2`. Establish `hU : cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) * J.map (inclE (F` using `F) Kv) * (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) = J.map (inclE (F := F) Kv) := hκ`.

Establish `hc : (cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv))).map φ2 = K1ᵀ`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `show (sp (sigR cm.sig Kv ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i))).2 = (sp ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i)).1`. Rewrite using `[hsig]`. Both sides reduce to the same expression.

Establish `hU2 : K1ᵀ * J2 * K2 = J2`. Use `congrArg (fun M => M.map φ2) hU` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`. Rewrite `this` using `[hc]`. Conclude with `this`.

Establish `hQ : ∀ u w : Fin n → Kv, (K1 *ᵥ u) ⬝ᵥ (J2 *ᵥ (K2 *ᵥ w)) = u ⬝ᵥ (J2 *ᵥ w)`. Introduce `u w`. Use `conv_rhs => rw [← hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`. Establish `hsum : ∀ u w : Fin n → Kv, (∑ i, ∑ j, u i * J2 i j * w j) = u ⬝ᵥ (J2 *ᵥ w)`. Introduce `u w`.

Simplify using `only [dotProduct, mulVec, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hL2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔ ∀ u : Fin n → Kv, (∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = u b) → u ⬝ᵥ (J2 *ᵥ w) ∈ v.adicCompletionIntegers F`. Introduce `w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, ey⟩ u ⟨z, hz, ez⟩`. Establish `h` using `((hint _).1 (((hsd y).1 hy) z hz)).2`. Rewrite `h` using `[pair2]`. Simplify using `only [ez, ey] at h`. Rewrite using `[← hsum]`.

Conclude with `h`. Introduce `h`. Use `⟨fun b => sp.symm (0, w b), ?_, fun b => by simp⟩` and prove the remaining obligations. Use `(hsd _).2 fun z hz => (hint _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pair1]`.

Simplify using the standard rewrite rules. Rewrite using `[pair2]`. Use `h (fun b => (sp (z b)).1) ⟨z, hz, fun _ => rfl⟩` as an intermediate fact. Rewrite `this` using `[← hsum]`. Establish `e : ∀ j, (sp (sp.symm (0, w j))).2 = w j` using `fun j => by simp`.

Simplify using `only [e]`. Conclude with `this`. Establish `hH : ∀ x : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = (K1 *ᵥ x) b` using `hfirst`. Establish `hK1inv : ∀ u : Fin n → Kv, ∃ u', K1 *ᵥ u' = u`. Introduce `u`.

Use `⟨(((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) *ᵥ u, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec]`. Establish `: K1 * (((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) = 1`. Use `(bc φ1 κ).mul_inv` as an intermediate fact. Conclude with `this`.

Rewrite using `[this, Matrix.one_mulVec]`. Establish `hK2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = (K2 *ᵥ w) b`. Introduce `w`. Rewrite using `[hL2, hL2]`. Prove the components needed by the constructor for the conclusion.

Introduce `h u hu`. Take `⟨u', rfl⟩` from `hK1inv u`. Rewrite using `[hQ]`. Conclude with `h u' ((hH u').2 hu)`. Introduce `h u hu`.

Rewrite using `[← hQ]`. Conclude with `h _ ((hH u).1 hu)`. Establish `hc1 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).1 = (K1 *ᵥ fun j => (sp (x j)).1) b`. Introduce `x b`. Simplify using `only [mulVec, dotProduct, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]`.

Both sides reduce to the same expression. Establish `hc2 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).2 = (K2 *ᵥ fun j => (sp (x j)).2) b`. Introduce `x b`. Simplify using `only [mulVec, dotProduct, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]`. Both sides reduce to the same expression.

Use `show κ ∈ UJ _ _ ⊓ stabGL _`. Rewrite using `[Subgroup.mem_inf]`. Use `⟨hκ, fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x ∈ loc v L ↔ _ ∈ loc v L`. Rewrite using `[hprod x, hprod (_ *ᵥ x)]`.

Simplify using `only [hc1, hc2]`. Rewrite using `[hH (fun j => (sp (x j)).1), hK2 (fun j => (sp (x j)).2)]`.
-/
theorem mem_levelVL_of_first_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (L : Submodule (𝓞 E) (Fin n → E)), SelfDualAt cm.sig J v L → ∀ κ ∈ UPts cm.sig J (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔ ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = ((bc ((RingHom.fst _ _).comp sp.toRingHom) κ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b) → κ ∈ levelVL cm.sig J v L := by
  intro F E _ _ _ _ _ _ cm n J v sp hsig hdiag L hsd κ hκ hfirst
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag

  have pair1 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).1 =
      ∑ i, ∑ j, (sp (z i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
    intro z y
    unfold hR hform
    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have pair2 : ∀ z y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) z y)).2 =
      ∑ i, ∑ j, (sp (z i)).1 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).2 * (sp (y j)).2 := by
    intro z y
    unfold hR hform
    rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl

  have hprod : ∀ y : Fin n → E ⊗[F] v.adicCompletion F, y ∈ loc v L ↔
      (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2 := by
    intro y
    refine ⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩
    rintro ⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩
    have ha : sp.symm (1, 0) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
    have hb : sp.symm (0, 1) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩
    have hm := (loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)
    have hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂ := by
      funext b
      apply sp.injective
      change sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)
      rw [map_add, map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      ext
      · simp [e₁ b]
      · simp [e₂ b]
    rw [hy]; exact hm

  set Kv := v.adicCompletion F with hKv
  set φ1 : E ⊗[F] Kv →+* Kv := (RingHom.fst _ _).comp sp.toRingHom with hφ1
  set φ2 : E ⊗[F] Kv →+* Kv := (RingHom.snd _ _).comp sp.toRingHom with hφ2
  have e1 : ∀ a, φ1 a = (sp a).1 := fun _ => rfl
  have e2 : ∀ a, φ2 a = (sp a).2 := fun _ => rfl
  set K1 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ1 with hK1
  set K2 : Matrix (Fin n) (Fin n) Kv := (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)).map φ2 with hK2
  set J2 : Matrix (Fin n) (Fin n) Kv := (J.map (inclE (F := F) Kv)).map φ2 with hJ2

  have hU : cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) * J.map (inclE (F := F) Kv) *
      (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) = J.map (inclE (F := F) Kv) := hκ
  have hc : (cT (sigR cm.sig Kv) (κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv))).map φ2 = K1ᵀ := by
    refine Matrix.ext fun i j => ?_
    show (sp (sigR cm.sig Kv ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i))).2 = (sp ((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) j i)).1
    rw [hsig]; rfl
  have hU2 : K1ᵀ * J2 * K2 = J2 := by
    have := congrArg (fun M => M.map φ2) hU
    simp only [Matrix.map_mul] at this
    rw [hc] at this
    exact this
  have hQ : ∀ u w : Fin n → Kv, (K1 *ᵥ u) ⬝ᵥ (J2 *ᵥ (K2 *ᵥ w)) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    conv_rhs => rw [← hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  have hsum : ∀ u w : Fin n → Kv, (∑ i, ∑ j, u i * J2 i j * w j) = u ⬝ᵥ (J2 *ᵥ w) := by
    intro u w
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

  have hL2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∀ u : Fin n → Kv, (∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = u b) → u ⬝ᵥ (J2 *ᵥ w) ∈ v.adicCompletionIntegers F := by
    intro w
    constructor
    · rintro ⟨y, hy, ey⟩ u ⟨z, hz, ez⟩
      have h := ((hint _).1 (((hsd y).1 hy) z hz)).2
      rw [pair2] at h
      simp only [ez, ey] at h
      rw [← hsum]; exact h
    · intro h
      refine ⟨fun b => sp.symm (0, w b), ?_, fun b => by simp⟩
      refine (hsd _).2 fun z hz => (hint _).2 ⟨?_, ?_⟩
      · rw [pair1]; simp
      · rw [pair2]
        have := h (fun b => (sp (z b)).1) ⟨z, hz, fun _ => rfl⟩
        rw [← hsum] at this
        have e : ∀ j, (sp (sp.symm (0, w j))).2 = w j := fun j => by simp
        simp only [e]
        exact this

  have hH : ∀ x : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = x b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).1 = (K1 *ᵥ x) b := hfirst
  have hK1inv : ∀ u : Fin n → Kv, ∃ u', K1 *ᵥ u' = u := by
    intro u
    refine ⟨(((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) *ᵥ u, ?_⟩
    rw [Matrix.mulVec_mulVec]
    have : K1 * (((bc φ1 κ)⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) = 1 := by
      have := (bc φ1 κ).mul_inv
      exact this
    rw [this, Matrix.one_mulVec]
  have hK2 : ∀ w : Fin n → Kv, (∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = w b) ↔
      ∃ y ∈ loc v L, ∀ b, (sp (y b)).2 = (K2 *ᵥ w) b := by
    intro w
    rw [hL2, hL2]
    constructor
    · intro h u hu
      obtain ⟨u', rfl⟩ := hK1inv u
      rw [hQ]
      exact h u' ((hH u').2 hu)
    · intro h u hu
      rw [← hQ]
      exact h _ ((hH u).1 hu)

  have hc1 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).1 =
      (K1 *ᵥ fun j => (sp (x j)).1) b := by
    intro x b
    simp only [mulVec, dotProduct, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]
    rfl
  have hc2 : ∀ (x : Fin n → E ⊗[F] Kv) b, (sp (((κ : Matrix (Fin n) (Fin n) (E ⊗[F] Kv)) *ᵥ x) b)).2 =
      (K2 *ᵥ fun j => (sp (x j)).2) b := by
    intro x b
    simp only [mulVec, dotProduct, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul]
    rfl
  show κ ∈ UJ _ _ ⊓ stabGL _
  rw [Subgroup.mem_inf]
  refine ⟨hκ, fun x => ?_⟩
  change x ∈ loc v L ↔ _ ∈ loc v L
  rw [hprod x, hprod (_ *ᵥ x)]
  simp only [hc1, hc2]
  rw [hH (fun j => (sp (x j)).1), hK2 (fun j => (sp (x j)).2)]

end GlobalTheory.St.G
