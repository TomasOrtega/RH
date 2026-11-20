import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreLat

variable {D : D7}

def SelfDualFor {ι : Type} [Fintype ι] (G : Matrix ι ι D.host.E) (Λ : Submodule (𝓞 D.host.E) (ι → D.host.E)) : Prop :=
  Submodule.IsLattice D.host.E Λ ∧ ∀ y : ι → D.host.E, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star x ⬝ᵥ (G *ᵥ y)

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]`.
-/
theorem form_eq {ι : Type} [Fintype ι] (G : Matrix ι ι D.host.E) (x y : ι → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

/- English proof (translation)
Unfold `IsSelfDualC SelfDualFor`. Simplify using `only [form_eq]`.
-/
theorem isSelfDualC_iff (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    IsSelfDualC S Λ ↔ SelfDualFor S.gram Λ := by
  unfold IsSelfDualC SelfDualFor
  simp only [form_eq]

/- English proof (translation)
Break down `hs with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho⟩; exact ⟨-o, by push_cast; linear_combination -ho⟩`. Introduce and unpack `⟨o, ho⟩; exact ⟨-o, by push_cast; linear_combination -ho⟩`.
-/
theorem integral_sign {s b : D.host.E} (hs : s = 1 ∨ s = -1) :
    (∃ o : 𝓞 D.host.E, (o : D.host.E) = s * b) ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = b := by
  rcases hs with rfl | rfl
  · simp
  · constructor
    · rintro ⟨o, ho⟩; exact ⟨-o, by push_cast; linear_combination -ho⟩
    · rintro ⟨o, ho⟩; exact ⟨-o, by push_cast; linear_combination -ho⟩

/- English proof (translation)
Use `set P : Matrix κ ι D.host.E := G⁻¹ * (s • (Qᴴ * G')) with hPdef`. Establish `hPQ : P * Q = 1`. Rewrite using `[hPdef, Matrix.mul_assoc, Matrix.smul_mul, ← hG]`. Conclude with `Matrix.nonsing_inv_mul G hdet`. Establish `hQP : Q * P = 1` using `(Matrix.mul_eq_one_comm_of_card_eq κ ι D.host.E hcard).1 hPQ`.

Establish `mem : ∀ y, y ∈ Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 D.host.E)) ↔ P *ᵥ y ∈ Λ`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]`.

Conclude with `hx`. Introduce `hy`. Use `⟨P *ᵥ y, hy, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]`. Establish `form : ∀ x y, star x ⬝ᵥ (G *ᵥ (P *ᵥ y)) = s * (star (Q *ᵥ x) ⬝ᵥ (G' *ᵥ y))`.

Introduce `x y`. Establish `h1 : G *ᵥ (P *ᵥ y) = s • (Qᴴ *ᵥ (G' *ᵥ y))`. Rewrite using `[hG, Matrix.mulVec_mulVec, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQP, Matrix.mul_one, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]`. Rewrite using `[h1, dotProduct_smul, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, smul_eq_mul]`. Use `⟨⟨hΛ.1.fg.map _, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `hsurj : Function.Surjective (Matrix.mulVecLin Q)` using `fun y => ⟨P *ᵥ y, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]⟩`. Establish `: (Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 D.host.E)) : Set (ι → D.host.E)) = (Matrix.mulVecLin Q) '' Λ`. Simplify using `[Submodule.map_coe]`. Rewrite using `[this, Submodule.span_image, hΛ.1.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]`. Introduce `y`.

Rewrite using `[mem, hΛ.2]`. Prove the components needed by the constructor for the conclusion. Introduce `h x' hx'`. Break down `hx' with ⟨x, hx, rfl⟩` into its components or cases. Use `h x hx` as an intermediate fact.

Rewrite `this` using `[form, integral_sign hs]`. Simplify `this` using `only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]`. Introduce `h x hx`. Rewrite using `[form, integral_sign hs]`. Use `h (Q *ᵥ x) ⟨x, hx, rfl⟩` as an intermediate fact.

Conclude with `this`.
-/
theorem selfDualFor_map {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {G' : Matrix ι ι D.host.E} {G : Matrix κ κ D.host.E} (Q : Matrix ι κ D.host.E) {s : D.host.E} (hs : s = 1 ∨ s = -1)
    (hG : G = s • (Qᴴ * G' * Q)) (hdet : IsUnit G.det) (hcard : Fintype.card κ = Fintype.card ι)
    {Λ : Submodule (𝓞 D.host.E) (κ → D.host.E)} (hΛ : SelfDualFor G Λ) :
    SelfDualFor G' (Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 D.host.E))) := by
  set P : Matrix κ ι D.host.E := G⁻¹ * (s • (Qᴴ * G')) with hPdef
  have hPQ : P * Q = 1 := by
    rw [hPdef, Matrix.mul_assoc, Matrix.smul_mul, ← hG]
    exact Matrix.nonsing_inv_mul G hdet
  have hQP : Q * P = 1 := (Matrix.mul_eq_one_comm_of_card_eq κ ι D.host.E hcard).1 hPQ
  have mem : ∀ y, y ∈ Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 D.host.E)) ↔ P *ᵥ y ∈ Λ := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
      exact hx
    · intro hy
      refine ⟨P *ᵥ y, hy, ?_⟩
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have form : ∀ x y, star x ⬝ᵥ (G *ᵥ (P *ᵥ y)) = s * (star (Q *ᵥ x) ⬝ᵥ (G' *ᵥ y)) := by
    intro x y
    have h1 : G *ᵥ (P *ᵥ y) = s • (Qᴴ *ᵥ (G' *ᵥ y)) := by
      rw [hG, Matrix.mulVec_mulVec, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQP,
        Matrix.mul_one, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    rw [h1, dotProduct_smul, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, smul_eq_mul]
  refine ⟨⟨hΛ.1.fg.map _, ?_⟩, ?_⟩
  · have hsurj : Function.Surjective (Matrix.mulVecLin Q) := fun y =>
      ⟨P *ᵥ y, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]⟩
    have : (Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 D.host.E)) : Set (ι → D.host.E)) = (Matrix.mulVecLin Q) '' Λ := by
      simp [Submodule.map_coe]
    rw [this, Submodule.span_image, hΛ.1.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
  · intro y
    rw [mem, hΛ.2]
    constructor
    · intro h x' hx'
      rcases hx' with ⟨x, hx, rfl⟩
      have := h x hx
      rw [form, integral_sign hs] at this
      simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] using this
    · intro h x hx
      rw [form, integral_sign hs]
      have := h (Q *ᵥ x) ⟨x, hx, rfl⟩
      exact this

end GlobalTheory.CoreLat

namespace GlobalTheory.CoreLat

variable {D : D7}

def extL (ι κ : Type) : (ι → D.host.E) →ₗ[D.host.E] (ι ⊕ κ → D.host.E) where
  toFun v := Sum.elim v (fun _ => 0)
  map_add' v w := by ext (i | i) <;> simp
  map_smul' c v := by ext (i | i) <;> simp

def extR (ι κ : Type) : (κ → D.host.E) →ₗ[D.host.E] (ι ⊕ κ → D.host.E) where
  toFun v := Sum.elim (fun _ => 0) v
  map_add' v w := by ext (i | i) <;> simp
  map_smul' c v := by ext (i | i) <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem extL_apply {ι κ : Type} (v : ι → D.host.E) : extL (D := D) ι κ v = Sum.elim v (fun _ => 0) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem extR_apply {ι κ : Type} (v : κ → D.host.E) : extR (D := D) ι κ v = Sum.elim (fun _ => 0) v := rfl

def sumLat {ι κ : Type} (ΛA : Submodule (𝓞 D.host.E) (ι → D.host.E)) (ΛB : Submodule (𝓞 D.host.E) (κ → D.host.E)) :
    Submodule (𝓞 D.host.E) (ι ⊕ κ → D.host.E) :=
  ΛA.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E Sum.inl) ⊓ ΛB.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E Sum.inr)

/- English proof (translation)
Simplify using `[sumLat, LinearMap.funLeft]`.
-/
theorem mem_sumLat {ι κ : Type} {ΛA : Submodule (𝓞 D.host.E) (ι → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (κ → D.host.E)}
    (y : ι ⊕ κ → D.host.E) : y ∈ sumLat ΛA ΛB ↔ y ∘ Sum.inl ∈ ΛA ∧ y ∘ Sum.inr ∈ ΛB := by
  simp [sumLat, LinearMap.funLeft]

/- English proof (translation)
Apply the tactic sequence `ext (i | i) <;> simp`.
-/
theorem split_vec {ι κ : Type} (y : ι ⊕ κ → D.host.E) :
    y = extL (D := D) ι κ (y ∘ Sum.inl) + extR (D := D) ι κ (y ∘ Sum.inr) := by
  ext (i | i) <;> simp

/- English proof (translation)
Rewrite using `[Matrix.fromBlocks_mulVec]`. Simplify using `only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, zero_add, add_zero, Pi.star_apply, Function.comp_apply]`.
-/
theorem form_sum {ι κ : Type} [Fintype ι] [Fintype κ] (GA : Matrix ι ι D.host.E) (GB : Matrix κ κ D.host.E)
    (x y : ι ⊕ κ → D.host.E) :
    star x ⬝ᵥ (fromBlocks GA 0 0 GB *ᵥ y) =
      star (x ∘ Sum.inl) ⬝ᵥ (GA *ᵥ (y ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (GB *ᵥ (y ∘ Sum.inr)) := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, zero_add, add_zero,
    Pi.star_apply, Function.comp_apply]

/- English proof (translation)
Establish `heq : sumLat ΛA ΛB = ΛA.map ((extL (D` using `D) ι κ).restrictScalars (𝓞 D.host.E)) ⊔ ΛB.map ((extR (D := D) ι κ).restrictScalars (𝓞 D.host.E)) := by`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[mem_sumLat]`. Rewrite using `[split_vec (D := D) y]`.

Conclude with `Submodule.add_mem_sup ⟨_, hy.1, rfl⟩ ⟨_, hy.2, rfl⟩`. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[mem_sumLat]`. Use `⟨by simpa using hx, ?_⟩` and prove the remaining obligations.

Establish `: (extL (D` using `D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp`. Simplify using `only [LinearMap.coe_restrictScalars] at this ⊢`. Rewrite using `[this]`. Conclude with `ΛB.zero_mem`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Rewrite using `[mem_sumLat]`. Use `⟨?_, by simpa using hx⟩` and prove the remaining obligations. Establish `: (extR (D` using `D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp`. Simplify using `only [LinearMap.coe_restrictScalars] at this ⊢`. Rewrite using `[this]`.

Conclude with `ΛA.zero_mem`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[heq]`. Conclude with `(hA.1.fg.map _).sup (hB.1.fg.map _)`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Rewrite using `[split_vec (D := D) y]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `h1 : extL (D` using `D) ι κ (y ∘ Sum.inl) ∈ Submodule.span D.host.E (extL (D := D) ι κ '' (ΛA : Set _)) := by`. Rewrite using `[Submodule.span_image, hA.1.span_eq_top]`.

Conclude with `⟨_, Submodule.mem_top, rfl⟩`. Use `Submodule.span_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[SetLike.mem_coe, heq]`. Conclude with `Submodule.mem_sup_left ⟨x, hx, rfl⟩`.

Establish `h1 : extR (D` using `D) ι κ (y ∘ Sum.inr) ∈ Submodule.span D.host.E (extR (D := D) ι κ '' (ΛB : Set _)) := by`. Rewrite using `[Submodule.span_image, hB.1.span_eq_top]`. Conclude with `⟨_, Submodule.mem_top, rfl⟩`. Use `Submodule.span_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Rewrite using `[SetLike.mem_coe, heq]`. Conclude with `Submodule.mem_sup_right ⟨x, hx, rfl⟩`. Introduce `y`. Rewrite using `[mem_sumLat, hA.2, hB.2]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩ x hx`. Rewrite `hx` using `[mem_sumLat]`. Take `⟨b1, hb1⟩` from `h1 _ hx.1`. Take `⟨b2, hb2⟩` from `h2 _ hx.2`. Conclude with `⟨b1 + b2, by rw [form_sum, ← hb1, ← hb2]; norm_cast⟩`.

Introduce `h`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Establish `hm : extL (D` using `D) ι κ x ∈ sumLat ΛA ΛB := by`. Rewrite using `[mem_sumLat]`.

Use `⟨by simpa using hx, ?_⟩` and prove the remaining obligations. Establish `: (extL (D` using `D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp`. Rewrite using `[this]`. Conclude with `ΛB.zero_mem`. Take `⟨b, hb⟩` from `h _ hm`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hb, form_sum]`. Establish `e1 : (extL (D` using `D) ι κ x) ∘ Sum.inl = x := by ext i; simp`. Establish `e2 : (extL (D` using `D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp`. Rewrite using `[e1, e2]`.

Simplify using the standard rewrite rules. Introduce `x hx`. Establish `hm : extR (D` using `D) ι κ x ∈ sumLat ΛA ΛB := by`. Rewrite using `[mem_sumLat]`. Use `⟨?_, by simpa using hx⟩` and prove the remaining obligations.

Establish `: (extR (D` using `D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp`. Rewrite using `[this]`. Conclude with `ΛA.zero_mem`. Take `⟨b, hb⟩` from `h _ hm`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Rewrite using `[hb, form_sum]`. Establish `e1 : (extR (D` using `D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp`. Establish `e2 : (extR (D` using `D) ι κ x) ∘ Sum.inr = x := by ext i; simp`. Rewrite using `[e1, e2]`. Simplify using the standard rewrite rules.
-/
theorem selfDualFor_sum {ι κ : Type} [Fintype ι] [Fintype κ] {GA : Matrix ι ι D.host.E} {GB : Matrix κ κ D.host.E}
    {ΛA : Submodule (𝓞 D.host.E) (ι → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (κ → D.host.E)}
    (hA : SelfDualFor GA ΛA) (hB : SelfDualFor GB ΛB) : SelfDualFor (fromBlocks GA 0 0 GB) (sumLat ΛA ΛB) := by
  have heq : sumLat ΛA ΛB = ΛA.map ((extL (D := D) ι κ).restrictScalars (𝓞 D.host.E)) ⊔
      ΛB.map ((extR (D := D) ι κ).restrictScalars (𝓞 D.host.E)) := by
    apply le_antisymm
    · intro y hy
      rw [mem_sumLat] at hy
      rw [split_vec (D := D) y]
      exact Submodule.add_mem_sup ⟨_, hy.1, rfl⟩ ⟨_, hy.2, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        rw [mem_sumLat]
        refine ⟨by simpa using hx, ?_⟩
        have : (extL (D := D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp
        simp only [LinearMap.coe_restrictScalars] at this ⊢
        rw [this]; exact ΛB.zero_mem
      · rintro _ ⟨x, hx, rfl⟩
        rw [mem_sumLat]
        refine ⟨?_, by simpa using hx⟩
        have : (extR (D := D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp
        simp only [LinearMap.coe_restrictScalars] at this ⊢
        rw [this]; exact ΛA.zero_mem
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [heq]; exact (hA.1.fg.map _).sup (hB.1.fg.map _)
  · rw [eq_top_iff]
    intro y _
    rw [split_vec (D := D) y]
    refine Submodule.add_mem _ ?_ ?_
    · have h1 : extL (D := D) ι κ (y ∘ Sum.inl) ∈ Submodule.span D.host.E (extL (D := D) ι κ '' (ΛA : Set _)) := by
        rw [Submodule.span_image, hA.1.span_eq_top]; exact ⟨_, Submodule.mem_top, rfl⟩
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, heq]
      exact Submodule.mem_sup_left ⟨x, hx, rfl⟩
    · have h1 : extR (D := D) ι κ (y ∘ Sum.inr) ∈ Submodule.span D.host.E (extR (D := D) ι κ '' (ΛB : Set _)) := by
        rw [Submodule.span_image, hB.1.span_eq_top]; exact ⟨_, Submodule.mem_top, rfl⟩
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, heq]
      exact Submodule.mem_sup_right ⟨x, hx, rfl⟩
  · intro y
    rw [mem_sumLat, hA.2, hB.2]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rw [mem_sumLat] at hx
      obtain ⟨b1, hb1⟩ := h1 _ hx.1
      obtain ⟨b2, hb2⟩ := h2 _ hx.2
      exact ⟨b1 + b2, by rw [form_sum, ← hb1, ← hb2]; norm_cast⟩
    · intro h
      constructor
      · intro x hx
        have hm : extL (D := D) ι κ x ∈ sumLat ΛA ΛB := by
          rw [mem_sumLat]
          refine ⟨by simpa using hx, ?_⟩
          have : (extL (D := D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp
          rw [this]; exact ΛB.zero_mem
        obtain ⟨b, hb⟩ := h _ hm
        refine ⟨b, ?_⟩
        rw [hb, form_sum]
        have e1 : (extL (D := D) ι κ x) ∘ Sum.inl = x := by ext i; simp
        have e2 : (extL (D := D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp
        rw [e1, e2]; simp
      · intro x hx
        have hm : extR (D := D) ι κ x ∈ sumLat ΛA ΛB := by
          rw [mem_sumLat]
          refine ⟨?_, by simpa using hx⟩
          have : (extR (D := D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp
          rw [this]; exact ΛA.zero_mem
        obtain ⟨b, hb⟩ := h _ hm
        refine ⟨b, ?_⟩
        rw [hb, form_sum]
        have e1 : (extR (D := D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp
        have e2 : (extR (D := D) ι κ x) ∘ Sum.inr = x := by ext i; simp
        rw [e1, e2]; simp

/- English proof (translation)
Take `⟨k, hk'⟩` from `Fintype.card_eq_one_iff.1 hk`. Establish `hu : (Finset.univ : Finset κ) = {k}` using `by ext i; simp [hk' i]`. Establish `ev : ∀ A : Matrix κ κ D.host.E, star ζ ⬝ᵥ (A *ᵥ ζ) = star (ζ k) * (A k k * ζ k)`. Introduce `A`. Simplify using `[dotProduct, Matrix.mulVec, hu]`.

Rewrite `h` using `[ev, ev]`. Rewrite `hζ` using `[ev]`. Establish `h0 : star (ζ k) ≠ 0` using `fun h0 => hζ (by rw [h0, zero_mul])`. Establish `h1 : ζ k ≠ 0` using `fun h1 => hζ (by rw [h1, mul_zero, mul_zero])`. Establish `hkk : M k k = N k k`.

Use `mul_left_cancel₀ h0 h` as an intermediate fact. Conclude with `mul_right_cancel₀ h1 this`. Conclude with `Matrix.ext fun i j => by rw [hk' i, hk' j]; exact hkk`.
-/
theorem line_mat_eq {κ : Type} [Fintype κ] (hk : Fintype.card κ = 1) {M N : Matrix κ κ D.host.E} {ζ : κ → D.host.E}
    (hζ : star ζ ⬝ᵥ (M *ᵥ ζ) ≠ 0) (h : star ζ ⬝ᵥ (M *ᵥ ζ) = star ζ ⬝ᵥ (N *ᵥ ζ)) : M = N := by
  obtain ⟨k, hk'⟩ := Fintype.card_eq_one_iff.1 hk
  have hu : (Finset.univ : Finset κ) = {k} := by ext i; simp [hk' i]
  have ev : ∀ A : Matrix κ κ D.host.E, star ζ ⬝ᵥ (A *ᵥ ζ) = star (ζ k) * (A k k * ζ k) := by
    intro A; simp [dotProduct, Matrix.mulVec, hu]
  rw [ev, ev] at h
  rw [ev] at hζ
  have h0 : star (ζ k) ≠ 0 := fun h0 => hζ (by rw [h0, zero_mul])
  have h1 : ζ k ≠ 0 := fun h1 => hζ (by rw [h1, mul_zero, mul_zero])
  have hkk : M k k = N k k := by
    have := mul_left_cancel₀ h0 h
    exact mul_right_cancel₀ h1 this
  exact Matrix.ext fun i j => by rw [hk' i, hk' j]; exact hkk

end GlobalTheory.CoreLat

namespace GlobalTheory.CoreLat

/- English proof (translation)
Take `⟨q, hqn, hq⟩` from `Nat.exists_infinite_primes (n + 1)`. Establish `hqZ : Prime (q : ℤ)` using `Nat.prime_iff_prime_int.1 hq`. Establish `hq0 : (q : ℤ) ≠ 0` using `by exact_mod_cast hq.ne_zero`. Use `haveI hP : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hq0).2 hqZ`. Establish `hinj : Function.Injective (algebraMap ℤ (𝓞 K))`.

Introduce `a b hab`. Simplify using `using hab`. Take `⟨Q, -, hQ, hcomap⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(q : ℤ)}) ⊥ (by`. Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot]`.

Establish `: x = 0` using `hinj (by rw [hx, map_zero])`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _)`. Establish `hqQ : algebraMap ℤ (𝓞 K) (q : ℤ) ∈ Q`. Rewrite using `[← Ideal.mem_comap, hcomap]`.

Conclude with `Ideal.subset_span rfl`. Establish `hne : Q ≠ ⊥`. Introduce `h`. Rewrite `hqQ` using `[h, Ideal.mem_bot]`. Conclude with `hq0 (hinj (by rw [hqQ, map_zero]))`.

Use `⟨⟨Q, hQ, hne⟩, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Establish `: algebraMap ℤ (𝓞 K) (n : ℤ) ∈ Q` using `by simpa using hmem`. Rewrite `this` using `[← Ideal.mem_comap, hcomap, Ideal.mem_span_singleton]`. Establish `hdvd : q ∣ n` using `by exact_mod_cast this`.

Use `Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_prime_not_mem (K : Type) [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ((n : 𝓞 K)) ∉ p.asIdeal := by
  obtain ⟨q, hqn, hq⟩ := Nat.exists_infinite_primes (n + 1)
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  haveI hP : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hq0).2 hqZ
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := by
    intro a b hab
    simpa using hab
  obtain ⟨Q, -, hQ, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(q : ℤ)}) ⊥ (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]; exact Ideal.zero_mem _)
  have hqQ : algebraMap ℤ (𝓞 K) (q : ℤ) ∈ Q := by
    rw [← Ideal.mem_comap, hcomap]; exact Ideal.subset_span rfl
  have hne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hqQ
    exact hq0 (hinj (by rw [hqQ, map_zero]))
  refine ⟨⟨Q, hQ, hne⟩, ?_⟩
  intro hmem
  have : algebraMap ℤ (𝓞 K) (n : ℤ) ∈ Q := by simpa using hmem
  rw [← Ideal.mem_comap, hcomap, Ideal.mem_span_singleton] at this
  have hdvd : q ∣ n := by exact_mod_cast this
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  omega

end GlobalTheory.CoreLat

namespace GlobalTheory.CoreLat

variable {D : D7}

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec]`.
-/
theorem quad_mul {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι κ D.host.E) (G : Matrix ι ι D.host.E) (x : κ → D.host.E) :
    star x ⬝ᵥ ((Aᴴ * (G * A)) *ᵥ x) = star (A *ᵥ x) ⬝ᵥ (G *ᵥ (A *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec]

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_smul {κ : Type} [Fintype κ] (c : D.host.E) (G : Matrix κ κ D.host.E) (x : κ → D.host.E) :
    star (c • x) ⬝ᵥ (G *ᵥ (c • x)) = star c * c * (star x ⬝ᵥ (G *ᵥ x)) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`.
-/
theorem quad_smul_mat {κ : Type} [Fintype κ] (c : D.host.E) (G : Matrix κ κ D.host.E) (x : κ → D.host.E) :
    star x ⬝ᵥ ((c • G) *ᵥ x) = c * (star x ⬝ᵥ (G *ᵥ x)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end GlobalTheory.CoreLat

namespace GlobalTheory.CoreLat

/- English proof (translation)
Introduce `D Ld hT Gi Gl Kc Yd cX ex W u hPk a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hζ hvτ hNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY`. Establish `hξ : D.host.xi0 ≠ 0` using `GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D`. Establish `hsξ : star D.host.xi0 ≠ 0` using `star_ne_zero.2 hξ`. Establish `hline : ∀ σ j (h : j + 2 * σ + 2 = D.R.m), ∃ Λ : Submodule (𝓞 D.host.E) (Fin (y.bes j σ h).L.rank → D.host.E), SelfDualFor (y.bes j σ h).L.gram Λ`. Introduce `σ`.

Proceed by induction on `σ with`. Consider the case `zero`. Introduce `j h`. Take `⟨hg, hv⟩` from `hTau j h`. Establish `hl` using `(y.bes j 0 h).line`.

Establish `hlam0 : (-D.host.xi0 ^ (D.R.m / 2) : D.host.E) ≠ 0` using `neg_ne_zero.2 (pow_ne_zero _ hξ)`. Establish `hc : (-(D.host.xi0 * star D.host.xi0) : D.host.E) ≠ 0` using `neg_ne_zero.2 (mul_ne_zero hξ hsξ)`. Establish `hval` using `quad_mul (y.τ j h) (y.bes j 0 h).L.gram a.ζ₀`. Rewrite `hval` using `[hg, hv, quad_smul, quad_smul_mat, hζ]`. Establish `hT0 : (D.mem u).A.T ≠ 0`.

Introduce `h0`. Rewrite `hval` using `[h0, Nat.cast_zero, mul_zero]`. Conclude with `mul_ne_zero (mul_ne_zero (star_ne_zero.2 hlam0) hlam0) hl.2 hval.symm`. Establish `hr1 : a.Lz.rank ≤ 1`. Establish `hu : IsUnit ((-(D.host.xi0 * star D.host.xi0)) • a.Lz.gram)`.

Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]`. Conclude with `((isUnit_iff_ne_zero.2 hc).pow _).mul (gram_isUnit_det _)`. Establish `hrk` using `Matrix.rank_of_isUnit _ hu`. Rewrite `hrk` using `[← hg, Fintype.card_fin]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hr0 : a.Lz.rank ≠ 0`. Introduce `h0`. Use `haveI : IsEmpty (Fin a.Lz.rank) := ⟨fun i => by have := i.2; omega⟩`. Establish `: star a.ζ₀ ⬝ᵥ (a.Lz.gram *ᵥ a.ζ₀) = 0` using `by simp [dotProduct]`. Rewrite `this` using `[hζ]`.

Conclude with `hT0 (by exact_mod_cast this)`. Take `⟨x, hx⟩` from `exists_prime_not_mem D.host.F hT0`. Establish `hxt : x ∉ v.tP` using `by rw [htP]; exact hx`. Take `⟨LZ, hLZsd, -⟩` from `hLZ D.R.m rfl x hxt`. Use `⟨_, selfDualFor_map (D.host.xi0⁻¹ • y.τ j h) (s := -1) (Or.inr rfl) ?_ (gram_isUnit_det _) ?_ ((isSelfDualC_iff _ _).1 hLZsd)⟩` and prove the remaining obligations.

Simplify using `only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]`. Rewrite using `[hg, smul_smul]`. Use `(one_smul D.host.E a.Lz.gram).symm using 2` and compare the differences between its conclusion and the goal. Rewrite using `[star_inv₀]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Fintype.card_fin, Fintype.card_fin, hl.1]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ σ ih`. Introduce `j h`. Take `⟨Λ', hΛ'⟩` from `ih (j + 1 + 1) (idx_step h)`.

Establish `lk` using `y.lnk j σ h`. Establish `hl` using `(y.bes j (σ + 1) h).line`. Establish `hl'` using `(y.bes (j + 1 + 1) σ (idx_step h)).line`. Use `⟨_, selfDualFor_map (D.host.xi0⁻¹ • lk.τ) (s := 1) (Or.inl rfl) ?_ (gram_isUnit_det _) ?_ hΛ'⟩` and prove the remaining obligations. Use `line_mat_eq (by rw [Fintype.card_fin, hl'.1]) hl'.2 ?_` and prove the remaining obligations.

Rewrite using `[one_smul, Matrix.mul_assoc, quad_mul, Matrix.smul_mulVec, lk.map, smul_neg, ← neg_smul, quad_smul]`. Express the relevant statement in the definitionally equal form `_ = star (-D.host.xi0⁻¹) * -D.host.xi0⁻¹ * (star (y.bes j (σ + 1) h).ζ ⬝ᵥ ((y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ))`. Rewrite using `[show star (y.bes j (σ + 1) h).ζ ⬝ᵥ ((y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ) = _ from lk.norm, star_neg, star_inv₀]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Fintype.card_fin, Fintype.card_fin, hl.1, hl'.1]`.

Introduce `j ρ h`. Take `⟨ΛL, hΛL⟩` from `hline ρ j h`. Establish `hA : SelfDualFor (D.sp.X j).gram (a.x j).L` using `(isSelfDualC_iff _ _).1 (hIs.x j (by omega)).sd`. Establish `hs` using `selfDualFor_sum hA hΛL`. Establish `hmap` using `selfDualFor_map (G' := (y.bes j ρ h).V₀.gram) (Matrix.fromCols (y.bes j ρ h).o.iA (y.bes j ρ h).o.iB) (s := 1) (Or.inl rfl) ?_ ?_ ?_ hs`.

Conclude with `⟨_, (isSelfDualC_iff _ _).2 hmap⟩`. Rewrite using `[one_smul, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, (y.bes j ρ h).o.isoA, (y.bes j ρ h).o.isoB, (y.bes j ρ h).o.orth, (y.bes j ρ h).o.orth']`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁]`. Conclude with `(gram_isUnit_det _).mul (gram_isUnit_det _)`. Rewrite using `[Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, (y.bes j ρ h).o.rank_add]`.
-/
theorem exists_selfDual_core : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ j ρ h, ∃ L : GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀, IsSelfDualC (y.bes j ρ h).V₀ L := by
  intro D Ld hT Gi Gl Kc Yd cX ex W u hPk a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hζ hvτ hNT hoζ hLT hgP htP hdisj hPre hLZ
    hbas FY sc hFY
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hsξ : star D.host.xi0 ≠ 0 := star_ne_zero.2 hξ
  have hline : ∀ σ j (h : j + 2 * σ + 2 = D.R.m), ∃ Λ : Submodule (𝓞 D.host.E) (Fin (y.bes j σ h).L.rank → D.host.E),
      SelfDualFor (y.bes j σ h).L.gram Λ := by
    intro σ
    induction σ with
    | zero =>
      intro j h
      obtain ⟨hg, hv⟩ := hTau j h
      have hl := (y.bes j 0 h).line
      have hlam0 : (-D.host.xi0 ^ (D.R.m / 2) : D.host.E) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ hξ)
      have hc : (-(D.host.xi0 * star D.host.xi0) : D.host.E) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hξ hsξ)
      have hval := quad_mul (y.τ j h) (y.bes j 0 h).L.gram a.ζ₀
      rw [hg, hv, quad_smul, quad_smul_mat, hζ] at hval
      have hT0 : (D.mem u).A.T ≠ 0 := by
        intro h0
        rw [h0, Nat.cast_zero, mul_zero] at hval
        exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hlam0) hlam0) hl.2 hval.symm
      have hr1 : a.Lz.rank ≤ 1 := by
        have hu : IsUnit ((-(D.host.xi0 * star D.host.xi0)) • a.Lz.gram) := by
          rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
          exact ((isUnit_iff_ne_zero.2 hc).pow _).mul (gram_isUnit_det _)
        have hrk := Matrix.rank_of_isUnit _ hu
        rw [← hg, Fintype.card_fin] at hrk
        calc a.Lz.rank = ((y.τ j h)ᴴ * ((y.bes j 0 h).L.gram * y.τ j h)).rank := hrk.symm
          _ ≤ ((y.bes j 0 h).L.gram * y.τ j h).rank := Matrix.rank_mul_le_right _ _
          _ ≤ (y.τ j h).rank := Matrix.rank_mul_le_right _ _
          _ ≤ Fintype.card (Fin (y.bes j 0 h).L.rank) := Matrix.rank_le_card_height _
          _ = 1 := by rw [Fintype.card_fin, hl.1]
      have hr0 : a.Lz.rank ≠ 0 := by
        intro h0
        haveI : IsEmpty (Fin a.Lz.rank) := ⟨fun i => by have := i.2; omega⟩
        have : star a.ζ₀ ⬝ᵥ (a.Lz.gram *ᵥ a.ζ₀) = 0 := by simp [dotProduct]
        rw [hζ] at this
        exact hT0 (by exact_mod_cast this)
      obtain ⟨x, hx⟩ := exists_prime_not_mem D.host.F hT0
      have hxt : x ∉ v.tP := by rw [htP]; exact hx
      obtain ⟨LZ, hLZsd, -⟩ := hLZ D.R.m rfl x hxt
      refine ⟨_, selfDualFor_map (D.host.xi0⁻¹ • y.τ j h) (s := -1) (Or.inr rfl) ?_ (gram_isUnit_det _) ?_
        ((isSelfDualC_iff _ _).1 hLZsd)⟩
      · simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        rw [hg, smul_smul]
        convert (one_smul D.host.E a.Lz.gram).symm using 2
        rw [star_inv₀]; field_simp
      · rw [Fintype.card_fin, Fintype.card_fin, hl.1]; omega
    | succ σ ih =>
      intro j h
      obtain ⟨Λ', hΛ'⟩ := ih (j + 1 + 1) (idx_step h)
      have lk := y.lnk j σ h
      have hl := (y.bes j (σ + 1) h).line
      have hl' := (y.bes (j + 1 + 1) σ (idx_step h)).line
      refine ⟨_, selfDualFor_map (D.host.xi0⁻¹ • lk.τ) (s := 1) (Or.inl rfl) ?_ (gram_isUnit_det _) ?_ hΛ'⟩
      · refine line_mat_eq (by rw [Fintype.card_fin, hl'.1]) hl'.2 ?_
        rw [one_smul, Matrix.mul_assoc, quad_mul, Matrix.smul_mulVec, lk.map, smul_neg, ← neg_smul, quad_smul]
        change _ = star (-D.host.xi0⁻¹) * -D.host.xi0⁻¹ *
          (star (y.bes j (σ + 1) h).ζ ⬝ᵥ ((y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ))
        rw [show star (y.bes j (σ + 1) h).ζ ⬝ᵥ ((y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ) = _ from lk.norm,
          star_neg, star_inv₀]
        field_simp
      · rw [Fintype.card_fin, Fintype.card_fin, hl.1, hl'.1]
  intro j ρ h
  obtain ⟨ΛL, hΛL⟩ := hline ρ j h
  have hA : SelfDualFor (D.sp.X j).gram (a.x j).L := (isSelfDualC_iff _ _).1 (hIs.x j (by omega)).sd
  have hs := selfDualFor_sum hA hΛL
  have hmap := selfDualFor_map (G' := (y.bes j ρ h).V₀.gram) (Matrix.fromCols (y.bes j ρ h).o.iA (y.bes j ρ h).o.iB)
    (s := 1) (Or.inl rfl) ?_ ?_ ?_ hs
  · exact ⟨_, (isSelfDualC_iff _ _).2 hmap⟩
  · rw [one_smul, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      (y.bes j ρ h).o.isoA, (y.bes j ρ h).o.isoB, (y.bes j ρ h).o.orth, (y.bes j ρ h).o.orth']
  · rw [Matrix.det_fromBlocks_zero₂₁]
    exact (gram_isUnit_det _).mul (gram_isUnit_det _)
  · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, (y.bes j ρ h).o.rank_add]

end GlobalTheory.CoreLat
