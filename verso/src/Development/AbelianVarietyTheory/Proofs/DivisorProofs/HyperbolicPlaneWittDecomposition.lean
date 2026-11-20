import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParDec
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.InducedCons.ParGrp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in

/- English proof (translation)
Establish `e : mat (m * m') = mat m * mat m'` using `rfl`. Establish `e1 : mat (γ * h₁) = mat γ * mat h₁` using `rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]`. Rewrite using `[e, ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]`.

Rewrite using `[e, Matrix.mul_assoc, h'.2.2, e1, ← Matrix.mul_assoc, h.2.2, Matrix.mul_assoc]`.
-/
theorem isLevi_mul {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {t s : (AE F E)ˣ}
    {γ h₁ : UA σ W₁.J} {m m' : UA σ W.J} (h : IsLevi (W₁ := W₁) H t γ m) (h' : IsLevi (W₁ := W₁) H s h₁ m') :
    IsLevi (W₁ := W₁) H (t * s) (γ * h₁) (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (γ * h₁) = mat γ * mat h₁ := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]
  · rw [e, ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [e, Matrix.mul_assoc, h'.2.2, e1, ← Matrix.mul_assoc, h.2.2, Matrix.mul_assoc]

omit [NumberField E] in

/- English proof (translation)
Establish `hi : mat m⁻¹ * mat m = 1` using `by show (m.1⁻¹ * m.1 : GL _ _).1 = 1`. Simplify using the standard rewrite rules. Establish `hg : mat γ * mat γ⁻¹ = 1` using `by show (γ.1 * γ.1⁻¹ : GL _ _).1 = 1`. Simplify using the standard rewrite rules. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg (fun v => ((t⁻¹ : (AE F E)ˣ) : AE F E) • (mat m⁻¹ *ᵥ v)) h.1`. Simplify using `only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul] at h1`. Conclude with `h1.symm`. Establish `h1` using `congrArg (fun v => cA σ (t : AE F E) • (mat m⁻¹ *ᵥ v)) h.2.1`. Simplify using `only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul] at h1`.

Rewrite using `[inv_inv]`. Conclude with `h1.symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isLevi_inv {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {t : (AE F E)ˣ}
    {γ : UA σ W₁.J} {m : UA σ W.J} (h : IsLevi (W₁ := W₁) H t γ m) : IsLevi (W₁ := W₁) H t⁻¹ γ⁻¹ m⁻¹ := by
  have hi : mat m⁻¹ * mat m = 1 := by
    show (m.1⁻¹ * m.1 : GL _ _).1 = 1
    simp
  have hg : mat γ * mat γ⁻¹ = 1 := by
    show (γ.1 * γ.1⁻¹ : GL _ _).1 = 1
    simp
  refine ⟨?_, ?_, ?_⟩
  · have h1 := congrArg (fun v => ((t⁻¹ : (AE F E)ˣ) : AE F E) • (mat m⁻¹ *ᵥ v)) h.1
    simp only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul,
      one_smul] at h1
    exact h1.symm
  · have h1 := congrArg (fun v => cA σ (t : AE F E) • (mat m⁻¹ *ᵥ v)) h.2.1
    simp only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, ← map_mul, Units.mul_inv,
      map_one, one_smul] at h1
    rw [inv_inv]
    exact h1.symm
  · calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * incM F H.ι * (mat γ * mat γ⁻¹) := by rw [hg, Matrix.mul_one]
      _ = mat m⁻¹ * (incM F H.ι * mat γ) * mat γ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = mat m⁻¹ * (mat m * incM F H.ι) * mat γ⁻¹ := by rw [h.2.2]
      _ = incM F H.ι * mat γ⁻¹ := by rw [← Matrix.mul_assoc (mat m⁻¹), hi, Matrix.one_mul]

omit [NumberField E] in

/- English proof (translation)
Establish `hi` using `isLevi_inv h`. Establish `hg : mat γ * mat γ⁻¹ = 1` using `by show (γ.1 * γ.1⁻¹ : GL _ _).1 = 1`. Simplify using the standard rewrite rules. Proceed by induction on `hu using Subgroup.closure_induction with`. Consider the case `mem u hu`.

Use `Subgroup.subset_closure ⟨?_, fun z => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(mat m * mat u * mat m⁻¹) *ᵥ _ = _`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hi.1, Matrix.mulVec_smul, hu.1, Matrix.mulVec_smul, h.1, smul_smul, Units.inv_mul, one_smul]`. Take `⟨a, ha⟩` from `hu.2 (mat γ⁻¹ *ᵥ z)`. Use `⟨a * t, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(mat m * mat u * mat m⁻¹) *ᵥ _ = _`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat m⁻¹), hi.2.2, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, h.1, smul_smul, Matrix.mulVec_mulVec, h.2.2, Matrix.mulVec_mulVec, Matrix.mul_assoc, hg, Matrix.mul_one]`. Consider the case `one => simpa using (unip σ W H).one_mem`. Consider the case `mul a b _ _ ha hb`. Establish `e : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹)` using `by group`.

Rewrite using `[e]`. Conclude with `(unip σ W H).mul_mem ha hb`. Consider the case `inv a _ ha`. Establish `e : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `(unip σ W H).inv_mem ha`.
-/
theorem conj_mem_unip {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {t : (AE F E)ˣ}
    {γ : UA σ W₁.J} {m : UA σ W.J} (h : IsLevi (W₁ := W₁) H t γ m) {u : UA σ W.J} (hu : u ∈ unip σ W H) :
    m * u * m⁻¹ ∈ unip σ W H := by
  have hi := isLevi_inv h
  have hg : mat γ * mat γ⁻¹ = 1 := by
    show (γ.1 * γ.1⁻¹ : GL _ _).1 = 1
    simp
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
    · change (mat m * mat u * mat m⁻¹) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hi.1, Matrix.mulVec_smul, hu.1, Matrix.mulVec_smul, h.1,
        smul_smul, Units.inv_mul, one_smul]
    · obtain ⟨a, ha⟩ := hu.2 (mat γ⁻¹ *ᵥ z)
      refine ⟨a * t, ?_⟩
      change (mat m * mat u * mat m⁻¹) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat m⁻¹), hi.2.2,
        ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, h.1, smul_smul,
        Matrix.mulVec_mulVec, h.2.2, Matrix.mulVec_mulVec, Matrix.mul_assoc, hg, Matrix.mul_one]
  | one => simpa using (unip σ W H).one_mem
  | mul a b _ _ ha hb =>
    have e : m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) := by group
    rw [e]
    exact (unip σ W H).mul_mem ha hb
  | inv a _ ha =>
    have e : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
    rw [e]
    exact (unip σ W H).inv_mem ha

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ c₀ hc₀ hW₁ hW M _ hM _ r Xf Yf _ X' Y' hF hX _ _`. Establish `hP : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁` using `⟨hn, hxx, hyy, hxy, hι, hJ⟩`. Establish `hd : W₁.J.det ≠ 0` using `fun h0 => hW₁.2 (by`. Establish `e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det` using `by rw [RingHom.map_det]; rfl`. Rewrite using `[Matrix.det_smul, e, h0, map_zero, mul_zero])`.

Use `set φ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ with hφ`. Use `set ψ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀ with hψ`. Establish `hU : ∀ g, g ∈ unip σ W H ↔ φ g ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}` using `fun g => hP.mem_unip_iff hσ hsk hd hc₀ hF (Nat.succ_pos r) hX g`. Establish `key : ∀ t y g, IsParDec hσ W W₁ H hc₀ X' M t y g ↔ ∃ u ∈ unip σ W H, ∃ l, IsLevi (W₁` using `W₁) H t (ψ.symm y) l ∧ g = φ (u * l) := by`. Introduce `t y g`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, m, hm, rfl⟩`. Use `⟨φ.symm u, (hU _).2 (by rwa [MulEquiv.apply_symm_apply]), m * M (ψ.symm y), ?_, ?_⟩` and prove the remaining obligations. Simplify `isLevi_mul hm (hM (ψ.symm y))` using `only [mul_one, one_mul]`. Rewrite using `[map_mul, map_mul, MulEquiv.apply_symm_apply, ← mul_assoc]`.

Both sides reduce to the same expression. Introduce and unpack `⟨u, hu, l, hl, rfl⟩`. Use `⟨φ u, (hU _).1 hu, l * (M (ψ.symm y))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Simplify `isLevi_mul hl (isLevi_inv (hM (ψ.symm y)))` using `only [inv_one, mul_one, mul_inv_cancel]`. Express the relevant statement in the definitionally equal form `φ (u * l) = φ u * φ (l * (M (ψ.symm y))⁻¹) * φ (M (ψ.symm y))`.

Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Use `group`. Use `⟨fun t t' y y' g g' h h' => ?_, fun t y g h => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, l, hl, rfl⟩` from `(key _ _ _).1 h`.

Take `⟨u', hu', l', hl', rfl⟩` from `(key _ _ _).1 h'`. Use `(key _ _ _).2 ⟨u * (l * u' * l⁻¹), mul_mem hu (conj_mem_unip hl hu'), l * l', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `isLevi_mul hl hl'`. Rewrite using `[← map_mul]`.

Use `congr 1`. Use `group`. Take `⟨u, hu, l, hl, rfl⟩` from `(key _ _ _).1 h`. Use `(key _ _ _).2 ⟨l⁻¹ * u⁻¹ * l⁻¹⁻¹, conj_mem_unip (isLevi_inv hl) (inv_mem hu), l⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv]`.

Conclude with `isLevi_inv hl`. Rewrite using `[← map_inv]`. Use `congr 1`. Use `group`.
-/
theorem isParDec_mul_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → (∀ (t t' : (AE F E)ˣ) (y y' : GAd σ (c₀ • W₁.J.map σ)) (g g' : GAd σ (c₀ • W.J.map σ)), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g → GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t' y' g' → GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M (t * t') (y * y') (g * g')) ∧
      (∀ (t : (AE F E)ˣ) (y : GAd σ (c₀ • W₁.J.map σ)) (g : GAd σ (c₀ • W.J.map σ)), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g → GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t⁻¹ y⁻¹ g⁻¹) := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ c₀ hc₀ hW₁ hW M _ hM _ r Xf Yf _ X' Y' hF hX _ _
  have hP : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, hι, hJ⟩
  have hd : W₁.J.det ≠ 0 := fun h0 => hW₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  set φ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ with hφ
  set ψ := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀ with hψ
  have hU : ∀ g, g ∈ unip σ W H ↔ φ g ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0} := fun g =>
    hP.mem_unip_iff hσ hsk hd hc₀ hF (Nat.succ_pos r) hX g

  have key : ∀ t y g, IsParDec hσ W W₁ H hc₀ X' M t y g ↔
      ∃ u ∈ unip σ W H, ∃ l, IsLevi (W₁ := W₁) H t (ψ.symm y) l ∧ g = φ (u * l) := by
    intro t y g
    constructor
    · rintro ⟨u, hu, m, hm, rfl⟩
      refine ⟨φ.symm u, (hU _).2 (by rwa [MulEquiv.apply_symm_apply]), m * M (ψ.symm y), ?_, ?_⟩
      · simpa only [mul_one, one_mul] using isLevi_mul hm (hM (ψ.symm y))
      · rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← mul_assoc]
        rfl
    · rintro ⟨u, hu, l, hl, rfl⟩
      refine ⟨φ u, (hU _).1 hu, l * (M (ψ.symm y))⁻¹, ?_, ?_⟩
      · simpa only [inv_one, mul_one, mul_inv_cancel] using isLevi_mul hl (isLevi_inv (hM (ψ.symm y)))
      · change φ (u * l) = φ u * φ (l * (M (ψ.symm y))⁻¹) * φ (M (ψ.symm y))
        rw [← map_mul, ← map_mul]
        congr 1
        group
  refine ⟨fun t t' y y' g g' h h' => ?_, fun t y g h => ?_⟩
  · obtain ⟨u, hu, l, hl, rfl⟩ := (key _ _ _).1 h
    obtain ⟨u', hu', l', hl', rfl⟩ := (key _ _ _).1 h'
    refine (key _ _ _).2 ⟨u * (l * u' * l⁻¹), mul_mem hu (conj_mem_unip hl hu'), l * l', ?_, ?_⟩
    · rw [map_mul]
      exact isLevi_mul hl hl'
    · rw [← map_mul]
      congr 1
      group
  · obtain ⟨u, hu, l, hl, rfl⟩ := (key _ _ _).1 h
    refine (key _ _ _).2 ⟨l⁻¹ * u⁻¹ * l⁻¹⁻¹, conj_mem_unip (isLevi_inv hl) (inv_mem hu), l⁻¹, ?_, ?_⟩
    · rw [map_inv]
      exact isLevi_inv hl
    · rw [← map_inv]
      congr 1
      group

end GlobalTheory.ThK.InducedCons.ParGrp

end
