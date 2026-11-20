import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective
import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspBasis

open GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, cc_sum', cc_mul']`.
-/
theorem map_cc_mul (A B : Matrix (Fin ρ) (Fin ρ) E) : (A * B).map cc = A.map cc * B.map cc := by
  ext a b
  simp [Matrix.mul_apply, cc_sum', cc_mul']

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[cc_cc']`.
-/
theorem map_cc_cc (A : Matrix (Fin ρ) (Fin ρ) E) : (A.map cc).map cc = A := by
  ext a b
  simp [cc_cc']

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `by_cases h : a = b <;> simp [Matrix.one_apply, h, cc]`.
-/
theorem map_cc_one : (1 : Matrix (Fin ρ) (Fin ρ) E).map cc = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.one_apply, h, cc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩`.
-/
theorem isSkew_iff (β : Matrix (Fin ρ) (Fin ρ) E) : FJ.IsSkew β ↔ β.map cc = -βᵀ :=
  ⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩`.
-/
theorem isHerm_iff (β : Matrix (Fin ρ) (Fin ρ) E) : FJ.IsHermE β ↔ β.map cc = βᵀ :=
  ⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩

/- English proof (translation)
Rewrite `h`, the goal using `[isHerm_iff]`. Rewrite using `[map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]`. Simplify using `[Matrix.transpose_mul, Matrix.mul_assoc]`.
-/
theorem isHerm_conj (P χ : Matrix (Fin ρ) (Fin ρ) E) (h : FJ.IsHermE χ) :
    FJ.IsHermE (P * χ * (P.map cc)ᵀ) := by
  rw [isHerm_iff] at h ⊢
  rw [map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/- English proof (translation)
Rewrite `h`, the goal using `[isSkew_iff]`. Rewrite using `[map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]`. Simplify using `[Matrix.transpose_mul, Matrix.mul_assoc]`.
-/
theorem isSkew_conj (P β : Matrix (Fin ρ) (Fin ρ) E) (h : FJ.IsSkew β) :
    FJ.IsSkew (Pᵀ * β * P.map cc) := by
  rw [isSkew_iff] at h ⊢
  rw [map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [h, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem comb_change {e₀ e : Fin ρ → Fin r → E} {P : Matrix (Fin ρ) (Fin ρ) E}
    (h : ∀ a, e₀ a = ∑ b, P a b • e b) (v : Fin ρ → E) :
    ∑ a, v a • e₀ a = ∑ b, (v ᵥ* P) b • e b := by
  simp only [h, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[Matrix.ext_iff_mulVec]`. Introduce `v`. Rewrite using `[zMatE_mulVec, zMatE_mulVec, comb_change h]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Use `congr 1`. Establish `h1 : (fun b => herm X.Gm v (e₀ b)) = P.map cc *ᵥ fun d => herm X.Gm v (e d)`. Use function extensionality and compare the values at `b`. Rewrite using `[h b, herm_comb_r]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `((β *ᵥ fun b => herm X.Gm v (e₀ b)) ᵥ* P) c = ((Pᵀ * β * P.map cc) *ᵥ fun d => herm X.Gm v (e d)) c`. Rewrite using `[h1, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem zMatE_change (X : Data E r) {e₀ e : Fin ρ → Fin r → E} {P : Matrix (Fin ρ) (Fin ρ) E}
    (h : ∀ a, e₀ a = ∑ b, P a b • e b) (β : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X e₀ β = FJ.zMatE X e (Pᵀ * β * P.map cc) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [zMatE_mulVec, zMatE_mulVec, comb_change h]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have h1 : (fun b => herm X.Gm v (e₀ b)) = P.map cc *ᵥ fun d => herm X.Gm v (e d) := by
    funext b
    rw [h b, herm_comb_r]
    rfl
  change ((β *ᵥ fun b => herm X.Gm v (e₀ b)) ᵥ* P) c =
    ((Pᵀ * β * P.map cc) *ᵥ fun d => herm X.Gm v (e d)) c
  rw [h1, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

variable {X : Data E r} {cu₀ cu : FJ.CuspFD X ρ} {P : Matrix (Fin ρ) (Fin ρ) E}

/- English proof (translation)
Take `⟨hs, γ, hγ, e⟩` from `hβ`. Conclude with `⟨isSkew_conj P β hs, γ, hγ, e.trans (zMatE_change X h β)⟩`.
-/
theorem zGam_change (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {β : Matrix (Fin ρ) (Fin ρ) E}
    (hβ : β ∈ FJ.zGam X cu₀) : Pᵀ * β * P.map cc ∈ FJ.zGam X cu := by
  obtain ⟨hs, γ, hγ, e⟩ := hβ
  exact ⟨isSkew_conj P β hs, γ, hγ, e.trans (zMatE_change X h β)⟩

/- English proof (translation)
Use `inf_le_inf_left _ fun x hx => ?_` and prove the remaining obligations. Establish `hle : Submodule.span E (Set.range cu₀.e) ≤ Submodule.span E (Set.range cu.e)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[h a]`.

Conclude with `sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`. Conclude with `hle hx`.
-/
theorem lattice_le (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) : cu₀.I ≤ cu.I := by
  refine inf_le_inf_left _ fun x hx => ?_
  have hle : Submodule.span E (Set.range cu₀.e) ≤ Submodule.span E (Set.range cu.e) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [h a]
    exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  exact hle hx

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨a, ha, x, hx, e⟩` from `hv`. Conclude with `Submodule.subset_span ⟨a, ha, x, lattice_le h hx, e.trans (comb_change h v)⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [Matrix.add_vecMul]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [Matrix.smul_vecMul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem crdI_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {v : Fin ρ → E} (hv : v ∈ FJ.crdI 𝔄 cu₀) :
    v ᵥ* P ∈ FJ.crdI 𝔄 cu := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, x, hx, e⟩ := hv
    exact Submodule.subset_span ⟨a, ha, x, lattice_le h hx, e.trans (comb_change h v)⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.smul_vecMul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(P *ᵥ l) ⬝ᵥ x = l ⬝ᵥ (x ᵥ* P)`. Rewrite using `[dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]`.
-/
theorem pair_change (P : Matrix (Fin ρ) (Fin ρ) E) (l x : Fin ρ → E) :
    ∑ i, (P *ᵥ l) i * x i = ∑ i, l i * (x ᵥ* P) i := by
  change (P *ᵥ l) ⬝ᵥ x = l ⬝ᵥ (x ᵥ* P)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

/- English proof (translation)
Rewrite `hl`, the goal using `[← SetLike.mem_coe, FJ.xcFD_coe]`. Introduce `x hx`. Rewrite using `[pair_change]`. Conclude with `hl _ (crdI_change 𝔄 h hx)`.
-/
theorem xcFD_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {l : Fin ρ → E} (hl : l ∈ FJ.XcFD 𝔄 cu) :
    P *ᵥ l ∈ FJ.XcFD 𝔄 cu₀ := by
  rw [← SetLike.mem_coe, FJ.xcFD_coe] at hl ⊢
  intro x hx
  rw [pair_change]
  exact hl _ (crdI_change 𝔄 h hx)

/- English proof (translation)
Introduce `l hl`. Establish `h1` using `hu _ (xcFD_change 𝔄 h hl)`. Establish `h2` using `pair_change P l u`. Simplify using `only [mul_comm (u _), mul_comm ((u ᵥ* P) _)] at h1 ⊢`. Rewrite using `[← h2]` and apply the resulting hypothesis.
-/
theorem dualOE_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {u : Fin ρ → E} (hu : u ∈ FJ.dualOE (FJ.XcFD 𝔄 cu₀)) :
    u ᵥ* P ∈ FJ.dualOE (FJ.XcFD 𝔄 cu) := by
  intro l hl
  have h1 := hu _ (xcFD_change 𝔄 h hl)
  have h2 := pair_change P l u
  simp only [mul_comm (u _), mul_comm ((u ᵥ* P) _)] at h1 ⊢
  rwa [← h2]

/- English proof (translation)
Establish `: Matrix.trace ((P * χ * (P.map cc)ᵀ)ᵀ * β) = Matrix.trace (χᵀ * (Pᵀ * β * P.map cc))`. Rewrite using `[← Matrix.mul_assoc χᵀ, Matrix.trace_mul_comm _ (P.map cc)]`. Simplify using `[Matrix.transpose_mul, Matrix.mul_assoc]`. Simplify using `only [FJ.prE, this]`.
-/
theorem prE_change (X : Data E r) (P χ β : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.prE X (P * χ * (P.map cc)ᵀ) β = FJ.prE X χ (Pᵀ * β * P.map cc) := by
  have : Matrix.trace ((P * χ * (P.map cc)ᵀ)ᵀ * β) = Matrix.trace (χᵀ * (Pᵀ * β * P.map cc)) := by
    rw [← Matrix.mul_assoc χᵀ, Matrix.trace_mul_comm _ (P.map cc)]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  simp only [FJ.prE, this]

/- English proof (translation)
Simplify using `[dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem form_eq (χ : Matrix (Fin ρ) (Fin ρ) E) (u m : Fin ρ → E) :
    ∑ i, ∑ k, u i * χ i k * cc (m k) = u ⬝ᵥ (χ *ᵥ fun k => cc (m k)) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `h1 : (fun k => cc ((m ᵥ* P) k)) = (P.map cc)ᵀ *ᵥ fun k => cc (m k)`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.vecMul, Matrix.mulVec, dotProduct, cc_sum', cc_mul', mul_comm]`. Rewrite using `[form_eq, form_eq, h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem form_change (P χ : Matrix (Fin ρ) (Fin ρ) E) (u m : Fin ρ → E) :
    ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) =
      ∑ i, ∑ k, (u ᵥ* P) i * χ i k * cc ((m ᵥ* P) k) := by
  have h1 : (fun k => cc ((m ᵥ* P) k)) = (P.map cc)ᵀ *ᵥ fun k => cc (m k) := by
    funext k
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cc_sum', cc_mul', mul_comm]
  rw [form_eq, form_eq, h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Introduce `β hβ` and use `by rw [prE_change] exact hχ _ (zGam_change h hβ)`.
-/
theorem phase_change (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) :
    ∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X (P * χ * (P.map cc)ᵀ) β = n := fun β hβ => by
  rw [prE_change]
  exact hχ _ (zGam_change h hβ)

/- English proof (translation)
Introduce `u hu m hm` and use `by rw [form_change] exact hχ _ (dualOE_change 1 h hu) _ (dualOE_change 1 h hm)`.
-/
theorem integral_change (N : ℕ) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b)
    {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu),
      (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) :
    ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀),
      (N : E) * ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) ∈
        Set.range (algebraMap (𝓞 E) E) := fun u hu m hm => by
  rw [form_change]
  exact hχ _ (dualOE_change 1 h hu) _ (dualOE_change 1 h hm)

/- English proof (translation)
Rewrite using `[comb_change h (P⁻¹ a)]`. Establish `h1 : P⁻¹ a ᵥ* P = (1 : Matrix (Fin ρ) (Fin ρ) E) a`. Rewrite using `[← Matrix.nonsing_inv_mul P hP]`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Simplify using `[Matrix.one_apply]`.
-/
theorem basis_inv (hP : IsUnit P.det) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) (a : Fin ρ) :
    cu.e a = ∑ b, P⁻¹ a b • cu₀.e b := by
  rw [comb_change h (P⁻¹ a)]
  have h1 : P⁻¹ a ᵥ* P = (1 : Matrix (Fin ρ) (Fin ρ) E) a := by
    rw [← Matrix.nonsing_inv_mul P hP]
    rfl
  rw [h1]
  simp [Matrix.one_apply]

/- English proof (translation)
Establish `h1 : (P⁻¹.map cc)ᵀ * (P.map cc)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, ← map_cc_mul, Matrix.mul_nonsing_inv P hP, map_cc_one, Matrix.transpose_one]`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP, Matrix.one_mul]`.
-/
theorem conj_inv (hP : IsUnit P.det) (χ : Matrix (Fin ρ) (Fin ρ) E) :
    P * (P⁻¹ * χ * (P⁻¹.map cc)ᵀ) * (P.map cc)ᵀ = χ := by
  have h1 : (P⁻¹.map cc)ᵀ * (P.map cc)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← map_cc_mul, Matrix.mul_nonsing_inv P hP, map_cc_one,
      Matrix.transpose_one]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

/- English proof (translation)
Introduce `E _ _ _ r ρ N X cu₀ cu P hP h H χ hχ`. Establish `hQ` using `basis_inv hP h`. Establish `H'` using `H _ (isHerm_conj P⁻¹ χ hχ)`. Prove the components needed by the constructor for the conclusion. Introduce `hA`.

Use `integral_change N h (H'.1 (phase_change hQ hA))` as an intermediate fact. Rewrite `this` using `[conj_inv hP]`. Then use the resulting hypothesis. Introduce `hB`. Use `phase_change h (H'.2 (integral_change N hQ hB))` as an intermediate fact. Rewrite `this` using `[conj_inv hP]`. Then use the resulting hypothesis.
-/
theorem expoMatch_of_basis_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ r ρ N X cu₀ cu P hP h H χ hχ
  have hQ := basis_inv hP h
  have H' := H _ (isHerm_conj P⁻¹ χ hχ)
  constructor
  · intro hA
    have := integral_change N h (H'.1 (phase_change hQ hA))
    rwa [conj_inv hP] at this
  · intro hB
    have := phase_change h (H'.2 (integral_change N hQ hB))
    rwa [conj_inv hP] at this

end GlobalTheory.CuspBasis
