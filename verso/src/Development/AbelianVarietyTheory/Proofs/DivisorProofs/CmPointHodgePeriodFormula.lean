import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.CMRiem

open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart u valueRules hL 0`. Establish `hl : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ))).left ⁻¹ᵁ L.U i` using `by rwa [ex_add_period u 0 _ l.2]`. Establish `hm : ⊤ ≤ (u.ex (0 + (m : Fin g → ℂ))).left ⁻¹ᵁ L.U i` using `by rwa [ex_add_period u 0 _ m.2]`. Establish `hlm : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ) + m)).left ⁻¹ᵁ L.U i`. Rewrite using `[ex_add_period u _ _ m.2, ex_add_period u 0 _ l.2]` and apply the resulting hypothesis.

Establish `e1` using `h.2.2.2 l i 0 hi`. Establish `e2` using `h.2.2.2 m i _ hl`. Establish `e3` using `h.2.2.2 m i 0 hi`. Establish `e4` using `h.2.2.2 l i _ hm`. Establish `hc : (0 : Fin g → ℂ) + m + l = 0 + l + m` using `by abel`.

Rewrite `e4` using `[hc]`. Establish `hne` using `u.fr_ne i _ hlm`. Rewrite `hne` using `[zero_add]`. Establish `hχl : χ l ≠ 0` using `fun h0 ↦ by simpa [h0] using h.2.2.1 l`. Establish `hχm : χ m ≠ 0` using `fun h0 ↦ by simpa [h0] using h.2.2.1 m`.

Simplify using `only [zero_add, zero_dotProduct, mul_zero, Complex.exp_add, Complex.exp_zero, one_mul] at e1 e2 e3 e4`. Use `set X := Complex.exp (Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))`. Use `set Y := Complex.exp (Real.pi / 2 * ((m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))))`. Establish `hX : X ≠ 0` using `Complex.exp_ne_zero _`. Establish `hY : Y ≠ 0` using `Complex.exp_ne_zero _`.

Establish `key : (χ l * χ m * X * Y * u.fr i ((l : Fin g → ℂ) + m)) * Complex.exp (Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)))) = (χ l * χ m * X * Y * u.fr i ((l : Fin g → ℂ) + m)) * Complex.exp (Real.pi * ((m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))`. Take the linear combination `(-1 : ℂ) * e1 - χ l * X * e2 + e3 + χ m * Y * e4`. Conclude with `mul_left_cancel₀ (by simp [hχl, hχm, hX, hY, hne]) key`.
-/
theorem exp_herm_swap {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (hL : L.IsLB)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (l m : u.Λ) :
    Complex.exp (Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)))) =
      Complex.exp (Real.pi * ((m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) := by
  obtain ⟨i, hi⟩ := exists_chart u valueRules hL 0
  have hl : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ))).left ⁻¹ᵁ L.U i := by rwa [ex_add_period u 0 _ l.2]
  have hm : ⊤ ≤ (u.ex (0 + (m : Fin g → ℂ))).left ⁻¹ᵁ L.U i := by rwa [ex_add_period u 0 _ m.2]
  have hlm : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ) + m)).left ⁻¹ᵁ L.U i := by
    rwa [ex_add_period u _ _ m.2, ex_add_period u 0 _ l.2]
  have e1 := h.2.2.2 l i 0 hi
  have e2 := h.2.2.2 m i _ hl
  have e3 := h.2.2.2 m i 0 hi
  have e4 := h.2.2.2 l i _ hm
  have hc : (0 : Fin g → ℂ) + m + l = 0 + l + m := by abel
  rw [hc] at e4
  have hne := u.fr_ne i _ hlm
  rw [zero_add] at hne
  have hχl : χ l ≠ 0 := fun h0 ↦ by simpa [h0] using h.2.2.1 l
  have hχm : χ m ≠ 0 := fun h0 ↦ by simpa [h0] using h.2.2.1 m
  simp only [zero_add, zero_dotProduct, mul_zero, Complex.exp_add, Complex.exp_zero, one_mul] at e1 e2 e3 e4
  set X := Complex.exp (Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))
  set Y := Complex.exp (Real.pi / 2 * ((m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))))
  have hX : X ≠ 0 := Complex.exp_ne_zero _
  have hY : Y ≠ 0 := Complex.exp_ne_zero _
  have key : (χ l * χ m * X * Y * u.fr i ((l : Fin g → ℂ) + m)) *
      Complex.exp (Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)))) =
      (χ l * χ m * X * Y * u.fr i ((l : Fin g → ℂ) + m)) *
      Complex.exp (Real.pi * ((m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) := by
    linear_combination (-1 : ℂ) * e1 - χ l * X * e2 + e3 + χ m * Y * e4
  exact mul_left_cancel₀ (by simp [hχl, hχm, hX, hY, hne]) key

end GlobalTheory.CMRiem

namespace GlobalTheory.CMRiem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]

/- English proof (translation)
Establish `hnr : ∀ i, NumberField.ComplexEmbedding.conjugate (φ i) ≠ φ i` using `fun i h ↦ (NumberField.InfinitePlace.isComplex_mk_iff.1 (NumberField.IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk (φ i)))) (NumberField.ComplexEmbedding.isReal_iff.2 h)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | i) (j | j) h`. Simplify using `only [Sum.elim_inl] at h`. Take `⟨k, -, hk⟩` from `hφ (φ i)`.

Rewrite using `[hk i (Or.inl rfl), hk j (Or.inl h)]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at h`. Take `⟨k, -, hk⟩` from `hφ (φ i)`. Use `(hk i (Or.inl rfl)).trans (hk j (Or.inr h)).symm` as an intermediate fact. Substitute `this` using the available equality.

Conclude with `absurd h.symm (hnr i)`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at h`. Take `⟨k, -, hk⟩` from `hφ (φ j)`. Use `(hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm` as an intermediate fact. Substitute `this` using the available equality.

Conclude with `absurd h (hnr i)`. Simplify using `only [Sum.elim_inr] at h`. Establish `h' : φ i = φ j`. Simplify using `using congrArg NumberField.ComplexEmbedding.conjugate h`. Take `⟨k, -, hk⟩` from `hφ (φ i)`.

Rewrite using `[hk i (Or.inl rfl), hk j (Or.inl h')]`. Introduce `σ`. Take `⟨i, hi, -⟩` from `hφ σ`. Break down `hi with h | h` into its components or cases. Conclude with `⟨Sum.inl i, h.symm⟩`.

Conclude with `⟨Sum.inr i, h.symm⟩`.
-/
theorem cmEmb_bijective (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    Function.Bijective (Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) := by
  have hnr : ∀ i, NumberField.ComplexEmbedding.conjugate (φ i) ≠ φ i := fun i h ↦
    (NumberField.InfinitePlace.isComplex_mk_iff.1 (NumberField.IsTotallyComplex.isComplex
      (NumberField.InfinitePlace.mk (φ i)))) (NumberField.ComplexEmbedding.isReal_iff.2 h)
  refine ⟨?_, ?_⟩
  · rintro (i | i) (j | j) h
    · simp only [Sum.elim_inl] at h
      obtain ⟨k, -, hk⟩ := hφ (φ i)
      rw [hk i (Or.inl rfl), hk j (Or.inl h)]
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      obtain ⟨k, -, hk⟩ := hφ (φ i)
      have := (hk i (Or.inl rfl)).trans (hk j (Or.inr h)).symm
      subst this
      exact absurd h.symm (hnr i)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      obtain ⟨k, -, hk⟩ := hφ (φ j)
      have := (hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm
      subst this
      exact absurd h (hnr i)
    · simp only [Sum.elim_inr] at h
      have h' : φ i = φ j := by
        simpa using congrArg NumberField.ComplexEmbedding.conjugate h
      obtain ⟨k, -, hk⟩ := hφ (φ i)
      rw [hk i (Or.inl rfl), hk j (Or.inl h')]
  · intro σ
    obtain ⟨i, hi, -⟩ := hφ σ
    rcases hi with h | h
    · exact ⟨Sum.inl i, h.symm⟩
    · exact ⟨Sum.inr i, h.symm⟩

/- English proof (translation)
Establish `h1` using `trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)`. Rewrite `h1` using `[eq_ratCast]`. Rewrite using `[h1, ← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ ↦ σ x) (fun σ ↦ σ x) (fun σ ↦ rfl), ← Fintype.sum_bijective _ (cmEmb_bijective φ hφ) (fun s ↦ (Sum.elim φ (fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s) x) (fun σ : E →+* ℂ ↦ σ x) (fun s ↦ rfl), Fin …`. Simplify using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem trace_eq_sum_cm (φ : I → E →+* ℂ) (hφ : IsCMType φ) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ i, (φ i x + starRingEnd ℂ (φ i x)) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h1
  rw [h1, ← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ ↦ σ x) (fun σ ↦ σ x)
    (fun σ ↦ rfl), ← Fintype.sum_bijective _ (cmEmb_bijective φ hφ) (fun s ↦ (Sum.elim φ
      (fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s) x) (fun σ : E →+* ℂ ↦ σ x) (fun s ↦ rfl),
    Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Establish `h` using `linearIndependent_monoidHom E ℂ`. Establish `hinj : Function.Injective (fun s : I ⊕ I ↦ ((Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s : E →* ℂ))`. Introduce `s t hst`. Apply `(cmEmb_bijective φ hφ).1` to reduce the goal to its premises. Use extensionality with `x`.

Conclude with `DFunLike.congr_fun hst x`. Conclude with `h.comp _ hinj`.
-/
theorem cmEmb_linearIndependent (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    LinearIndependent ℂ (fun s : I ⊕ I ↦
      ((Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s : E → ℂ)) := by
  have h := linearIndependent_monoidHom E ℂ
  have hinj : Function.Injective (fun s : I ⊕ I ↦
      ((Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s : E →* ℂ)) := by
    intro s t hst
    apply (cmEmb_bijective φ hφ).1
    ext x
    exact DFunLike.congr_fun hst x
  exact h.comp _ hinj

end GlobalTheory.CMRiem

namespace GlobalTheory.CMRiem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]

/- English proof (translation)
Use `set W := Submodule.span ℚ L`. Set `Φ : E →ₗ[ℚ] (Fin g → ℂ)` to `(AddMonoidHom.mk' (fun x j ↦ φ (e j) x) (fun a b ↦ by funext j; simp)).toRatLinearMap`. Set `b` to `Module.finBasis ℚ W`. Set `v : Fin (Module.finrank ℚ W) → (Fin g → ℂ)` to `fun k ↦ Φ (b k)`. Establish `hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤ Submodule.span ℝ (Set.range v)`.

Rewrite using `[Submodule.span_le]`. Introduce `w hw`. Take `⟨x, hx, rfl⟩` from `(hlat w).1 hw`. Establish `hxW : x ∈ W` using `Submodule.subset_span hx`. Establish `h1 : (fun j ↦ φ (e j) x) = Φ ((⟨x, hxW⟩ : W) : E)` using `rfl`.

Rewrite using `[h1, ← b.sum_repr ⟨x, hxW⟩]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]`. Use `Submodule.sum_mem _ fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← Rat.cast_smul_eq_qsmul ℝ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Establish `h2g : Module.finrank ℝ (Fin g → ℂ) = 2 * g`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex, mul_comm]`. Establish `hrank : 2 * g ≤ Module.finrank ℚ W`. Combine the equalities or inequalities in the displayed calculation.

Establish `hE : Module.finrank ℚ E = 2 * g`. Rewrite using `[← NumberField.Embeddings.card E ℂ, ← Fintype.card_of_bijective (cmEmb_bijective φ hφ), Fintype.card_sum, ← Fintype.card_congr e, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) (hE ▸ hrank))`.
-/
theorem span_eq_top_of_full (φ : I → E →+* ℂ) (hφ : IsCMType φ) {g : ℕ} (e : Fin g ≃ I) (L : Set E)
    (Λ : Submodule ℤ (Fin g → ℂ)) (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hlat : ∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) : Submodule.span ℚ L = ⊤ := by
  set W := Submodule.span ℚ L
  let Φ : E →ₗ[ℚ] (Fin g → ℂ) :=
    (AddMonoidHom.mk' (fun x j ↦ φ (e j) x) (fun a b ↦ by funext j; simp)).toRatLinearMap
  let b := Module.finBasis ℚ W
  let v : Fin (Module.finrank ℚ W) → (Fin g → ℂ) := fun k ↦ Φ (b k)
  have hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤ Submodule.span ℝ (Set.range v) := by
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨x, hx, rfl⟩ := (hlat w).1 hw
    have hxW : x ∈ W := Submodule.subset_span hx
    have h1 : (fun j ↦ φ (e j) x) = Φ ((⟨x, hxW⟩ : W) : E) := rfl
    rw [h1, ← b.sum_repr ⟨x, hxW⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [← Rat.cast_smul_eq_qsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h2g : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm]
  have hrank : 2 * g ≤ Module.finrank ℚ W := by
    calc 2 * g = Module.finrank ℝ (⊤ : Submodule ℝ (Fin g → ℂ)) := by rw [finrank_top, h2g]
      _ = Module.finrank ℝ (Submodule.span ℝ (Λ : Set (Fin g → ℂ))) := by rw [hfull]
      _ ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin (Module.finrank ℚ W)) := finrank_range_le_card v
      _ = Module.finrank ℚ W := Fintype.card_fin _
  have hE : Module.finrank ℚ E = 2 * g := by
    rw [← NumberField.Embeddings.card E ℂ, ← Fintype.card_of_bijective (cmEmb_bijective φ hφ),
      Fintype.card_sum, ← Fintype.card_congr e, Fintype.card_fin]
    ring
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) (hE ▸ hrank))

/- English proof (translation)
Set `S : Submodule ℚ E` to `(LinearMap.range (Algebra.linearMap ℚ ℝ)).comap f.toRatLinearMap`. Establish `hLS : L ⊆ S` using `fun x hx ↦ by`. Take `⟨q, hq⟩` from `hf x hx`. Conclude with `⟨q, by simp [hq]⟩`. Establish `hS : S = ⊤` using `eq_top_iff.2 (hL ▸ Submodule.span_le.2 hLS)`.

Establish `hx : x ∈ S` using `hS ▸ Submodule.mem_top`. Take `⟨q, hq⟩` from `hx`. Conclude with `⟨q, by simpa using hq.symm⟩`.
-/
theorem rat_of_span {L : Set E} (hL : Submodule.span ℚ L = ⊤) (f : E →+ ℝ)
    (hf : ∀ x ∈ L, ∃ q : ℚ, f x = q) (x : E) : ∃ q : ℚ, f x = q := by
  let S : Submodule ℚ E := (LinearMap.range (Algebra.linearMap ℚ ℝ)).comap f.toRatLinearMap
  have hLS : L ⊆ S := fun x hx ↦ by
    obtain ⟨q, hq⟩ := hf x hx
    exact ⟨q, by simp [hq]⟩
  have hS : S = ⊤ := eq_top_iff.2 (hL ▸ Submodule.span_le.2 hLS)
  have hx : x ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨q, hq⟩ := hx
  exact ⟨q, by simpa using hq.symm⟩

end GlobalTheory.CMRiem

namespace GlobalTheory.CMRiem

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def hermE (φ : I → E →+* ℂ) (h : I → ℝ) (x x' : E) : ℂ := ∑ i, (h i : ℂ) * (φ i x * starRingEnd ℂ (φ i x'))

/- English proof (translation)
Simplify using `only [hermE, map_add, add_mul, mul_add, Finset.sum_add_distrib]`.
-/
theorem hermE_add_left (φ : I → E →+* ℂ) (h : I → ℝ) (a b x' : E) :
    hermE φ h (a + b) x' = hermE φ h a x' + hermE φ h b x' := by
  simp only [hermE, map_add, add_mul, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermE, map_add, add_mul, mul_add, Finset.sum_add_distrib]`.
-/
theorem hermE_add_right (φ : I → E →+* ℂ) (h : I → ℝ) (x a b : E) :
    hermE φ h x (a + b) = hermE φ h x a + hermE φ h x b := by
  simp only [hermE, map_add, add_mul, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermE, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ by ring`.
-/
theorem hermE_swap (φ : I → E →+* ℂ) (h : I → ℝ) (x x' : E) :
    hermE φ h x' x = starRingEnd ℂ (hermE φ h x x') := by
  simp only [hermE, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/- English proof (translation)
Simplify using `[hermE, Complex.im_sum]`.
-/
theorem hermE_one_im (φ : I → E →+* ℂ) (h : I → ℝ) (w : E) :
    (hermE φ h w 1).im = ∑ i, h i * (φ i w).im := by
  simp [hermE, Complex.im_sum]

end GlobalTheory.CMRiem

open GlobalTheory.CMRiem in

/- English proof (translation)
Introduce `E _ _ _ I _ φ hφ c y hc 𝔠 T`. Take `⟨χ, hAH⟩` from `T.U.ah`. Establish `hLB : (T.X.diag T.U.c).IsLB` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (T.X.isLB T.U.c) _`. Establish `hlatΛ : ∀ w, w ∈ T.U.u.Λ ↔ ∃ x ∈ lattice c y, w = fun j ↦ φ (T.U.e j) x`. Introduce `w`.

Rewrite using `[T.U.lat]`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]`. Establish `hH : ∀ x x', ((fun j ↦ φ (T.U.e j) x) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec (star fun j ↦ φ (T.U.e j) x')) = hermE φ T.U.h x x'`. Introduce `x x'`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hermE]`.

Rewrite using `[Equiv.sum_comp T.U.e (fun i ↦ φ i x * ((T.U.h i : ℂ) * star (φ i x')))]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ by simp only [Complex.star_def]; ring`. Establish `hint : ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, ∃ n : ℤ, (hermE φ T.U.h x x').im = n`. Introduce `x hx x' hx'`. Establish `hl : (fun j ↦ φ (T.U.e j) x) ∈ T.U.u.Λ` using `(hlatΛ _).2 ⟨x, hx, rfl⟩`.

Establish `hm : (fun j ↦ φ (T.U.e j) x') ∈ T.U.u.Λ` using `(hlatΛ _).2 ⟨x', hx', rfl⟩`. Establish `hs` using `exp_herm_swap T.U.u hLB hAH ⟨_, hl⟩ ⟨_, hm⟩`. Simplify using `only [hH] at hs`. Take `⟨n, hn⟩` from `Complex.exp_eq_exp_iff_exists_int.1 hs`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `him` using `congrArg Complex.im hn`. Rewrite `him` using `[hermE_swap φ T.U.h x x']`. Simplify using `at him`. Establish `hπ : Real.pi ≠ 0` using `Real.pi_ne_zero`. Establish `h2 : Real.pi * (2 * ((hermE φ T.U.h x x').im - n)) = 0` using `by linarith`.

Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 hπ`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hspan` using `span_eq_top_of_full φ hφ T.U.e (lattice c y) T.U.u.Λ T.U.u.full hlatΛ`. Set `Bf : E → E →+ ℝ` to `fun x' ↦ AddMonoidHom.mk' (fun x ↦ (hermE φ T.U.h x x').im) (fun a b ↦ by simp only [hermE_add_left, Complex.add_im])`.

Set `Cf : E → E →+ ℝ` to `fun x ↦ AddMonoidHom.mk' (fun x' ↦ (hermE φ T.U.h x x').im) (fun a b ↦ by simp only [hermE_add_right, Complex.add_im])`. Establish `hrat1 : ∀ x' ∈ lattice c y, ∀ x, ∃ q : ℚ, (hermE φ T.U.h x x').im = q` using `fun x' hx' x ↦ rat_of_span hspan (Bf x') (fun x hx ↦ by`. Take `⟨n, hn⟩` from `hint x hx x' hx'`. Conclude with `⟨n, by simp [Bf, hn]⟩) x`. Establish `hrat : ∀ x x', ∃ q : ℚ, (hermE φ T.U.h x x').im = q` using `fun x x' ↦ rat_of_span hspan (Cf x) (fun x' hx' ↦ hrat1 x' hx' x) x'`.

Use `choose q hq using fun w ↦ hrat w 1`. Set `f : Module.Dual ℚ E` to `{ toFun := q map_add' := fun a b ↦ Rat.cast_injective (α := ℝ) (by`. Rewrite using `[Rat.cast_add, ← hq, ← hq, ← hq]`. Conclude with `(Bf 1).map_add a b)`. Use the proof step `map_smul' := fun r a ↦ Rat.cast_injective (α := ℝ) (by`.

Rewrite using `[RingHom.id_apply, smul_eq_mul, Rat.cast_mul, ← hq, ← hq]`. Use `(Bf 1).toRatLinearMap.map_smul r a` as an intermediate fact. Simplify using `only [AddMonoidHom.coe_toRatLinearMap, Rat.smul_def] at this`. Rewrite using `[Rat.smul_def]`. Conclude with `this) }`.

Use `set β := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm f`. Establish `htr : ∀ w, Algebra.trace ℚ E (β * w) = q w` using `fun w ↦ by`. Rewrite using `[← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]`. Both sides reduce to the same expression. Set `gc : I ⊕ I → ℂ` to `Sum.elim (fun i ↦ φ i β + Complex.I * T.U.h i / 2) (fun i ↦ starRingEnd ℂ (φ i β) - Complex.I * T.U.h i / 2)`.

Establish `hrel : ∑ s, gc s • ((Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s : E → ℂ) = 0`. Use function extensionality and compare the values at `w`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, smul_eq_mul, NumberField.ComplexEmbedding.conjugate_coe_eq, Pi.zero_apply, gc]`. Establish `ht` using `trace_eq_sum_cm φ hφ (β * w)`. Rewrite `ht` using `[htr w]`.

Establish `hqw : ((q w : ℚ) : ℂ) = ∑ i, ((T.U.h i : ℂ) * ((φ i w).im : ℂ))`. Use `hq w` as an intermediate fact. Rewrite `this` using `[hermE_one_im]`. Rewrite using `[← Complex.ofReal_ratCast, ← this]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[← Finset.sum_add_distrib]`. Establish `hterm : ∀ i, (φ i β + Complex.I * T.U.h i / 2) * φ i w + (starRingEnd ℂ (φ i β) - Complex.I * T.U.h i / 2) * starRingEnd ℂ (φ i w) = (φ i (β * w) + starRingEnd ℂ (φ i (β * w))) - (T.U.h i : ℂ) * ((φ i w).im : ℂ)`. Introduce `i`. Establish `hz` using `Complex.sub_conj (φ i w)`.

Move the coercions through the operations in `at hz`. Rewrite using `[map_mul, map_mul]`. Take the linear combination `(Complex.I * T.U.h i / 2) * hz + ((T.U.h i : ℂ) * ((φ i w).im : ℂ)) * Complex.I_sq`. Rewrite using `[Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_sub_distrib, ← ht, ← hqw, sub_self]`. Use `⟨β, fun i ↦ ?_⟩` and prove the remaining obligations.

Establish `h0` using `Fintype.linearIndependent_iff.1 (cmEmb_linearIndependent φ hφ) gc hrel (Sum.inl i)`. Simplify using `only [gc, Sum.elim_inl] at h0`. Take the linear combination `(-2 * Complex.I) * h0 + (T.U.h i : ℂ) * Complex.I_sq`.
-/
theorem GlobalTheory.cmPoint_herm_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)),
      ∃ β : E, ∀ i, (T.U.h i : ℂ) = 2 * Complex.I * φ i β := by
  intro E _ _ _ I _ φ hφ c y hc 𝔠 T
  obtain ⟨χ, hAH⟩ := T.U.ah
  have hLB : (T.X.diag T.U.c).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (T.X.isLB T.U.c) _
  have hlatΛ : ∀ w, w ∈ T.U.u.Λ ↔ ∃ x ∈ lattice c y, w = fun j ↦ φ (T.U.e j) x := by
    intro w; rw [T.U.lat]; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hH : ∀ x x', ((fun j ↦ φ (T.U.e j) x) ⬝ᵥ (Matrix.diagonal fun j ↦ (T.U.h (T.U.e j) : ℂ)).mulVec
      (star fun j ↦ φ (T.U.e j) x')) = hermE φ T.U.h x x' := by
    intro x x'
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hermE]
    rw [Equiv.sum_comp T.U.e (fun i ↦ φ i x * ((T.U.h i : ℂ) * star (φ i x')))]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [Complex.star_def]; ring
  have hint : ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, ∃ n : ℤ, (hermE φ T.U.h x x').im = n := by
    intro x hx x' hx'
    have hl : (fun j ↦ φ (T.U.e j) x) ∈ T.U.u.Λ := (hlatΛ _).2 ⟨x, hx, rfl⟩
    have hm : (fun j ↦ φ (T.U.e j) x') ∈ T.U.u.Λ := (hlatΛ _).2 ⟨x', hx', rfl⟩
    have hs := exp_herm_swap T.U.u hLB hAH ⟨_, hl⟩ ⟨_, hm⟩
    simp only [hH] at hs
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hs
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    rw [hermE_swap φ T.U.h x x'] at him
    simp at him
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h2 : Real.pi * (2 * ((hermE φ T.U.h x x').im - n)) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hπ
    · linarith
  have hspan := span_eq_top_of_full φ hφ T.U.e (lattice c y) T.U.u.Λ T.U.u.full hlatΛ
  let Bf : E → E →+ ℝ := fun x' ↦ AddMonoidHom.mk' (fun x ↦ (hermE φ T.U.h x x').im)
    (fun a b ↦ by simp only [hermE_add_left, Complex.add_im])
  let Cf : E → E →+ ℝ := fun x ↦ AddMonoidHom.mk' (fun x' ↦ (hermE φ T.U.h x x').im)
    (fun a b ↦ by simp only [hermE_add_right, Complex.add_im])
  have hrat1 : ∀ x' ∈ lattice c y, ∀ x, ∃ q : ℚ, (hermE φ T.U.h x x').im = q := fun x' hx' x ↦
    rat_of_span hspan (Bf x') (fun x hx ↦ by
      obtain ⟨n, hn⟩ := hint x hx x' hx'
      exact ⟨n, by simp [Bf, hn]⟩) x
  have hrat : ∀ x x', ∃ q : ℚ, (hermE φ T.U.h x x').im = q := fun x x' ↦
    rat_of_span hspan (Cf x) (fun x' hx' ↦ hrat1 x' hx' x) x'
  choose q hq using fun w ↦ hrat w 1
  let f : Module.Dual ℚ E :=
    { toFun := q
      map_add' := fun a b ↦ Rat.cast_injective (α := ℝ) (by
        rw [Rat.cast_add, ← hq, ← hq, ← hq]; exact (Bf 1).map_add a b)
      map_smul' := fun r a ↦ Rat.cast_injective (α := ℝ) (by
        rw [RingHom.id_apply, smul_eq_mul, Rat.cast_mul, ← hq, ← hq]
        have := (Bf 1).toRatLinearMap.map_smul r a
        simp only [AddMonoidHom.coe_toRatLinearMap, Rat.smul_def] at this
        rw [Rat.smul_def]
        exact this) }
  set β := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm f
  have htr : ∀ w, Algebra.trace ℚ E (β * w) = q w := fun w ↦ by
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]; rfl
  let gc : I ⊕ I → ℂ := Sum.elim (fun i ↦ φ i β + Complex.I * T.U.h i / 2)
    (fun i ↦ starRingEnd ℂ (φ i β) - Complex.I * T.U.h i / 2)
  have hrel : ∑ s, gc s • ((Sum.elim φ fun i ↦ NumberField.ComplexEmbedding.conjugate (φ i)) s : E → ℂ) = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, smul_eq_mul,
      NumberField.ComplexEmbedding.conjugate_coe_eq, Pi.zero_apply, gc]
    have ht := trace_eq_sum_cm φ hφ (β * w)
    rw [htr w] at ht
    have hqw : ((q w : ℚ) : ℂ) = ∑ i, ((T.U.h i : ℂ) * ((φ i w).im : ℂ)) := by
      have := hq w
      rw [hermE_one_im] at this
      rw [← Complex.ofReal_ratCast, ← this]
      push_cast; rfl
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ i, (φ i β + Complex.I * T.U.h i / 2) * φ i w +
        (starRingEnd ℂ (φ i β) - Complex.I * T.U.h i / 2) * starRingEnd ℂ (φ i w) =
        (φ i (β * w) + starRingEnd ℂ (φ i (β * w))) - (T.U.h i : ℂ) * ((φ i w).im : ℂ) := by
      intro i
      have hz := Complex.sub_conj (φ i w)
      push_cast at hz
      rw [map_mul, map_mul]
      linear_combination (Complex.I * T.U.h i / 2) * hz + ((T.U.h i : ℂ) * ((φ i w).im : ℂ)) * Complex.I_sq
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_sub_distrib, ← ht, ← hqw, sub_self]
  refine ⟨β, fun i ↦ ?_⟩
  have h0 := Fintype.linearIndependent_iff.1 (cmEmb_linearIndependent φ hφ) gc hrel (Sum.inl i)
  simp only [gc, Sum.elim_inl] at h0
  linear_combination (-2 * Complex.I) * h0 + (T.U.h i : ℂ) * Complex.I_sq
