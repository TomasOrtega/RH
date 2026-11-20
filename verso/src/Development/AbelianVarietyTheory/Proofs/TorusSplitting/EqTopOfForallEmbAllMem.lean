import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.CMLattice

noncomputable section

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
/- English proof (translation)
Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
lemma conjugate_conjugate (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

/- English proof (translation)
Rewrite using `[← Embeddings.card E ℂ]`. Establish `h1 : Ψ.card = Ψᶜ.card`. Use `Finset.card_bij' (fun τ _ => ComplexEmbedding.conjugate τ) (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ hτ`. Conclude with `Finset.mem_compl.2 ((h τ).1 hτ)`.

Introduce `τ hτ`. Use `(h _).2 ?_` and prove the remaining obligations. Rewrite using `[conjugate_conjugate]`. Conclude with `Finset.mem_compl.1 hτ`. Introduce `τ _`.

Conclude with `conjugate_conjugate τ`. Introduce `τ _`. Conclude with `conjugate_conjugate τ`. Rewrite using `[← Finset.card_add_card_compl Ψ, ← h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma finrank_eq_two_mul_card (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Module.finrank ℚ E = 2 * Ψ.card := by
  classical
  rw [← Embeddings.card E ℂ]
  have h1 : Ψ.card = Ψᶜ.card := by
    refine Finset.card_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
      (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_
    · intro τ hτ
      exact Finset.mem_compl.2 ((h τ).1 hτ)
    · intro τ hτ
      refine (h _).2 ?_
      rw [conjugate_conjugate]
      exact Finset.mem_compl.1 hτ
    · intro τ _; exact conjugate_conjugate τ
    · intro τ _; exact conjugate_conjugate τ
  rw [← Finset.card_add_card_compl Ψ, ← h1]; ring

/- English proof (translation)
Set `z : (E →+* ℂ) → ℂ` to `fun σ => if hσ : σ ∈ Ψ then y ⟨σ, hσ⟩ else if hσ' : ComplexEmbedding.conjugate σ ∈ Ψ then (starRingEnd ℂ) (y ⟨_, hσ'⟩) else 0`. Set `B` to `canonicalEmbedding.latticeBasis E`. Establish `hz : ∀ σ, z σ = ∑ i, B.repr z i * σ (integralBasis E i)`. Introduce `σ`. Use `conv_lhs => rw [← B.sum_repr z]`.

Simplify using `[B, canonicalEmbedding.latticeBasis_apply, Finset.sum_apply]`. Use `⟨fun i => (B.repr z i).re, fun τ => ?_⟩` and prove the remaining obligations. Establish `h1 : y τ = ∑ i, B.repr z i * τ.1 (integralBasis E i)`. Rewrite using `[← hz]`. Simplify using `[z, τ.2]`.

Establish `h2 : (starRingEnd ℂ) (y τ) = ∑ i, B.repr z i * (starRingEnd ℂ) (τ.1 (integralBasis E i))`. Use `hz (ComplexEmbedding.conjugate τ.1)` as an intermediate fact. Simplify using `only [ComplexEmbedding.conjugate_coe_eq] at this`. Rewrite using `[← this]`. Establish `h3` using `h τ.1 τ.2`.

Establish `h4 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1) ∈ Ψ`. Rewrite using `[conjugate_conjugate]`. Conclude with `τ.2`. Simplify using `only [z, dif_neg h3, dif_pos h4]`. Use `congr 2`.

Conclude with `Subtype.ext (conjugate_conjugate τ.1).symm`. Establish `h5 : y τ = ∑ i, (starRingEnd ℂ) (B.repr z i) * τ.1 (integralBasis E i)`. Use `congrArg (starRingEnd ℂ) h2` as an intermediate fact. Simplify `this` using `[map_sum]`. Establish `h6 : y τ = (y τ + y τ) / 2` using `by ring`.

Rewrite using `[h6]`. Use `nth_rewrite 1 [h1]`. Rewrite using `[h5, ← Finset.sum_add_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.re_eq_add_conj]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_real_combination (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ → ComplexEmbedding.conjugate τ ∉ Ψ) (y : Ψ → ℂ) :
    ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ,
      ∀ τ : Ψ, y τ = ∑ i, (c i : ℂ) * τ.1 (integralBasis E i) := by
  classical
  let z : (E →+* ℂ) → ℂ := fun σ =>
    if hσ : σ ∈ Ψ then y ⟨σ, hσ⟩
    else if hσ' : ComplexEmbedding.conjugate σ ∈ Ψ then (starRingEnd ℂ) (y ⟨_, hσ'⟩) else 0
  let B := canonicalEmbedding.latticeBasis E
  have hz : ∀ σ, z σ = ∑ i, B.repr z i * σ (integralBasis E i) := by
    intro σ
    conv_lhs => rw [← B.sum_repr z]
    simp [B, canonicalEmbedding.latticeBasis_apply, Finset.sum_apply]
  refine ⟨fun i => (B.repr z i).re, fun τ => ?_⟩
  have h1 : y τ = ∑ i, B.repr z i * τ.1 (integralBasis E i) := by
    rw [← hz]; simp [z, τ.2]
  have h2 : (starRingEnd ℂ) (y τ) =
      ∑ i, B.repr z i * (starRingEnd ℂ) (τ.1 (integralBasis E i)) := by
    have := hz (ComplexEmbedding.conjugate τ.1)
    simp only [ComplexEmbedding.conjugate_coe_eq] at this
    rw [← this]
    have h3 := h τ.1 τ.2
    have h4 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1) ∈ Ψ := by
      rw [conjugate_conjugate]; exact τ.2
    simp only [z, dif_neg h3, dif_pos h4]
    congr 2
    exact Subtype.ext (conjugate_conjugate τ.1).symm
  have h5 : y τ = ∑ i, (starRingEnd ℂ) (B.repr z i) * τ.1 (integralBasis E i) := by
    have := congrArg (starRingEnd ℂ) h2
    simpa [map_sum] using this
  have h6 : y τ = (y τ + y τ) / 2 := by ring
  rw [h6]
  nth_rewrite 1 [h1]
  rw [h5, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_eq_add_conj]; ring

def embAll (Ψ : Finset (E →+* ℂ)) (r : ℕ) : (Fin r → E) →ₗ[ℤ] (Ψ → Fin r → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun v τ a => τ.1 (v a)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma embAll_apply (Ψ : Finset (E →+* ℂ)) (r : ℕ) (v : Fin r → E) (τ : Ψ) (a : Fin r) :
    embAll Ψ r v τ a = τ.1 (v a) := rfl

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `y -`. Use `choose c hc using fun a : Fin r => exists_real_combination Ψ h (fun τ => y τ a)`. Establish `: y = ∑ a, ∑ i, c a i • embAll Ψ r (Pi.single a (integralBasis E i))`. Use extensionality with `τ a`.

Rewrite using `[hc a τ]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, embAll_apply]`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Pi.single_eq_of_ne' hb]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `S.sum_mem fun a _ => S.sum_mem fun i _ => S.smul_mem _ (hS _)`.
-/
lemma eq_top_of_forall_embAll_mem (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ → ComplexEmbedding.conjugate τ ∉ Ψ) (r : ℕ)
    (S : Submodule ℝ (Ψ → Fin r → ℂ)) (hS : ∀ v, embAll Ψ r v ∈ S) : S = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro y -
  choose c hc using fun a : Fin r => exists_real_combination Ψ h (fun τ => y τ a)
  have : y = ∑ a, ∑ i, c a i • embAll Ψ r (Pi.single a (integralBasis E i)) := by
    ext τ a
    rw [hc a τ]
    simp only [Finset.sum_apply, Pi.smul_apply, embAll_apply]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne' hb]
    · simp
  rw [this]
  exact S.sum_mem fun a _ => S.sum_mem fun i _ => S.smul_mem _ (hS _)

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (Λ : Set (Fin r → E))` using `hΛ ▸ Submodule.mem_top`. Establish `key : ∀ e : E, embAll Ψ r (e • v) ∈ S`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Introduce `e`.

Establish `: embAll Ψ r (e • x) = ∑ i, (((integralBasis E).repr e i : ℚ) : ℝ) • embAll Ψ r ((RingOfIntegers.basis E i) • x)`. Use extensionality with `τ a`. Use `conv_lhs => rw [← (integralBasis E).sum_repr e]`. Simplify using `[Finset.sum_apply, Finset.sum_mul, integralBasis_apply, Rat.smul_def, mul_assoc, Algebra.smul_def]`. Rewrite using `[this]`.

Conclude with `S.sum_mem fun i _ => S.smul_mem _ (hS _ (Λ.smul_mem _ hx))`. Consider the case `zero => intro e`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro e`. Rewrite using `[smul_add, map_add]`.

Conclude with `S.add_mem (hx e) (hy e)`. Consider the case `smul a x _ hx => intro e`. Rewrite using `[smul_smul]`. Conclude with `hx _`. Simplify using `using key 1`.
-/
lemma embAll_mem_of_span (Ψ : Finset (E →+* ℂ)) (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (S : Submodule ℝ (Ψ → Fin r → ℂ)) (hS : ∀ v ∈ Λ, embAll Ψ r v ∈ S) (v : Fin r → E) :
    embAll Ψ r v ∈ S := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := hΛ ▸ Submodule.mem_top
  have key : ∀ e : E, embAll Ψ r (e • v) ∈ S := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
      intro e
      have : embAll Ψ r (e • x) = ∑ i, (((integralBasis E).repr e i : ℚ) : ℝ) •
          embAll Ψ r ((RingOfIntegers.basis E i) • x) := by
        ext τ a
        conv_lhs => rw [← (integralBasis E).sum_repr e]
        simp [Finset.sum_apply, Finset.sum_mul, integralBasis_apply, Rat.smul_def, mul_assoc,
          Algebra.smul_def]
      rw [this]
      exact S.sum_mem fun i _ => S.smul_mem _ (hS _ (Λ.smul_mem _ hx))
    | zero => intro e; simp
    | add x y _ _ hx hy => intro e; rw [smul_add, map_add]; exact S.add_mem (hx e) (hy e)
    | smul a x _ hx => intro e; rw [smul_smul]; exact hx _
  simpa using key 1

/- English proof (translation)
Set `L : Submodule ℤ (Fin r → E)` to `Λ.restrictScalars ℤ`. Use `haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg`. Use `haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ`. Use `haveI : Module.Finite ℤ L := inferInstanceAs (Module.Finite ℤ Λ)`. Use `haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'`.

Set `c` to `Module.Free.chooseBasis ℤ L`. Set `w : Module.Free.ChooseBasisIndex ℤ L → (Fin r → E)` to `fun i => (c i : Fin r → E)`. Establish `hw : Submodule.span ℤ (Set.range w) = L`. Establish `: Set.range w = L.subtype '' Set.range c`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, c.span_eq, Submodule.map_subtype_top]`. Establish `hli : LinearIndependent ℤ w` using `c.linearIndependent.map' L.subtype L.ker_subtype`. Establish `hliQ : LinearIndependent ℚ w` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 hli`. Establish `hle : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) ≤ 2 * (Ψ.card * r)`.

Use `hliQ.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Module.finrank_pi_fintype, Finset.sum_const, finrank_eq_two_mul_card Ψ h]`. Simplify using `only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this`. Combine the equalities or inequalities in the displayed calculation. Establish `hZ : Submodule.span ℤ (Set.range (embAll Ψ r ∘ w)) = L.map (embAll Ψ r)`.

Rewrite using `[Set.range_comp, ← Submodule.map_span, hw]`. Establish `htop : Submodule.span ℝ (Set.range (embAll Ψ r ∘ w)) = ⊤`. Use `eq_top_of_forall_embAll_mem Ψ (fun τ => (h τ).1) r _ (embAll_mem_of_span Ψ r Λ hΛ _ fun v hv => ?_)` and prove the remaining obligations. Establish `: embAll Ψ r v ∈ Submodule.span ℤ (Set.range (embAll Ψ r ∘ w))`. Rewrite using `[hZ]`.

Conclude with `Submodule.mem_map_of_mem hv`. Conclude with `Submodule.span_subset_span ℤ ℝ _ this`. Establish `hfr : Module.finrank ℝ (Ψ → Fin r → ℂ) = 2 * (Ψ.card * r)`. Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hge : 2 * (Ψ.card * r) ≤ Fintype.card (Module.Free.ChooseBasisIndex ℤ L)`. Rewrite using `[← hfr, ← finrank_top, ← htop]`. Conclude with `finrank_range_le_card _`. Establish `hcard` using `le_antisymm hle hge`. Set `b` to `basisOfTopLeSpanOfCardEqFinrank (embAll Ψ r ∘ w) htop.ge (hcard.trans hfr.symm)`.

Use `⟨b.reindex (Fintype.equivFinOfCardEq hcard), fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.range_reindex, coe_basisOfTopLeSpanOfCardEqFinrank, hZ]`. Both sides reduce to the same expression.
-/
theorem exists_basis_of_cmType (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ b : Module.Basis (Fin (2 * (Ψ.card * r))) ℝ (Ψ → Fin r → ℂ),
      ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ ∃ v ∈ Λ, embAll Ψ r v = y := by
  classical
  let L : Submodule ℤ (Fin r → E) := Λ.restrictScalars ℤ
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  haveI : Module.Finite ℤ L := inferInstanceAs (Module.Finite ℤ Λ)
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let c := Module.Free.chooseBasis ℤ L
  let w : Module.Free.ChooseBasisIndex ℤ L → (Fin r → E) := fun i => (c i : Fin r → E)
  have hw : Submodule.span ℤ (Set.range w) = L := by
    have : Set.range w = L.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, c.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent ℤ w := c.linearIndependent.map' L.subtype L.ker_subtype
  have hliQ : LinearIndependent ℚ w := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hle : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) ≤ 2 * (Ψ.card * r) := by
    have := hliQ.fintype_card_le_finrank
    rw [Module.finrank_pi_fintype, Finset.sum_const, finrank_eq_two_mul_card Ψ h] at this
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hZ : Submodule.span ℤ (Set.range (embAll Ψ r ∘ w)) = L.map (embAll Ψ r) := by
    rw [Set.range_comp, ← Submodule.map_span, hw]
  have htop : Submodule.span ℝ (Set.range (embAll Ψ r ∘ w)) = ⊤ := by
    refine eq_top_of_forall_embAll_mem Ψ (fun τ => (h τ).1) r _
      (embAll_mem_of_span Ψ r Λ hΛ _ fun v hv => ?_)
    have : embAll Ψ r v ∈ Submodule.span ℤ (Set.range (embAll Ψ r ∘ w)) := by
      rw [hZ]; exact Submodule.mem_map_of_mem hv
    exact Submodule.span_subset_span ℤ ℝ _ this
  have hfr : Module.finrank ℝ (Ψ → Fin r → ℂ) = 2 * (Ψ.card * r) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have hge : 2 * (Ψ.card * r) ≤ Fintype.card (Module.Free.ChooseBasisIndex ℤ L) := by
    rw [← hfr, ← finrank_top, ← htop]
    exact finrank_range_le_card _
  have hcard := le_antisymm hle hge
  let b := basisOfTopLeSpanOfCardEqFinrank (embAll Ψ r ∘ w) htop.ge (hcard.trans hfr.symm)
  refine ⟨b.reindex (Fintype.equivFinOfCardEq hcard), fun y => ?_⟩
  rw [Module.Basis.range_reindex, coe_basisOfTopLeSpanOfCardEqFinrank, hZ]
  rfl

/- English proof (translation)
The claim follows from `exists_basis_of_cmType X.Ψ X.cmType r X.Λ X.Λ_fg X.Λ_span`.
-/
theorem exists_basis_lattice (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) :
    ∃ b : Module.Basis (Fin (2 * (X.Ψ.card * r))) ℝ (X.Ψ → Fin r → ℂ),
      ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔
        ∃ v ∈ X.Λ, (fun τ : X.Ψ => Data.emb τ.1 v) = y :=
  exists_basis_of_cmType X.Ψ X.cmType r X.Λ X.Λ_fg X.Λ_span

end

end GlobalTheory.CMLattice
