import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKer
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerSmulLe

open Finset

noncomputable section

namespace Formalism.NG

namespace ColKerChi

open ColumnGeneratorDecomposition

variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}
  {M : Type*} [AddCommGroup M] [Module A M]

/- English proof (translation)
Establish `h0 : ψ ((0 : Ymod r χ E), 0) = 0` using `map_zero ψ`. Rewrite using `[map_colGenJ]`. Simplify using `[h0]`.
-/
lemma map_nuRel (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (l : ι) (t : A) :
    ψ (colGenJ 0 l t 0 0) = t • ψ (fNu l) := by
  have h0 : ψ ((0 : Ymod r χ E), 0) = 0 := map_zero ψ
  rw [map_colGenJ]
  simp [h0]

end ColKerChi

open ColumnGeneratorDecomposition ColKerChi

/- English proof (translation)
Introduce `O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ D j Kc k0 he₁ hE hk0 hδ`. Set `K` to `kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0`. Set `q : ColFreeJ A r χ E ι j →ₗ[A] ColNNJ r χ E e₁ δ D j Kc k0` to `Submodule.mkQ _`. Establish `hval : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) (z : ColFreeJ A r χ E ι j), z ∈ colRelJ r χ E e₁ δ D j Kc k0 → (φ ∘ₗ q) z = 0` using `fun φ z hz => by`. Rewrite using `[LinearMap.comp_apply, show q z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]`.

Establish `hKY : ∀ φ ∈ K, ∀ y : Ymod r χ E, φ (q (y, 0)) = 0` using `fun φ hφ y => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hφ y)`. Establish `hσ : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l a, φ (q (fSig l a)) = 0`. Introduce `φ l a`. Establish `h` using `hval φ (colGenJ 0 l 0 (Pi.single a (1 - e₁)) 0) (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))`. Rewrite `h` using `[map_sigRel, sub_smul, one_smul, he₁, sub_zero]`.

Conclude with `h`. Establish `hσ0 : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l, φ (q (fSig0 l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)`. Introduce `φ l`. Establish `h` using `hval φ (colGenJ 0 l 0 0 (algebraMap T' A δ - E)) (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))`. Rewrite `h` using `[map_sig0Rel, sub_smul, hδ, hE, sub_zero]`.

Rewrite using `[LinearMap.mem_ker, DistribSMul.toLinearMap_apply]`. Conclude with `h`. Establish `hν : ∀ φ ∈ K, ∀ l, φ (q (fNu l)) ∈ LinearMap.ker (colDO (O` using `O) (M := d → KO O) r χ (D l)) := by`. Introduce `φ hφ l`. Rewrite using `[LinearMap.mem_ker]`.

Use function extensionality and compare the values at `g`. Establish `h` using `hval φ _ (Submodule.subset_span (Or.inr ⟨l, g, g.2, rfl⟩))`. Rewrite `h` using `[map_colGenJ]`. Take `⟨b, hb⟩` from `hk0 l g`. Simplify using `only [LinearMap.comp_apply, hKY φ hφ, hσ φ, zero_add, hb, neg_smul, mul_smul, hE, smul_zero, neg_zero, add_zero, Finset.sum_const_zero] at h`.

Use `show ((((χ g)⁻¹ : T'ˣ) : T') • r g) • φ (q (fNu l)) - φ (q (fNu l)) = 0`. Rewrite `h` using `[sub_smul, one_smul]`. Conclude with `h`. Set `evK : ColNNJ r χ E e₁ δ D j Kc k0 → (K →ₗ[O] (d → KO O))` to `fun x => evalO x ∘ₗ K.subtype`. Set `Φ : K →ₗ[O] ((l : ι) → LinearMap.ker (colDO (O` to `O) (M := d → KO O) r χ (D l)) × LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) := LinearMap.pi fun l => (LinearMap.codRestrict _ (evK (q (fNu l))) (fun φ => hν φ.1 φ.2 l)).prod (LinearMap.codRestrict _ (evK (q (fSig0 l))) (fun φ => hσ0 φ.1 l))`.

Establish `hΦ : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `φ h`. Establish `h1 : ∀ l, φ.1 (q (fNu l)) = 0` using `fun l => congrArg Subtype.val (congrArg Prod.fst (congrFun h l))`. Establish `h2 : ∀ l, φ.1 (q (fSig0 l)) = 0` using `fun l => congrArg Subtype.val (congrArg Prod.snd (congrFun h l))`.

Conclude with `Subtype.ext (eq_zero_of_gens φ.1 (hKY φ.1 φ.2) h1 (hσ φ.1) h2)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Module.length_pi_of_fintype]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Module.length_prod, KernelLengthBounds.length_ker_smul_pi]`.

Use `_ = _ := by`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]`.
-/
theorem colKerChiC : StatColKerChiC := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ D j Kc k0 he₁ hE hk0 hδ
  let K := kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0
  let q : ColFreeJ A r χ E ι j →ₗ[A] ColNNJ r χ E e₁ δ D j Kc k0 := Submodule.mkQ _
  have hval : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) (z : ColFreeJ A r χ E ι j),
      z ∈ colRelJ r χ E e₁ δ D j Kc k0 → (φ ∘ₗ q) z = 0 := fun φ z hz => by
    rw [LinearMap.comp_apply, show q z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  have hKY : ∀ φ ∈ K, ∀ y : Ymod r χ E, φ (q (y, 0)) = 0 := fun φ hφ y =>
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hφ y)
  have hσ : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l a, φ (q (fSig l a)) = 0 := by
    intro φ l a
    have h := hval φ (colGenJ 0 l 0 (Pi.single a (1 - e₁)) 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))
    rw [map_sigRel, sub_smul, one_smul, he₁, sub_zero] at h
    exact h
  have hσ0 : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l,
      φ (q (fSig0 l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO) := by
    intro φ l
    have h := hval φ (colGenJ 0 l 0 0 (algebraMap T' A δ - E))
      (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))
    rw [map_sig0Rel, sub_smul, hδ, hE, sub_zero] at h
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
    exact h
  have hν : ∀ φ ∈ K, ∀ l, φ (q (fNu l)) ∈
      LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)) := by
    intro φ hφ l
    rw [LinearMap.mem_ker]
    funext g
    have h := hval φ _ (Submodule.subset_span (Or.inr ⟨l, g, g.2, rfl⟩))
    rw [map_colGenJ] at h
    obtain ⟨b, hb⟩ := hk0 l g
    simp only [LinearMap.comp_apply, hKY φ hφ, hσ φ, zero_add, hb, neg_smul, mul_smul, hE,
      smul_zero, neg_zero, add_zero, Finset.sum_const_zero] at h
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g) • φ (q (fNu l)) - φ (q (fNu l)) = 0
    rw [sub_smul, one_smul] at h
    exact h
  let evK : ColNNJ r χ E e₁ δ D j Kc k0 → (K →ₗ[O] (d → KO O)) := fun x => evalO x ∘ₗ K.subtype
  let Φ : K →ₗ[O] ((l : ι) → LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)) ×
      LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) :=
    LinearMap.pi fun l =>
      (LinearMap.codRestrict _ (evK (q (fNu l))) (fun φ => hν φ.1 φ.2 l)).prod
        (LinearMap.codRestrict _ (evK (q (fSig0 l))) (fun φ => hσ0 φ.1 l))
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ h
    have h1 : ∀ l, φ.1 (q (fNu l)) = 0 := fun l =>
      congrArg Subtype.val (congrArg Prod.fst (congrFun h l))
    have h2 : ∀ l, φ.1 (q (fSig0 l)) = 0 := fun l =>
      congrArg Subtype.val (congrArg Prod.snd (congrFun h l))
    exact Subtype.ext (eq_zero_of_gens φ.1 (hKY φ.1 φ.2) h1 (hσ φ.1) h2)
  calc Module.length O K
      ≤ Module.length O ((l : ι) → LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)) ×
          LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) :=
        Module.length_le_of_injective Φ hΦ
    _ = ∑ l, (Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l))) +
          (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO) := by
        rw [Module.length_pi_of_fintype]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Module.length_prod, KernelLengthBounds.length_ker_smul_pi]
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_assoc]

/- English proof (translation)
Introduce `O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ D j Kc k0 ℓ e' hu he₁ hE hδ hk`. Set `K` to `kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0`. Set `q : ColFreeJ A r χ E ι j →ₗ[A] ColNNJ r χ E e₁ δ D j Kc k0` to `Submodule.mkQ _`. Establish `hval : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) (z : ColFreeJ A r χ E ι j), z ∈ colRelJ r χ E e₁ δ D j Kc k0 → (φ ∘ₗ q) z = 0` using `fun φ z hz => by`. Rewrite using `[LinearMap.comp_apply, show q z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]`.

Establish `hKY : ∀ φ ∈ K, ∀ y : Ymod r χ E, φ (q (y, 0)) = 0` using `fun φ hφ y => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hφ y)`. Establish `hσ : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l a, φ (q (fSig l a)) = 0`. Introduce `φ l a`. Establish `h` using `hval φ (colGenJ 0 l 0 (Pi.single a (1 - e₁)) 0) (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))`. Rewrite `h` using `[map_sigRel, sub_smul, one_smul, he₁, sub_zero]`.

Conclude with `h`. Establish `hν : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l, φ (q (fNu l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)`. Introduce `φ l`. Establish `h` using `hval φ (colGenJ 0 l E 0 0) (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))))`. Rewrite `h` using `[map_nuRel, hE]`.

Rewrite using `[LinearMap.mem_ker, DistribSMul.toLinearMap_apply]`. Conclude with `h`. Establish `hσ0 : ∀ φ ∈ K, ∀ l, φ (q (fSig0 l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) ((ℓ : O) ^ e' l * δO * δO))`. Introduce `φ hφ l`. Take `⟨g, hgD, c, hc, hkc⟩` from `hk l`.

Establish `h` using `hval φ _ (Submodule.subset_span (Or.inr ⟨l, g, hgD, rfl⟩))`. Rewrite `h` using `[map_colGenJ]`. Establish `hu' : ((((χ g)⁻¹ : T'ˣ) : T') • r g) • φ (q (fNu l)) = φ (q (fNu l))` using `hu g _`. Simplify using `only [LinearMap.comp_apply, hKY φ hφ, hσ φ, zero_add, sub_smul, one_smul, hu', sub_self, neg_smul, mul_smul, hkc, hδ, smul_zero, Finset.sum_const_zero, add_zero, neg_eq_zero] at h`. Rewrite using `[LinearMap.mem_ker, DistribSMul.toLinearMap_apply]`.

Establish `key : c • (((ℓ : O) ^ e' l * δO * δO) • φ (q (fSig0 l))) = 0`. Rewrite using `[smul_smul, show c * ((ℓ : O) ^ e' l * δO * δO) = δO * ((ℓ : O) ^ e' l * δO * c) by ring]`. Simplify `h` using `only [mul_smul]`. Conclude with `hc.smul_eq_zero.mp key`. Set `evK : ColNNJ r χ E e₁ δ D j Kc k0 → (K →ₗ[O] (d → KO O))` to `fun x => evalO x ∘ₗ K.subtype`.

Set `Φ : K →ₗ[O] ((l : ι) → LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) ((ℓ : O) ^ e' l * δO * δO)) × LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO))` to `LinearMap.pi fun l => (LinearMap.codRestrict _ (evK (q (fSig0 l))) (fun φ => hσ0 φ.1 φ.2 l)).prod (LinearMap.codRestrict _ (evK (q (fNu l))) (fun φ => hν φ.1 l))`. Establish `hΦ : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `φ h`. Establish `h1 : ∀ l, φ.1 (q (fSig0 l)) = 0` using `fun l => congrArg Subtype.val (congrArg Prod.fst (congrFun h l))`.

Establish `h2 : ∀ l, φ.1 (q (fNu l)) = 0` using `fun l => congrArg Subtype.val (congrArg Prod.snd (congrFun h l))`. Conclude with `Subtype.ext (eq_zero_of_gens φ.1 (hKY φ.1 φ.2) h2 (hσ φ.1) h1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Module.length_pi_of_fintype]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Module.length_prod, KernelLengthBounds.length_ker_smul_pi, KernelLengthBounds.length_ker_smul_pi, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, ← IdempotentNormalFormsLenFacts.length_quot_span (ℓ : O), nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]`.
-/
theorem colKerChiOne : StatColKerChiOne := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ D j Kc k0 ℓ e' hu he₁ hE hδ hk
  let K := kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0
  let q : ColFreeJ A r χ E ι j →ₗ[A] ColNNJ r χ E e₁ δ D j Kc k0 := Submodule.mkQ _
  have hval : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) (z : ColFreeJ A r χ E ι j),
      z ∈ colRelJ r χ E e₁ δ D j Kc k0 → (φ ∘ₗ q) z = 0 := fun φ z hz => by
    rw [LinearMap.comp_apply, show q z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  have hKY : ∀ φ ∈ K, ∀ y : Ymod r χ E, φ (q (y, 0)) = 0 := fun φ hφ y =>
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hφ y)
  have hσ : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l a, φ (q (fSig l a)) = 0 := by
    intro φ l a
    have h := hval φ (colGenJ 0 l 0 (Pi.single a (1 - e₁)) 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))
    rw [map_sigRel, sub_smul, one_smul, he₁, sub_zero] at h
    exact h
  have hν : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l,
      φ (q (fNu l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO) := by
    intro φ l
    have h := hval φ (colGenJ 0 l E 0 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))))
    rw [map_nuRel, hE] at h
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
    exact h
  have hσ0 : ∀ φ ∈ K, ∀ l, φ (q (fSig0 l)) ∈ LinearMap.ker
      (DistribSMul.toLinearMap O (d → KO O) ((ℓ : O) ^ e' l * δO * δO)) := by
    intro φ hφ l
    obtain ⟨g, hgD, c, hc, hkc⟩ := hk l
    have h := hval φ _ (Submodule.subset_span (Or.inr ⟨l, g, hgD, rfl⟩))
    rw [map_colGenJ] at h
    have hu' : ((((χ g)⁻¹ : T'ˣ) : T') • r g) • φ (q (fNu l)) = φ (q (fNu l)) := hu g _
    simp only [LinearMap.comp_apply, hKY φ hφ, hσ φ, zero_add, sub_smul, one_smul, hu', sub_self,
      neg_smul, mul_smul, hkc, hδ, smul_zero, Finset.sum_const_zero, add_zero,
      neg_eq_zero] at h
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
    have key : c • (((ℓ : O) ^ e' l * δO * δO) • φ (q (fSig0 l))) = 0 := by
      rw [smul_smul, show c * ((ℓ : O) ^ e' l * δO * δO) = δO * ((ℓ : O) ^ e' l * δO * c) by ring]
      simpa only [mul_smul] using h
    exact hc.smul_eq_zero.mp key
  let evK : ColNNJ r χ E e₁ δ D j Kc k0 → (K →ₗ[O] (d → KO O)) := fun x => evalO x ∘ₗ K.subtype
  let Φ : K →ₗ[O] ((l : ι) →
      LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) ((ℓ : O) ^ e' l * δO * δO)) ×
      LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) :=
    LinearMap.pi fun l =>
      (LinearMap.codRestrict _ (evK (q (fSig0 l))) (fun φ => hσ0 φ.1 φ.2 l)).prod
        (LinearMap.codRestrict _ (evK (q (fNu l))) (fun φ => hν φ.1 l))
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ h
    have h1 : ∀ l, φ.1 (q (fSig0 l)) = 0 := fun l =>
      congrArg Subtype.val (congrArg Prod.fst (congrFun h l))
    have h2 : ∀ l, φ.1 (q (fNu l)) = 0 := fun l =>
      congrArg Subtype.val (congrArg Prod.snd (congrFun h l))
    exact Subtype.ext (eq_zero_of_gens φ.1 (hKY φ.1 φ.2) h2 (hσ φ.1) h1)
  calc Module.length O K
      ≤ Module.length O ((l : ι) →
          LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) ((ℓ : O) ^ e' l * δO * δO)) ×
          LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) :=
        Module.length_le_of_injective Φ hΦ
    _ = ∑ l, ((Fintype.card d : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' l : ℕ∞) +
          2 * IsDiscreteValuationRing.addVal O δO) +
          (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO) := by
        rw [Module.length_pi_of_fintype]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Module.length_prod, KernelLengthBounds.length_ker_smul_pi, KernelLengthBounds.length_ker_smul_pi,
          AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow,
          ← IdempotentNormalFormsLenFacts.length_quot_span (ℓ : O), nsmul_eq_mul]
        ring
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_assoc]

end Formalism.NG
