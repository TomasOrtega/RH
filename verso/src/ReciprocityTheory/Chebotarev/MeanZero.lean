import ReciprocityTheory.Chebotarev.DiscreteTopologyLatOf
import ReciprocityTheory.Chebotarev.NormCongr

open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite using `[Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]`. Establish `h2 : Nat.Coprime (Ideal.absNorm C) ((l * Ideal.absNorm B) * Ideal.absNorm B)` using `Nat.Coprime.mul_right hcop (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hcop)`. Take `⟨u, v, huv⟩ : IsCoprime (Ideal.absNorm C : ℤ) (((l * Ideal.absNorm B) * Ideal.absNorm B : ℕ) : ℤ)` from `Nat.isCoprime_iff_coprime.mpr h2`. Establish `hmem1 : ((l * Ideal.absNorm B : ℕ) : 𝓞 E) * ((Ideal.absNorm B : ℕ) : 𝓞 E) ∈ Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B` using `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.absNorm_mem B)`. Establish `hmem2 : ((Ideal.absNorm C : ℕ) : 𝓞 E) ∈ C` using `Ideal.absNorm_mem C`.

Establish `h1 : (1 : 𝓞 E) = (v : 𝓞 E) * (((l * Ideal.absNorm B : ℕ) : 𝓞 E) * ((Ideal.absNorm B : ℕ) : 𝓞 E)) + (u : 𝓞 E) * ((Ideal.absNorm C : ℕ) : 𝓞 E)`. Use `congrArg (Int.cast : ℤ → 𝓞 E) huv` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Take the linear combination `-this`. Rewrite using `[h1]`.

Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hmem1)) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hmem2))`.
-/
theorem isCoprime_span_mul_of_coprime_absNorm {l : ℕ} (B C : Ideal (𝓞 E))
    (hcop : Nat.Coprime (Ideal.absNorm C) (l * Ideal.absNorm B)) :
    IsCoprime (Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B) C := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have h2 : Nat.Coprime (Ideal.absNorm C) ((l * Ideal.absNorm B) * Ideal.absNorm B) :=
    Nat.Coprime.mul_right hcop (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hcop)
  obtain ⟨u, v, huv⟩ : IsCoprime (Ideal.absNorm C : ℤ)
      (((l * Ideal.absNorm B) * Ideal.absNorm B : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr h2
  have hmem1 : ((l * Ideal.absNorm B : ℕ) : 𝓞 E) * ((Ideal.absNorm B : ℕ) : 𝓞 E) ∈
      Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B :=
    Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.absNorm_mem B)
  have hmem2 : ((Ideal.absNorm C : ℕ) : 𝓞 E) ∈ C := Ideal.absNorm_mem C
  have h1 : (1 : 𝓞 E) = (v : 𝓞 E) * (((l * Ideal.absNorm B : ℕ) : 𝓞 E) * ((Ideal.absNorm B : ℕ) : 𝓞 E))
      + (u : 𝓞 E) * ((Ideal.absNorm C : ℕ) : 𝓞 E) := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) huv
    push_cast at this ⊢
    linear_combination -this
  rw [h1]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hmem1))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hmem2))

/- English proof (translation)
Use `set e := Ideal.quotientMulEquivQuotientProd I C hIC`. Establish `hfst : ∀ p, Ideal.Quotient.mk I (σ (e.symm p)) = p.1`. Introduce `p`. Use `congrArg Prod.fst (e.apply_symm_apply p)` as an intermediate fact. Rewrite `this` using `[← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]`.

Conclude with `this`. Establish `hsnd : ∀ p, Ideal.Quotient.mk C (σ (e.symm p)) = p.2`. Introduce `p`. Use `congrArg Prod.snd (e.apply_symm_apply p)` as an intermediate fact. Rewrite `this` using `[← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]`.

Conclude with `this`. Rewrite using `[← (e.symm.toEquiv).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_eq_zero fun u _ => ?_` and prove the remaining obligations. Establish `hfe : ∀ v, f (σ (e.symm (u, v))) = f (σ (e.symm (u, 0)))`. Introduce `v`.

Apply `hf` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq, hfst, hfst]`. Establish `hC : ∀ v, σ (e.symm (u, v)) ∈ C ↔ v = 0`. Introduce `v`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hsnd]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]`. Rewrite using `[hfe v]`. Simplify using `only [hC v]`. Use `_ = f (σ (e.symm (u, 0))) * ∑ v : R ⧸ C, (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) := by`.

Rewrite using `[Finset.mul_sum]`. Use `_ = 0 := by`. Simplify using `[Finset.sum_sub_distrib]`.
-/
theorem sum_crt_weight_eq_zero {R : Type*} [CommRing R] (I C : Ideal R) (hIC : IsCoprime I C)
    [Fintype (R ⧸ I * C)] [Fintype (R ⧸ I)] [Fintype (R ⧸ C)] (f : R → ℂ)
    (hf : ∀ a b, a - b ∈ I → f a = f b) (σ : R ⧸ I * C → R)
    (hσ : ∀ y, Ideal.Quotient.mk _ (σ y) = y) :
    ∑ y, f (σ y) * (1 - (Fintype.card (R ⧸ C) : ℂ) * if σ y ∈ C then 1 else 0) = 0 := by
  set e := Ideal.quotientMulEquivQuotientProd I C hIC
  have hfst : ∀ p, Ideal.Quotient.mk I (σ (e.symm p)) = p.1 := by
    intro p
    have := congrArg Prod.fst (e.apply_symm_apply p)
    rw [← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk] at this
    exact this
  have hsnd : ∀ p, Ideal.Quotient.mk C (σ (e.symm p)) = p.2 := by
    intro p
    have := congrArg Prod.snd (e.apply_symm_apply p)
    rw [← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk] at this
    exact this
  rw [← (e.symm.toEquiv).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun u _ => ?_
  have hfe : ∀ v, f (σ (e.symm (u, v))) = f (σ (e.symm (u, 0))) := by
    intro v
    apply hf
    rw [← Ideal.Quotient.eq, hfst, hfst]
  have hC : ∀ v, σ (e.symm (u, v)) ∈ C ↔ v = 0 := by
    intro v
    rw [← Ideal.Quotient.eq_zero_iff_mem, hsnd]
  calc ∑ v, f (σ (e.symm.toEquiv (u, v))) *
        (1 - (Fintype.card (R ⧸ C) : ℂ) * if σ (e.symm.toEquiv (u, v)) ∈ C then 1 else 0)
      = ∑ v : R ⧸ C, f (σ (e.symm (u, 0))) *
        (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) :=
        Finset.sum_congr rfl fun v _ => by
          simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
          rw [hfe v]
          simp only [hC v]
    _ = f (σ (e.symm (u, 0))) * ∑ v : R ⧸ C, (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) := by
        rw [Finset.mul_sum]
    _ = 0 := by
        simp [Finset.sum_sub_distrib]

/- English proof (translation)
Establish `hM : mbc l b.1 c.1 = Ideal.span {((l * Ideal.absNorm b.1 : ℕ) : 𝓞 E)} * b.1 * c.1` using `rfl`. Rewrite using `[hM]`. Take `⟨B, hB0⟩` from `b`. Take `⟨C, hC0⟩` from `c`. Simplify using `only at hcop ⊢`.

Use `set I : Ideal (𝓞 E) := Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B with hI`. Establish `hIC : IsCoprime I C` using `isCoprime_span_mul_of_coprime_absNorm B C hcop`. Establish `hIB : I ≤ B` using `Ideal.mul_le_right`. Establish `hIspan : I ≤ Ideal.span {((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E)}`. Establish `: ((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E) = ((l * Ideal.absNorm B : ℕ) : 𝓞 E)` using `by push_cast; rfl`.

Rewrite using `[this]`. Conclude with `Ideal.mul_le_left`. Establish `hMB : I * C ≤ B` using `le_trans Ideal.mul_le_left hIB`. Establish `hMBC : I * C ≤ B * C` using `Ideal.mul_mono_left hIB`. Establish `hBC : B * C = B ⊓ C` using `Ideal.mul_eq_inf_of_coprime (Ideal.isCoprime_iff_sup_eq.mp (hIC.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hIB)))`.

Establish `hl0 : (l * Ideal.absNorm B : ℕ) ≠ 0` using `Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`. Establish `hI0 : I ≠ ⊥`. Rewrite using `[hI, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]`. Conclude with `⟨by exact_mod_cast hl0, hB0⟩`. Establish `hM0 : I * C ≠ ⊥`.

Rewrite using `[Ne, Ideal.mul_eq_bot, not_or]`. Conclude with `⟨hI0, hC0⟩`. Use `Ideal.finiteQuotientOfFreeOfNeBot (I * C) hM0` as an intermediate fact. Use `Ideal.finiteQuotientOfFreeOfNeBot I hI0` as an intermediate fact. Use `Ideal.finiteQuotientOfFreeOfNeBot C hC0` as an intermediate fact.

Set `: Fintype (𝓞 E ⧸ I * C)` to `Fintype.ofFinite _`. Set `: Fintype (𝓞 E ⧸ I)` to `Fintype.ofFinite _`. Set `: Fintype (𝓞 E ⧸ C)` to `Fintype.ofFinite _`. Establish `hsurj : Function.Surjective (Ideal.Quotient.mk (I * C))` using `Ideal.Quotient.mk_surjective`. Take `⟨σ, hσ⟩ : ∃ σ : 𝓞 E ⧸ I * C → 𝓞 E, ∀ y, Ideal.Quotient.mk (I * C) (σ y) = y` from `⟨_, Function.surjInv_eq hsurj⟩`.

Establish `hσinj : Function.Injective σ` using `fun y₁ y₂ h => by rw [← hσ y₁, ← hσ y₂, h]`. Establish `hkey : ∀ y₁ y₂, σ y₁ - σ y₂ ∈ I * C → y₁ = y₂`. Introduce `y₁ y₂ h`. Rewrite using `[← hσ y₁, ← hσ y₂]`. Conclude with `Ideal.Quotient.eq.mpr h`.

Use `set F : 𝓞 E → ℂ := fun α => χ (((Algebra.norm ℤ α / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) * (1 - (Ideal.absNorm C : ℂ) * (if α ∈ B * C then 1 else 0)) with hF`. Establish `hcf : ∀ α, cfun χ B C (embZ α) = F α`. Introduce `α`. Simplify using `only [cfun, preZ_embZ, hF]`. Establish `hchi : ∀ a a', a ∈ B → a' ∈ B → a - a' ∈ I → χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) = χ (((Algebra.norm ℤ a' / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l)`.

Introduce `a a' ha ha' h`. Use `congr 1`. Conclude with `(ZMod.intCast_eq_intCast_iff _ _ _).mpr (norm_div_absNorm_modEq (l : ℤ) ha ha' (hIspan h))`. Establish `hper : ∀ μ ∈ I * C, ∀ a ∈ B, F (μ + a) = F a`. Introduce `μ hμ a ha`.

Simplify using `only [hF]`. Rewrite using `[hchi (μ + a) a (B.add_mem (hMB hμ) ha) ha (by rw [add_sub_cancel_right]; exact Ideal.mul_le_left hμ)]`. Simplify using `only [Ideal.add_mem_iff_right _ (hMBC hμ)]`. Use `set reps : Finset (mixedSpace E) := (Finset.univ.filter fun y => σ y ∈ B).image (fun y => embZ (σ y)) with hreps`. Establish `hmemreps : ∀ β ∈ reps, ∃ y, σ y ∈ B ∧ embZ (σ y) = β`.

Introduce `β hβ`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hβ`. Conclude with `⟨y, (Finset.mem_filter.mp hy).2, rfl⟩`. Use `⟨latOf_mono hMB, reps, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `β hβ`.

Take `⟨y, hy, rfl⟩` from `hmemreps β hβ`. Conclude with `mem_latOf.mpr ⟨_, hy, rfl⟩`. Introduce `α hα`. Take `⟨a, ha, rfl⟩` from `mem_latOf.mp hα`. Establish `hya : σ (Ideal.Quotient.mk _ a) - a ∈ I * C` using `Ideal.Quotient.eq.mp (hσ _)`.

Establish `hyB : σ (Ideal.Quotient.mk _ a) ∈ B`. Use `B.add_mem (hMB hya) ha` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Use `⟨embZ (a - σ (Ideal.Quotient.mk _ a)), mem_latOf.mpr ⟨_, ?_, rfl⟩, embZ (σ (Ideal.Quotient.mk _ a)), ?_, ?_⟩` and prove the remaining obligations. Use `(I * C).neg_mem hya` as an intermediate fact.

Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Conclude with `Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyB⟩, rfl⟩`. Rewrite using `[map_sub, sub_add_cancel]`. Introduce `β₁ h₁ β₂ h₂ hd`. Take `⟨y₁, -, rfl⟩` from `hmemreps β₁ h₁`.

Take `⟨y₂, -, rfl⟩` from `hmemreps β₂ h₂`. Take `⟨μ, hμ, hμe⟩` from `mem_latOf.mp hd`. Establish `: μ = σ y₁ - σ y₂` using `embZ_injective (by rw [hμe, map_sub])`. Rewrite using `[hkey y₁ y₂ (this ▸ hμ)]`. Introduce `l' hl' β hβ`.

Take `⟨y, hy, rfl⟩` from `hmemreps β hβ`. Take `⟨μ, hμ, rfl⟩` from `mem_latOf.mp hl'`. Rewrite using `[← map_add, hcf, hcf, hper μ hμ _ hy]`. Rewrite using `[hreps, Finset.sum_image (fun y₁ _ y₂ _ h => hσinj (embZ_injective h))]`. Simplify using `only [hcf]`.

Rewrite using `[Finset.sum_filter]`. Use `set f : 𝓞 E → ℂ := fun a => if a ∈ B then χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) else 0 with hf`. Establish `hfper : ∀ a a', a - a' ∈ I → f a = f a'`. Introduce `a a' h`. Establish `hiff : a ∈ B ↔ a' ∈ B`.

Establish `h'` using `hIB h`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Use `B.sub_mem ha h'` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Introduce `ha'`. Use `B.add_mem h' ha'` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Simplify using `only [hf]`. Distinguish the cases in `ha : a ∈ B`.

Rewrite using `[if_pos ha, if_pos (hiff.mp ha), hchi a a' ha (hiff.mp ha) h]`. Rewrite using `[if_neg ha, if_neg (fun h' => ha (hiff.mpr h'))]`. Establish `hcard : (Ideal.absNorm C : ℂ) = (Fintype.card (𝓞 E ⧸ C) : ℂ)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]`. Use `(Finset.sum_congr rfl fun y _ => ?_).trans (sum_crt_weight_eq_zero I C hIC f hfper σ hσ)` and prove the remaining obligations.

Distinguish the cases in `hy : σ y ∈ B`. Simplify using `only [hf, hF, ← hcard, if_pos hy, hBC, Ideal.mem_inf, hy, true_and, if_true]`. Simplify using `only [hf, if_neg hy, zero_mul]`.
-/
theorem exists_reps_meanZero {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    latOf (mbc l b.1 c.1) ≤ latOf b.1 ∧
    ∃ reps : Finset (mixedSpace E), (∀ β ∈ reps, β ∈ latOf b.1) ∧
      (∀ α ∈ latOf b.1, ∃ l' ∈ latOf (mbc l b.1 c.1), ∃ β ∈ reps, α = l' + β) ∧
      (∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ latOf (mbc l b.1 c.1) → β₁ = β₂) ∧
      (∀ l' ∈ latOf (mbc l b.1 c.1), ∀ β ∈ reps, cfun χ b.1 c.1 (l' + β) = cfun χ b.1 c.1 β) ∧
      ∑ β ∈ reps, cfun χ b.1 c.1 β = 0 := by
  have hM : mbc l b.1 c.1 = Ideal.span {((l * Ideal.absNorm b.1 : ℕ) : 𝓞 E)} * b.1 * c.1 := rfl
  rw [hM]
  obtain ⟨B, hB0⟩ := b
  obtain ⟨C, hC0⟩ := c
  simp only at hcop ⊢
  set I : Ideal (𝓞 E) := Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B with hI
  have hIC : IsCoprime I C := isCoprime_span_mul_of_coprime_absNorm B C hcop
  have hIB : I ≤ B := Ideal.mul_le_right
  have hIspan : I ≤ Ideal.span {((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E)} := by
    have : ((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E) = ((l * Ideal.absNorm B : ℕ) : 𝓞 E) := by
      push_cast; rfl
    rw [this]; exact Ideal.mul_le_left
  have hMB : I * C ≤ B := le_trans Ideal.mul_le_left hIB
  have hMBC : I * C ≤ B * C := Ideal.mul_mono_left hIB
  have hBC : B * C = B ⊓ C := Ideal.mul_eq_inf_of_coprime
    (Ideal.isCoprime_iff_sup_eq.mp (hIC.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hIB)))
  have hl0 : (l * Ideal.absNorm B : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨by exact_mod_cast hl0, hB0⟩
  have hM0 : I * C ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨hI0, hC0⟩
  have := Ideal.finiteQuotientOfFreeOfNeBot (I * C) hM0
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  have := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  let : Fintype (𝓞 E ⧸ I * C) := Fintype.ofFinite _
  let : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  let : Fintype (𝓞 E ⧸ C) := Fintype.ofFinite _
  have hsurj : Function.Surjective (Ideal.Quotient.mk (I * C)) := Ideal.Quotient.mk_surjective
  obtain ⟨σ, hσ⟩ : ∃ σ : 𝓞 E ⧸ I * C → 𝓞 E, ∀ y, Ideal.Quotient.mk (I * C) (σ y) = y :=
    ⟨_, Function.surjInv_eq hsurj⟩
  have hσinj : Function.Injective σ := fun y₁ y₂ h => by rw [← hσ y₁, ← hσ y₂, h]
  have hkey : ∀ y₁ y₂, σ y₁ - σ y₂ ∈ I * C → y₁ = y₂ := by
    intro y₁ y₂ h
    rw [← hσ y₁, ← hσ y₂]; exact Ideal.Quotient.eq.mpr h

  set F : 𝓞 E → ℂ := fun α => χ (((Algebra.norm ℤ α / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) *
    (1 - (Ideal.absNorm C : ℂ) * (if α ∈ B * C then 1 else 0)) with hF
  have hcf : ∀ α, cfun χ B C (embZ α) = F α := by
    intro α; simp only [cfun, preZ_embZ, hF]
  have hchi : ∀ a a', a ∈ B → a' ∈ B → a - a' ∈ I →
      χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) =
      χ (((Algebra.norm ℤ a' / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) := by
    intro a a' ha ha' h
    congr 1
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (norm_div_absNorm_modEq (l : ℤ) ha ha' (hIspan h))
  have hper : ∀ μ ∈ I * C, ∀ a ∈ B, F (μ + a) = F a := by
    intro μ hμ a ha
    simp only [hF]
    rw [hchi (μ + a) a (B.add_mem (hMB hμ) ha) ha (by rw [add_sub_cancel_right]; exact Ideal.mul_le_left hμ)]
    simp only [Ideal.add_mem_iff_right _ (hMBC hμ)]
  set reps : Finset (mixedSpace E) :=
    (Finset.univ.filter fun y => σ y ∈ B).image (fun y => embZ (σ y)) with hreps
  have hmemreps : ∀ β ∈ reps, ∃ y, σ y ∈ B ∧ embZ (σ y) = β := by
    intro β hβ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hβ
    exact ⟨y, (Finset.mem_filter.mp hy).2, rfl⟩
  refine ⟨latOf_mono hMB, reps, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨y, hy, rfl⟩ := hmemreps β hβ
    exact mem_latOf.mpr ⟨_, hy, rfl⟩
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := mem_latOf.mp hα
    have hya : σ (Ideal.Quotient.mk _ a) - a ∈ I * C := Ideal.Quotient.eq.mp (hσ _)
    have hyB : σ (Ideal.Quotient.mk _ a) ∈ B := by
      have := B.add_mem (hMB hya) ha
      rwa [sub_add_cancel] at this
    refine ⟨embZ (a - σ (Ideal.Quotient.mk _ a)), mem_latOf.mpr ⟨_, ?_, rfl⟩,
      embZ (σ (Ideal.Quotient.mk _ a)), ?_, ?_⟩
    · have := (I * C).neg_mem hya
      rwa [neg_sub] at this
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyB⟩, rfl⟩
    · rw [map_sub, sub_add_cancel]
  · intro β₁ h₁ β₂ h₂ hd
    obtain ⟨y₁, -, rfl⟩ := hmemreps β₁ h₁
    obtain ⟨y₂, -, rfl⟩ := hmemreps β₂ h₂
    obtain ⟨μ, hμ, hμe⟩ := mem_latOf.mp hd
    have : μ = σ y₁ - σ y₂ := embZ_injective (by rw [hμe, map_sub])
    rw [hkey y₁ y₂ (this ▸ hμ)]
  · intro l' hl' β hβ
    obtain ⟨y, hy, rfl⟩ := hmemreps β hβ
    obtain ⟨μ, hμ, rfl⟩ := mem_latOf.mp hl'
    rw [← map_add, hcf, hcf, hper μ hμ _ hy]
  · rw [hreps, Finset.sum_image (fun y₁ _ y₂ _ h => hσinj (embZ_injective h))]
    simp only [hcf]
    rw [Finset.sum_filter]
    set f : 𝓞 E → ℂ := fun a => if a ∈ B then
      χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) else 0 with hf
    have hfper : ∀ a a', a - a' ∈ I → f a = f a' := by
      intro a a' h
      have hiff : a ∈ B ↔ a' ∈ B := by
        have h' := hIB h
        constructor
        · intro ha; have := B.sub_mem ha h'; rwa [sub_sub_cancel] at this
        · intro ha'; have := B.add_mem h' ha'; rwa [sub_add_cancel] at this
      simp only [hf]
      by_cases ha : a ∈ B
      · rw [if_pos ha, if_pos (hiff.mp ha), hchi a a' ha (hiff.mp ha) h]
      · rw [if_neg ha, if_neg (fun h' => ha (hiff.mpr h'))]
    have hcard : (Ideal.absNorm C : ℂ) = (Fintype.card (𝓞 E ⧸ C) : ℂ) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    refine (Finset.sum_congr rfl fun y _ => ?_).trans (sum_crt_weight_eq_zero I C hIC f hfper σ hσ)
    by_cases hy : σ y ∈ B
    · simp only [hf, hF, ← hcard, if_pos hy, hBC, Ideal.mem_inf, hy, true_and, if_true]
    · simp only [hf, if_neg hy, zero_mul]

end ReciprocityTheory.Cheb
