import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.GalMean

open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

/- English proof (translation)
Use `set R : IntermediateField ℚ ℂ := φK.toRatAlgHom.fieldRange`. Use `set A : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({a, b} : Set ℂ)`. Establish `h1 : FiniteDimensional ℚ R` using `(AlgEquiv.ofInjectiveField φK.toRatAlgHom).toLinearEquiv.finiteDimensional`. Establish `h2 : FiniteDimensional ℚ A`. Use `IntermediateField.finiteDimensional_adjoin fun x hx => ?_` and prove the remaining obligations.

Break down `hx with rfl | hx` into its components or cases. Conclude with `ha.isIntegral`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `hb.isIntegral`. Use `set M : IntermediateField ℚ ℂ := R ⊔ A`.

Establish `: FiniteDimensional ℚ M` using `IntermediateField.finiteDimensional_sup _ _`. Establish `hn : IsNormalClosure ℚ M (IntermediateField.normalClosure ℚ M ℂ)` using `Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)`. Establish `: Normal ℚ (IntermediateField.normalClosure ℚ M ℂ)` using `hn.normal`. Establish `hle : M ≤ IntermediateField.normalClosure ℚ M ℂ` using `IntermediateField.le_normalClosure M`. Establish `hR : R ≤ M` using `le_sup_left`.

Establish `hA : A ≤ M` using `le_sup_right`. Use `⟨_, inferInstance, {}, fun x => hle (hR ⟨x, rfl⟩), hle (hA (IntermediateField.subset_adjoin ℚ _ (by simp))), hle (hA (IntermediateField.subset_adjoin ℚ _ (by simp)))⟩` and prove the remaining obligations.
-/
theorem exists_field {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (a b : ℂ)
    (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) :
    ∃ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L ∧ IsGalois ℚ L ∧ (∀ x : K, φK x ∈ L) ∧ a ∈ L ∧ b ∈ L := by
  set R : IntermediateField ℚ ℂ := φK.toRatAlgHom.fieldRange
  set A : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({a, b} : Set ℂ)
  have h1 : FiniteDimensional ℚ R :=
    (AlgEquiv.ofInjectiveField φK.toRatAlgHom).toLinearEquiv.finiteDimensional
  have h2 : FiniteDimensional ℚ A := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    rcases hx with rfl | hx
    · exact ha.isIntegral
    · rw [Set.mem_singleton_iff.1 hx]; exact hb.isIntegral
  set M : IntermediateField ℚ ℂ := R ⊔ A
  have : FiniteDimensional ℚ M := IntermediateField.finiteDimensional_sup _ _
  have hn : IsNormalClosure ℚ M (IntermediateField.normalClosure ℚ M ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun x => IsAlgClosed.splits _)
  have : Normal ℚ (IntermediateField.normalClosure ℚ M ℂ) := hn.normal
  have hle : M ≤ IntermediateField.normalClosure ℚ M ℂ := IntermediateField.le_normalClosure M
  have hR : R ≤ M := le_sup_left
  have hA : A ≤ M := le_sup_right
  refine ⟨_, inferInstance, {}, fun x => hle (hR ⟨x, rfl⟩), hle (hA (IntermediateField.subset_adjoin ℚ _ (by simp))),
    hle (hA (IntermediateField.subset_adjoin ℚ _ (by simp)))⟩

open IntermediateField in

/- English proof (translation)
Use `set b : L := ⟨β, hβ⟩`. Establish `hint : IsIntegral ℚ b` using `.of_finite ℚ b`. Establish `hmin : minpoly ℚ b = minpoly ℚ β`. Use `minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ L ℂ) Subtype.val_injective b` as an intermediate fact. Conclude with `this.symm`.

Establish `h2` using `Algebra.norm_eq_norm_adjoin ℚ b`. Establish `h3 : Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ b) = (-1) ^ (minpoly ℚ β).natDegree * (minpoly ℚ β).coeff 0`. Use `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)` as an intermediate fact. Rewrite `this` using `[IntermediateField.adjoin.powerBasis_gen hint, IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin]`. Conclude with `this`.

Use `set m := Module.finrank ℚ⟮b⟯ L`. Use `⟨m, Module.finrank_pos, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.finrank_mul_finrank ℚ ℚ⟮b⟯ L, IntermediateField.adjoin.finrank hint, hmin, mul_comm]`. Establish `hN : |Algebra.norm ℚ b| = |(minpoly ℚ β).coeff 0| ^ m`. Rewrite using `[h2, abs_pow]`.

Use `erw [h3]`. Rewrite using `[abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]`. Establish `hprod` using `Algebra.norm_eq_prod_embeddings ℚ ℂ b`. Establish `hne : ∀ τ : L →+* ℂ, ‖τ b‖ ≠ 0` using `fun τ => by`. Rewrite using `[norm_ne_zero_iff]`.

Conclude with `(map_ne_zero τ).2 (fun h => h0 (congrArg Subtype.val h))`. Rewrite using `[← Real.log_prod (fun τ _ => hne τ), ← norm_prod]`. Establish `e : ∏ τ : L →+* ℂ, τ b = ∏ σ : L →ₐ[ℚ] ℂ, σ b` using `Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ (fun τ => rfl)`. Rewrite using `[e, ← hprod, eq_ratCast, Complex.norm_ratCast]`. Rewrite using `[show |((Algebra.norm ℚ b : ℚ) : ℝ)| = (((|Algebra.norm ℚ b|) : ℚ) : ℝ) by push_cast; rfl, hN]`.

Use `push_cast`. Rewrite using `[Real.log_pow]`.
-/
theorem sum_log_emb (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [NumberField L] (β : ℂ) (hβ : β ∈ L)
    (h0 : β ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ Module.finrank ℚ L = m * (minpoly ℚ β).natDegree ∧
      ∑ τ : L →+* ℂ, Real.log ‖τ ⟨β, hβ⟩‖ = m * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| := by
  set b : L := ⟨β, hβ⟩
  have hint : IsIntegral ℚ b := .of_finite ℚ b
  have hmin : minpoly ℚ b = minpoly ℚ β := by
    have := minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ L ℂ) Subtype.val_injective b
    exact this.symm
  have h2 := Algebra.norm_eq_norm_adjoin ℚ b
  have h3 : Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ b) =
      (-1) ^ (minpoly ℚ β).natDegree * (minpoly ℚ β).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen hint, IntermediateField.minpoly_gen,
      IntermediateField.adjoin.powerBasis_dim, hmin] at this
    exact this
  set m := Module.finrank ℚ⟮b⟯ L
  refine ⟨m, Module.finrank_pos, ?_, ?_⟩
  · rw [← Module.finrank_mul_finrank ℚ ℚ⟮b⟯ L, IntermediateField.adjoin.finrank hint, hmin, mul_comm]
  · have hN : |Algebra.norm ℚ b| = |(minpoly ℚ β).coeff 0| ^ m := by
      rw [h2, abs_pow]; erw [h3]; rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ b
    have hne : ∀ τ : L →+* ℂ, ‖τ b‖ ≠ 0 := fun τ => by
      rw [norm_ne_zero_iff]; exact (map_ne_zero τ).2 (fun h => h0 (congrArg Subtype.val h))
    rw [← Real.log_prod (fun τ _ => hne τ), ← norm_prod]
    have e : ∏ τ : L →+* ℂ, τ b = ∏ σ : L →ₐ[ℚ] ℂ, σ b :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ (fun τ => rfl)
    rw [e, ← hprod, eq_ratCast, Complex.norm_ratCast]
    rw [show |((Algebra.norm ℚ b : ℚ) : ℝ)| = (((|Algebra.norm ℚ b|) : ℚ) : ℝ) by push_cast; rfl, hN]
    push_cast
    rw [Real.log_pow]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h3 : ({g, φK, (starRingEnd ℂ).comp φK} : Finset (K →+* ℂ)).card = 3` using `Finset.card_eq_three.2 ⟨g, φK, _, h.1, h.2, hc.symm, rfl⟩`. Use `Finset.card_le_univ ({g, φK, (starRingEnd ℂ).comp φK} : Finset (K →+* ℂ))` as an intermediate fact. Rewrite `this` using `[h3, NumberField.Embeddings.card, hK2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem emb_two {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (hK2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (g : K →+* ℂ) : g = φK ∨ g = (starRingEnd ℂ).comp φK := by
  classical
  by_contra h
  push_neg at h
  have h3 : ({g, φK, (starRingEnd ℂ).comp φK} : Finset (K →+* ℂ)).card = 3 :=
    Finset.card_eq_three.2 ⟨g, φK, _, h.1, h.2, hc.symm, rfl⟩
  have := Finset.card_le_univ ({g, φK, (starRingEnd ℂ).comp φK} : Finset (K →+* ℂ))
  rw [h3, NumberField.Embeddings.card, hK2] at this
  omega

open Classical in

/- English proof (translation)
Use `set P : (L →+* ℂ) → Prop := fun τ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x with hPdef`. Use `set c : (L →+* ℂ) → (L →+* ℂ) := fun τ => (starRingEnd ℂ).comp τ with hcdef`. Establish `hcc : ∀ τ, c (c τ) = τ` using `fun τ => RingHom.ext fun x => by simp [c]`. Establish `key : ∀ τ, ¬ P τ ↔ P (c τ)`. Introduce `τ`.

Set `g : K →+* ℂ` to `τ.comp (φK.codRestrict L hK)`. Establish `hP : P τ ↔ g = φK` using `⟨fun h => RingHom.ext fun x => h x, fun h x => RingHom.congr_fun h x⟩`. Establish `hPc : P (c τ) ↔ (starRingEnd ℂ).comp g = φK` using `⟨fun h => RingHom.ext fun x => h x, fun h x => RingHom.congr_fun h x⟩`. Rewrite using `[hP, hPc]`. Break down `emb_two φK hK2 hc g with h | h` into its components or cases.

Rewrite using `[h]`. Conclude with `iff_of_false (not_not.2 rfl) hc`. Rewrite using `[h]; exact iff_of_true hc (RingHom.ext fun x => by simp)`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ P f, two_mul]`. Use `congr 1`.

Use `Finset.sum_nbij' c c ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`. Conclude with `(key a).1 ha`. Introduce `a ha`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`. Conclude with `(key (c a)).2 (by rw [hcc]; exact ha)`. Introduce `a _`. Conclude with `hcc a`. Introduce `a _`.

Conclude with `hcc a`. Introduce `a _`. Conclude with `(hf a).symm`.
-/
theorem sum_halve {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (hK2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (L : IntermediateField ℚ ℂ) [NumberField L] (hK : ∀ x : K, φK x ∈ L)
    (f : (L →+* ℂ) → ℝ) (hf : ∀ τ, f ((starRingEnd ℂ).comp τ) = f τ) :
    ∑ τ : L →+* ℂ, f τ =
      2 * ∑ τ ∈ Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x), f τ := by
  classical
  set P : (L →+* ℂ) → Prop := fun τ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x with hPdef
  set c : (L →+* ℂ) → (L →+* ℂ) := fun τ => (starRingEnd ℂ).comp τ with hcdef
  have hcc : ∀ τ, c (c τ) = τ := fun τ => RingHom.ext fun x => by simp [c]
  have key : ∀ τ, ¬ P τ ↔ P (c τ) := by
    intro τ
    let g : K →+* ℂ := τ.comp (φK.codRestrict L hK)
    have hP : P τ ↔ g = φK := ⟨fun h => RingHom.ext fun x => h x, fun h x => RingHom.congr_fun h x⟩
    have hPc : P (c τ) ↔ (starRingEnd ℂ).comp g = φK :=
      ⟨fun h => RingHom.ext fun x => h x, fun h x => RingHom.congr_fun h x⟩
    rw [hP, hPc]
    rcases emb_two φK hK2 hc g with h | h
    · rw [h]; exact iff_of_false (not_not.2 rfl) hc
    · rw [h]; exact iff_of_true hc (RingHom.ext fun x => by simp)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P f, two_mul]
  congr 1
  refine Finset.sum_nbij' c c ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (key a).1 ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (key (c a)).2 (by rw [hcc]; exact ha)
  · intro a _; exact hcc a
  · intro a _; exact hcc a
  · intro a _; exact (hf a).symm

open Classical in

/- English proof (translation)
Use `set Fx := Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x) with hFx`. Use `set S : ClassGroup (𝓞 K) → Finset (L →+* ℂ) := fun C => Finset.univ.filter (fun τ => ∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧ ClassGroup.mk K (𝔞 σ) = C) with hSdef`. Establish `hS : ∀ C, (S C).card * (2 * classNumber K) = Module.finrank ℚ L`. Introduce `C`. Use `hE.2.2 L inferInstance inferInstance hK hj C` as an intermediate fact.

Rewrite `this` using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Then use the resulting hypothesis. Establish `hsame : ∀ (τ : L →+* ℂ) (σ σ' : ℂ ≃+* ℂ), Fixes φK σ → Fixes φK σ' → (∀ x : L, σ (x : ℂ) = τ x) → (∀ x : L, σ' (x : ℂ) = τ x) → ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ')`. Introduce `τ σ σ' hσ hσ' h h'`. Use `(hE.2.1 σ σ' hσ hσ').2 ?_` and prove the remaining obligations. Establish `e1` using `h ⟨j₀, hj⟩`.

Establish `e2` using `h' ⟨j₀, hj⟩`. Simplify using `only at e1 e2`. Rewrite using `[e1, e2]`. Establish `hdisj : ∀ C ∈ (Finset.univ : Finset (ClassGroup (𝓞 K))), ∀ C' ∈ (Finset.univ : Finset (ClassGroup (𝓞 K))), C ≠ C' → Disjoint (S C) (S C')`. Introduce `C _ C' _ hCC'`.

Rewrite using `[Finset.disjoint_left]`. Introduce `t ht ht'`. Take `⟨σ, hσ, hσt, hC⟩` from `(Finset.mem_filter.1 ht).2`. Take `⟨σ', hσ', hσt', hC'⟩` from `(Finset.mem_filter.1 ht').2`. Conclude with `hCC' (hC.symm.trans ((hsame t σ σ' hσ hσ' hσt hσt').trans hC'))`.

Establish `hsub : Finset.univ.biUnion S ⊆ Fx`. Introduce `t ht`. Take `⟨C, -, htC⟩` from `Finset.mem_biUnion.1 ht`. Take `⟨σ, hσ, hσt, -⟩` from `(Finset.mem_filter.1 htC).2`. Use `Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hσt]`. Conclude with `hσ x`. Establish `hh : 0 < classNumber K` using `Fintype.card_pos`. Establish `hcardU : 2 * (Finset.univ.biUnion S).card = Module.finrank ℚ L`. Rewrite using `[Finset.card_biUnion hdisj]`.

Establish `e : (∑ C, (S C).card) * (2 * classNumber K) = classNumber K * Module.finrank ℚ L`. Rewrite using `[Finset.sum_mul, Finset.sum_congr rfl (fun C _ => hS C), Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Both sides reduce to the same expression. Establish `e2 : (2 * ∑ C, (S C).card) * classNumber K = Module.finrank ℚ L * classNumber K`. Rewrite using `[mul_comm (Module.finrank ℚ L), ← e]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Nat.eq_of_mul_eq_mul_right hh e2`. Establish `hU : Finset.univ.biUnion S = Fx` using `Finset.eq_of_subset_of_card_le hsub (by omega)`. Establish `hex : ∀ τ : L →+* ℂ, ∃ σ : ℂ ≃+* ℂ, τ ∈ Fx → Fixes φK σ ∧ ∀ x : L, σ (x : ℂ) = τ x`. Introduce `τ`.

Distinguish the cases in `hτ : τ ∈ Fx`. Rewrite `hτ` using `[← hU]`. Take `⟨C, -, htC⟩` from `Finset.mem_biUnion.1 hτ`. Take `⟨σ, hσ, hσt, -⟩` from `(Finset.mem_filter.1 htC).2`. Conclude with `⟨σ, fun _ => ⟨hσ, hσt⟩⟩`.

Conclude with `⟨RingEquiv.refl ℂ, fun h => absurd h hτ⟩`. Use `choose ext hext using hex`. Use `⟨ext, fun τ hτ => hext τ hτ, fun C => ?_⟩` and prove the remaining obligations. Rewrite using `[← hS C]`. Use `congr 1`.

Use `congr 1`. Use extensionality with `τ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, S]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hτ, hC⟩`.

Conclude with `⟨ext τ, (hext τ (by simpa [Fx] using hτ)).1, (hext τ (by simpa [Fx] using hτ)).2, hC⟩`. Introduce and unpack `⟨σ, hσ, hσt, hC⟩`. Establish `hτ : τ ∈ Fx` using `hsub (Finset.mem_biUnion.2 ⟨C, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, σ, hσ, hσt, hC⟩⟩)`. Use `⟨by simpa [Fx] using hτ, ?_⟩` and prove the remaining obligations. Rewrite using `[hsame τ (ext τ) σ (hext τ hτ).1 hσ (hext τ hτ).2 hσt, hC]`.
-/
theorem cover {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (j₀ : ℂ)
    (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hE : Equidistributed φK j₀ 𝔞)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [IsGalois ℚ L] [NumberField L] (hK : ∀ x : K, φK x ∈ L)
    (hj : j₀ ∈ L)
    (hcard : 2 * (Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x)).card = Module.finrank ℚ L) :
    ∃ ext : (L →+* ℂ) → (ℂ ≃+* ℂ),
      (∀ τ ∈ Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x),
        Fixes φK (ext τ) ∧ ∀ x : L, ext τ (x : ℂ) = τ x) ∧
      ∀ C : ClassGroup (𝓞 K), ((Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x)).filter
        (fun τ => ClassGroup.mk K (𝔞 (ext τ)) = C)).card * (2 * classNumber K) = Module.finrank ℚ L := by
  set Fx := Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x) with hFx
  set S : ClassGroup (𝓞 K) → Finset (L →+* ℂ) := fun C => Finset.univ.filter
    (fun τ => ∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧ ClassGroup.mk K (𝔞 σ) = C) with hSdef
  have hS : ∀ C, (S C).card * (2 * classNumber K) = Module.finrank ℚ L := by
    intro C
    have := hE.2.2 L inferInstance inferInstance hK hj C
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this

  have hsame : ∀ (τ : L →+* ℂ) (σ σ' : ℂ ≃+* ℂ), Fixes φK σ → Fixes φK σ' → (∀ x : L, σ (x : ℂ) = τ x) →
      (∀ x : L, σ' (x : ℂ) = τ x) → ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') := by
    intro τ σ σ' hσ hσ' h h'
    refine (hE.2.1 σ σ' hσ hσ').2 ?_
    have e1 := h ⟨j₀, hj⟩
    have e2 := h' ⟨j₀, hj⟩
    simp only at e1 e2
    rw [e1, e2]
  have hdisj : ∀ C ∈ (Finset.univ : Finset (ClassGroup (𝓞 K))), ∀ C' ∈ (Finset.univ : Finset (ClassGroup (𝓞 K))),
      C ≠ C' → Disjoint (S C) (S C') := by
    intro C _ C' _ hCC'
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨σ, hσ, hσt, hC⟩ := (Finset.mem_filter.1 ht).2
    obtain ⟨σ', hσ', hσt', hC'⟩ := (Finset.mem_filter.1 ht').2
    exact hCC' (hC.symm.trans ((hsame t σ σ' hσ hσ' hσt hσt').trans hC'))
  have hsub : Finset.univ.biUnion S ⊆ Fx := by
    intro t ht
    obtain ⟨C, -, htC⟩ := Finset.mem_biUnion.1 ht
    obtain ⟨σ, hσ, hσt, -⟩ := (Finset.mem_filter.1 htC).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩
    rw [← hσt]; exact hσ x
  have hh : 0 < classNumber K := Fintype.card_pos
  have hcardU : 2 * (Finset.univ.biUnion S).card = Module.finrank ℚ L := by
    rw [Finset.card_biUnion hdisj]
    have e : (∑ C, (S C).card) * (2 * classNumber K) = classNumber K * Module.finrank ℚ L := by
      rw [Finset.sum_mul, Finset.sum_congr rfl (fun C _ => hS C), Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rfl
    have e2 : (2 * ∑ C, (S C).card) * classNumber K = Module.finrank ℚ L * classNumber K := by
      rw [mul_comm (Module.finrank ℚ L), ← e]; ring
    exact Nat.eq_of_mul_eq_mul_right hh e2
  have hU : Finset.univ.biUnion S = Fx := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hex : ∀ τ : L →+* ℂ, ∃ σ : ℂ ≃+* ℂ, τ ∈ Fx → Fixes φK σ ∧ ∀ x : L, σ (x : ℂ) = τ x := by
    intro τ
    by_cases hτ : τ ∈ Fx
    · rw [← hU] at hτ
      obtain ⟨C, -, htC⟩ := Finset.mem_biUnion.1 hτ
      obtain ⟨σ, hσ, hσt, -⟩ := (Finset.mem_filter.1 htC).2
      exact ⟨σ, fun _ => ⟨hσ, hσt⟩⟩
    · exact ⟨RingEquiv.refl ℂ, fun h => absurd h hτ⟩
  choose ext hext using hex
  refine ⟨ext, fun τ hτ => hext τ hτ, fun C => ?_⟩
  rw [← hS C]
  congr 1
  congr 1
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  constructor
  · rintro ⟨hτ, hC⟩
    exact ⟨ext τ, (hext τ (by simpa [Fx] using hτ)).1, (hext τ (by simpa [Fx] using hτ)).2, hC⟩
  · rintro ⟨σ, hσ, hσt, hC⟩
    have hτ : τ ∈ Fx := hsub (Finset.mem_biUnion.2 ⟨C, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, σ, hσ, hσt, hC⟩⟩)
    refine ⟨by simpa [Fx] using hτ, ?_⟩
    rw [hsame τ (ext τ) σ (hext τ hτ).1 hσ (hext τ hτ).2 hσt, hC]

/- English proof (translation)
Introduce `K _ _ φK j₀ 𝔞 β F hK2 hc hE hβa hβ0 hFc hFb`. Take `⟨L, hLf, hLg, hK, hj, hβ⟩` from `exists_field φK j₀ β hE.1 hβa`. Use `haveI : NumberField L := ⟨⟩`. Use `set Fx := Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x) with hFx`. Establish `hcard : 2 * Fx.card = Module.finrank ℚ L`.

Use `sum_halve φK hK2 hc L hK (fun _ => (1 : ℝ)) (fun _ => rfl)` as an intermediate fact. Simplify using `only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, NumberField.Embeddings.card] at this`. Conclude with `this.symm` after adjusting the coercions. Take `⟨ext, hext, hcnt⟩` from `cover φK j₀ 𝔞 hE L hK hj hcard`. Establish `hn : 0 < Module.finrank ℚ L` using `Module.finrank_pos`.

Establish `hh : 0 < classNumber K` using `Fintype.card_pos`. Establish `hrep : ∀ C : ClassGroup (𝓞 K), ∃ σ, Fixes φK σ ∧ ClassGroup.mk K (𝔞 σ) = C`. Introduce `C`. Establish `h1` using `hcnt C`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : (Fx.filter (fun τ => ClassGroup.mk K (𝔞 (ext τ)) = C)).Nonempty := by`.

Rewrite using `[← Finset.card_pos]`. Assume the negation of the conclusion as `h0`. Rewrite `h1` using `[Nat.eq_zero_of_not_pos h0, zero_mul]`. Use linear arithmetic over natural numbers and integers. Rewrite `hτ` using `[Finset.mem_filter]`.

Conclude with `⟨ext τ, (hext τ hτ.1).1, hτ.2⟩`. Use `choose rep hrepP using hrep`. Use `⟨rep, fun C => hrepP C, ?_⟩` and prove the remaining obligations. Take `⟨m, hm, hdeg, hsum⟩` from `sum_log_emb L β hβ hβ0`. Use `set b : L := ⟨β, hβ⟩`.

Use `set cls : (L →+* ℂ) → ClassGroup (𝓞 K) := fun τ => ClassGroup.mk K (𝔞 (ext τ))`. Establish `hb : ∀ τ ∈ Fx, Real.log ‖τ b‖ ≤ F (rep (cls τ))`. Introduce `τ hτ`. Establish `e : ext τ β = τ b` using `(hext τ hτ).2 b`. Rewrite using `[← e]`.

Use `(hFb _ (hext τ hτ).1).trans (le_of_eq ?_)` and prove the remaining obligations. Conclude with `hFc _ _ (hext τ hτ).1 (hrepP _).1 (hrepP _).2.symm`. Establish `hhalf` using `sum_halve φK hK2 hc L hK (fun τ => Real.log ‖τ b‖) (fun τ => by simp)`. Use `set k : ClassGroup (𝓞 K) → ℕ := fun C => (Fx.filter (fun τ => cls τ = C)).card`. Establish `hfib : ∑ τ ∈ Fx, F (rep (cls τ)) = ∑ C, (k C : ℝ) * F (rep C)`.

Rewrite using `[← Finset.sum_fiberwise Fx cls (fun τ => F (rep (cls τ)))]`. Use `Finset.sum_congr rfl fun C _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun τ hτ => by rw [(Finset.mem_filter.1 hτ).2]), Finset.sum_const, nsmul_eq_mul]`. Establish `hk : ∀ C, (2 : ℝ) * k C = m * (minpoly ℚ β).natDegree / classNumber K`. Introduce `C`.

Use `hcnt C` as an intermediate fact. Rewrite `this` using `[hdeg]`. Establish `hhr : (classNumber K : ℝ) ≠ 0` using `by exact_mod_cast hh.ne'`. Rewrite using `[eq_div_iff hhr]`. Establish `: ((k C * (2 * classNumber K) : ℕ) : ℝ) = ((m * (minpoly ℚ β).natDegree : ℕ) : ℝ)`.

Conclude with `this` after adjusting the coercions. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmain : (m : ℝ) * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤ m * ((minpoly ℚ β).natDegree * ((∑ c, F (rep c)) / (classNumber K : ℝ)))`. Rewrite using `[← hsum, hhalf]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hfib, Finset.mul_sum]; refine Finset.sum_congr rfl fun C _ => by ring`. Use `_ = ∑ C, (m * (minpoly ℚ β).natDegree / classNumber K) * F (rep C) := by`. Use `Finset.sum_congr rfl fun C _ => by rw [hk C]` and prove the remaining obligations. Use `_ = _ := by rw [← Finset.mul_sum]; ring`.

Establish `hm' : (0 : ℝ) < m` using `by exact_mod_cast hm`. Conclude with `le_of_mul_le_mul_left hmain hm'`.
-/
theorem galmean : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (j₀ : ℂ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (β : ℂ) (F : (ℂ ≃+* ℂ) → ℝ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK →
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Equidistributed φK j₀ 𝔞 → IsAlgebraic ℚ β → β ≠ 0 →
    (∀ σ σ' : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ' →
      ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') → F σ = F σ') →
    (∀ σ : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → Real.log ‖σ β‖ ≤ F σ) →
    ∃ rep : ClassGroup (𝓞 K) → (ℂ ≃+* ℂ), (∀ c, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK (rep c) ∧ ClassGroup.mk K (𝔞 (rep c)) = c) ∧
      Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤
        (minpoly ℚ β).natDegree * ((∑ c, F (rep c)) / (NumberField.classNumber K : ℝ)) := by
  intro K _ _ φK j₀ 𝔞 β F hK2 hc hE hβa hβ0 hFc hFb
  classical
  obtain ⟨L, hLf, hLg, hK, hj, hβ⟩ := exists_field φK j₀ β hE.1 hβa
  haveI : NumberField L := ⟨⟩
  set Fx := Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x) with hFx
  have hcard : 2 * Fx.card = Module.finrank ℚ L := by
    have := sum_halve φK hK2 hc L hK (fun _ => (1 : ℝ)) (fun _ => rfl)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, NumberField.Embeddings.card] at this
    exact_mod_cast this.symm
  obtain ⟨ext, hext, hcnt⟩ := cover φK j₀ 𝔞 hE L hK hj hcard
  have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hh : 0 < classNumber K := Fintype.card_pos
  have hrep : ∀ C : ClassGroup (𝓞 K), ∃ σ, Fixes φK σ ∧ ClassGroup.mk K (𝔞 σ) = C := by
    intro C
    have h1 := hcnt C
    obtain ⟨τ, hτ⟩ : (Fx.filter (fun τ => ClassGroup.mk K (𝔞 (ext τ)) = C)).Nonempty := by
      rw [← Finset.card_pos]
      by_contra h0
      rw [Nat.eq_zero_of_not_pos h0, zero_mul] at h1
      omega
    rw [Finset.mem_filter] at hτ
    exact ⟨ext τ, (hext τ hτ.1).1, hτ.2⟩
  choose rep hrepP using hrep
  refine ⟨rep, fun C => hrepP C, ?_⟩
  obtain ⟨m, hm, hdeg, hsum⟩ := sum_log_emb L β hβ hβ0
  set b : L := ⟨β, hβ⟩
  set cls : (L →+* ℂ) → ClassGroup (𝓞 K) := fun τ => ClassGroup.mk K (𝔞 (ext τ))

  have hb : ∀ τ ∈ Fx, Real.log ‖τ b‖ ≤ F (rep (cls τ)) := by
    intro τ hτ
    have e : ext τ β = τ b := (hext τ hτ).2 b
    rw [← e]
    refine (hFb _ (hext τ hτ).1).trans (le_of_eq ?_)
    exact hFc _ _ (hext τ hτ).1 (hrepP _).1 (hrepP _).2.symm
  have hhalf := sum_halve φK hK2 hc L hK (fun τ => Real.log ‖τ b‖) (fun τ => by simp)
  set k : ClassGroup (𝓞 K) → ℕ := fun C => (Fx.filter (fun τ => cls τ = C)).card
  have hfib : ∑ τ ∈ Fx, F (rep (cls τ)) = ∑ C, (k C : ℝ) * F (rep C) := by
    rw [← Finset.sum_fiberwise Fx cls (fun τ => F (rep (cls τ)))]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_congr rfl (fun τ hτ => by rw [(Finset.mem_filter.1 hτ).2]), Finset.sum_const, nsmul_eq_mul]
  have hk : ∀ C, (2 : ℝ) * k C = m * (minpoly ℚ β).natDegree / classNumber K := by
    intro C
    have := hcnt C
    rw [hdeg] at this
    have hhr : (classNumber K : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [eq_div_iff hhr]
    have : ((k C * (2 * classNumber K) : ℕ) : ℝ) = ((m * (minpoly ℚ β).natDegree : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this
    linarith
  have hmain : (m : ℝ) * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤
      m * ((minpoly ℚ β).natDegree * ((∑ c, F (rep c)) / (classNumber K : ℝ))) := by
    rw [← hsum, hhalf]
    calc 2 * ∑ τ ∈ Fx, Real.log ‖τ b‖ ≤ 2 * ∑ τ ∈ Fx, F (rep (cls τ)) := by
          gcongr with τ hτ; exact hb τ hτ
      _ = ∑ C, (2 * (k C : ℝ)) * F (rep C) := by
          rw [hfib, Finset.mul_sum]; refine Finset.sum_congr rfl fun C _ => by ring
      _ = ∑ C, (m * (minpoly ℚ β).natDegree / classNumber K) * F (rep C) := by
          refine Finset.sum_congr rfl fun C _ => by rw [hk C]
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  exact le_of_mul_le_mul_left hmain hm'

end GlobalTheory.GalMean
