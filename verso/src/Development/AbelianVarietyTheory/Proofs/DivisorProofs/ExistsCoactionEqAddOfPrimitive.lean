import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.HopfQuot

section
variable {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]

/- English proof (translation)
Establish `h1 : ∀ w : Λ ⊗[R] Λ, ev Λ l (w * (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b)) = ev Λ l w * b + ev Λ (l ∘ₗ LinearMap.mulRight R b) w`. Introduce `w`. Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add u v hu hv`.

Simplify using `only [add_mul, map_add, hu, hv]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul u v => simp [mul_add]`. Establish `h2` using `hl (u * b)`. Rewrite `h2` using `[Bialgebra.comul_mul, hb, h1, hl, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one]`.

Rewrite using `[← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ev_mulRight_comul_of_primitive (l : Λ →ₗ[R] R)
    (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : Λ)
    (hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) (u : Λ) :
    ev Λ (l ∘ₗ LinearMap.mulRight R b) (Coalgebra.comul u) =
      l (u * b) • (1 : Λ) - l u • b := by
  have h1 : ∀ w : Λ ⊗[R] Λ, ev Λ l (w * (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b)) =
      ev Λ l w * b + ev Λ (l ∘ₗ LinearMap.mulRight R b) w := by
    intro w
    induction w with
    | zero => simp
    | add u v hu hv =>
      simp only [add_mul, map_add, hu, hv]
      ring
    | tmul u v => simp [mul_add]
  have h2 := hl (u * b)
  rw [Bialgebra.comul_mul, hb, h1, hl, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] at h2
  rw [← h2]
  ring

/- English proof (translation)
Use `set l' := l ∘ₗ LinearMap.mulRight R b with hl'`. Set `F : B ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] B ⊗[R] Λ` to `((ev Λ l').restrictScalars R).lTensor B`. Establish `h1 : ∀ w : B ⊗[R] Λ, ρ (ev B l' w) = F (TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ w))`. Introduce `w`. Proceed by induction on `w with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a b`. Rewrite using `[ev_tmul, map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]`. Generalize the expression as in `ρ a = w`.

Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]`. Consider the case `tmul u v => simp [F]`. Establish `h2 : ∀ w : B ⊗[R] Λ, F ((Coalgebra.comul (R` using `R)).lTensor B w) = ev B l' w ⊗ₜ 1 - ev B l w ⊗ₜ b := by`.

Introduce `w`. Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add a c ha hc`. Simplify using `only [map_add, add_tmul, ha, hc]`.

Normalize the expressions using the abelian group laws. Consider the case `tmul a c`. Use `ev_mulRight_comul_of_primitive l hl b hb c` as an intermediate fact. Rewrite `this` using `[← hl']`. Simplify using `only [F, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, this, ev_tmul, tmul_sub, smul_tmul]`.

Both sides reduce to the same expression. Rewrite using `[h1, hassoc, h2]`.
-/
theorem coact_ev_mulRight_of_primitive (ρ : B →ₐ[R] B ⊗[R] Λ)
    (hassoc : ∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a))
    (l : Λ →ₗ[R] R) (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : Λ)
    (hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) (f : B) :
    ρ (ev B (l ∘ₗ LinearMap.mulRight R b) (ρ f)) =
      ev B (l ∘ₗ LinearMap.mulRight R b) (ρ f) ⊗ₜ[R] 1 - ev B l (ρ f) ⊗ₜ[R] b := by
  set l' := l ∘ₗ LinearMap.mulRight R b with hl'
  let F : B ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] B ⊗[R] Λ := ((ev Λ l').restrictScalars R).lTensor B
  have h1 : ∀ w : B ⊗[R] Λ, ρ (ev B l' w) =
      F (TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ w)) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      rw [ev_tmul, map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      generalize ρ a = w
      induction w with
      | zero => simp
      | add u v hu hv => simp only [map_add, smul_add, add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : B ⊗[R] Λ, F ((Coalgebra.comul (R := R)).lTensor B w) =
      ev B l' w ⊗ₜ 1 - ev B l w ⊗ₜ b := by
    intro w
    induction w with
    | zero => simp
    | add a c ha hc =>
      simp only [map_add, add_tmul, ha, hc]
      abel
    | tmul a c =>
      have := ev_mulRight_comul_of_primitive l hl b hb c
      rw [← hl'] at this
      simp only [F, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, this, ev_tmul,
        tmul_sub, smul_tmul]
      rfl
  rw [h1, hassoc, h2]

end

/- English proof (translation)
Introduce `R Λ B _ _ _ _ _ _ _ ρ hassoc hcounit hsurj b hb0`. Establish `hb : Coalgebra.comul (R` using `R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by`. Rewrite `hb0` using `[cobOne_apply, sub_sub, sub_eq_zero]`. Conclude with `hb0`. Take `⟨-, -, hff, -⟩` from `finite_faithfullyFlat_ker ρ hassoc hcounit hsurj`.

Use `set B₀ := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) with hB₀`. Set `I : Ideal B₀` to `{ carrier := {y | ∃ x : B, ρ x = x ⊗ₜ[R] 1 + (y : B) ⊗ₜ[R] b} add_mem' := by`. Introduce and unpack `y z ⟨x, hx⟩ ⟨x', hx'⟩`. Use `⟨x + x', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hx, hx', Subalgebra.coe_add, add_tmul, add_tmul]`.

Normalize the expressions using the abelian group laws. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `t y ⟨x, hx⟩`. Establish `ht : ρ t = (t : B) ⊗ₜ 1` using `t.2`.

Use `⟨t * x, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ht, hx]`. Simplify using `[mul_add] }`. Take `⟨n, l, T, hl, hT⟩` from `exists_integrals R Λ`. Establish `hmem : ∀ k f, ev B (l k) (ρ f) ∈ I.map (algebraMap B₀ B)`.

Introduce `k f`. Use `Ideal.mem_map_of_mem (algebraMap B₀ B) (x := ⟨ev B (l k) (ρ f), ev_mem_equalizer ρ hassoc _ (hl k) f⟩) ?_` and prove the remaining obligations. Use `⟨-ev B (l k ∘ₗ LinearMap.mulRight R b) (ρ f), ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, coact_ev_mulRight_of_primitive ρ hassoc _ (hl k) b hb, neg_tmul]`. Normalize the expressions using the abelian group laws.

Establish `hall : ∀ k z, ev B (l k) z ∈ I.map (algebraMap B₀ B)`. Introduce `k z`. Take `⟨w, rfl⟩` from `hsurj z`. Proceed by induction on `w with`. Consider the case `zero => simp`.

Consider the case `add u v hu hv`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem hu hv`. Consider the case `tmul u v`. Establish `: (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) u * ρ v = u • ρ v`.

Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[Algebra.TensorProduct.productMap_apply_tmul, this, map_smul]`. Conclude with `Ideal.mul_mem_left _ _ (hmem k v)`. Establish `h1 : (1 : B) ∈ I.map (algebraMap B₀ B)`.

Establish `: (1 : B) = ∑ k, ev B (l k) (1 ⊗ₜ T k)`. Establish `h` using `hT 1`. Simplify using `only [mul_one, Bialgebra.counit_one] at h`. Simplify using `[← Finset.sum_smul, h]`. Rewrite using `[this]`.

Conclude with `Ideal.sum_mem _ fun k _ => hall k _`. Establish `h2 : (1 : B₀) ∈ I`. Rewrite using `[← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I, Ideal.mem_comap, map_one]`. Conclude with `h1`. Conclude with `h2`.
-/
theorem exists_coact_eq_add_of_primitive : ∀ {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] B ⊗[R] Λ), (∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a)) → (∀ a, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ a)) = a) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) → ∀ b : Λ, cobOne R Λ b = 0 → ∃ x : B, ρ x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  intro R Λ B _ _ _ _ _ _ _ ρ hassoc hcounit hsurj b hb0
  have hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb0
    exact hb0
  obtain ⟨-, -, hff, -⟩ := finite_faithfullyFlat_ker ρ hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) with hB₀
  let I : Ideal B₀ :=
    { carrier := {y | ∃ x : B, ρ x = x ⊗ₜ[R] 1 + (y : B) ⊗ₜ[R] b}
      add_mem' := by
        rintro y z ⟨x, hx⟩ ⟨x', hx'⟩
        refine ⟨x + x', ?_⟩
        rw [map_add, hx, hx', Subalgebra.coe_add, add_tmul, add_tmul]
        abel
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro t y ⟨x, hx⟩
        have ht : ρ t = (t : B) ⊗ₜ 1 := t.2
        refine ⟨t * x, ?_⟩
        rw [map_mul, ht, hx]
        simp [mul_add] }
  obtain ⟨n, l, T, hl, hT⟩ := exists_integrals R Λ
  have hmem : ∀ k f, ev B (l k) (ρ f) ∈ I.map (algebraMap B₀ B) := by
    intro k f
    refine Ideal.mem_map_of_mem (algebraMap B₀ B)
      (x := ⟨ev B (l k) (ρ f), ev_mem_equalizer ρ hassoc _ (hl k) f⟩) ?_
    refine ⟨-ev B (l k ∘ₗ LinearMap.mulRight R b) (ρ f), ?_⟩
    rw [map_neg, coact_ev_mulRight_of_primitive ρ hassoc _ (hl k) b hb, neg_tmul]
    abel
  have hall : ∀ k z, ev B (l k) z ∈ I.map (algebraMap B₀ B) := by
    intro k z
    obtain ⟨w, rfl⟩ := hsurj z
    induction w with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, map_add]
      exact add_mem hu hv
    | tmul u v =>
      have : (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) u * ρ v = u • ρ v := by
        rw [Algebra.smul_def]
        rfl
      rw [Algebra.TensorProduct.productMap_apply_tmul, this, map_smul]
      exact Ideal.mul_mem_left _ _ (hmem k v)
  have h1 : (1 : B) ∈ I.map (algebraMap B₀ B) := by
    have : (1 : B) = ∑ k, ev B (l k) (1 ⊗ₜ T k) := by
      have h := hT 1
      simp only [mul_one, Bialgebra.counit_one] at h
      simp [← Finset.sum_smul, h]
    rw [this]
    exact Ideal.sum_mem _ fun k _ => hall k _
  have h2 : (1 : B₀) ∈ I := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I, Ideal.mem_comap, map_one]
    exact h1
  exact h2

end GlobalTheory.HopfQuot
