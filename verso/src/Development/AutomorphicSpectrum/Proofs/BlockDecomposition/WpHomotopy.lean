import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpHomotopy

/- English proof (translation)
Introduce `A _ B _ _ K _ _ ι δ hW hδ`. Establish `huniq : ∀ (m : ℕ) (T : Type) [CommRing T] [Algebra A T] (f g : K m →ₐ[A] T), (∀ i, f.comp (ι m i) = g.comp (ι m i)) → f = g`. Introduce `m T _ _ f g hfg`. Establish `key` using `(hW m).uniq T (f : K m →+* T) (g : K m →+* T) (by ext a; simp) (fun i => by`. Use extensionality with `b`.

Conclude with `DFunLike.congr_fun (hfg i) b)`. Use extensionality with `x`. Conclude with `DFunLike.congr_fun key x`. Establish `hex : ∀ n, ∃ h : K (n + 1) →ₐ[A] B ⊗[A] K n, h.comp (ι (n + 1) 0) = Algebra.TensorProduct.includeLeft ∧ ∀ i : Fin n, h.comp (ι (n + 1) i.succ) = (Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n).comp (ι n i)`. Introduce `n`.

Take `⟨z, hz, hzi⟩` from `(hW (n + 1)).ex (B ⊗[A] K n) (algebraMap A (B ⊗[A] K n)) (Fin.cons (α := fun _ => B →+* B ⊗[A] K n) ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] K n) : B →+* B ⊗[A] K n) (fun i => (((Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n).comp (ι n i) : B →ₐ[A] B ⊗[A] …`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Use extensionality with `a`. Simplify using the standard rewrite rules.

Use extensionality with `a`. Use the proof step `simp)`. Use `⟨{ z with commutes' := fun a => DFunLike.congr_fun hz a }, ?_, fun i => ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Simplify using `using DFunLike.congr_fun (hzi 0) b`.

Use extensionality with `b`. Simplify using `using DFunLike.congr_fun (hzi i.succ) b`. Use `choose h hl hr using hex`. Establish `h0 : ∀ n, (h n).comp (δ n 0) = (Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n)`. Introduce `n`.

Use `huniq n _ _ _ (fun i => ?_)` and prove the remaining obligations. Rewrite using `[AlgHom.comp_assoc, hδ, Fin.succAbove_zero]`. Conclude with `hr n i`. Establish `hs : ∀ n (k : Fin (n + 1)), (h (n + 1)).comp (δ (n + 1) k.succ) = (Algebra.TensorProduct.map (AlgHom.id A B) (δ n k)).comp (h n)`. Introduce `n k`.

Use `huniq (n + 1) _ _ _ (fun i => ?_)` and prove the remaining obligations. Rewrite using `[AlgHom.comp_assoc, hδ, AlgHom.comp_assoc]`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.succ_succAbove_zero, hl, hl]`. Use extensionality with `b`.

Simplify using the standard rewrite rules. Rewrite using `[Fin.succ_succAbove_succ, hr, hr, ← AlgHom.comp_assoc]`. Establish `e` using `hδ n k j`. Use extensionality with `b`. Establish `e'` using `DFunLike.congr_fun e b`.

Simplify using `only [AlgHom.comp_apply] at e' ⊢`. Simplify using `[e']`. Use `⟨fun n => (h n).toLinearMap, fun z => ?_, fun n z => ?_⟩` and prove the remaining obligations. Establish `e` using `DFunLike.congr_fun (h0 0) z`. Simplify `e` using `[alt]`.

Establish `e0` using `DFunLike.congr_fun (h0 (n + 1)) z`. Establish `es : ∀ k : Fin (n + 1), h (n + 1) (δ (n + 1) k.succ z) = ((δ n k).toLinearMap.lTensor B) (h n z)`. Introduce `k`. Establish `e` using `DFunLike.congr_fun (hs n k) z`. Simplify using `only [AlgHom.comp_apply] at e`.

Rewrite using `[e]`. Generalize the expression as in `h n z = t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `a1 : alt (δ (n + 1)) z = δ (n + 1) 0 z + ∑ k : Fin (n + 1), -((-1 : ℤ) ^ (k : ℕ) • δ (n + 1) k.succ z)`. Simplify using `[alt, Fin.sum_univ_succ, LinearMap.sum_apply, pow_succ]`. Establish `a2 : ∀ t : B ⊗[A] K n, (alt (δ n)).lTensor B t = ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ((δ n k).toLinearMap.lTensor B) t`. Introduce `t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `only [alt, LinearMap.lTensor_tmul, LinearMap.sum_apply, LinearMap.smul_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]`. Consider the case `add x y hx hy`.

Simplify using `only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]`. Use `show (alt (δ n)).lTensor B (h n z) + h (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z`. Establish `e1 : h (n + 1) (δ (n + 1) 0 z) = (1 : B) ⊗ₜ[A] z`. Simplify using `using e0`. Rewrite using `[a1, a2, map_add, e1, map_sum, add_left_comm, ← Finset.sum_add_distrib]`.

Establish `: ∀ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ((δ n k).toLinearMap.lTensor B) (h n z) + h (n + 1) (-((-1 : ℤ) ^ (k : ℕ) • δ (n + 1) k.succ z)) = 0`. Introduce `k`. Rewrite using `[map_neg, map_zsmul, es k, add_neg_cancel]`. Rewrite using `[Finset.sum_congr rfl (fun k _ => this k)]`. Simplify using the standard rewrite rules.
-/
theorem wp_homotopy : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∃ H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n, (∀ z, H 0 (alt (δ 0) z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (alt (δ n)).lTensor B (H n z) + H (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z := by
  intro A _ B _ _ K _ _ ι δ hW hδ
  have huniq : ∀ (m : ℕ) (T : Type) [CommRing T] [Algebra A T] (f g : K m →ₐ[A] T),
      (∀ i, f.comp (ι m i) = g.comp (ι m i)) → f = g := by
    intro m T _ _ f g hfg
    have key := (hW m).uniq T (f : K m →+* T) (g : K m →+* T)
      (by ext a; simp)
      (fun i => by
        ext b
        exact DFunLike.congr_fun (hfg i) b)
    ext x
    exact DFunLike.congr_fun key x
  have hex : ∀ n, ∃ h : K (n + 1) →ₐ[A] B ⊗[A] K n,
      h.comp (ι (n + 1) 0) = Algebra.TensorProduct.includeLeft ∧
      ∀ i : Fin n, h.comp (ι (n + 1) i.succ) =
        (Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n).comp (ι n i) := by
    intro n
    obtain ⟨z, hz, hzi⟩ := (hW (n + 1)).ex (B ⊗[A] K n) (algebraMap A (B ⊗[A] K n))
      (Fin.cons (α := fun _ => B →+* B ⊗[A] K n)
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] K n) : B →+* B ⊗[A] K n)
        (fun i => (((Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n).comp (ι n i) :
          B →ₐ[A] B ⊗[A] K n) : B →+* B ⊗[A] K n)))
      (by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · ext a; simp
        · ext a; simp)
    refine ⟨{ z with commutes' := fun a => DFunLike.congr_fun hz a }, ?_, fun i => ?_⟩
    · ext b
      simpa using DFunLike.congr_fun (hzi 0) b
    · ext b
      simpa using DFunLike.congr_fun (hzi i.succ) b
  choose h hl hr using hex
  have h0 : ∀ n, (h n).comp (δ n 0) = (Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n) := by
    intro n
    refine huniq n _ _ _ (fun i => ?_)
    rw [AlgHom.comp_assoc, hδ, Fin.succAbove_zero]
    exact hr n i
  have hs : ∀ n (k : Fin (n + 1)), (h (n + 1)).comp (δ (n + 1) k.succ) =
      (Algebra.TensorProduct.map (AlgHom.id A B) (δ n k)).comp (h n) := by
    intro n k
    refine huniq (n + 1) _ _ _ (fun i => ?_)
    rw [AlgHom.comp_assoc, hδ, AlgHom.comp_assoc]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.succ_succAbove_zero, hl, hl]
      ext b
      simp
    · rw [Fin.succ_succAbove_succ, hr, hr, ← AlgHom.comp_assoc]
      have e := hδ n k j
      ext b
      have e' := DFunLike.congr_fun e b
      simp only [AlgHom.comp_apply] at e' ⊢
      simp [e']
  refine ⟨fun n => (h n).toLinearMap, fun z => ?_, fun n z => ?_⟩
  · have e := DFunLike.congr_fun (h0 0) z
    simpa [alt] using e
  · have e0 := DFunLike.congr_fun (h0 (n + 1)) z
    have es : ∀ k : Fin (n + 1), h (n + 1) (δ (n + 1) k.succ z) =
        ((δ n k).toLinearMap.lTensor B) (h n z) := by
      intro k
      have e := DFunLike.congr_fun (hs n k) z
      simp only [AlgHom.comp_apply] at e
      rw [e]
      generalize h n z = t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    have a1 : alt (δ (n + 1)) z = δ (n + 1) 0 z +
        ∑ k : Fin (n + 1), -((-1 : ℤ) ^ (k : ℕ) • δ (n + 1) k.succ z) := by
      simp [alt, Fin.sum_univ_succ, LinearMap.sum_apply, pow_succ]
    have a2 : ∀ t : B ⊗[A] K n, (alt (δ n)).lTensor B t =
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ((δ n k).toLinearMap.lTensor B) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [alt, LinearMap.lTensor_tmul, LinearMap.sum_apply, LinearMap.smul_apply,
          TensorProduct.tmul_sum, TensorProduct.tmul_smul]
      | add x y hx hy =>
        simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]
    show (alt (δ n)).lTensor B (h n z) + h (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z
    have e1 : h (n + 1) (δ (n + 1) 0 z) = (1 : B) ⊗ₜ[A] z := by
      simpa using e0
    rw [a1, a2, map_add, e1, map_sum, add_left_comm, ← Finset.sum_add_distrib]
    have : ∀ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ((δ n k).toLinearMap.lTensor B) (h n z) +
        h (n + 1) (-((-1 : ℤ) ^ (k : ℕ) • δ (n + 1) k.succ z)) = 0 := by
      intro k
      rw [map_neg, map_zsmul, es k, add_neg_cancel]
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    simp

end GlobalTheory.CompanionTheory.WpHomotopy
