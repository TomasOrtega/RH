import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
import BuildAid.D3
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

/- English proof (translation)
Introduce `p q hpq`. Take `⟨⟨a, b⟩, rfl⟩` from `finProdFinEquiv.surjective p`. Take `⟨⟨a', b'⟩, rfl⟩` from `finProdFinEquiv.surjective q`. Simplify using `only [Equiv.symm_apply_apply]`. Establish `h1 : (b : ℕ) + h * a < b' + h * a'` using `hpq`.

Break down `lt_trichotomy a a' with hlt | rfl | hgt` into its components or cases. Conclude with `Sigma.Lex.left _ _ hlt`. Conclude with `Sigma.Lex.right _ _ (show b < b' from by`. Rewrite using `[Fin.lt_def]`. Use the proof step `omega)`.

It suffices to derive a contradiction. Establish `h2 : (a' : ℕ) + 1 ≤ a` using `hgt`. Establish `h3` using `Nat.mul_le_mul_left h h2`. Establish `h4` using `b'.2`. Rewrite `h3` using `[Nat.mul_add, Nat.mul_one]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem flat_strictMono (d h : ℕ) : StrictMono (fun p : Fin (d * h) =>
    (toLex ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2⟩ : Σₗ _ : Fin d, Fin h)) := by
  intro p q hpq
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨a', b'⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [Equiv.symm_apply_apply]
  have h1 : (b : ℕ) + h * a < b' + h * a' := hpq
  rcases lt_trichotomy a a' with hlt | rfl | hgt
  · exact Sigma.Lex.left _ _ hlt
  · exact Sigma.Lex.right _ _ (show b < b' from by
      rw [Fin.lt_def]; omega)
  · exfalso
    have h2 : (a' : ℕ) + 1 ≤ a := hgt
    have h3 := Nat.mul_le_mul_left h h2
    have h4 := b'.2
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega

/- English proof (translation)
Introduce `k _ _ _ _ d h y N M hN hM hM'`. Establish `hφ` using `GlobalTheory.SmGL.Stages.stages_equiv (k := k) d N (fun _ => h) (fun a b => (y a b).1) (fun a => stdBlocks (fun b => (y a b).1) (hN a)) _ (fun a b => (y a b).rep) (Fin M) (stdBlocks N hM)`. Take `⟨E0, ⟨φ⟩⟩` from `hφ`. Set `F : Fin (d * h) ≃ Σₗ _ : Fin d, Fin h` to `finProdFinEquiv.symm.trans ((Equiv.sigmaEquivProd (Fin d) (Fin h)).symm.trans toLex)`. Set `E : (Σ p : Fin (d * h), Fin (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) ≃ Fin M` to `(Equiv.sigmaCongrLeft (β := fun c : Σₗ _ : Fin d, Fin h => Fin (y (ofLex c).1 (ofLex c).2).1) F).trans E0`.

Establish `hψ` using `GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) F (flat_strictMono d h) F.surjective E0 E (fun _ _ => rfl) fun c => (y (ofLex c).1 (ofLex c).2).rep`. Take `⟨ψ⟩` from `hψ`. Establish `hχ` using `GlobalTheory.ProdReorder.multiProd_placing (k := k) E (stdBlocks (fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) hM') fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).rep`. Take `⟨χ⟩` from `hχ`. Conclude with `⟨φ.trans (ψ.trans χ)⟩`.
-/
theorem _root_.GlobalTheory.T.parabolicInduction_in_stages_product_of_products : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d h : ℕ) (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM')) := by
  intro k _ _ _ _ d h y N M hN hM hM'
  have hφ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) d N (fun _ => h) (fun a b => (y a b).1)
    (fun a => stdBlocks (fun b => (y a b).1) (hN a)) _ (fun a b => (y a b).rep) (Fin M) (stdBlocks N hM)
  obtain ⟨E0, ⟨φ⟩⟩ := hφ
  let F : Fin (d * h) ≃ Σₗ _ : Fin d, Fin h :=
    finProdFinEquiv.symm.trans ((Equiv.sigmaEquivProd (Fin d) (Fin h)).symm.trans toLex)
  let E : (Σ p : Fin (d * h), Fin (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) ≃ Fin M :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ _ : Fin d, Fin h => Fin (y (ofLex c).1 (ofLex c).2).1) F).trans E0
  have hψ := GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) F (flat_strictMono d h) F.surjective E0 E
    (fun _ _ => rfl) fun c => (y (ofLex c).1 (ofLex c).2).rep
  obtain ⟨ψ⟩ := hψ
  have hχ := GlobalTheory.ProdReorder.multiProd_placing (k := k) E
    (stdBlocks (fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) hM')
    fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).rep
  obtain ⟨χ⟩ := hχ
  exact ⟨φ.trans (ψ.trans χ)⟩
