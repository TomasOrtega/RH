import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.SuppFirstBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[val_emb₂]`. Use `conv_lhs => rw [← fromBlocks_toBlocks z]`. Simplify using `[fromBlocks_multiply]`.
-/
theorem toBlocks₁₁_mul_diag {A D E : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k) :
    (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₁ = z.toBlocks₁₁ * x.val := by
  rw [val_emb₂]
  conv_lhs => rw [← fromBlocks_toBlocks z]
  simp [fromBlocks_multiply]

/- English proof (translation)
Set `N : Matrix A A 𝒪[k]` to `fun i j => ⟨M i j, hM i j⟩`. Establish `hN : (algebraMap 𝒪[k] k).mapMatrix N = M` using `rfl`. Establish `hu : IsUnit N.det`. Rewrite using `[(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one, RingHom.map_det, hN]`. Conclude with `hd`.

Use `⟨((Matrix.isUnit_iff_isUnit_det N).2 hu).unit, ?_⟩` and prove the remaining obligations. Conclude with `hN`.
-/
theorem exists_GL_of_int {A : Type} [Fintype A] [DecidableEq A] (M : Matrix A A k)
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hd : valuation k M.det = 1) :
    ∃ g : GL A 𝒪[k], (GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) g : Matrix A A k) = M := by
  let N : Matrix A A 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have hN : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
  have hu : IsUnit N.det := by
    rw [(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one, RingHom.map_det, hN]
    exact hd
  refine ⟨((Matrix.isUnit_iff_isUnit_det N).2 hu).unit, ?_⟩
  exact hN

end GlobalTheory.SuppFirstBlock

open GlobalTheory.SuppFirstBlock in
/- English proof (translation)
Introduce `k _ _ _ _ A D E _ _ _ _ _ _ z x y hz hw`. Establish `hb` using `toBlocks₁₁_mul_diag z x y`. Take `⟨g, hg⟩` from `exists_GL_of_int z.toBlocks₁₁ (fun i j => hz.1 _ _) hz.2.1`. Take `⟨h, hh⟩` from `exists_GL_of_int (z.toBlocks₁₁ * x.val) (fun i j => by rw [← hb]; exact hw.1 _ _) (by rw [← hb]; exact hw.2.1)`. Establish `key : GeneralLinearGroup.map (n` using `A) (algebraMap 𝒪[k] k) g * x = GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) h := by ext1`.

Rewrite using `[Units.val_mul, hg, hh]`. Use `⟨g⁻¹ * h, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, ← key, inv_mul_cancel_left]`.
-/
theorem GlobalTheory.SuppFirstBlock.mem_KO_of_inSupp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (z : Matrix (A ⊕ E) (A ⊕ D) k) (x : GL A k) (y : GL D k),
    InSupp z → InSupp (z * (emb₂ k (Equiv.refl (A ⊕ D)) (x, y) : Matrix (A ⊕ D) (A ⊕ D) k)) → x ∈ KO k A := by
  intro k _ _ _ _ A D E _ _ _ _ _ _ z x y hz hw
  have hb := toBlocks₁₁_mul_diag z x y
  obtain ⟨g, hg⟩ := exists_GL_of_int z.toBlocks₁₁ (fun i j => hz.1 _ _) hz.2.1
  obtain ⟨h, hh⟩ := exists_GL_of_int (z.toBlocks₁₁ * x.val)
    (fun i j => by rw [← hb]; exact hw.1 _ _) (by rw [← hb]; exact hw.2.1)
  have key : GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) g * x =
      GeneralLinearGroup.map (n := A) (algebraMap 𝒪[k] k) h := by
    ext1
    rw [Units.val_mul, hg, hh]
  refine ⟨g⁻¹ * h, ?_⟩
  rw [map_mul, map_inv, ← key, inv_mul_cancel_left]
