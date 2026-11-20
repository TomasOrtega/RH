import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
open ValuativeRel Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SymChain.SymData
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

/- English proof (translation)
Introduce `k _ _ _ _ s κ S x hx`. Take `⟨hxK, hpat⟩` from `(mem_J_iff_pattern k s κ S x).1 hx`. Use `set M : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) k := fun a b => if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b with hMdef`. Establish `hMax : MaxM (M - x.val)`. Introduce `a b`.

Use `show valuation k ((if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b) - x.val a b) < 1`. Use `split_ifs with h`. Simplify using the standard rewrite rules. Rewrite using `[Valuation.map_sub_swap]`. Conclude with `hpat a b h`.

Take `⟨u, hu, hMu⟩` from `exists_mul_KOne hxK hMax`. Establish `hMK : x * u ∈ KO k _` using `mul_mem hxK (KOne_le_KO hu)`. Establish `hpatM : ∀ a b, ¬ FreeTop S.ρ a b → (x * u).val a b = (1 : Matrix _ _ k) a b`. Introduce `a b h`. Rewrite using `[hMu]`.

Simplify using `[hMdef, h]`. Take `⟨n, hn, γ, hγ, e⟩` from `GlobalTheory.SymPattern.exists_of_pat S.ρ (x * u) hpatM`. Establish `hγv : ∀ i j, γ.val i j = (x * u).val (Sum.inl i) (Sum.inl j)`. Introduce `i j`. Rewrite using `[e, Units.val_mul, Radical.embX_val, GlobalTheory.SymPattern.mul_fromBlocks_inl]`.

Establish `e1 : ∀ t, n.val (Sum.inl i) (Sum.inl t) = (1 : Matrix (Fin κ) (Fin κ) k) i t`. Introduce `t`. Rewrite using `[hn _ _ (by simp [lev])]`. Simplify using `[Matrix.one_apply]`. Simplify using `only [e1]`.

Rewrite using `[← Matrix.mul_apply, Matrix.one_mul]`. Establish `hγint : ∀ i j, γ.val i j ∈ 𝒪[k]` using `fun i j => by`. Rewrite using `[hγv]`. Conclude with `intM_of_mem_KO hMK _ _`. Establish `hγK : γ ∈ KO k (Fin κ)`.

Set `A₀ : Matrix (Fin κ) (Fin κ) 𝒪[k]` to `fun i j => ⟨γ.val i j, hγint i j⟩`. Establish `hmap : (algebraMap 𝒪[k] k).mapMatrix A₀ = γ.val` using `by ext i j; rfl`. Establish `hdet1 : γ.val.det = 1` using `Radical.Uni.det (b := Fin.val) hγ`. Establish `hdet : A₀.det = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `RingHom.map_det (algebraMap 𝒪[k] k) A₀` as an intermediate fact. Rewrite `this` using `[hmap, hdet1]`. Simplify using `using this`. Use `⟨Matrix.nonsingInvUnit A₀ (by rw [hdet]; exact isUnit_one), ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `hembK : embX (s + 1) γ ∈ KO k _`. Use `mem_KO.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Radical.embX_val]`. Conclude with `intM_fromBlocks.2 ⟨intM_of_mem_KO hγK, intM_zero, intM_zero, intM_one⟩`.

Rewrite using `[← map_inv, Radical.embX_val]`. Conclude with `intM_fromBlocks.2 ⟨intM_of_mem_KO (inv_mem hγK), intM_zero, intM_zero, intM_one⟩`. Establish `hnK : n ∈ KO k _`. Establish `: n = (x * u) * (embX (s + 1) γ)⁻¹` using `by rw [e]; group`. Rewrite using `[this]`.

Conclude with `mul_mem hMK (inv_mem hembK)`. Use `⟨n, γ, (Radical.mem_N_iff n).2 hn, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(mem_J_iff_pattern k s κ S n).2 ⟨hnK, fun a b hab => ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.SymPattern.pat_of_mul S.ρ n hn 1 (fun r s _ => rfl) a b hab`. Rewrite `h1` using `[map_one, mul_one]`.

Rewrite using `[h1, sub_self, map_zero]`. Conclude with `zero_lt_one`. Use `(mem_J_iff_pattern k s κ S _).2 ⟨hembK, fun a b hab => ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.SymPattern.pat_of_mul S.ρ 1 (fun r s _ => rfl) γ hγ a b hab`. Rewrite `h1` using `[one_mul]`.

Rewrite using `[h1, sub_self, map_zero]`. Conclude with `zero_lt_one`. Rewrite using `[← e, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]`. Conclude with `inv_mem hu`.
-/
theorem exists_N_embX_inv_mul_mem_KOne :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : GlobalTheory.SymChain.SymData k s κ), ∀ x ∈ S.P.J, ∃ (n : GL (Fin κ ⊕ Fin (s + 1)) k) (γ : GL (Fin κ) k),
        n ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) ∧ n ∈ S.P.J ∧ GlobalTheory.RootEx.embX (s + 1) γ ∈ S.P.J ∧
        (n * GlobalTheory.RootEx.embX (s + 1) γ)⁻¹ * x ∈ GlobalTheory.SplitWeil.KOne k (Fin κ ⊕ Fin (s + 1)) := by
  intro k _ _ _ _ s κ S x hx
  obtain ⟨hxK, hpat⟩ := (mem_J_iff_pattern k s κ S x).1 hx
  set M : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) k :=
    fun a b => if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b with hMdef
  have hMax : MaxM (M - x.val) := by
    intro a b
    show valuation k ((if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b) - x.val a b) < 1
    split_ifs with h
    · simp
    · rw [Valuation.map_sub_swap]; exact hpat a b h
  obtain ⟨u, hu, hMu⟩ := exists_mul_KOne hxK hMax
  have hMK : x * u ∈ KO k _ := mul_mem hxK (KOne_le_KO hu)
  have hpatM : ∀ a b, ¬ FreeTop S.ρ a b → (x * u).val a b = (1 : Matrix _ _ k) a b := by
    intro a b h; rw [hMu]; simp [hMdef, h]
  obtain ⟨n, hn, γ, hγ, e⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ (x * u) hpatM

  have hγv : ∀ i j, γ.val i j = (x * u).val (Sum.inl i) (Sum.inl j) := by
    intro i j
    rw [e, Units.val_mul, Radical.embX_val, GlobalTheory.SymPattern.mul_fromBlocks_inl]
    have e1 : ∀ t, n.val (Sum.inl i) (Sum.inl t) = (1 : Matrix (Fin κ) (Fin κ) k) i t := by
      intro t
      rw [hn _ _ (by simp [lev])]
      simp [Matrix.one_apply]
    simp only [e1]
    rw [← Matrix.mul_apply, Matrix.one_mul]
  have hγint : ∀ i j, γ.val i j ∈ 𝒪[k] := fun i j => by
    rw [hγv]; exact intM_of_mem_KO hMK _ _

  have hγK : γ ∈ KO k (Fin κ) := by
    let A₀ : Matrix (Fin κ) (Fin κ) 𝒪[k] := fun i j => ⟨γ.val i j, hγint i j⟩
    have hmap : (algebraMap 𝒪[k] k).mapMatrix A₀ = γ.val := by ext i j; rfl
    have hdet1 : γ.val.det = 1 := Radical.Uni.det (b := Fin.val) hγ
    have hdet : A₀.det = 1 := by
      apply Subtype.ext
      have := RingHom.map_det (algebraMap 𝒪[k] k) A₀
      rw [hmap, hdet1] at this
      simpa using this
    refine ⟨Matrix.nonsingInvUnit A₀ (by rw [hdet]; exact isUnit_one), ?_⟩
    ext i j
    rfl
  have hembK : embX (s + 1) γ ∈ KO k _ := by
    refine mem_KO.2 ⟨?_, ?_⟩
    · rw [Radical.embX_val]
      exact intM_fromBlocks.2 ⟨intM_of_mem_KO hγK, intM_zero, intM_zero, intM_one⟩
    · rw [← map_inv, Radical.embX_val]
      exact intM_fromBlocks.2 ⟨intM_of_mem_KO (inv_mem hγK), intM_zero, intM_zero, intM_one⟩
  have hnK : n ∈ KO k _ := by
    have : n = (x * u) * (embX (s + 1) γ)⁻¹ := by rw [e]; group
    rw [this]; exact mul_mem hMK (inv_mem hembK)
  refine ⟨n, γ, (Radical.mem_N_iff n).2 hn, ?_, ?_, ?_⟩
  · refine (mem_J_iff_pattern k s κ S n).2 ⟨hnK, fun a b hab => ?_⟩
    have h1 := GlobalTheory.SymPattern.pat_of_mul S.ρ n hn 1 (fun r s _ => rfl) a b hab
    rw [map_one, mul_one] at h1
    rw [h1, sub_self, map_zero]; exact zero_lt_one
  · refine (mem_J_iff_pattern k s κ S _).2 ⟨hembK, fun a b hab => ?_⟩
    have h1 := GlobalTheory.SymPattern.pat_of_mul S.ρ 1 (fun r s _ => rfl) γ hγ a b hab
    rw [one_mul] at h1
    rw [h1, sub_self, map_zero]; exact zero_lt_one
  · rw [← e, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem hu

end GlobalTheory.SymChain.SymData
