import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.SBOfHalf

/- English proof (translation)
Introduce `D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT Λ hAo hAc Φ hΦ`. Use `set A : AddSubgroup (Matrix Y Y' k) := Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) with hA`. Take `⟨hsupp, k₀, hk₀, hinv, hsup⟩` from `hΦ`. Establish `hkF : ((k₀ : D.host.F)) ≠ 0` using `Nat.cast_ne_zero.2 hk₀.ne'`. Establish `hkk : ((k₀ : k)) ≠ 0`.

Establish `h` using `(map_ne_zero (p.π.comp (algebraMap D.host.F (AE D)))).2 hkF`. Simplify using `using h`. Establish `hupA : ∀ a : Matrix Y Y' k, a ∈ A ↔ p.up FS FT a ∈ Λ` using `fun a => Iff.rfl`. Establish `hnsmul : ∀ (x : Matrix Y Y' k), k₀ • x = (k₀ : k) • x` using `fun x => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul k]`.

Establish `hup_nsmul : ∀ (x : Matrix Y Y' k), p.up FS FT (k₀ • x) = k₀ • p.up FS FT x` using `fun x => map_nsmul (GlobalTheory.LocMod.Witness.upH p FS FT) k₀ x`. Set `f : Matrix Y Y' k → ℂ` to `fun x => Φ (p.up FS FT x)`. Establish `hloc : IsLocallyConstant f`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`.

Establish `hV : IsOpen {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A}` using `hAo.preimage (continuous_const_smul _)`. Establish `h0 : (x - x) ∈ {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A}`. Simplify using `only [sub_self, Set.mem_setOf_eq, smul_zero]`. Conclude with `A.zero_mem`. Establish `hn` using `(continuous_sub_right x).continuousAt.preimage_mem_nhds (hV.mem_nhds h0)`.

Use `filter_upwards [hn] with y hy`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hy`. Establish `hy' : y = x + k₀ • ((k₀ : k)⁻¹ • (y - x))`. Rewrite using `[hnsmul, smul_smul, mul_inv_cancel₀ hkk, one_smul, add_sub_cancel]`. Use `show Φ (p.up FS FT y) = Φ (p.up FS FT x)`.

Rewrite using `[hy', GlobalTheory.LocMod.Witness.up_add, hup_nsmul]`. Conclude with `hinv _ hy (GlobalTheory.LocMod.Witness.up_half p FS FT _) _`. Establish `hcpt : HasCompactSupport f`. Use `HasCompactSupport.intro (hAc.image (continuous_const_smul ((k₀ : k)⁻¹))) fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Apply `hx` to reduce the goal to its premises. Use `⟨k₀ • x, ?_, ?_⟩` and prove the remaining obligations. Use `show p.up FS FT (k₀ • x) ∈ Λ`. Rewrite using `[hup_nsmul]`. Conclude with `hsup _ hne`.

Use `show (k₀ : k)⁻¹ • k₀ • x = x`. Rewrite using `[hnsmul, smul_smul, inv_mul_cancel₀ hkk, one_smul]`. Use `⟨⟨f, hloc, hcpt⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `t`. Rewrite using `[GlobalTheory.LocMod.Witness.ext_apply]`.

Use `split_ifs with ht`. Use `show Φ (p.up FS FT (p.down FS FT t)) = Φ t`. Rewrite using `[GlobalTheory.LocMod.Witness.up_down p FS FT ht]`. Assume the negation of the conclusion as `h`. Conclude with `ht (hsupp t (Ne.symm h))`.
-/
theorem exists_sb_ext_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  intro D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT Λ hAo hAc Φ hΦ
  classical
  set A : AddSubgroup (Matrix Y Y' k) := Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) with hA
  obtain ⟨hsupp, k₀, hk₀, hinv, hsup⟩ := hΦ
  have hkF : ((k₀ : D.host.F)) ≠ 0 := Nat.cast_ne_zero.2 hk₀.ne'
  have hkk : ((k₀ : k)) ≠ 0 := by
    have h := (map_ne_zero (p.π.comp (algebraMap D.host.F (AE D)))).2 hkF
    simpa using h
  have hupA : ∀ a : Matrix Y Y' k, a ∈ A ↔ p.up FS FT a ∈ Λ := fun a => Iff.rfl
  have hnsmul : ∀ (x : Matrix Y Y' k), k₀ • x = (k₀ : k) • x := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k]
  have hup_nsmul : ∀ (x : Matrix Y Y' k), p.up FS FT (k₀ • x) = k₀ • p.up FS FT x := fun x =>
    map_nsmul (GlobalTheory.LocMod.Witness.upH p FS FT) k₀ x
  let f : Matrix Y Y' k → ℂ := fun x => Φ (p.up FS FT x)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hV : IsOpen {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} :=
      hAo.preimage (continuous_const_smul _)
    have h0 : (x - x) ∈ {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} := by
      simp only [sub_self, Set.mem_setOf_eq, smul_zero]; exact A.zero_mem
    have hn := (continuous_sub_right x).continuousAt.preimage_mem_nhds (hV.mem_nhds h0)
    filter_upwards [hn] with y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
    have hy' : y = x + k₀ • ((k₀ : k)⁻¹ • (y - x)) := by
      rw [hnsmul, smul_smul, mul_inv_cancel₀ hkk, one_smul, add_sub_cancel]
    show Φ (p.up FS FT y) = Φ (p.up FS FT x)
    rw [hy', GlobalTheory.LocMod.Witness.up_add, hup_nsmul]
    exact hinv _ hy (GlobalTheory.LocMod.Witness.up_half p FS FT _) _
  have hcpt : HasCompactSupport f := by
    refine HasCompactSupport.intro (hAc.image (continuous_const_smul ((k₀ : k)⁻¹))) fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨k₀ • x, ?_, ?_⟩
    · show p.up FS FT (k₀ • x) ∈ Λ
      rw [hup_nsmul]; exact hsup _ hne
    · show (k₀ : k)⁻¹ • k₀ • x = x
      rw [hnsmul, smul_smul, inv_mul_cancel₀ hkk, one_smul]
  refine ⟨⟨f, hloc, hcpt⟩, ?_⟩
  funext t
  rw [GlobalTheory.LocMod.Witness.ext_apply]
  split_ifs with ht
  · show Φ (p.up FS FT (p.down FS FT t)) = Φ t
    rw [GlobalTheory.LocMod.Witness.up_down p FS FT ht]
  · by_contra h
    exact ht (hsupp t (Ne.symm h))

end GlobalTheory.SBOfHalf
