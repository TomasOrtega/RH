import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct Matrix

namespace Formalism.L2.SG.Pf.RedExists0Pf

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf

/- English proof (translation)
Introduce `I w p hp hcard m hm x hx`. Substitute `hm` using the available equality. Establish `: NeZero p` using `⟨hp.ne_zero⟩`. Take `⟨b, hb⟩` from `exists_redBasis I w hp hcard`. Establish `hx' : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf` using `hx`.

Establish `hxi : x⁻¹ ∈ I.Kset` using `(Formalism.UG.stabGL I.Lf).inv_mem hx`. Establish `hxi' : ∀ v, v ∈ I.Lf ↔ I.fmat x⁻¹ *ᵥ v ∈ I.Lf` using `hxi`. Use `choose c hc using fun i => coords I w hp hcard hb ((hx' _).1 (DictLat.iv_mem I (hb.1 i)))`. Use `choose c' hc' using fun i => coords I w hp hcard hb ((hxi' _).1 (DictLat.iv_mem I (hb.1 i)))`. Set `M : Matrix (Fin I.n) (Fin I.n) (ZMod p)` to `Matrix.of fun j i => ((c i j : ℤ) : ZMod p)`.

Set `N : Matrix (Fin I.n) (Fin I.n) (ZMod p)` to `Matrix.of fun k j => ((c' j k : ℤ) : ZMod p)`. Establish `hzs : ∀ (z : ℤ) {v : Fin I.n → I.E ⊗[I.F] Af I.F}, v ∈ lamAf (F` using `I.F) (wLat0 I w) → (z : I.E ⊗[I.F] Af I.F) • v ∈ lamAf (F := I.F) (wLat0 I w) := fun z v hv => by`. Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `zsmul_mem hv z`. Establish `hdiv : ∀ i k, (p : ℤ) ∣ (1 : Matrix (Fin I.n) (Fin I.n) ℤ) i k - ∑ j, c i j * c' j k`.

Introduce `i`. Establish `hW : iv I (b i) - ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • ∑ k, (c' j k : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ lamAf (F` using `I.F) (wLat0 I w) := by`. Establish `h1` using `stab_w I w hxi (hc i)`. Establish `h2 : ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ iv I (b j) - ∑ k, (c' j k : I.E ⊗[I.F] Af I.F) • iv I (b k)) ∈ lamAf (F` using `I.F) (wLat0 I w) := Submodule.sum_mem _ fun j _ => hzs _ (hc' j)`. Establish `h3` using `Submodule.add_mem _ h1 h2`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_sum]`. Simplify using `only [Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Establish `hW2 : iv I (b i - ∑ k, ((∑ j, c i j * c' j k : ℤ) : I.E) • b k) ∈ lamAf (F` using `I.F) (wLat0 I w) := by`.

Rewrite using `[iv_lin]`. Use `hW using 2` and compare the differences between its conclusion and the goal. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [← Finset.sum_smul, Int.cast_sum, Int.cast_mul]`. Establish `h4` using `inter I w hW2`. Introduce `k`. Establish `h5 : ∑ k, (((1 : Matrix (Fin I.n) (Fin I.n) ℤ) i k - ∑ j, c i j * c' j k : ℤ) : I.E) • b k ∈ wLat0 I w`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Int.cast_sub, sub_smul, Finset.sum_sub_distrib]`. Use `congr 1`. Simplify using `[Matrix.one_apply]`. Conclude with `redBasis_indep I w hp hcard hb _ h5 k`. Establish `hNM : N * M = 1`.

Use extensionality with `k i`. Establish `h` using `hdiv i k`. Rewrite `h` using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at h`. Rewrite `h` using `[sub_eq_zero]`.

Simplify using `only [N, M, Matrix.mul_apply, Matrix.of_apply]`. Establish `e : ∑ j, ((c' j k : ℤ) : ZMod p) * ((c i j : ℤ) : ZMod p) = ∑ j, ((c i j : ℤ) : ZMod p) * ((c' j k : ℤ) : ZMod p)` using `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Rewrite using `[e, ← h]`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hik, Matrix.one_apply_ne (Ne.symm hik)]`. Establish `hMN : M * N = 1` using `mul_eq_one_comm.1 hNM`. Use `⟨⟨M, N, hMN, hNM⟩, b, hb, fun i => ?_⟩` and prove the remaining obligations. Use `show I.fmat x *ᵥ iv I (b i) - ∑ j, ((((M j i).val : ℕ)) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ lamAf (F := I.F) (wLat0 I w)`.

Establish `hS : (∑ j, ((((((c i j : ℤ) : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) - ((c i j : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j))) ∈ lamAf (F` using `I.F) (wLat0 I w) := Submodule.sum_mem _ fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)`. Establish `key` using `Submodule.sub_mem _ (hc i) hS`. Use `key using 1` and compare the differences between its conclusion and the goal. Simplify using `only [M, Matrix.of_apply, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem reduction_exists : Formalism.L2.SG.Pf.RowDictPf.RedExists0 := by
  intro I w p hp hcard m hm x hx
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨b, hb⟩ := exists_redBasis I w hp hcard
  have hx' : ∀ v, v ∈ I.Lf ↔ I.fmat x *ᵥ v ∈ I.Lf := hx
  have hxi : x⁻¹ ∈ I.Kset := (Formalism.UG.stabGL I.Lf).inv_mem hx
  have hxi' : ∀ v, v ∈ I.Lf ↔ I.fmat x⁻¹ *ᵥ v ∈ I.Lf := hxi
  choose c hc using fun i => coords I w hp hcard hb ((hx' _).1 (DictLat.iv_mem I (hb.1 i)))
  choose c' hc' using fun i => coords I w hp hcard hb ((hxi' _).1 (DictLat.iv_mem I (hb.1 i)))
  let M : Matrix (Fin I.n) (Fin I.n) (ZMod p) := Matrix.of fun j i => ((c i j : ℤ) : ZMod p)
  let N : Matrix (Fin I.n) (Fin I.n) (ZMod p) := Matrix.of fun k j => ((c' j k : ℤ) : ZMod p)
  have hzs : ∀ (z : ℤ) {v : Fin I.n → I.E ⊗[I.F] Af I.F}, v ∈ lamAf (F := I.F) (wLat0 I w) →
      (z : I.E ⊗[I.F] Af I.F) • v ∈ lamAf (F := I.F) (wLat0 I w) := fun z v hv => by
    rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem hv z
  have hdiv : ∀ i k, (p : ℤ) ∣ (1 : Matrix (Fin I.n) (Fin I.n) ℤ) i k - ∑ j, c i j * c' j k := by
    intro i
    have hW : iv I (b i) - ∑ j, (c i j : I.E ⊗[I.F] Af I.F) •
        ∑ k, (c' j k : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ lamAf (F := I.F) (wLat0 I w) := by
      have h1 := stab_w I w hxi (hc i)
      have h2 : ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ iv I (b j) -
          ∑ k, (c' j k : I.E ⊗[I.F] Af I.F) • iv I (b k)) ∈ lamAf (F := I.F) (wLat0 I w) :=
        Submodule.sum_mem _ fun j _ => hzs _ (hc' j)
      have h3 := Submodule.add_mem _ h1 h2
      convert h3 using 1
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    have hW2 : iv I (b i - ∑ k, ((∑ j, c i j * c' j k : ℤ) : I.E) • b k) ∈
        lamAf (F := I.F) (wLat0 I w) := by
      rw [iv_lin]
      convert hW using 2
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [← Finset.sum_smul, Int.cast_sum, Int.cast_mul]
    have h4 := inter I w hW2
    intro k
    have h5 : ∑ k, (((1 : Matrix (Fin I.n) (Fin I.n) ℤ) i k - ∑ j, c i j * c' j k : ℤ) : I.E) • b k ∈
        wLat0 I w := by
      convert h4 using 1
      simp only [Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    exact redBasis_indep I w hp hcard hb _ h5 k
  have hNM : N * M = 1 := by
    ext k i
    have h := hdiv i k
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    push_cast at h
    rw [sub_eq_zero] at h
    simp only [N, M, Matrix.mul_apply, Matrix.of_apply]
    have e : ∑ j, ((c' j k : ℤ) : ZMod p) * ((c i j : ℤ) : ZMod p) =
        ∑ j, ((c i j : ℤ) : ZMod p) * ((c' j k : ℤ) : ZMod p) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e, ← h]
    by_cases hik : i = k
    · subst hik; simp
    · simp [Matrix.one_apply_ne hik, Matrix.one_apply_ne (Ne.symm hik)]
  have hMN : M * N = 1 := mul_eq_one_comm.1 hNM
  refine ⟨⟨M, N, hMN, hNM⟩, b, hb, fun i => ?_⟩
  show I.fmat x *ᵥ iv I (b i) - ∑ j, ((((M j i).val : ℕ)) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈
    lamAf (F := I.F) (wLat0 I w)
  have hS : (∑ j, ((((((c i j : ℤ) : ZMod p)).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ((c i j : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j))) ∈ lamAf (F := I.F) (wLat0 I w) :=
    Submodule.sum_mem _ fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)
  have key := Submodule.sub_mem _ (hc i) hS
  convert key using 1
  simp only [M, Matrix.of_apply, Finset.sum_sub_distrib]
  abel

end Formalism.L2.SG.Pf.RedExists0Pf
