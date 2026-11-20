import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

open Module

/- English proof (translation)
Establish `hle : Submodule.span ℤ (Set.range v) ≤ L` using `Submodule.span_le.2 (Set.range_subset_iff.2 hv)`. Establish `hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v))` using `DiscreteTopology.of_continuous_injective (f := fun x => (⟨x.1, hle x.2⟩ : L)) (continuous_subtype_val.subtype_mk _) (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc]`. Conclude with `(finrank_span_eq_card hz).symm`.
-/
theorem SublatticeExtension.linearIndependent_real_of_discrete {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] (v : ι → V) (hv : ∀ i, v i ∈ L) (hz : LinearIndependent ℤ v) :
    LinearIndependent ℝ v := by
  have hle : Submodule.span ℤ (Set.range v) ≤ L := Submodule.span_le.2 (Set.range_subset_iff.2 hv)
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) :=
    DiscreteTopology.of_continuous_injective (f := fun x => (⟨x.1, hle x.2⟩ : L))
      (continuous_subtype_val.subtype_mk _) (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc]
  exact (finrank_span_eq_card hz).symm

/- English proof (translation)
Introduce `E E' _ _ R R' φ φ' _ _ _ ψ hφ hφ' hψ hnorm`. Establish `mem : ∀ {G : Type} [AddCommGroup G] {n : ℕ} (χ : G →+ EuclideanSpace ℝ (Fin n)) (y), y ∈ imageLattice χ ↔ ∃ x, χ x = y` using `fun χ y => by`. Rewrite using `[imageLattice, ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe, AddMonoidHom.mem_range]`. Set `b` to `Free.chooseBasis ℤ (imageLattice φ')`. Set `bR` to `b.ofZLatticeBasis ℝ (imageLattice φ')`.

Set `g : _ → E'` to `fun i => Classical.choose ((mem φ' _).1 (b i).2)`. Establish `hg : ∀ i, φ' (g i) = b i` using `fun i => Classical.choose_spec ((mem φ' _).1 (b i).2)`. Set `Ψ` to `bR.constr ℝ (fun i => φ (ψ (g i)))`. Establish `hΨb : ∀ i, Ψ (b i) = φ (ψ (g i))` using `fun i => by`. Rewrite using `[← b.ofZLatticeBasis_apply ℝ (imageLattice φ') i]`.

Conclude with `bR.constr_basis ℝ _ i`. Establish `hext : ∀ x, Ψ (φ' x) = φ (ψ x)`. Introduce `x`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : _ → ℤ, x = ∑ i, c i • g i := by`. Use `⟨b.repr ⟨φ' x, (mem φ' _).2 ⟨x, rfl⟩⟩, hφ' ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Simplify using `only [map_zsmul, hg]`. Establish `hs` using `congrArg Subtype.val (b.sum_repr ⟨φ' x, (mem φ' _).2 ⟨x, rfl⟩⟩)`. Rewrite `hs` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at hs`.

Conclude with `hs.symm`. Rewrite using `[hc]`. Simplify using `only [map_sum, map_zsmul, hg, hΨb]`. Establish `hlat : ∀ y ∈ imageLattice φ', ‖Ψ y‖ ≤ ‖y‖`. Introduce `y hy`.

Take `⟨x, rfl⟩` from `(mem φ' y).1 hy`. Rewrite using `[hext]`. Conclude with `hnorm x`. Set `f : (_ → ℚ) → EuclideanSpace ℝ (Fin R')` to `fun q => bR.equivFun.symm (fun i => (q i : ℝ))`. Establish `hf : DenseRange f` using `(bR.equivFun.symm.surjective.denseRange).comp (DenseRange.piMap fun _ => Rat.denseRange_cast) (LinearMap.continuous_of_finiteDimensional bR.equivFun.symm.toLinearMap)`.

Establish `hrat : ∀ q, ‖Ψ (f q)‖ ≤ ‖f q‖`. Introduce `q`. Establish `hNpos : (0 : ℝ) < (∏ i, (q i).den : ℕ)`. Conclude with `Finset.prod_pos fun i _ => (q i).den_pos` after adjusting the coercions. Establish `hz : ∀ i, ∃ z : ℤ, ((∏ i, (q i).den : ℕ) : ℝ) * (q i : ℝ) = z`.

Introduce `i`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)`. Use `⟨k * (q i).num, ?_⟩` and prove the remaining obligations. Establish `: ((∏ i, (q i).den : ℕ) : ℚ) * q i = k * (q i).num`. Rewrite using `[hk]`.

Use `push_cast`. Rewrite using `[mul_comm ((q i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]`. Conclude with `this` after adjusting the coercions. Use `choose z hz using hz`. Establish `hmem : ((∏ i, (q i).den : ℕ) : ℝ) • f q ∈ imageLattice φ'`.

Establish `: ((∏ i, (q i).den : ℕ) : ℝ) • f q = ∑ i, z i • (b i : EuclideanSpace ℝ (Fin R'))`. Simplify using `only [f, Basis.equivFun_symm_apply, Finset.smul_sum, smul_smul, hz, ← Int.cast_smul_eq_zsmul ℝ, bR, Basis.ofZLatticeBasis_apply]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2`. Establish `h` using `hlat _ hmem`.

Rewrite `h` using `[map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hNpos.le]`. Conclude with `le_of_mul_le_mul_left h hNpos`. Establish `hall : ∀ y, ‖Ψ y‖ ≤ ‖y‖`. Establish `hS : IsClosed {y | ‖Ψ y‖ ≤ ‖y‖}` using `isClosed_le (continuous_norm.comp (LinearMap.continuous_of_finiteDimensional Ψ)) continuous_norm`. Establish `hd : Dense {y | ‖Ψ y‖ ≤ ‖y‖}` using `Dense.mono (Set.range_subset_iff.2 fun q => hrat q) hf`.

Establish `h` using `hd.closure_eq`. Rewrite `h` using `[hS.closure_eq]`. Conclude with `Set.eq_univ_iff_forall.1 h`. Establish `hvZ : LinearIndependent ℤ (fun i => φ (ψ (g i)))`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `c hc`. Establish `h0 : ∑ i, c i • g i = 0`. Apply `hψ` to reduce the goal to its premises. Apply `hφ` to reduce the goal to its premises. Simplify `hc` using `[map_sum, map_zsmul]`.

Establish `h1 : ∑ i, c i • b i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg φ' h0` as an intermediate fact. Simplify `this` using `[map_sum, map_zsmul, hg]`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent c h1`.

Establish `hvR` using `SublatticeExtension.linearIndependent_real_of_discrete (imageLattice φ) _ (fun i => (mem φ _).2 ⟨ψ (g i), rfl⟩) hvZ`. Use `⟨Ψ, hext, hall, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Establish `hc` using `Fintype.linearIndependent_iff.1 hvR (bR.equivFun y) (by rw [← bR.constr_apply_fintype ℝ]; exact hy)`.

Conclude with `bR.equivFun.injective (by ext i; simp [hc i])`.
-/
theorem SublatticeExtension.proof : SublatticeExtension.Statement := by
  intro E E' _ _ R R' φ φ' _ _ _ ψ hφ hφ' hψ hnorm
  classical
  have mem : ∀ {G : Type} [AddCommGroup G] {n : ℕ} (χ : G →+ EuclideanSpace ℝ (Fin n)) (y),
      y ∈ imageLattice χ ↔ ∃ x, χ x = y := fun χ y => by
    rw [imageLattice, ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe, AddMonoidHom.mem_range]
  let b := Free.chooseBasis ℤ (imageLattice φ')
  let bR := b.ofZLatticeBasis ℝ (imageLattice φ')
  let g : _ → E' := fun i => Classical.choose ((mem φ' _).1 (b i).2)
  have hg : ∀ i, φ' (g i) = b i := fun i => Classical.choose_spec ((mem φ' _).1 (b i).2)
  let Ψ := bR.constr ℝ (fun i => φ (ψ (g i)))
  have hΨb : ∀ i, Ψ (b i) = φ (ψ (g i)) := fun i => by
    rw [← b.ofZLatticeBasis_apply ℝ (imageLattice φ') i]; exact bR.constr_basis ℝ _ i

  have hext : ∀ x, Ψ (φ' x) = φ (ψ x) := by
    intro x
    obtain ⟨c, hc⟩ : ∃ c : _ → ℤ, x = ∑ i, c i • g i := by
      refine ⟨b.repr ⟨φ' x, (mem φ' _).2 ⟨x, rfl⟩⟩, hφ' ?_⟩
      rw [map_sum]; simp only [map_zsmul, hg]
      have hs := congrArg Subtype.val (b.sum_repr ⟨φ' x, (mem φ' _).2 ⟨x, rfl⟩⟩)
      rw [Submodule.coe_sum] at hs; simp only [Submodule.coe_smul] at hs
      exact hs.symm
    rw [hc]; simp only [map_sum, map_zsmul, hg, hΨb]

  have hlat : ∀ y ∈ imageLattice φ', ‖Ψ y‖ ≤ ‖y‖ := by
    intro y hy; obtain ⟨x, rfl⟩ := (mem φ' y).1 hy; rw [hext]; exact hnorm x
  let f : (_ → ℚ) → EuclideanSpace ℝ (Fin R') := fun q => bR.equivFun.symm (fun i => (q i : ℝ))
  have hf : DenseRange f :=
    (bR.equivFun.symm.surjective.denseRange).comp (DenseRange.piMap fun _ => Rat.denseRange_cast)
      (LinearMap.continuous_of_finiteDimensional bR.equivFun.symm.toLinearMap)
  have hrat : ∀ q, ‖Ψ (f q)‖ ≤ ‖f q‖ := by
    intro q
    have hNpos : (0 : ℝ) < (∏ i, (q i).den : ℕ) := by
      exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    have hz : ∀ i, ∃ z : ℤ, ((∏ i, (q i).den : ℕ) : ℝ) * (q i : ℝ) = z := by
      intro i
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
      refine ⟨k * (q i).num, ?_⟩
      have : ((∏ i, (q i).den : ℕ) : ℚ) * q i = k * (q i).num := by
        rw [hk]; push_cast; rw [mul_comm ((q i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
      exact_mod_cast this
    choose z hz using hz
    have hmem : ((∏ i, (q i).den : ℕ) : ℝ) • f q ∈ imageLattice φ' := by
      have : ((∏ i, (q i).den : ℕ) : ℝ) • f q = ∑ i, z i • (b i : EuclideanSpace ℝ (Fin R')) := by
        simp only [f, Basis.equivFun_symm_apply, Finset.smul_sum, smul_smul, hz,
          ← Int.cast_smul_eq_zsmul ℝ, bR, Basis.ofZLatticeBasis_apply]
      rw [this]; exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
    have h := hlat _ hmem
    rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hNpos.le] at h
    exact le_of_mul_le_mul_left h hNpos
  have hall : ∀ y, ‖Ψ y‖ ≤ ‖y‖ := by
    have hS : IsClosed {y | ‖Ψ y‖ ≤ ‖y‖} :=
      isClosed_le (continuous_norm.comp (LinearMap.continuous_of_finiteDimensional Ψ)) continuous_norm
    have hd : Dense {y | ‖Ψ y‖ ≤ ‖y‖} := Dense.mono (Set.range_subset_iff.2 fun q => hrat q) hf
    have h := hd.closure_eq
    rw [hS.closure_eq] at h
    exact Set.eq_univ_iff_forall.1 h

  have hvZ : LinearIndependent ℤ (fun i => φ (ψ (g i))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : ∑ i, c i • g i = 0 := by
      apply hψ; apply hφ; simpa [map_sum, map_zsmul] using hc
    have h1 : ∑ i, c i • b i = 0 := by
      apply Subtype.ext
      have := congrArg φ' h0
      simpa [map_sum, map_zsmul, hg] using this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c h1
  have hvR := SublatticeExtension.linearIndependent_real_of_discrete (imageLattice φ) _
    (fun i => (mem φ _).2 ⟨ψ (g i), rfl⟩) hvZ
  refine ⟨Ψ, hext, hall, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hc := Fintype.linearIndependent_iff.1 hvR (bR.equivFun y)
    (by rw [← bR.constr_apply_fintype ℝ]; exact hy)
  exact bR.equivFun.injective (by ext i; simp [hc i])

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
