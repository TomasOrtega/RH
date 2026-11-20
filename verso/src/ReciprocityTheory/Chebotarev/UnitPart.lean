import ReciprocityTheory.Chebotarev.Ucoord

open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Unfold `uphi`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `Tent_nonneg _`.
-/
theorem uphi_nonneg (x : mixedSpace E) : 0 ≤ uphi x := by
  unfold uphi
  split_ifs
  · exact le_rfl
  · exact Tent_nonneg _

/- English proof (translation)
Unfold `uphi`. Use `split_ifs`. Conclude with `zero_le_one`. Conclude with `Tent_le_one _`.
-/
theorem uphi_le_one (x : mixedSpace E) : uphi x ≤ 1 := by
  unfold uphi
  split_ifs
  · exact zero_le_one
  · exact Tent_le_one _

/- English proof (translation)
Unfold `uphi`. Rewrite using `[if_pos hx]`.
-/
theorem uphi_of_norm_eq_zero {x : mixedSpace E} (hx : mixedEmbedding.norm x = 0) : uphi x = 0 := by
  unfold uphi
  rw [if_pos hx]

/- English proof (translation)
Unfold `uphi ucoord`. Rewrite using `[norm_unit_smul, logMap_torsion_smul x hζ]`.
-/
theorem uphi_torsion_smul {ζ : (𝓞 E)ˣ} (hζ : ζ ∈ torsion E) (x : mixedSpace E) :
    uphi (ζ • x) = uphi x := by
  unfold uphi ucoord
  rw [norm_unit_smul, logMap_torsion_smul x hζ]

/- English proof (translation)
Rewrite using `[ofMul_prod, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ofMul_zpow, map_zsmul, logEmbedding_fundSystem, Int.cast_smul_eq_zsmul]`.
-/
theorem logEmbedding_prod_fundSystem (f : Fin (rank E) → ℤ) :
    logEmbedding E (Additive.ofMul (∏ i, (fundSystem E i) ^ (f i))) =
      ∑ i, (f i : ℝ) • ((basisUnitLattice E i : unitLattice E) : logSpace E) := by
  rw [ofMul_prod, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofMul_zpow, map_zsmul, logEmbedding_fundSystem, Int.cast_smul_eq_zsmul]

/- English proof (translation)
Unfold `ucoord`. Rewrite using `[logMap_unit_smul _ hx, logEmbedding_prod_fundSystem, map_add]`. Establish `: ∀ j, ((basisUnitLattice E j : unitLattice E) : logSpace E) = (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E) j` using `fun j => (Module.Basis.ofZLatticeBasis_apply ℝ (unitLattice E) (basisUnitLattice E) j).symm`. Repeatedly rewrite using `[this, map_sum, map_smul, Module.Basis.repr_self]`. Simplify using `[Finsupp.single_apply, add_comm]`.
-/
theorem ucoord_prod_fundSystem_smul (f : Fin (rank E) → ℤ) (x : mixedSpace E)
    (hx : mixedEmbedding.norm x ≠ 0) (i : Fin (rank E)) :
    ucoord ((∏ i, (fundSystem E i) ^ (f i)) • x) i = ucoord x i + f i := by
  unfold ucoord
  rw [logMap_unit_smul _ hx, logEmbedding_prod_fundSystem, map_add]
  have : ∀ j, ((basisUnitLattice E j : unitLattice E) : logSpace E) =
      (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E) j := fun j =>
    (Module.Basis.ofZLatticeBasis_apply ℝ (unitLattice E) (basisUnitLattice E) j).symm
  simp_rw [this, map_sum, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, add_comm]

/- English proof (translation)
Establish `h1 : HasSum (fun _ : α => (1 : ℝ)) (Fintype.card α)`. Simplify using `using hasSum_fintype (fun _ : α => (1 : ℝ))`. Establish `hs : Summable (fun p : α × β => (fun _ : α => (1 : ℝ)) p.1 * g p.2)` using `Summable.mul_of_nonneg h1.summable hg.summable (fun _ => zero_le_one) hg0`. Simplify `h1.mul hg hs` using `only [one_mul]`.
-/
theorem hasSum_snd_of_fintype {α β : Type*} [Fintype α] {g : β → ℝ} (hg0 : ∀ b, 0 ≤ g b) {t : ℝ}
    (hg : HasSum g t) : HasSum (fun p : α × β => g p.2) (Fintype.card α * t) := by
  have h1 : HasSum (fun _ : α => (1 : ℝ)) (Fintype.card α) := by
    simpa using hasSum_fintype (fun _ : α => (1 : ℝ))
  have hs : Summable (fun p : α × β => (fun _ : α => (1 : ℝ)) p.1 * g p.2) :=
    Summable.mul_of_nonneg h1.summable hg.summable (fun _ => zero_le_one) hg0
  simpa only [one_mul] using h1.mul hg hs

/- English proof (translation)
Establish `: Fintype (torsion E)` using `Fintype.ofFinite _`. Establish `h2 : HasSum (fun n : Fin (rank E) → ℤ => Tent (fun i => y i + n i)) 1` using `hasSum_Tent_add_int y`. Establish `h` using `hasSum_snd_of_fintype (α := torsion E) (g := fun n : Fin (rank E) → ℤ => Tent (fun i => y i + n i)) (fun n => Tent_nonneg _) h2`. Rewrite `h` using `[mul_one, ← Nat.card_eq_fintype_card]`. Then use the resulting hypothesis.
-/
theorem hasSum_Tent_torsion_prod (y : Fin (rank E) → ℝ) :
    HasSum (fun p : torsion E × (Fin (rank E) → ℤ) => Tent (fun i => y i + p.2 i))
      (torsionOrder E : ℝ) := by
  have : Fintype (torsion E) := Fintype.ofFinite _
  have h2 : HasSum (fun n : Fin (rank E) → ℤ => Tent (fun i => y i + n i)) 1 := hasSum_Tent_add_int y
  have h := hasSum_snd_of_fintype (α := torsion E)
    (g := fun n : Fin (rank E) → ℤ => Tent (fun i => y i + n i)) (fun n => Tent_nonneg _) h2
  rwa [mul_one, ← Nat.card_eq_fintype_card] at h

/- English proof (translation)
Set `e : torsion E × (Fin (rank E) → ℤ) → (𝓞 E)ˣ` to `fun p => (p.1 : (𝓞 E)ˣ) * ∏ i, (fundSystem E i) ^ (p.2 i)`. Establish `he : Function.Bijective e`. Use `⟨fun p q h => ?_, fun u => ?_⟩` and prove the remaining obligations. Take `⟨c, -, hc⟩` from `exist_unique_eq_mul_prod E (e p)`. Conclude with `(hc p rfl).trans (hc q h).symm`.

Take `⟨c, hc, -⟩` from `exist_unique_eq_mul_prod E u`. Conclude with `⟨c, hc.symm⟩`. Set `eq` to `Equiv.ofBijective e he`. Rewrite using `[← eq.hasSum_iff]`. Establish `hval : ∀ p : torsion E × (Fin (rank E) → ℤ), uphi (eq p • x) = (fun _ : torsion E => (1 : ℝ)) p.1 * (fun n : Fin (rank E) → ℤ => Tent (fun i => ucoord x i + n i)) p.2`.

Introduce `p`. Establish `h0 : eq p • x = (p.1 : (𝓞 E)ˣ) • ((∏ i, (fundSystem E i) ^ (p.2 i)) • x)` using `mul_smul _ _ _`. Rewrite using `[h0, uphi_torsion_smul p.1.2, one_mul]`. Unfold `uphi`. Rewrite using `[if_neg (by rwa [norm_unit_smul])]`.

Conclude with `congrArg Tent (funext fun i => ucoord_prod_fundSystem_smul p.2 x hx i)`. Establish `key : (fun u : (𝓞 E)ˣ => uphi (u • x)) ∘ eq = fun p : torsion E × (Fin (rank E) → ℤ) => Tent (fun i => ucoord x i + p.2 i)` using `funext fun p => by rw [Function.comp_apply, hval, one_mul]`. Rewrite using `[key]`. Conclude with `hasSum_Tent_torsion_prod (ucoord x)`.
-/
theorem hasSum_uphi_unit_smul (x : mixedSpace E) (hx : mixedEmbedding.norm x ≠ 0) :
    HasSum (fun u : (𝓞 E)ˣ => uphi (u • x)) (torsionOrder E : ℝ) := by
  let e : torsion E × (Fin (rank E) → ℤ) → (𝓞 E)ˣ :=
    fun p => (p.1 : (𝓞 E)ˣ) * ∏ i, (fundSystem E i) ^ (p.2 i)
  have he : Function.Bijective e := by
    refine ⟨fun p q h => ?_, fun u => ?_⟩
    · obtain ⟨c, -, hc⟩ := exist_unique_eq_mul_prod E (e p)
      exact (hc p rfl).trans (hc q h).symm
    · obtain ⟨c, hc, -⟩ := exist_unique_eq_mul_prod E u
      exact ⟨c, hc.symm⟩
  let eq := Equiv.ofBijective e he
  rw [← eq.hasSum_iff]
  have hval : ∀ p : torsion E × (Fin (rank E) → ℤ),
      uphi (eq p • x) = (fun _ : torsion E => (1 : ℝ)) p.1 *
        (fun n : Fin (rank E) → ℤ => Tent (fun i => ucoord x i + n i)) p.2 := by
    intro p
    have h0 : eq p • x = (p.1 : (𝓞 E)ˣ) • ((∏ i, (fundSystem E i) ^ (p.2 i)) • x) := mul_smul _ _ _
    rw [h0, uphi_torsion_smul p.1.2, one_mul]
    unfold uphi
    rw [if_neg (by rwa [norm_unit_smul])]
    exact congrArg Tent (funext fun i => ucoord_prod_fundSystem_smul p.2 x hx i)
  have key : (fun u : (𝓞 E)ˣ => uphi (u • x)) ∘ eq = fun p : torsion E × (Fin (rank E) → ℤ) =>
      Tent (fun i => ucoord x i + p.2 i) := funext fun p => by rw [Function.comp_apply, hval, one_mul]
  rw [key]
  exact hasSum_Tent_torsion_prod (ucoord x)

end ReciprocityTheory.Cheb
