import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section FinalA

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

/- English proof (translation)
Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `W hm hfd hWG hWk hWF`. Distinguish the cases in `hW0 : W = ⊥`.

Rewrite using `[hW0]`. Conclude with `bot_le`. Take `⟨y, hyW, hy0, μ, hy⟩` from `exists_khw hE (isKUnitary_of_isInfUnitary hU) hfd hWk hW0`. Take `⟨S', hS'W, hyS', hS'⟩` from `exists_irr_sub_of_khw hE hU W hfd hWk hyW hy0 hy`. Establish `hμF : μ ∈ F` using `hWF y hyW hy0 μ hy`.

Establish `hS'T : S' ≤ T μ`. Establish `hst : IsKStableSub ε E (S' ⊓ T μ)` using `fun a b hab v hv => Submodule.mem_inf.2 ⟨hS'.2.1 a b hab v (Submodule.mem_inf.1 hv).1, hTk μ a b hab v (Submodule.mem_inf.1 hv).2⟩`. Break down `hS'.2.2.1 (S' ⊓ T μ) inf_le_left hst with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hyI : y ∈ S' ⊓ T μ` using `Submodule.mem_inf.2 ⟨hyS', hTG μ y (hWG hyW) hy⟩`.

Rewrite `hyI` using `[h, Submodule.mem_bot]`. Conclude with `hy0 hyI`. Rewrite using `[← h]`. Conclude with `inf_le_right`. Use `haveI : FiniteDimensional ℂ S' := hS'.1`.

Use `haveI : FiniteDimensional ℂ W := hfd`. Establish `hW'W : S'ᗮ ⊓ W ≤ W` using `inf_le_right`. Establish `hlt : S'ᗮ ⊓ W < W`. Use `lt_of_le_of_ne hW'W fun heq => hy0 ?_` and prove the remaining obligations. Establish `hyW' : y ∈ S'ᗮ ⊓ W`.

Rewrite using `[heq]`. Conclude with `hyW`. Conclude with `inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hyS' (Submodule.mem_inf.1 hyW').1)`. Establish `hfd' : FiniteDimensional ℂ (S'ᗮ ⊓ W : Submodule ℂ M)` using `Submodule.finiteDimensional_of_le hW'W`. Establish `hk' : IsKStableSub ε E (S'ᗮ ⊓ W)` using `fun a b hab v hv => Submodule.mem_inf.2 ⟨orthogonal_kStable (isKUnitary_of_isInfUnitary hU) hS'.2.1 a b hab v (Submodule.mem_inf.1 hv).1, hWk a b hab v (Submodule.mem_inf.1 hv).2⟩`.

Establish `key : S'ᗮ ⊓ W ≤ F.sup T` using `ih _ (by rw [← hm]; exact Submodule.finrank_lt_finrank_of_lt hlt) (S'ᗮ ⊓ W) rfl hfd' (hW'W.trans hWG) hk' (fun w hw hw0 ν hν => hWF w (hW'W hw) hw0 ν hν)`. Rewrite using `[← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hS'W]`. Conclude with `sup_le (hS'T.trans (Finset.le_sup (f := T) hμF)) key`.
-/
theorem finalA_le_sup (hE : IsGlRep E) (hU : IsInfUnitary ε E) (G : Submodule ℂ M)
    (T : (Fin n → ℝ) → Submodule ℂ M) (hTk : ∀ μ, IsKStableSub ε E (T μ))
    (hTG : ∀ μ, ∀ w ∈ G, IsKHWVec ε E μ w → w ∈ T μ) (F : Finset (Fin n → ℝ)) :
    ∀ (m : ℕ) (W : Submodule ℂ M), Module.finrank ℂ W = m → FiniteDimensional ℂ W → W ≤ G →
      IsKStableSub ε E W → (∀ w ∈ W, w ≠ 0 → ∀ μ, IsKHWVec ε E μ w → μ ∈ F) → W ≤ F.sup T := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W hm hfd hWG hWk hWF
  by_cases hW0 : W = ⊥
  · rw [hW0]
    exact bot_le
  obtain ⟨y, hyW, hy0, μ, hy⟩ := exists_khw hE (isKUnitary_of_isInfUnitary hU) hfd hWk hW0
  obtain ⟨S', hS'W, hyS', hS'⟩ := exists_irr_sub_of_khw hE hU W hfd hWk hyW hy0 hy
  have hμF : μ ∈ F := hWF y hyW hy0 μ hy
  have hS'T : S' ≤ T μ := by
    have hst : IsKStableSub ε E (S' ⊓ T μ) := fun a b hab v hv =>
      Submodule.mem_inf.2 ⟨hS'.2.1 a b hab v (Submodule.mem_inf.1 hv).1,
        hTk μ a b hab v (Submodule.mem_inf.1 hv).2⟩
    rcases hS'.2.2.1 (S' ⊓ T μ) inf_le_left hst with h | h
    · exfalso
      have hyI : y ∈ S' ⊓ T μ := Submodule.mem_inf.2 ⟨hyS', hTG μ y (hWG hyW) hy⟩
      rw [h, Submodule.mem_bot] at hyI
      exact hy0 hyI
    · rw [← h]
      exact inf_le_right
  haveI : FiniteDimensional ℂ S' := hS'.1
  haveI : FiniteDimensional ℂ W := hfd
  have hW'W : S'ᗮ ⊓ W ≤ W := inf_le_right
  have hlt : S'ᗮ ⊓ W < W := by
    refine lt_of_le_of_ne hW'W fun heq => hy0 ?_
    have hyW' : y ∈ S'ᗮ ⊓ W := by
      rw [heq]
      exact hyW
    exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hyS' (Submodule.mem_inf.1 hyW').1)
  have hfd' : FiniteDimensional ℂ (S'ᗮ ⊓ W : Submodule ℂ M) := Submodule.finiteDimensional_of_le hW'W
  have hk' : IsKStableSub ε E (S'ᗮ ⊓ W) := fun a b hab v hv =>
    Submodule.mem_inf.2 ⟨orthogonal_kStable (isKUnitary_of_isInfUnitary hU) hS'.2.1 a b hab v
      (Submodule.mem_inf.1 hv).1, hWk a b hab v (Submodule.mem_inf.1 hv).2⟩
  have key : S'ᗮ ⊓ W ≤ F.sup T :=
    ih _ (by rw [← hm]; exact Submodule.finrank_lt_finrank_of_lt hlt) (S'ᗮ ⊓ W) rfl hfd' (hW'W.trans hWG) hk'
      (fun w hw hw0 ν hν => hWF w (hW'W hw) hw0 ν hν)
  rw [← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hS'W]
  exact sup_le (hS'T.trans (Finset.le_sup (f := T) hμF)) key

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Set `T : Fin n → Module.End ℂ S` to `fun c => (E c c).restrict (hS c)`. Establish `hTs : ∀ c, (T c).IsSymmetric`. Introduce `c x z`.

Conclude with `hU c c rfl (x : M) (z : M)`. Establish `hcomm : Pairwise (Function.onFun Commute T)`. Introduce `a c _`. Conclude with `LinearMap.ext fun x => Subtype.ext (kUnit_diag_comm hE a c (x : M))`. Establish `htop` using `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hcomm`.

Establish `hle : ∀ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (T c) (χ c)).map f ≤ (ℂ ∙ y)ᗮ`. Introduce `χ`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[Submodule.mem_orthogonal_singleton_iff_inner_right]`. Distinguish the cases in `hx0 : x = 0`.

Rewrite using `[hx0, map_zero, inner_zero_right]`. Establish `hxc : ∀ c, E c c (x : M) = χ c • (x : M)`. Introduce `c`. Establish `h1` using `Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx c)`. Conclude with `congrArg Subtype.val h1`.

Establish `hx0' : (x : M) ≠ 0` using `fun h => hx0 (Subtype.ext h)`. Establish `hreal : ∀ c, χ c = (((χ c).re : ℝ) : ℂ)` using `fun c => kUnit_eig_real hU hx0' (hxc c)`. Establish `hxν : ∀ c, E c c (x : M) = ((((χ c).re : ℝ)) : ℂ) • (x : M)` using `fun c => (hxc c).trans (congrArg (· • (x : M)) (hreal c))`. Take `⟨c, hc⟩` from `hno (x : M) x.2 hx0'`. Establish `hfx : E c c (f x) = (((χ c).re : ℝ) : ℂ) • f x` using `hf (fun c => (χ c).re) x hxν c`.

Establish `hne : (χ c).re ≠ μ c` using `fun h => hc (by rw [hxν c, h])`. Establish `h1` using `hU c c rfl y (f x)`. Rewrite `h1` using `[hμ c, hfx, inner_smul_left, inner_smul_right, Complex.conj_ofReal]`. Establish `h2 : ((μ c : ℂ) - (((χ c).re : ℝ) : ℂ)) * inner ℂ y (f x) = 0`. Rewrite using `[sub_mul, h1, sub_self]`.

Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `absurd (Complex.ofReal_injective (sub_eq_zero.mp h)).symm hne`. Conclude with `h`. Establish `hR : LinearMap.range f ≤ (ℂ ∙ y)ᗮ`. Rewrite using `[LinearMap.range_eq_map, ← htop, Submodule.map_iSup]`.

Conclude with `iSup_le hle`. Conclude with `hy0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hR hy)))`.
-/
theorem finalA_wt_mem (hE : IsGlRep E) (hU : IsKUnitary ε E) (S : Submodule ℂ M) [FiniteDimensional ℂ S]
    (hS : ∀ c, ∀ v ∈ S, E c c v ∈ S) (f : S →ₗ[ℂ] M)
    (hf : ∀ (ν : Fin n → ℝ) (s : S), (∀ c, E c c (s : M) = (ν c : ℂ) • (s : M)) →
      ∀ c, E c c (f s) = (ν c : ℂ) • f s)
    {y : M} (hy : y ∈ LinearMap.range f) (hy0 : y ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ c, E c c y = (μ c : ℂ) • y) :
    ∃ s ∈ S, s ≠ 0 ∧ ∀ c, E c c s = (μ c : ℂ) • s := by
  classical
  by_contra hno
  push_neg at hno
  let T : Fin n → Module.End ℂ S := fun c => (E c c).restrict (hS c)
  have hTs : ∀ c, (T c).IsSymmetric := by
    intro c x z
    exact hU c c rfl (x : M) (z : M)
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a c _
    exact LinearMap.ext fun x => Subtype.ext (kUnit_diag_comm hE a c (x : M))
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hcomm
  have hle : ∀ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (T c) (χ c)).map f ≤ (ℂ ∙ y)ᗮ := by
    intro χ
    rintro _ ⟨x, hx, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    by_cases hx0 : x = 0
    · rw [hx0, map_zero, inner_zero_right]
    have hxc : ∀ c, E c c (x : M) = χ c • (x : M) := by
      intro c
      have h1 := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx c)
      exact congrArg Subtype.val h1
    have hx0' : (x : M) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hreal : ∀ c, χ c = (((χ c).re : ℝ) : ℂ) := fun c => kUnit_eig_real hU hx0' (hxc c)
    have hxν : ∀ c, E c c (x : M) = ((((χ c).re : ℝ)) : ℂ) • (x : M) := fun c =>
      (hxc c).trans (congrArg (· • (x : M)) (hreal c))
    obtain ⟨c, hc⟩ := hno (x : M) x.2 hx0'
    have hfx : E c c (f x) = (((χ c).re : ℝ) : ℂ) • f x := hf (fun c => (χ c).re) x hxν c
    have hne : (χ c).re ≠ μ c := fun h => hc (by rw [hxν c, h])
    have h1 := hU c c rfl y (f x)
    rw [hμ c, hfx, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
    have h2 : ((μ c : ℂ) - (((χ c).re : ℝ) : ℂ)) * inner ℂ y (f x) = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h)).symm hne
    · exact h
  have hR : LinearMap.range f ≤ (ℂ ∙ y)ᗮ := by
    rw [LinearMap.range_eq_map, ← htop, Submodule.map_iSup]
    exact iSup_le hle
  exact hy0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hR hy)))

end FinalA

end ReciprocityTheory.ChartRestriction.DS
