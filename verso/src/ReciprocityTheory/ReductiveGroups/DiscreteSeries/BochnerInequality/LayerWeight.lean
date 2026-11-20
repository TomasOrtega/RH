import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PositionPrependMemNoncompactPositionSubmodule
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Weights
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LayerWeight

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

/- English proof (translation)
Use `set Lk := layer ε E V k with hLk`. Use `haveI : FiniteDimensional ℂ Lk := finiteDimensional_layer (ε := ε) (E := E) hVfd k`. Use `set N := ncV ε V (k + 1) with hN`. Use `haveI : FiniteDimensional ℂ N := finiteDimensional_ncV (ε := ε) hVfd (k + 1)`. Use `set U : Submodule ℂ (Big n (k + 1) M) := N ⊓ Lk.comap (phi E (k + 1)) with hUdef`.

Use `haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left`. Establish `hKu : ∀ a b, ε a = ε b → ∀ x y : M, inner ℂ x (E a b y) = inner ℂ (E b a x) y`. Introduce `a b hab x y`. Rewrite using `[hU b a x y]`. Simplify using `[adjSign, hab.symm]`.

Establish `hLkK : IsKStableSub ε E Lk` using `layer_kStable hE hVk k`. Establish `hLkoK : ∀ a b, ε a = ε b → ∀ y ∈ Lkᗮ, E a b y ∈ Lkᗮ`. Introduce `a b hab y hy`. Rewrite `hy`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`.

Rewrite using `[hKu a b hab u y]`. Conclude with `hy _ (hLkK b a hab.symm u hu)`. Establish `hBu` using `bAct_isKUnitary hU (k + 1)`. Establish `hNK : IsKStableSub ε (bAct E (k + 1)) N` using `ncV_kStable hVk (k + 1)`. Establish `hUK : ∀ a b, ε a = ε b → ∀ H ∈ U, bAct E (k + 1) a b H ∈ U`.

Introduce `a b hab H hH`. Use `⟨hNK a b hab H hH.1, ?_⟩` and prove the remaining obligations. Use `show phi E (k + 1) (bAct E (k + 1) a b H) ∈ Lk`. Rewrite using `[wordContraction_tensorAction hE]`. Conclude with `hLkK a b hab _ hH.2`.

Establish `hUoK : ∀ a b, ε a = ε b → ∀ H ∈ Uᗮ, bAct E (k + 1) a b H ∈ Uᗮ`. Introduce `a b hab H hH`. Rewrite `hH`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[← hBu b a hab.symm u H]`.

Conclude with `hH _ (hUK b a hab.symm u hu)`. Set `Ψ : Big n (k + 1) M →ₗ[ℂ] M` to `(LinearMap.id - ((Lk.starProjection : M →L[ℂ] M) : M →ₗ[ℂ] M)) ∘ₗ phi E (k + 1)`. Establish `hΨ : ∀ H, Ψ H = phi E (k + 1) H - Lk.starProjection (phi E (k + 1) H)` using `fun H => rfl`. Establish `hPmem : ∀ v, Lk.starProjection v ∈ Lk` using `fun v => by`. Rewrite using `[Submodule.starProjection_apply]`.

Conclude with `SetLike.coe_mem _`. Establish `hzero : ∀ x, x ∈ Lk → x ∈ Lkᗮ → x = 0`. Introduce `x h1 h2`. Establish `hm : x ∈ Lk ⊓ Lkᗮ` using `⟨h1, h2⟩`. Rewrite `hm` using `[Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot]`.

Conclude with `hm`. Establish `hΨo : ∀ H, Ψ H ∈ Lkᗮ` using `fun H => by`. Rewrite using `[hΨ]`. Conclude with `Submodule.sub_starProjection_mem_orthogonal _`. Establish `hΨeq : ∀ a b, ε a = ε b → ∀ H, Ψ (bAct E (k + 1) a b H) = E a b (Ψ H)`.

Introduce `a b hab H`. Rewrite using `[← sub_eq_zero]`. Apply `hzero` to reduce the goal to its premises. Rewrite using `[hΨ, hΨ, wordContraction_tensorAction hE, map_sub]`. Establish `e : E a b (phi E (k + 1) H) - Lk.starProjection (E a b (phi E (k + 1) H)) - (E a b (phi E (k + 1) H) - E a b (Lk.starProjection (phi E (k + 1) H))) = E a b (Lk.starProjection (phi E (k + 1) H)) - Lk.starProjection (E a b (phi E (k + 1) H))` using `by abel`.

Rewrite using `[e]`. Conclude with `Lk.sub_mem (hLkK a b hab _ (hPmem _)) (hPmem _)`. Conclude with `Lkᗮ.sub_mem (hΨo _) (hLkoK a b hab _ (hΨo _))`. Establish `hinj : ∀ H ∈ Uᗮ, H ∈ N → Ψ H = 0 → H = 0`. Introduce `H hHo hHN h0`.

Establish `hphi : phi E (k + 1) H ∈ Lk`. Rewrite `h0` using `[hΨ, sub_eq_zero]`. Rewrite using `[h0]`. Conclude with `hPmem _`. Establish `hm : H ∈ U ⊓ Uᗮ` using `⟨⟨hHN, hphi⟩, hHo⟩`.

Rewrite `hm` using `[Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot]`. Conclude with `hm`. Take `⟨l, hl, y, hy, hly⟩` from `Submodule.mem_sup.mp (layer_succ_le hE hVk k hw)`. Take `⟨G0, hG0, rfl⟩` from `Submodule.mem_map.mp hy`. Establish `hUmem : U.starProjection G0 ∈ U`.

Rewrite using `[Submodule.starProjection_apply]`. Conclude with `SetLike.coe_mem _`. Use `set G := G0 - U.starProjection G0 with hG`. Establish `hGo : G ∈ Uᗮ` using `Submodule.sub_starProjection_mem_orthogonal G0`. Establish `hGN : G ∈ N` using `N.sub_mem hG0 hUmem.1`.

Establish `hwo : w ∈ Lkᗮ` using `by rw [Submodule.mem_orthogonal]; exact hperp`. Establish `hΨG : Ψ G = w`. Rewrite using `[← sub_eq_zero]`. Apply `hzero` to reduce the goal to its premises. Rewrite using `[hΨ, hG, map_sub, ← hly]`.

Establish `hpu : phi E (k + 1) (U.starProjection G0) ∈ Lk` using `hUmem.2`. Establish `e : phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0) - Lk.starProjection (phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0)) - (l + phi E (k + 1) G0) = -(phi E (k + 1) (U.starProjection G0)) - Lk.starProjection (phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0)) - …`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Lk.sub_mem (Lk.sub_mem (Lk.neg_mem hpu) (hPmem _)) hl`.

Conclude with `Lkᗮ.sub_mem (hΨo G) hwo`. Use `⟨G, hGN, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hw0` to reduce the goal to its premises. Rewrite using `[← hΨG, h0, map_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce `a`. Establish `hD : bAct E (k + 1) a a G - ((μ a : ℂ)) • G = 0`. Apply `hinj` to reduce the goal to its premises. Conclude with `Uᗮ.sub_mem (hUoK a a rfl G hGo) (Uᗮ.smul_mem _ hGo)`.

Conclude with `N.sub_mem (hNK a a rfl G hGN) (N.smul_mem _ hGN)`. Rewrite using `[map_sub, map_smul, hΨeq a a rfl, hΨG, hμ.1 a, sub_self]`. Conclude with `sub_eq_zero.mp hD`. Introduce `a b hab hεab`. Apply `hinj _ (hUoK a b hεab G hGo) (hNK a b hεab G hGN)` to reduce the goal to its premises.

Rewrite using `[hΨeq a b hεab, hΨG, hμ.2 a b hab hεab]`. Introduce `F hF hphi`. Rewrite `hGo` using `[Submodule.mem_orthogonal]`. Conclude with `hGo F ⟨hF, hphi⟩`.
-/
theorem lift_layer (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) {k : ℕ} {w : M} (hw : w ∈ layer ε E V (k + 1))
    (hperp : ∀ u ∈ layer ε E V k, inner ℂ u w = 0) {μ : Fin n → ℝ} (hμ : IsKHWVec ε E μ w)
    (hw0 : w ≠ 0) :
    ∃ P ∈ ncV ε V (k + 1), P ≠ 0 ∧ IsKHWVec ε (bAct E (k + 1)) μ P ∧
      ∀ F ∈ ncV ε V (k + 1), phi E (k + 1) F ∈ layer ε E V k → inner ℂ F P = 0 := by
  classical
  set Lk := layer ε E V k with hLk
  haveI : FiniteDimensional ℂ Lk := finiteDimensional_layer (ε := ε) (E := E) hVfd k
  set N := ncV ε V (k + 1) with hN
  haveI : FiniteDimensional ℂ N := finiteDimensional_ncV (ε := ε) hVfd (k + 1)
  set U : Submodule ℂ (Big n (k + 1) M) := N ⊓ Lk.comap (phi E (k + 1)) with hUdef
  haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left

  have hKu : ∀ a b, ε a = ε b → ∀ x y : M, inner ℂ x (E a b y) = inner ℂ (E b a x) y := by
    intro a b hab x y
    rw [hU b a x y]
    simp [adjSign, hab.symm]
  have hLkK : IsKStableSub ε E Lk := layer_kStable hE hVk k
  have hLkoK : ∀ a b, ε a = ε b → ∀ y ∈ Lkᗮ, E a b y ∈ Lkᗮ := by
    intro a b hab y hy
    rw [Submodule.mem_orthogonal] at hy ⊢
    intro u hu
    rw [hKu a b hab u y]
    exact hy _ (hLkK b a hab.symm u hu)
  have hBu := bAct_isKUnitary hU (k + 1)
  have hNK : IsKStableSub ε (bAct E (k + 1)) N := ncV_kStable hVk (k + 1)
  have hUK : ∀ a b, ε a = ε b → ∀ H ∈ U, bAct E (k + 1) a b H ∈ U := by
    intro a b hab H hH
    refine ⟨hNK a b hab H hH.1, ?_⟩
    show phi E (k + 1) (bAct E (k + 1) a b H) ∈ Lk
    rw [wordContraction_tensorAction hE]
    exact hLkK a b hab _ hH.2
  have hUoK : ∀ a b, ε a = ε b → ∀ H ∈ Uᗮ, bAct E (k + 1) a b H ∈ Uᗮ := by
    intro a b hab H hH
    rw [Submodule.mem_orthogonal] at hH ⊢
    intro u hu
    rw [← hBu b a hab.symm u H]
    exact hH _ (hUK b a hab.symm u hu)

  let Ψ : Big n (k + 1) M →ₗ[ℂ] M :=
    (LinearMap.id - ((Lk.starProjection : M →L[ℂ] M) : M →ₗ[ℂ] M)) ∘ₗ phi E (k + 1)
  have hΨ : ∀ H, Ψ H = phi E (k + 1) H - Lk.starProjection (phi E (k + 1) H) := fun H => rfl
  have hPmem : ∀ v, Lk.starProjection v ∈ Lk := fun v => by
    rw [Submodule.starProjection_apply]; exact SetLike.coe_mem _
  have hzero : ∀ x, x ∈ Lk → x ∈ Lkᗮ → x = 0 := by
    intro x h1 h2
    have hm : x ∈ Lk ⊓ Lkᗮ := ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
    exact hm
  have hΨo : ∀ H, Ψ H ∈ Lkᗮ := fun H => by
    rw [hΨ]; exact Submodule.sub_starProjection_mem_orthogonal _
  have hΨeq : ∀ a b, ε a = ε b → ∀ H, Ψ (bAct E (k + 1) a b H) = E a b (Ψ H) := by
    intro a b hab H
    rw [← sub_eq_zero]
    apply hzero
    · rw [hΨ, hΨ, wordContraction_tensorAction hE, map_sub]
      have e : E a b (phi E (k + 1) H) - Lk.starProjection (E a b (phi E (k + 1) H)) -
          (E a b (phi E (k + 1) H) - E a b (Lk.starProjection (phi E (k + 1) H))) =
          E a b (Lk.starProjection (phi E (k + 1) H)) -
            Lk.starProjection (E a b (phi E (k + 1) H)) := by abel
      rw [e]
      exact Lk.sub_mem (hLkK a b hab _ (hPmem _)) (hPmem _)
    · exact Lkᗮ.sub_mem (hΨo _) (hLkoK a b hab _ (hΨo _))
  have hinj : ∀ H ∈ Uᗮ, H ∈ N → Ψ H = 0 → H = 0 := by
    intro H hHo hHN h0
    have hphi : phi E (k + 1) H ∈ Lk := by
      rw [hΨ, sub_eq_zero] at h0
      rw [h0]; exact hPmem _
    have hm : H ∈ U ⊓ Uᗮ := ⟨⟨hHN, hphi⟩, hHo⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
    exact hm

  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.mp (layer_succ_le hE hVk k hw)
  obtain ⟨G0, hG0, rfl⟩ := Submodule.mem_map.mp hy
  have hUmem : U.starProjection G0 ∈ U := by
    rw [Submodule.starProjection_apply]; exact SetLike.coe_mem _
  set G := G0 - U.starProjection G0 with hG
  have hGo : G ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal G0
  have hGN : G ∈ N := N.sub_mem hG0 hUmem.1
  have hwo : w ∈ Lkᗮ := by rw [Submodule.mem_orthogonal]; exact hperp
  have hΨG : Ψ G = w := by
    rw [← sub_eq_zero]
    apply hzero
    · rw [hΨ, hG, map_sub, ← hly]
      have hpu : phi E (k + 1) (U.starProjection G0) ∈ Lk := hUmem.2
      have e : phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0) -
          Lk.starProjection (phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0)) -
          (l + phi E (k + 1) G0) =
          -(phi E (k + 1) (U.starProjection G0)) -
            Lk.starProjection (phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0)) - l := by
        abel
      rw [e]
      exact Lk.sub_mem (Lk.sub_mem (Lk.neg_mem hpu) (hPmem _)) hl
    · exact Lkᗮ.sub_mem (hΨo G) hwo
  refine ⟨G, hGN, ?_, ?_, ?_⟩
  · intro h0
    apply hw0
    rw [← hΨG, h0, map_zero]
  · constructor
    · intro a
      have hD : bAct E (k + 1) a a G - ((μ a : ℂ)) • G = 0 := by
        apply hinj
        · exact Uᗮ.sub_mem (hUoK a a rfl G hGo) (Uᗮ.smul_mem _ hGo)
        · exact N.sub_mem (hNK a a rfl G hGN) (N.smul_mem _ hGN)
        · rw [map_sub, map_smul, hΨeq a a rfl, hΨG, hμ.1 a, sub_self]
      exact sub_eq_zero.mp hD
    · intro a b hab hεab
      apply hinj _ (hUoK a b hεab G hGo) (hNK a b hεab G hGN)
      rw [hΨeq a b hεab, hΨG, hμ.2 a b hab hεab]
  · intro F hF hphi
    rw [Submodule.mem_orthogonal] at hGo
    exact hGo F ⟨hF, hphi⟩

/- English proof (translation)
Take `⟨w₀, hw₀V, hw₀, ws, hsum, hws⟩` from `layer_khw_decomp hE hU hV.1 hV.2.1 hw hμ`. Distinguish the cases in `h0 : w₀ = 0`. Establish `hex : ∃ j, ws j ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Apply `hw0` to reduce the goal to its premises. Rewrite using `[hsum, h0]`. Simplify using `[hc]`. Take `⟨j, hj⟩` from `hex`. Take `⟨hj1, hj2, hj3⟩` from `hws j`.

Take `⟨P, hPN, hP0, hPk, -⟩` from `lift_layer hE hU hV.1 hV.2.1 hj1 hj2 hj3 hj`. Conclude with `⟨(j : ℕ) + 1, by omega, khw_big_weight hE hV hPN hP0 hPk⟩`. Set `F : Big n 0 M` to `WithLp.toLp 2 (fun _ => w₀)`. Establish `hF : ∀ κ, F κ = w₀` using `fun κ => rfl`. Establish `hFN : F ∈ ncV ε V 0`.

Rewrite using `[mem_ncV_iff]`. Introduce `κ`. Simplify using `[hF, hw₀V]`. Establish `hF0 : F ≠ 0`. Introduce `hF'`.

Apply `h0` to reduce the goal to its premises. Use `congrArg (fun G : Big n 0 M => G (fun i => i.elim0)) hF'` as an intermediate fact. Simplify `this` using `[hF]`. Establish `hFk : IsKHWVec ε (bAct E 0) μ F`. Prove the components needed by the constructor for the conclusion.

Introduce `a`. Use extensionality with `κ`. Rewrite using `[bAct_apply]`. Simplify using `[hF, hw₀.1 a]`. Introduce `a b hab hε`.

Use extensionality with `κ`. Rewrite using `[bAct_apply]`. Simplify using `[hF, hw₀.2 a b hab hε]`. Conclude with `⟨0, Nat.zero_le _, khw_big_weight hE hV hFN hF0 hFk⟩`.
-/
theorem khw_layer_weight (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (k : ℕ) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ layer ε E V k) (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) :
    ∃ j ≤ k, IsNCSum ε j (μ - lowK ε lam) := by
  classical
  obtain ⟨w₀, hw₀V, hw₀, ws, hsum, hws⟩ := layer_khw_decomp hE hU hV.1 hV.2.1 hw hμ
  by_cases h0 : w₀ = 0
  · have hex : ∃ j, ws j ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hw0
      rw [hsum, h0]
      simp [hc]
    obtain ⟨j, hj⟩ := hex
    obtain ⟨hj1, hj2, hj3⟩ := hws j
    obtain ⟨P, hPN, hP0, hPk, -⟩ := lift_layer hE hU hV.1 hV.2.1 hj1 hj2 hj3 hj
    exact ⟨(j : ℕ) + 1, by omega, khw_big_weight hE hV hPN hP0 hPk⟩
  ·
    let F : Big n 0 M := WithLp.toLp 2 (fun _ => w₀)
    have hF : ∀ κ, F κ = w₀ := fun κ => rfl
    have hFN : F ∈ ncV ε V 0 := by
      rw [mem_ncV_iff]
      intro κ
      simp [hF, hw₀V]
    have hF0 : F ≠ 0 := by
      intro hF'
      apply h0
      have := congrArg (fun G : Big n 0 M => G (fun i => i.elim0)) hF'
      simpa [hF] using this
    have hFk : IsKHWVec ε (bAct E 0) μ F := by
      constructor
      · intro a
        ext κ
        rw [bAct_apply]
        simp [hF, hw₀.1 a]
      · intro a b hab hε
        ext κ
        rw [bAct_apply]
        simp [hF, hw₀.2 a b hab hε]
    exact ⟨0, Nat.zero_le _, khw_big_weight hE hV hFN hF0 hFk⟩

end LayerWeight

end ReciprocityTheory.ChartRestriction.DS
