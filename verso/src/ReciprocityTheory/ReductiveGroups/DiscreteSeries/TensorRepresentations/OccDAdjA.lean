import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefBTensSubKStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DataGenSubIrred

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Use `set TM : Module.End ℂ M := T.restrict hT`. Use `set Φ' : M →ₗ[ℂ] W := Φ.comp M.subtype`. Use `set p : Submodule ℂ M := LinearMap.ker Φ'`. Establish `hp : p ≤ p.comap TM`. Introduce `y hy`.

Simplify using `only [Submodule.mem_comap, p, LinearMap.mem_ker, Φ', LinearMap.comp_apply, Submodule.subtype_apply] at hy ⊢`. Conclude with `hΦ y y.2 hy`. Use `set Tb : Module.End ℂ (M ⧸ p) := p.mapQ p TM hp`. Establish `: FiniteDimensional ℂ (LinearMap.range Φ')` using `inferInstance`. Establish `: FiniteDimensional ℂ (M ⧸ p)` using `LinearEquiv.finiteDimensional Φ'.quotKerEquivRange.symm`.

Establish `hfin` using `Module.End.finite_hasEigenvalue Tb`. Use `⟨∑ μ ∈ hfin.toFinset, ‖μ‖, fun y hy θ hθ hTy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hq : Submodule.Quotient.mk (p` using `p) (⟨y, hy⟩ : M) ≠ 0 := by`. Rewrite using `[Ne, Submodule.Quotient.mk_eq_zero]`.

Conclude with `hne`. Establish `hTb : Tb (Submodule.Quotient.mk (⟨y, hy⟩ : M)) = (θ : ℂ) • Submodule.Quotient.mk (⟨y, hy⟩ : M)`. Rewrite using `[Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]`. Use `congr 1`. Conclude with `Subtype.ext hTy`.

Establish `hev : Tb.HasEigenvalue (θ : ℂ)` using `Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hTb, hq⟩`. Establish `hmem : (θ : ℂ) ∈ hfin.toFinset` using `hfin.mem_toFinset.2 hev`. Establish `hle : ‖(θ : ℂ)‖ ≤ ∑ μ ∈ hfin.toFinset, ‖μ‖` using `Finset.single_le_sum (f := fun μ : ℂ => ‖μ‖) (fun _ _ => norm_nonneg _) hmem`. Rewrite `hle` using `[Complex.norm_real, Real.norm_eq_abs]`. Combine the linear relations using `[le_abs_self θ]`.
-/
theorem adjA_high {D : Type*} [AddCommGroup D] [Module ℂ D] {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (M : Submodule ℂ D) (T : Module.End ℂ D) (hT : ∀ y ∈ M, T y ∈ M)
    (Φ : D →ₗ[ℂ] W) (hΦ : ∀ y ∈ M, Φ y = 0 → Φ (T y) = 0) :
    ∃ C : ℝ, ∀ y ∈ M, ∀ θ : ℝ, C < θ → T y = (θ : ℂ) • y → Φ y = 0 := by
  classical
  set TM : Module.End ℂ M := T.restrict hT
  set Φ' : M →ₗ[ℂ] W := Φ.comp M.subtype
  set p : Submodule ℂ M := LinearMap.ker Φ'
  have hp : p ≤ p.comap TM := by
    intro y hy
    simp only [Submodule.mem_comap, p, LinearMap.mem_ker, Φ', LinearMap.comp_apply,
      Submodule.subtype_apply] at hy ⊢
    exact hΦ y y.2 hy
  set Tb : Module.End ℂ (M ⧸ p) := p.mapQ p TM hp
  have : FiniteDimensional ℂ (LinearMap.range Φ') := inferInstance
  have : FiniteDimensional ℂ (M ⧸ p) := LinearEquiv.finiteDimensional Φ'.quotKerEquivRange.symm
  have hfin := Module.End.finite_hasEigenvalue Tb
  refine ⟨∑ μ ∈ hfin.toFinset, ‖μ‖, fun y hy θ hθ hTy => ?_⟩
  by_contra hne
  have hq : Submodule.Quotient.mk (p := p) (⟨y, hy⟩ : M) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hne
  have hTb : Tb (Submodule.Quotient.mk (⟨y, hy⟩ : M)) = (θ : ℂ) • Submodule.Quotient.mk (⟨y, hy⟩ : M) := by
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext hTy
  have hev : Tb.HasEigenvalue (θ : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hTb, hq⟩
  have hmem : (θ : ℂ) ∈ hfin.toFinset := hfin.mem_toFinset.2 hev
  have hle : ‖(θ : ℂ)‖ ≤ ∑ μ ∈ hfin.toFinset, ‖μ‖ :=
    Finset.single_le_sum (f := fun μ : ℂ => ‖μ‖) (fun _ _ => norm_nonneg _) hmem
  rw [Complex.norm_real, Real.norm_eq_abs] at hle
  linarith [le_abs_self θ]

/- English proof (translation)
Consider the cases of `dual`. Use `⟨a, if b = c then 1 else 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.

Use `⟨b, if a = c then -1 else 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [tensF, cond_true, tensVd_coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all [sub_eq_add_neg]`.
-/
theorem adjA_tensF_single {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (y : M) :
    ∃ c' : Fin n, ∃ r : ℂ, tensF dual E a b (Pi.single c y) = Pi.single c (E a b y) + r • (Pi.single c' y : Fin n → M) := by
  classical
  cases dual
  · refine ⟨a, if b = c then 1 else 0, ?_⟩
    funext x
    simp only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · refine ⟨b, if a = c then -1 else 0, ?_⟩
    funext x
    simp only [tensF, cond_true, tensVd_coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all [sub_eq_add_neg]

/- English proof (translation)
Use `Submodule.mem_pi.2 fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `hy`. Conclude with `S.zero_mem`.
-/
theorem adjA_single_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} (c : Fin n) {y : M}
    (hy : y ∈ S) : (Pi.single c y : Fin n → M) ∈ tensSub S := by
  classical
  refine Submodule.mem_pi.2 fun x _ => ?_
  rw [Pi.single_apply]
  split_ifs
  · exact hy
  · exact S.zero_mem

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

/- English proof (translation)
Establish `hE` using `hD.glRep`. Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Establish `hUk` using `isKUnitary_of_isInfUnitary hU`. Take `⟨m', hm'⟩` from `exists_layer_of_mem_genSub hE hV'k hx'`. Use `set L' := layer ε E V' m'`.

Establish `hL'f : FiniteDimensional ℂ L'` using `finiteDimensional_layer hV'f m'`. Establish `hL'k : IsKStableSub ε E L'` using `layer_kStable hE hV'k m'`. Use `set bs := Module.finBasis ℂ L'`. Use `set Φ : D →ₗ[ℂ] (Fin n × Fin (Module.finrank ℂ L') → ℂ) := LinearMap.pi fun p => (innerₛₗ ℂ (bs p.2 : D)).comp (ps.comp (LinearMap.single ℂ (fun _ => D) p.1))`. Establish `hΦ : ∀ y, ∀ p : Fin n × Fin (Module.finrank ℂ L'), Φ y p = inner ℂ (bs p.2 : D) (ps (Pi.single p.1 y))` using `fun y p => rfl`.

Use `set P : D → Prop := fun y => ∀ v ∈ L', ∀ c, inner ℂ v (ps (Pi.single c y)) = 0`. Establish `hPΦ : ∀ y, Φ y = 0 → P y`. Introduce `y hy v hv c`. Establish `hv' : v = ∑ i, (bs.repr ⟨v, hv⟩ i) • (bs i : D)`. Use `congrArg Subtype.val (bs.sum_repr ⟨v, hv⟩)` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_sum]`. Simplify `this.symm` using `only [Submodule.coe_smul]`. Rewrite using `[hv', sum_inner]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, ← hΦ y (c, i), hy, Pi.zero_apply, mul_zero]`.

Establish `hΦP : ∀ y, P y → Φ y = 0`. Introduce `y hy`. Use function extensionality and compare the values at `p`. Rewrite using `[hΦ, Pi.zero_apply]`. Conclude with `hy _ (bs p.2).2 p.1`.

Establish `hMk : IsKStableSub ε E (genSub E V)` using `fun a b _ v hv => closure_E_mem_genSub a b hv`. Establish `hPE : ∀ y ∈ genSub E V, P y → ∀ a b, ε a = ε b → P (E a b y)`. Introduce `y hy hPy a b hab v hv c`. Take `⟨c', r, hcr⟩` from `adjA_tensF_single dual E a b c y`. Establish `h1 : ps (Pi.single c (E a b y)) = E a b (ps (Pi.single c y)) - r • ps (Pi.single c' y)`.

Rewrite using `[← hps a b _ (adjA_single_mem c hy), hcr, map_add, map_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1, inner_sub_right, inner_smul_right, hPy v hv c', mul_zero, sub_zero, ← hUk b a hab.symm]`. Conclude with `hPy _ (hL'k b a hab.symm v hv) c`. Establish `hPadd : ∀ s : Finset (Fin n), ∀ g : Fin n → D, (∀ q ∈ s, P (g q)) → P (∑ q ∈ s, g q)`.

Introduce `s g hg v hv c`. Establish `: (Pi.single c (∑ q ∈ s, g q) : Fin n → D) = ∑ q ∈ s, Pi.single c (g q)`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.single_apply, Finset.sum_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[this, map_sum, inner_sum]`. Conclude with `Finset.sum_eq_zero fun q hq => hg q hq v hv c`. Establish `hcasP : ∀ y ∈ genSub E V, P y → P (casimirK ε E y)`. Introduce `y hy hPy`. Simplify using `only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]`.

Use `hPadd _ _ fun a _ => hPadd _ _ fun b hb => ?_` and prove the remaining obligations. Establish `hq' : ε b = ε a` using `(Finset.mem_filter.1 hb).2`. Conclude with `hPE _ (closure_E_mem_genSub _ _ hy) (hPE y hy hPy b a hq') a b hq'.symm`. Take `⟨C, hC⟩` from `adjA_high (genSub E V) (casimirK ε E) (fun y hy => casimirK_mem_of_kStable hMk hy) Φ (fun y hy h0 => hΦP _ (hcasP y hy (hPΦ y h0)))`. Take `⟨K, hK⟩` from `coefB_adm hE hU hV hc hgap C`.

Establish `hTsym : ∀ x y, inner ℂ (casimirK ε E x) y = inner ℂ x (casimirK ε E y)` using `casimirK_inner_symm hUk`. Use `set ℓ : D →ₗ[ℂ] ℂ := (innerₛₗ ℂ x').comp (ps.comp (LinearMap.single ℂ (fun _ => D) c))`. Take `⟨z, hzM, hz⟩` from `coefA_toSum hTsym (coefB_locFin hE hV.1 hV.2.1) ℓ C (finiteDimensional_layer hV.1 K) (layer_le_genSub K) (fun y hy θ hθ hyθ => hK y hy θ hθ hyθ) (fun y hy θ hθ hyθ => hPΦ y (hC y hy θ hθ hyθ) x' hm' c)`. Conclude with `⟨z, hzM, fun y hy => hz y hy⟩`.
-/
theorem adjA_rep (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam : Fin n → ℝ} {V V' : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hV'f : FiniteDimensional ℂ V')
    (hV'k : IsKStableSub ε E V') {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps : ∀ a b, ∀ f ∈ tensSub (genSub E V), ps (tensF dual E a b f) = E a b (ps f))
    {x' : D} (hx' : x' ∈ genSub E V') (c : Fin n) :
    ∃ z ∈ genSub E V, ∀ y ∈ genSub E V, inner ℂ z y = inner ℂ x' (ps (Pi.single c y)) := by
  classical
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hUk := isKUnitary_of_isInfUnitary hU
  obtain ⟨m', hm'⟩ := exists_layer_of_mem_genSub hE hV'k hx'
  set L' := layer ε E V' m'
  have hL'f : FiniteDimensional ℂ L' := finiteDimensional_layer hV'f m'
  have hL'k : IsKStableSub ε E L' := layer_kStable hE hV'k m'
  set bs := Module.finBasis ℂ L'
  set Φ : D →ₗ[ℂ] (Fin n × Fin (Module.finrank ℂ L') → ℂ) :=
    LinearMap.pi fun p => (innerₛₗ ℂ (bs p.2 : D)).comp (ps.comp (LinearMap.single ℂ (fun _ => D) p.1))
  have hΦ : ∀ y, ∀ p : Fin n × Fin (Module.finrank ℂ L'), Φ y p = inner ℂ (bs p.2 : D) (ps (Pi.single p.1 y)) :=
    fun y p => rfl

  set P : D → Prop := fun y => ∀ v ∈ L', ∀ c, inner ℂ v (ps (Pi.single c y)) = 0
  have hPΦ : ∀ y, Φ y = 0 → P y := by
    intro y hy v hv c
    have hv' : v = ∑ i, (bs.repr ⟨v, hv⟩ i) • (bs i : D) := by
      have := congrArg Subtype.val (bs.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simpa only [Submodule.coe_smul] using this.symm
    rw [hv', sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left, ← hΦ y (c, i), hy, Pi.zero_apply, mul_zero]
  have hΦP : ∀ y, P y → Φ y = 0 := by
    intro y hy
    funext p
    rw [hΦ, Pi.zero_apply]
    exact hy _ (bs p.2).2 p.1
  have hMk : IsKStableSub ε E (genSub E V) := fun a b _ v hv => closure_E_mem_genSub a b hv
  have hPE : ∀ y ∈ genSub E V, P y → ∀ a b, ε a = ε b → P (E a b y) := by
    intro y hy hPy a b hab v hv c
    obtain ⟨c', r, hcr⟩ := adjA_tensF_single dual E a b c y
    have h1 : ps (Pi.single c (E a b y)) = E a b (ps (Pi.single c y)) - r • ps (Pi.single c' y) := by
      rw [← hps a b _ (adjA_single_mem c hy), hcr, map_add, map_smul]
      abel
    rw [h1, inner_sub_right, inner_smul_right, hPy v hv c', mul_zero, sub_zero, ← hUk b a hab.symm]
    exact hPy _ (hL'k b a hab.symm v hv) c
  have hPadd : ∀ s : Finset (Fin n), ∀ g : Fin n → D, (∀ q ∈ s, P (g q)) → P (∑ q ∈ s, g q) := by
    intro s g hg v hv c
    have : (Pi.single c (∑ q ∈ s, g q) : Fin n → D) = ∑ q ∈ s, Pi.single c (g q) := by
      funext x
      simp only [Pi.single_apply, Finset.sum_apply]
      split_ifs <;> simp
    rw [this, map_sum, inner_sum]
    exact Finset.sum_eq_zero fun q hq => hg q hq v hv c
  have hcasP : ∀ y ∈ genSub E V, P y → P (casimirK ε E y) := by
    intro y hy hPy
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
    refine hPadd _ _ fun a _ => hPadd _ _ fun b hb => ?_
    have hq' : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hPE _ (closure_E_mem_genSub _ _ hy) (hPE y hy hPy b a hq') a b hq'.symm
  obtain ⟨C, hC⟩ := adjA_high (genSub E V) (casimirK ε E)
    (fun y hy => casimirK_mem_of_kStable hMk hy) Φ (fun y hy h0 => hΦP _ (hcasP y hy (hPΦ y h0)))
  obtain ⟨K, hK⟩ := coefB_adm hE hU hV hc hgap C
  have hTsym : ∀ x y, inner ℂ (casimirK ε E x) y = inner ℂ x (casimirK ε E y) := casimirK_inner_symm hUk
  set ℓ : D →ₗ[ℂ] ℂ := (innerₛₗ ℂ x').comp (ps.comp (LinearMap.single ℂ (fun _ => D) c))
  obtain ⟨z, hzM, hz⟩ := coefA_toSum hTsym (coefB_locFin hE hV.1 hV.2.1) ℓ C
    (finiteDimensional_layer hV.1 K) (layer_le_genSub K) (fun y hy θ hθ hyθ => hK y hy θ hθ hyθ)
    (fun y hy θ hθ hyθ => hPΦ y (hC y hy θ hθ hyθ) x' hm' c)
  exact ⟨z, hzM, fun y hy => hz y hy⟩

end Rep

end ReciprocityTheory.ChartRestriction.DS
