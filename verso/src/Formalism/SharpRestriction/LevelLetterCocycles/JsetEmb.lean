import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Lemmata.GeneralBFactUpperForm.Imports
import Lemmata.GeneralBFactUpperVariant.Imports

noncomputable section

namespace Formalism.MainNotions.N.JsetEmb

open Formalism.WeaklyAdmissibleFiltrations Module

section Iface

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def EmbSplitSt (PD : PeriodData G Qp K₀ K B BdR) : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [Fintype (K →ₐ[Qp] LL)],
    CharZero Qp → FiniteDimensional Qp LL → Fintype.card (K →ₐ[Qp] LL) = finrank Qp K →
    ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
      (ρ : Representation LL G V), Module.Finite LL ↥(DdR PD ρ) →
      finrank LL ↥(DdR PD ρ) = ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD ρ τ) ∧
      ∀ a : ℤ, finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
        ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(FildR PD ρ τ a)

end Iface

end Formalism.MainNotions.N.JsetEmb

end

noncomputable section

namespace Formalism.MainNotions.N.JsetEmb

open Formalism.WeaklyAdmissibleFiltrations Module Polynomial TensorProduct

section Gen

variable {Qp K LL M : Type*} [Field Qp] [Field K] [Field LL] [Algebra Qp K] [Algebra Qp LL]
  [AddCommGroup M] [Module LL M]

/- English proof (translation)
Rewrite using `[Lagrange.nodal_eq]`. Use `Finset.prod_dvd_of_coprime ?_ fun i _ => dvd_iff_isRoot.2 (hP i)` and prove the remaining obligations. Conclude with `(pairwise_coprime_X_sub_C hv).set_pairwise _`.
-/
theorem nodal_dvd_of_roots {ι : Type*} [Fintype ι] {v : ι → LL} (hv : Function.Injective v)
    {P : LL[X]} (hP : ∀ i, P.eval (v i) = 0) : Lagrange.nodal Finset.univ v ∣ P := by
  rw [Lagrange.nodal_eq]
  refine Finset.prod_dvd_of_coprime ?_ fun i _ => dvd_iff_isRoot.2 (hP i)
  exact (pairwise_coprime_X_sub_C hv).set_pairwise _

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_upper_form.goal1 .. | (apply Bl.general_b_fact_upper_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upp …`.
-/
theorem aeval_mem_stable_submodule (T : Module.End LL M) (W : Submodule LL M) (hW : ∀ x ∈ W, T x ∈ W)
    (p : LL[X]) : ∀ x ∈ W, aeval T p x ∈ W := by
  first | exact Bl.general_b_fact_upper_form.goal1 .. | (apply Bl.general_b_fact_upper_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› ‹_› ‹_› T W hW p x ‹_› | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› ‹_› ‹_› T W hW p x | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› ‹_› ‹_› T W hW p | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› ‹_› ‹_› T W hW | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› ‹_› ‹_› T W | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› ‹_› ‹_› T | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› ‹_› | exact @Bl.general_b_fact_upper_form.goal1 LL M ‹_› | exact @Bl.general_b_fact_upper_form.goal1 LL M | exact @Bl.general_b_fact_upper_form.goal1 LL

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_upper_variant.goal1 .. | (apply Bl.general_b_fact_upper_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_variant.goal1 <;> assumption) | (intros; apply @Bl.genera …`.
-/
theorem aeval_apply_eigenvector_alt (T : Module.End LL M) (a : LL) (y : M) (hy : T y = a • y) (p : LL[X]) :
    aeval T p y = p.eval a • y := by
  first | exact Bl.general_b_fact_upper_variant.goal1 .. | (apply Bl.general_b_fact_upper_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_variant.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_variant.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_variant.goal1 LL M ‹_› ‹_› ‹_› T a y hy p | exact @Bl.general_b_fact_upper_variant.goal1 LL M ‹_› ‹_› ‹_› T a y hy | exact @Bl.general_b_fact_upper_variant.goal1 LL M ‹_› ‹_› ‹_› T a y | exact @Bl.general_b_fact_upper_variant.goal1 LL M ‹_› ‹_› ‹_› T a | exact @Bl.general_b_fact_upper_variant.goal1 LL M ‹_› ‹_› ‹_› T | exact @Bl.general_b_fact_upper_variant.goal1 LL M ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_upper_variant.goal1 LL M ‹_› ‹_› | exact @Bl.general_b_fact_upper_variant.goal1 LL M ‹_› | exact @Bl.general_b_fact_upper_variant.goal1 LL M | exact @Bl.general_b_fact_upper_variant.goal1 LL

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_map, aeval_def, hom_eval₂]`. Conclude with `congrArg (fun f => eval₂ f (m α) g) (RingHom.ext fun q => (hm q).symm)`.
-/
theorem aeval_map_commute (m : K →+* Module.End LL M)
    (hm : ∀ q, m (algebraMap Qp K q) = algebraMap LL _ (algebraMap Qp LL q)) (α : K) (g : Qp[X]) :
    aeval (m α) (g.map (algebraMap Qp LL)) = m (aeval α g) := by
  rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
  exact congrArg (fun f => eval₂ f (m α) g) (RingHom.ext fun q => (hm q).symm)

/- English proof (translation)
Establish `hinj : Set.InjOn v (Finset.univ : Finset ι)` using `fun _ _ _ _ h => hv h`. Use `⟨fun i x => ?_, fun x => ?_, fun i j u hu => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : Lagrange.nodal Finset.univ v ∣ (X - C (v i)) * Lagrange.basis Finset.univ v i := by`. Use `nodal_dvd_of_roots hv fun j => ?_` and prove the remaining obligations. Rewrite using `[eval_mul]`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _), mul_zero]`. Establish `h0` using `congrArg (fun P => aeval T P x) hq`.

Simplify using `only [map_mul, map_sub, aeval_X, aeval_C, hT, zero_mul, Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply] at h0`. Conclude with `sub_eq_zero.1 h0`. Establish `hs` using `Lagrange.sum_basis hinj (Finset.univ_nonempty (α := ι))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum, LinearMap.sum_apply]`.

Use `_ = x := by rw [hs, map_one, Module.End.one_apply]`. Rewrite using `[aeval_apply_eigenvector_alt T (v j) u hu]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Lagrange.eval_basis_self hinj (Finset.mem_univ _), one_smul, if_pos rfl]`.

Rewrite using `[Lagrange.eval_basis_of_ne h (Finset.mem_univ _), zero_smul, if_neg h]`.
-/
theorem lagrange_eigen_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {v : ι → LL}
    (hv : Function.Injective v) (T : Module.End LL M)
    (hT : aeval T (Lagrange.nodal Finset.univ v) = 0) :
    (∀ i x, T (aeval T (Lagrange.basis Finset.univ v i) x) =
        v i • aeval T (Lagrange.basis Finset.univ v i) x) ∧
    (∀ x, ∑ i, aeval T (Lagrange.basis Finset.univ v i) x = x) ∧
    (∀ i j u, T u = v j • u →
        aeval T (Lagrange.basis Finset.univ v i) u = if i = j then u else 0) := by
  have hinj : Set.InjOn v (Finset.univ : Finset ι) := fun _ _ _ _ h => hv h
  refine ⟨fun i x => ?_, fun x => ?_, fun i j u hu => ?_⟩
  · obtain ⟨q, hq⟩ : Lagrange.nodal Finset.univ v ∣ (X - C (v i)) * Lagrange.basis Finset.univ v i := by
      refine nodal_dvd_of_roots hv fun j => ?_
      rw [eval_mul]
      by_cases h : j = i
      · subst h; simp
      · rw [Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _), mul_zero]
    have h0 := congrArg (fun P => aeval T P x) hq
    simp only [map_mul, map_sub, aeval_X, aeval_C, hT, zero_mul, Module.End.mul_apply,
      LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply] at h0
    exact sub_eq_zero.1 h0
  · have hs := Lagrange.sum_basis hinj (Finset.univ_nonempty (α := ι))
    calc ∑ i, aeval T (Lagrange.basis Finset.univ v i) x
        = aeval T (∑ i, Lagrange.basis Finset.univ v i) x := by
          rw [map_sum, LinearMap.sum_apply]
      _ = x := by rw [hs, map_one, Module.End.one_apply]
  · rw [aeval_apply_eigenvector_alt T (v j) u hu]
    by_cases h : i = j
    · subst h; rw [Lagrange.eval_basis_self hinj (Finset.mem_univ _), one_smul, if_pos rfl]
    · rw [Lagrange.eval_basis_of_ne h (Finset.mem_univ _), zero_smul, if_neg h]

/- English proof (translation)
Establish `pb : PowerBasis Qp K` using `Field.powerBasisOfFiniteOfSeparable Qp K`. Establish `hU : ∀ (τ : K →ₐ[Qp] LL) (u : M), u ∈ (⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)) ↔ ∀ c, m c u = τ c • u`. Introduce `τ u`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Establish `hv : Function.Injective fun τ : K →ₐ[Qp] LL => τ pb.gen` using `fun τ σ h => pb.algHom_ext h`.

Establish `hint : IsIntegral Qp pb.gen` using `Algebra.IsIntegral.isIntegral _`. Establish `hroot : ∀ τ : K →ₐ[Qp] LL, ((minpoly Qp pb.gen).map (algebraMap Qp LL)).eval (τ pb.gen) = 0`. Introduce `τ`. Rewrite using `[eval_map, ← aeval_def, aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hnf : (minpoly Qp pb.gen).map (algebraMap Qp LL) = Lagrange.nodal Finset.univ fun τ : K →ₐ[Qp] LL => τ pb.gen`.

Use `eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) (nodal_dvd_of_roots hv hroot) ?_` and prove the remaining obligations. Rewrite using `[natDegree_map, pb.natDegree_minpoly, ← pb.finrank, ← hcard, Lagrange.natDegree_nodal, Finset.card_univ]`. Establish `hT0 : aeval (m pb.gen) (Lagrange.nodal Finset.univ fun τ : K →ₐ[Qp] LL => τ pb.gen) = 0`. Rewrite using `[← hnf, aeval_map_commute m hm, minpoly.aeval, map_zero]`. Establish `: Nonempty (K →ₐ[Qp] LL)` using `Fintype.card_pos_iff.1 (hcard ▸ Module.finrank_pos)`.

Take `⟨heig, hsum, hsel⟩` from `lagrange_eigen_decomposition hv (m pb.gen) hT0`. Establish `hall : ∀ (τ : K →ₐ[Qp] LL) (u : M), m pb.gen u = τ pb.gen • u → ∀ c, m c u = τ c • u`. Introduce `τ u hu c`. Take `⟨g, -, rfl⟩` from `pb.exists_eq_aeval c`. Rewrite using `[← aeval_map_commute m hm, aeval_apply_eigenvector_alt _ _ u hu, eval_map, ← aeval_def, aeval_algHom_apply]`.

Use `set e : (K →ₐ[Qp] LL) → Module.End LL M := fun τ => aeval (m pb.gen) (Lagrange.basis Finset.univ (fun σ : K →ₐ[Qp] LL => σ pb.gen) τ) with he`. Establish `heW : ∀ τ x, x ∈ W → e τ x ∈ W` using `fun τ x hx => aeval_mem_stable_submodule _ W (fun y hy => hW pb.gen y hy) _ x hx`. Establish `heU : ∀ τ x, e τ x ∈ (⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id))` using `fun τ x => (hU τ _).2 (hall τ _ (heig τ x))`. Establish `hsel' : ∀ σ τ u, u ∈ (⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)) → e σ u = if σ = τ then u else 0` using `fun σ τ u hu => hsel σ τ u ((hU τ u).1 hu pb.gen)`. Set `Φ : W ≃ₗ[LL] ((τ : K →ₐ[Qp] LL) → ↥(W ⊓ ⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)))` to `{ toFun := fun w τ => ⟨e τ w, Submodule.mem_inf.2 ⟨heW τ w w.2, heU τ w⟩⟩ map_add' := fun x y => by`.

Use function extensionality and compare the values at `τ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show e τ (x + y : M) = e τ x + e τ y`. Rewrite using `[map_add]`. Use the proof step `map_smul' := fun a x => by`.

Use function extensionality and compare the values at `τ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show e τ (a • (x : M)) = a • e τ x`. Rewrite using `[map_smul]`. Use `invFun := fun F => ⟨∑ τ, (F τ : M), W.sum_mem fun τ _ => (Submodule.mem_inf.1 (F τ).2).1⟩`.

Use `left_inv := fun w => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ∑ τ, e τ w = w`. Conclude with `hsum w`. Use `right_inv := fun F => by`.

Use function extensionality and compare the values at `σ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show e σ (∑ τ, (F τ : M)) = F σ`. Rewrite using `[map_sum, Finset.sum_congr rfl fun τ _ => hsel' σ τ _ (Submodule.mem_inf.1 (F τ).2).2]`. Simplify using `}`.

Rewrite using `[Φ.finrank_eq, Module.finrank_pi_fintype]`.
-/
theorem finrank_sum_embedding_eigenspaces [FiniteDimensional Qp K] [Algebra.IsSeparable Qp K] [Fintype (K →ₐ[Qp] LL)]
    (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (m : K →+* Module.End LL M)
    (hm : ∀ q, m (algebraMap Qp K q) = algebraMap LL _ (algebraMap Qp LL q))
    (W : Submodule LL M) [FiniteDimensional LL W] (hW : ∀ c x, x ∈ W → m c x ∈ W) :
    finrank LL W = ∑ τ : K →ₐ[Qp] LL,
      finrank LL ↥(W ⊓ ⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)) := by
  classical
  have pb : PowerBasis Qp K := Field.powerBasisOfFiniteOfSeparable Qp K
  have hU : ∀ (τ : K →ₐ[Qp] LL) (u : M),
      u ∈ (⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)) ↔
        ∀ c, m c u = τ c • u := by
    intro τ u
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hv : Function.Injective fun τ : K →ₐ[Qp] LL => τ pb.gen := fun τ σ h => pb.algHom_ext h
  have hint : IsIntegral Qp pb.gen := Algebra.IsIntegral.isIntegral _
  have hroot : ∀ τ : K →ₐ[Qp] LL,
      ((minpoly Qp pb.gen).map (algebraMap Qp LL)).eval (τ pb.gen) = 0 := by
    intro τ
    rw [eval_map, ← aeval_def, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hnf : (minpoly Qp pb.gen).map (algebraMap Qp LL) =
      Lagrange.nodal Finset.univ fun τ : K →ₐ[Qp] LL => τ pb.gen := by
    refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _)
      (nodal_dvd_of_roots hv hroot) ?_
    rw [natDegree_map, pb.natDegree_minpoly, ← pb.finrank, ← hcard, Lagrange.natDegree_nodal,
      Finset.card_univ]
  have hT0 : aeval (m pb.gen) (Lagrange.nodal Finset.univ fun τ : K →ₐ[Qp] LL => τ pb.gen) = 0 := by
    rw [← hnf, aeval_map_commute m hm, minpoly.aeval, map_zero]
  have : Nonempty (K →ₐ[Qp] LL) :=
    Fintype.card_pos_iff.1 (hcard ▸ Module.finrank_pos)
  obtain ⟨heig, hsum, hsel⟩ := lagrange_eigen_decomposition hv (m pb.gen) hT0

  have hall : ∀ (τ : K →ₐ[Qp] LL) (u : M), m pb.gen u = τ pb.gen • u → ∀ c, m c u = τ c • u := by
    intro τ u hu c
    obtain ⟨g, -, rfl⟩ := pb.exists_eq_aeval c
    rw [← aeval_map_commute m hm, aeval_apply_eigenvector_alt _ _ u hu, eval_map, ← aeval_def,
      aeval_algHom_apply]
  set e : (K →ₐ[Qp] LL) → Module.End LL M := fun τ =>
    aeval (m pb.gen) (Lagrange.basis Finset.univ (fun σ : K →ₐ[Qp] LL => σ pb.gen) τ) with he
  have heW : ∀ τ x, x ∈ W → e τ x ∈ W := fun τ x hx =>
    aeval_mem_stable_submodule _ W (fun y hy => hW pb.gen y hy) _ x hx
  have heU : ∀ τ x, e τ x ∈ (⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)) :=
    fun τ x => (hU τ _).2 (hall τ _ (heig τ x))
  have hsel' : ∀ σ τ u, u ∈ (⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)) →
      e σ u = if σ = τ then u else 0 := fun σ τ u hu => hsel σ τ u ((hU τ u).1 hu pb.gen)
  let Φ : W ≃ₗ[LL] ((τ : K →ₐ[Qp] LL) →
      ↥(W ⊓ ⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id))) :=
    { toFun := fun w τ => ⟨e τ w, Submodule.mem_inf.2 ⟨heW τ w w.2, heU τ w⟩⟩
      map_add' := fun x y => by
        funext τ; apply Subtype.ext
        show e τ (x + y : M) = e τ x + e τ y
        rw [map_add]
      map_smul' := fun a x => by
        funext τ; apply Subtype.ext
        show e τ (a • (x : M)) = a • e τ x
        rw [map_smul]
      invFun := fun F => ⟨∑ τ, (F τ : M), W.sum_mem fun τ _ => (Submodule.mem_inf.1 (F τ).2).1⟩
      left_inv := fun w => by
        apply Subtype.ext
        show ∑ τ, e τ w = w
        exact hsum w
      right_inv := fun F => by
        funext σ; apply Subtype.ext
        show e σ (∑ τ, (F τ : M)) = F σ
        rw [map_sum, Finset.sum_congr rfl fun τ _ => hsel' σ τ _ (Submodule.mem_inf.1 (F τ).2).2]
        simp }
  rw [Φ.finrank_eq, Module.finrank_pi_fintype]

end Gen

section Conc

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [mulVdR]`. Consider the case `add x y hx hy => rw [map_add, hx, hy, map_add]`.
-/
theorem de_rham_mul_one : mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) (1 : K) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR]
  | add x y hx hy => rw [map_add, hx, hy, map_add]

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply]`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [mulVdR]`.

Consider the case `add x y hx hy => rw [map_add, hx, hy, map_add, map_add]`.
-/
theorem de_rham_mul_mul (c d : K) : mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) (c * d) =
    mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c * mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) d := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [mulVdR]`. Consider the case `add x y hx hy => rw [map_add, hx, hy]`.

Simplify using the standard rewrite rules.
-/
theorem de_rham_mul_zero : mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) (0 : K) = 0 := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR]
  | add x y hx hy => rw [map_add, hx, hy]; simp

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply]`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [mulVdR, add_mul, TensorProduct.tmul_add]`.

Consider the case `add x y hx hy => rw [map_add, hx, hy, map_add, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem de_rham_mul_add (c d : K) : mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) (c + d) =
    mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c + mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) d := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.add_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR, add_mul, TensorProduct.tmul_add]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]; abel

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[Module.algebraMap_end_apply]`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`.

Simplify using `only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply Qp K BdR, ← Algebra.smul_def, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', algebraMap_smul]`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`.
-/
theorem de_rham_mul_algebraMap (q : Qp) : mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) (algebraMap Qp K q) =
    algebraMap LL (Module.End LL (V ⊗[Qp] BdR)) (algebraMap Qp LL q) := by
  refine LinearMap.ext fun x => ?_
  rw [Module.algebraMap_end_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    rw [← IsScalarTower.algebraMap_apply Qp K BdR, ← Algebra.smul_def, ← TensorProduct.smul_tmul,
      TensorProduct.smul_tmul', algebraMap_smul]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

variable (PD : PeriodData G Qp K₀ K B BdR) (ρ : Representation LL G V)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVdR, mulVdR, map_mul, AlgEquiv.commutes]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem de_rham_action_mul (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c x) =
      mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR, map_mul, AlgEquiv.commutes]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢`. Introduce `g`. Rewrite using `[de_rham_action_mul, hx g]`.
-/
theorem de_rham_mul_stable (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c x ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [de_rham_action_mul, hx g]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Use `⟨v ⊗ₜ ⟨algebraMap K BdR c * b, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Algebra.smul_def]`. Conclude with `(PD.Fil a).smul_mem c b.2`. Simplify using `[mulVdR]`. Consider the case `add y z hy hz => rw [map_add, map_add]`. Conclude with `Submodule.add_mem _ hy hz`.
-/
theorem de_rham_mul_filtration_stable (a : ℤ) (c : K) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨algebraMap K BdR c * b, ?_⟩, ?_⟩
    · rw [← Algebra.smul_def]; exact (PD.Fil a).smul_mem c b.2
    · simp [mulVdR]
  | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

end Conc

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

/- English proof (translation)
Introduce `LL _ _ _ hQp _ hcard V _ _ _ _ ρ hfin`. Use `hQp` as an intermediate fact. Use `hfin` as an intermediate fact. Establish `: FiniteDimensional Qp K` using `PD.finK`. Establish `: Algebra.IsSeparable Qp K` using `Algebra.IsAlgebraic.isSeparable_of_perfectField`.

Set `m : K →+* Module.End LL (V ⊗[Qp] BdR)` to `{ toFun := fun c => mulVdR c map_one' := de_rham_mul_one map_mul' := de_rham_mul_mul map_zero' := de_rham_mul_zero map_add' := de_rham_mul_add }`. Establish `hm : ∀ q, m (algebraMap Qp K q) = algebraMap LL _ (algebraMap Qp LL q)` using `de_rham_mul_algebraMap`. Use `⟨finrank_sum_embedding_eigenspaces hcard m hm (DdR PD ρ) fun c x hx => de_rham_mul_stable PD ρ c x hx, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[finrank_sum_embedding_eigenspaces hcard m hm (DdR PD ρ ⊓ FilV PD a) fun c x hx => Submodule.mem_inf.2 ⟨de_rham_mul_stable PD ρ c x (Submodule.mem_inf.1 hx).1, de_rham_mul_filtration_stable PD a c x (Submodule.mem_inf.1 hx).2⟩]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[FildR, DdRE, inf_right_comm]`. Both sides reduce to the same expression.
-/
theorem embSplit (PD : PeriodData G Qp K₀ K B BdR) : EmbSplitSt PD := by
  intro LL _ _ _ hQp _ hcard V _ _ _ _ ρ hfin
  have := hQp
  have := hfin
  have : FiniteDimensional Qp K := PD.finK
  have : Algebra.IsSeparable Qp K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let m : K →+* Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR c
      map_one' := de_rham_mul_one
      map_mul' := de_rham_mul_mul
      map_zero' := de_rham_mul_zero
      map_add' := de_rham_mul_add }
  have hm : ∀ q, m (algebraMap Qp K q) = algebraMap LL _ (algebraMap Qp LL q) := de_rham_mul_algebraMap
  refine ⟨finrank_sum_embedding_eigenspaces hcard m hm (DdR PD ρ) fun c x hx => de_rham_mul_stable PD ρ c x hx, fun a => ?_⟩
  rw [finrank_sum_embedding_eigenspaces hcard m hm (DdR PD ρ ⊓ FilV PD a) fun c x hx => Submodule.mem_inf.2
    ⟨de_rham_mul_stable PD ρ c x (Submodule.mem_inf.1 hx).1,
      de_rham_mul_filtration_stable PD a c x (Submodule.mem_inf.1 hx).2⟩]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [FildR, DdRE, inf_right_comm]
  rfl

end Formalism.MainNotions.N.JsetEmb

noncomputable section

namespace Formalism.MainNotions.N.JsetEmb

open Formalism.WeaklyAdmissibleFiltrations Module Polynomial TensorProduct

section GenSup

variable {Qp K LL M : Type*} [Field Qp] [Field K] [Field LL] [Algebra Qp K] [Algebra Qp LL]
  [AddCommGroup M] [Module LL M]

/- English proof (translation)
Establish `pb : PowerBasis Qp K` using `Field.powerBasisOfFiniteOfSeparable Qp K`. Establish `hU : ∀ (τ : K →ₐ[Qp] LL) (u : M), u ∈ (⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)) ↔ ∀ c, m c u = τ c • u`. Introduce `τ u`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Establish `hv : Function.Injective fun τ : K →ₐ[Qp] LL => τ pb.gen` using `fun τ σ h => pb.algHom_ext h`.

Establish `hint : IsIntegral Qp pb.gen` using `Algebra.IsIntegral.isIntegral _`. Establish `hroot : ∀ τ : K →ₐ[Qp] LL, ((minpoly Qp pb.gen).map (algebraMap Qp LL)).eval (τ pb.gen) = 0`. Introduce `τ`. Rewrite using `[eval_map, ← aeval_def, aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hnf : (minpoly Qp pb.gen).map (algebraMap Qp LL) = Lagrange.nodal Finset.univ fun τ : K →ₐ[Qp] LL => τ pb.gen`.

Use `eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) (nodal_dvd_of_roots hv hroot) ?_` and prove the remaining obligations. Rewrite using `[natDegree_map, pb.natDegree_minpoly, ← pb.finrank, ← hcard, Lagrange.natDegree_nodal, Finset.card_univ]`. Establish `hT0 : aeval (m pb.gen) (Lagrange.nodal Finset.univ fun τ : K →ₐ[Qp] LL => τ pb.gen) = 0`. Rewrite using `[← hnf, aeval_map_commute m hm, minpoly.aeval, map_zero]`. Establish `: Nonempty (K →ₐ[Qp] LL)` using `Fintype.card_pos_iff.1 (hcard ▸ Module.finrank_pos)`.

Take `⟨heig, hsum, -⟩` from `lagrange_eigen_decomposition hv (m pb.gen) hT0`. Establish `hall : ∀ (τ : K →ₐ[Qp] LL) (u : M), m pb.gen u = τ pb.gen • u → ∀ c, m c u = τ c • u`. Introduce `τ u hu c`. Take `⟨g, -, rfl⟩` from `pb.exists_eq_aeval c`. Rewrite using `[← aeval_map_commute m hm, aeval_apply_eigenvector_alt _ _ u hu, eval_map, ← aeval_def, aeval_algHom_apply]`.

Introduce `x hx`. Rewrite using `[← hsum x]`. Use `Submodule.sum_mem _ fun τ _ => Submodule.mem_iSup_of_mem τ (Submodule.mem_inf.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `aeval_mem_stable_submodule _ W (fun y hy => hW pb.gen y hy) _ x hx`. Conclude with `(hU τ _).2 (hall τ _ (heig τ x))`.
-/
theorem le_iSup_embedding_eigenspaces [FiniteDimensional Qp K] [Algebra.IsSeparable Qp K]
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (m : K →+* Module.End LL M)
    (hm : ∀ q, m (algebraMap Qp K q) = algebraMap LL _ (algebraMap Qp LL q))
    (W : Submodule LL M) (hW : ∀ c x, x ∈ W → m c x ∈ W) :
    W ≤ ⨆ τ : K →ₐ[Qp] LL,
      W ⊓ ⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id) := by
  classical
  have pb : PowerBasis Qp K := Field.powerBasisOfFiniteOfSeparable Qp K
  have hU : ∀ (τ : K →ₐ[Qp] LL) (u : M),
      u ∈ (⨅ c : K, LinearMap.ker ((m c : M →ₗ[LL] M) - τ c • LinearMap.id)) ↔
        ∀ c, m c u = τ c • u := by
    intro τ u
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hv : Function.Injective fun τ : K →ₐ[Qp] LL => τ pb.gen := fun τ σ h => pb.algHom_ext h
  have hint : IsIntegral Qp pb.gen := Algebra.IsIntegral.isIntegral _
  have hroot : ∀ τ : K →ₐ[Qp] LL,
      ((minpoly Qp pb.gen).map (algebraMap Qp LL)).eval (τ pb.gen) = 0 := by
    intro τ
    rw [eval_map, ← aeval_def, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hnf : (minpoly Qp pb.gen).map (algebraMap Qp LL) =
      Lagrange.nodal Finset.univ fun τ : K →ₐ[Qp] LL => τ pb.gen := by
    refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _)
      (nodal_dvd_of_roots hv hroot) ?_
    rw [natDegree_map, pb.natDegree_minpoly, ← pb.finrank, ← hcard, Lagrange.natDegree_nodal,
      Finset.card_univ]
  have hT0 : aeval (m pb.gen) (Lagrange.nodal Finset.univ fun τ : K →ₐ[Qp] LL => τ pb.gen) = 0 := by
    rw [← hnf, aeval_map_commute m hm, minpoly.aeval, map_zero]
  have : Nonempty (K →ₐ[Qp] LL) :=
    Fintype.card_pos_iff.1 (hcard ▸ Module.finrank_pos)
  obtain ⟨heig, hsum, -⟩ := lagrange_eigen_decomposition hv (m pb.gen) hT0
  have hall : ∀ (τ : K →ₐ[Qp] LL) (u : M), m pb.gen u = τ pb.gen • u → ∀ c, m c u = τ c • u := by
    intro τ u hu c
    obtain ⟨g, -, rfl⟩ := pb.exists_eq_aeval c
    rw [← aeval_map_commute m hm, aeval_apply_eigenvector_alt _ _ u hu, eval_map, ← aeval_def,
      aeval_algHom_apply]
  intro x hx
  rw [← hsum x]
  refine Submodule.sum_mem _ fun τ _ => Submodule.mem_iSup_of_mem τ (Submodule.mem_inf.2 ⟨?_, ?_⟩)
  · exact aeval_mem_stable_submodule _ W (fun y hy => hW pb.gen y hy) _ x hx
  · exact (hU τ _).2 (hall τ _ (heig τ x))

end GenSup

section ConcJump

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Establish `: FiniteDimensional Qp K` using `PD.finK`. Establish `: Algebra.IsSeparable Qp K` using `Algebra.IsAlgebraic.isSeparable_of_perfectField`. Set `m : K →+* Module.End LL (V ⊗[Qp] BdR)` to `{ toFun := fun c => mulVdR c map_one' := de_rham_mul_one map_mul' := de_rham_mul_mul map_zero' := de_rham_mul_zero map_add' := de_rham_mul_add }`. Establish `hm : ∀ q, m (algebraMap Qp K q) = algebraMap LL _ (algebraMap Qp LL q)` using `de_rham_mul_algebraMap`. Use `le_antisymm ?_ (iSup_le fun τ => ?_)` and prove the remaining obligations.

Use `(le_iSup_embedding_eigenspaces hcard m hm (DdR PD ρ ⊓ FilV PD b) fun c x hx => Submodule.mem_inf.2 ⟨de_rham_mul_stable PD ρ c x (Submodule.mem_inf.1 hx).1, de_rham_mul_filtration_stable PD b c x (Submodule.mem_inf.1 hx).2⟩).trans (iSup_mono fun τ => ?_)` and prove the remaining obligations. Introduce `x hx`. Take `⟨⟨h1, h2⟩, h3⟩` from `hx`. Conclude with `⟨⟨h1, h3⟩, h2⟩`. Introduce `x hx`.

Take `⟨⟨h1, -⟩, h2⟩` from `hx`. Conclude with `⟨h1, h2⟩`.
-/
theorem de_rham_filtration_eq_iSup_embeddings [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (b : ℤ) :
    DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) b = ⨆ τ : K →ₐ[Qp] LL, FildR PD ρ τ b := by
  have : FiniteDimensional Qp K := PD.finK
  have : Algebra.IsSeparable Qp K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let m : K →+* Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR c
      map_one' := de_rham_mul_one
      map_mul' := de_rham_mul_mul
      map_zero' := de_rham_mul_zero
      map_add' := de_rham_mul_add }
  have hm : ∀ q, m (algebraMap Qp K q) = algebraMap LL _ (algebraMap Qp LL q) := de_rham_mul_algebraMap
  refine le_antisymm ?_ (iSup_le fun τ => ?_)
  · refine (le_iSup_embedding_eigenspaces hcard m hm (DdR PD ρ ⊓ FilV PD b) fun c x hx =>
      Submodule.mem_inf.2 ⟨de_rham_mul_stable PD ρ c x (Submodule.mem_inf.1 hx).1,
        de_rham_mul_filtration_stable PD b c x (Submodule.mem_inf.1 hx).2⟩).trans (iSup_mono fun τ => ?_)
    intro x hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    exact ⟨⟨h1, h3⟩, h2⟩
  · intro x hx
    obtain ⟨⟨h1, -⟩, h2⟩ := hx
    exact ⟨h1, h2⟩

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Establish `heq : ∀ τ : K →ₐ[Qp] LL, FildR PD ρ τ (a + 1) = FildR PD ρ τ a` using `fun τ => not_not.1 fun h => hno ⟨τ, h⟩`. Apply `ha` to reduce the goal to its premises. Rewrite using `[de_rham_filtration_eq_iSup_embeddings PD hcard ρ (a + 1), de_rham_filtration_eq_iSup_embeddings PD hcard ρ a]`. Conclude with `iSup_congr heq`.
-/
theorem jump_exists_of_filtration_strict [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (a : ℤ)
    (ha : DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (a + 1) ≠ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) :
    ∃ τ : K →ₐ[Qp] LL, IsJumpV PD ρ τ a := by
  by_contra hno
  have heq : ∀ τ : K →ₐ[Qp] LL, FildR PD ρ τ (a + 1) = FildR PD ρ τ a :=
    fun τ => not_not.1 fun h => hno ⟨τ, h⟩
  apply ha
  rw [de_rham_filtration_eq_iSup_embeddings PD hcard ρ (a + 1), de_rham_filtration_eq_iSup_embeddings PD hcard ρ a]
  exact iSup_congr heq

end ConcJump

end Formalism.MainNotions.N.JsetEmb

noncomputable section

namespace Formalism.MainNotions.N.JsetEmb

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module

/- English proof (translation)
Take `⟨-, -, hKs, hLL⟩` from `h`. Establish `: FiniteDimensional ℚ_[l] ↥LL.1` using `LL.2`. Establish `: FiniteDimensional ℚ_[l] ↥K.1` using `K.2`. Establish `key : ∀ g : ↥K.1 →ₐ[ℚ_[l]] Om l, ∀ x, g x ∈ LL.1`. Introduce `g x`.

Establish `h1` using `g.liftNormal_commutes (Om l) x`. Establish `h2` using `hLL (((g.liftNormal (Om l))).comp (Ks K s).val) ⟨x.1, hKs x.2⟩`. Simplify using `only [AlgHom.comp_apply, IntermediateField.coe_val] at h2`. Rewrite `h1` using `[Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[← h1]`.

Conclude with `h2`. Set `e : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≃ (↥K.1 →ₐ[ℚ_[l]] Om l)` to `{ toFun := fun f => LL.1.val.comp f invFun := fun g => g.codRestrict LL.1.toSubalgebra (key g) left_inv := fun f => by ext; rfl right_inv := fun g => by ext; rfl }`. Rewrite using `[Nat.card_congr e]`. Conclude with `AlgHom.natCard_of_splits _ _ _ (fun _ => IsAlgClosed.splits _)`.
-/
theorem card_emb_good {l : ℕ} [Fact l.Prime] {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  obtain ⟨-, -, hKs, hLL⟩ := h
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have key : ∀ g : ↥K.1 →ₐ[ℚ_[l]] Om l, ∀ x, g x ∈ LL.1 := by
    intro g x
    have h1 := g.liftNormal_commutes (Om l) x
    have h2 := hLL (((g.liftNormal (Om l))).comp (Ks K s).val) ⟨x.1, hKs x.2⟩
    simp only [AlgHom.comp_apply, IntermediateField.coe_val] at h2
    rw [Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [← h1]
    exact h2
  let e : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≃ (↥K.1 →ₐ[ℚ_[l]] Om l) :=
    { toFun := fun f => LL.1.val.comp f
      invFun := fun g => g.codRestrict LL.1.toSubalgebra (key g)
      left_inv := fun f => by ext; rfl
      right_inv := fun g => by ext; rfl }
  rw [Nat.card_congr e]
  exact AlgHom.natCard_of_splits _ _ _ (fun _ => IsAlgClosed.splits _)

/- English proof (translation)
Introduce `D HW l _ K s LL h Y a ha`. Establish `hc` using `card_emb_good h`. Establish `: FiniteDimensional ℚ_[l] ↥K.1` using `K.2`. Establish `: Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)` using `Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')`. Use `letI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)`.

Conclude with `jump_exists_of_filtration_strict ((D.loc l).PD K) (by rw [Fintype.card_eq_nat_card, hc]) Y.ρ a ha`.
-/
theorem jsetSplit_all : ∀ (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (a : ℤ),
    a ∈ Formalism.MainNotions.LocalSituation.Jset (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) Y →
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, IsJumpV ((D.loc l).PD K) Y.ρ τ a := by
  intro D HW l _ K s LL h Y a ha
  have hc := card_emb_good h
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  exact jump_exists_of_filtration_strict ((D.loc l).PD K) (by rw [Fintype.card_eq_nat_card, hc]) Y.ρ a ha

end Formalism.MainNotions.N.JsetEmb
