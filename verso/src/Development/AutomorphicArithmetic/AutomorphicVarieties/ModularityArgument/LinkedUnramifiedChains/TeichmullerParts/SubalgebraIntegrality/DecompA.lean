import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicGroupTopology
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCompactFundamentalSetUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace UpperTheory.V.Z.J.D.Dc

open GlobalTheory.DefU in

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable E n`. Take `⟨C, hC, hcov⟩` from `UpperTheory.exists_compact_fundamental_set_unitary E n`. Take `⟨B, hdef, hinv⟩` from `UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient (UA E n) (ratU E n) C hC hcov`. Establish `hsum` using `UpperTheory.mem_iSup_automorphicReps_of_invariant_form E n B (fun φ h => hdef φ h.cont h.left) (fun x φ ψ h h' => hinv x φ ψ h.cont h.left h'.cont h'.left)`. Establish `hi` using `Submodule.map_injective_of_injective (autU E n).injective_subtype`.

Take `⟨κ, _, U, P, hU, hP, hPe, hPs⟩` from `UpperTheory.exists_equivariant_projections_of_sum_irreducible (UA E n) (autU E n) (autRep E n) (fun x => by`. Establish `key : ∀ (Z : Submodule ℂ (autU E n)), (∀ σ, IsAutRepU σ → σ.comap (autU E n).subtype ≤ Z) → x ∈ Z`. Introduce `Z hZ`. Establish `hle : (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1) ≤ Z.map (autU E n).subtype` using `iSup_le fun σ φ hφ => ⟨⟨φ, σ.2.aut φ hφ⟩, hZ σ.1 σ.2 hφ, rfl⟩`. Take `⟨y, hy, e⟩` from `hle (hsum x.1 x.2)`.

Conclude with `Subtype.ext e ▸ hy`. Use `key _ fun σ hσ => ?_` and prove the remaining obligations. Establish `hm : (σ.comap (autU E n).subtype).map (autU E n).subtype = σ`. Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.2 hσ.aut`.

Use `le_iSup_of_le ⟨σ.comap (autU E n).subtype, fun h => hσ.ne_bot ?_, fun g u hu => hσ.stable g u.1 hu, fun N hN hst => ?_⟩ le_rfl` and prove the remaining obligations. Rewrite using `[← hm, h, Submodule.map_bot]`. Use `(hσ.irred (N.map (autU E n).subtype) (hm ▸ Submodule.map_mono hN) ?_).imp (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans hm.symm)` and prove the remaining obligations. Introduce and unpack `g _ ⟨u, hu, rfl⟩`. Conclude with `⟨_, hst g u hu, rfl⟩) M hM`.

Use `⟨κ, inferInstance, fun i => (U i).map (autU E n).subtype, P, fun i => ⟨?_, ?_, ?_, fun N hN hst => ?_⟩, fun i φ => ⟨_, hP i φ, rfl⟩, hPe, hPs⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨u, -, rfl⟩`. Conclude with `u.2`. Introduce and unpack `g _ ⟨u, hu, rfl⟩`. Conclude with `⟨_, (hU i).2.1 g u hu, rfl⟩`.

Conclude with `fun h => (hU i).1 (hi (h.trans (Submodule.map_bot _).symm))`. Establish `hm : (N.comap (autU E n).subtype).map (autU E n).subtype = N`. Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.2 (hN.trans (Submodule.map_subtype_le _ _))`. Break down `(hU i).2.2 (N.comap (autU E n).subtype) (fun u hu => by` into its components or cases.

Take `⟨w, hw, e⟩` from `hN hu`. Conclude with `Subtype.ext e ▸ hw) (fun g u hu => hst g u.1 hu) with h | h`. Use `left`. Rewrite using `[← hm, h, Submodule.map_bot]`. Use `right`.

Rewrite using `[← hm, h]`.
-/
theorem autProj (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M : Submodule ℂ (autU E n))
    (hM : FiniteDimensional ℂ M) :
    ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA E n → ℂ)) (P : κ → autU E n →ₗ[ℂ] autU E n),
      (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧ (∀ i x φ, P i (autRep E n x φ) = autRep E n x (P i φ)) ∧
      ∀ φ ∈ M, ∑ i, P i φ = φ := by
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable E n
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_unitary E n
  obtain ⟨B, hdef, hinv⟩ := UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient (UA E n) (ratU E n) C hC hcov
  have hsum := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E n B (fun φ h => hdef φ h.cont h.left)
    (fun x φ ψ h h' => hinv x φ ψ h.cont h.left h'.cont h'.left)
  have hi := Submodule.map_injective_of_injective (autU E n).injective_subtype
  obtain ⟨κ, _, U, P, hU, hP, hPe, hPs⟩ := UpperTheory.exists_equivariant_projections_of_sum_irreducible (UA E n) (autU E n) (autRep E n) (fun x => by
    have key : ∀ (Z : Submodule ℂ (autU E n)), (∀ σ, IsAutRepU σ → σ.comap (autU E n).subtype ≤ Z) → x ∈ Z := by
      intro Z hZ
      have hle : (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1) ≤ Z.map (autU E n).subtype :=
        iSup_le fun σ φ hφ => ⟨⟨φ, σ.2.aut φ hφ⟩, hZ σ.1 σ.2 hφ, rfl⟩
      obtain ⟨y, hy, e⟩ := hle (hsum x.1 x.2)
      exact Subtype.ext e ▸ hy
    refine key _ fun σ hσ => ?_
    have hm : (σ.comap (autU E n).subtype).map (autU E n).subtype = σ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hσ.aut
    refine le_iSup_of_le ⟨σ.comap (autU E n).subtype, fun h => hσ.ne_bot ?_, fun g u hu => hσ.stable g u.1 hu,
      fun N hN hst => ?_⟩ le_rfl
    · rw [← hm, h, Submodule.map_bot]
    · refine (hσ.irred (N.map (autU E n).subtype) (hm ▸ Submodule.map_mono hN) ?_).imp
        (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans hm.symm)
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨_, hst g u hu, rfl⟩) M hM
  refine ⟨κ, inferInstance, fun i => (U i).map (autU E n).subtype, P, fun i => ⟨?_, ?_, ?_, fun N hN hst => ?_⟩,
    fun i φ => ⟨_, hP i φ, rfl⟩, hPe, hPs⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, (hU i).2.1 g u hu, rfl⟩
  · exact fun h => (hU i).1 (hi (h.trans (Submodule.map_bot _).symm))
  · have hm : (N.comap (autU E n).subtype).map (autU E n).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hN.trans (Submodule.map_subtype_le _ _))
    rcases (hU i).2.2 (N.comap (autU E n).subtype) (fun u hu => by
      obtain ⟨w, hw, e⟩ := hN hu
      exact Subtype.ext e ▸ hw) (fun g u hu => hst g u.1 hu) with h | h
    · left; rw [← hm, h, Submodule.map_bot]
    · right; rw [← hm, h]

/- English proof (translation)
Set `Ψ : (Π₀ j, σ j) →ₗ[ℂ] M` to `DFinsupp.lsum ℕ fun j => (σ j).subtype`. Establish `hinj : Function.Injective Ψ` using `h.dfinsupp_lsum_injective`. Establish `hΨ : ∀ y, Ψ y = ∑ j, (y j : M)` using `fun y => by`. Express the relevant statement in the definitionally equal form `DFinsupp.lsum ℕ (fun j => (σ j).subtype) y = _`. Rewrite using `[DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum_eq_sum_fintype _ (fun j => map_zero _)]`.

Both sides reduce to the same expression. Establish `hr : LinearMap.range Ψ = ⨆ j, σ j` using `(Submodule.iSup_eq_range_dfinsupp_lsum σ).symm`. Set `e : (Π₀ j, σ j) ≃ₗ[ℂ] ↥(⨆ j, σ j)` to `(LinearEquiv.ofInjective Ψ hinj).trans (LinearEquiv.ofEq _ _ hr)`. Establish `he : ∀ y, (e y : M) = Ψ y` using `fun y => rfl`. Use `⟨fun t => (σ t).subtype ∘ₗ DFinsupp.lapply t ∘ₗ e.symm.toLinearMap, fun t φ => (e.symm φ t).2, fun φ => ?_, fun x hx φ hφ t => ?_⟩` and prove the remaining obligations.

Use `he (e.symm φ)` as an intermediate fact. Rewrite `this` using `[e.apply_symm_apply, hΨ]`. Conclude with `this.symm`. Set `y : Π₀ j, σ j` to `DFinsupp.mk Finset.univ fun j => ⟨x j, hx j⟩`. Establish `hy : ∀ j, (y j : M) = x j` using `fun j => by`.

Simplify using `[y, DFinsupp.mk_apply]`. Establish `: e.symm φ = y`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[he, hΨ, hφ]`.

Conclude with `Finset.sum_congr rfl fun j _ => (hy j).symm`. Express the relevant statement in the definitionally equal form `((e.symm φ) t : M) = x t`. Rewrite using `[this, hy]`.
-/
theorem indepProj {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (σ : J → Submodule ℂ M) (h : iSupIndep σ) :
    ∃ P : J → ↥(⨆ j, σ j) →ₗ[ℂ] M, (∀ t φ, P t φ ∈ σ t) ∧ (∀ φ, ∑ t, P t φ = φ) ∧
      ∀ (x : J → M), (∀ j, x j ∈ σ j) → ∀ φ : ↥(⨆ j, σ j), (φ : M) = ∑ j, x j → ∀ t, P t φ = x t := by
  classical
  let Ψ : (Π₀ j, σ j) →ₗ[ℂ] M := DFinsupp.lsum ℕ fun j => (σ j).subtype
  have hinj : Function.Injective Ψ := h.dfinsupp_lsum_injective
  have hΨ : ∀ y, Ψ y = ∑ j, (y j : M) := fun y => by
    change DFinsupp.lsum ℕ (fun j => (σ j).subtype) y = _
    rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum_eq_sum_fintype _ (fun j => map_zero _)]
    rfl
  have hr : LinearMap.range Ψ = ⨆ j, σ j := (Submodule.iSup_eq_range_dfinsupp_lsum σ).symm
  let e : (Π₀ j, σ j) ≃ₗ[ℂ] ↥(⨆ j, σ j) := (LinearEquiv.ofInjective Ψ hinj).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ y, (e y : M) = Ψ y := fun y => rfl
  refine ⟨fun t => (σ t).subtype ∘ₗ DFinsupp.lapply t ∘ₗ e.symm.toLinearMap, fun t φ => (e.symm φ t).2, fun φ => ?_,
    fun x hx φ hφ t => ?_⟩
  · have := he (e.symm φ)
    rw [e.apply_symm_apply, hΨ] at this
    exact this.symm
  · let y : Π₀ j, σ j := DFinsupp.mk Finset.univ fun j => ⟨x j, hx j⟩
    have hy : ∀ j, (y j : M) = x j := fun j => by
      simp [y, DFinsupp.mk_apply]
    have : e.symm φ = y := by
      rw [LinearEquiv.symm_apply_eq]
      refine Subtype.ext ?_
      rw [he, hΨ, hφ]
      exact Finset.sum_congr rfl fun j _ => (hy j).symm
    change ((e.symm φ) t : M) = x t
    rw [this, hy]

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} {Y D : Type} [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup D] [Module ℂ D]

/- English proof (translation)
Set `Φ : Fin m → D →ₗ[ℂ] W` to `fun i => (tf (F i)).codRestrict W (hFW i)`. Establish `hΦ : ∀ i ℓ, (Φ i ℓ : UA E n → ℂ) = tf (F i) ℓ` using `fun _ _ => rfl`. Establish `hex : ∀ t i, ∃ G ∈ A, ∀ ℓ, tf G ℓ = P t (Φ i ℓ)` using `fun t i => hsur (P t ∘ₗ Φ i) (fun ℓ => hσ t _ (hP t _)) fun ℓ x hx => by`. Establish `e : (⟨RU E n x (Φ i ℓ), hW x _ (Φ i ℓ).2⟩ : W) = Φ i (r x ℓ)` using `Subtype.ext (heq i ℓ x hx)`. Conclude with `(hPe t x (Φ i ℓ)).symm.trans (by rw [e]; rfl)`.

Use `choose G hGA hG using hex`. Use `⟨G, hGA, fun t i ℓ => hG t i ℓ ▸ hP t _, funext fun i => ?_, fun T k a hTA hT hF t i => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_apply]`. Use `sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun t _ => hGA t i) (hFA i)) fun ℓ => ?_)` and prove the remaining obligations. Simplify using `only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hG]`.

Conclude with `sub_eq_zero.2 (hPs i ℓ)`. Use `sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun j _ => A.smul_mem _ (hTA _ (hGA t j))) (hGA t i)) fun ℓ => ?_)` and prove the remaining obligations. Establish `e : ∑ j, a i j • (⟨RU E n k (Φ j ℓ), hW k _ (Φ j ℓ).2⟩ : W) = Φ i ℓ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun y => tf y ℓ) (hF i)` as an intermediate fact.

Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hT] at this`. Rewrite using `[Submodule.coe_sum]`. Conclude with `this`. Establish `e2` using `congrArg (P t) e`. Simplify using `only [map_sum, map_smul, hPe] at e2`.

Simplify using `only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, hT, hG]`. Conclude with `sub_eq_zero.2 e2`.
-/
theorem coreP {κ : Type} [Fintype κ] (A : Submodule ℂ Y) (tf : Y →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ))
    (r : UA E n → D → D) (hinj : ∀ F ∈ A, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ A, ∀ ℓ, tf F ℓ = Φ ℓ)
    (W : Submodule ℂ (UA E n → ℂ)) (hW : ∀ x, ∀ φ ∈ W, RU E n x φ ∈ W)
    (σ : κ → Submodule ℂ (UA E n → ℂ)) (P : κ → W →ₗ[ℂ] (UA E n → ℂ)) (hσ : ∀ t, ∀ φ ∈ σ t, IsAutFormU φ)
    (hP : ∀ t φ, P t φ ∈ σ t) (hPe : ∀ t x (φ : W), P t ⟨RU E n x φ, hW x φ φ.2⟩ = RU E n x (P t φ))
    (F : Fin m → Y) (hFA : ∀ i, F i ∈ A) (hFW : ∀ i ℓ, tf (F i) ℓ ∈ W)
    (hPs : ∀ i ℓ, ∑ t, P t ⟨tf (F i) ℓ, hFW i ℓ⟩ = tf (F i) ℓ)
    (heq : ∀ i ℓ, ∀ x ∈ infU E n, RU E n x (tf (F i) ℓ) = tf (F i) (r x ℓ)) :
    ∃ G : κ → Fin m → Y, (∀ t i, G t i ∈ A) ∧ (∀ t i ℓ, tf (G t i) ℓ ∈ σ t) ∧ ∑ t, G t = F ∧
      ∀ (T : Y → Y) (k : UA E n) (a : Fin m → Fin m → ℂ), (∀ F ∈ A, T F ∈ A) →
        (∀ F ℓ, tf (T F) ℓ = RU E n k (tf F ℓ)) → (∀ i, ∑ j, a i j • T (F j) = F i) →
        ∀ t i, ∑ j, a i j • T (G t j) = G t i := by
  let Φ : Fin m → D →ₗ[ℂ] W := fun i => (tf (F i)).codRestrict W (hFW i)
  have hΦ : ∀ i ℓ, (Φ i ℓ : UA E n → ℂ) = tf (F i) ℓ := fun _ _ => rfl
  have hex : ∀ t i, ∃ G ∈ A, ∀ ℓ, tf G ℓ = P t (Φ i ℓ) := fun t i =>
    hsur (P t ∘ₗ Φ i) (fun ℓ => hσ t _ (hP t _)) fun ℓ x hx => by
      have e : (⟨RU E n x (Φ i ℓ), hW x _ (Φ i ℓ).2⟩ : W) = Φ i (r x ℓ) := Subtype.ext (heq i ℓ x hx)
      exact (hPe t x (Φ i ℓ)).symm.trans (by rw [e]; rfl)
  choose G hGA hG using hex
  refine ⟨G, hGA, fun t i ℓ => hG t i ℓ ▸ hP t _, funext fun i => ?_, fun T k a hTA hT hF t i => ?_⟩
  · rw [Finset.sum_apply]
    refine sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun t _ => hGA t i) (hFA i)) fun ℓ => ?_)
    simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hG]
    exact sub_eq_zero.2 (hPs i ℓ)
  · refine sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun j _ => A.smul_mem _ (hTA _ (hGA t j))) (hGA t i))
      fun ℓ => ?_)
    have e : ∑ j, a i j • (⟨RU E n k (Φ j ℓ), hW k _ (Φ j ℓ).2⟩ : W) = Φ i ℓ := by
      apply Subtype.ext
      have := congrArg (fun y => tf y ℓ) (hF i)
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hT] at this
      rw [Submodule.coe_sum]
      exact this
    have e2 := congrArg (P t) e
    simp only [map_sum, map_smul, hPe] at e2
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, hT, hG]
    exact sub_eq_zero.2 e2

open GlobalTheory.DefU in

/- English proof (translation)
Establish `hFa` using `haut F hFA hF`. Set `Φ : Fin m → D →ₗ[ℂ] autU E n` to `fun i => (tf (F i)).codRestrict (autU E n) (hFa i)`. Take `⟨κ, _, σ', P, hσ', hP, hPe, hPs⟩` from `autProj E n (⨆ i, LinearMap.range (Φ i)) inferInstance`. Take `⟨G', hG'A, hG', hsum', hinv'⟩` from `coreP A tf r hinj hsur (autU E n) (fun x φ hφ => (autRep E n x ⟨φ, hφ⟩).2) σ' (fun t => (autU E n).subtype ∘ₗ P t) (fun t φ hφ => (hσ' t).aut φ hφ) hP (fun t x φ => congrArg Subtype.val (hPe t x φ)) F hFA hFa (fun i ℓ => by`. Establish `e` using `congrArg Subtype.val (hPs (Φ i ℓ) (Submodule.mem_iSup_of_mem i ⟨ℓ, rfl⟩))`.

Rewrite `e` using `[Submodule.coe_sum]`. Conclude with `e)`. Use the proof step `(fun i ℓ x hx => heq _ (hFA i) ℓ x hx)`. Establish `hinvG : ∀ t u i, ∑ j, a u i j • T u (G' t j) = G' t i` using `fun t u i => hinv' (T u) (k u) (a u) (hTA u) (hT u) (hF u) t i`. Establish `hmem : ∀ t i ℓ, tf (G' t i) ℓ ∈ ⨆ j, σ j` using `fun t i ℓ => by`.

Distinguish the cases in `h0 : G' t = 0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Conclude with `hcov _ (hσ' t) (hwt _ (hσ' t) _ (fun i => hG'A t i) (hinvG t) h0 (hG' t)) ⟨hG' t i ℓ, hfix _ (fun i => hG'A t i) (hinvG t) i ℓ⟩`. Establish `hFW : ∀ i ℓ, tf (F i) ℓ ∈ ⨆ j, σ j` using `fun i ℓ => by`.

Establish `e : F i = ∑ t, G' t i`. Rewrite using `[← hsum', Finset.sum_apply]`. Rewrite using `[e, map_sum, LinearMap.sum_apply]`. Conclude with `Submodule.sum_mem _ fun t _ => hmem t i ℓ`. Take `⟨Q, hQ, hQs, hQu⟩` from `indepProj σ hind`.

Establish `hst : ∀ x, ∀ φ ∈ ⨆ j, σ j, RU E n x φ ∈ ⨆ j, σ j` using `fun x φ hφ => by`. Establish `hle : (⨆ j, σ j) ≤ (⨆ j, σ j).comap (RU E n x)` using `iSup_le fun j ψ hψ => Submodule.mem_iSup_of_mem j ((hσ j).stable x ψ hψ)`. Conclude with `hle hφ`. Take `⟨G, hGA, hG, hsum, hinv⟩` from `coreP A tf r hinj hsur (⨆ j, σ j) hst σ Q (fun t φ hφ => (hσ t).aut φ hφ) hQ (fun t x φ => hQu (fun j => RU E n x (Q j φ)) (fun j => (hσ j).stable x _ (hQ j φ)) _ (by`. Express the relevant statement in the definitionally equal form `RU E n x (φ : UA E n → ℂ) = _`.

Rewrite using `[← map_sum, hQs]) t) F hFA hFW (fun i ℓ => hQs _) (fun i ℓ x hx => heq _ (hFA i) ℓ x hx)`. Conclude with `⟨G, hGA, fun j u i => hinv (T u) (k u) (a u) (hTA u) (hT u) (hF u) j i, hG, hsum⟩`.
-/
theorem absMain {I J : Type} [Fintype J] [FiniteDimensional ℂ D] (A : Submodule ℂ Y) (tf : Y →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ))
    (r : UA E n → D → D) (hinj : ∀ F ∈ A, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ A, ∀ ℓ, tf F ℓ = Φ ℓ)
    (T : I → Y → Y) (k : I → UA E n) (a : I → Fin m → Fin m → ℂ) (hTA : ∀ u, ∀ F ∈ A, T u F ∈ A)
    (hT : ∀ u F ℓ, tf (T u F) ℓ = RU E n (k u) (tf F ℓ)) (Kf : Submodule ℂ (UA E n → ℂ))
    (Pw : Submodule ℂ (UA E n → ℂ) → Prop)
    (haut : ∀ F : Fin m → Y, (∀ i, F i ∈ A) → (∀ u i, ∑ j, a u i j • T u (F j) = F i) → ∀ i ℓ, IsAutFormU (tf (F i) ℓ))
    (heq : ∀ G ∈ A, ∀ ℓ, ∀ x ∈ infU E n, RU E n x (tf G ℓ) = tf G (r x ℓ))
    (hfix : ∀ F : Fin m → Y, (∀ i, F i ∈ A) → (∀ u i, ∑ j, a u i j • T u (F j) = F i) → ∀ i ℓ, tf (F i) ℓ ∈ Kf)
    (hwt : ∀ σ, IsAutRepU σ → ∀ F : Fin m → Y, (∀ i, F i ∈ A) → (∀ u i, ∑ j, a u i j • T u (F j) = F i) → F ≠ 0 →
      (∀ i ℓ, tf (F i) ℓ ∈ σ) → Pw σ)
    (σ : J → Submodule ℂ (UA E n → ℂ)) (hσ : ∀ j, IsAutRepU (σ j)) (hind : iSupIndep σ)
    (hcov : ∀ π, IsAutRepU π → Pw π → π ⊓ Kf ≤ ⨆ j, σ j)
    (F : Fin m → Y) (hFA : ∀ i, F i ∈ A) (hF : ∀ u i, ∑ j, a u i j • T u (F j) = F i) :
    ∃ G : J → Fin m → Y, (∀ j i, G j i ∈ A) ∧ (∀ j u i, ∑ l, a u i l • T u (G j l) = G j i) ∧
      (∀ j i ℓ, tf (G j i) ℓ ∈ σ j) ∧ ∑ j, G j = F := by
  have hFa := haut F hFA hF
  let Φ : Fin m → D →ₗ[ℂ] autU E n := fun i => (tf (F i)).codRestrict (autU E n) (hFa i)
  obtain ⟨κ, _, σ', P, hσ', hP, hPe, hPs⟩ := autProj E n (⨆ i, LinearMap.range (Φ i)) inferInstance
  obtain ⟨G', hG'A, hG', hsum', hinv'⟩ := coreP A tf r hinj hsur (autU E n) (fun x φ hφ => (autRep E n x ⟨φ, hφ⟩).2) σ'
    (fun t => (autU E n).subtype ∘ₗ P t) (fun t φ hφ => (hσ' t).aut φ hφ) hP
    (fun t x φ => congrArg Subtype.val (hPe t x φ)) F hFA hFa
    (fun i ℓ => by
      have e := congrArg Subtype.val (hPs (Φ i ℓ) (Submodule.mem_iSup_of_mem i ⟨ℓ, rfl⟩))
      rw [Submodule.coe_sum] at e
      exact e)
    (fun i ℓ x hx => heq _ (hFA i) ℓ x hx)
  have hinvG : ∀ t u i, ∑ j, a u i j • T u (G' t j) = G' t i := fun t u i =>
    hinv' (T u) (k u) (a u) (hTA u) (hT u) (hF u) t i
  have hmem : ∀ t i ℓ, tf (G' t i) ℓ ∈ ⨆ j, σ j := fun t i ℓ => by
    by_cases h0 : G' t = 0
    · rw [h0]
      simp
    · exact hcov _ (hσ' t) (hwt _ (hσ' t) _ (fun i => hG'A t i) (hinvG t) h0 (hG' t)) ⟨hG' t i ℓ,
        hfix _ (fun i => hG'A t i) (hinvG t) i ℓ⟩
  have hFW : ∀ i ℓ, tf (F i) ℓ ∈ ⨆ j, σ j := fun i ℓ => by
    have e : F i = ∑ t, G' t i := by
      rw [← hsum', Finset.sum_apply]
    rw [e, map_sum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun t _ => hmem t i ℓ
  obtain ⟨Q, hQ, hQs, hQu⟩ := indepProj σ hind
  have hst : ∀ x, ∀ φ ∈ ⨆ j, σ j, RU E n x φ ∈ ⨆ j, σ j := fun x φ hφ => by
    have hle : (⨆ j, σ j) ≤ (⨆ j, σ j).comap (RU E n x) :=
      iSup_le fun j ψ hψ => Submodule.mem_iSup_of_mem j ((hσ j).stable x ψ hψ)
    exact hle hφ
  obtain ⟨G, hGA, hG, hsum, hinv⟩ := coreP A tf r hinj hsur (⨆ j, σ j) hst σ Q (fun t φ hφ => (hσ t).aut φ hφ) hQ
    (fun t x φ => hQu (fun j => RU E n x (Q j φ)) (fun j => (hσ j).stable x _ (hQ j φ)) _ (by
      change RU E n x (φ : UA E n → ℂ) = _
      rw [← map_sum, hQs]) t) F hFA hFW (fun i ℓ => hQs _) (fun i ℓ x hx => heq _ (hFA i) ℓ x hx)
  exact ⟨G, hGA, fun j u i => hinv (T u) (k u) (a u) (hTA u) (hT u) (hF u) j i, hG, hsum⟩

/- English proof (translation)
Introduce `i`. Rewrite using `[Submodule.disjoint_def]`. Introduce `y hy hy'`. Use `hsep i y hy fun t => ?_` and prove the remaining obligations. Establish `h1 : (⨆ j, ⨆ _ : j ≠ i, Yv j) ≤ (⨆ j, ⨆ _ : j ≠ i, σ j).comap (Tt t)` using `iSup₂_le fun j hj z hz => Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hY j z hz t))`.

Conclude with `(Submodule.disjoint_def.1 (hind i)) _ (hY i y hy t) (h1 hy')`.
-/
theorem indepOf {M N J K : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (σ : J → Submodule ℂ N)
    (hind : iSupIndep σ) (Yv : J → Submodule ℂ M) (Tt : K → M →ₗ[ℂ] N) (hY : ∀ i, ∀ y ∈ Yv i, ∀ t, Tt t y ∈ σ i)
    (hsep : ∀ i, ∀ y ∈ Yv i, (∀ t, Tt t y = 0) → y = 0) : iSupIndep Yv := by
  intro i
  rw [Submodule.disjoint_def]
  intro y hy hy'
  refine hsep i y hy fun t => ?_
  have h1 : (⨆ j, ⨆ _ : j ≠ i, Yv j) ≤ (⨆ j, ⨆ _ : j ≠ i, σ j).comap (Tt t) :=
    iSup₂_le fun j hj z hz => Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hY j z hz t))
  exact (Submodule.disjoint_def.1 (hind i)) _ (hY i y hy t) (h1 hy')

end Core

end UpperTheory.V.Z.J.D.Dc
