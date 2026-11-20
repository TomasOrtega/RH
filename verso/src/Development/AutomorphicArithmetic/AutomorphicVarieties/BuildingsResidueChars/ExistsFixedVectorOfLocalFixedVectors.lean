import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedVectorInLocallyStableSubspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteAdelicUnitaryMemNhdsOneOfTrivialAtPlaces
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ n σ hσ K hKf hKr T hT hKT h`. Set `P : Finset (HeightOneSpectrum (𝓞 E)) → UA E n → Prop` to `fun S k => k ∈ K ∧ ∀ w ∈ S, ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u k = 1`. Establish `hR : ∀ (a b : UA E n) (φ : UA E n → ℂ), RU E n (a * b) φ = RU E n a (RU E n b φ)` using `fun a b φ => by`. Rewrite using `[map_mul, Module.End.mul_apply]`. Establish `key : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P S k → RU E n k φ = φ) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P ∅ k → RU E n k φ = φ`.

Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact id`. Consider the case `insert w S hw ih`. Introduce and unpack `⟨v, hvσ, hv0, hv⟩`.

Set `W : Submodule ℂ (UA E n → ℂ)` to `σ ⊓ ⨅ k : {k // P (insert w S) k}, LinearMap.ker (RU E n k.1 - 1)`. Establish `hWm : ∀ x, x ∈ W ↔ x ∈ σ ∧ ∀ k, P (insert w S) k → RU E n k x = x` using `fun x => by`. Simplify using `only [W, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, Subtype.forall]`. Take `⟨φ, hφ, hφ0, hφK⟩` from `h w`. Take `⟨x, hxW, hx0, hx⟩` from `UpperTheory.exists_fixed_vector_in_locally_stable_subspace E n σ hσ w (K ⊓ locU n w) inf_le_right ⟨φ, hφ, hφ0, fun k hk => hφK k hk.1 hk.2⟩ W inf_le_left (fun e => hv0 (by`.

Use `(hWm v).2 ⟨hvσ, hv⟩` as an intermediate fact. Rewrite using `[e, Submodule.mem_bot] at this))` and apply the resulting hypothesis. Use the proof step `(fun g hg x hx => (hWm _).2 ⟨hσ.stable g x ((hWm x).1 hx).1, fun k hk => by`. Establish `e : k * g = g * k`. Use `Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)` and prove the remaining obligations.

Simplify using `only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hg, one_mul, mul_one]`. Distinguish the cases in `hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))`. Establish `h1 : Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) k.1 = 1` using `hk.2 w (Finset.mem_insert_self _ _) u hu`. Simplify using `only [Subgroup.coe_mul, map_mul, h1, one_mul, mul_one]`. Simplify using `only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hg hu, one_mul, mul_one]`.

Rewrite using `[← hR, e, hR, ((hWm x).1 hx).2 k hk]⟩)`. Use `ih ⟨x, ((hWm x).1 hxW).1, hx0, fun k hk => ?_⟩` and prove the remaining obligations. Establish `h1 : GlobalTheory.DefU.LocRet.ret0 w n k ∈ K` using `hKr w k hk.1`. Establish `h2 : P (insert w S) (k * (GlobalTheory.DefU.LocRet.ret0 w n k)⁻¹)`. Use `⟨mul_mem hk.1 (inv_mem h1), fun w' hw' u hu => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `huw : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))`. Establish `h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = cLoc u k` using `GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq huw k`. Rewrite using `[map_mul, map_inv, h3, mul_inv_cancel]`. Establish `h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = 1` using `GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_ne huw k`. Break down `Finset.mem_insert.1 hw' with rfl | hw'` into its components or cases.

Conclude with `absurd hu huw`. Rewrite using `[map_mul, map_inv, h3, hk.2 w' hw' u hu, inv_one, mul_one]`. Establish `h3 : RU E n (GlobalTheory.DefU.LocRet.ret0 w n k) x = x` using `hx _ ⟨h1, GlobalTheory.DefU.LocRet.unitaryAdelicLocalRetractionEnd_mem_localPoints k⟩`. Establish `h4` using `((hWm x).1 hxW).2 _ h2`. Rewrite `h4` using `[← h3, ← hR, inv_mul_cancel_right, h3]`. Then use the resulting hypothesis.

Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff σ).1 hσ.ne_bot`. Take `⟨S, hS⟩` from `UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places E n T hT _ ((hσ.aut v hv).level.mem_nhds (x := 1) (by simp))`. Take `⟨x, hx, hx0, hxK⟩` from `key S ⟨v, hv, hv0, fun k hk => hS ⟨k, hKf hk.1⟩ (hKT k hk.1) fun u hu => hk.2 u hu u rfl⟩`. Conclude with `⟨x, hx, hx0, fun k hk => hxK k ⟨hk, by simp⟩⟩`.
-/
theorem UpperTheory.exists_fixed_vector_of_local_fixed_vectors :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ K : Subgroup (UA E n), K ≤ finU E n → (∀ w, ∀ k ∈ K, GlobalTheory.DefU.LocRet.ret0 w n k ∈ K) → ∀ T : Set (HeightOneSpectrum (𝓞 E)), T.Finite → (∀ k ∈ K, ∀ u ∉ T, cLoc u k ∈ GlobalTheory.LFun.KGL u n) → (∀ w, ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, k ∈ locU n w → RU E n k φ = φ) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ := by
  classical
  intro E _ _ _ n σ hσ K hKf hKr T hT hKT h
  let P : Finset (HeightOneSpectrum (𝓞 E)) → UA E n → Prop := fun S k =>
    k ∈ K ∧ ∀ w ∈ S, ∀ u : HeightOneSpectrum (𝓞 E),
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u k = 1
  have hR : ∀ (a b : UA E n) (φ : UA E n → ℂ), RU E n (a * b) φ = RU E n a (RU E n b φ) := fun a b φ => by
    rw [map_mul, Module.End.mul_apply]
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P S k → RU E n k φ = φ) →
      ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P ∅ k → RU E n k φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hvσ, hv0, hv⟩
      let W : Submodule ℂ (UA E n → ℂ) := σ ⊓ ⨅ k : {k // P (insert w S) k}, LinearMap.ker (RU E n k.1 - 1)
      have hWm : ∀ x, x ∈ W ↔ x ∈ σ ∧ ∀ k, P (insert w S) k → RU E n k x = x := fun x => by
        simp only [W, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          Module.End.one_apply, sub_eq_zero, Subtype.forall]
      obtain ⟨φ, hφ, hφ0, hφK⟩ := h w
      obtain ⟨x, hxW, hx0, hx⟩ := UpperTheory.exists_fixed_vector_in_locally_stable_subspace E n σ hσ w (K ⊓ locU n w) inf_le_right
        ⟨φ, hφ, hφ0, fun k hk => hφK k hk.1 hk.2⟩ W inf_le_left
        (fun e => hv0 (by
          have := (hWm v).2 ⟨hvσ, hv⟩
          rwa [e, Submodule.mem_bot] at this))
        (fun g hg x hx => (hWm _).2 ⟨hσ.stable g x ((hWm x).1 hx).1, fun k hk => by
          have e : k * g = g * k := by
            refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
            · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hg, one_mul, mul_one]
            · by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
              · have h1 : Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) k.1 = 1 :=
                  hk.2 w (Finset.mem_insert_self _ _) u hu
                simp only [Subgroup.coe_mul, map_mul, h1, one_mul, mul_one]
              · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hg hu, one_mul, mul_one]
          rw [← hR, e, hR, ((hWm x).1 hx).2 k hk]⟩)
      refine ih ⟨x, ((hWm x).1 hxW).1, hx0, fun k hk => ?_⟩
      have h1 : GlobalTheory.DefU.LocRet.ret0 w n k ∈ K := hKr w k hk.1
      have h2 : P (insert w S) (k * (GlobalTheory.DefU.LocRet.ret0 w n k)⁻¹) := by
        refine ⟨mul_mem hk.1 (inv_mem h1), fun w' hw' u hu => ?_⟩
        by_cases huw : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
        · have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = cLoc u k := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq huw k
          rw [map_mul, map_inv, h3, mul_inv_cancel]
        · have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = 1 := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_ne huw k
          rcases Finset.mem_insert.1 hw' with rfl | hw'
          · exact absurd hu huw
          · rw [map_mul, map_inv, h3, hk.2 w' hw' u hu, inv_one, mul_one]
      have h3 : RU E n (GlobalTheory.DefU.LocRet.ret0 w n k) x = x := hx _ ⟨h1, GlobalTheory.DefU.LocRet.unitaryAdelicLocalRetractionEnd_mem_localPoints k⟩
      have h4 := ((hWm x).1 hxW).2 _ h2
      rwa [← h3, ← hR, inv_mul_cancel_right, h3] at h4
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff σ).1 hσ.ne_bot
  obtain ⟨S, hS⟩ := UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places E n T hT _ ((hσ.aut v hv).level.mem_nhds (x := 1) (by simp))
  obtain ⟨x, hx, hx0, hxK⟩ := key S ⟨v, hv, hv0, fun k hk =>
    hS ⟨k, hKf hk.1⟩ (hKT k hk.1) fun u hu => hk.2 u hu u rfl⟩
  exact ⟨x, hx, hx0, fun k hk => hxK k ⟨hk, by simp⟩⟩
