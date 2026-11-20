import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ n π hπ w K hK hu W hWπ hW0 hW`. Take `⟨φ, hφ, hφ0, hφK⟩` from `hu`. Set `Ψ : GlobalTheory.DefU.AutSub E n` to `⟨π, hπ⟩`. Take `⟨τ, -, hirr, f, hf0, hfm, hf⟩` from `GlobalTheory.DefU.LocAdm.exists_admissible_comp E n Ψ w`. Set `ρ : Representation ℂ (locU n w) Ψ.V` to `Ψ.rep.comp (locU n w).subtype`.

Set `F : Representation.IntertwiningMap τ.ρ ρ` to `⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩`. Establish `hF0 : F ≠ 0` using `fun h => hf0 (LinearMap.ext fun v => by`. Use `congrArg Subtype.val (DFunLike.congr_fun h v)` as an intermediate fact. Conclude with `this)`. Take `⟨r, -, -, hr⟩` from `GlobalTheory.DefU.LocRet.exists_ret E n w`.

Establish `htop` using `(GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V τ.V τ.V Ψ.rep (locU n w).subtype τ.ρ τ.ρ Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1`. Establish `hfi : ∀ (i : Representation.IntertwiningMap τ.ρ ρ) g u, i.toLinearMap (τ.ρ g u) = ρ g (i.toLinearMap u)` using `fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u`. Set `K' : Subgroup (locU n w)` to `K.comap (locU n w).subtype`. Establish `hfix : ∃ v : τ.V, v ≠ 0 ∧ ∀ k ∈ K', τ.ρ k v = v`. Assume the negation of the conclusion as `hn`.

Establish `key` using `GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ρ τ.ρ hirr (fun i : Representation.IntertwiningMap τ.ρ ρ => i.toLinearMap) hfi (K' : Set (locU n w)) ⊥ (fun i v hv => by`. Establish `hv' : v = 0`. Assume the negation of the conclusion as `h`. Conclude with `hn ⟨v, h, hv⟩`. Rewrite using `[hv', map_zero]`.

Conclude with `Submodule.zero_mem _)`. Use the proof step `(fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) ⟨φ, hφ⟩`. Use the proof step `(fun k hk => Subtype.ext (hφK k.1 hk)) (by rw [htop]; exact Submodule.mem_top)`. Conclude with `hφ0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 key))`. Take `⟨v, hvW, hv0, hv⟩` from `UpperTheory.V.Af.GlobalFixedVectors.sub_fixed τ.ρ hirr ρ (by`.

Rewrite using `[eq_top_iff, ← htop]`. Conclude with `iSup_le fun i => le_iSup_of_le ⟨i.toLinearMap, hfi i⟩ le_rfl)`. Use the proof step `(W.comap π.subtype) (fun g v hv => hW g.1 g.2 v.1 hv)`. Use the proof step `(fun e => hW0 ((Submodule.eq_bot_iff W).2 fun x hx => by`. Establish `h : (⟨x, hWπ hx⟩ : π) ∈ W.comap π.subtype` using `hx`.

Rewrite `h` using `[e]`. Conclude with `congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h))) K' hfix`. Conclude with `⟨v.1, hvW, fun e => hv0 (Subtype.ext e), fun k hk => congrArg Subtype.val (hv ⟨k, hK hk⟩ hk)⟩`.
-/
theorem UpperTheory.exists_fixed_vector_in_locally_stable_subspace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ (w : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E n)), K ≤ locU n w → (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ) → ∀ W : Submodule ℂ (UA E n → ℂ), W ≤ σ → W ≠ ⊥ → (∀ x ∈ locU n w, ∀ φ ∈ W, RU E n x φ ∈ W) → ∃ φ ∈ W, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ := by
  intro E _ _ _ n π hπ w K hK hu W hWπ hW0 hW
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  obtain ⟨τ, -, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n Ψ w
  let ρ : Representation ℂ (locU n w) Ψ.V := Ψ.rep.comp (locU n w).subtype
  let F : Representation.IntertwiningMap τ.ρ ρ :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V τ.V τ.V Ψ.rep (locU n w).subtype
    τ.ρ τ.ρ Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  have hfi : ∀ (i : Representation.IntertwiningMap τ.ρ ρ) g u, i.toLinearMap (τ.ρ g u) = ρ g (i.toLinearMap u) :=
    fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u
  let K' : Subgroup (locU n w) := K.comap (locU n w).subtype
  have hfix : ∃ v : τ.V, v ≠ 0 ∧ ∀ k ∈ K', τ.ρ k v = v := by
    by_contra hn
    have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ρ τ.ρ hirr
      (fun i : Representation.IntertwiningMap τ.ρ ρ => i.toLinearMap) hfi (K' : Set (locU n w)) ⊥
      (fun i v hv => by
        have hv' : v = 0 := by
          by_contra h
          exact hn ⟨v, h, hv⟩
        rw [hv', map_zero]
        exact Submodule.zero_mem _)
      (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) ⟨φ, hφ⟩
      (fun k hk => Subtype.ext (hφK k.1 hk)) (by rw [htop]; exact Submodule.mem_top)
    exact hφ0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 key))
  obtain ⟨v, hvW, hv0, hv⟩ := UpperTheory.V.Af.GlobalFixedVectors.sub_fixed τ.ρ hirr ρ
    (by
      rw [eq_top_iff, ← htop]
      exact iSup_le fun i => le_iSup_of_le ⟨i.toLinearMap, hfi i⟩ le_rfl)
    (W.comap π.subtype) (fun g v hv => hW g.1 g.2 v.1 hv)
    (fun e => hW0 ((Submodule.eq_bot_iff W).2 fun x hx => by
      have h : (⟨x, hWπ hx⟩ : π) ∈ W.comap π.subtype := hx
      rw [e] at h
      exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h))) K' hfix
  exact ⟨v.1, hvW, fun e => hv0 (Subtype.ext e), fun k hk => congrArg Subtype.val (hv ⟨k, hK hk⟩ hk)⟩
