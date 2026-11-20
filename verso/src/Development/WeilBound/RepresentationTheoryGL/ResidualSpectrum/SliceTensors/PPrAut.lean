import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormDerivativeModerateGrowth

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspStab

namespace PositivityTheory.Rg.Rs.PrAut

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k`. Use `⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)`. Rewrite using `[mul_assoc, h.left]`.

Establish `e : {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ} = (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E N k' φ = φ}`. Use extensionality with `k'`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `e`.

Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Introduce `e`. Use `congrArg (finRep E N k) e` as an intermediate fact. Rewrite `this` using `[Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E N k), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `IsOpen {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ}`.

Rewrite using `[e]`. Conclude with `h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)`. Use `h.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E N c φ)).map (finRep E N k)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`.

Conclude with `⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩`. Conclude with `zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) h.zfin`. Take `⟨C, M, h1⟩` from `h.growth (g * finGL E N k)`. Use `⟨C, M, fun y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖φ.1 (g * infGL E N y * finGL E N k)‖ ≤ _`.

Rewrite using `[mul_assoc, infGL_comm, ← mul_assoc]`. Conclude with `h1 y`. Consider the case `cpt c`. Use `⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits c)) = φ.1 (g * infGL E N (Unitary.toUnits c))`.

Rewrite using `[mul_assoc, h.left]`. Conclude with `level_of_le h.level fun k hk => by`. Express the relevant statement in the definitionally equal form `finRep E N k (cptRep E N c φ) = cptRep E N c φ`. Rewrite using `[← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]`. Use `h.kfin` as an intermediate fact.

Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E N c φ)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨c', rfl⟩`. Use `Submodule.subset_span ⟨c' * c, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (cptRep E N c' * cptRep E N c) φ`. Rewrite using `[← map_mul]`.

Conclude with `zfin_of_comm _ (fun z hz => GlobalTheory.ZalgCpt.zalg_comm_cptRep E N c z hz) h.zfin`. Take `⟨C, M, h1⟩` from `growth_mul (Unitary.toUnits c) (h.growth g)`. Use `⟨C, M, fun y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖φ.1 (g * infGL E N y * infGL E N (Unitary.toUnits c))‖ ≤ _`. Rewrite using `[mul_assoc, ← map_mul]`.

Conclude with `h1 y`. Consider the case `lie X`. Use `⟨fun γ g => ?_, ?_, GlobalTheory.CuspRep.KFin.kfin_lie E N X φ h.kfin, zfin_of_comm _ (fun z hz => GlobalTheory.CuspRep.Zalg_mul_lie E N X z hz) h.zfin, GlobalTheory.CuspStab.lie_growth hF E N X φ h⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `lieD X φ.1 (ratGL E N γ * g) = lieD X φ.1 g`. Establish `e : chart φ.1 (ratGL E N γ * g) = chart φ.1 g`.

Use function extensionality and compare the values at `x`. Unfold `chart`. Use `split_ifs`. Rewrite using `[mul_assoc, h.left]`. Both sides reduce to the same expression.

Unfold `lieD`. Rewrite using `[e]`. Conclude with `level_of_le h.level fun k hk => by`. Express the relevant statement in the definitionally equal form `finRep E N k (lie E N X φ) = lie E N X φ`. Express the relevant statement in the definitionally equal form `(rt E N (finGL E N k) * lie E N X) φ = _`.

Rewrite using `[← lie_rt_fin, Module.End.mul_apply]`. Conclude with `congrArg (lie E N X) hk`.
-/
theorem isAutForm_act (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E N) {φ : Sm E N} (h : IsAutForm φ) :
    IsAutForm (act o φ) := by
  cases o with
  | fin k =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)
      rw [mul_assoc, h.left]
    · have e : {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ} =
          (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E N k' φ = φ} := by
        ext k'
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul]
        constructor
        · intro e
          rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply]
        · intro e
          have := congrArg (finRep E N k) e
          rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E N k), ← map_mul,
            mul_inv_cancel, map_one, Module.End.one_apply] at this
      change IsOpen {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ}
      rw [e]
      exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E N c φ)).map
        (finRep E N k)) (Submodule.span_le.2 ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
    · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) h.zfin
    · obtain ⟨C, M, h1⟩ := h.growth (g * finGL E N k)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * finGL E N k)‖ ≤ _
      rw [mul_assoc, infGL_comm, ← mul_assoc]
      exact h1 y
  | cpt c =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits c)) = φ.1 (g * infGL E N (Unitary.toUnits c))
      rw [mul_assoc, h.left]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (cptRep E N c φ) = cptRep E N c φ
        rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E N c φ))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨c', rfl⟩
      refine Submodule.subset_span ⟨c' * c, ?_⟩
      change _ = (cptRep E N c' * cptRep E N c) φ
      rw [← map_mul]
    · exact zfin_of_comm _ (fun z hz => GlobalTheory.ZalgCpt.zalg_comm_cptRep E N c z hz) h.zfin
    · obtain ⟨C, M, h1⟩ := growth_mul (Unitary.toUnits c) (h.growth g)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * infGL E N (Unitary.toUnits c))‖ ≤ _
      rw [mul_assoc, ← map_mul]
      exact h1 y
  | lie X =>
    refine ⟨fun γ g => ?_, ?_, GlobalTheory.CuspRep.KFin.kfin_lie E N X φ h.kfin,
      zfin_of_comm _ (fun z hz => GlobalTheory.CuspRep.Zalg_mul_lie E N X z hz) h.zfin,
      GlobalTheory.CuspStab.lie_growth hF E N X φ h⟩
    · change lieD X φ.1 (ratGL E N γ * g) = lieD X φ.1 g
      have e : chart φ.1 (ratGL E N γ * g) = chart φ.1 g := by
        funext x
        unfold chart
        split_ifs
        · rw [mul_assoc, h.left]
        · rfl
      unfold lieD
      rw [e]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (lie E N X φ) = lie E N X φ
        change (rt E N (finGL E N k) * lie E N X) φ = _
        rw [← lie_rt_fin, Module.End.mul_apply]
        exact congrArg (lie E N X) hk

end PositivityTheory.Rg.Rs.PrAut

end
