import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianDim

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open GlobalTheory.ArchSch GlobalTheory.ArchSchB GlobalTheory.ArchSchA in

/- English proof (translation)
Introduce `_hP F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' i₀ i₁ j₀ j₁ hB hXW _hM _hM₁ hH hH' T T' hT hR hR'`. Take `⟨r, s, r', s', hX, hW⟩` from `hXW`. Establish `atι : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evI F) z → At (evI F) (incM F H.ι * z * (incM F H'.ι)ᵀ)`. Introduce `z hz u hu`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu]`.

Simplify using the standard rewrite rules. Establish `F1 : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), GlobalTheory.ThK.EvUniqB.InfRel B M M₁ H.ι H'.ι (isoA H H') S → ∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin n × Fin d), ∀ g₁ : SInf F (Fin n₁ × Fin d₁), ⇑f₁ = sch (trP F _) (arch F (M.co.e (incM F H.ι * z * (incM F H' …`. Introduce `S hS z hz f f₁ g₁ h1 h2`. Conclude with `hS.1 z hz f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M.co B.ψ hB.std (incM F H.ι * z * (incM F H'.ι)ᵀ) (atι z hz) f f₁ h1) g₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M₁.co B.ψ hB.std z hz (S f) g₁ h2)`. Establish `F2 : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), GlobalTheory.ThK.EvUniqB.InfRel B M M₁ H.ι H'.ι (isoA H H') S → ∀ u ∈ isoA (F` using `F) H H', At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ⇑f₁ = sch (trP F _) (arch F (M.co.e u).1) (arch F (M.co.e u).2) ⇑f → S f₁ = S f := fun S hS u hu hat f f₁ h => hS.2 u hu hat f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M.co B.ψ hB.std u hat f f₁ h)`.

Take `⟨h0, hadd, hsmul⟩` from `GlobalTheory.ArchSchA.lagSetA_submodule M M₁ H H'`. Establish `hiso` using `GlobalTheory.T.adapted_planes_good_models_descent B M M₁ H H' hB hX hW hH hH'`. Establish `hco` using `GlobalTheory.T.adapted_planes_good_models_local B M M₁ H H' hB hX hW hH hH'`. Set `Λ : Submodule ℝ ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))` to `{ carrier := lagSetA M M₁ H H' add_mem' := fun ha hb => hadd _ ha _ hb zero_mem' := h0 smul_mem' := fun t l hl => hsmul t l hl }`. Set `ℓ : (SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) → SInf F (Fin n × Fin d) →L[ℂ] ℂ` to `fun S => ((BoundedContinuousFunction.evalCLM ℂ (0 : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp S`.

Establish `hℓ : ∀ S f, ℓ S f = S f 0` using `fun _ _ => rfl`. Establish `eadd : ∀ x y : Matrix (Fin n) (Fin d) (AE F E), arch F (M.co.e (x + y)).1 = arch F (M.co.e x).1 + arch F (M.co.e y).1 ∧ arch F (M.co.e (x + y)).2 = arch F (M.co.e x).2 + arch F (M.co.e y).2` using `fun x y => ⟨by rw [map_add, Prod.fst_add, archA_add], by rw [map_add, Prod.snd_add, archA_add]⟩`. Establish `inv : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), GlobalTheory.ThK.EvUniqB.InfRel B M M₁ H.ι H'.ι (isoA H H') S → ∀ l ∈ Λ, ∀ f g : SInf F (Fin n × Fin d), ⇑g = sch (trP F _) l.1 l.2 ⇑f → ℓ S g = ℓ S f`. Introduce `S hS l hl f g hg`. Take `⟨y, c, z, hy, hc, hz, hz1, rfl⟩` from `hl`.

Use `set u₁ := Matrix.vecMulVec y (incV F H'.x) with hu₁`. Use `set u₂ := Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) with hu₂`. Use `set w := incM F H.ι * z * (incM F H'.ι)ᵀ with hw`. Establish `hat1 : At (evI F) u₁` using `at_vecMulVec_left hy _`. Establish `hat2 : At (evI F) u₂` using `at_vecMulVec_right _ (at_mulVec _ hc)`.

Establish `m1 : (arch F (M.co.e u₁).1, arch F (M.co.e u₁).2) ∈ lagSetA M M₁ H H'` using `mem_lagSetA_y M M₁ H H' hy`. Establish `m2 : (arch F (M.co.e (u₂ + w)).1, arch F (M.co.e (u₂ + w)).2) ∈ lagSetA M M₁ H H'` using `mem_lagSetA_cz M M₁ H H' hc hz hz1`. Establish `m3 : (arch F (M.co.e u₂).1, arch F (M.co.e u₂).2) ∈ lagSetA M M₁ H H'` using `mem_lagSetA_c M M₁ H H' hc`. Establish `m4 : (arch F (M.co.e w).1, arch F (M.co.e w).2) ∈ lagSetA M M₁ H H'` using `mem_lagrangian_set_archimedean M M₁ H H' hz hz1`. Establish `hsplit : ⇑g = sch (trP F _) (arch F (M.co.e u₁).1) (arch F (M.co.e u₁).2) (sch (trP F _) (arch F (M.co.e u₂).1) (arch F (M.co.e u₂).2) (sch (trP F _) (arch F (M.co.e w).1) (arch F (M.co.e w).2) ⇑f))`.

Rewrite using `[hg]`. Simplify using `only`. Rewrite using `[add_assoc, (eadd _ _).1, (eadd _ _).2, schA_add _ _ _ _ _ (hiso _ m1 _ m2), (eadd _ _).1, (eadd _ _).2, schA_add _ _ _ _ _ (hiso _ m3 _ m4)]`. Take `⟨h₃, hh₃⟩` from `GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e w).1) (arch F (M.co.e w).2) f`. Take `⟨h₂, hh₂⟩` from `GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e u₂).1) (arch F (M.co.e u₂).2) h₃`.

Take `⟨g₁, hg₁⟩` from `GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) (S f)`. Rewrite `hsplit` using `[← hh₃, ← hh₂]`. Rewrite using `[hℓ, hℓ, F2 S hS u₁ (Or.inl ⟨y, rfl⟩) hat1 h₂ g hsplit, F2 S hS u₂ (Or.inr ⟨c, rfl⟩) hat2 h₃ h₂ hh₂, F1 S hS z hz f h₃ g₁ hh₃ hg₁, hg₁]`. Simplify using `[sch, hz1, echA_zero]`. Establish `zξ : ∀ ξ : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F, ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evI F) z ∧ arch F (M₁.co.e z).1 = ξ ∧ arch F (M₁.co.e z).2 = 0`.

Introduce `ξ`. Use `⟨M₁.co.e.symm (fun i => liftA F (ξ i), 0), fun u hu => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearEquiv.map_smul]`. Establish `: u • ((fun i => liftA F (ξ i), 0) : (Fin n₁ × Fin d₁ → AF F) × (Fin n₁ × Fin d₁ → AF F)) = 0`. Use `Prod.ext (funext fun i => ?_) (by simp)` and prove the remaining obligations.

Simplify using `[atA_liftA (ξ i) u hu]`. Rewrite using `[this, map_zero]`. Use function extensionality and compare the values at `i`. Simplify using `[arch, evIA_liftA]`. Simplify using `[archA_zero]`.

Establish `key : ∀ (f : SInf F (Fin n × Fin d)) (ξ : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F), ∃ h : SInf F (Fin n × Fin d), ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), GlobalTheory.ThK.EvUniqB.InfRel B M M₁ H.ι H'.ι (isoA H H') S → S h 0 = S f ξ`. Introduce `f ξ`. Take `⟨z, hz, hz1, hz2⟩` from `zξ ξ`. Take `⟨h, hh⟩` from `GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1) (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2) f`. Use `⟨h, fun S hS => ?_⟩` and prove the remaining obligations.

Take `⟨g₁, hg₁⟩` from `GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) (S f)`. Rewrite using `[F1 S hS z hz f h g₁ hh hg₁, hg₁]`. Simplify using `[sch, hz1, hz2, echA_zero]`. Establish `hne : ℓ T ≠ 0`. Introduce `h`.

Apply `hT` to reduce the goal to its premises. Use `ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_` and prove the remaining obligations. Take `⟨h', hh'⟩` from `key f ξ`. Use `congrArg (fun L => L h') h` as an intermediate fact. Simplify using `only [hℓ, ContinuousLinearMap.zero_apply] at this`.

Rewrite using `[← hh' T hR, this]`. Both sides reduce to the same expression. Establish `hiso' : ∀ l ∈ Λ, ∀ l' ∈ Λ, trP F (Fin n × Fin d) l.1 l'.2 = trP F (Fin n × Fin d) l'.1 l.2` using `fun l hl l' hl' => hiso l hl l' hl'`. Establish `hco' : ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F), (∀ l ∈ Λ, trP F (Fin n × Fin d) v.1 l.2 = trP F (Fin n × Fin d) l.1 v.2) → v ∈ Λ` using `fun v hv => hco v hv`. Establish `hT1` using `inv T hR`.

Establish `hT2` using `inv T' hR'`. Take `⟨C, hC'⟩` from `GlobalTheory.T.aux_statement_2 (Y := Fin n × Fin d → mixedEmbedding.mixedSpace F) (trP F (Fin n × Fin d)) (GlobalTheory.T.trace_pairing_nondegenerate F (Fin n × Fin d)) Λ hiso' hco' (ℓ T) (ℓ T') hT1 hT2 hne`. Use `⟨C, ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_⟩` and prove the remaining obligations. Take `⟨h', hh'⟩` from `key f ξ`. Use `congrArg (fun L => L h') hC'` as an intermediate fact.

Simplify using `only [hℓ, ContinuousLinearMap.smul_apply, smul_eq_mul] at this`. Rewrite using `[← hh' T' hR', this, hh' T hR]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.ArchSchA.infRelA_proportional_uniq : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₂ : Model σ X₁ W₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (i₀ i₁ j₀ j₁ : ℕ), B.IsGood σ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    M.IsGood B.ψ → M₂.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ T T' : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), T ≠ 0 →
    GlobalTheory.ThK.EvUniqB.InfRel B M M₂ H.ι H'.ι (isoA H H') T → GlobalTheory.ThK.EvUniqB.InfRel B M M₂ H.ι H'.ι (isoA H H') T' →
    ∃ c : ℂ, T' = c • T := by
  intro _hP F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' i₀ i₁ j₀ j₁ hB hXW _hM _hM₁ hH hH' T T' hT hR hR'
  obtain ⟨r, s, r', s', hX, hW⟩ := hXW
  classical
  have atι : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evI F) z →
      At (evI F) (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
    intro z hz u hu
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz u hu]
    simp
  have F1 : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      GlobalTheory.ThK.EvUniqB.InfRel B M M₁ H.ι H'.ι (isoA H H') S →
      ∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin n × Fin d), ∀ g₁ : SInf F (Fin n₁ × Fin d₁),
        ⇑f₁ = sch (trP F _) (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1)
          (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2) ⇑f →
        ⇑g₁ = sch (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) ⇑(S f) → S f₁ = g₁ := by
    intro S hS z hz f f₁ g₁ h1 h2
    exact hS.1 z hz f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M.co B.ψ hB.std (incM F H.ι * z * (incM F H'.ι)ᵀ) (atι z hz) f f₁ h1) g₁
      (GlobalTheory.T.darboux_schroedinger_archimedean_acts M₁.co B.ψ hB.std z hz (S f) g₁ h2)
  have F2 : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      GlobalTheory.ThK.EvUniqB.InfRel B M M₁ H.ι H'.ι (isoA H H') S →
      ∀ u ∈ isoA (F := F) H H', At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d),
        ⇑f₁ = sch (trP F _) (arch F (M.co.e u).1) (arch F (M.co.e u).2) ⇑f → S f₁ = S f :=
    fun S hS u hu hat f f₁ h => hS.2 u hu hat f f₁ (GlobalTheory.T.darboux_schroedinger_archimedean_acts M.co B.ψ hB.std u hat f f₁ h)
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.ArchSchA.lagSetA_submodule M M₁ H H'
  have hiso := GlobalTheory.T.adapted_planes_good_models_descent B M M₁ H H' hB hX hW hH hH'
  have hco := GlobalTheory.T.adapted_planes_good_models_local B M M₁ H H' hB hX hW hH hH'
  let Λ : Submodule ℝ ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { carrier := lagSetA M M₁ H H'
      add_mem' := fun ha hb => hadd _ ha _ hb
      zero_mem' := h0
      smul_mem' := fun t l hl => hsmul t l hl }
  let ℓ : (SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) → SInf F (Fin n × Fin d) →L[ℂ] ℂ := fun S =>
    ((BoundedContinuousFunction.evalCLM ℂ (0 : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp S
  have hℓ : ∀ S f, ℓ S f = S f 0 := fun _ _ => rfl
  have eadd : ∀ x y : Matrix (Fin n) (Fin d) (AE F E),
      arch F (M.co.e (x + y)).1 = arch F (M.co.e x).1 + arch F (M.co.e y).1 ∧
      arch F (M.co.e (x + y)).2 = arch F (M.co.e x).2 + arch F (M.co.e y).2 := fun x y =>
    ⟨by rw [map_add, Prod.fst_add, archA_add], by rw [map_add, Prod.snd_add, archA_add]⟩
  have inv : ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      GlobalTheory.ThK.EvUniqB.InfRel B M M₁ H.ι H'.ι (isoA H H') S →
      ∀ l ∈ Λ, ∀ f g : SInf F (Fin n × Fin d), ⇑g = sch (trP F _) l.1 l.2 ⇑f → ℓ S g = ℓ S f := by
    intro S hS l hl f g hg
    obtain ⟨y, c, z, hy, hc, hz, hz1, rfl⟩ := hl
    set u₁ := Matrix.vecMulVec y (incV F H'.x) with hu₁
    set u₂ := Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ c) with hu₂
    set w := incM F H.ι * z * (incM F H'.ι)ᵀ with hw
    have hat1 : At (evI F) u₁ := at_vecMulVec_left hy _
    have hat2 : At (evI F) u₂ := at_vecMulVec_right _ (at_mulVec _ hc)
    have m1 : (arch F (M.co.e u₁).1, arch F (M.co.e u₁).2) ∈ lagSetA M M₁ H H' :=
      mem_lagSetA_y M M₁ H H' hy
    have m2 : (arch F (M.co.e (u₂ + w)).1, arch F (M.co.e (u₂ + w)).2) ∈ lagSetA M M₁ H H' :=
      mem_lagSetA_cz M M₁ H H' hc hz hz1
    have m3 : (arch F (M.co.e u₂).1, arch F (M.co.e u₂).2) ∈ lagSetA M M₁ H H' :=
      mem_lagSetA_c M M₁ H H' hc
    have m4 : (arch F (M.co.e w).1, arch F (M.co.e w).2) ∈ lagSetA M M₁ H H' :=
      mem_lagrangian_set_archimedean M M₁ H H' hz hz1
    have hsplit : ⇑g = sch (trP F _) (arch F (M.co.e u₁).1) (arch F (M.co.e u₁).2)
        (sch (trP F _) (arch F (M.co.e u₂).1) (arch F (M.co.e u₂).2)
          (sch (trP F _) (arch F (M.co.e w).1) (arch F (M.co.e w).2) ⇑f)) := by
      rw [hg]
      dsimp only
      rw [add_assoc, (eadd _ _).1, (eadd _ _).2, schA_add _ _ _ _ _ (hiso _ m1 _ m2), (eadd _ _).1, (eadd _ _).2,
        schA_add _ _ _ _ _ (hiso _ m3 _ m4)]
    obtain ⟨h₃, hh₃⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e w).1) (arch F (M.co.e w).2) f
    obtain ⟨h₂, hh₂⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e u₂).1) (arch F (M.co.e u₂).2) h₃
    obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) (S f)
    rw [← hh₃, ← hh₂] at hsplit
    rw [hℓ, hℓ, F2 S hS u₁ (Or.inl ⟨y, rfl⟩) hat1 h₂ g hsplit, F2 S hS u₂ (Or.inr ⟨c, rfl⟩) hat2 h₃ h₂ hh₂,
      F1 S hS z hz f h₃ g₁ hh₃ hg₁, hg₁]
    simp [sch, hz1, echA_zero]
  have zξ : ∀ ξ : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F, ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
      At (evI F) z ∧ arch F (M₁.co.e z).1 = ξ ∧ arch F (M₁.co.e z).2 = 0 := by
    intro ξ
    refine ⟨M₁.co.e.symm (fun i => liftA F (ξ i), 0), fun u hu => ?_, ?_, ?_⟩
    · rw [← LinearEquiv.map_smul]
      have : u • ((fun i => liftA F (ξ i), 0) : (Fin n₁ × Fin d₁ → AF F) × (Fin n₁ × Fin d₁ → AF F)) = 0 := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        simp [atA_liftA (ξ i) u hu]
      rw [this, map_zero]
    · funext i; simp [arch, evIA_liftA]
    · simp [archA_zero]
  have key : ∀ (f : SInf F (Fin n × Fin d)) (ξ : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F),
      ∃ h : SInf F (Fin n × Fin d), ∀ S : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
        GlobalTheory.ThK.EvUniqB.InfRel B M M₁ H.ι H'.ι (isoA H H') S → S h 0 = S f ξ := by
    intro f ξ
    obtain ⟨z, hz, hz1, hz2⟩ := zξ ξ
    obtain ⟨h, hh⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).1)
      (arch F (M.co.e (incM F H.ι * z * (incM F H'.ι)ᵀ)).2) f
    refine ⟨h, fun S hS => ?_⟩
    obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.schroedinger_preserves_schwartz_real (trP F _) (arch F (M₁.co.e z).1) (arch F (M₁.co.e z).2) (S f)
    rw [F1 S hS z hz f h g₁ hh hg₁, hg₁]
    simp [sch, hz1, hz2, echA_zero]
  have hne : ℓ T ≠ 0 := by
    intro h
    apply hT
    refine ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_
    obtain ⟨h', hh'⟩ := key f ξ
    have := congrArg (fun L => L h') h
    simp only [hℓ, ContinuousLinearMap.zero_apply] at this
    rw [← hh' T hR, this]
    rfl
  have hiso' : ∀ l ∈ Λ, ∀ l' ∈ Λ, trP F (Fin n × Fin d) l.1 l'.2 = trP F (Fin n × Fin d) l'.1 l.2 :=
    fun l hl l' hl' => hiso l hl l' hl'
  have hco' : ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      (∀ l ∈ Λ, trP F (Fin n × Fin d) v.1 l.2 = trP F (Fin n × Fin d) l.1 v.2) → v ∈ Λ := fun v hv => hco v hv
  have hT1 := inv T hR
  have hT2 := inv T' hR'
  obtain ⟨C, hC'⟩ := GlobalTheory.T.aux_statement_2 (Y := Fin n × Fin d → mixedEmbedding.mixedSpace F)
    (trP F (Fin n × Fin d)) (GlobalTheory.T.trace_pairing_nondegenerate F (Fin n × Fin d)) Λ hiso' hco' (ℓ T) (ℓ T') hT1 hT2 hne
  refine ⟨C, ContinuousLinearMap.ext fun f => SchwartzMap.ext fun ξ => ?_⟩
  obtain ⟨h', hh'⟩ := key f ξ
  have := congrArg (fun L => L h') hC'
  simp only [hℓ, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
  rw [← hh' T' hR', this, hh' T hR]
  rfl
