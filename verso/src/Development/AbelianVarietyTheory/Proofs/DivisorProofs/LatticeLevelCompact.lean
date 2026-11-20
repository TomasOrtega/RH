import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingAdelicMatrixBoundedStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.ThKLevelCpt

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d J K hK`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Use `haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension`.

Establish `hcA : Continuous (cA σ : AE F E → AE F E)` using `IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap`. Establish `hc : IsClosed ((UG (cA σ) (incM F J) : Subgroup (GL (Fin d) (AE F E))) : Set (GL (Fin d) (AE F E)))`. Establish `hv : Continuous fun g : GL (Fin d) (AE F E) => (g : Matrix (Fin d) (Fin d) (AE F E))` using `Units.continuous_val`. Conclude with `isClosed_eq (((hv.matrix_transpose).matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA)) continuous_const`. Set `S : Set (Matrix (Fin d) (Fin d) (AE F E))` to `Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K`.

Establish `hS : IsCompact S` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK`. Establish `hemb` using `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin d) (Fin d) (AE F E))).comp hc.isClosedEmbedding_subtypeVal`. Use `⟨_, hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op)), fun g h1 h2 => ?_⟩` and prove the remaining obligations. Conclude with `⟨fun i _ j _ => h1 i j, (mat g⁻¹), fun i _ j _ => h2 i j, rfl⟩`.
-/
theorem exists_compact_of_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (K : Set (AE F E)), IsCompact K →
    ∃ C : Set (UA σ J), IsCompact C ∧ ∀ g : UA σ J, (∀ i j, mat g i j ∈ K) → (∀ i j, mat g⁻¹ i j ∈ K) → g ∈ C := by
  intro F E _ _ _ _ _ σ d J K hK
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed ((UG (cA σ) (incM F J) : Subgroup (GL (Fin d) (AE F E))) : Set (GL (Fin d) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin d) (AE F E) => (g : Matrix (Fin d) (Fin d) (AE F E)) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose).matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))
      continuous_const
  let S : Set (Matrix (Fin d) (Fin d) (AE F E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin d) (Fin d) (AE F E))).comp
    hc.isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op)), fun g h1 h2 => ?_⟩
  exact ⟨fun i _ j _ => h1 i j, (mat g⁻¹), fun i _ j _ => h2 i j, rfl⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d W hL`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Establish `hm : Continuous fun g : UA σ W.J => mat g` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hmi : Continuous fun g : UA σ W.J => mat g⁻¹` using `hm.comp continuous_inv`.

Take `⟨K, hK, hKe⟩` from `GlobalTheory.T.lattice_preserving_adelic_matrix_bounded F E d W hL`. Take `⟨C, hC, hCe⟩` from `exists_compact_of_entries F E σ d W.J K hK`. Establish `hcl : IsClosed (GlobalTheory.ThKLevel.latLevel σ W : Set (UA σ W.J))`. Establish `h1 : IsClosed (GlobalTheory.ThKAdm.FinPt σ W)` using `isClosed_UAtSub (σ := σ) W (fun a : AF F => a.2)`. Establish `h2 : IsClosed {k : UA σ W.J | ∀ w : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W w, mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W w ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W w}`.

Simplify using `only [Set.ofPred_forall]`. Use `isClosed_iInter fun w => isClosed_iInter fun z => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `((GlobalTheory.T.local_lattice_isClosed F E d W hL w).preimage (hm.matrix_mulVec continuous_const)).inter ((GlobalTheory.T.local_lattice_isClosed F E d W hL w).preimage (hmi.matrix_mulVec continuous_const))`. Conclude with `h1.inter h2`. Use `hC.of_isClosed_subset hcl fun k hk => hCe k ?_ ?_` and prove the remaining obligations.

Conclude with `hKe (mat k) hk.1 (fun v z hz => (hk.2 v z hz).1)`. Establish `hk' : k⁻¹ ∈ GlobalTheory.ThKLevel.latLevel σ W` using `(GlobalTheory.ThKLevel.latLevel σ W).inv_mem hk`. Conclude with `hKe (mat k⁻¹) hk'.1 (fun v z hz => (hk'.2 v z hz).1)`.
-/
theorem isCompact_latLevel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d), W.L.IsLattice E →
    IsCompact (GlobalTheory.ThKLevel.latLevel σ W : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)) := by
  intro F E _ _ _ _ _ σ d W hL
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ W.J => mat g⁻¹ := hm.comp continuous_inv
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.T.lattice_preserving_adelic_matrix_bounded F E d W hL
  obtain ⟨C, hC, hCe⟩ := exists_compact_of_entries F E σ d W.J K hK
  have hcl : IsClosed (GlobalTheory.ThKLevel.latLevel σ W : Set (UA σ W.J)) := by
    have h1 : IsClosed (GlobalTheory.ThKAdm.FinPt σ W) := isClosed_UAtSub (σ := σ) W (fun a : AF F => a.2)
    have h2 : IsClosed {k : UA σ W.J | ∀ w : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W w,
        mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W w ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W w} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun w => isClosed_iInter fun z => isClosed_iInter fun _ => ?_
      exact ((GlobalTheory.T.local_lattice_isClosed F E d W hL w).preimage (hm.matrix_mulVec continuous_const)).inter
        ((GlobalTheory.T.local_lattice_isClosed F E d W hL w).preimage (hmi.matrix_mulVec continuous_const))
    exact h1.inter h2
  refine hC.of_isClosed_subset hcl fun k hk => hCe k ?_ ?_
  · exact hKe (mat k) hk.1 (fun v z hz => (hk.2 v z hz).1)
  · have hk' : k⁻¹ ∈ GlobalTheory.ThKLevel.latLevel σ W := (GlobalTheory.ThKLevel.latLevel σ W).inv_mem hk
    exact hKe (mat k⁻¹) hk'.1 (fun v z hz => (hk'.2 v z hz).1)

end GlobalTheory.ThKLevelCpt

end
