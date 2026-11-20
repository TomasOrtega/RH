import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldSphericalVectorTheta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulIntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.StdSphOf

/- English proof (translation)
Establish `hset : ({x : F | x ∈ 𝒪[F]} : Set F) = (valBall F 0 : Set F)`. Rewrite using `[coe_valBall_zero]`. Both sides reduce to the same expression. Establish `hc1 : IsClopen ({x : F | x ∈ 𝒪[F]} : Set F)`. Rewrite using `[hset]`.

Conclude with `⟨isClosed_valBall 0, isOpen_valBall 0⟩`. Establish `hk1 : IsCompact ({x : F | x ∈ 𝒪[F]} : Set F)`. Rewrite using `[hset]`. Conclude with `isCompact_valBall 0`. Establish `hS : ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F)) = ({x : F | x ∈ 𝒪[F]} : Set F) ×ˢ ({x : F | x ∈ 𝒪[F]} : Set F)` using `rfl`.

Establish `hclopen : IsClopen ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F))`. Rewrite using `[hS]`. Conclude with `hc1.prod hc1`. Establish `hcomp : IsCompact ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F))`. Rewrite using `[hS]`.

Conclude with `hk1.prod hk1`. Use `⟨?_, HasCompactSupport.intro hcomp fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Use `(IsLocallyConstant.iff_exists_open _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F))`. Conclude with `⟨_, hclopen.isOpen, hx, fun y hy => by`.

Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Use the proof step `rfl⟩`. Conclude with `⟨_, hclopen.compl.isOpen, hx, fun y hy => by`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩`.
-/
theorem indicator_prod_integers (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    IsLocallyConstant (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} (1 : F × F → ℂ)) ∧
      HasCompactSupport (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} (1 : F × F → ℂ)) := by
  have hset : ({x : F | x ∈ 𝒪[F]} : Set F) = (valBall F 0 : Set F) := by
    rw [coe_valBall_zero]; rfl
  have hc1 : IsClopen ({x : F | x ∈ 𝒪[F]} : Set F) := by
    rw [hset]; exact ⟨isClosed_valBall 0, isOpen_valBall 0⟩
  have hk1 : IsCompact ({x : F | x ∈ 𝒪[F]} : Set F) := by
    rw [hset]; exact isCompact_valBall 0
  have hS : ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F)) =
      ({x : F | x ∈ 𝒪[F]} : Set F) ×ˢ ({x : F | x ∈ 𝒪[F]} : Set F) := rfl
  have hclopen : IsClopen ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F)) := by
    rw [hS]; exact hc1.prod hc1
  have hcomp : IsCompact ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F)) := by
    rw [hS]; exact hk1.prod hk1
  refine ⟨?_, HasCompactSupport.intro hcomp fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ ({x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} : Set (F × F))
  · exact ⟨_, hclopen.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨_, hclopen.compl.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

/- English proof (translation)
Introduce `K _ _ hF hS hL hN h2 c v hU W' hW`. Establish `hψ : IsStd (GP.psiF v)` using `GlobalTheory.CompanionTheory.StdCharQ.stdChar v`. Take `⟨hχc, hχ1, hχ0⟩` from `(GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1`. Break down `hW with ⟨w₁, w₂, i₁, i₂, hne, rfl⟩ | ⟨w, i, hu, σ, η, hσ, hη, rfl⟩` into its components or cases. Use `haveI := i₁ haveI := i₂`.

Establish `r₁ : IsUnramifiedChar (cAt c v w₁)` using `GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1`. Establish `r₂ : IsUnramifiedChar (cAt c v w₂)` using `GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hU w₂).1`. Take `⟨hlc, hcs⟩` from `indicator_prod_integers (Qv v)`. Conclude with `⟨hS (Qv v) _ hχc hχ1 hχ0 _ _ r₁ r₂, Or.inl ⟨w₁, w₂, i₁, i₂, hne, Submodule.subset_span ⟨_, hlc, hcs, 1, by simp⟩, rfl⟩⟩`. Use `haveI := i`.

Break down `GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w _ => (hU w).2) with ⟨a, b, ha, hb, hab⟩ | ⟨w', hw', -, hf, hord⟩` into its components or cases. Conclude with `absurd ((hu a ha).trans (hu b hb).symm) hab`. Take `rfl : w' = w` from `hu w' hw'`. Establish `hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2` using `GlobalTheory.CompanionTheory.NormGauss.card_E hf hord`. Establish `hcont : Continuous (algebraMap (Qv v) (Kv K w'))` using `continuous_adicCompletionMap v w'`.

Establish `hcu` using `(hU w').1`. Establish `hsph` using `hF (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hχ0 hres (localChar c w') hcu`. Take `⟨hlam, hneg⟩` from `hL (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hχ0 hres`. Establish `hWm` using `GlobalTheory.CompanionTheory.NormModulus.wMod (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη`. Establish `hSB : Set.indicator {x : Kv K w' | x ∈ 𝒪[Kv K w']} (1 : Kv K w' → ℂ) ∈ GL2LocalData.SBc (Qv v) (Kv K w') (localChar c w')`.

Take `⟨h1, h3⟩` from `GlobalTheory.CompanionTheory.SphFUnr.indicator_integers_mem_SBE (Kv K w')`. Use `⟨h1, h3, fun u hu' x => ?_⟩` and prove the remaining obligations. Establish `hm : modulus (u : Kv K w') = 1`. Establish `h` using `hWm (u : Kv K w')`. Rewrite `h` using `[hu']`.

Simplify using `only [modulus_one] at h`. Conclude with `h` after adjusting the coercions. Establish `hcone : localChar c w' u = 1` using `MonoidHom.mem_ker.1 (hcu (ord_eq_zero_iff_mem.1 (modulus_eq_one_iff.1 hm).2))`. Rewrite using `[GlobalTheory.CompanionTheory.PiKFUnr.indicator_mul_of_modulus_eq_one hm x, hcone]`. Simplify using the standard rewrite rules.

Use `⟨hsph, Or.inr ⟨w', i, hu, σ, η, hσ, hη, Submodule.subset_span ⟨_, hSB, 1, by simp⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hlam, hneg]`. Simplify using the standard rewrite rules.
-/
theorem stdsph : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.Th.SPHF → Ad3.K.QuadraticBaseChangeGL3.Th.SPHS →
    Ad3.K.QuadraticBaseChangeGL3.Th.LAMU → Ad3.K.QuadraticBaseChangeGL3.Th.NORMU → Ad3.K.QuadraticBaseChangeGL3.Th.STDSPH K := by
  intro K _ _ hF hS hL hN h2 c v hU W' hW
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  obtain ⟨hχc, hχ1, hχ0⟩ :=
    (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
  rcases hW with ⟨w₁, w₂, i₁, i₂, hne, rfl⟩ | ⟨w, i, hu, σ, η, hσ, hη, rfl⟩
  · haveI := i₁
    haveI := i₂
    have r₁ : IsUnramifiedChar (cAt c v w₁) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
    have r₂ : IsUnramifiedChar (cAt c v w₂) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hU w₂).1
    obtain ⟨hlc, hcs⟩ := indicator_prod_integers (Qv v)
    exact ⟨hS (Qv v) _ hχc hχ1 hχ0 _ _ r₁ r₂, Or.inl ⟨w₁, w₂, i₁, i₂, hne,
      Submodule.subset_span ⟨_, hlc, hcs, 1, by simp⟩, rfl⟩⟩
  · haveI := i
    rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w _ => (hU w).2) with
      ⟨a, b, ha, hb, hab⟩ | ⟨w', hw', -, hf, hord⟩
    · exact absurd ((hu a ha).trans (hu b hb).symm) hab
    obtain rfl : w' = w := hu w' hw'
    have hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2 := GlobalTheory.CompanionTheory.NormGauss.card_E hf hord
    have hcont : Continuous (algebraMap (Qv v) (Kv K w')) := continuous_adicCompletionMap v w'
    have hcu := (hU w').1
    have hsph := hF (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hχ0 hres (localChar c w') hcu
    obtain ⟨hlam, hneg⟩ := hL (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hχ0 hres
    have hWm := GlobalTheory.CompanionTheory.NormModulus.wMod (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη
    have hSB : Set.indicator {x : Kv K w' | x ∈ 𝒪[Kv K w']} (1 : Kv K w' → ℂ) ∈
        GL2LocalData.SBc (Qv v) (Kv K w') (localChar c w') := by
      obtain ⟨h1, h3⟩ := GlobalTheory.CompanionTheory.SphFUnr.indicator_integers_mem_SBE (Kv K w')
      refine ⟨h1, h3, fun u hu' x => ?_⟩
      have hm : modulus (u : Kv K w') = 1 := by
        have h := hWm (u : Kv K w')
        rw [hu'] at h
        simp only [modulus_one] at h
        exact_mod_cast h
      have hcone : localChar c w' u = 1 :=
        MonoidHom.mem_ker.1 (hcu (ord_eq_zero_iff_mem.1 (modulus_eq_one_iff.1 hm).2))
      rw [GlobalTheory.CompanionTheory.PiKFUnr.indicator_mul_of_modulus_eq_one hm x, hcone]
      simp
    refine ⟨hsph, Or.inr ⟨w', i, hu, σ, η, hσ, hη, Submodule.subset_span ⟨_, hSB, 1, by simp⟩, ?_⟩⟩
    rw [hlam, hneg]
    simp

end GlobalTheory.CompanionTheory.StdSphOf
