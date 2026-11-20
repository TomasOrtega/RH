import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldInducedMaxCompactVector
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphFUnr

/- English proof (translation)
Establish `hset : ({x : E | x ∈ 𝒪[E]} : Set E) = (valBall E 0 : Set E)`. Rewrite using `[coe_valBall_zero]`. Both sides reduce to the same expression. Establish `hclopen : IsClopen ({x : E | x ∈ 𝒪[E]} : Set E)`. Rewrite using `[hset]`.

Conclude with `⟨isClosed_valBall 0, isOpen_valBall 0⟩`. Establish `hcomp : IsCompact ({x : E | x ∈ 𝒪[E]} : Set E)`. Rewrite using `[hset]`. Conclude with `isCompact_valBall 0`. Use `⟨?_, HasCompactSupport.intro hcomp fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations.

Use `(IsLocallyConstant.iff_exists_open _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ ({x : E | x ∈ 𝒪[E]} : Set E)`. Conclude with `⟨_, hclopen.isOpen, hx, fun y hy => by`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Use the proof step `rfl⟩`.

Conclude with `⟨_, hclopen.compl.isOpen, hx, fun y hy => by`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩`.
-/
theorem indicator_integers_mem_SBE (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    IsLocallyConstant (Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ)) ∧
      HasCompactSupport (Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ)) := by
  have hset : ({x : E | x ∈ 𝒪[E]} : Set E) = (valBall E 0 : Set E) := by
    rw [coe_valBall_zero]; rfl
  have hclopen : IsClopen ({x : E | x ∈ 𝒪[E]} : Set E) := by
    rw [hset]; exact ⟨isClosed_valBall 0, isOpen_valBall 0⟩
  have hcomp : IsCompact ({x : E | x ∈ 𝒪[E]} : Set E) := by
    rw [hset]; exact isCompact_valBall 0
  refine ⟨?_, HasCompactSupport.intro hcomp fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ ({x : E | x ∈ 𝒪[E]} : Set E)
  · exact ⟨_, hclopen.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨_, hclopen.compl.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

/- English proof (translation)
Introduce `hP hK hN F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη hcond hres c hcu`. Establish `hW` using `GlobalTheory.CompanionTheory.NormModulus.wMod F χ hχ hχ1 E hd hc σ hσ η hη`. Establish `hmodt : ∀ t : Eˣ, modulus (Algebra.norm F (t : E)) = 1 → modulus (t : E) = 1`. Introduce `t ht`. Establish `h` using `hW (t : E)`.

Rewrite `h` using `[ht]`. Conclude with `h` after adjusting the coercions. Establish `hct : ∀ t : Eˣ, modulus (t : E) = 1 → c t = 1`. Introduce `t ht`. Establish `hmem : t ∈ unitFiltrationUnits E 0` using `ord_eq_zero_iff_mem.1 (modulus_eq_one_iff.1 ht).2`.

Conclude with `MonoidHom.mem_ker.1 (hcu hmem)`. Establish `hSB : Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ) ∈ GL2LocalData.SBc F E c`. Take `⟨h1, h2⟩` from `indicator_integers_mem_SBE E`. Use `⟨h1, h2, fun u hu x => ?_⟩` and prove the remaining obligations. Establish `hm : modulus (u : E) = 1` using `hmodt u (by rw [hu]; simp)`.

Rewrite using `[GlobalTheory.CompanionTheory.PiKFUnr.indicator_mul_of_modulus_eq_one hm x, hct u hm]`. Simplify using the standard rewrite rules. Use `⟨fun k hk g => ?_, ?_⟩` and prove the remaining obligations. Take `⟨hk1, hk2⟩` from `(GLnLocal.mem_integralGL_iff F 2).1 hk`. Set `u : Fˣ` to `Matrix.GeneralLinearGroup.det k`.

Establish `hu1 : (u : F) ∈ 𝒪[F]` using `GlobalTheory.CompanionTheory.PiKFUnr.det_mem_of_entries hk1`. Establish `hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F]`. Establish `: ((u⁻¹ : Fˣ) : F) = ((k⁻¹ : GL (Fin 2) F).val).det`. Simplify using `[u, map_inv]`. Rewrite using `[this]`.

Conclude with `GlobalTheory.CompanionTheory.PiKFUnr.det_mem_of_entries hk2`. Establish `hex : ∃ t : Eˣ, Algebra.norm F (t : E) = (k.val).det` using `hN F χ hχ hχ1 E hd hc σ hσ η hη hres u hu1 hu2`. Rewrite using `[(hP F χ hχ hχ1 E hd hc σ hσ η hη c _ hSB g k hex).1, hK F χ hχ hχ1 E hd hc σ hσ η hη hcond hres c hcu k hk]`. Use `show GL2LocalData.Wc χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) c _ 1 = 1`. Establish `hex : ∃ t : Eˣ, Algebra.norm F (t : E) = ((1 : GL (Fin 2) F).val).det` using `⟨1, by simp⟩`.

Unfold `GL2LocalData.Wc`. Rewrite using `[dif_pos hex]`. Establish `hN1 : Algebra.norm F (hex.choose : E) = 1`. Rewrite using `[hex.choose_spec]`. Simplify using the standard rewrite rules.

Generalize the expression as in `hex.choose = t at hN1 ⊢`. Establish `hm : modulus (t : E) = 1` using `hmodt _ (by rw [hN1]; simp)`. Establish `hmem : (t : E) ∈ {x : E | x ∈ 𝒪[E]}` using `modulus_le_one_iff.1 hm.le`. Establish `hns : GL2LocalData.nsg E (1 : F) = 1`. Unfold `GL2LocalData.nsg`.

Rewrite using `[if_pos ⟨1, by simp⟩]`. Rewrite using `[hct _ hm]`. Simplify using `only [GL2LocalData.rW]`. Simplify using `[hns]`. Conclude with `Set.indicator_of_mem hmem (1 : E → ℂ)`.
-/
theorem sphf : Ad3.K.GL2LocalData.WPiRep → Ad3.K.QuadraticBaseChangeGL3.Th.PIKF → Ad3.K.QuadraticBaseChangeGL3.Th.NORMU → Ad3.K.QuadraticBaseChangeGL3.Th.SPHF := by
  intro hP hK hN F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη hcond hres c hcu
  have hW := GlobalTheory.CompanionTheory.NormModulus.wMod F χ hχ hχ1 E hd hc σ hσ η hη
  have hmodt : ∀ t : Eˣ, modulus (Algebra.norm F (t : E)) = 1 → modulus (t : E) = 1 := by
    intro t ht
    have h := hW (t : E)
    rw [ht] at h
    exact_mod_cast h
  have hct : ∀ t : Eˣ, modulus (t : E) = 1 → c t = 1 := by
    intro t ht
    have hmem : t ∈ unitFiltrationUnits E 0 :=
      ord_eq_zero_iff_mem.1 (modulus_eq_one_iff.1 ht).2
    exact MonoidHom.mem_ker.1 (hcu hmem)
  have hSB : Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ) ∈ GL2LocalData.SBc F E c := by
    obtain ⟨h1, h2⟩ := indicator_integers_mem_SBE E
    refine ⟨h1, h2, fun u hu x => ?_⟩
    have hm : modulus (u : E) = 1 := hmodt u (by rw [hu]; simp)
    rw [GlobalTheory.CompanionTheory.PiKFUnr.indicator_mul_of_modulus_eq_one hm x, hct u hm]
    simp
  refine ⟨fun k hk g => ?_, ?_⟩
  · obtain ⟨hk1, hk2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
    let u : Fˣ := Matrix.GeneralLinearGroup.det k
    have hu1 : (u : F) ∈ 𝒪[F] := GlobalTheory.CompanionTheory.PiKFUnr.det_mem_of_entries hk1
    have hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
      have : ((u⁻¹ : Fˣ) : F) = ((k⁻¹ : GL (Fin 2) F).val).det := by
        simp [u, map_inv]
      rw [this]
      exact GlobalTheory.CompanionTheory.PiKFUnr.det_mem_of_entries hk2
    have hex : ∃ t : Eˣ, Algebra.norm F (t : E) = (k.val).det :=
      hN F χ hχ hχ1 E hd hc σ hσ η hη hres u hu1 hu2
    rw [(hP F χ hχ hχ1 E hd hc σ hσ η hη c _ hSB g k hex).1,
      hK F χ hχ hχ1 E hd hc σ hσ η hη hcond hres c hcu k hk]
  · show GL2LocalData.Wc χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) c _ 1 = 1
    have hex : ∃ t : Eˣ, Algebra.norm F (t : E) = ((1 : GL (Fin 2) F).val).det :=
      ⟨1, by simp⟩
    unfold GL2LocalData.Wc
    rw [dif_pos hex]
    have hN1 : Algebra.norm F (hex.choose : E) = 1 := by
      rw [hex.choose_spec]; simp
    generalize hex.choose = t at hN1 ⊢
    have hm : modulus (t : E) = 1 := hmodt _ (by rw [hN1]; simp)
    have hmem : (t : E) ∈ {x : E | x ∈ 𝒪[E]} := modulus_le_one_iff.1 hm.le
    have hns : GL2LocalData.nsg E (1 : F) = 1 := by
      unfold GL2LocalData.nsg
      rw [if_pos ⟨1, by simp⟩]
    rw [hct _ hm]
    simp only [GL2LocalData.rW]
    simp [hns]
    exact Set.indicator_of_mem hmem (1 : E → ℂ)

end GlobalTheory.CompanionTheory.SphFUnr
