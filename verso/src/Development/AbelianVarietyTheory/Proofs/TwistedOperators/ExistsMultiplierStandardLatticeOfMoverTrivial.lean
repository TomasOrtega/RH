import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.MoverStd

/- English proof (translation)
Introduce `D S k₀ Λ' σ w hσ hk hm v hv`. Take `⟨hfg, -, -⟩` from `Base.stdL_mem_Vset (E := D.host.E) S.rank 1`. Establish `hs : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤`. Rewrite using `[stdL, Submodule.span_span_of_tower, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `ht : ∀ u, MovLev.lf (MovLev.idem w.asIdeal) • (fmtC S k₀⁻¹ *ᵥ u) = MovLev.lf (MovLev.idem w.asIdeal) • u` using `fun u => MovLev.smul_mulVec_eq _ _ (fun v' => by`. Distinguish the cases in `hv' : w.asIdeal ≤ v'.asIdeal`. Establish `e : v' = w` using `(HeightOneSpectrum.ext (w.isMaximal.eq_of_le v'.isPrime.ne_top hv')).symm`.

Substitute `e` using the available equality. Use `Or.inr fun ε hε i j => ?_` and prove the remaining obligations. Take `⟨α, rfl, -, hα0⟩` from `hε`. Establish `hασ : α * σ = 0`. Use `FiniteAdeleRing.ext D.host.F fun u => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `α u * σ u = 0`. Distinguish the cases in `hu : u = v'`. Substitute `hu` using the available equality. Rewrite using `[show σ u = 0 from hσ, mul_zero]`. Rewrite using `[show α u = 0 from hα0 u hu, zero_mul]`.

Establish `hmul : pairA D.host.F 0 α * (1 - pairA D.host.F 0 σ) = pairA D.host.F 0 α`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(0 : Ainf D.host.F) * (1 - 0) = 0`. Rewrite using `[zero_mul]`. Express the relevant statement in the definitionally equal form `α * (1 - σ) = α`.

Rewrite using `[mul_sub, mul_one, hασ, sub_zero]`. Establish `h0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * (mt S k₀⁻¹ - 1) i j = 0`. Rewrite using `[← hmul, map_mul, mul_assoc, map_sub, map_one, hk i j, mul_zero]`. Use `congrArg (cA D) h0` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero, Matrix.sub_apply, map_sub]`.

Establish `e1 : cA D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)`. Express the relevant statement in the definitionally equal form `(pairA D.host.F 0 α) ⊗ₜ D.sp.cm.sig 1 = (pairA D.host.F 0 α) ⊗ₜ 1`. Rewrite using `[map_one]`. Establish `e' : cA D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j`. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Use `exacts [map_one _, map_zero _]`. Rewrite `this` using `[e1, e']`. Conclude with `this`. Conclude with `Or.inl (if_neg hv')) u`.

Take `⟨t, htw, H⟩` from `MovLev.exists_mul (E := D.host.E) w.asIdeal.primeCompl w.asIdeal (fun v' hv' => by`. Establish `h1 : ¬ v'.asIdeal ≤ w.asIdeal` using `fun h => hv' ((v'.isMaximal.eq_of_le w.isPrime.ne_top h) ▸ le_rfl)`. Take `⟨a, ha, ha'⟩` from `SetLike.not_le_iff_exists.1 h1`. Conclude with `⟨a, ha', ha⟩)`. Use the proof step `(L := Submodule.span (𝓞 D.host.E) {v}) (Λ := stdL D.host.E S.rank) (Submodule.fg_span_singleton v) hfg hs`.

Use the proof step `(fun z hz => by`. Establish `hz' : z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin S.rank → D.host.E))` using `AddSubgroup.closure_mono (by`. Introduce and unpack `y ⟨a, ha, x, hx, e⟩`. Conclude with `⟨a, ha, x, (Submodule.span_le.2 (Set.singleton_subset_iff.2 hv)) hx, e⟩) hz`. Express the relevant statement in the definitionally equal form `MovLev.lf (MovLev.idem w.asIdeal) • z ∈ _`.

Rewrite using `[← ht z]`. Conclude with `MovLev.hat_int (MovLev.idem_int _) ((hm _).2 ⟨z, hz', rfl⟩))`. Conclude with `⟨t, htw, H v (Submodule.mem_span_singleton_self v)⟩`.
-/
theorem exists_mul_std : ∀ (D : D7) (S : HSp D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (σ : Af D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), evalV D.host.F w σ = 0 → (∀ i j, (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * (mt S k₀⁻¹ - 1) i j = 0) → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ v ∈ Λ', ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • v ∈ stdL D.host.E S.rank := by
  intro D S k₀ Λ' σ w hσ hk hm v hv
  obtain ⟨hfg, -, -⟩ := Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  have hs : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
    congr 2
    funext i
    simp
  have ht : ∀ u, MovLev.lf (MovLev.idem w.asIdeal) • (fmtC S k₀⁻¹ *ᵥ u) = MovLev.lf (MovLev.idem w.asIdeal) • u :=
    fun u => MovLev.smul_mulVec_eq _ _ (fun v' => by
      by_cases hv' : w.asIdeal ≤ v'.asIdeal
      · have e : v' = w := (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v'.isPrime.ne_top hv')).symm
        subst e
        refine Or.inr fun ε hε i j => ?_
        obtain ⟨α, rfl, -, hα0⟩ := hε
        have hασ : α * σ = 0 := by
          refine FiniteAdeleRing.ext D.host.F fun u => ?_
          change α u * σ u = 0
          by_cases hu : u = v'
          · subst hu
            rw [show σ u = 0 from hσ, mul_zero]
          · rw [show α u = 0 from hα0 u hu, zero_mul]
        have hmul : pairA D.host.F 0 α * (1 - pairA D.host.F 0 σ) = pairA D.host.F 0 α := by
          refine Prod.ext ?_ ?_
          · change (0 : Ainf D.host.F) * (1 - 0) = 0
            rw [zero_mul]
          · change α * (1 - σ) = α
            rw [mul_sub, mul_one, hασ, sub_zero]
        have h0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * (mt S k₀⁻¹ - 1) i j = 0 := by
          rw [← hmul, map_mul, mul_assoc, map_sub, map_one, hk i j, mul_zero]
        have := congrArg (cA D) h0
        rw [map_mul, map_zero, Matrix.sub_apply, map_sub] at this
        have e1 : cA D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
            algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
          change (pairA D.host.F 0 α) ⊗ₜ D.sp.cm.sig 1 = (pairA D.host.F 0 α) ⊗ₜ 1
          rw [map_one]
        have e' : cA D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
            (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
          rw [Matrix.one_apply]
          split_ifs
          exacts [map_one _, map_zero _]
        rw [e1, e'] at this
        exact this
      · exact Or.inl (if_neg hv')) u
  obtain ⟨t, htw, H⟩ := MovLev.exists_mul (E := D.host.E) w.asIdeal.primeCompl w.asIdeal (fun v' hv' => by
      have h1 : ¬ v'.asIdeal ≤ w.asIdeal := fun h => hv' ((v'.isMaximal.eq_of_le w.isPrime.ne_top h) ▸ le_rfl)
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h1
      exact ⟨a, ha', ha⟩)
    (L := Submodule.span (𝓞 D.host.E) {v}) (Λ := stdL D.host.E S.rank) (Submodule.fg_span_singleton v) hfg hs
    (fun z hz => by
      have hz' : z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin S.rank → D.host.E)) := AddSubgroup.closure_mono (by
        rintro y ⟨a, ha, x, hx, e⟩
        exact ⟨a, ha, x, (Submodule.span_le.2 (Set.singleton_subset_iff.2 hv)) hx, e⟩) hz
      change MovLev.lf (MovLev.idem w.asIdeal) • z ∈ _
      rw [← ht z]
      exact MovLev.hat_int (MovLev.idem_int _) ((hm _).2 ⟨z, hz', rfl⟩))
  exact ⟨t, htw, H v (Submodule.mem_span_singleton_self v)⟩

end GlobalTheory.Ker.MoverStd
