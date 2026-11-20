import Mathlib
import GroundTheory.PAdicHodge.BCrisNewton
import GroundTheory.PAdicHodge.GalSmulAlgebraMapPadicPlus
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Abstract

variable {G B E : Type*} [Group G] [CommRing B] [IsDomain B] [MulSemiringAction G B] [Field E]
  [MulSemiringAction G E]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem image_fixedPoints_fractionRing_of_embedding (ι : B →+* E) (hι : Function.Injective ι)
    (hequiv : ∀ (g : G) (b : B), ι (g • b) = g • ι b)
    (hfix : ∀ a b : B, b ≠ 0 → (∀ g : G, g • (ι a / ι b) = ι a / ι b) →
      ∃ y : B, (∀ g : G, g • y = y) ∧ ι y = ι a / ι b) :
    letI := IsFractionRing.mulSemiringAction G B (FractionRing B)
    algebraMap B (FractionRing B) '' MulAction.fixedPoints G B =
      MulAction.fixedPoints G (FractionRing B) := by
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  set j : FractionRing B →+* E := IsFractionRing.lift hι with hj
  have hjalg : ∀ x : B, j (algebraMap B (FractionRing B) x) = ι x := fun x =>
    IsFractionRing.lift_algebraMap _ _
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ g
    rw [← algebraMap.coe_smul', hy g]
  · intro hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hfixE : ∀ g : G, g • (ι a / ι b) = ι a / ι b := by
      intro g
      have h1 := congrArg j (hx g)
      rw [smul_div₀', ← algebraMap.coe_smul', ← algebraMap.coe_smul', map_div₀, map_div₀, hjalg,
        hjalg, hjalg, hjalg, hequiv, hequiv] at h1
      rw [smul_div₀']
      exact h1
    obtain ⟨y, hy, hyab⟩ := hfix a b hb0 hfixE
    refine ⟨y, hy, j.injective ?_⟩
    rw [hjalg, hyab, map_div₀, hjalg, hjalg]

end Abstract

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

include hζ in
set_option maxHeartbeats 3200000 in

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_fixed_iotaB_eq [FiniteDimensional ℚ_[p] K] {x : 𝔹dR} (hx : x ∈ fracBCris hε hζ)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ y : BCris hε, (∀ σ : Gal(PadicAlgCl p/K), galB hε σ y = y) ∧ iotaB hε hζ y = x := by
  obtain ⟨k, hk, hxk⟩ := fracBCris_fixed (K := K) hε hζ hx hfix
  obtain ⟨y, hy, hyk⟩ := exists_bCris_fixed (K := K) hε hζ hk
  exact ⟨y, hy, by rw [hyk, hxk]; rfl⟩

include hζ in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem image_fixedPoints_fractionRing [FiniteDimensional ℚ_[p] K] :
    letI := isDomain_bCris hε hζ
    letI := galBAction (K := K) hε
    letI := IsFractionRing.mulSemiringAction Gal(PadicAlgCl p/K) (BCris hε) (FractionRing (BCris hε))
    algebraMap (BCris hε) (FractionRing (BCris hε)) ''
        MulAction.fixedPoints Gal(PadicAlgCl p/K) (BCris hε) =
      MulAction.fixedPoints Gal(PadicAlgCl p/K) (FractionRing (BCris hε)) :=
  letI := isDomain_bCris hε hζ
  letI := galBAction (K := K) hε
  image_fixedPoints_fractionRing_of_embedding (iotaB hε hζ) (iotaB_injective hε hζ)
    (fun σ b => iotaB_galB (K := K) hε hζ σ b)
    (fun a b _ h => exists_fixed_iotaB_eq (K := K) hε hζ
      (div_mem (iotaB_mem_fracBCris hε hζ a) (iotaB_mem_fracBCris hε hζ b)) h)

end ACris

end GroundTheory.PAdicHodge
