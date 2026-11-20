import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.RtWMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host
namespace UpperTheory.V.Sd.Wc
private def wGL (R : Type) [CommRing R] : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `f ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) S) i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem map_wGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    GeneralLinearGroup.map f (wGL R) = wGL S := by
  ext i j
  change f ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) i j) = (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) S) i j
  fin_cases i <;> fin_cases j <;> simp
/- English proof (translation)
Rewrite using `[map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq]`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.scalar (Fin 2) g.val.det = !![0, 1; -1, 0] * (g.val * !![0, -1; 1, 0]) * g.valᵀ`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`.

Apply the tactic sequence `simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring`.
-/
private theorem invT_eq {R : Type} [CommRing R] (g : GL (Fin 2) R) :
    invT 2 R g = GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det g)⁻¹ * (wGL R * (g * (wGL R)⁻¹)) := by
  rw [map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change Matrix.scalar (Fin 2) g.val.det = !![0, 1; -1, 0] * (g.val * !![0, -1; 1, 0]) * g.valᵀ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring
/- English proof (translation)
Set `k : TR.Kinf F 2` to `⟨!![0, -1; 1, 0], by`. Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Use extensionality with `i j : 1`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩`. Establish `hk : Unitary.toUnits k = (wGL (TR.Rinf F))⁻¹` using `Units.ext rfl`.

Rewrite using `[← TR.infGL_mul_finGL (wGL (Ad F))⁻¹, map_inv, map_wGL, ← hk, map_mul]`. Conclude with `π.stable (.cpt k) _ (π.stable (.fin _) _ hφ)`.
-/
private theorem rt_w_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    {φ : TR.Sm F 2} (hφ : φ ∈ π.V) : TR.rt F 2 (wGL (Ad F))⁻¹ φ ∈ π.V := by
  let k : TR.Kinf F 2 := ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hk : Unitary.toUnits k = (wGL (TR.Rinf F))⁻¹ := Units.ext rfl
  rw [← TR.infGL_mul_finGL (wGL (Ad F))⁻¹, map_inv, map_wGL, ← hk, map_mul]
  exact π.stable (.cpt k) _ (π.stable (.fin _) _ hφ)
end UpperTheory.V.Sd.Wc
open UpperTheory.V UpperTheory.V.Sd.Wc in
/- English proof (translation)
Introduce `P F _ _ _ π ω h`. Take `⟨B, hl, hr, hf, hc, hX⟩` from `P.gkR F 2 π`. Use `TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX ?_` and prove the remaining obligations. Establish `hle : (π.dual.twist ω).V ≤ π.V`. Introduce and unpack `_ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩`.

Use `rt_w_mem π hφ using 1` and compare the differences between its conclusion and the goal. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 (invT 2 (Ad F) g) * ((ω.1 (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = φ.1 (g * (wGL (Ad F))⁻¹)`. Establish `e : wGL (Ad F) = ratGL F 2 (wGL F)` using `(map_wGL _).symm`. Rewrite using `[invT_eq, h _ φ hφ, map_inv, mul_right_comm, Units.inv_mul, one_mul]`.

Use `conv_lhs => rw [e]`. Rewrite using `[(π.cusp φ hφ).1.left, ← e]`. Establish `e : π.dual.twist ω = π` using `TR.CuspSub.ext ((π.irred _ hle (π.dual.twist ω).stable).resolve_left (π.dual.twist ω).ne_bot)`. Rewrite using `[e]`. Conclude with `TR.CuspSub.Iso.refl π`.
-/
theorem UpperTheory.V.Sd.Wc.polGL2_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Wc.PolGL2 := by
  intro P F _ _ _ π ω h
  obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
  refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX ?_
  have hle : (π.dual.twist ω).V ≤ π.V := by
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    convert rt_w_mem π hφ using 1
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (invT 2 (Ad F) g) * ((ω.1 (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = φ.1 (g * (wGL (Ad F))⁻¹)
    have e : wGL (Ad F) = ratGL F 2 (wGL F) := (map_wGL _).symm
    rw [invT_eq, h _ φ hφ, map_inv, mul_right_comm, Units.inv_mul, one_mul]
    conv_lhs => rw [e]
    rw [(π.cusp φ hφ).1.left, ← e]
  have e : π.dual.twist ω = π :=
    TR.CuspSub.ext ((π.irred _ hle (π.dual.twist ω).stable).resolve_left (π.dual.twist ω).ne_bot)
  rw [e]
  exact TR.CuspSub.Iso.refl π
end
end
