import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
noncomputable section
open Polynomial Pointwise
namespace GlobalTheory.Ord2.SrcForm
open TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
/- English proof (translation)
Establish `hl : Fact l.Prime` using `inferInstance`. Take `⟨π, hinf, hsat⟩` from `P.newform k hk f (-j)`. Use `⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]`. Introduce `h`.

Establish `h1 : (k : ℂ) = 1` using `by linear_combination h`. Establish `h2 : k = 1` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers. Introduce `z hz`. Simplify using `only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz`.

Break down `hz with rfl | rfl` into its components or cases. Conclude with `⟨-j, by push_cast; ring⟩`. Conclude with `⟨1 - k - j, by push_cast; ring⟩`. Use `filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM`. Take `⟨B, hB, hpoly⟩` from `hsat w (not_dvd_of_not_mem hwM)`.

Use `⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `(hw A hA).1 s hs`. Establish `h2 : cycZ ℚ Ω l s = 1`. Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)` and prove the remaining obligations. Rewrite using `[cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]`.

Simplify using the standard rewrite rules. Establish `h3 : (cycBar ℚ Ω l ^ j) s = 1`. Rewrite using `[MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]`. Apply `Units.ext` to reduce the goal to its premises. Establish `h4` using `congrArg Units.val h1`.

Rewrite `h4` using `[tw_val, h3, Units.val_one, one_smul]`. Then use the resulting hypothesis. Establish `h1` using `(hw A hA).2 σ hσ`. Rewrite `h1` using `[tw_val, ← hpoly]`. Use `scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_` and prove the remaining obligations. Rewrite using `[h1]`.

Establish `h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ)`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _`. Rewrite using `[cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]`. Establish `h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j)`. Rewrite using `[MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, inv_zpow']`.

Rewrite using `[h3]`. Use `filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM`. Conclude with `hsat w (not_dvd_of_not_mem hwM)`.
-/
theorem exists_rep_alt (P : _root_.UpperTheory.V.Af.Hypotheses') [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 2 ≤ k) (f : Newform k) (ι : Qbar l ≃+* ℂ) (W : R2 Ω l) (j : ℤ)
    (hf : f.Att ι (tw W (cycBar ℚ Ω l ^ j))) :
    ∃ π : TR.CuspSub ℚ 2, π.IsRegAlg ∧ AttR ι W π ∧ ∀ᶠ w : Pl in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧
      ((algSat 2 (normV w) Bs).map fun b => X - C ((normV w : ℂ) ^ (-j) * b)).prod = f.heckePoly (normV w) := by
  have hl : Fact l.Prime := inferInstance
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ⟨ss_of_tw _ _ hf.1, ?_⟩, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    obtain ⟨B, hB, hpoly⟩ := hsat w (not_dvd_of_not_mem hwM)
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]
  · filter_upwards [ev_not_mem f.M f.pos.ne'] with w hwM
    exact hsat w (not_dvd_of_not_mem hwM)
end GlobalTheory.Ord2.SrcForm
namespace GlobalTheory.Ord2
open TwDet SrcForm
end GlobalTheory.Ord2
end
end
end
