import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPhaseAt

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar

open IsDedekindDomain Topology

/- English proof (translation)
Establish `hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a` using `fun x a => by show GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ x) = _`. Rewrite using `[GlobalTheory.LFun.toFinAd_tmul, mul_comm]`. Use `GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (GlobalTheory.BotFormula.toFinE D).toRingHom) hι ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(GlobalTheory.BotFormula.toFinE D) ((GlobalTheory.BotFormula.toFinE D).symm t) ∈ _`. Rewrite using `[RingEquiv.apply_symm_apply]`.

Conclude with `ht`.
-/
theorem toFinE_symm_mem_OhE {D : D7} (t : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (ht : ∀ w : HeightOneSpectrum (𝓞 D.host.E), t w ∈ w.adicCompletionIntegers D.host.E) :
    (GlobalTheory.BotFormula.toFinE D).symm t ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := fun x a => by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ x) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
  refine GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (GlobalTheory.BotFormula.toFinE D).toRingHom) hι ?_
  change (GlobalTheory.BotFormula.toFinE D) ((GlobalTheory.BotFormula.toFinE D).symm t) ∈ _
  rw [RingEquiv.apply_symm_apply]
  exact ht

/- English proof (translation)
Use `continuous_of_continuousAt_one (finChar c) ?_` and prove the remaining obligations. Take `⟨m, hm, hc⟩` from `c.cont`. Establish `hcont : Continuous (finIdl D)` using `Continuous.units_map _ (GlobalTheory.DefU.ClassFin.continuous_finAdEquiv.comp (GlobalTheory.Member.continuous_finPart D))`. Use `set W : Set (FiniteAdeleRing (𝓞 D.host.E) D.host.E) := {z | ∀ w : HeightOneSpectrum (𝓞 D.host.E), z w ∈ w.adicCompletionIntegers D.host.E} with hW`. Establish `hWo : IsOpen W` using `RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _`.

Use `set k : FiniteAdeleRing (𝓞 D.host.E) D.host.E := algebraMap D.host.E _ (m : D.host.E)⁻¹ with hk`. Establish `h1 : Continuous fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)` using `Units.continuous_val.comp hcont`. Establish `h2 : Continuous fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)` using `Units.continuous_coe_inv.comp hcont`. Establish `h3 : Continuous fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k` using `(h1.sub continuous_const).mul continuous_const`. Use `set V : Set (AE D)ˣ := ((fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩ (fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W …`.

Establish `hV : IsOpen V` using `((hWo.preimage h1).inter (hWo.preimage h2)).inter (hWo.preimage h3)`. Establish `hzero : (0 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W` using `fun w => zero_mem _`. Establish `hone : (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W` using `fun w => one_mem _`. Establish `h1V : (1 : (AE D)ˣ) ∈ V`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show ((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W`. Rewrite using `[map_one, Units.val_one]`. Conclude with `hone`. Use `show (((finIdl D 1)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W`. Rewrite using `[map_one, inv_one, Units.val_one]`.

Conclude with `hone`. Use `show (((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k ∈ W`. Rewrite using `[map_one, Units.val_one, sub_self, zero_mul]`. Conclude with `hzero`. Establish `hmE : (m : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`.

Establish `key : ∀ x ∈ V, finChar c x = 1`. Introduce and unpack `x ⟨⟨hx1, hx2⟩, hx3⟩`. Use `set u := finIdl D x with hu`. Establish `hy : Formalism.MainNotions.StandardLatticesGL3.IntU D (finY D x)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[coe_finY, ← coe_finIdl]`. Conclude with `toFinE_symm_mem_OhE _ hx1`. Rewrite using `[← map_inv, coe_finY, ← coe_finIdl, map_inv]`. Conclude with `toFinE_symm_mem_OhE _ hx2`. Establish `hs : ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, ((finY D x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s`.

Use `⟨(GlobalTheory.BotFormula.toFinE D).symm ((((u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k), toFinE_symm_mem_OhE _ hx3, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_finY, ← coe_finIdl, ← hu, ← map_natCast (GlobalTheory.BotFormula.toFinE D).symm m, ← map_mul, ← map_one (GlobalTheory.BotFormula.toFinE D).symm, ← map_sub]`. Use `congr 1`. Establish `hmk : (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * k = 1`. Rewrite using `[hk, ← map_natCast (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) m, ← map_mul, mul_inv_cancel₀ hmE, map_one]`.

Rewrite using `[mul_comm, mul_assoc, mul_comm k, hmk, mul_one]`. Establish `hf` using `hc _ hy hs`. Conclude with `Circle.ext (by rw [coe_finChar, hf, Units.val_one, Circle.coe_one])`. Use `show Filter.Tendsto (finChar c) (𝓝 1) (𝓝 (finChar c 1))`. Rewrite using `[map_one]`.

Conclude with `tendsto_nhds_of_eventually_eq (Filter.eventually_of_mem (hV.mem_nhds h1V) key)`.
-/
theorem continuous_finChar {D : D7} {N : ℕ} (c : HeckeU D N) : Continuous (finChar c) := by
  refine continuous_of_continuousAt_one (finChar c) ?_
  obtain ⟨m, hm, hc⟩ := c.cont
  have hcont : Continuous (finIdl D) :=
    Continuous.units_map _ (GlobalTheory.DefU.ClassFin.continuous_finAdEquiv.comp (GlobalTheory.Member.continuous_finPart D))
  set W : Set (FiniteAdeleRing (𝓞 D.host.E) D.host.E) :=
    {z | ∀ w : HeightOneSpectrum (𝓞 D.host.E), z w ∈ w.adicCompletionIntegers D.host.E} with hW
  have hWo : IsOpen W := RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  set k : FiniteAdeleRing (𝓞 D.host.E) D.host.E := algebraMap D.host.E _ (m : D.host.E)⁻¹ with hk
  have h1 : Continuous fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) := Units.continuous_val.comp hcont
  have h2 : Continuous fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) := Units.continuous_coe_inv.comp hcont
  have h3 : Continuous fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k := (h1.sub continuous_const).mul continuous_const
  set V : Set (AE D)ˣ := ((fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩
      (fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩
      (fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k) ⁻¹' W) with hVdef
  have hV : IsOpen V :=
    ((hWo.preimage h1).inter (hWo.preimage h2)).inter (hWo.preimage h3)
  have hzero : (0 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W := fun w => zero_mem _
  have hone : (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W := fun w => one_mem _
  have h1V : (1 : (AE D)ˣ) ∈ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show ((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W
      rw [map_one, Units.val_one]; exact hone
    · show (((finIdl D 1)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W
      rw [map_one, inv_one, Units.val_one]; exact hone
    · show (((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k ∈ W
      rw [map_one, Units.val_one, sub_self, zero_mul]; exact hzero
  have hmE : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ x ∈ V, finChar c x = 1 := by
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    set u := finIdl D x with hu
    have hy : Formalism.MainNotions.StandardLatticesGL3.IntU D (finY D x) := by
      refine ⟨?_, ?_⟩
      · rw [coe_finY, ← coe_finIdl]
        exact toFinE_symm_mem_OhE _ hx1
      · rw [← map_inv, coe_finY, ← coe_finIdl, map_inv]
        exact toFinE_symm_mem_OhE _ hx2
    have hs : ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, ((finY D x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 =
        (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
      refine ⟨(GlobalTheory.BotFormula.toFinE D).symm ((((u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
        FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k), toFinE_symm_mem_OhE _ hx3, ?_⟩
      rw [coe_finY, ← coe_finIdl, ← hu, ← map_natCast (GlobalTheory.BotFormula.toFinE D).symm m, ← map_mul, ← map_one
        (GlobalTheory.BotFormula.toFinE D).symm, ← map_sub]
      congr 1
      have hmk : (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * k = 1 := by
        rw [hk, ← map_natCast (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) m, ← map_mul,
          mul_inv_cancel₀ hmE, map_one]
      rw [mul_comm, mul_assoc, mul_comm k, hmk, mul_one]
    have hf := hc _ hy hs
    exact Circle.ext (by rw [coe_finChar, hf, Units.val_one, Circle.coe_one])
  show Filter.Tendsto (finChar c) (𝓝 1) (𝓝 (finChar c 1))
  rw [map_one]
  exact tendsto_nhds_of_eventually_eq (Filter.eventually_of_mem (hV.mem_nhds h1V) key)

end GlobalTheory.HeckeUChar
