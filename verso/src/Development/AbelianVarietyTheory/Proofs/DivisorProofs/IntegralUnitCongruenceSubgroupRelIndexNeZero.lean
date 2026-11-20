import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

namespace GlobalTheory.CMVal.LatEnt

/- English proof (translation)
Introduce `E _ _ N hN`. Use `PicFin.finite_quot (E := E) hN.ne'` as an intermediate fact. Set `U : Subgroup (Af E)ˣ` to `congr (fun _ => 1)`. Set `r : U →* PicFin.intR E ⧸ Ideal.span {(N : PicFin.intR E)}` to `{ toFun := fun u => Ideal.Quotient.mk _ ⟨(u.1 : Af E), fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (u.2 v).1.le⟩ map_one' := map_one (Ideal.Quotient.mk _) map_mul' := fun a b => by rw [← map_mul]; rfl }`. Establish `h1 : r.toHomUnits.ker.FiniteIndex` using `Subgroup.finiteIndex_ker _`.

Establish `h2 : ((congr (radN E N)).subgroupOf U).FiniteIndex`. Use `Subgroup.finiteIndex_of_le (H := r.toHomUnits.ker) fun u hu w => ⟨(u.2 w).1, ?_⟩` and prove the remaining obligations. Establish `h2 : Ideal.Quotient.mk (Ideal.span {(N : PicFin.intR E)}) ⟨(u.1 : Af E), fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (u.2 v).1.le⟩ = Ideal.Quotient.mk _ 1` using `congrArg Units.val (MonoidHom.mem_ker.1 hu)`. Rewrite `h2` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Take `⟨β, hβ⟩` from `h2`.

Establish `h3 : ((u.1 : (Af E)ˣ) : Af E) - 1 = (N : Af E) * β.1` using `congrArg Subtype.val hβ`. Rewrite `h3` using `[← map_natCast (algebraMap E (Af E))]`. Establish `h4 : ((u.1 : (Af E)ˣ) : Af E) w - 1 = algebraMap E (w.adicCompletion E) (N : E) * β.1 w` using `congrArg (fun z : Af E => z w) h3`. Use `show Valued.v (((u.1 : (Af E)ˣ) : Af E) w - 1) ≤ Valued.v (N : w.adicCompletion E)`. Rewrite using `[h4, map_mul, map_natCast]`.

Conclude with `mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (β.2 w))`. Conclude with `h2.1`.
-/
theorem relIndex_congr_radN_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N →
    (congr (radN E N)).relIndex (congr (fun _ => 1)) ≠ 0 := by
  intro E _ _ N hN
  have := PicFin.finite_quot (E := E) hN.ne'
  let U : Subgroup (Af E)ˣ := congr (fun _ => 1)
  let r : U →* PicFin.intR E ⧸ Ideal.span {(N : PicFin.intR E)} :=
    { toFun := fun u => Ideal.Quotient.mk _ ⟨(u.1 : Af E), fun v =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (u.2 v).1.le⟩
      map_one' := map_one (Ideal.Quotient.mk _)
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  have h1 : r.toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have h2 : ((congr (radN E N)).subgroupOf U).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := r.toHomUnits.ker) fun u hu w => ⟨(u.2 w).1, ?_⟩
    have h2 : Ideal.Quotient.mk (Ideal.span {(N : PicFin.intR E)}) ⟨(u.1 : Af E), fun v =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (u.2 v).1.le⟩ =
        Ideal.Quotient.mk _ 1 := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
    obtain ⟨β, hβ⟩ := h2
    have h3 : ((u.1 : (Af E)ˣ) : Af E) - 1 = (N : Af E) * β.1 := congrArg Subtype.val hβ
    rw [← map_natCast (algebraMap E (Af E))] at h3
    have h4 : ((u.1 : (Af E)ˣ) : Af E) w - 1 = algebraMap E (w.adicCompletion E) (N : E) * β.1 w :=
      congrArg (fun z : Af E => z w) h3
    show Valued.v (((u.1 : (Af E)ˣ) : Af E) w - 1) ≤ Valued.v (N : w.adicCompletion E)
    rw [h4, map_mul, map_natCast]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (β.2 w))
  exact h2.1

end GlobalTheory.CMVal.LatEnt
