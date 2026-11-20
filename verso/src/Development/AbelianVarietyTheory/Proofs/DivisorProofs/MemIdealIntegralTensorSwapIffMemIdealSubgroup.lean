import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IdealDict

open GlobalTheory.StdRead.CharVal

variable {D : D7}

/- English proof (translation)
The claim follows from `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective.comp (GlobalTheory.BotFormula.toAfE D).bijective`.
-/
theorem toE_bijective (D : D7) : Function.Bijective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective.comp (GlobalTheory.BotFormula.toAfE D).bijective

/- English proof (translation)
Rewrite using `[← finQ_incA, toE_finQ]`. Both sides reduce to the same expression.
-/
theorem toE_inc (b : 𝓞 D.host.E) :
    toE D (inc D (b : D.host.E)) = (Formalism.L2.DIV.oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  rw [← finQ_incA, toE_finQ]
  rfl

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, t, ht, rfl⟩` from `hy`. Establish `ht'` using `(toE_int_iff t).2 ht`. Establish `h` using `Ideal.mul_mem_right (⟨_, ht'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _ (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)`.

Rewrite using `[RingHom.map_mul, toE_inc]`. Conclude with `⟨_, h⟩`. Consider the case `zero => rw [RingHom.map_zero]`. Conclude with `⟨zero_mem _, Ideal.zero_mem _⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨h1, h2⟩` from `ha`. Take `⟨h3, h4⟩` from `hb`. Rewrite using `[RingHom.map_add]`. Conclude with `⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩`. Consider the case `neg a _ ha`.

Take `⟨h1, h2⟩` from `ha`. Rewrite using `[RingHom.map_neg]`. Conclude with `⟨neg_mem h1, Submodule.neg_mem _ h2⟩`.
-/
theorem inId_of_mem {𝔪 : Ideal (𝓞 D.host.E)} {y : Formalism.MainNotions.StandardLatticesGL3.AE D} (hy : y ∈ hatId D 𝔪) : InId 𝔪 (toE D y) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    have ht' := (toE_int_iff t).2 ht
    have h := Ideal.mul_mem_right (⟨_, ht'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _
      (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)
    rw [RingHom.map_mul, toE_inc]
    exact ⟨_, h⟩
  | zero => rw [RingHom.map_zero]; exact ⟨zero_mem _, Ideal.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    rw [RingHom.map_add]
    exact ⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩
  | neg a _ ha =>
    obtain ⟨h1, h2⟩ := ha
    rw [RingHom.map_neg]
    exact ⟨neg_mem h1, Submodule.neg_mem _ h2⟩

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, rfl⟩` from `hx`. Conclude with `⟨inc D (b : D.host.E), AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩, toE_inc b⟩`. Consider the case `zero => exact ⟨0, zero_mem _, RingHom.map_zero _⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨y, hy, e⟩` from `ha`. Take `⟨z, hz, e'⟩` from `hb`. Use `⟨y + z, add_mem hy hz, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_add, e, e']`.

Conclude with `(AddMemClass.coe_add _ a b).symm`. Consider the case `smul s a _ ha`. Take `⟨y, hy, e⟩` from `ha`. Take `⟨t, ht⟩` from `(toE_bijective D).2 s.1`. Establish `htO : t ∈ OhE D` using `(toE_int_iff t).1 (by rw [ht]; exact s.2)`.

Use `⟨t * y, GlobalTheory.FunObj.StdDatum.mul_mem_hatId htO hy, ?_⟩` and prove the remaining obligations. Establish `h1` using `(toE D).map_mul t y`. Rewrite `h1` using `[e, ht]`. Rewrite using `[smul_eq_mul]`. Conclude with `h1.trans (MulMemClass.coe_mul _ s a).symm`.
-/
theorem exists_of_mem_idS {𝔪 : Ideal (𝓞 D.host.E)} {u : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hu : u ∈ Ideal.map (Formalism.L2.DIV.oToS D.host.F D.host.E) 𝔪) : ∃ y ∈ hatId D 𝔪, toE D y = u.1 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨inc D (b : D.host.E), AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩, toE_inc b⟩
  | zero => exact ⟨0, zero_mem _, RingHom.map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨z, hz, e'⟩ := hb
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [RingHom.map_add, e, e']
    exact (AddMemClass.coe_add _ a b).symm
  | smul s a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨t, ht⟩ := (toE_bijective D).2 s.1
    have htO : t ∈ OhE D := (toE_int_iff t).1 (by rw [ht]; exact s.2)
    refine ⟨t * y, GlobalTheory.FunObj.StdDatum.mul_mem_hatId htO hy, ?_⟩
    have h1 := (toE D).map_mul t y
    rw [e, ht] at h1
    rw [smul_eq_mul]
    exact h1.trans (MulMemClass.coe_mul _ s a).symm

/- English proof (translation)
Introduce `D 𝔪 y`. Use `⟨fun ⟨h, hm⟩ => ?_, inId_of_mem⟩` and prove the remaining obligations. Take `⟨z, hz, e⟩` from `exists_of_mem_idS hm`. Rewrite using `[← (toE_bijective D).1 e]` and apply the resulting hypothesis.
-/
theorem inId_toE_iff : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D), InId 𝔪 (toE D y) ↔ y ∈ hatId D 𝔪 := by
  intro D 𝔪 y
  refine ⟨fun ⟨h, hm⟩ => ?_, inId_of_mem⟩
  obtain ⟨z, hz, e⟩ := exists_of_mem_idS hm
  rwa [← (toE_bijective D).1 e]

end GlobalTheory.StdRead.IdealDict

end
