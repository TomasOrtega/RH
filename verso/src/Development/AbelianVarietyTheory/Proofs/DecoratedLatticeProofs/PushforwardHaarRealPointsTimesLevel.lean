import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpenStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainOnto.HaarInf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Simplify using `only [Lev.finE, MonoidHom.comp_apply]`. Rewrite using `[show finHom V x = 1 from hx, map_one]`.
-/
theorem finE_of_mem_ginfC (V : HSp D) {x : GA D V} (hx : x ∈ GinfC V) : Lev.finE V x = 1 := by
  simp only [Lev.finE, MonoidHom.comp_apply]
  rw [show finHom V x = 1 from hx, map_one]

/- English proof (translation)
Use `conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]`. Rewrite using `[map_mul, finE_of_mem_ginfC V (GlobalTheory.AutMult.toInf V g).2, one_mul]`.
-/
theorem finE_toFin (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.AutMult.toFin V g : GA D V) = Lev.finE V g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  rw [map_mul, finE_of_mem_ginfC V (GlobalTheory.AutMult.toInf V g).2, one_mul]

/- English proof (translation)
Rewrite using `[← GlobalTheory.AutMult.toInf_coe x]`. Conclude with `GlobalTheory.AdelicU.proj_ofInf _ _ v _`.
-/
theorem proj_of_mem_ginfC (V : HSp D) (x : GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (x : GA D V) = 1 := by
  rw [← GlobalTheory.AutMult.toInf_coe x]
  exact GlobalTheory.AdelicU.proj_ofInf _ _ v _

/- English proof (translation)
Use `⟨fun h => ?_, fun h => by simpa using GlobalTheory.AutMult.toInf_coe_fin (⟨g, h⟩ : GfC V)⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.AutMult.toInf_mul_toFin g`. Rewrite `e` using `[h, OneMemClass.coe_one, one_mul]`. Conclude with `e ▸ (GlobalTheory.AutMult.toFin V g).2`.
-/
theorem toInf_eq_one_iff (V : HSp D) (g : GA D V) : GlobalTheory.AutMult.toInf V g = 1 ↔ g ∈ GfC V := by
  refine ⟨fun h => ?_, fun h => by simpa using GlobalTheory.AutMult.toInf_coe_fin (⟨g, h⟩ : GfC V)⟩
  have e := GlobalTheory.AutMult.toInf_mul_toFin g
  rw [h, OneMemClass.coe_one, one_mul] at e
  exact e ▸ (GlobalTheory.AutMult.toFin V g).2

/- English proof (translation)
Introduce `D hL c hc j hj s hs`. Take `⟨h1, -, h3, -, -, -⟩` from `hL c hc j hj s hs`. Use `haveI := hs.haar`. Use `set V := s.V`. Use `set K := Lev.levG s.V s.β s.L`.

Set `A : Subgroup (GA D V)` to `(Formalism.L2.DIV.lev D.sp.cm V.gram s.β s.L).comap (Lev.finE V)`. Establish `hAset : (A : Set (GA D V)) = {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}` using `rfl`. Establish `hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K` using `fun g hg => ⟨(GlobalTheory.AutMult.toFin V g).2, Subgroup.mem_comap.2 (by rw [finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩`. Establish `hAopen : IsOpen (A : Set (GA D V))`. Take `⟨U, hU, hUK⟩` from `h1`.

Set `Lf : Subgroup (GfC V)` to `K.subgroupOf (GfC V)`. Establish `hLf : IsOpen (Lf : Set (GfC V))`. Use `Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)` and prove the remaining obligations. Conclude with `(hUK k hk k.2).1`. Establish `e : (A : Set (GA D V)) = GlobalTheory.AutMult.toFin V ⁻¹' (Lf : Set (GfC V))`.

Use extensionality with `g`. Use `⟨fun hg => hfinK g hg, fun hg => ?_⟩` and prove the remaining obligations. Use `Subgroup.mem_comap.1 hg.2` as an intermediate fact. Use `Subgroup.mem_comap.2 ?_` and prove the remaining obligations. Rewrite using `[← finE_toFin]`.

Conclude with `this`. Rewrite using `[e]`. Conclude with `hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)`. Establish `hAint : (A : Set (GA D V)) ⊆ intOff c s`. Introduce `g hg v _`.

Rewrite using `[← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]`. Conclude with `h3 _ (hfinK g hg) v`. Set `I : Subgroup (GA D V)` to `{ carrier := intOff c s mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv) one_mem' := fun v _ => by rw [map_one]; exact one_mem _ inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }`. Establish `hIopen : IsOpen (I : Set (GA D V))` using `Subgroup.isOpen_mono (H₁ := A) hAint hAopen`. Establish `hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V))`.

Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, toInf_eq_one_iff]`. Conclude with `⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩`. Establish `hKc : IsCompact (K : Set (GA D V))` using `GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D V s.Λ hs.selfDual K inf_le_left h3 (by`. Take `⟨U, hU, hUK⟩` from `h1`.

Conclude with `⟨U, hU, fun k hk hk' => (hUK k hk hk').1⟩)`. Establish `hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b` using `fun b => GlobalTheory.AutMult.toInf_coe b`. Establish `hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A` using `fun b => by`. Use `Subgroup.mem_comap.2 ?_` and prove the remaining obligations. Rewrite using `[Subgroup.subtype_apply, finE_of_mem_ginfC V b.2]`.

Conclude with `one_mem _`. Establish `hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure` using `GlobalTheory.T.map_restrict_isHaar_of_open_product_compact (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)`. Use `⟨hIopen.measurableSet, hAopen.measurableSet, hAint, fun g hg => ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩`. Use `⟨_, hHaar, fun f F hf hF => ?_⟩` and prove the remaining obligations.

Establish `hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))` using `(GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable`. Establish `hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g)` using `fun g hg => by conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]`. Conclude with `hF _ _ (hfinK g hg)`. Establish `hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν` using `(integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf`. Use `⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hAset, setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]`.
-/
theorem pushforward_haar_real : ∀ D : D7, LevFacts D → ForStage D fun c _ s => MeasurableSet (intOff c s) ∧ MeasurableSet {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ∧ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ⊆ intOff c s ∧ (∀ g : GA D s.V, Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} s.ν ∧ ∫ g in {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}, F g ∂s.ν = ∫ b, f b ∂mR := by
  intro D hL c hc j hj s hs
  obtain ⟨h1, -, h3, -, -, -⟩ := hL c hc j hj s hs
  haveI := hs.haar
  set V := s.V
  set K := Lev.levG s.V s.β s.L
  let A : Subgroup (GA D V) := (Formalism.L2.DIV.lev D.sp.cm V.gram s.β s.L).comap (Lev.finE V)
  have hAset : (A : Set (GA D V)) = {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} := rfl

  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin V g).2, Subgroup.mem_comap.2 (by rw [finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩

  have hAopen : IsOpen (A : Set (GA D V)) := by
    obtain ⟨U, hU, hUK⟩ := h1
    let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
    have hLf : IsOpen (Lf : Set (GfC V)) := by
      refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
      exact (hUK k hk k.2).1
    have e : (A : Set (GA D V)) = GlobalTheory.AutMult.toFin V ⁻¹' (Lf : Set (GfC V)) := by
      ext g
      refine ⟨fun hg => hfinK g hg, fun hg => ?_⟩
      have := Subgroup.mem_comap.1 hg.2
      refine Subgroup.mem_comap.2 ?_
      rw [← finE_toFin]; exact this
    rw [e]; exact hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)

  have hAint : (A : Set (GA D V)) ⊆ intOff c s := by
    intro g hg v _
    rw [← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]
    exact h3 _ (hfinK g hg) v

  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen

  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D V s.Λ hs.selfDual K inf_le_left h3 (by
      obtain ⟨U, hU, hUK⟩ := h1
      exact ⟨U, hU, fun k hk hk' => (hUK k hk hk').1⟩)
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, finE_of_mem_ginfC V b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.T.map_restrict_isHaar_of_open_product_compact (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨hIopen.measurableSet, hAopen.measurableSet, hAint, fun g hg => ?_, ?_⟩
  · exact ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  refine ⟨_, hHaar, fun f F hf hF => ?_⟩
  have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
    (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
  have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
    conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
    exact hF _ _ (hfinK g hg)
  have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
  refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
  rw [← hAset, setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]

end GlobalTheory.ChainOnto.HaarInf
