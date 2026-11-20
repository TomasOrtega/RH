import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmV

noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

/- English proof (translation)
Take `⟨hlc, hsc, ht2, htg⟩` from `hN`. Introduce `μN hμN h hh f hf`. Take `⟨μ0, hμ0, hinv⟩` from `hex h hh`. Rewrite using `[Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure, hinv f hf]`.
-/
theorem conjInv_of_one {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by
  obtain ⟨hlc, hsc, ht2, htg⟩ := hN
  intro μN hμN h hh f hf
  obtain ⟨μ0, hμ0, hinv⟩ := hex h hh
  rw [Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure,
    hinv f hf]

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

/- English proof (translation)
Introduce `hJ hσσ r P T hP`. Establish `hsc : SecondCountableTopology (Af F)` using `PI.LevelKSplit.W.SC.finite_adeles_secondCountable F`. Establish `hL : LCSC (HA (Af F) σ J)` using `PI.LevelKSplit.W.ExS.lcsc_HAf hsc`. Establish `: BorelSpace (HA (Af F) σ J)` using `⟨rfl⟩`. Establish `: SecondCountableTopology (HA (Af F) σ J)` using `hL.2.1`.

Take `⟨-, cN, -⟩` from `PI.LevelKSplit.W.ExC.closed_SNH hJ hσσ P T hP`. Take `⟨lN, -⟩` from `subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ _ hL cN inferInstance inferInstance`. Use `conjInv_of_one _ _ lN ?_` and prove the remaining obligations. Introduce `h hh`. Take `⟨A, Z, Ψ, cA, cZ, hleft, hconj⟩` from `hC hJ hσσ r P T hP`.

Take `⟨⟨lcA, scA, t2A, tgA⟩, -⟩` from `subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ A hL cA inferInstance inferInstance`. Take `⟨⟨lcZ, scZ, t2Z, tgZ⟩, -⟩` from `subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ Z hL cZ inferInstance inferInstance`. Take `⟨lcN, scN, t2N, tgN⟩` from `lN`. Establish `: BorelSpace A` using `Subtype.borelSpace _`. Establish `: BorelSpace Z` using `Subtype.borelSpace _`.

Establish `: BorelSpace (Nsub (Af F) σ J P)` using `Subtype.borelSpace _`. Establish `: SecondCountableTopology (Af F ⊗[F] E)` using `sc_tens`. Establish `: BorelSpace (Af F ⊗[F] E)` using `⟨rfl⟩`. Establish `: BorelSpace (Fin M → Af F ⊗[F] E)` using `Pi.borelSpace`. Establish `H` using `SemiA.datR_hyp (R := Af F) hσσ hJ hP`.

Establish `cW : IsClosed ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E))`. Establish `e1 : ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E)) = {v | DatL.pL (SemiA.datR (Af F) σ J P T) v = v}`. Use extensionality with `v`. Conclude with `mem_Wp_iff H v`. Rewrite using `[e1]`.

Conclude with `isClosed_eq (LinearMap.continuous_on_pi _) continuous_id`. Establish `: LocallyCompactSpace (Wp (Af F) σ J P)` using `cW.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology (Wp (Af F) σ J P)` using `TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val`. Establish `: BorelSpace (Wp (Af F) σ J P)` using `Subtype.borelSpace _`. Establish `: BorelSpace (Fin r → Wp (Af F) σ J P)` using `Pi.borelSpace`.

Establish `: BorelSpace ((Fin r → Wp (Af F) σ J P) × Z)` using `Prod.borelSpace`. Establish `: BorelSpace (A × ((Fin r → Wp (Af F) σ J P) × Z))` using `Prod.borelSpace`. Set `μA : Measure A` to `Measure.haar`. Set `μZ : Measure Z` to `Measure.haar`. Set `μW : Measure (Wp (Af F) σ J P)` to `Measure.addHaar`.

Set `μQ : Measure (Fin r → Wp (Af F) σ J P)` to `Measure.pi fun _ => μW`. Set `ρ : Measure (A × ((Fin r → Wp (Af F) σ J P) × Z))` to `μA.prod (μQ.prod μZ)`. Establish `hΨm : Measurable Ψ` using `Ψ.continuous.measurable`. Use `⟨ρ.map Ψ, ?_, ?_⟩` and prove the remaining obligations. Establish `hli : (ρ.map Ψ).IsMulLeftInvariant`.

Use `⟨fun n0 => ?_⟩` and prove the remaining obligations. Take `⟨a0, t, c, ht, hc, hform⟩` from `hleft n0`. Establish `hcomm : (fun n => n0 * n) ∘ Ψ = Ψ ∘ (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) => (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2)))`. Use function extensionality and compare the values at `⟨u, y, z⟩`. Conclude with `hform u y z`.

Establish `hinner : ∀ u : A, MeasurePreserving (fun q : (Fin r → Wp (Af F) σ J P) × Z => (q.1 + t u, c (u, q.1) * q.2)) (μQ.prod μZ) (μQ.prod μZ)`. Introduce `u`. Use `(measurePreserving_add_right μQ (t u)).skew_product (g := fun y z => c (u, y) * z) ?_ (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μZ (c (u, y)))` and prove the remaining obligations. Conclude with `(show Continuous fun q : (Fin r → Wp (Af F) σ J P) × Z => c (u, q.1) * q.2 from (hc.comp (continuous_const.prodMk continuous_fst)).mul continuous_snd).measurable`. Establish `hgm : Continuous fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) => (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2)` using `(continuous_snd.fst.add (ht.comp continuous_fst)).prodMk ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).mul continuous_snd.snd)`.

Establish `hT : MeasurePreserving (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) => (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) ρ ρ` using `(measurePreserving_mul_left μA a0).skew_product (g := fun (u : A) (q : (Fin r → Wp (Af F) σ J P) × Z) => (q.1 + t u, c (u, q.1) * q.2)) hgm.measurable (Filter.Eventually.of_forall fun u => (hinner u).map_eq)`. Rewrite using `[Measure.map_map (measurable_const_mul n0) hΨm, hcomm, ← Measure.map_map hΨm hT.measurable, hT.map_eq]`. Establish `hfc : IsFiniteMeasureOnCompacts (ρ.map Ψ)` using `Measure.IsFiniteMeasureOnCompacts.map ρ Ψ`. Establish `hop : (ρ.map Ψ).IsOpenPosMeasure` using `Ψ.continuous.isOpenPosMeasure_map Ψ.surjective`. Use `hfc` as an intermediate fact.

Use `hli` as an intermediate fact. Use `hop` as an intermediate fact. Conclude with `Measure.IsHaarMeasure.mk`. Introduce `f hf`. Establish `hF : Measurable fun n : Nsub (Af F) σ J P => f (h * (n : HA (Af F) σ J) * h⁻¹)` using `hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable`.

Establish `hF0 : Measurable fun n : Nsub (Af F) σ J P => f (n : HA (Af F) σ J)` using `hf.comp continuous_subtype_val.measurable`. Establish `hlinm : Measurable (linWp hh)` using `(((LinearMap.continuous_on_pi (lin (Af F) σ J h)).comp continuous_subtype_val).subtype_mk _).measurable`. Set `Lq : (Fin r → Wp (Af F) σ J P) → (Fin r → Wp (Af F) σ J P)` to `fun y a => linWp hh (y a)`. Establish `hLq : MeasurePreserving Lq μQ μQ` using `measurePreserving_pi (fun _ => μW) (fun _ => μW) (fun _ => ⟨hlinm, wp_map hσσ hJ hP hV hh μW inferInstance⟩)`. Establish `hT : MeasurePreserving (Prod.map id (Prod.map Lq id)) ρ ρ` using `(MeasurePreserving.id μA).prod (hLq.prod (MeasurePreserving.id μZ))`.

Rewrite using `[lintegral_map hF hΨm, lintegral_map hF0 hΨm]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `⟨u, y, z⟩`. Take `⟨y', hy', he⟩` from `hconj h hh u y z`.

Establish `e2 : y' = Lq y` using `funext fun a => Subtype.ext (hy' a)`. Use `show f (h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹) = f (Ψ (u, Lq y, z) : HA (Af F) σ J)`. Rewrite using `[he, e2]`. Use `_ = ∫⁻ p, f (Ψ p : HA (Af F) σ J) ∂ρ := hT.lintegral_comp (show Measurable fun p => f (Ψ p : HA (Af F) σ J) from hf.comp (continuous_subtype_val.comp Ψ.continuous).measurable)`.
-/
theorem conjNH_of (hC : NCoord F E σ M J) (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) :
    PI.LevelKSplit.W.ExS.ConjNH F E σ M J := by
  intro hJ hσσ r P T hP
  have hsc : SecondCountableTopology (Af F) := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  have hL : LCSC (HA (Af F) σ J) := PI.LevelKSplit.W.ExS.lcsc_HAf hsc
  have : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  have : SecondCountableTopology (HA (Af F) σ J) := hL.2.1
  obtain ⟨-, cN, -⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hσσ P T hP
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ _ hL cN inferInstance inferInstance
  refine conjInv_of_one _ _ lN ?_
  intro h hh
  obtain ⟨A, Z, Ψ, cA, cZ, hleft, hconj⟩ := hC hJ hσσ r P T hP
  obtain ⟨⟨lcA, scA, t2A, tgA⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ A hL cA inferInstance inferInstance
  obtain ⟨⟨lcZ, scZ, t2Z, tgZ⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ Z hL cZ inferInstance inferInstance
  obtain ⟨lcN, scN, t2N, tgN⟩ := lN
  have : BorelSpace A := Subtype.borelSpace _
  have : BorelSpace Z := Subtype.borelSpace _
  have : BorelSpace (Nsub (Af F) σ J P) := Subtype.borelSpace _
  have : SecondCountableTopology (Af F ⊗[F] E) := sc_tens
  have : BorelSpace (Af F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fin M → Af F ⊗[F] E) := Pi.borelSpace
  have H := SemiA.datR_hyp (R := Af F) hσσ hJ hP
  have cW : IsClosed ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) :
      Set (Fin M → Af F ⊗[F] E)) := by
    have e1 : ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E)) =
        {v | DatL.pL (SemiA.datR (Af F) σ J P T) v = v} := by
      ext v
      exact mem_Wp_iff H v
    rw [e1]
    exact isClosed_eq (LinearMap.continuous_on_pi _) continuous_id
  have : LocallyCompactSpace (Wp (Af F) σ J P) := cW.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (Wp (Af F) σ J P) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  have : BorelSpace (Wp (Af F) σ J P) := Subtype.borelSpace _
  have : BorelSpace (Fin r → Wp (Af F) σ J P) := Pi.borelSpace
  have : BorelSpace ((Fin r → Wp (Af F) σ J P) × Z) := Prod.borelSpace
  have : BorelSpace (A × ((Fin r → Wp (Af F) σ J P) × Z)) := Prod.borelSpace
  let μA : Measure A := Measure.haar
  let μZ : Measure Z := Measure.haar
  let μW : Measure (Wp (Af F) σ J P) := Measure.addHaar
  let μQ : Measure (Fin r → Wp (Af F) σ J P) := Measure.pi fun _ => μW
  let ρ : Measure (A × ((Fin r → Wp (Af F) σ J P) × Z)) := μA.prod (μQ.prod μZ)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  refine ⟨ρ.map Ψ, ?_, ?_⟩
  · have hli : (ρ.map Ψ).IsMulLeftInvariant := by
      refine ⟨fun n0 => ?_⟩
      obtain ⟨a0, t, c, ht, hc, hform⟩ := hleft n0
      have hcomm : (fun n => n0 * n) ∘ Ψ = Ψ ∘ (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) := by
        funext ⟨u, y, z⟩
        exact hform u y z
      have hinner : ∀ u : A, MeasurePreserving
          (fun q : (Fin r → Wp (Af F) σ J P) × Z => (q.1 + t u, c (u, q.1) * q.2))
          (μQ.prod μZ) (μQ.prod μZ) := by
        intro u
        refine (measurePreserving_add_right μQ (t u)).skew_product (g := fun y z => c (u, y) * z)
          ?_ (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μZ (c (u, y)))
        exact (show Continuous fun q : (Fin r → Wp (Af F) σ J P) × Z => c (u, q.1) * q.2 from
          (hc.comp (continuous_const.prodMk continuous_fst)).mul continuous_snd).measurable
      have hgm : Continuous fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2) :=
        (continuous_snd.fst.add (ht.comp continuous_fst)).prodMk
          ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).mul continuous_snd.snd)
      have hT : MeasurePreserving (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) ρ ρ :=
        (measurePreserving_mul_left μA a0).skew_product
          (g := fun (u : A) (q : (Fin r → Wp (Af F) σ J P) × Z) => (q.1 + t u, c (u, q.1) * q.2)) hgm.measurable
          (Filter.Eventually.of_forall fun u => (hinner u).map_eq)
      rw [Measure.map_map (measurable_const_mul n0) hΨm, hcomm, ← Measure.map_map hΨm hT.measurable,
        hT.map_eq]
    have hfc : IsFiniteMeasureOnCompacts (ρ.map Ψ) := Measure.IsFiniteMeasureOnCompacts.map ρ Ψ
    have hop : (ρ.map Ψ).IsOpenPosMeasure := Ψ.continuous.isOpenPosMeasure_map Ψ.surjective
    have := hfc
    have := hli
    have := hop
    exact Measure.IsHaarMeasure.mk
  · intro f hf
    have hF : Measurable fun n : Nsub (Af F) σ J P => f (h * (n : HA (Af F) σ J) * h⁻¹) :=
      hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF0 : Measurable fun n : Nsub (Af F) σ J P => f (n : HA (Af F) σ J) :=
      hf.comp continuous_subtype_val.measurable
    have hlinm : Measurable (linWp hh) :=
      (((LinearMap.continuous_on_pi (lin (Af F) σ J h)).comp continuous_subtype_val).subtype_mk
        _).measurable
    let Lq : (Fin r → Wp (Af F) σ J P) → (Fin r → Wp (Af F) σ J P) := fun y a => linWp hh (y a)
    have hLq : MeasurePreserving Lq μQ μQ :=
      measurePreserving_pi (fun _ => μW) (fun _ => μW)
        (fun _ => ⟨hlinm, wp_map hσσ hJ hP hV hh μW inferInstance⟩)
    have hT : MeasurePreserving (Prod.map id (Prod.map Lq id)) ρ ρ :=
      (MeasurePreserving.id μA).prod (hLq.prod (MeasurePreserving.id μZ))
    rw [lintegral_map hF hΨm, lintegral_map hF0 hΨm]
    calc ∫⁻ p, f (h * (Ψ p : HA (Af F) σ J) * h⁻¹) ∂ρ
        = ∫⁻ p, f (Ψ (Prod.map id (Prod.map Lq id) p) : HA (Af F) σ J) ∂ρ := by
          congr 1
          funext ⟨u, y, z⟩
          obtain ⟨y', hy', he⟩ := hconj h hh u y z
          have e2 : y' = Lq y := funext fun a => Subtype.ext (hy' a)
          show f (h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹) = f (Ψ (u, Lq y, z) : HA (Af F) σ J)
          rw [he, e2]
      _ = ∫⁻ p, f (Ψ p : HA (Af F) σ J) ∂ρ :=
          hT.lintegral_comp (show Measurable fun p => f (Ψ p : HA (Af F) σ J) from
            hf.comp (continuous_subtype_val.comp Ψ.continuous).measurable)

/- English proof (translation)
Introduce `hC hV` and use `conjNH_of hC hV`.
-/
theorem normal_conjugation_hypothesis : NCAsm F E σ M J := fun hC hV => conjNH_of hC hV

end Af

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`. Conclude with `normal_conjugation_hypothesis`.
-/
theorem normal_conjugation_all : NCAsmAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact normal_conjugation_hypothesis

end PI.LevelKSplit.W.NCA
