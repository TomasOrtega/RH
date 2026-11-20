import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NVolAllOf

noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

/- English proof (translation)
Establish `hf : AEMeasurable (fun x : α => Measure.map (Prod.mk x) ν) μ`. Assume the negation of the conclusion as `hf`. Apply `h0` to reduce the goal to its premises. Rewrite using `[Measure.prod, Measure.bind, Measure.map_of_not_aemeasurable hf, Measure.join_zero]`. Rewrite using `[Measure.prod, Measure.bind_apply (hs.prod ht) hf]`.

Establish `key : ∀ x, Measure.map (Prod.mk x) ν (s ×ˢ t) = s.indicator (fun _ => ν t) x`. Introduce `x`. Rewrite using `[Measure.map_apply measurable_prodMk_left (hs.prod ht)]`. Distinguish the cases in `hx : x ∈ s`. Simplify using `[hx, Set.mk_preimage_prod_right hx]`.

Simplify using `[hx, Set.mk_preimage_prod_right_eq_empty hx]`. Repeatedly rewrite using `[key]`. Rewrite using `[lintegral_indicator_const hs, mul_comm]`.
-/
theorem prod_rect_of_ne_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) (h0 : μ.prod ν ≠ 0) {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  have hf : AEMeasurable (fun x : α => Measure.map (Prod.mk x) ν) μ := by
    by_contra hf
    apply h0
    rw [Measure.prod, Measure.bind, Measure.map_of_not_aemeasurable hf, Measure.join_zero]
  rw [Measure.prod, Measure.bind_apply (hs.prod ht) hf]
  have key : ∀ x, Measure.map (Prod.mk x) ν (s ×ˢ t) = s.indicator (fun _ => ν t) x := by
    intro x
    rw [Measure.map_apply measurable_prodMk_left (hs.prod ht)]
    by_cases hx : x ∈ s
    · simp [hx, Set.mk_preimage_prod_right hx]
    · simp [hx, Set.mk_preimage_prod_right_eq_empty hx]
  simp_rw [key]
  rw [lintegral_indicator_const hs, mul_comm]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Rewrite using `[tauF_tmul]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem tauF_eq_comm {D : D7} (X : HidaSetting D) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    tauF X.B.I y = Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E
      (tensMap (E := X.B.I.E) (sndA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Establish `hbr` using `((toHA_isBridge X.B.I hb) (s, 1)).2`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Establish `e` using `congrFun (congrFun hbr i) j`.

Simplify using `only [ofHAFin, Matrix.map_apply] at e`. Rewrite `e` using `[tauF_eq_comm]`. Establish `e2` using `congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E).symm e`. Rewrite `e2` using `[AlgEquiv.symm_apply_apply]`. Use `show tensMap (E := X.B.I.E) (sndA X.B.I.F) _ = _`.

Rewrite using `[← e2]`. Use `show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j`. Simplify using `only [Formalism.MainNotions.S.AutInst.fmat, OneMemClass.coe_one, Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem toHA_fin_one {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, 1))).2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) (s, 1)).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have e2 := congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E).symm e
  rw [AlgEquiv.symm_apply_apply] at e2
  show tensMap (E := X.B.I.E) (sndA X.B.I.F) _ = _
  rw [← e2]
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j
  simp only [Formalism.MainNotions.S.AutInst.fmat, OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

section Split

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

/- English proof (translation)
Establish `hbr` using `((toHA_isBridge X.B.I hb) p).2`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Establish `e` using `congrFun (congrFun hbr i) j`.

Simplify using `only [ofHAFin, Matrix.map_apply] at e`. Rewrite `e` using `[tauF_eq_comm]`. Establish `h2 : tensMap (E` using `X.B.I.E) (sndA X.B.I.F) (hmat X.B.I (toHA X.B.I hb p) i j) = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j := by`. Use `congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J => (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h` as an intermediate fact. Conclude with `this`.

Rewrite `e` using `[h2]`. Rewrite `e` using `[Formalism.MainNotions.S.AutInst.fmat]`. Use `show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i j`. Rewrite using `[e, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eq_one_of_toHA_fin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : X.B.I.GA)
    (h : (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p)).2 = 1) : p.2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) p).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have h2 : tensMap (E := X.B.I.E) (sndA X.B.I.F) (hmat X.B.I (toHA X.B.I hb p) i j) =
      (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j := by
    have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
      (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
    exact this
  rw [h2] at e
  rw [Formalism.MainNotions.S.AutInst.fmat] at e
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i j
  rw [e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `Prod.ext rfl (toHA_fin_one X hb s)`.
-/
theorem split_unitary_infinite_one (s : X.B.I.Ginf) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, 1)) = (X.toInf hb s, 1) :=
  Prod.ext rfl (toHA_fin_one X hb s)

/- English proof (translation)
Introduce `s t hst`. Take `⟨e, he⟩` from `hS X.B.I.cm.sig X.B.I.J`. Establish `h1 : e (toHA X.B.I hb (s, 1)) = e (toHA X.B.I hb (t, 1))`. Rewrite using `[he, split_unitary_infinite_one, split_unitary_infinite_one, hst]`. Establish `h2` using `(toHA X.B.I hb).injective (e.injective h1)`.

Conclude with `congrArg Prod.fst h2`.
-/
theorem toInf_injective (hS : SplitIso) : Function.Injective (X.toInf hb) := by
  intro s t hst
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have h1 : e (toHA X.B.I hb (s, 1)) = e (toHA X.B.I hb (t, 1)) := by
    rw [he, split_unitary_infinite_one, split_unitary_infinite_one, hst]
  have h2 := (toHA X.B.I hb).injective (e.injective h1)
  exact congrArg Prod.fst h2

/- English proof (translation)
Take `⟨e, he⟩` from `hS X.B.I.cm.sig X.B.I.J`. Establish `hc : Continuous (splitA X.B.I.cm.sig X.B.I.J)` using `by rw [← he]; exact e.continuous_toFun`. Conclude with `continuous_fst.comp (hc.comp ((toHA X.B.I hb).continuous_toFun.comp (continuous_id.prodMk continuous_const)))`.
-/
theorem continuous_toInf_of (hS : SplitIso) : Continuous (X.toInf hb) := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have hc : Continuous (splitA X.B.I.cm.sig X.B.I.J) := by rw [← he]; exact e.continuous_toFun
  exact continuous_fst.comp (hc.comp ((toHA X.B.I hb).continuous_toFun.comp
    (continuous_id.prodMk continuous_const)))

/- English proof (translation)
Use `haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩`. Conclude with `(continuous_toInf_of X hb hS).measurable`.
-/
theorem measurable_toInf_of (hS : SplitIso) : Measurable (X.toInf hb) := by
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (continuous_toInf_of X hb hS).measurable

/- English proof (translation)
Take `⟨e, he⟩` from `hS X.B.I.cm.sig X.B.I.J`. Set `Φ : X.B.I.GA ≃ₜ* (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J × HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)` to `(toHA X.B.I hb).trans e`. Establish `hΦ : ∀ s, Φ (s, 1) = (X.toInf hb s, 1)` using `fun s => by show e (toHA X.B.I hb (s, 1)) = _`. Rewrite using `[he]`. Conclude with `split_unitary_infinite_one X hb s`.

Set `ψ : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → X.B.I.GA` to `fun y => Φ.symm (y, 1)`. Establish `hψc : Continuous ψ` using `Φ.symm.continuous_toFun.comp (continuous_id.prodMk continuous_const)`. Establish `hset : X.toInf hb '' FdN = (fun y => (ψ y).1) ⁻¹' FdN`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hs, rfl⟩ show (Φ.symm (X.toInf hb s, 1)).1 ∈ FdN`. Rewrite using `[← hΦ, Φ.symm_apply_apply]`. Conclude with `hs`. Introduce `h1`. Establish `h2 : (ψ y).2 = 1`.

Apply `eq_one_of_toHA_fin X hb` to reduce the goal to its premises. Establish `h3 : e (toHA X.B.I hb (ψ y)) = (y, 1)` using `Φ.apply_symm_apply _`. Rewrite `h3` using `[he]`. Rewrite using `[h3]`. Use `⟨(ψ y).1, h1, ?_⟩` and prove the remaining obligations.

Establish `hp : ψ y = ((ψ y).1, 1)` using `Prod.ext rfl h2`. Use `congrArg Φ hp` as an intermediate fact. Rewrite `this` using `[show Φ (ψ y) = (y, 1) from Φ.apply_symm_apply _, hΦ]`. Conclude with `(congrArg Prod.fst this).symm`. Use `haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩`.

Rewrite using `[hset]`. Conclude with `(continuous_fst.comp hψc).measurable hF`.
-/
theorem measurableSet_image_toInf (hS : SplitIso) {FdN : Set X.B.I.Ginf} (hF : MeasurableSet FdN) :
    MeasurableSet (X.toInf hb '' FdN) := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  let Φ : X.B.I.GA ≃ₜ* (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J × HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    (toHA X.B.I hb).trans e
  have hΦ : ∀ s, Φ (s, 1) = (X.toInf hb s, 1) := fun s => by
    show e (toHA X.B.I hb (s, 1)) = _
    rw [he]
    exact split_unitary_infinite_one X hb s
  let ψ : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → X.B.I.GA := fun y => Φ.symm (y, 1)
  have hψc : Continuous ψ := Φ.symm.continuous_toFun.comp (continuous_id.prodMk continuous_const)
  have hset : X.toInf hb '' FdN = (fun y => (ψ y).1) ⁻¹' FdN := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      show (Φ.symm (X.toInf hb s, 1)).1 ∈ FdN
      rw [← hΦ, Φ.symm_apply_apply]
      exact hs
    · intro h1
      have h2 : (ψ y).2 = 1 := by
        apply eq_one_of_toHA_fin X hb
        have h3 : e (toHA X.B.I hb (ψ y)) = (y, 1) := Φ.apply_symm_apply _
        rw [he] at h3
        rw [h3]
      refine ⟨(ψ y).1, h1, ?_⟩
      have hp : ψ y = ((ψ y).1, 1) := Prod.ext rfl h2
      have := congrArg Φ hp
      rw [show Φ (ψ y) = (y, 1) from Φ.apply_symm_apply _, hΦ] at this
      exact (congrArg Prod.fst this).symm
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  rw [hset]
  exact (continuous_fst.comp hψc).measurable hF

end Split

/- English proof (translation)
Introduce `hS D X hb u FdN hT hTie hF`. Use `haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩`. Use `haveI : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩`. Use `haveI : BorelSpace (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩`. Take `⟨e, he⟩` from `hS X.B.I.cm.sig X.B.I.J`.

Establish `hc : Continuous (splitA X.B.I.cm.sig X.B.I.J)` using `by rw [← he]; exact e.continuous_toFun`. Establish `hm : Measurable (splitA X.B.I.cm.sig X.B.I.J)` using `(continuous_fst.comp hc).measurable.prodMk (continuous_snd.comp hc).measurable`. Establish `hTm : MeasurableSet (X.toInf hb '' FdN)` using `measurableSet_image_toInf X hb hS hF.1`. Establish `hKm : MeasurableSet (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))` using `(hKo X).2.measurableSet`. Establish `hRm : MeasurableSet ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))` using `hTm.prod hKm`.

Establish `hFd : FdA X hb u FdN = Subtype.val ⁻¹' (splitA X.B.I.cm.sig X.B.I.J ⁻¹' ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))))`. Use extensionality with `n`. Simplify using `only [FdA, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, h1, h2⟩`.

Conclude with `⟨⟨s, hs, h1.symm⟩, h2⟩`. Introduce and unpack `⟨⟨s, hs, h1⟩, h2⟩`. Conclude with `⟨s, hs, h1.symm, h2⟩`. Establish `hN` using `hT.2.2.2.2.2.2.2.2.2.1`. Establish `hHaar : (X.measW u).μN.IsHaarMeasure` using `hT.2.2.2.1`.

Establish `h0 : (amb (X.measW u).μNinf).prod (amb (X.measW u).μNf) ≠ 0`. Rewrite using `[← hN]`. Introduce `h`. Establish `h'` using `congrArg (fun μ => μ Set.univ) h`. Simplify using `only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Measure.coe_zero, Pi.zero_apply] at h'`.

Conclude with `(isOpen_univ.measure_ne_zero (X.measW u).μN Set.univ_nonempty) h'`. Rewrite using `[hFd]`. Use `erw [← Measure.map_apply measurable_subtype_coe (hm hRm)]`. Rewrite using `[← Measure.map_apply hm hRm]`. Express the relevant statement in the definitionally equal form `((amb (X.measW u).μN).map (splitA X.B.I.cm.sig X.B.I.J)) _ = _`.

Rewrite using `[hN, prod_rect_of_ne_zero _ _ h0 hTm hKm, (hTie.2.2.2 u).1, Measure.map_apply (measurable_toInf_of X hb hS) hTm, Set.preimage_image_eq _ (toInf_injective X hb hS), Measure.map_apply measurable_subtype_coe hKm]`.
-/
theorem elliptic_centralizer_quotient_compact (hKo : KCompactOpen) : N4 := by
  intro hS D X hb u FdN hT hTie hF
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : BorelSpace (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have hc : Continuous (splitA X.B.I.cm.sig X.B.I.J) := by rw [← he]; exact e.continuous_toFun
  have hm : Measurable (splitA X.B.I.cm.sig X.B.I.J) :=
    (continuous_fst.comp hc).measurable.prodMk (continuous_snd.comp hc).measurable
  have hTm : MeasurableSet (X.toInf hb '' FdN) := measurableSet_image_toInf X hb hS hF.1
  have hKm : MeasurableSet (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := (hKo X).2.measurableSet
  have hRm : MeasurableSet ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) :=
    hTm.prod hKm
  have hFd : FdA X hb u FdN = Subtype.val ⁻¹' (splitA X.B.I.cm.sig X.B.I.J ⁻¹'
      ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))) := by
    ext n
    simp only [FdA, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_image]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨⟨s, hs, h1.symm⟩, h2⟩
    · rintro ⟨⟨s, hs, h1⟩, h2⟩
      exact ⟨s, hs, h1.symm, h2⟩
  have hN := hT.2.2.2.2.2.2.2.2.2.1
  have hHaar : (X.measW u).μN.IsHaarMeasure := hT.2.2.2.1
  have h0 : (amb (X.measW u).μNinf).prod (amb (X.measW u).μNf) ≠ 0 := by
    rw [← hN]
    intro h
    have h' := congrArg (fun μ => μ Set.univ) h
    simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
      Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Measure.coe_zero, Pi.zero_apply] at h'
    exact (isOpen_univ.measure_ne_zero (X.measW u).μN Set.univ_nonempty) h'
  rw [hFd]
  erw [← Measure.map_apply measurable_subtype_coe (hm hRm)]
  rw [← Measure.map_apply hm hRm]
  change ((amb (X.measW u).μN).map (splitA X.B.I.cm.sig X.B.I.J)) _ = _
  rw [hN, prod_rect_of_ne_zero _ _ h0 hTm hKm, (hTie.2.2.2 u).1,
    Measure.map_apply (measurable_toInf_of X hb hS) hTm, Set.preimage_image_eq _ (toInf_injective X hb hS),
    Measure.map_apply measurable_subtype_coe hKm]

end MassDataMassesW
