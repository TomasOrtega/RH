import Mathlib
open MeasureTheory

namespace GlobalTheory.MultilinFubini

/- English proof (translation)
Establish `key : ∀ s : Finset ι, AEStronglyMeasurable (fun x (i : ι) => if i ∈ s then f i x else 0) ν`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.notMem_empty, if_false]`. Conclude with `aestronglyMeasurable_const`.

Consider the case `insert a s ha ih`. Establish `hc : Continuous (fun p : E a × (∀ i, E i) => Function.update p.2 a p.1)` using `continuous_snd.update a continuous_fst`. Use `(hc.comp_aestronglyMeasurable ((hf a).prodMk ih)).congr (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = a`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hi, hi]`. Simplify using `using key Finset.univ`.
-/
theorem aestronglyMeasurable_pi_of_forall {α : Type*} {m0 : MeasurableSpace α} {ν : Measure α}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : ∀ i, α → E i} (hf : ∀ i, AEStronglyMeasurable (f i) ν) :
    AEStronglyMeasurable (fun x i => f i x) ν := by
  have key : ∀ s : Finset ι,
      AEStronglyMeasurable (fun x (i : ι) => if i ∈ s then f i x else 0) ν := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, if_false]; exact aestronglyMeasurable_const
    | insert a s ha ih =>
      have hc : Continuous (fun p : E a × (∀ i, E i) => Function.update p.2 a p.1) :=
        continuous_snd.update a continuous_fst
      refine (hc.comp_aestronglyMeasurable ((hf a).prodMk ih)).congr (ae_of_all _ fun x => ?_)
      funext i
      by_cases hi : i = a
      · subst hi; simp
      · simp [Function.update_of_ne hi, hi]
  simpa using key Finset.univ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

def vecOn (g : ∀ i, X i → E i) (s : Finset ι) (m : ∀ i, E i) (x : ∀ i : s, X i) : ∀ i, E i :=
  fun i => if h : i ∈ s then g i (x ⟨i, h⟩) else m i

/- English proof (translation)
Establish `hmeas : AEStronglyMeasurable (fun x => vecOn g s m x) (Measure.pi fun i : s => μ i)`. Use `aestronglyMeasurable_pi_of_forall (f := fun i x => vecOn g s m x i) fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i ∈ s`. Simplify using `only [vecOn, dif_pos hi]`. Conclude with `(hg i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun j : s => μ j) ⟨i, hi⟩)`.

Simplify using `only [vecOn, dif_neg hi]`. Conclude with `aestronglyMeasurable_const`. Establish `hdom : Integrable (fun x : ∀ j : s, X j => ‖Φ‖ * ((∏ j : s, ‖g j (x j)‖) * ∏ i ∈ sᶜ, ‖m i‖)) (Measure.pi fun i : s => μ i)` using `((Integrable.fintype_prod_dep (f := fun (j : s) (y : X j) => ‖g j y‖) fun j => (hg j).norm).mul_const _).const_mul _`. Use `hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Use `(Φ.le_opNorm _).trans (le_of_eq ?_)` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[← Finset.prod_mul_prod_compl s]`. Use `congr 1`. Rewrite using `[← Finset.prod_coe_sort s]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `[vecOn, j.2]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `[vecOn, Finset.mem_compl.1 hi]`.
-/
theorem integrable_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) (m : ∀ i, E i) :
    Integrable (fun x => Φ (vecOn g s m x)) (Measure.pi fun i : s => μ i) := by
  have hmeas : AEStronglyMeasurable (fun x => vecOn g s m x) (Measure.pi fun i : s => μ i) := by
    refine aestronglyMeasurable_pi_of_forall (f := fun i x => vecOn g s m x i) fun i => ?_
    by_cases hi : i ∈ s
    · simp only [vecOn, dif_pos hi]
      exact (hg i).1.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun j : s => μ j) ⟨i, hi⟩)
    · simp only [vecOn, dif_neg hi]; exact aestronglyMeasurable_const
  have hdom : Integrable (fun x : ∀ j : s, X j => ‖Φ‖ * ((∏ j : s, ‖g j (x j)‖) * ∏ i ∈ sᶜ, ‖m i‖))
      (Measure.pi fun i : s => μ i) :=
    ((Integrable.fintype_prod_dep (f := fun (j : s) (y : X j) => ‖g j y‖)
      fun j => (hg j).norm).mul_const _).const_mul _
  refine hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => ?_)
  refine (Φ.le_opNorm _).trans (le_of_eq ?_)
  congr 1
  rw [← Finset.prod_mul_prod_compl s]
  congr 1
  · rw [← Finset.prod_coe_sort s]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [vecOn, j.2]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [vecOn, Finset.mem_compl.1 hi]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `m`. Rewrite using `[Measure.pi_of_empty (x := fun i => isEmptyElim i)]`. Establish `hc : (fun x : ∀ i : (∅ : Finset ι), X i => Φ (vecOn g ∅ m x)) = fun _ => Φ m`.

Use function extensionality and compare the values at `x`. Use `congr 1`. Rewrite using `[hc]`. Simplify using the standard rewrite rules. Consider the case `insert a s ha ih`.

Introduce `m`. Rewrite using `[Finset.insert_eq]`. Establish `hd : Disjoint ({a} : Finset ι) s` using `Finset.disjoint_singleton_left.2 ha`. Establish `hmp` using `measurePreserving_piFinsetUnion hd μ`. Use `letI : Unique ↥({a} : Finset ι) := ⟨⟨⟨a, Finset.mem_singleton_self a⟩⟩, fun j => Subtype.ext (Finset.mem_singleton.1 j.2)⟩`.

Establish `hpt : ∀ p : (∀ i : ({a} : Finset ι), X i) × (∀ i : s, X i), vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p) = vecOn g s (Function.update m a (g a (p.1 default))) p.2`. Introduce and unpack `⟨y, z⟩`. Establish `he : (MeasurableEquiv.piFinsetUnion X hd (y, z) : ∀ i : ↥({a} ∪ s), X i) = Equiv.piFinsetUnion X hd (y, z)` using `rfl`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hia : i = a`.

Substitute `hia` using the available equality. Establish `h1 : i ∈ ({i} : Finset ι) ∪ s` using `by simp`. Simplify using `only [vecOn, dif_pos h1, dif_neg ha, Function.update_self, he]`. Rewrite using `[Equiv.piFinsetUnion_left X hd (Finset.mem_singleton_self i)]`. Both sides reduce to the same expression.

Distinguish the cases in `his : i ∈ s`. Establish `h1 : i ∈ ({a} : Finset ι) ∪ s` using `by simp [his]`. Simplify using `only [vecOn, dif_pos h1, dif_pos his, he]`. Rewrite using `[Equiv.piFinsetUnion_right X hd his]`. Establish `h1 : i ∉ ({a} : Finset ι) ∪ s` using `by simp [his, hia]`.

Simplify using `only [vecOn, dif_neg h1, dif_neg his, Function.update_of_ne hia]`. Establish `hint : Integrable (fun p => Φ (vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p))) ((Measure.pi fun i : ({a} : Finset ι) => μ i).prod (Measure.pi fun i : s => μ i))` using `(hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 (integrable_vecOn μ Φ g hg _ m)`. Rewrite using `[← hmp.integral_comp', integral_prod _ hint]`. Simplify using `only [hpt, ih]`. Use `set w : ∀ i, E i := fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i with hw`.

Establish `hupd : ∀ c : E a, (fun i => if i ∈ s then ∫ y, g i y ∂μ i else Function.update m a c i) = Function.update w a c`. Introduce `c`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality.

Simplify using `[hw, ha]`. Distinguish the cases in `his : i ∈ s`. Simplify using `[hw, his, Function.update_of_ne hia]`. Simplify using `[hw, his, Function.update_of_ne hia]`. Simplify using `only [hupd]`.

Establish `hL : ∀ c : E a, Φ (Function.update w a c) = Φ.toContinuousLinearMap w a c` using `fun c => rfl`. Simplify using `only [hL]`. Establish `h1` using `(measurePreserving_piUnique (fun i : ({a} : Finset ι) => μ i)).integral_comp' (fun t => Φ.toContinuousLinearMap w a (g a t))`. Rewrite using `[show (∫ x : ∀ i : ({a} : Finset ι), X i, Φ.toContinuousLinearMap w a (g a (x default)) ∂Measure.pi fun i : ({a} : Finset ι) => μ i) = ∫ t, Φ.toContinuousLinearMap w a (g a t) ∂μ a from h1]`. Rewrite using `[(Φ.toContinuousLinearMap w a).integral_comp_comm (hg a), ← hL]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Simplify using `[hw]`.

Distinguish the cases in `his : i ∈ s`. Simplify using `[hw, his, Function.update_of_ne hia]`. Simplify using `[hw, his, hia, Function.update_of_ne hia]`.
-/
theorem integral_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, CompleteSpace (E i)] [CompleteSpace F]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) : ∀ m : ∀ i, E i,
    ∫ x, Φ (vecOn g s m x) ∂(Measure.pi fun i : s => μ i) =
      Φ (fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Measure.pi_of_empty (x := fun i => isEmptyElim i)]
    have hc : (fun x : ∀ i : (∅ : Finset ι), X i => Φ (vecOn g ∅ m x)) = fun _ => Φ m := by
      funext x; congr 1
    rw [hc]; simp
  | insert a s ha ih =>
    intro m
    rw [Finset.insert_eq]
    have hd : Disjoint ({a} : Finset ι) s := Finset.disjoint_singleton_left.2 ha
    have hmp := measurePreserving_piFinsetUnion hd μ
    letI : Unique ↥({a} : Finset ι) :=
      ⟨⟨⟨a, Finset.mem_singleton_self a⟩⟩, fun j => Subtype.ext (Finset.mem_singleton.1 j.2)⟩
    have hpt : ∀ p : (∀ i : ({a} : Finset ι), X i) × (∀ i : s, X i),
        vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p) =
          vecOn g s (Function.update m a (g a (p.1 default))) p.2 := by
      rintro ⟨y, z⟩
      have he : (MeasurableEquiv.piFinsetUnion X hd (y, z) : ∀ i : ↥({a} ∪ s), X i) =
          Equiv.piFinsetUnion X hd (y, z) := rfl
      funext i
      by_cases hia : i = a
      · subst hia
        have h1 : i ∈ ({i} : Finset ι) ∪ s := by simp
        simp only [vecOn, dif_pos h1, dif_neg ha, Function.update_self, he]
        rw [Equiv.piFinsetUnion_left X hd (Finset.mem_singleton_self i)]
        rfl
      · by_cases his : i ∈ s
        · have h1 : i ∈ ({a} : Finset ι) ∪ s := by simp [his]
          simp only [vecOn, dif_pos h1, dif_pos his, he]
          rw [Equiv.piFinsetUnion_right X hd his]
        · have h1 : i ∉ ({a} : Finset ι) ∪ s := by simp [his, hia]
          simp only [vecOn, dif_neg h1, dif_neg his, Function.update_of_ne hia]
    have hint : Integrable (fun p => Φ (vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p)))
        ((Measure.pi fun i : ({a} : Finset ι) => μ i).prod (Measure.pi fun i : s => μ i)) :=
      (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
        (integrable_vecOn μ Φ g hg _ m)
    rw [← hmp.integral_comp', integral_prod _ hint]
    simp only [hpt, ih]
    set w : ∀ i, E i := fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i with hw
    have hupd : ∀ c : E a, (fun i => if i ∈ s then ∫ y, g i y ∂μ i else Function.update m a c i) =
        Function.update w a c := by
      intro c; funext i
      by_cases hia : i = a
      · subst hia; simp [hw, ha]
      · by_cases his : i ∈ s
        · simp [hw, his, Function.update_of_ne hia]
        · simp [hw, his, Function.update_of_ne hia]
    simp only [hupd]
    have hL : ∀ c : E a, Φ (Function.update w a c) = Φ.toContinuousLinearMap w a c := fun c => rfl
    simp only [hL]
    have h1 := (measurePreserving_piUnique (fun i : ({a} : Finset ι) => μ i)).integral_comp'
      (fun t => Φ.toContinuousLinearMap w a (g a t))
    rw [show (∫ x : ∀ i : ({a} : Finset ι), X i, Φ.toContinuousLinearMap w a (g a (x default))
        ∂Measure.pi fun i : ({a} : Finset ι) => μ i) = ∫ t, Φ.toContinuousLinearMap w a (g a t) ∂μ a from h1]
    rw [(Φ.toContinuousLinearMap w a).integral_comp_comm (hg a), ← hL]
    congr 1
    funext i
    by_cases hia : i = a
    · subst hia; simp [hw]
    · by_cases his : i ∈ s
      · simp [hw, his, Function.update_of_ne hia]
      · simp [hw, his, hia, Function.update_of_ne hia]

/- English proof (translation)
Introduce `ι _ _ X _ μ _ E _ _ _ F _ _ _ Φ g hg`. Prove the components needed by the constructor for the conclusion. Establish `hmeas : AEStronglyMeasurable (fun x : ∀ i, X i => fun i => g i (x i)) (Measure.pi μ)` using `aestronglyMeasurable_pi_of_forall (f := fun i (x : ∀ i, X i) => g i (x i)) fun i => (hg i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)`. Establish `hdom : Integrable (fun x : ∀ i, X i => ‖Φ‖ * ∏ i, ‖g i (x i)‖) (Measure.pi μ)` using `(Integrable.fintype_prod_dep (f := fun i (y : X i) => ‖g i y‖) fun i => (hg i).norm).const_mul _`. Conclude with `hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => Φ.le_opNorm _)`.

Set `e : (↥(Finset.univ : Finset ι)) ≃ ι` to `Equiv.subtypeUnivEquiv Finset.mem_univ`. Establish `hmp` using `measurePreserving_piCongrLeft μ e`. Rewrite using `[← hmp.integral_comp']`. Establish `hpt : ∀ z : ∀ i : (Finset.univ : Finset ι), X i, (fun i => g i (MeasurableEquiv.piCongrLeft X e z i)) = vecOn g Finset.univ 0 z`. Introduce `z`.

Use function extensionality and compare the values at `i`. Establish `h` using `Equiv.piCongrLeft_apply_apply X e z ⟨i, Finset.mem_univ i⟩`. Simplify using `only [vecOn, dif_pos (Finset.mem_univ i)]`. Rewrite using `[MeasurableEquiv.coe_piCongrLeft]`. Conclude with `congrArg (g i) h`.

Use `((integral_congr_ae (ae_of_all _ fun z => congrArg Φ (hpt z))).trans (integral_vecOn μ Φ g hg Finset.univ 0)).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem integral_multilinear_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  intro ι _ _ X _ μ _ E _ _ _ F _ _ _ Φ g hg
  constructor
  · have hmeas : AEStronglyMeasurable (fun x : ∀ i, X i => fun i => g i (x i)) (Measure.pi μ) :=
      aestronglyMeasurable_pi_of_forall (f := fun i (x : ∀ i, X i) => g i (x i)) fun i =>
        (hg i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
    have hdom : Integrable (fun x : ∀ i, X i => ‖Φ‖ * ∏ i, ‖g i (x i)‖) (Measure.pi μ) :=
      (Integrable.fintype_prod_dep (f := fun i (y : X i) => ‖g i y‖) fun i => (hg i).norm).const_mul _
    exact hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => Φ.le_opNorm _)
  · let e : (↥(Finset.univ : Finset ι)) ≃ ι := Equiv.subtypeUnivEquiv Finset.mem_univ
    have hmp := measurePreserving_piCongrLeft μ e
    rw [← hmp.integral_comp']
    have hpt : ∀ z : ∀ i : (Finset.univ : Finset ι), X i,
        (fun i => g i (MeasurableEquiv.piCongrLeft X e z i)) = vecOn g Finset.univ 0 z := by
      intro z; funext i
      have h := Equiv.piCongrLeft_apply_apply X e z ⟨i, Finset.mem_univ i⟩
      simp only [vecOn, dif_pos (Finset.mem_univ i)]
      rw [MeasurableEquiv.coe_piCongrLeft]
      exact congrArg (g i) h
    refine ((integral_congr_ae (ae_of_all _ fun z => congrArg Φ (hpt z))).trans
      (integral_vecOn μ Φ g hg Finset.univ 0)).trans ?_
    simp

end GlobalTheory.MultilinFubini
