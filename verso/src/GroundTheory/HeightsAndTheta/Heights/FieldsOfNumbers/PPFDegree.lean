import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForward
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Pull

variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

/- English proof (translation)
The claim follows from `j.injective.extend_apply b 0 k`.
-/
theorem extend_apply_self {M : Type*} [Zero M] (b : K → M) (k : K) :
    Function.extend j b 0 (j k) = b k :=
  j.injective.extend_apply b 0 k

/- English proof (translation)
Rewrite using `[Function.extend_apply' _ _ _ h]`. Both sides reduce to the same expression.
-/
theorem extend_apply_not {M : Type*} [Zero M] (b : K → M) (k' : K') (h : ¬ ∃ k, j k = k') :
    Function.extend j b 0 k' = 0 := by
  rw [Function.extend_apply' _ _ _ h]
  rfl

/- English proof (translation)
Use `⟨fun h => funext fun k => ?_, fun h => h ▸ rfl⟩` and prove the remaining obligations. Use `congrFun h (j k)` as an intermediate fact. Rewrite `this` using `[extend_apply_self, extend_apply_self]`. Then use the resulting hypothesis.
-/
theorem extend_inj {M : Type*} [Zero M] {b₁ b₂ : K → M} :
    Function.extend j b₁ 0 = Function.extend j b₂ 0 ↔ b₁ = b₂ := by
  refine ⟨fun h => funext fun k => ?_, fun h => h ▸ rfl⟩
  have := congrFun h (j k)
  rwa [extend_apply_self, extend_apply_self] at this

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]`.
-/
theorem weight_apply_eval {σ : Type*} (w : σ → K' → ℕ) (d : σ →₀ ℕ) (k' : K') :
    Finsupp.weight w d k' = Finsupp.weight (fun v => w v k') d := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

variable [DecidableEq K] [DecidableEq K']

omit [DecidableEq K] [DecidableEq K'] in

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply]`. Rewrite using `[Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Both sides reduce to the same expression.
-/
theorem weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (g : σ → τ)
    (d : σ →₀ ℕ) : Finsupp.weight w (Finsupp.mapDomain g d) = Finsupp.weight (w ∘ g) d := by
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  rfl

/- English proof (translation)
Rewrite using `[weight_mapDomain]`. Use function extensionality and compare the values at `k'`. Rewrite using `[weight_apply_eval]`. Distinguish the cases in `h : ∃ k, j k = k'`. Take `⟨k, rfl⟩` from `h`.

Rewrite using `[extend_apply_self, weight_apply_eval]`. Establish `e : (fun v => (blockWeight ι' ∘ blockIncl j ι') v (j k)) = fun v => blockWeight (fun k => ι' (j k)) v k`. Use function extensionality and compare the values at `v`. Use `show (Pi.single (j v.1) 1 : K' → ℕ) (j k) = (Pi.single v.1 1 : K → ℕ) k`. Simplify using `only [Pi.single_apply, j.injective.eq_iff]`.

Rewrite using `[e]`. Rewrite using `[extend_apply_not j _ k' h]`. Establish `h0 : (fun v => (blockWeight ι' ∘ blockIncl j ι') v k') = 0`. Use function extensionality and compare the values at `v`. Use `show (Pi.single (j v.1) 1 : K' → ℕ) k' = 0`.

Rewrite using `[Pi.single_apply, if_neg (fun hv => h ⟨v.1, hv.symm⟩)]`. Rewrite using `[h0]`. Simplify using `[Finsupp.weight_apply]`.
-/
theorem weight_blockIncl (d : (Σ k, ι' (j k)) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain (blockIncl j ι') d) =
      Function.extend j (Finsupp.weight (blockWeight (fun k => ι' (j k))) d) 0 := by
  rw [weight_mapDomain]
  funext k'
  rw [weight_apply_eval]
  by_cases h : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [extend_apply_self, weight_apply_eval]
    have e : (fun v => (blockWeight ι' ∘ blockIncl j ι') v (j k)) =
        fun v => blockWeight (fun k => ι' (j k)) v k := by
      funext v
      show (Pi.single (j v.1) 1 : K' → ℕ) (j k) = (Pi.single v.1 1 : K → ℕ) k
      simp only [Pi.single_apply, j.injective.eq_iff]
    rw [e]
  · rw [extend_apply_not j _ k' h]
    have h0 : (fun v => (blockWeight ι' ∘ blockIncl j ι') v k') = 0 := by
      funext v
      show (Pi.single (j v.1) 1 : K' → ℕ) k' = 0
      rw [Pi.single_apply, if_neg (fun hv => h ⟨v.1, hv.symm⟩)]
    rw [h0]
    simp [Finsupp.weight_apply]

variable {F : Type u} [Field F]

/- English proof (translation)
Establish `ha' : IsWeightedHomogeneous (blockWeight (fun k => ι' (j k))) a c` using `ha`. Use `show IsWeightedHomogeneous _ _ _`. Introduce `d' hd'`. Establish `hmem : d' ∈ (rename (blockIncl j ι') a).support` using `mem_support_iff.mpr hd'`. Rewrite `hmem` using `[support_rename_of_injective (blockIncl_injective j ι')]`.

Take `⟨d, hd, rfl⟩` from `Finset.mem_image.mp hmem`. Rewrite using `[weight_blockIncl, ha' (mem_support_iff.mp hd)]`.
-/
theorem isMultiHomog_rename {a : MRing (fun k => ι' (j k)) F} {c : K → ℕ} (ha : IsMultiHomog a c) :
    IsMultiHomog (rename (blockIncl j ι') a) (Function.extend j c 0) := by
  classical
  have ha' : IsWeightedHomogeneous (blockWeight (fun k => ι' (j k))) a c := ha
  show IsWeightedHomogeneous _ _ _
  intro d' hd'
  have hmem : d' ∈ (rename (blockIncl j ι') a).support := mem_support_iff.mpr hd'
  rw [support_rename_of_injective (blockIncl_injective j ι')] at hmem
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hmem
  rw [weight_blockIncl, ha' (mem_support_iff.mp hd)]

/- English proof (translation)
Use extensionality with `d'`. Rewrite using `[coeff_weightedHomogeneousComponent]`. Distinguish the cases in `hd : ∃ d, Finsupp.mapDomain (blockIncl j ι') d = d'`. Take `⟨d, rfl⟩` from `hd`. Rewrite using `[coeff_rename_mapDomain _ (blockIncl_injective j ι'), coeff_rename_mapDomain _ (blockIncl_injective j ι'), coeff_weightedHomogeneousComponent, weight_blockIncl]`.

Distinguish the cases in `hw : Finsupp.weight (blockWeight (fun k => ι' (j k))) d = b`. Rewrite using `[if_pos hw, if_pos (by rw [hw])]`. Rewrite using `[if_neg hw, if_neg (fun h => hw ((extend_inj j).mp h))]`. Use `push Not at hd`. Rewrite using `[coeff_rename_eq_zero _ _ d' (fun u hu => absurd hu (hd u)), coeff_rename_eq_zero _ a d' (fun u hu => absurd hu (hd u))]`.

Simplify using the standard rewrite rules.
-/
theorem rename_component (a : MRing (fun k => ι' (j k)) F) (b : K → ℕ) :
    rename (blockIncl j ι') (weightedHomogeneousComponent (blockWeight (fun k => ι' (j k))) b a) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0)
        (rename (blockIncl j ι') a) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain (blockIncl j ι') d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain _ (blockIncl_injective j ι'),
      coeff_rename_mapDomain _ (blockIncl_injective j ι'), coeff_weightedHomogeneousComponent,
      weight_blockIncl]
    by_cases hw : Finsupp.weight (blockWeight (fun k => ι' (j k))) d = b
    · rw [if_pos hw, if_pos (by rw [hw])]
    · rw [if_neg hw, if_neg (fun h => hw ((extend_inj j).mp h))]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ d' (fun u hu => absurd hu (hd u)),
      coeff_rename_eq_zero _ a d' (fun u hu => absurd hu (hd u))]
    simp

/- English proof (translation)
Use `hP'.isPrime` as an intermediate fact. Conclude with `contractPrime.isPrime j P'`. Use `multiHomog := by`. Introduce `f hf b`. Use `show rename (blockIncl j ι') _ ∈ P'`.

Rewrite using `[rename_component]`. Conclude with `hP'.multiHomog _ hf _`. Use `relevant := by`. Introduce `k`. Take `⟨i, hi⟩` from `hP'.relevant (j k)`.

Use `⟨i, ?_⟩` and prove the remaining obligations. Use `show rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'`. Rewrite using `[rename_X]`. Conclude with `hi`.
-/
theorem isMultiProjPrime_contractPrime {P' : Ideal (MRing ι' F)} (hP' : IsMultiProjPrime P') :
    IsMultiProjPrime (contractPrime j P') where
  isPrime := by
    have := hP'.isPrime
    exact contractPrime.isPrime j P'
  multiHomog := by
    intro f hf b
    show rename (blockIncl j ι') _ ∈ P'
    rw [rename_component]
    exact hP'.multiHomog _ hf _
  relevant := by
    intro k
    obtain ⟨i, hi⟩ := hP'.relevant (j k)
    refine ⟨i, ?_⟩
    show rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'
    rw [rename_X]
    exact hi

omit [DecidableEq K] [DecidableEq K'] in

/- English proof (translation)
Unfold `contractFracMap`. Conclude with `IsFractionRing.lift_algebraMap (g := ((IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp (contractQuot j P')).toRingHom) ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp Ideal.quotientMap_injective) _`.
-/
theorem contractFracMap_algebraMap (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (a : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') a)) =
      algebraMap _ (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') a)) := by
  unfold contractFracMap
  exact IsFractionRing.lift_algebraMap
    (g := ((IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      (contractQuot j P')).toRingHom)
    ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      Ideal.quotientMap_injective) _

/- English proof (translation)
Unfold `homFracDegZero`. Rewrite using `[IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨x, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩`. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Use `⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g, isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]`.
-/
theorem map_homFracDegZero_le (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
  apply IntermediateField.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_⟩
  rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]

omit [DecidableEq K] [DecidableEq K'] in

/- English proof (translation)
Use function extensionality and compare the values at `k'`. Distinguish the cases in `h : ∃ k, j k = k'`. Take `⟨k, rfl⟩` from `h`. Simplify using `only [pullDeg, extend_apply_self]`. Simplify using `only [pullDeg, extend_apply_not j _ k' h]`.

Simplify using the standard rewrite rules.
-/
theorem pullDeg_sub (bf bg : K → ℕ) :
    pullDeg j (fun k => (bf k : ℤ) - bg k) =
      fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ) := by
  funext k'
  by_cases h : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := h
    simp only [pullDeg, extend_apply_self]
  · simp only [pullDeg, extend_apply_not j _ k' h]
    simp

end Pull

/- English proof (translation)
Introduce `F _ K K' _ _ _ _ j ι' _ P' hP' n`. Proceed by induction on `n generalizing P' with`. Consider the case `zero`. Introduce `hdim hdimP bs`. Use `hP'.isPrime` as an intermediate fact.

Use `⟨map_homFracDegZero_le j ι' P', ?_⟩` and prove the remaining obligations. Establish `hP` using `isMultiProjPrime_contractPrime j ι' hP'`. Establish `e1 : (fun i : Fin 0 => pullDeg j (bs i)) = ![]` using `Subsingleton.elim _ _`. Establish `e2 : bs = ![]` using `Subsingleton.elim _ _`. Rewrite using `[e1, e2, (h2 F K' ι' P' hP' hdim).2, (h2 F K _ _ hP hdimP).2, ← IntermediateField.finrank_bot_mul_relfinrank (map_homFracDegZero_le j ι' P'), ← (IntermediateField.equivMap _ (contractFracMap j P')).toLinearEquiv.finrank_eq]`.

Unfold `relDeg`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ n ih`. Introduce `hdim hdimP bs`.

Use `hP'.isPrime` as an intermediate fact. Use `⟨map_homFracDegZero_le j ι' P', ?_⟩` and prove the remaining obligations. Establish `hP` using `isMultiProjPrime_contractPrime j ι' hP'`. Take `⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩` from `ExistsForm.proof F K (fun k => ι' (j k)) (contractPrime j P') hP (bs (Fin.last n))`. Establish `hbs : bs = Fin.snoc (α` using `fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by`.

Rewrite using `[hb, Fin.snoc_init_self]`. Establish `hpull : (fun i => pullDeg j (bs i)) = Fin.snoc (α` using `fun _ => K' → ℤ) (fun i => pullDeg j (Fin.init bs i)) (fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ)) := by`. Rewrite using `[← pullDeg_sub, hb]`. Use function extensionality and compare the values at `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `only [Fin.snoc_last]`. Simplify using `only [Fin.snoc_castSucc, Fin.init]`. Establish `hcutP : intNum F (contractPrime j P') bs = cycEval (fun W => intNum F W (Fin.init bs)) (ratDiv (contractPrime j P') f g)` using `by conv_lhs => rw [hbs]`. Conclude with `h1 F K _ _ hP n hdimP bf bg f g hf hg hfP hgP (Fin.init bs)`. Establish `hcutP'` using `h1 F K' ι' P' hP' n hdim _ _ (rename (blockIncl j ι') f) (rename (blockIncl j ι') g) (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg) hfP hgP (fun i => pullDeg j (Fin.init bs i))`.

Establish `hyp1 : ∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) → relDim (contractPrime j W') = (n : ℕ) → haveI` using `hW'.isPrime intNum F W' (fun i => pullDeg j (Fin.init bs i)) = relDeg j W' * intNum F (contractPrime j W') (Fin.init bs) := fun W' hW' hd hc => (ih W' hW' hd hc (Fin.init bs)).2`. Establish `hyp2 : ∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) → relDim (contractPrime j W') < (n : ℕ) → intNum F W' (fun i => pullDeg j (Fin.init bs i)) = 0` using `fun W' hW' hd hlt => h3 F K K' j ι' W' hW' n hd hlt (Fin.init bs)`. Establish `hpf` using `h4 F K K' j ι' P' hP' n hdim hdimP bf f hf hfP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i))) (fun W => intNum F W (Fin.init bs)) hyp1 hyp2`. Establish `hpg` using `h4 F K K' j ι' P' hP' n hdim hdimP bg g hg hgP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i))) (fun W => intNum F W (Fin.init bs)) hyp1 hyp2`. Rewrite using `[hpull, hcutP', hcutP, cycEval_ratDiv, cycEval_ratDiv, mul_sub, hpf, hpg]`.
-/
theorem ProjectionFormulaDegree.proof (h1 : CutRational.Statement.{u})
    (h2 : IntNumBase.Statement.{u}) (h3 : ProjectionFormulaContracted.Statement.{u})
    (h4 : DivPushForward.Statement.{u}) : ProjectionFormulaDegree.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n
  induction n generalizing P' with
  | zero =>
    intro hdim hdimP bs
    have := hP'.isPrime
    refine ⟨map_homFracDegZero_le j ι' P', ?_⟩
    have hP := isMultiProjPrime_contractPrime j ι' hP'
    have e1 : (fun i : Fin 0 => pullDeg j (bs i)) = ![] := Subsingleton.elim _ _
    have e2 : bs = ![] := Subsingleton.elim _ _
    rw [e1, e2, (h2 F K' ι' P' hP' hdim).2, (h2 F K _ _ hP hdimP).2,
      ← IntermediateField.finrank_bot_mul_relfinrank (map_homFracDegZero_le j ι' P'),
      ← (IntermediateField.equivMap _ (contractFracMap j P')).toLinearEquiv.finrank_eq]
    unfold relDeg
    push_cast
    ring
  | succ n ih =>
    intro hdim hdimP bs
    have := hP'.isPrime
    refine ⟨map_homFracDegZero_le j ι' P', ?_⟩
    have hP := isMultiProjPrime_contractPrime j ι' hP'
    obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩ :=
      ExistsForm.proof F K (fun k => ι' (j k)) (contractPrime j P') hP (bs (Fin.last n))
    have hbs : bs = Fin.snoc (α := fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by
      rw [hb, Fin.snoc_init_self]
    have hpull : (fun i => pullDeg j (bs i)) = Fin.snoc (α := fun _ => K' → ℤ)
        (fun i => pullDeg j (Fin.init bs i))
        (fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ)) := by
      rw [← pullDeg_sub, hb]
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc, Fin.init]
    have hcutP : intNum F (contractPrime j P') bs =
        cycEval (fun W => intNum F W (Fin.init bs)) (ratDiv (contractPrime j P') f g) := by
      conv_lhs => rw [hbs]
      exact h1 F K _ _ hP n hdimP bf bg f g hf hg hfP hgP (Fin.init bs)
    have hcutP' := h1 F K' ι' P' hP' n hdim _ _ (rename (blockIncl j ι') f)
      (rename (blockIncl j ι') g) (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg)
      hfP hgP (fun i => pullDeg j (Fin.init bs i))
    have hyp1 : ∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) →
        relDim (contractPrime j W') = (n : ℕ) →
        haveI := hW'.isPrime
        intNum F W' (fun i => pullDeg j (Fin.init bs i)) =
          relDeg j W' * intNum F (contractPrime j W') (Fin.init bs) :=
      fun W' hW' hd hc => (ih W' hW' hd hc (Fin.init bs)).2
    have hyp2 : ∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) →
        relDim (contractPrime j W') < (n : ℕ) →
        intNum F W' (fun i => pullDeg j (Fin.init bs i)) = 0 :=
      fun W' hW' hd hlt => h3 F K K' j ι' W' hW' n hd hlt (Fin.init bs)
    have hpf := h4 F K K' j ι' P' hP' n hdim hdimP bf f hf hfP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i)))
      (fun W => intNum F W (Fin.init bs)) hyp1 hyp2
    have hpg := h4 F K K' j ι' P' hP' n hdim hdimP bg g hg hgP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i)))
      (fun W => intNum F W (Fin.init bs)) hyp1 hyp2
    rw [hpull, hcutP', hcutP, cycEval_ratDiv, cycEval_ratDiv, mul_sub, hpf, hpg]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
