import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine
open scoped Classical

namespace GlobalTheory.VacFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_SB_iff' {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ IsLocallyConstant f ∧ HasCompactSupport f := Iff.rfl

/- English proof (translation)
The claim follows from `funext fun i => Subtype.ext (funext fun u => h u i)`.
-/
theorem pt_ext {a b : κ → Af F} (h : ∀ u i, evalV F u (a i) = evalV F u (b i)) : a = b :=
  funext fun i => Subtype.ext (funext fun u => h u i)

def setAt (y : κ → Af F) (v : Pl F) (z : κ → Fv F v) : κ → Af F :=
  fun i => y i + singleFin v (z i - evalV F v (y i))

/- English proof (translation)
Rewrite using `[setAt, map_add, evalV_singleFin_self]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evalV_setAt_self (y : κ → Af F) (v : Pl F) (z : κ → Fv F v) (i : κ) :
    evalV F v (setAt y v z i) = z i := by
  rw [setAt, map_add, evalV_singleFin_self]; ring

/- English proof (translation)
Rewrite using `[setAt, map_add, evalV_singleFin_ne h, add_zero]`.
-/
theorem evalV_setAt_ne (y : κ → Af F) {v u : Pl F} (h : u ≠ v) (z : κ → Fv F v) (i : κ) :
    evalV F u (setAt y v z i) = evalV F u (y i) := by
  rw [setAt, map_add, evalV_singleFin_ne h, add_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[setAt]`.
-/
theorem setAt_eval (y : κ → Af F) (v : Pl F) : setAt y v (fun i => evalV F v (y i)) = y := by
  funext i; simp [setAt]

/- English proof (translation)
Apply `pt_ext` to reduce the goal to its premises. Introduce `u i`. Distinguish the cases in `h : u = v`. Substitute `h` using the available equality. Simplify using `only [Pi.add_apply, map_add, evalV_setAt_self, evalV_singleFin_self]`.

Simplify using `only [Pi.add_apply, map_add, evalV_setAt_ne y h, evalV_singleFin_ne h, add_zero]`.
-/
theorem setAt_add (y : κ → Af F) (v : Pl F) (z p : κ → Fv F v) :
    (setAt y v z + fun i => singleFin v (p i)) = setAt y v (z + p) := by
  apply pt_ext
  intro u i
  by_cases h : u = v
  · subst h
    simp only [Pi.add_apply, map_add, evalV_setAt_self, evalV_singleFin_self]
  · simp only [Pi.add_apply, map_add, evalV_setAt_ne y h, evalV_singleFin_ne h, add_zero]

def setOn (S : Finset (Pl F)) (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) : κ → Af F :=
  fun i => y i + ∑ v ∈ S, singleFin v (z₀ v i - evalV F v (y i))

/- English proof (translation)
Rewrite using `[setOn, map_add, map_sum, Finset.sum_eq_single u (fun w _ hw => evalV_singleFin_ne (Ne.symm hw) _) (fun h => absurd hu h), evalV_singleFin_self]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evalV_setOn_mem {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {u : Pl F} (hu : u ∈ S)
    (i : κ) : evalV F u (setOn S y z₀ i) = z₀ u i := by
  rw [setOn, map_add, map_sum, Finset.sum_eq_single u (fun w _ hw => evalV_singleFin_ne (Ne.symm hw) _)
    (fun h => absurd hu h), evalV_singleFin_self]
  ring

/- English proof (translation)
Rewrite using `[setOn, map_add, map_sum, Finset.sum_eq_zero (fun w hw => evalV_singleFin_ne (by rintro rfl; exact hu hw) _), add_zero]`.
-/
theorem evalV_setOn_not {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {u : Pl F} (hu : u ∉ S)
    (i : κ) : evalV F u (setOn S y z₀ i) = evalV F u (y i) := by
  rw [setOn, map_add, map_sum, Finset.sum_eq_zero (fun w hw => evalV_singleFin_ne (by rintro rfl; exact hu hw) _),
    add_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[setOn]`.
-/
theorem setOn_empty (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) : setOn ∅ y z₀ = y := by
  funext i; simp [setOn]

/- English proof (translation)
Apply `pt_ext` to reduce the goal to its premises. Introduce `u i`. Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Rewrite using `[evalV_setAt_self, evalV_setOn_mem y z₀ (Finset.mem_insert_self u S)]`.

Rewrite using `[evalV_setAt_ne _ h]`. Distinguish the cases in `hS : u ∈ S`. Rewrite using `[evalV_setOn_mem y z₀ hS, evalV_setOn_mem y z₀ (Finset.mem_insert_of_mem hS)]`. Rewrite using `[evalV_setOn_not y z₀ hS, evalV_setOn_not y z₀ (by simp [h, hS])]`.
-/
theorem setAt_setOn {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {w : Pl F} (hw : w ∉ S) :
    setAt (setOn S y z₀) w (z₀ w) = setOn (insert w S) y z₀ := by
  apply pt_ext
  intro u i
  by_cases h : u = w
  · subst h
    rw [evalV_setAt_self, evalV_setOn_mem y z₀ (Finset.mem_insert_self u S)]
  · rw [evalV_setAt_ne _ h]
    by_cases hS : u ∈ S
    · rw [evalV_setOn_mem y z₀ hS, evalV_setOn_mem y z₀ (Finset.mem_insert_of_mem hS)]
    · rw [evalV_setOn_not y z₀ hS, evalV_setOn_not y z₀ (by simp [h, hS])]

/- English proof (translation)
Take `⟨hlc, hcs⟩` from `(mem_SB_iff' g).mp hg`. Establish `hcont : Continuous fun z : κ → Fv F v => setAt y v z` using `continuous_pi fun i => continuous_const.add ((continuous_singleFin v).comp ((continuous_apply i).sub continuous_const))`. Establish `hE : Continuous fun x : κ → Af F => fun i => evalV F v (x i)` using `continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)`. Use `(mem_SB_iff' _).mpr ⟨hlc.comp_continuous hcont, ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (hcs.isCompact.image hE) fun z hz => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hz ⟨setAt y v z, subset_tsupport _ h, funext fun i => evalV_setAt_self y v z i⟩`.
-/
theorem slice_mem_SB {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (y : κ → Af F) (v : Pl F) :
    (fun z : κ → Fv F v => g (setAt y v z)) ∈ SB (κ → Fv F v) := by
  obtain ⟨hlc, hcs⟩ := (mem_SB_iff' g).mp hg
  have hcont : Continuous fun z : κ → Fv F v => setAt y v z :=
    continuous_pi fun i => continuous_const.add
      ((continuous_singleFin v).comp ((continuous_apply i).sub continuous_const))
  have hE : Continuous fun x : κ → Af F => fun i => evalV F v (x i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  refine (mem_SB_iff' _).mpr ⟨hlc.comp_continuous hcont, ?_⟩
  refine HasCompactSupport.intro (hcs.isCompact.image hE) fun z hz => ?_
  by_contra h
  exact hz ⟨setAt y v z, subset_tsupport _ h, funext fun i => evalV_setAt_self y v z i⟩

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `e` using `congrFun h (setAt y v z)`. Establish `hz : (fun i => evalV F v (setAt y v z i)) = z` using `funext fun i => evalV_setAt_self y v z i`. Simplify using `only [finOp, Pi.smul_apply, smul_eq_mul, hz, setAt_add] at e`. Simplify using `only [locOp, Pi.smul_apply, smul_eq_mul]`.

Conclude with `e`.
-/
theorem locOp_slice (ψ : AddChar (AF F) ℂ) (g : (κ → Af F) → ℂ) (y : κ → Af F) (v : Pl F)
    (p : (κ → Fv F v) × (κ → Fv F v)) (c : ℂ) (h : finOp ψ v p g = c • g) :
    locOp ψ v p (fun z => g (setAt y v z)) = c • fun z => g (setAt y v z) := by
  funext z
  have e := congrFun h (setAt y v z)
  have hz : (fun i => evalV F v (setAt y v z i)) = z := funext fun i => evalV_setAt_self y v z i
  simp only [finOp, Pi.smul_apply, smul_eq_mul, hz, setAt_add] at e
  simp only [locOp, Pi.smul_apply, smul_eq_mul]
  exact e

/- English proof (translation)
Take `⟨a, ha⟩` from `hline _ (slice_mem_SB hg y v) fun q hq => locOp_slice ψ g y v q.1 q.2 (heig q hq)`. Establish `h1` using `congrFun ha (fun i => evalV F v (y i))`. Establish `h2` using `congrFun ha z₁`. Simplify using `only [Pi.smul_apply, smul_eq_mul, setAt_eval] at h1 h2`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eigen_place (ψ : AddChar (AF F) ℂ) (v : Pl F) (vacv : (κ → Fv F v) → ℂ)
    (Qv : Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ))
    (hline : ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Qv, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vacv)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (heig : ∀ q ∈ Qv, finOp ψ v q.1 g = q.2 • g)
    (y : κ → Af F) (z₁ : κ → Fv F v) :
    g y * vacv z₁ = g (setAt y v z₁) * vacv (fun i => evalV F v (y i)) := by
  obtain ⟨a, ha⟩ := hline _ (slice_mem_SB hg y v) fun q hq => locOp_slice ψ g y v q.1 q.2 (heig q hq)
  have h1 := congrFun ha (fun i => evalV F v (y i))
  have h2 := congrFun ha z₁
  simp only [Pi.smul_apply, smul_eq_mul, setAt_eval] at h1 h2
  rw [h1, h2]; ring

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp [setOn_empty]`. Consider the case `insert w S hw ih`. Establish `e` using `eigen_place ψ w (vac w) (Q w) (hline w) hg (heig w) (setOn S y z₀) (z₀ w)`. Rewrite `e` using `[setAt_setOn y z₀ hw]`.

Establish `hyw : (fun i => evalV F w (setOn S y z₀ i)) = fun i => evalV F w (y i)`. Use function extensionality and compare the values at `fun i => evalV_setOn_not y z₀ hw i`. Rewrite `e` using `[hyw]`. Rewrite using `[Finset.prod_insert hw, Finset.prod_insert hw]`. Take the linear combination `(vac w (z₀ w)) * ih + (∏ v ∈ S, vac v (fun i => evalV F v (y i))) * e`.
-/
theorem eigen_finset (ψ : AddChar (AF F) ℂ) (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ))
    (hline : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (heig : ∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g)
    (z₀ : ∀ v : Pl F, κ → Fv F v) (y : κ → Af F) (S : Finset (Pl F)) :
    g y * ∏ v ∈ S, vac v (z₀ v) = g (setOn S y z₀) * ∏ v ∈ S, vac v (fun i => evalV F v (y i)) := by
  induction S using Finset.induction_on with
  | empty => simp [setOn_empty]
  | insert w S hw ih =>
    have e := eigen_place ψ w (vac w) (Q w) (hline w) hg (heig w) (setOn S y z₀) (z₀ w)
    rw [setAt_setOn y z₀ hw] at e
    have hyw : (fun i => evalV F w (setOn S y z₀ i)) = fun i => evalV F w (y i) :=
      funext fun i => evalV_setOn_not y z₀ hw i
    rw [hyw] at e
    rw [Finset.prod_insert hw, Finset.prod_insert hw]
    linear_combination (vac w (z₀ w)) * ih + (∏ v ∈ S, vac v (fun i => evalV F v (y i))) * e

/- English proof (translation)
Establish `hf1 : Function.mulSupport (fun u => if u ∈ S then A u else (1 : ℂ)) ⊆ (S : Set (Pl F))`. Introduce `u hu`. Assume the negation of the conclusion as `h`. Conclude with `hu (by simp only [Finset.mem_coe] at h; simp [h])`. Establish `hint : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ HeightOneSpectrum.adicCompletionIntegers F u` using `Filter.eventually_all.mpr fun i => (y i).2`.

Establish `hf2 : (Function.mulSupport fun u => if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))).Finite`. Establish `h : ∀ᶠ u in cofinite, (if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))) = 1` using `by filter_upwards [hint] with u hu split_ifs`. Both sides reduce to the same expression. Simplify using `[indO, Set.indicator, hu]`. Conclude with `(Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp`.

Establish `hsplit : (fun u => if u ∈ S then A u else indO u (fun i => evalV F u (y i))) = fun u => (if u ∈ S then A u else (1 : ℂ)) * (if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i)))`. Apply the tactic sequence `funext u; split_ifs <;> simp`. Rewrite using `[hsplit, finprod_mul_distrib ((S.finite_toSet).subset hf1) hf2, finprod_eq_prod_of_mulSupport_subset _ hf1]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun u hu => if_pos hu`.
-/
theorem finprod_split (S : Finset (Pl F)) (y : κ → Af F) (A : Pl F → ℂ) :
    (∏ᶠ u, if u ∈ S then A u else indO u (fun i => evalV F u (y i))) =
      (∏ u ∈ S, A u) * ∏ᶠ u, if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i)) := by
  have hf1 : Function.mulSupport (fun u => if u ∈ S then A u else (1 : ℂ)) ⊆ (S : Set (Pl F)) := by
    intro u hu
    by_contra h
    exact hu (by simp only [Finset.mem_coe] at h; simp [h])
  have hint : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ HeightOneSpectrum.adicCompletionIntegers F u :=
    Filter.eventually_all.mpr fun i => (y i).2
  have hf2 : (Function.mulSupport fun u => if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))).Finite := by
    have h : ∀ᶠ u in cofinite, (if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))) = 1 := by
      filter_upwards [hint] with u hu
      split_ifs
      · rfl
      · simp [indO, Set.indicator, hu]
    exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp
  have hsplit : (fun u => if u ∈ S then A u else indO u (fun i => evalV F u (y i))) =
      fun u => (if u ∈ S then A u else (1 : ℂ)) * (if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))) := by
    funext u; split_ifs <;> simp
  rw [hsplit, finprod_mul_distrib ((S.finite_toSet).subset hf1) hf2, finprod_eq_prod_of_mulSupport_subset _ hf1]
  congr 1
  exact Finset.prod_congr rfl fun u hu => if_pos hu

/- English proof (translation)
Introduce `F _ _ κ _ ψ vac Q _ hne hvacO hline g hg heig`. Take `⟨m, φ, -, hφstd, hrep⟩` from `GlobalTheory.SBRestrProd.sb_eq_sum_restrProd g hg`. Establish `hgood : ∀ᶠ v in cofinite, (∀ j, φ j v = indO v) ∧ vac v = indO v` using `(Filter.eventually_all.mpr hφstd).and hvacO`. Establish `hfin` using `Filter.eventually_cofinite.mp hgood`. Use `set S := hfin.toFinset with hSdef`.

Establish `hout : ∀ u, u ∉ S → (∀ j, φ j u = indO u) ∧ vac u = indO u`. Introduce `u hu`. Assume the negation of the conclusion as `h`. Conclude with `hu (hfin.mem_toFinset.mpr h)`. Establish `hz : ∀ v, ∃ z, vac v z ≠ 0` using `fun v => Function.ne_iff.mp (hne v)`.

Use `choose z₀ hz₀ using hz`. Establish `hP0 : (∏ v ∈ S, vac v (z₀ v)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun v _ => hz₀ v`. Use `set R : (κ → Af F) → ℂ := fun y => ∏ᶠ u, if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i)) with hR`. Use `set c : ℂ := ∑ j, ∏ u ∈ S, φ j u (z₀ u) with hc`. Establish `hvac : ∀ y, vacProd vac y = (∏ u ∈ S, vac u (fun i => evalV F u (y i))) * R y`.

Introduce `y`. Rewrite using `[← finprod_split S y]`. Unfold `vacProd`. Use `finprod_congr fun u => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite using `[(hout u h).2]`. Establish `hgS : ∀ y, g (setOn S y z₀) = c * R y`. Introduce `y`. Rewrite using `[hrep, hc, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← finprod_split S y]`. Use `finprod_congr fun u => ?_` and prove the remaining obligations. Use `split_ifs with h`. Use `congr 1`.

Conclude with `funext fun i => evalV_setOn_mem y z₀ h i`. Rewrite using `[(hout u h).1 j]`. Use `congr 1`. Conclude with `funext fun i => evalV_setOn_not y z₀ h i`. Use `⟨c / ∏ v ∈ S, vac v (z₀ v), funext fun y => ?_⟩` and prove the remaining obligations.

Establish `key` using `eigen_finset ψ vac Q hline hg heig z₀ y S`. Rewrite `key` using `[hgS]`. Rewrite using `[Pi.smul_apply, smul_eq_mul, hvac]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `key`.
-/
theorem eq_smul_vacProd : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ) (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ)),
    (∀ v, vac v ∈ SB (κ → Fv F v)) → (∀ v, vac v ≠ 0) → (∀ᶠ v in cofinite, vac v = indO v) →
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v) →
    ∀ g ∈ SB (κ → Af F), (∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g) → ∃ a : ℂ, g = a • vacProd vac := by
  intro F _ _ κ _ ψ vac Q _ hne hvacO hline g hg heig
  obtain ⟨m, φ, -, hφstd, hrep⟩ := GlobalTheory.SBRestrProd.sb_eq_sum_restrProd g hg
  have hgood : ∀ᶠ v in cofinite, (∀ j, φ j v = indO v) ∧ vac v = indO v :=
    (Filter.eventually_all.mpr hφstd).and hvacO
  have hfin := Filter.eventually_cofinite.mp hgood
  set S := hfin.toFinset with hSdef
  have hout : ∀ u, u ∉ S → (∀ j, φ j u = indO u) ∧ vac u = indO u := by
    intro u hu
    by_contra h
    exact hu (hfin.mem_toFinset.mpr h)
  have hz : ∀ v, ∃ z, vac v z ≠ 0 := fun v => Function.ne_iff.mp (hne v)
  choose z₀ hz₀ using hz
  have hP0 : (∏ v ∈ S, vac v (z₀ v)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hz₀ v
  set R : (κ → Af F) → ℂ := fun y => ∏ᶠ u, if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i)) with hR
  set c : ℂ := ∑ j, ∏ u ∈ S, φ j u (z₀ u) with hc
  have hvac : ∀ y, vacProd vac y = (∏ u ∈ S, vac u (fun i => evalV F u (y i))) * R y := by
    intro y
    rw [← finprod_split S y]
    unfold vacProd
    refine finprod_congr fun u => ?_
    split_ifs with h
    · rfl
    · rw [(hout u h).2]
  have hgS : ∀ y, g (setOn S y z₀) = c * R y := by
    intro y
    rw [hrep, hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← finprod_split S y]
    refine finprod_congr fun u => ?_
    split_ifs with h
    · congr 1
      exact funext fun i => evalV_setOn_mem y z₀ h i
    · rw [(hout u h).1 j]
      congr 1
      exact funext fun i => evalV_setOn_not y z₀ h i
  refine ⟨c / ∏ v ∈ S, vac v (z₀ v), funext fun y => ?_⟩
  have key := eigen_finset ψ vac Q hline hg heig z₀ y S
  rw [hgS] at key
  rw [Pi.smul_apply, smul_eq_mul, hvac]
  field_simp
  linear_combination key

end GlobalTheory.VacFactor
