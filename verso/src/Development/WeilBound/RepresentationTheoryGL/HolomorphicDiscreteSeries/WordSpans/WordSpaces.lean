import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.QminorInt
import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.WordSpaces

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC PositivityTheory.UnitaryDecomposition.Com PositivityTheory.RgHe.SM

section WS

variable {V : Type} [AddCommGroup V] [Module ℂ V] {m : ℕ} (E : Fin m → Fin m → Module.End ℂ V)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨[], by simp, by simp⟩`.
-/
theorem one_mem_ws (L : ℕ) : (1 : Module.End ℂ V) ∈ wordSpan E L :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩`.
-/
theorem gen_mem_ws (a b : Fin m) : E a b ∈ wordSpan E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

/- English proof (translation)
Establish `key : wordSpan E L * wordSpan E L' ≤ wordSpan E (L + L')`. Unfold `wordSpan`. Rewrite using `[Submodule.span_mul_span]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨A, ⟨w, hw, rfl⟩, B, ⟨w', hw', rfl⟩, rfl⟩`.

Conclude with `⟨w ++ w', by simp only [List.length_append]; omega, by simp [List.map_append, List.prod_append]⟩`. Conclude with `key (Submodule.mul_mem_mul hT hT')`.
-/
theorem ws_mul {L L' : ℕ} {T T' : Module.End ℂ V} (hT : T ∈ wordSpan E L) (hT' : T' ∈ wordSpan E L') :
    T * T' ∈ wordSpan E (L + L') := by
  have key : wordSpan E L * wordSpan E L' ≤ wordSpan E (L + L') := by
    unfold wordSpan
    rw [Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨A, ⟨w, hw, rfl⟩, B, ⟨w', hw', rfl⟩, rfl⟩
    exact ⟨w ++ w', by simp only [List.length_append]; omega, by simp [List.map_append, List.prod_append]⟩
  exact key (Submodule.mul_mem_mul hT hT')

variable {k : ℕ} (F : Fin k → Fin k → Module.End ℂ V)

/- English proof (translation)
Unfold `Tm`. Use `Submodule.add_mem _ ?_ (hF a b)` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ _ (one_mem_ws E 1)`.

Conclude with `Submodule.zero_mem _`.
-/
theorem tm_mem (hF : ∀ a b, F a b ∈ wordSpan E 1) (u : ℂ) (a b : Fin k) : Tm F u a b ∈ wordSpan E 1 := by
  unfold Tm
  refine Submodule.add_mem _ ?_ (hF a b)
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (one_mem_ws E 1)
  · exact Submodule.zero_mem _

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using one_mem_ws E 0`. Consider the case `cons x l ih`. Rewrite using `[List.prod_cons, List.length_cons, add_comm]`. Conclude with `ws_mul E (h x (by simp)) (ih fun y hy => h y (by simp [hy]))`.
-/
theorem prod_mem_ws (l : List (Module.End ℂ V)) (h : ∀ x ∈ l, x ∈ wordSpan E 1) : l.prod ∈ wordSpan E l.length := by
  induction l with
  | nil => simpa using one_mem_ws E 0
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons, add_comm]
    exact ws_mul E (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/- English proof (translation)
Unfold `qminor`. Use `Submodule.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Establish `h` using `prod_mem_ws E (List.ofFn fun i : Fin t => Tm F (u - (i : ℂ)) (a (σ i)) (b i)) (by`. Introduce `x hx`. Rewrite `hx` using `[List.mem_ofFn]`.

Take `⟨i, rfl⟩` from `hx`. Conclude with `tm_mem E F hF _ _ _)`. Rewrite `h` using `[List.length_ofFn]`. Rewrite using `[← zsmul_eq_mul]`. Conclude with `zsmul_mem h _`.
-/
theorem qminor_mem (hF : ∀ a b, F a b ∈ wordSpan E 1) {t : ℕ} (a b : Fin t → Fin k) (u : ℂ) :
    qminor F a b u ∈ wordSpan E t := by
  unfold qminor
  refine Submodule.sum_mem _ fun σ _ => ?_
  have h := prod_mem_ws E (List.ofFn fun i : Fin t => Tm F (u - (i : ℂ)) (a (σ i)) (b i)) (by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact tm_mem E F hF _ _ _)
  rw [List.length_ofFn] at h
  rw [← zsmul_eq_mul]
  exact zsmul_mem h _

end WS

/- English proof (translation)
Use `set ι : Fin (N + 1) → Fin (N + 2) := fun a => e (Sum.inl a) with hι`. Use `set z : Fin (N + 2) := zi e with hz`. Use `set m : Fin (N + 1) → ℂ := fun i => (mu i : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2 with hm`. Establish `hq : ∀ u v, qdet E' u v = (∏ i, (u + m i)) • v` using `cap_of hG.hc' hσ hS'`. Use `set w : ℂ := -m j with hw`.

Establish `hPs : ∀ v : S, P v ∈ S'` using `fun v => (hS'.mem _).2 (smooth_map hG.fits hP ((hS.mem _).1 v.2))`. Set `f : S →ₗ[ℂ] S'` to `{ toFun := fun v => ⟨P v, hPs v⟩ map_add' := fun a b => Subtype.ext (by simp) map_smul' := fun c a => Subtype.ext (by simp) }`. Establish `hf : ∀ a b (v : S), f (E (ι a) (ι b) v) = E' a b (f v)` using `fun a b v => Subtype.ext (by show P (E (ι a) (ι b) v : H) = (E' a b (f v) : H')`. Rewrite using `[hS.act, hS'.act, ← blk_single (e := e)]`. Conclude with `dsigC_map hG.fits hP (fun X hX => (hS.real X hX v).differentiableAt) _)`.

Set `co : (Fin (N + 1) → S') → Fin (N + 1) → H'` to `fun x l => x l`. Establish `hco : ∀ x, co x ∈ SmT ε' σ` using `fun x l => (hS'.mem _).1 (x l).2`. Set `Y : (Fin (N + 1) → S') → X.S → Fin (N + 1) → S'` to `fun x t c => ⟨X.p t (co x) c, (hS'.mem _).2 (X.p_sm t t.2 _ (hco x) c)⟩`. Establish `hYe : ∀ x t, EE E' (Y x t) = X.κ t • Y x t` using `fun x t => funext fun c => Subtype.ext (by`. Use `congrFun (X.cas t t.2 _ (hco x)) c` as an intermediate fact.

Rewrite using `[EE_apply, Submodule.coe_sum]`. Simplify using `only [hS'.act]`. Conclude with `this)`. Establish `hYs : ∀ x, ∑ t, Y x t = x` using `fun x => funext fun c => Subtype.ext (by`. Use `congrFun (X.sum _ (hco x)) c` as an intermediate fact.

Rewrite `this` using `[Finset.sum_apply]`. Rewrite using `[Finset.sum_apply, Submodule.coe_sum]`. Conclude with `(Finset.sum_coe_sort X.S fun t => X.p t (co x) c).trans this)`. Use `set d : ℂ := ∏ i ∈ univ.erase j, (-m j + m i) with hd`. Establish `hd0 : d ≠ 0`.

Rewrite using `[hd, Finset.prod_ne_zero_iff]`. Introduce `i hi h0`. Establish `hne : i ≠ j` using `Finset.ne_of_mem_erase hi`. Establish `: mu i = mu j`. Establish `h1 : (mu i : ℂ) = mu j` using `by simp only [hm] at h0; linear_combination h0`.

Conclude with `h1` after adjusting the coercions. Conclude with `hne (hG.hc'.1.injective this)`. Establish `hth : ∀ x, Th E' w x = d • Y x ⟨j, hj⟩` using `fun x => by`. Establish `h` using `th_proj hS'.gl hq univ (Y x) (fun t : X.S => X.κ t) (fun a _ b _ h => Subtype.ext (X.κ_inj a.2 b.2 h)) (fun t _ => hYe x t) (mem_univ (⟨j, hj⟩ : X.S)) j (by rw [hκ]; simp only [hm]; push_cast; ring)`. Rewrite `h` using `[hYs]`. Then use the resulting hypothesis.

Set `T : Fin (N + 1) → Module.End ℂ S` to `fun l => ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (l : ℕ))) • (qminor (fun a b => E (ι a) (ι b)) a.succAbove l.succAbove w * E (ι a) z)`. Use `⟨fun l => d⁻¹ • T l, fun l => ?_, fun ζ hζ l => ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Conclude with `ws_mul E (qminor_mem E _ (fun a b => gen_mem_ws E _ _) _ _ _) (gen_mem_ws E _ _)`. Use `set ζ' : S := ⟨ζ, hζ⟩`.

Set `X0 : Fin (N + 1) → S` to `fun a => E (ι a) z ζ'`. Set `x : Fin (N + 1) → S'` to `fun c => f (X0 c)`. Establish `hco' : co x = phi E e P ζ` using `funext fun c => by`. Simplify using `only [co, x, X0, phi, ap, dif_pos hζ]`. Both sides reduce to the same expression.

Establish `hT : T l ζ' = Th (fun a b => E (ι a) (ι b)) w X0 l`. Rewrite using `[Th_apply]`. Simplify using `only [T, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]`. Both sides reduce to the same expression. Establish `h1 : P (ap (d⁻¹ • T l) ζ) = d⁻¹ • (f (Th (fun a b => E (ι a) (ι b)) w X0 l) : H')`.

Simplify using `only [ap, dif_pos hζ, LinearMap.smul_apply, Submodule.coe_smul, map_smul]`. Rewrite using `[hT]`. Both sides reduce to the same expression. Establish `h2` using `(thMap S S' N (fun a b => E (ι a) (ι b)) E' f hf w X0 l).1`. Rewrite using `[h1, h2, show (fun l => f (X0 l)) = x from rfl, hth x, ← hco']`.

Simplify using `only [Pi.smul_apply, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hd0, one_smul]`. Both sides reduce to the same expression.
-/
theorem pj_words {N : ℕ} {ε : Fin (N + 2) → Bool} {ε' : Fin (N + 1) → Bool} {e : Fin (N + 1) ⊕ Unit ≃ Fin (N + 2)}
    {lam : Fin (N + 2) → ℝ} {mu : Fin (N + 1) → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → (H' →L[ℂ] H')} {S : Submodule ℂ H} {E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ S}
    {S' : Submodule ℂ H'} {E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ S'} {P : H →L[ℂ] H'} (hG : Gp ε lam ε' mu e)
    (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ) (hS : IsSmMod ε π S E) (hS' : IsSmMod ε' σ S' E') (hP : Intertw ε' e π σ P)
    (X : Dec ε' mu σ) (hκ : ∀ s, X.κ s = (mu s : ℂ) + (((N + 1 : ℕ) : ℂ) - 1) / 2) (j : Fin (N + 1)) (hj : j ∈ X.S) :
    ∃ R : Fin (N + 1) → Module.End ℂ S, (∀ l, R l ∈ wordSpan E (N + 1)) ∧
      ∀ ζ ∈ S, ∀ l, X.p j (phi E e P ζ) l = P (ap (R l) ζ) := by
  classical
  set ι : Fin (N + 1) → Fin (N + 2) := fun a => e (Sum.inl a) with hι
  set z : Fin (N + 2) := zi e with hz
  set m : Fin (N + 1) → ℂ := fun i => (mu i : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2 with hm
  have hq : ∀ u v, qdet E' u v = (∏ i, (u + m i)) • v := cap_of hG.hc' hσ hS'
  set w : ℂ := -m j with hw
  have hPs : ∀ v : S, P v ∈ S' := fun v => (hS'.mem _).2 (smooth_map hG.fits hP ((hS.mem _).1 v.2))
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun v => ⟨P v, hPs v⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  have hf : ∀ a b (v : S), f (E (ι a) (ι b) v) = E' a b (f v) := fun a b v => Subtype.ext (by
    show P (E (ι a) (ι b) v : H) = (E' a b (f v) : H')
    rw [hS.act, hS'.act, ← blk_single (e := e)]
    exact dsigC_map hG.fits hP (fun X hX => (hS.real X hX v).differentiableAt) _)
  let co : (Fin (N + 1) → S') → Fin (N + 1) → H' := fun x l => x l
  have hco : ∀ x, co x ∈ SmT ε' σ := fun x l => (hS'.mem _).1 (x l).2
  let Y : (Fin (N + 1) → S') → X.S → Fin (N + 1) → S' := fun x t c =>
    ⟨X.p t (co x) c, (hS'.mem _).2 (X.p_sm t t.2 _ (hco x) c)⟩
  have hYe : ∀ x t, EE E' (Y x t) = X.κ t • Y x t := fun x t => funext fun c => Subtype.ext (by
    have := congrFun (X.cas t t.2 _ (hco x)) c
    rw [EE_apply, Submodule.coe_sum]
    simp only [hS'.act]
    exact this)
  have hYs : ∀ x, ∑ t, Y x t = x := fun x => funext fun c => Subtype.ext (by
    have := congrFun (X.sum _ (hco x)) c
    rw [Finset.sum_apply] at this
    rw [Finset.sum_apply, Submodule.coe_sum]
    exact (Finset.sum_coe_sort X.S fun t => X.p t (co x) c).trans this)
  set d : ℂ := ∏ i ∈ univ.erase j, (-m j + m i) with hd
  have hd0 : d ≠ 0 := by
    rw [hd, Finset.prod_ne_zero_iff]
    intro i hi h0
    have hne : i ≠ j := Finset.ne_of_mem_erase hi
    have : mu i = mu j := by
      have h1 : (mu i : ℂ) = mu j := by simp only [hm] at h0; linear_combination h0
      exact_mod_cast h1
    exact hne (hG.hc'.1.injective this)
  have hth : ∀ x, Th E' w x = d • Y x ⟨j, hj⟩ := fun x => by
    have h := th_proj hS'.gl hq univ (Y x) (fun t : X.S => X.κ t)
      (fun a _ b _ h => Subtype.ext (X.κ_inj a.2 b.2 h)) (fun t _ => hYe x t) (mem_univ (⟨j, hj⟩ : X.S)) j
      (by rw [hκ]; simp only [hm]; push_cast; ring)
    rwa [hYs] at h
  let T : Fin (N + 1) → Module.End ℂ S := fun l =>
    ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (l : ℕ))) •
      (qminor (fun a b => E (ι a) (ι b)) a.succAbove l.succAbove w * E (ι a) z)
  refine ⟨fun l => d⁻¹ • T l, fun l => ?_, fun ζ hζ l => ?_⟩
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
    exact ws_mul E (qminor_mem E _ (fun a b => gen_mem_ws E _ _) _ _ _) (gen_mem_ws E _ _)
  · set ζ' : S := ⟨ζ, hζ⟩
    let X0 : Fin (N + 1) → S := fun a => E (ι a) z ζ'
    let x : Fin (N + 1) → S' := fun c => f (X0 c)
    have hco' : co x = phi E e P ζ := funext fun c => by
      simp only [co, x, X0, phi, ap, dif_pos hζ]
      rfl
    have hT : T l ζ' = Th (fun a b => E (ι a) (ι b)) w X0 l := by
      rw [Th_apply]
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
      rfl
    have h1 : P (ap (d⁻¹ • T l) ζ) = d⁻¹ • (f (Th (fun a b => E (ι a) (ι b)) w X0 l) : H') := by
      simp only [ap, dif_pos hζ, LinearMap.smul_apply, Submodule.coe_smul, map_smul]
      rw [hT]
      rfl
    have h2 := (thMap S S' N (fun a b => E (ι a) (ι b)) E' f hf w X0 l).1
    rw [h1, h2, show (fun l => f (X0 l)) = x from rfl, hth x, ← hco']
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rfl

end PositivityTheory.RgHe.SM.WordSpaces
