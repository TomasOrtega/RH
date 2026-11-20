import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Set
open scoped Interval

noncomputable section

def fiBox (m : ℕ) : Set (Fin m → ℝ) := Set.univ.pi (fun _ : Fin m => Set.Ioc (0 : ℝ) 1)

def fiG {f : ℕ} (h : (Fin f → ℂ) → ℂ) (ν : Fin f → ℤ) (s : Fin f → ℂ) : ℂ :=
  h s * Complex.exp (-2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * s k)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma fourCoeff_eq_fiG {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) (ν : Fin f → ℤ) :
    fourCoeff h b ν =
      ∫ x in fiBox f, fiG h ν (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) := rfl

/- English proof (translation)
Use `set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm`. Establish `hem : MeasurePreserving e` using `(volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _`. Establish `hpre : e ⁻¹' fiBox (n + 1) = Set.Ioc (0 : ℝ) 1 ×ˢ fiBox n`. Use extensionality with `⟨t, y⟩`. Simplify using `[e, fiBox, Set.mem_pi, Fin.forall_iff_succAbove i]`.

Establish `hint : IntegrableOn Φ (fiBox (n + 1))`. Establish `hc : IsCompact (Set.univ.pi (fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1))` using `isCompact_univ_pi (fun _ => isCompact_Icc)`. Use `(hΦ.continuousOn.integrableOn_compact hc).mono_set ?_` and prove the remaining obligations. Conclude with `Set.pi_mono (fun _ _ => Set.Ioc_subset_Icc_self)`. Establish `hint' : IntegrableOn (Φ ∘ e) (Set.Ioc (0 : ℝ) 1 ×ˢ fiBox n) (volume.prod volume)`.

Rewrite using `[← hpre, ← Measure.volume_eq_prod]`. Conclude with `(hem.integrableOn_comp_preimage e.measurableEmbedding).2 hint`. Rewrite using `[← hem.map_eq, setIntegral_map_equiv, hpre, Measure.volume_eq_prod]`. Rewrite `hint'` using `[IntegrableOn, ← Measure.prod_restrict]`. Rewrite using `[← Measure.prod_restrict, integral_prod_symm (fun z => Φ (e z)) hint']`.

Simplify using `[e]`. Both sides reduce to the same expression.
-/
lemma fiBox_slices {n : ℕ} (i : Fin (n + 1)) (Φ : (Fin (n + 1) → ℝ) → ℂ) (hΦ : Continuous Φ) :
    ∫ x in fiBox (n + 1), Φ x = ∫ y in fiBox n, ∫ t in Set.Ioc (0 : ℝ) 1, Φ (i.insertNth t y) := by
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' fiBox (n + 1) = Set.Ioc (0 : ℝ) 1 ×ˢ fiBox n := by
    ext ⟨t, y⟩
    simp [e, fiBox, Set.mem_pi, Fin.forall_iff_succAbove i]
  have hint : IntegrableOn Φ (fiBox (n + 1)) := by
    have hc : IsCompact (Set.univ.pi (fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    refine (hΦ.continuousOn.integrableOn_compact hc).mono_set ?_
    exact Set.pi_mono (fun _ _ => Set.Ioc_subset_Icc_self)
  have hint' : IntegrableOn (Φ ∘ e) (Set.Ioc (0 : ℝ) 1 ×ˢ fiBox n) (volume.prod volume) := by
    rw [← hpre, ← Measure.volume_eq_prod]
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 hint
  rw [← hem.map_eq, setIntegral_map_equiv, hpre, Measure.volume_eq_prod]
  rw [IntegrableOn, ← Measure.prod_restrict] at hint'
  rw [← Measure.prod_restrict, integral_prod_symm (fun z => Φ (e z)) hint']
  simp [e]
  rfl

/- English proof (translation)
Establish `hd : Differentiable ℂ (fun s : Fin f → ℂ => Complex.exp (-2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * s k))` using `by fun_prop`. Conclude with `hh.mul hd.differentiableOn`.
-/
lemma fiG_differentiableOn {f : ℕ} {Ω : Set (Fin f → ℝ)} {h : (Fin f → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (tube f Ω)) (ν : Fin f → ℤ) :
    DifferentiableOn ℂ (fiG h ν) (tube f Ω) := by
  have hd : Differentiable ℂ
      (fun s : Fin f → ℂ => Complex.exp (-2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * s k)) := by
    fun_prop
  exact hh.mul hd.differentiableOn

/- English proof (translation)
Introduce `s hs m`. Unfold `fiG`. Rewrite using `[hper s hs m]`. Use `congr 1`. Establish `hsum : ∑ k, (ν k : ℂ) * (s + fun k => (m k : ℂ)) k = ∑ k, (ν k : ℂ) * s k + ((∑ k, ν k * m k : ℤ) : ℂ)`.

Use `push_cast`. Simplify using `[Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Rewrite using `[hsum, mul_add, Complex.exp_add]`. Establish `h2 : Complex.exp (-2 * Real.pi * Complex.I * ((∑ k, ν k * m k : ℤ) : ℂ)) = 1`. Rewrite using `[← Complex.exp_int_mul_two_pi_mul_I (-(∑ k, ν k * m k))]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, mul_one]`.
-/
lemma fiG_periodic {f : ℕ} {Ω : Set (Fin f → ℝ)} {h : (Fin f → ℂ) → ℂ}
    (hper : ∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h (s + fun k => (m k : ℂ)) = h s) (ν : Fin f → ℤ) :
    ∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, fiG h ν (s + fun k => (m k : ℂ)) = fiG h ν s := by
  intro s hs m
  unfold fiG
  rw [hper s hs m]
  congr 1
  have hsum : ∑ k, (ν k : ℂ) * (s + fun k => (m k : ℂ)) k =
      ∑ k, (ν k : ℂ) * s k + ((∑ k, ν k * m k : ℤ) : ℂ) := by
    push_cast
    simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hsum, mul_add, Complex.exp_add]
  have h2 : Complex.exp (-2 * Real.pi * Complex.I * ((∑ k, ν k * m k : ℤ) : ℂ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I (-(∑ k, ν k * m k))]
    congr 1
    push_cast
    ring
  rw [h2, mul_one]

/- English proof (translation)
Use `set base : Fin (n + 1) → ℂ := fun k => ((i.insertNth (0 : ℝ) y : Fin (n + 1) → ℝ) k : ℂ) + (b k : ℂ) * Complex.I`. Use `set P : ℂ → Fin (n + 1) → ℂ := fun z k => if k = i then z else base k with hPdef`. Establish `hP : ∀ t c : ℝ, (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) + (Function.update b i c k : ℂ) * Complex.I) = P (t + c * Complex.I)`. Introduce `t c`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[P]`. Take `⟨j, rfl⟩` from `Fin.exists_succAbove_eq hk`. Simplify using `[P, base, hk]`.

Establish `hb : Function.update b i (b i) = b` using `Function.update_eq_self i b`. Establish `hPim : ∀ z : ℂ, (fun k => (P z k).im) = Function.update b i z.im`. Introduce `z`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `[P]`. Simplify using `[P, base, hk]`. Establish `hPdiff : Differentiable ℂ P`. Use `differentiable_pi.2 fun k => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : k = i`. Simplify using `only [P, hk, if_true]`. Conclude with `differentiable_id`. Simplify using `only [P, hk, if_false]`. Conclude with `differentiable_const _`.

Use `set g : ℂ → ℂ := fun z => fiG h ν (P z) with hgdef`. Establish `hgd : DifferentiableOn ℂ g ([[(0 : ℝ), 1]] ×ℂ [[b i, β]])`. Use `(fiG_differentiableOn hh ν).comp hPdiff.differentiableOn ?_` and prove the remaining obligations. Introduce `z hz`. Use `show (fun k => (P z k).im) ∈ Ω`.

Rewrite using `[hPim]`. Conclude with `hseg _ hz.2`. Establish `hC` using `Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨0, b i⟩ ⟨1, β⟩ hgd`. Simplify using `only at hC`. Establish `hv : ∫ y in (b i)..β, g (((1 : ℝ) : ℂ) + y * Complex.I) = ∫ y in (b i)..β, g (((0 : ℝ) : ℂ) + y * Complex.I)`.

Use `intervalIntegral.integral_congr fun t ht => ?_` and prove the remaining obligations. Use `show fiG h ν (P (((1 : ℝ) : ℂ) + t * Complex.I)) = fiG h ν (P (((0 : ℝ) : ℂ) + t * Complex.I))`. Establish `hm : P (((1 : ℝ) : ℂ) + t * Complex.I) = P (((0 : ℝ) : ℂ) + t * Complex.I) + fun k => ((Pi.single i (1 : ℤ) : Fin (n + 1) → ℤ) k : ℂ)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `[P]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[P, hk]`. Rewrite using `[hm]`.

Apply `fiG_periodic hper` to reduce the goal to its premises. Use `show (fun k => (P _ k).im) ∈ Ω`. Rewrite using `[hPim]`. Establish `him : ((((0 : ℝ) : ℂ) + t * Complex.I) : ℂ).im = t` using `by simp`. Rewrite using `[him]`.

Conclude with `hseg t ht`. Establish `hh1 : ∫ x in (0 : ℝ)..1, g (x + (b i) * Complex.I) = ∫ x in (0 : ℝ)..1, g (x + β * Complex.I)`. Rewrite `hC` using `[hv, add_sub_cancel_right, sub_eq_zero]`. Conclude with `hC`. Establish `e1 : ∀ t : ℝ, fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) + (b k : ℂ) * Complex.I) = g (t + (b i) * Complex.I)`.

Introduce `t`. Use `hP t (b i)` as an intermediate fact. Rewrite `this` using `[hb]`. Simplify using `only [g]`. Rewrite using `[this]`.

Establish `e2 : ∀ t : ℝ, fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) + (Function.update b i β k : ℂ) * Complex.I) = g (t + β * Complex.I)`. Introduce `t`. Simplify using `only [g]`. Rewrite using `[hP]`. Simplify using `only [e1, e2]`.

Rewrite using `[← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]`. Conclude with `hh1`.
-/
lemma fiSlice_eq {n : ℕ} {Ω : Set (Fin (n + 1) → ℝ)} {h : (Fin (n + 1) → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (tube (n + 1) Ω))
    (hper : ∀ s ∈ tube (n + 1) Ω, ∀ m : Fin (n + 1) → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (ν : Fin (n + 1) → ℤ) (i : Fin (n + 1)) (b : Fin (n + 1) → ℝ) (β : ℝ)
    (hseg : ∀ t ∈ Set.uIcc (b i) β, Function.update b i t ∈ Ω) (y : Fin n → ℝ) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
        fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) + (b k : ℂ) * Complex.I) =
      ∫ t in Set.Ioc (0 : ℝ) 1,
        fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) +
          (Function.update b i β k : ℂ) * Complex.I) := by
  set base : Fin (n + 1) → ℂ :=
    fun k => ((i.insertNth (0 : ℝ) y : Fin (n + 1) → ℝ) k : ℂ) + (b k : ℂ) * Complex.I
  set P : ℂ → Fin (n + 1) → ℂ := fun z k => if k = i then z else base k with hPdef
  have hP : ∀ t c : ℝ, (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) +
      (Function.update b i c k : ℂ) * Complex.I) = P (t + c * Complex.I) := by
    intro t c
    funext k
    by_cases hk : k = i
    · subst hk
      simp [P]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      simp [P, base, hk]
  have hb : Function.update b i (b i) = b := Function.update_eq_self i b
  have hPim : ∀ z : ℂ, (fun k => (P z k).im) = Function.update b i z.im := by
    intro z
    funext k
    by_cases hk : k = i
    · subst hk
      simp [P]
    · simp [P, base, hk]
  have hPdiff : Differentiable ℂ P := by
    refine differentiable_pi.2 fun k => ?_
    by_cases hk : k = i
    · simp only [P, hk, if_true]
      exact differentiable_id
    · simp only [P, hk, if_false]
      exact differentiable_const _
  set g : ℂ → ℂ := fun z => fiG h ν (P z) with hgdef
  have hgd : DifferentiableOn ℂ g ([[(0 : ℝ), 1]] ×ℂ [[b i, β]]) := by
    refine (fiG_differentiableOn hh ν).comp hPdiff.differentiableOn ?_
    intro z hz
    show (fun k => (P z k).im) ∈ Ω
    rw [hPim]
    exact hseg _ hz.2
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨0, b i⟩ ⟨1, β⟩ hgd
  dsimp only at hC
  have hv : ∫ y in (b i)..β, g (((1 : ℝ) : ℂ) + y * Complex.I) =
      ∫ y in (b i)..β, g (((0 : ℝ) : ℂ) + y * Complex.I) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    show fiG h ν (P (((1 : ℝ) : ℂ) + t * Complex.I)) = fiG h ν (P (((0 : ℝ) : ℂ) + t * Complex.I))
    have hm : P (((1 : ℝ) : ℂ) + t * Complex.I) = P (((0 : ℝ) : ℂ) + t * Complex.I) +
        fun k => ((Pi.single i (1 : ℤ) : Fin (n + 1) → ℤ) k : ℂ) := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp [P]
        ring
      · simp [P, hk]
    rw [hm]
    apply fiG_periodic hper
    show (fun k => (P _ k).im) ∈ Ω
    rw [hPim]
    have him : ((((0 : ℝ) : ℂ) + t * Complex.I) : ℂ).im = t := by simp
    rw [him]
    exact hseg t ht
  have hh1 : ∫ x in (0 : ℝ)..1, g (x + (b i) * Complex.I) =
      ∫ x in (0 : ℝ)..1, g (x + β * Complex.I) := by
    rw [hv, add_sub_cancel_right, sub_eq_zero] at hC
    exact hC
  have e1 : ∀ t : ℝ, fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) +
      (b k : ℂ) * Complex.I) = g (t + (b i) * Complex.I) := by
    intro t
    have := hP t (b i)
    rw [hb] at this
    simp only [g]
    rw [this]
  have e2 : ∀ t : ℝ, fiG h ν (fun k => ((i.insertNth t y : Fin (n + 1) → ℝ) k : ℂ) +
      (Function.update b i β k : ℂ) * Complex.I) = g (t + β * Complex.I) := by
    intro t
    simp only [g]
    rw [hP]
  simp only [e1, e2]
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  exact hh1

/- English proof (translation)
Establish `hcont : ∀ d ∈ Ω, Continuous (fun x : Fin (n + 1) → ℝ => fiG h ν (fun k => (x k : ℂ) + (d k : ℂ) * Complex.I))`. Introduce `d hd`. Use `(fiG_differentiableOn hh ν).continuousOn.comp_continuous (by fun_prop) (fun x => ?_)` and prove the remaining obligations. Use `show (fun k => ((x k : ℂ) + (d k : ℂ) * Complex.I).im) ∈ Ω`. Simplify using `using hd`.

Establish `hc : c ∈ Ω` using `by simpa using hseg (c a) Set.left_mem_uIcc`. Establish `hc' : Function.update c a β ∈ Ω` using `hseg β Set.right_mem_uIcc`. Rewrite using `[fourCoeff_eq_fiG, fourCoeff_eq_fiG, fiBox_slices a _ (hcont c hc), fiBox_slices a _ (hcont _ hc')]`. Use `congr 1 with y`. Conclude with `fiSlice_eq hh hper ν a c β hseg y`.
-/
lemma fiStep_eq {n : ℕ} {Ω : Set (Fin (n + 1) → ℝ)} {h : (Fin (n + 1) → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (tube (n + 1) Ω))
    (hper : ∀ s ∈ tube (n + 1) Ω, ∀ m : Fin (n + 1) → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (ν : Fin (n + 1) → ℤ) (c : Fin (n + 1) → ℝ) (a : Fin (n + 1)) (β : ℝ)
    (hseg : ∀ t ∈ Set.uIcc (c a) β, Function.update c a t ∈ Ω) :
    fourCoeff h c ν = fourCoeff h (Function.update c a β) ν := by
  have hcont : ∀ d ∈ Ω, Continuous (fun x : Fin (n + 1) → ℝ =>
      fiG h ν (fun k => (x k : ℂ) + (d k : ℂ) * Complex.I)) := by
    intro d hd
    refine (fiG_differentiableOn hh ν).continuousOn.comp_continuous (by fun_prop) (fun x => ?_)
    show (fun k => ((x k : ℂ) + (d k : ℂ) * Complex.I).im) ∈ Ω
    simpa using hd
  have hc : c ∈ Ω := by simpa using hseg (c a) Set.left_mem_uIcc
  have hc' : Function.update c a β ∈ Ω := hseg β Set.right_mem_uIcc
  rw [fourCoeff_eq_fiG, fourCoeff_eq_fiG, fiBox_slices a _ (hcont c hc),
    fiBox_slices a _ (hcont _ hc')]
  congr 1 with y
  exact fiSlice_eq hh hper ν a c β hseg y

/- English proof (translation)
Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.1 hΩ b hb`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Establish `key : ∀ s : Finset (Fin (n + 1)), ∀ c ∈ Metric.ball b r, (∀ i ∉ s, c i = b i) → fourCoeff h c ν = fourCoeff h b ν`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty`. Introduce `c _ hc`. Establish `: c = b` using `funext fun i => hc i (Finset.notMem_empty i)`. Rewrite using `[this]`. Consider the case `insert a s ha ih`.

Introduce `c hcb hc`. Establish `hcb'` using `hcb`. Rewrite `hcb'` using `[Metric.mem_ball, dist_pi_lt_iff hr]`. Use `set c' := Function.update c a (b a) with hc'def`. Establish `hc'b : c' ∈ Metric.ball b r`.

Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hr]`. Introduce `i`. Distinguish the cases in `hi : i = a`. Substitute `hi` using the available equality. Simplify using `[c', hr]`.

Simplify using `[c', Function.update_of_ne hi, hcb' i]`. Establish `hc'off : ∀ i ∉ s, c' i = b i`. Introduce `i hi`. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality.

Simplify using `[c']`. Simplify using `only [c', Function.update_of_ne hia]`. Conclude with `hc i (by simp [hia, hi])`. Establish `hseg : ∀ t ∈ Set.uIcc (c' a) (c a), Function.update c' a t ∈ Ω`. Introduce `t ht`.

Apply `hball` to reduce the goal to its premises. Establish `hca : c' a = b a` using `by simp [c']`. Rewrite `ht` using `[hca]`. Rewrite using `[Metric.mem_ball, dist_pi_lt_iff hr]`. Introduce `i`.

Distinguish the cases in `hi : i = a`. Substitute `hi` using the available equality. Simplify using `only [Function.update_self]`. Use `hcb' i` as an intermediate fact. Rewrite `this`, the goal using `[Real.dist_eq]`.

Rewrite `this`, the goal using `[abs_lt]`. Apply the tactic sequence `rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith`. Simplify using `[c', Function.update_of_ne hi, hcb' i]`. Establish `e : Function.update c' a (c a) = c` using `by simp [c']`. Rewrite using `[← ih c' hc'b hc'off, fiStep_eq hh hper ν c' a (c a) hseg, e]`.

Introduce `c hc`. Conclude with `key Finset.univ c hc (by simp)`.
-/
lemma fiBall_const {n : ℕ} {Ω : Set (Fin (n + 1) → ℝ)} {h : (Fin (n + 1) → ℂ) → ℂ}
    (hΩ : IsOpen Ω) (hh : DifferentiableOn ℂ h (tube (n + 1) Ω))
    (hper : ∀ s ∈ tube (n + 1) Ω, ∀ m : Fin (n + 1) → ℤ, h (s + fun k => (m k : ℂ)) = h s)
    (ν : Fin (n + 1) → ℤ) (b : Fin (n + 1) → ℝ) (hb : b ∈ Ω) :
    ∃ r > 0, ∀ c ∈ Metric.ball b r, fourCoeff h c ν = fourCoeff h b ν := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ b hb
  refine ⟨r, hr, ?_⟩
  have key : ∀ s : Finset (Fin (n + 1)), ∀ c ∈ Metric.ball b r, (∀ i ∉ s, c i = b i) →
      fourCoeff h c ν = fourCoeff h b ν := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro c _ hc
      have : c = b := funext fun i => hc i (Finset.notMem_empty i)
      rw [this]
    | insert a s ha ih =>
      intro c hcb hc
      have hcb' := hcb
      rw [Metric.mem_ball, dist_pi_lt_iff hr] at hcb'
      set c' := Function.update c a (b a) with hc'def
      have hc'b : c' ∈ Metric.ball b r := by
        rw [Metric.mem_ball, dist_pi_lt_iff hr]
        intro i
        by_cases hi : i = a
        · subst hi
          simp [c', hr]
        · simp [c', Function.update_of_ne hi, hcb' i]
      have hc'off : ∀ i ∉ s, c' i = b i := by
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp [c']
        · simp only [c', Function.update_of_ne hia]
          exact hc i (by simp [hia, hi])
      have hseg : ∀ t ∈ Set.uIcc (c' a) (c a), Function.update c' a t ∈ Ω := by
        intro t ht
        apply hball
        have hca : c' a = b a := by simp [c']
        rw [hca] at ht
        rw [Metric.mem_ball, dist_pi_lt_iff hr]
        intro i
        by_cases hi : i = a
        · subst hi
          simp only [Function.update_self]
          have := hcb' i
          rw [Real.dist_eq] at this ⊢
          rw [abs_lt] at this ⊢
          rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
        · simp [c', Function.update_of_ne hi, hcb' i]
      have e : Function.update c' a (c a) = c := by simp [c']
      rw [← ih c' hc'b hc'off, fiStep_eq hh hper ν c' a (c a) hseg, e]
  intro c hc
  exact key Finset.univ c hc (by simp)

/- English proof (translation)
Introduce `Ω h hΩ hpre hh hper b hb b' hb' ν`. Consider the cases of `f with`. Consider the case `zero => rw [Subsingleton.elim b b']`. Consider the case `succ n => classical`. Set `F : (Fin (n + 1) → ℝ) → Bool` to `fun c => decide (fourCoeff h c ν = fourCoeff h b ν)`.

Establish `hF : ContinuousOn F Ω`. Introduce `c hc`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Take `⟨r, hr, hrc⟩` from `fiBall_const hΩ hh hper ν c hc`. Establish `hev : (fun _ => F c) =ᶠ[𝓝 c] F` using `by filter_upwards [Metric.ball_mem_nhds c hr] with d hd`.

Simplify using `only [F, hrc d hd]`. Conclude with `continuousAt_const.congr hev`. Establish `hcst : F b = F b'` using `hpre.constant hF hb hb'`. Establish `hb'eq : F b' = true`. Rewrite using `[← hcst]`.

Simplify using `[F]`. Simplify `hb'eq` using `[F, eq_comm]`.
-/
theorem four_indep (f : ℕ) : FOURIndepStatement f := by
  intro Ω h hΩ hpre hh hper b hb b' hb' ν
  cases f with
  | zero => rw [Subsingleton.elim b b']
  | succ n =>
    classical
    let F : (Fin (n + 1) → ℝ) → Bool := fun c => decide (fourCoeff h c ν = fourCoeff h b ν)
    have hF : ContinuousOn F Ω := by
      intro c hc
      apply ContinuousAt.continuousWithinAt
      obtain ⟨r, hr, hrc⟩ := fiBall_const hΩ hh hper ν c hc
      have hev : (fun _ => F c) =ᶠ[𝓝 c] F := by
        filter_upwards [Metric.ball_mem_nhds c hr] with d hd
        simp only [F, hrc d hd]
      exact continuousAt_const.congr hev
    have hcst : F b = F b' := hpre.constant hF hb hb'
    have hb'eq : F b' = true := by
      rw [← hcst]
      simp [F]
    simpa [F, eq_comm] using hb'eq

end

end ReciprocityTheory.L2DbarEstimates.Y
