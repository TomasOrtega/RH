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
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
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
Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma fiG_differentiableOn {f : ℕ} {Ω : Set (Fin f → ℝ)} {h : (Fin f → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (tube f Ω)) (ν : Fin f → ℤ) :
    DifferentiableOn ℂ (fiG h ν) (tube f Ω) := by
  have hd : Differentiable ℂ
      (fun s : Fin f → ℂ => Complex.exp (-2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * s k)) := by
    fun_prop
  exact hh.mul hd.differentiableOn

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify by unfolding definitions. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
