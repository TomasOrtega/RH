import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KsetMulConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using SmDerA.inG_zero ε`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `smc_inG_add (smc_inG_rsmul (hX a (Finset.mem_insert_self a s)) (r a)) (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))`.
-/
theorem inG_rsum {ι : Type*} (s : Finset ι) (r : ι → ℝ) (X : ι → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i ∈ s, inG ε (X i)) : inG ε (∑ i ∈ s, (r i : ℂ) • X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmDerA.inG_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact smc_inG_add (smc_inG_rsmul (hX a (Finset.mem_insert_self a s)) (r a))
      (ih fun i hi => hX i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using SmDerA.dS_zero_mat (σ := σ) v`. Consider the case `insert a s ha ih`. Establish `hs : ∀ i ∈ s, inG ε (X i)` using `fun i hi => hX i (Finset.mem_insert_of_mem hi)`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, add_comm, dS_add_smul hσ (inG_rsum s r X hs) (hX a (Finset.mem_insert_self a s)) (r a) hv, ih hs, add_comm]`.
-/
theorem dS_rsum (hσ : IsURepOn (UJset ε) σ) {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (X : ι → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ i ∈ s, inG ε (X i)) {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ (∑ i ∈ s, (r i : ℂ) • X i) v = ∑ i ∈ s, (r i : ℂ) • dS σ (X i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SmDerA.dS_zero_mat (σ := σ) v
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, inG ε (X i) := fun i hi => hX i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, dS_add_smul hσ (inG_rsum s r X hs)
      (hX a (Finset.mem_insert_self a s)) (r a) hv, ih hs, add_comm]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using dS_smul_vec (σ := σ) 0 X 0`. Consider the case `insert a s ha ih`. Establish `hs : ∀ i ∈ s, IsSmoothVecU ε σ (v i)` using `fun i hi => hv i (Finset.mem_insert_of_mem hi)`. Establish `hsum : IsSmoothVecU ε σ (∑ i ∈ s, c i • v i)` using `by clear ih`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (isSmoothVecU_zero : IsSmoothVecU ε σ (0 : H))`. Consider the case `insert b t hb ih2`. Rewrite using `[Finset.sum_insert hb]`. Conclude with `((hs b (Finset.mem_insert_self b t)).smul (c b)).add (ih2 (fun h => ha (Finset.mem_insert_of_mem h)) (fun i hi => hv i (by`.

Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `Finset.mem_insert_self _ _`. Conclude with `Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)))`. Use the proof step `(fun i hi => hs i (Finset.mem_insert_of_mem hi)))`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, dS_add_vec hσ hX ((hv a (Finset.mem_insert_self a s)).smul _) hsum, dS_smul_vec, ih hs]`.
-/
theorem dS_vsum (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → H) (hv : ∀ i ∈ s, IsSmoothVecU ε σ (v i)) :
    dS σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dS σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dS_smul_vec (σ := σ) 0 X 0
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsSmoothVecU ε σ (v i) := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hsum : IsSmoothVecU ε σ (∑ i ∈ s, c i • v i) := by
      clear ih
      induction s using Finset.induction_on with
      | empty => simpa using (isSmoothVecU_zero : IsSmoothVecU ε σ (0 : H))
      | insert b t hb ih2 =>
        rw [Finset.sum_insert hb]
        exact ((hs b (Finset.mem_insert_self b t)).smul (c b)).add
          (ih2 (fun h => ha (Finset.mem_insert_of_mem h)) (fun i hi => hv i (by
            rcases Finset.mem_insert.1 hi with rfl | hi
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)))
            (fun i hi => hs i (Finset.mem_insert_of_mem hi)))
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dS_add_vec hσ hX ((hv a (Finset.mem_insert_self a s)).smul _)
      hsum, dS_smul_vec, ih hs]

/- English proof (translation)
Establish `hY1 : S7.cpart1 ε Y = Y` using `((smc_cpart Y).2.2.2 hY).1`. Use `set L : Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ := { toFun := S7.cpart1 ε, map_zero' := by simpa using smc_cpart1_real (ε := ε) 0 0, map_add' := smc_cpart1_add }`. Establish `hdec : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • Matrix.single p.1 p.2 1 + ((Y p.1 p.2).im : ℂ) • (Complex.I • Matrix.single p.1 p.2 1))` using `by conv_lhs => rw [Matrix.matrix_eq_sum_single Y]`. Rewrite using `[← Finset.univ_product_univ, Finset.sum_product]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[smul_smul, ← add_smul, Complex.re_add_im, Matrix.smul_single, smul_eq_mul, mul_one]`. Establish `h2 : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • S7.cpart1 ε (Matrix.single p.1 p.2 1) + ((-(Y p.1 p.2).im : ℝ) : ℂ) • S7.cpart2 ε (Matrix.single p.1 p.2 1))` using `by conv_lhs => rw [← hY1, hdec]`. Express the relevant statement in the definitionally equal form `L (∑ p : Fin n × Fin n, _) = _`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `S7.cpart1 ε _ = _`. Rewrite using `[smc_cpart1_add, smc_cpart1_real, smc_cpart1_real, smc_cpart1_I, Complex.ofReal_neg, smul_neg, neg_smul]`. Rewrite using `[Fintype.sum_prod_type]`. Use `conv_lhs => rw [h2]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool]`. Simplify using `only [cond_true, cond_false]`.
-/
theorem inG_expand {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) :
    Y = ∑ p : (Fin n × Fin n) × Bool, ((cond p.2 (Y p.1.1 p.1.2).re (-(Y p.1.1 p.1.2).im) : ℝ) : ℂ) •
      cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1)) := by
  classical
  have hY1 : S7.cpart1 ε Y = Y := ((smc_cpart Y).2.2.2 hY).1
  set L : Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ :=
    { toFun := S7.cpart1 ε, map_zero' := by simpa using smc_cpart1_real (ε := ε) 0 0,
      map_add' := smc_cpart1_add }
  have hdec : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • Matrix.single p.1 p.2 1 +
      ((Y p.1 p.2).im : ℂ) • (Complex.I • Matrix.single p.1 p.2 1)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    rw [smul_smul, ← add_smul, Complex.re_add_im, Matrix.smul_single, smul_eq_mul, mul_one]
  have h2 : Y = ∑ p : Fin n × Fin n, (((Y p.1 p.2).re : ℂ) • S7.cpart1 ε (Matrix.single p.1 p.2 1) +
      ((-(Y p.1 p.2).im : ℝ) : ℂ) • S7.cpart2 ε (Matrix.single p.1 p.2 1)) := by
    conv_lhs => rw [← hY1, hdec]
    change L (∑ p : Fin n × Fin n, _) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    change S7.cpart1 ε _ = _
    rw [smc_cpart1_add, smc_cpart1_real, smc_cpart1_real, smc_cpart1_I, Complex.ofReal_neg, smul_neg, neg_smul]
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [h2]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_bool]
  simp only [cond_true, cond_false]

def FinCont (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (z : S7.KG ε → H) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → S7.KG ε → ℂ) (v : ι → H),
    (∀ i, Continuous (d i)) ∧ (∀ i, IsSmoothVecU ε σ (v i)) ∧ ∀ k, z k = ∑ i, d i k • v i

/- English proof (translation)
Take `⟨ι, _, d, v, hd, hv, hz⟩` from `hz`. Use `set Y : S7.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => (S7.toMK k)ᴴ * X * S7.toMK k`. Establish `hYc : Continuous Y`. Establish `hc` using `S7.IdA.continuous_toMK (ε := ε)`. Conclude with `(hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc`.

Establish `hYg : ∀ k, inG ε (Y k)` using `fun k => inG_conj_K k.2 hX`. Use `set B : (Fin n × Fin n) × Bool → Matrix (Fin n) (Fin n) ℂ := fun p => cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1))`. Establish `hB : ∀ p, inG ε (B p)`. Introduce and unpack `⟨q, _ | _⟩`. Conclude with `(smc_cpart _).2.1`.

Conclude with `(smc_cpart _).1`. Use `set r : S7.KG ε → (Fin n × Fin n) × Bool → ℝ := fun k p => cond p.2 (Y k p.1.1 p.1.2).re (-(Y k p.1.1 p.1.2).im)`. Use `⟨ι × ((Fin n × Fin n) × Bool), inferInstance, fun q k => d q.1 k * (r k q.2 : ℂ), fun q => dS σ (B q.2) (v q.1), fun q => ?_, fun q => dS_smooth hσ (hB q.2) (hv q.1), fun k => ?_⟩` and prove the remaining obligations. Use `(hd q.1).mul (Complex.continuous_ofReal.comp ?_)` and prove the remaining obligations. Establish `hent : Continuous fun k => Y k q.2.1.1 q.2.1.2` using `(continuous_apply q.2.1.2).comp ((continuous_apply q.2.1.1).comp hYc)`.

Break down `q with ⟨i, q, _ | _⟩` into its components or cases. Conclude with `(Complex.continuous_im.comp hent).neg`. Conclude with `Complex.continuous_re.comp hent`. Use `show dS σ (Y k) (z k) = _`. Rewrite using `[hz k, dS_vsum hσ (hYg k) _ _ _ fun i _ => hv i, Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [inG_expand (hYg k)]`. Rewrite using `[dS_rsum hσ _ _ _ (fun p _ => hB p) (hv i), Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [r]`.

Rewrite using `[smul_smul, mul_comm]`.
-/
theorem finCont_step (hσ : IsURepOn (UJset ε) σ) {z : S7.KG ε → H} (hz : FinCont ε σ z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    FinCont ε σ (fun k => dS σ ((S7.toMK k)ᴴ * X * S7.toMK k) (z k)) := by
  classical
  obtain ⟨ι, _, d, v, hd, hv, hz⟩ := hz
  set Y : S7.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => (S7.toMK k)ᴴ * X * S7.toMK k
  have hYc : Continuous Y := by
    have hc := S7.IdA.continuous_toMK (ε := ε)
    exact (hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc
  have hYg : ∀ k, inG ε (Y k) := fun k => inG_conj_K k.2 hX
  set B : (Fin n × Fin n) × Bool → Matrix (Fin n) (Fin n) ℂ := fun p =>
    cond p.2 (S7.cpart1 ε (Matrix.single p.1.1 p.1.2 1)) (S7.cpart2 ε (Matrix.single p.1.1 p.1.2 1))
  have hB : ∀ p, inG ε (B p) := by
    rintro ⟨q, _ | _⟩
    · exact (smc_cpart _).2.1
    · exact (smc_cpart _).1
  set r : S7.KG ε → (Fin n × Fin n) × Bool → ℝ := fun k p =>
    cond p.2 (Y k p.1.1 p.1.2).re (-(Y k p.1.1 p.1.2).im)
  refine ⟨ι × ((Fin n × Fin n) × Bool), inferInstance, fun q k => d q.1 k * (r k q.2 : ℂ),
    fun q => dS σ (B q.2) (v q.1), fun q => ?_, fun q => dS_smooth hσ (hB q.2) (hv q.1), fun k => ?_⟩
  · refine (hd q.1).mul (Complex.continuous_ofReal.comp ?_)
    have hent : Continuous fun k => Y k q.2.1.1 q.2.1.2 :=
      (continuous_apply q.2.1.2).comp ((continuous_apply q.2.1.1).comp hYc)
    rcases q with ⟨i, q, _ | _⟩
    · exact (Complex.continuous_im.comp hent).neg
    · exact Complex.continuous_re.comp hent
  · show dS σ (Y k) (z k) = _
    rw [hz k, dS_vsum hσ (hYg k) _ _ _ fun i _ => hv i, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [inG_expand (hYg k)]
    rw [dS_rsum hσ _ _ _ (fun p _ => hB p) (hv i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only [r]
    rw [smul_smul, mul_comm]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => u, fun _ => continuous_const, fun _ => hu, fun k => by simp [dSW]⟩`. Consider the case `cons X w ih`. Conclude with `finCont_step hσ (ih fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (hw X List.mem_cons_self)`.
-/
theorem finCont_dSW (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {u : H} (hu : IsSmoothVecU ε σ u) :
    FinCont ε σ (fun k => dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u) := by
  induction w with
  | nil => exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => u, fun _ => continuous_const, fun _ => hu,
      fun k => by simp [dSW]⟩
  | cons X w ih =>
    exact finCont_step hσ (ih fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (hw X List.mem_cons_self)

/- English proof (translation)
Take `⟨ι, _, d, v, hd, -, hz⟩` from `finCont_dSW hσ hw hu`. Establish `e : (fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u)) = fun k => ∑ i, d i k • σ (S7.toMK k) (v i)`. Use function extensionality and compare the values at `k`. Rewrite using `[dSW_conj hσ (k := S7.toMK k) k.2 hw hu, show dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u = _ from hz k, map_sum]`. Simplify using `only [map_smul]`.

Rewrite using `[e]`. Use `continuous_finsetSum _ fun i _ => (hd i).smul ?_` and prove the remaining obligations. Conclude with `(hσ.2.2 (v i)).comp_continuous S7.IdA.continuous_toMK fun k => smd_inUJ_of_Kset k.2`.
-/
theorem continuous_dSW_orbit (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)}
    (hw : ∀ X ∈ w, inG ε X) {u : H} (hu : IsSmoothVecU ε σ u) :
    Continuous fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u) := by
  obtain ⟨ι, _, d, v, hd, -, hz⟩ := finCont_dSW hσ hw hu
  have e : (fun k : S7.KG ε => dSW σ w (σ (S7.toMK k) u)) =
      fun k => ∑ i, d i k • σ (S7.toMK k) (v i) := by
    funext k
    rw [dSW_conj hσ (k := S7.toMK k) k.2 hw hu, show dSW σ (w.map fun X => (S7.toMK k)ᴴ * X * S7.toMK k) u = _ from hz k, map_sum]
    simp only [map_smul]
  rw [e]
  refine continuous_finsetSum _ fun i _ => (hd i).smul ?_
  exact (hσ.2.2 (v i)).comp_continuous S7.IdA.continuous_toMK fun k => smd_inUJ_of_Kset k.2
end ReciprocityTheory.ChartRestriction.DS.DecInf
