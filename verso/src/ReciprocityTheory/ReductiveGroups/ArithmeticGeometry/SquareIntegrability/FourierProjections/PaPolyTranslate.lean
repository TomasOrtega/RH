import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaUContinuous

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

/- English proof (translation)
Simplify using `[paMono, paPF, MvPolynomial.eval_monomial, Finsupp.prod_pow]`.
-/
theorem paMono_eq (α : ι →₀ ℕ) (v : EuclideanSpace ℂ ι) : paMono α v = ∏ i, v i ^ α i := by
  simp [paMono, paPF, MvPolynomial.eval_monomial, Finsupp.prod_pow]

def jRot (j : ι) (u : Circle) : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = j then rotation u else LinearIsometryEquiv.refl ℝ ℂ)

/- English proof (translation)
Apply the tactic sequence `by_cases h : i = j <;> simp [jRot, h, rotation_apply]`.
-/
theorem jRot_apply (j : ι) (u : Circle) (z : EuclideanSpace ℂ ι) (i : ι) :
    jRot j u z i = (if i = j then (u : ℂ) else 1) * z i := by
  by_cases h : i = j <;> simp [jRot, h, rotation_apply]

/- English proof (translation)
Rewrite using `[paMono_eq, paMono_eq]`. Simplify using `only [jRot_apply, mul_pow, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`.
-/
theorem paMono_rot (α : ι →₀ ℕ) (j : ι) (u : Circle) (z : EuclideanSpace ℂ ι) :
    paMono α (jRot j u z) = (u : ℂ) ^ (α j) * paMono α z := by
  rw [paMono_eq, paMono_eq]
  simp only [jRot_apply, mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, α j ≠ β j := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (Finsupp.ext hc)`. Establish `hab : ((α j : ℝ) - β j) ≠ 0` using `sub_ne_zero.mpr (by exact_mod_cast hj)`.

Take `⟨θ, hθ⟩ : ∃ θ : ℝ, ((α j : ℝ) - β j) * θ = Real.pi` from `⟨Real.pi / ((α j : ℝ) - β j), by field_simp⟩`. Establish `hc : ((α j : ℂ) - β j) * θ = Real.pi` using `by exact_mod_cast hθ`. Establish `hfac : ((Circle.exp θ : Circle) : ℂ) ^ (α j) * (starRingEnd ℂ) (((Circle.exp θ : Circle) : ℂ) ^ (β j)) = -1`. Rewrite using `[Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_pi_mul_I]`. Use `congr 1`.

Rewrite using `[map_mul, Complex.conj_ofReal, Complex.conj_I]`. Take the linear combination `I * hc`. Establish `hw : ∀ v, paW q (jRot j (Circle.exp θ) v) = paW q v`. Introduce `v`. Simplify using `only [paW, LinearIsometryEquiv.norm_map]`.

Establish `key : ∀ v, paMono α (jRot j (Circle.exp θ) v) * (starRingEnd ℂ) (paMono β (jRot j (Circle.exp θ) v)) * (paW q (jRot j (Circle.exp θ) v) : ℂ) = -(paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ))`. Introduce `v`. Rewrite using `[paMono_rot, paMono_rot, hw, map_mul]`. Take the linear combination `(paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) * hfac`. Establish `hI : paIP q (paMono α) (paMono β) = -paIP q (paMono α) (paMono β)`.

Unfold `paIP`. Rewrite using `[← integral_neg]`. Use `conv_lhs =>`. Rewrite using `[← ((jRot j (Circle.exp θ)).measurePreserving).integral_comp (jRot j (Circle.exp θ)).toHomeomorph.measurableEmbedding]`. Use `congr 1`.

Use function extensionality and compare the values at `v`. Conclude with `key v`. Take the linear combination `hI / 2`.
-/
theorem gaussianInner_monomial_orthogonal (q : ℕ) {α β : ι →₀ ℕ} (h : α ≠ β) : paIP q (paMono α) (paMono β) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext hc)
  have hab : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ((α j : ℝ) - β j) * θ = Real.pi :=
    ⟨Real.pi / ((α j : ℝ) - β j), by field_simp⟩
  have hc : ((α j : ℂ) - β j) * θ = Real.pi := by exact_mod_cast hθ
  have hfac : ((Circle.exp θ : Circle) : ℂ) ^ (α j) *
      (starRingEnd ℂ) (((Circle.exp θ : Circle) : ℂ) ^ (β j)) = -1 := by
    rw [Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add, ← Complex.exp_pi_mul_I]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination I * hc
  have hw : ∀ v, paW q (jRot j (Circle.exp θ) v) = paW q v := by
    intro v
    simp only [paW, LinearIsometryEquiv.norm_map]
  have key : ∀ v, paMono α (jRot j (Circle.exp θ) v) * (starRingEnd ℂ) (paMono β (jRot j (Circle.exp θ) v)) *
      (paW q (jRot j (Circle.exp θ) v) : ℂ) = -(paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) := by
    intro v
    rw [paMono_rot, paMono_rot, hw, map_mul]
    linear_combination (paMono α v * (starRingEnd ℂ) (paMono β v) * (paW q v : ℂ)) * hfac
  have hI : paIP q (paMono α) (paMono β) = -paIP q (paMono α) (paMono β) := by
    unfold paIP
    rw [← integral_neg]
    conv_lhs =>
      rw [← ((jRot j (Circle.exp θ)).measurePreserving).integral_comp
        (jRot j (Circle.exp θ)).toHomeomorph.measurableEmbedding]
    congr 1
    funext v
    exact key v
  linear_combination hI / 2

/- English proof (translation)
Unfold `Finsupp.degree`. Distinguish the cases in `h : i ∈ α.support`. Conclude with `Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) h`. Establish `h0 : α i = 0` using `by simpa [Finsupp.mem_support_iff] using h`. Rewrite using `[h0]`.

Conclude with `Nat.zero_le _`.
-/
private lemma finsupp_apply_le_degree (α : ι →₀ ℕ) (i : ι) : α i ≤ α.degree := by
  unfold Finsupp.degree
  by_cases h : i ∈ α.support
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) h
  · have h0 : α i = 0 := by simpa [Finsupp.mem_support_iff] using h
    rw [h0]
    exact Nat.zero_le _

/- English proof (translation)
Simplify using `only [paS, Finset.mem_filter, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range, Equiv.coe_toEmbedding]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h⟩`. Conclude with `h`. Introduce `h`.

Use `⟨⟨α, fun i => ?_, ?_⟩, h⟩` and prove the remaining obligations. Use `finsupp_apply_le_degree α i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
private lemma mem_paS' {c : ℕ} {α : ι →₀ ℕ} : α ∈ paS (ι := ι) c ↔ α.degree ≤ c := by
  simp only [paS, Finset.mem_filter, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨⟨α, fun i => ?_, ?_⟩, h⟩
    · have := finsupp_apply_le_degree α i
      omega
    · simp

/- English proof (translation)
Unfold `Finsupp.degree`. Conclude with `Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)`.
-/
private lemma finsupp_degree_eq_sum (α : ι →₀ ℕ) : α.degree = ∑ i, α i := by
  unfold Finsupp.degree
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)

/- English proof (translation)
Unfold `paPoly`. Conclude with `Submodule.subset_span ⟨α, mem_paS'.mpr h, rfl⟩`.
-/
private lemma paMono_mem_paPoly_of_degree_le {c : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ c) :
    paMono α ∈ paPoly (ι := ι) c := by
  unfold paPoly
  exact Submodule.subset_span ⟨α, mem_paS'.mpr h, rfl⟩

/- English proof (translation)
Unfold `paPoly`. Apply `Submodule.span_mono` to reduce the goal to its premises. Apply `Set.image_mono` to reduce the goal to its premises. Introduce `γ hγ`. Conclude with `mem_paS'.mpr (le_trans (mem_paS'.mp hγ) (by exact_mod_cast h))`.
-/
theorem paPoly_mono {c d : ℕ} (h : c ≤ d) : paPoly (ι := ι) c ≤ paPoly d := by
  unfold paPoly
  apply Submodule.span_mono
  apply Set.image_mono
  intro γ hγ
  exact mem_paS'.mpr (le_trans (mem_paS'.mp hγ) (by exact_mod_cast h))

/- English proof (translation)
Unfold `paPoly at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨α, _, rfl⟩` from `hx`. Establish `he : paMono α = fun v : EuclideanSpace ℂ ι => ∏ i, v i ^ α i` using `funext (paMono_eq α)`.

Rewrite using `[he]`. Conclude with `contDiff_prod fun i _ => ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff).pow (α i)`. Consider the case `zero => exact contDiff_const`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `smul a x _ hx => exact hx.const_smul a`.
-/
theorem paPoly_contDiff {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ContDiff ℂ (⊤ : ℕ∞) F := by
  unfold paPoly at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, _, rfl⟩ := hx
    have he : paMono α = fun v : EuclideanSpace ℂ ι => ∏ i, v i ^ α i := funext (paMono_eq α)
    rw [he]
    exact contDiff_prod fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff).pow (α i)
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

/- English proof (translation)
Use function extensionality and compare the values at `v`. Simplify using `only [Pi.mul_apply, paMono_eq, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]`.
-/
private lemma paMono_mul (α β : ι →₀ ℕ) :
    paMono α * paMono β = paMono (ι := ι) (α + β) := by
  funext v
  simp only [Pi.mul_apply, paMono_eq, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

/- English proof (translation)
Unfold `paPoly at hF hG ⊢`. Establish `hm` using `Submodule.mul_mem_mul hF hG`. Rewrite `hm` using `[Submodule.span_mul_span]`. Use `Submodule.span_le.mpr (Set.mul_subset_iff.mpr ?_) hm` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩`.

Rewrite using `[paMono_mul]`. Use `Submodule.subset_span ⟨α + β, mem_paS'.mpr ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `add_le_add (mem_paS'.mp hα) (mem_paS'.mp hβ)`.
-/
theorem paPoly_mul {c d : ℕ} {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (hG : G ∈ paPoly d) :
    F * G ∈ paPoly (c + d) := by
  unfold paPoly at hF hG ⊢
  have hm := Submodule.mul_mem_mul hF hG
  rw [Submodule.span_mul_span] at hm
  refine Submodule.span_le.mpr (Set.mul_subset_iff.mpr ?_) hm
  rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
  rw [paMono_mul]
  refine Submodule.subset_span ⟨α + β, mem_paS'.mpr ?_, rfl⟩
  rw [map_add]
  exact add_le_add (mem_paS'.mp hα) (mem_paS'.mp hβ)

/- English proof (translation)
Establish `h1 : paMono (0 : ι →₀ ℕ) = fun _ : EuclideanSpace ℂ ι => (1 : ℂ)`. Use function extensionality and compare the values at `v`. Simplify using `[paMono_eq]`. Establish `h2 : (fun _ : EuclideanSpace ℂ ι => a) = a • paMono (0 : ι →₀ ℕ)`. Rewrite using `[h1]`.

Use function extensionality and compare the values at `v`. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ a (paMono_mem_paPoly_of_degree_le (by simp))`.
-/
theorem paPoly_const (a : ℂ) : (fun _ : EuclideanSpace ℂ ι => a) ∈ paPoly 0 := by
  have h1 : paMono (0 : ι →₀ ℕ) = fun _ : EuclideanSpace ℂ ι => (1 : ℂ) := by
    funext v
    simp [paMono_eq]
  have h2 : (fun _ : EuclideanSpace ℂ ι => a) = a • paMono (0 : ι →₀ ℕ) := by
    rw [h1]
    funext v
    simp
  rw [h2]
  exact Submodule.smul_mem _ a (paMono_mem_paPoly_of_degree_le (by simp))

/- English proof (translation)
Establish `h1 : (fun v : EuclideanSpace ℂ ι => v i) = paMono (Finsupp.single i 1)`. Use function extensionality and compare the values at `v`. Rewrite using `[paMono_eq, Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Finsupp.single_apply, hb, Ne.symm hb]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`. Rewrite using `[h1]`. Conclude with `paMono_mem_paPoly_of_degree_le (le_of_eq (by rw [finsupp_degree_eq_sum]; simp [Finsupp.single_apply]))`.
-/
theorem paPoly_coord (i : ι) : (fun v : EuclideanSpace ℂ ι => v i) ∈ paPoly 1 := by
  have h1 : (fun v : EuclideanSpace ℂ ι => v i) = paMono (Finsupp.single i 1) := by
    funext v
    rw [paMono_eq, Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb, Ne.symm hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [h1]
  exact paMono_mem_paPoly_of_degree_le (le_of_eq (by rw [finsupp_degree_eq_sum]; simp [Finsupp.single_apply]))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, zero_mul]`. Conclude with `paPoly_const 1`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, add_mul, one_mul]`. Conclude with `paPoly_mul ih hF`.
-/
theorem paPoly_pow {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (n : ℕ) :
    F ^ n ∈ paPoly (n * c) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul]
    exact paPoly_const 1
  | succ n ih =>
    rw [pow_succ, add_mul, one_mul]
    exact paPoly_mul ih hF

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Finset.sum_empty]`. Conclude with `paPoly_const (ι := ι) 1`. Consider the case `@insert j s hj ih`.

Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj]`. Conclude with `paPoly_mul (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
private lemma prod_mem_paPoly (s : Finset ι) (f : ι → EuclideanSpace ℂ ι → ℂ) (d : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ paPoly (ι := ι) (d i)) : (∏ i ∈ s, f i) ∈ paPoly (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact paPoly_const (ι := ι) 1
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact paPoly_mul (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Unfold `paPoly at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨α, hα, rfl⟩` from `hx`. Establish `hdeg` using `mem_paS'.mp hα`.

Establish `he : (fun v => paMono α (v - a)) = ∏ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ^ (α i)`. Use function extensionality and compare the values at `v`. Simplify using `[paMono_eq, Finset.prod_apply]`. Rewrite using `[he]`. Establish `hi : ∀ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ∈ paPoly (ι` using `ι) 1 := fun i => Submodule.sub_mem _ (paPoly_coord i) (paPoly_mono (Nat.zero_le 1) (paPoly_const (a i)))`.

Establish `hle : ∑ i, α i * 1 ≤ c`. Rewrite `hdeg` using `[finsupp_degree_eq_sum]`. Simplify using `using hdeg`. Conclude with `paPoly_mono hle (prod_mem_paPoly Finset.univ _ (fun i => α i * 1) fun i _ => paPoly_pow (hi i) (α i))`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `smul b x _ hx => exact Submodule.smul_mem _ b hx`.
-/
theorem paPoly_translate {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (a : EuclideanSpace ℂ ι) : (fun v => F (v - a)) ∈ paPoly c := by
  unfold paPoly at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hdeg := mem_paS'.mp hα
    have he : (fun v => paMono α (v - a)) =
        ∏ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ^ (α i) := by
      funext v
      simp [paMono_eq, Finset.prod_apply]
    rw [he]
    have hi : ∀ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ∈ paPoly (ι := ι) 1 :=
      fun i => Submodule.sub_mem _ (paPoly_coord i) (paPoly_mono (Nat.zero_le 1) (paPoly_const (a i)))
    have hle : ∑ i, α i * 1 ≤ c := by
      rw [finsupp_degree_eq_sum] at hdeg
      simpa using hdeg
    exact paPoly_mono hle (prod_mem_paPoly Finset.univ _ (fun i => α i * 1)
      fun i _ => paPoly_pow (hi i) (α i))
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul b x _ hx => exact Submodule.smul_mem _ b hx

/- English proof (translation)
Establish `h1 : (fun v : EuclideanSpace ℂ ι => Hf v a) = ∑ i, (starRingEnd ℂ) (a i) • (fun v : EuclideanSpace ℂ ι => v i)`. Use function extensionality and compare the values at `v`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Hf, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.

Rewrite using `[h1]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (paPoly_coord i)`.
-/
theorem paPoly_Hf (a : EuclideanSpace ℂ ι) : (fun v : EuclideanSpace ℂ ι => Hf v a) ∈ paPoly 1 := by
  have h1 : (fun v : EuclideanSpace ℂ ι => Hf v a) =
      ∑ i, (starRingEnd ℂ) (a i) • (fun v : EuclideanSpace ℂ ι => v i) := by
    funext v
    rw [Finset.sum_apply]
    simp only [Hf, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (paPoly_coord i)

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
