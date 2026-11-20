import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section VK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Apply the tactic sequence `by_cases h : c = a <;> simp [tensV, prj, h]`.
-/
theorem vk_tensV_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

/- English proof (translation)
Apply the tactic sequence `by_cases h : c = b <;> simp [tensVd, prj, h]`.
-/
theorem vk_tensVd_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

/- English proof (translation)
Simplify using `[eeV, prj, LinearMap.sum_apply]`.
-/
theorem vk_eeV_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `[eeVd, prj, LinearMap.sum_apply]`.
-/
theorem vk_eeVd_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

/- English proof (translation)
Establish `h` using `LinearMap.congr_fun (hE a b c d) x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Apply the tactic sequence `split_ifs at h ⊢ <;> (try simp only [LinearMap.zero_apply, sub_zero, add_zero] at h ⊢) <;> (rw [sub_eq_iff_eq_add] at h; rw [h]; abel)`.
-/
theorem vk_rel (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b c d : Fin n) (x : M) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  have h := LinearMap.congr_fun (hE a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  split_ifs at h ⊢ <;> (try simp only [LinearMap.zero_apply, sub_zero, add_zero] at h ⊢) <;>
    (rw [sub_eq_iff_eq_add] at h; rw [h]; abel)

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun d => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, vk_eeV_apply]`. Establish `h1 : ∀ c, E c d (tensV E a b f c) = E a b (E c d (f c)) + (if d = a then E c b (f c) else 0) - (if b = c then E a d (f c) else 0) + (if c = a then E a d (f b) else 0)`. Introduce `c`. Rewrite using `[vk_tensV_apply, map_add, vk_rel E hE c d a b]`.

Distinguish the cases in `h : c = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[Finset.sum_congr rfl fun c _ => h1 c]`.

Simplify using `only [vk_tensV_apply, vk_eeV_apply, map_sum]`. Distinguish the cases in `hda : d = a`. Substitute `hda` using the available equality. Simplify using `[Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']`. Simplify using `[hda, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']`.
-/
theorem vk_eeV_comm (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    eeV E * tensV E a b = tensV E a b * eeV E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  simp only [Module.End.mul_apply, vk_eeV_apply]
  have h1 : ∀ c, E c d (tensV E a b f c) = E a b (E c d (f c)) + (if d = a then E c b (f c) else 0) -
      (if b = c then E a d (f c) else 0) + (if c = a then E a d (f b) else 0) := by
    intro c
    rw [vk_tensV_apply, map_add, vk_rel E hE c d a b]
    by_cases h : c = a
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  simp only [vk_tensV_apply, vk_eeV_apply, map_sum]
  by_cases hda : d = a
  · subst hda; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp [hda, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun d => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, vk_eeVd_apply]`. Establish `h1 : ∀ c, E d c (tensVd E a b f c) = E a b (E d c (f c)) + (if c = a then E d b (f c) else 0) - (if b = d then E a c (f c) else 0) - (if c = b then E d b (f a) else 0)`. Introduce `c`. Rewrite using `[vk_tensVd_apply, map_sub, vk_rel E hE d c a b]`.

Distinguish the cases in `h : c = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[Finset.sum_congr rfl fun c _ => h1 c]`.

Simplify using `only [vk_tensVd_apply, vk_eeVd_apply, map_sum, map_neg]`. Distinguish the cases in `hdb : d = b`. Substitute `hdb` using the available equality. Simplify using `[Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']`. Normalize the expressions using the abelian group laws.

Establish `hbd : ¬ b = d` using `fun h => hdb h.symm`. Simplify using `[hdb, hbd, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']`.
-/
theorem vk_eeVd_comm (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    eeVd E * tensVd E a b = tensVd E a b * eeVd E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  simp only [Module.End.mul_apply, vk_eeVd_apply]
  have h1 : ∀ c, E d c (tensVd E a b f c) = E a b (E d c (f c)) + (if c = a then E d b (f c) else 0) -
      (if b = d then E a c (f c) else 0) - (if c = b then E d b (f a) else 0) := by
    intro c
    rw [vk_tensVd_apply, map_sub, vk_rel E hE d c a b]
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  simp only [vk_tensVd_apply, vk_eeVd_apply, map_sum, map_neg]
  by_cases hdb : d = b
  · subst hdb
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    abel
  · have hbd : ¬ b = d := fun h => hdb h.symm
    simp [hdb, hbd, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']

end VK

section GenKill

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
The claim follows from `le_sInf fun _ hT => hT.1`.
-/
theorem vk_le_genSub (T : Fin n → Fin n → Module.End ℂ W) (S : Submodule ℂ W) : S ≤ genSub T S :=
  le_sInf fun _ hT => hT.1

/- English proof (translation)
Rewrite `hv`, the goal using `[genSub, Submodule.mem_sInf]`. Introduce `P hP`. Conclude with `hP.2 a b v (hv P hP)`.
-/
theorem vk_genSub_stable (T : Fin n → Fin n → Module.End ℂ W) (S : Submodule ℂ W) (a b : Fin n) (v : W)
    (hv : v ∈ genSub T S) : T a b v ∈ genSub T S := by
  rw [genSub, Submodule.mem_sInf] at hv ⊢
  intro P hP
  exact hP.2 a b v (hv P hP)

/- English proof (translation)
The claim follows from `sInf_le ⟨h.trans (vk_le_genSub T S'), fun a b v hv => vk_genSub_stable T S' a b v hv⟩`.
-/
theorem vk_genSub_mono (T : Fin n → Fin n → Module.End ℂ W) {S S' : Submodule ℂ W} (h : S ≤ S') :
    genSub T S ≤ genSub T S' :=
  sInf_le ⟨h.trans (vk_le_genSub T S'), fun a b v hv => vk_genSub_stable T S' a b v hv⟩

/- English proof (translation)
Introduce `x hx`. Establish `hle : genSub T (Submodule.span ℂ S) ≤ P.comap B`. Use `sInf_le ⟨Submodule.span_le.mpr fun y hy => hS y hy, fun a b v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[Submodule.mem_comap]`. Rewrite using `[← Module.End.mul_apply, hB a b, Module.End.mul_apply]`.

Conclude with `hP a b _ hv`. Conclude with `hle hx`.
-/
theorem vk_genSub_map (T : Fin n → Fin n → Module.End ℂ W) (B : Module.End ℂ W)
    (hB : ∀ a b, B * T a b = T a b * B) (P : Submodule ℂ W) (hP : ∀ a b, ∀ v ∈ P, T a b v ∈ P)
    (S : Set W) (hS : ∀ x ∈ S, B x ∈ P) : ∀ x ∈ genSub T (Submodule.span ℂ S), B x ∈ P := by
  intro x hx
  have hle : genSub T (Submodule.span ℂ S) ≤ P.comap B := by
    refine sInf_le ⟨Submodule.span_le.mpr fun y hy => hS y hy, fun a b v hv => ?_⟩
    rw [Submodule.mem_comap] at hv ⊢
    rw [← Module.End.mul_apply, hB a b, Module.End.mul_apply]
    exact hP a b _ hv
  exact hle hx

/- English proof (translation)
Rewrite using `[sub_mul, mul_sub, hAT, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`.
-/
theorem vk_shift_comm (T : Fin n → Fin n → Module.End ℂ W) (A : Module.End ℂ W)
    (hAT : ∀ a b, A * T a b = T a b * A) (c : ℂ) (a b : Fin n) :
    (A - c • 1) * T a b = T a b * (A - c • 1) := by
  rw [sub_mul, mul_sub, hAT, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/- English proof (translation)
Simplify using `[Algebra.algebraMap_eq_smul_one]`.
-/
theorem vk_aeval_lin (A : Module.End ℂ W) (c : ℂ) : aeval A (X - C c) = A - c • 1 := by
  simp [Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Establish `main : ∀ m k : ℕ, n ≤ k + m → ∀ x ∈ genSub T (Submodule.span ℂ (g '' {d : Fin n | k ≤ (d : ℕ)})), aeval A (∏ t ∈ univ.filter (fun d : Fin n => k ≤ (d : ℕ)), (X - C (θ t))) x = 0`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `k hk x hx`.

Establish `hempty : g '' {d : Fin n | k ≤ (d : ℕ)} = ∅`. Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]`. Introduce `d hd`. Use `d.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite `hx` using `[hempty, Submodule.span_empty]`. Establish `hbot : genSub T ⊥ ≤ ⊥` using `sInf_le ⟨le_refl _, fun a b v hv => by rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero]⟩`. Establish `hx0 : x = 0` using `by simpa using hbot hx`. Rewrite using `[hx0, map_zero]`.

Consider the case `succ m ih`. Introduce `k hk x hx`. Distinguish the cases in `hkn : n ≤ k`. Conclude with `ih k (by omega) x hx`. Use `replace hkn : k < n := not_le.mp hkn`.

Establish `hfil : univ.filter (fun d : Fin n => k ≤ (d : ℕ)) = insert ⟨k, hkn⟩ (univ.filter (fun d : Fin n => k + 1 ≤ (d : ℕ)))`. Use extensionality with `d`. Simplify using `only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hnot : (⟨k, hkn⟩ : Fin n) ∉ univ.filter (fun d : Fin n => k + 1 ≤ (d : ℕ))` using `by simp`.

Rewrite using `[hfil, prod_insert hnot, mul_comm, map_mul, Module.End.mul_apply]`. Apply `ih (k + 1) (by omega)` to reduce the goal to its premises. Rewrite using `[vk_aeval_lin]`. Establish `hmono : ∀ t : Fin n, k ≤ (t : ℕ) → genSub T (Submodule.span ℂ (g '' {d | t < d})) ≤ genSub T (Submodule.span ℂ (g '' {d : Fin n | k + 1 ≤ (d : ℕ)}))`. Introduce `t ht`.

Apply `vk_genSub_mono` to reduce the goal to its premises. Apply `Submodule.span_mono` to reduce the goal to its premises. Apply `Set.image_mono` to reduce the goal to its premises. Introduce `d hd`. Simplify using `only [Set.mem_ofPred_eq, Fin.lt_def] at hd ⊢`.

Use linear arithmetic over natural numbers and integers. Use `vk_genSub_map T _ (vk_shift_comm T A hAT _) _ (vk_genSub_stable T _) _ ?_ x hx` and prove the remaining obligations. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq] at hd`. Break down `eq_or_lt_of_le hd with h | h` into its components or cases.

Establish `hdt : d = ⟨k, hkn⟩` using `Fin.ext h.symm`. Rewrite using `[hdt]`. Conclude with `hmono _ le_rfl (hstep _)`. Establish `e : (A - θ ⟨k, hkn⟩ • 1) (g d) = (A - θ d • 1) (g d) + (θ d - θ ⟨k, hkn⟩) • g d`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_smul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `add_mem (hmono d hd (hstep d)) (Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Conclude with `vk_le_genSub _ _ (Submodule.subset_span ⟨d, h, rfl⟩)`. Introduce `x hx`.

Establish `h0` using `main n 0 (by omega) x (by`. Establish `: g '' {d : Fin n | 0 ≤ (d : ℕ)} = Set.range g`. Rewrite using `[← Set.image_univ]`. Use `congr 1`. Use extensionality with `d`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hx)`. Establish `hf : univ.filter (fun d : Fin n => 0 ≤ (d : ℕ)) = univ` using `by ext d; simp`. Rewrite `h0` using `[hf]`. Then use the resulting hypothesis.
-/
theorem vk_kill (T : Fin n → Fin n → Module.End ℂ W) (A : Module.End ℂ W)
    (hAT : ∀ a b, A * T a b = T a b * A) (θ : Fin n → ℂ) (g : Fin n → W)
    (hstep : ∀ t, (A - θ t • 1) (g t) ∈ genSub T (Submodule.span ℂ (g '' {d | t < d}))) :
    ∀ x ∈ genSub T (Submodule.span ℂ (Set.range g)), aeval A (∏ t, (X - C (θ t))) x = 0 := by
  have main : ∀ m k : ℕ, n ≤ k + m →
      ∀ x ∈ genSub T (Submodule.span ℂ (g '' {d : Fin n | k ≤ (d : ℕ)})),
        aeval A (∏ t ∈ univ.filter (fun d : Fin n => k ≤ (d : ℕ)), (X - C (θ t))) x = 0 := by
    intro m
    induction m with
    | zero =>
      intro k hk x hx
      have hempty : g '' {d : Fin n | k ≤ (d : ℕ)} = ∅ := by
        ext y
        simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
          not_and]
        intro d hd
        have := d.isLt
        omega
      rw [hempty, Submodule.span_empty] at hx
      have hbot : genSub T ⊥ ≤ ⊥ :=
        sInf_le ⟨le_refl _, fun a b v hv => by rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero]⟩
      have hx0 : x = 0 := by simpa using hbot hx
      rw [hx0, map_zero]
    | succ m ih =>
      intro k hk x hx
      by_cases hkn : n ≤ k
      · exact ih k (by omega) x hx
      · replace hkn : k < n := not_le.mp hkn
        have hfil : univ.filter (fun d : Fin n => k ≤ (d : ℕ)) =
            insert ⟨k, hkn⟩ (univ.filter (fun d : Fin n => k + 1 ≤ (d : ℕ))) := by
          ext d
          simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
          omega
        have hnot : (⟨k, hkn⟩ : Fin n) ∉ univ.filter (fun d : Fin n => k + 1 ≤ (d : ℕ)) := by simp
        rw [hfil, prod_insert hnot, mul_comm, map_mul, Module.End.mul_apply]
        apply ih (k + 1) (by omega)
        rw [vk_aeval_lin]
        have hmono : ∀ t : Fin n, k ≤ (t : ℕ) →
            genSub T (Submodule.span ℂ (g '' {d | t < d})) ≤
              genSub T (Submodule.span ℂ (g '' {d : Fin n | k + 1 ≤ (d : ℕ)})) := by
          intro t ht
          apply vk_genSub_mono
          apply Submodule.span_mono
          apply Set.image_mono
          intro d hd
          simp only [Set.mem_ofPred_eq, Fin.lt_def] at hd ⊢
          omega
        refine vk_genSub_map T _ (vk_shift_comm T A hAT _) _ (vk_genSub_stable T _) _ ?_ x hx
        rintro _ ⟨d, hd, rfl⟩
        simp only [Set.mem_ofPred_eq] at hd
        rcases eq_or_lt_of_le hd with h | h
        · have hdt : d = ⟨k, hkn⟩ := Fin.ext h.symm
          rw [hdt]
          exact hmono _ le_rfl (hstep _)
        · have e : (A - θ ⟨k, hkn⟩ • 1) (g d) = (A - θ d • 1) (g d) + (θ d - θ ⟨k, hkn⟩) • g d := by
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
            abel
          rw [e]
          refine add_mem (hmono d hd (hstep d)) (Submodule.smul_mem _ _ ?_)
          exact vk_le_genSub _ _ (Submodule.subset_span ⟨d, h, rfl⟩)
  intro x hx
  have h0 := main n 0 (by omega) x (by
    have : g '' {d : Fin n | 0 ≤ (d : ℕ)} = Set.range g := by
      rw [← Set.image_univ]; congr 1; ext d; simp
    rw [this]; exact hx)
  have hf : univ.filter (fun d : Fin n => 0 ≤ (d : ℕ)) = univ := by ext d; simp
  rwa [hf] at h0

/- English proof (translation)
Rewrite using `[prodShift, ← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Use `congrArg List.prod (congrArg List.ofFn (funext fun t => ?_))` and prove the remaining obligations. Simplify using `[Algebra.algebraMap_eq_smul_one]`.
-/
theorem vk_prodShift_eq (A : Module.End ℂ W) (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C ((θ t : ℝ) : ℂ))) := by
  rw [prodShift, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun t => ?_))
  simp [Algebra.algebraMap_eq_smul_one]

end GenKill

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
