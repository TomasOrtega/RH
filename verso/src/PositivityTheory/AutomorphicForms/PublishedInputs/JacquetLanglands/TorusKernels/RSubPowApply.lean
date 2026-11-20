import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

namespace UpperTheory.Esk.CommutingOperatorTraces

open Module Module.End

variable {J V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def E (T : J → Module.End ℂ V) (s : J → ℂ) : Submodule ℂ V :=
  ⨅ j, (T j).maxGenEigenspace (s j)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
lemma mapsTo_E (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (i : J) : Set.MapsTo (T i) (E T s) (E T s) := by
  intro x hx
  simp only [E, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
  intro j
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hT j i) (s j) (hx j)

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma mapsTo_prod (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) : Set.MapsTo (W.map T).prod (E T s) (E T s) := by
  induction W with
  | nil => intro x hx; simpa using hx
  | cons a W ih =>
    intro x hx
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact mapsTo_E T hT s a (ih hx)

noncomputable def R (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (j : J) : Module.End ℂ (E T s) :=
  (T j).restrict (mapsTo_E T hT s j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma R_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (j : J) (x : E T s) : ((R T hT s j x : E T s) : V) = T j x := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma R_comm (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (i j : J) : Commute (R T hT s i) (R T hT s j) := by
  show R T hT s i * R T hT s j = R T hT s j * R T hT s i
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [Module.End.mul_apply, R_apply]
  exact LinearMap.congr_fun (hT i j) x

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
lemma R_prod_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) (x : E T s) : (((W.map (R T hT s)).prod x : E T s) : V) = (W.map T).prod x := by
  induction W with
  | nil => simp
  | cons a W ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, R_apply, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
lemma R_sub_pow_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i)
    (s : J → ℂ) (j : J) (n : ℕ) (x : E T s) :
    ((((R T hT s j - algebraMap ℂ _ (s j)) ^ n) x : E T s) : V) = ((T j - s j • 1) ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    rw [← ih]
    simp [R_apply, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
lemma R_nil (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ) (j : J) :
    IsNilpotent (R T hT s j - algebraMap ℂ _ (s j)) := by
  rw [Module.End.isNilpotent_iff_of_finite]
  intro x
  have hx := x.2
  simp only [E] at hx
  obtain ⟨k, hk⟩ := (Module.End.mem_iInf_maxGenEigenspace_iff T s (x : V)).mp hx j
  refine ⟨k, Subtype.ext ?_⟩
  rw [R_sub_pow_apply, hk]
  rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
lemma trace_R_prod (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) : LinearMap.trace ℂ (E T s) (W.map (R T hT s)).prod =
      (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
  induction W with
  | nil => simp [LinearMap.trace_one]
  | cons a W ih =>
    have hc : Commute (W.map (R T hT s)).prod (R T hT s a) := by
      apply Commute.list_prod_left
      intro y hy
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
      exact R_comm T hT s b a
    simp only [List.map_cons, List.prod_cons]
    rw [← hc.eq, Module.End.mul_eq_comp,
      LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (s a) hc (R_nil T hT s a), ih]
    ring

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
-/
lemma trace_restrict (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) (h : Set.MapsTo (W.map T).prod (E T s) (E T s)) :
    LinearMap.trace ℂ (E T s) ((W.map T).prod.restrict h) =
      (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
  have : (W.map T).prod.restrict h = (W.map (R T hT s)).prod := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [R_prod_apply]
    rfl
  rw [this, trace_R_prod]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma exists_eigvec (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (hs : E T s ≠ ⊥) : ∃ f : V, f ≠ 0 ∧ ∀ j, T j f = s j • f := by
  classical
  let P : Set (Submodule ℂ V) :=
    {U | U ≠ ⊥ ∧ U ≤ E T s ∧ ∀ j, ∀ x ∈ U, T j x ∈ U}
  have hP : (E T s) ∈ P := ⟨hs, le_rfl, fun j x hx => mapsTo_E T hT s j hx⟩
  obtain ⟨U, ⟨hU0, hUE, hUT⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min P ⟨_, hP⟩
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).mp hU0
  refine ⟨x, hx0, fun j => ?_⟩

  have hsub : ∀ n : ℕ, ∀ y ∈ U, ((T j - s j • 1) ^ n) y ∈ U := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      have h1 := ih y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.sub_mem (hUT j _ h1) (U.smul_mem _ h1)
  let U' : Submodule ℂ V := U ⊓ (T j).eigenspace (s j)
  have hU'P : U' ∈ P := by
    refine ⟨?_, inf_le_left.trans hUE, ?_⟩
    · have hxE : x ∈ E T s := hUE hxU
      simp only [E] at hxE
      have hex := (Module.End.mem_iInf_maxGenEigenspace_iff T s x).mp hxE j
      let k := Nat.find hex
      have hk : ((T j - s j • 1) ^ k) x = 0 := Nat.find_spec hex
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0, pow_zero, Module.End.one_apply] at hk
        exact hx0 hk
      obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hne : ((T j - s j • 1) ^ k') x ≠ 0 := by
        have := Nat.find_min hex (show k' < k by omega)
        exact this
      rw [Submodule.ne_bot_iff]
      refine ⟨((T j - s j • 1) ^ k') x, ⟨hsub k' x hxU, ?_⟩, hne⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h2 : ((T j - s j • 1) ^ k) x = 0 := hk
      rw [hk', pow_succ', Module.End.mul_apply] at h2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h2
      exact sub_eq_zero.mp h2
    · intro i y hy
      refine ⟨hUT i y hy.1, ?_⟩
      have hy2 : T j y = s j • y := (Module.End.mem_eigenspace_iff).mp hy.2
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := LinearMap.congr_fun (hT j i) y
      simp only [Module.End.mul_apply] at this
      rw [this, hy2, map_smul]
  have hle : U' ≤ U := inf_le_left
  have hUU : U' = U := by
    by_contra hne
    exact hmin U' hU'P (lt_of_le_of_ne hle hne)
  have hxU' : x ∈ U' := hUU ▸ hxU
  exact (Module.End.mem_eigenspace_iff).mp hxU'.2

end UpperTheory.Esk.CommutingOperatorTraces

open UpperTheory.Esk.CommutingOperatorTraces in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Esk.pf_Sys : UpperTheory.Esk.Sys := by
  intro J V _ _ _ T hT
  classical
  have hind : iSupIndep (E T) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hT j i) φ)
  have htop : ⨆ s, E T s = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T
      (fun i j _ => hT i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (T i))
  have hfin : {s | E T s ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have htr : ∀ W : List J, LinearMap.trace ℂ V (W.map T).prod =
      ∑ s ∈ hfin.toFinset, (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
    intro W
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (mapsTo_prod T hT · W)]
    exact Finset.sum_congr rfl fun s _ => trace_restrict T hT s W _
  refine ⟨hfin.toFinset, fun s => Module.finrank ℂ (E T s), ?_, ?_, ?_, htr⟩
  · intro s
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · exact exists_eigvec T hT s
    · rintro ⟨f, hf0, hf⟩ hbot
      have hfE : f ∈ E T s := by
        simp only [E, Submodule.mem_iInf]
        intro j
        apply Module.End.eigenspace_le_maxGenEigenspace
        exact (Module.End.mem_eigenspace_iff).mpr (hf j)
      rw [hbot, Submodule.mem_bot] at hfE
      exact hf0 hfE
  · intro s hs
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    exact Submodule.one_le_finrank_iff.mpr hs
  · have h0 := htr []
    simp only [List.map_nil, List.prod_nil, LinearMap.trace_one, mul_one] at h0
    exact_mod_cast h0.symm
