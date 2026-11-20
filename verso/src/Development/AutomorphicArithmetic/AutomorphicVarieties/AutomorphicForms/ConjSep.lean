import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.LFun

namespace UpperTheory.V.Af

section Sep

variable {G H V V' V'' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup V''] [Module ℂ V'']

def Sep (σ : ℂ ≃+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') : Prop :=
  ∀ x : V, x ≠ 0 → ∃ p : V →+ V', (∀ (c : ℂ) v, p (c • v) = σ c • p v) ∧ (∀ g v, p (ρ g v) = ρ' g (p v)) ∧ p x ≠ 0

variable {σ σ' : ℂ ≃+* ℂ} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} {ρ'' : Representation ℂ G V''}

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem Sep.trans (h : Sep σ ρ ρ') (h' : Sep σ' ρ' ρ'') : Sep (σ.trans σ') ρ ρ'' := fun x hx => by
  obtain ⟨p, h1, h2, h3⟩ := h x hx
  obtain ⟨q, k1, k2, k3⟩ := h' _ h3
  exact ⟨q.comp p, fun c v => by simp [h1, k1], fun g v => by simp [h2, k2], k3⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem Sep.comp (h : Sep σ ρ ρ') (e : H →* G) : Sep σ (ρ.comp e) (ρ'.comp e) := fun x hx => by
  obtain ⟨p, h1, h2, h3⟩ := h x hx
  exact ⟨p, h1, fun g v => h2 _ v, h3⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem Sep.of_injective (f : V →ₗ[ℂ] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (hi : Function.Injective f) :
    Sep (RingEquiv.refl ℂ) ρ ρ' := fun x hx =>
  ⟨f.toAddMonoidHom, fun c v => map_smul f c v, hf, (map_ne_zero_iff f hi).2 hx⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem Sep.of_equiv (T : V ≃ₗ[ℂ] V') (hT : ∀ g v, T (ρ g v) = ρ' g (T v)) :
    Sep (RingEquiv.refl ℂ) ρ ρ' ∧ Sep (RingEquiv.refl ℂ) ρ' ρ :=
  ⟨.of_injective T.toLinearMap hT T.injective, .of_injective T.symm.toLinearMap (fun g v => T.injective (by
    change T (T.symm _) = T (ρ g (T.symm v))
    rw [hT, T.apply_symm_apply, T.apply_symm_apply])) T.symm.injective⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem Sep.of_irred (hρ : ρ.IsIrreducible) (f : V →ₗ[ℂ] V') (h0 : f ≠ 0) (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    Sep (RingEquiv.refl ℂ) ρ ρ' := by
  refine .of_injective f hf (LinearMap.ker_eq_bot.1 ?_)
  refine (((isIrreducible_iff ρ).1 hρ).2 (LinearMap.ker f) fun g v hv => ?_).resolve_right
    fun e => h0 (LinearMap.ker_eq_top.1 e)
  rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem exists_sep_module {R M S ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (Φ : (ι →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ) (x : M) (hx : x ≠ 0) :
    ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  obtain ⟨s, hs'⟩ := IsSemisimpleModule.lifting_property Φ hs (LinearMap.id : M →ₗ[R] M)
  have h0 : s x ≠ 0 := fun e => hx (by rw [← LinearMap.id_apply (R := R) x, ← hs', LinearMap.comp_apply, e, map_zero])
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h0
  exact ⟨Finsupp.lapply i ∘ₗ s, hi⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem Sep.of_isotypic (hρ : ρ'.IsIrreducible)
    (h : ⨆ f : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)}, LinearMap.range f.1 = ⊤) :
    Sep (RingEquiv.refl ℂ) ρ ρ' := by
  classical
  intro x hx
  let F : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)} → ρ'.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρ' ρ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
  let Φ := Finsupp.lsum ℕ F
  have hs : Function.Surjective Φ := fun y => by
    have hy : (y : V) ∈ ⨆ f : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)}, LinearMap.range f.1 := by
      rw [h]; exact @Submodule.mem_top _ V _ _ _ y
    refine Submodule.iSup_induction _ (motive := fun y : V => ∃ z, Φ z = y) hy ?_ ⟨0, map_zero Φ⟩ ?_
    · rintro f _ ⟨v, rfl⟩
      exact ⟨Finsupp.single f v, Finsupp.lsum_single _ _ _ _⟩
    · rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
      exact ⟨z + z', map_add Φ z z'⟩
  obtain ⟨p, hp⟩ := exists_sep_module Φ hs x hx
  let q := (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ').symm p
  exact ⟨q.toLinearMap.toAddMonoidHom, fun c v => map_smul q.toLinearMap c v, fun g v => q.isIntertwining _ _ g v, hp⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem Sep.hasFixed (h : Sep σ ρ ρ') {U : Subgroup G} (hU : HasFixed ρ U) : HasFixed ρ' U := by
  obtain ⟨x, hx, hU⟩ := hU
  obtain ⟨p, -, h2, h3⟩ := h x hx
  exact ⟨p x, h3, fun u hu => by rw [← h2, hU u hu]⟩

end Sep

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem IsConjBy.sep {E : Type} [Field E] [NumberField E] {a : ℕ} {σ : ℂ ≃+* ℂ} {τ τ' : SmIrr (GL (Fin a) (Af E))}
    (h : IsConjBy σ τ τ') : Sep σ τ.ρ τ'.ρ ∧ Sep σ.symm τ'.ρ τ.ρ := by
  obtain ⟨T, h1, h2⟩ := h
  refine ⟨fun x hx => ⟨T.toAddMonoidHom, h1, h2, (map_ne_zero_iff T T.injective).2 hx⟩,
    fun x hx => ⟨T.symm.toAddMonoidHom, fun c v => T.injective ?_, fun g v => T.injective ?_,
      (map_ne_zero_iff T.symm T.symm.injective).2 hx⟩⟩
  · change T (T.symm _) = T (_ • T.symm v)
    rw [h1]; simp
  · change T (T.symm _) = T (τ.ρ g (T.symm v))
    rw [h2]; simp

section Sat

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem satEig_eq_algSat {q : ℕ} (hq : q ≠ 0) (n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    satEig q n B j = ((q : ℂ) ^ j.choose 2)⁻¹ * (algSat n q B).esymm j := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have e : algSat n q B = (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((q : ℂ) ^ (((n : ℂ) - 1) / 2)) • x := by
    rw [algSat, Multiset.map_map, Complex.ofReal_cpow (Nat.cast_nonneg q)]
    simp
  rw [e, ← Multiset.pow_smul_esymm, satEig, smul_eq_mul, ← mul_assoc, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast,
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ hq', Nat.cast_choose_two]
  congr 2
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem esymm_map_ringEquiv (σ : ℂ ≃+* ℂ) (A : Multiset ℂ) (j : ℕ) : (A.map σ).esymm j = σ (A.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum, Function.comp_def,
    map_multiset_prod]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem satEig_conj {q : ℕ} (hq : q ≠ 0) {n : ℕ} {σ : ℂ ≃+* ℂ} {B B' : Multiset ℂˣ}
    (h : algSat n q B' = (algSat n q B).map σ) (j : ℕ) : satEig q n B' j = σ (satEig q n B j) := by
  rw [satEig_eq_algSat hq, satEig_eq_algSat hq, h, esymm_map_ringEquiv, map_mul, map_inv₀, map_pow, map_natCast]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem exists_algSat_conj {q : ℕ} (hq : q ≠ 0) (n : ℕ) (σ : ℂ ≃+* ℂ) (B : Multiset ℂˣ) :
    ∃ B' : Multiset ℂˣ, algSat n q B' = (algSat n q B).map σ := by
  have h0 : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'
  refine ⟨B.map fun α => (Units.mk0 _ h0)⁻¹ * Units.map σ.toMonoidHom (Units.mk0 _ h0 * α), ?_⟩
  simp only [algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp [h0]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V'}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem map_heckeTj {σ : ℂ ≃+* ℂ} (p : V →+ V') (h1 : ∀ (c : ℂ) v, p (c • v) = σ c • p v)
    (h2 : ∀ g v, p (ρ g v) = ρ' g (p v)) {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) (x : V) :
    p (heckeVec ρ (KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) x) =
      heckeVec ρ' (KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) (p x) := by
  refine (p.map_finsum (finite_heckeVec (Formalism.UG.Final.GLintComm E w n) (Tj_mem_hecke hϖ j) ρ x)).trans
    (finsum_congr fun c => ?_)
  rw [h1, h2]
  congr 1
  simp only [Formalism.UG.Tj, Formalism.UG.dosetInd, Set.indicator]
  split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Sep.hasSatGL {σ : ℂ ≃+* ℂ} (h : Sep σ ρ ρ') (h' : Sep σ.symm ρ' ρ) {B B' : Multiset ℂˣ} (hB : HasSatGL w ρ B)
    (e : algSat n (normV w) B' = (algSat n (normV w) B).map σ) : HasSatGL w ρ' B' := by
  have hc : B'.card = n := by simpa [algSat, hB.card] using congrArg Multiset.card e
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    obtain ⟨y, h0, hy⟩ := h.hasFixed ⟨x, hx.1, GlobalTheory.LGrp.mem_fixed.1 hx.2.1⟩
    exact (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, h0⟩
  · refine fun y hy h0 => ⟨h0, hy, hc, fun ϖ hϖ j hj => ?_⟩
    by_contra hne
    obtain ⟨p, h1, h2, h3⟩ := h' _ (sub_ne_zero.2 hne)
    refine h3 ?_
    have e2 : satEig (Formalism.UG.qV E w) n B' j = σ (satEig (Formalism.UG.qV E w) n B j) := satEig_conj (qV_ne_zero w) e j
    rw [map_sub, map_heckeTj p h1 h2 hϖ, h1, e2, σ.symm_apply_apply, sub_eq_zero]
    by_cases hp : p y = 0
    · simp [hp, heckeVec]
    · exact (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← h2, GlobalTheory.LGrp.mem_fixed.1 hy k hk]) hp).2.2.2 ϖ hϖ j hj

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem Sep.exists_hasSatGL {σ : ℂ ≃+* ℂ} (h : Sep σ ρ ρ') (h' : Sep σ.symm ρ' ρ) {B : Multiset ℂˣ} (hB : HasSatGL w ρ B) :
    ∃ B', HasSatGL w ρ' B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ := by
  obtain ⟨B', e⟩ := exists_algSat_conj (q := normV w) (qV_ne_zero w) n σ B
  exact ⟨B', h.hasSatGL h' hB e, e⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Sep.hasSatGL_refl (h : Sep (RingEquiv.refl ℂ) ρ ρ') (h' : Sep (RingEquiv.refl ℂ) ρ' ρ) {B : Multiset ℂˣ}
    (hB : HasSatGL w ρ B) : HasSatGL w ρ' B := h.hasSatGL h' hB (by simp)

end Sat

section Fin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Treat this case separately. A detailed English derivation is pending.
-/
theorem act_fin_comm (k : GL (Fin a) (Af E)) (o : Op E a) (ho : ∀ k', o ≠ .fin k') :
    act o * act (.fin k) = act (.fin k) * act o := by
  cases o with
  | fin k' => exact (ho k' rfl).elim
  | cpt u =>
    change rt E a _ * rt E a _ = rt E a _ * rt E a _
    rw [← map_mul, ← map_mul]
    exact congrArg _ (infGL_comm _ _)
  | lie X => exact lie_rt_fin X k

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsFinComp.iSup_range {π : CuspSub E a} {τ : SmIrr (GL (Fin a) (Af E))} (h : IsFinComp π τ) :
    ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.finPart g (f v)}, LinearMap.range f.1 = ⊤ := by
  obtain ⟨f, h0, hf⟩ := h
  set W := ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.finPart g (f v)}, LinearMap.range f.1 with hW
  have hs : ∀ o, W ≤ W.comap (π.op o) := fun o => iSup_le fun f => by
    rintro _ ⟨v, rfl⟩
    by_cases ho : ∀ k', o ≠ .fin k'
    · exact Submodule.mem_iSup_of_mem ⟨π.op o ∘ₗ f.1, fun g v => by
        rw [LinearMap.comp_apply, f.2]
        exact Subtype.ext (LinearMap.congr_fun (act_fin_comm g o ho) (f.1 v).1)⟩ ⟨v, rfl⟩
    · push Not at ho
      obtain ⟨k, rfl⟩ := ho
      exact Submodule.mem_iSup_of_mem f ⟨τ.ρ k v, f.2 k v⟩
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hs o hx, rfl⟩) with e | e
  · refine (h0 (LinearMap.range_eq_bot.1 (le_bot_iff.1 ?_))).elim
    rw [← Submodule.map_bot π.V.subtype] at e
    rw [← Submodule.map_injective_of_injective π.V.subtype_injective e]
    exact le_iSup (fun f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.finPart g (f v)} => LinearMap.range f.1) ⟨f, hf⟩
  · exact Submodule.map_injective_of_injective π.V.subtype_injective (e.trans (Submodule.map_subtype_top _).symm)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem IsFinComp.sep {π : CuspSub E a} {τ : SmIrr (GL (Fin a) (Af E))} (h : IsFinComp π τ) :
    Sep (RingEquiv.refl ℂ) π.finPart τ.ρ ∧ Sep (RingEquiv.refl ℂ) τ.ρ π.finPart :=
  ⟨.of_isotypic τ.irred h.iSup_range, by
    obtain ⟨f, h0, hf⟩ := h
    exact .of_irred τ.irred f h0 hf⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem sep_of_conj {π π' : CuspSub E a} {τ τ' : SmIrr (GL (Fin a) (Af E))} {σ : ℂ ≃+* ℂ} (h : IsFinComp π τ)
    (h' : IsFinComp π' τ') (hc : IsConjBy σ τ τ') : Sep σ π.finPart π'.finPart ∧ Sep σ.symm π'.finPart π.finPart :=
  ⟨(h.sep.1.trans hc.sep.1).trans h'.sep.2, (h'.sep.1.trans hc.sep.2).trans h.sep.2⟩

end Fin

end UpperTheory.V.Af
