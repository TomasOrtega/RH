import Formalism.LogVandermondeBounds.FinrankFiberSumZero

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Core

variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]

def eps (a h : H) : K := if h = a then 1 else if h = 1 then -1 else 0

def bas (a : ι → {c : H // c ≠ 1}) (h : ι → H) : K := ∏ w, (eps ((a w : H)) (h w) : K)

omit [Fintype H] in
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma mulSingle_mul_apply_ne (v w : ι) (c : H) (h : ι → H) (hw : w ≠ v) :
    ((Pi.mulSingle v c : ι → H) * h) w = h w := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, _root_.one_mul]

omit [Fintype H] in
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma mulSingle_mul_apply_self (v : ι) (c : H) (h : ι → H) :
    ((Pi.mulSingle v c : ι → H) * h) v = c * h v := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_same]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_eps (a t : H) (ha : a ≠ 1) : ∑ c : H, (eps a (c * t) : K) = 0 := by
  have key : ∀ h : H, (eps a h : K) = (if h = a then 1 else 0) + (if h = 1 then -1 else 0) := by
    intro h
    unfold eps
    by_cases h1 : h = a
    · subst h1
      simp [ha]
    · simp [h1]
  rw [show (∑ c : H, (eps a (c * t) : K)) = ∑ h : H, (eps a h : K) from
    Equiv.sum_comp (Equiv.mulRight t) (fun h => (eps a h : K))]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma sum_bas (a : ι → {c : H // c ≠ 1}) (v : ι) (h : ι → H) :
    ∑ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K) = 0 := by
  have hfac : ∀ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K)
      = (eps (a v : H) (c * h v) : K) * ∏ w ∈ univ.erase v, (eps (a w : H) (h w) : K) := by
    intro c
    unfold bas
    rw [← Finset.mul_prod_erase univ _ (mem_univ v)]
    simp only [mulSingle_mul_apply_self]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mulSingle_mul_apply_ne v w c h (Finset.ne_of_mem_erase hw)]
  simp only [hfac, ← Finset.sum_mul, sum_eps (K := K) (a v : H) (h v) (a v).2, zero_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma bas_avoid (a b : ι → {c : H // c ≠ 1}) :
    (bas a (fun w => (b w : H)) : K) = if a = b then 1 else 0 := by
  unfold bas
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun w _ => ?_
    unfold eps
    simp
  · rw [if_neg hab]
    have hw : ∃ w, a w ≠ b w := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hab (funext hcon)
    obtain ⟨w, hw⟩ := hw
    refine Finset.prod_eq_zero (mem_univ w) ?_
    have h1 : (b w : H) ≠ a w := fun h => hw (Subtype.ext h.symm)
    unfold eps
    simp [h1, (b w).2]

/- English proof (translation)
Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
lemma inj_core (ψ : (ι → H) → K)
    (hψ : ∀ (v : ι) (h : ι → H), ∑ c : H, ψ ((Pi.mulSingle v c : ι → H) * h) = 0)
    (h0 : ∀ a : ι → {c : H // c ≠ 1}, ψ (fun w => (a w : H)) = 0) :
    ∀ h, ψ h = 0 := by
  classical
  suffices key : ∀ n, ∀ h : ι → H, (univ.filter (fun w => h w = 1)).card = n → ψ h = 0 from
    fun h => key _ h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hn
    by_cases hall : ∀ w, h w ≠ 1
    · exact h0 (fun w => ⟨h w, hall w⟩)
    · simp only [not_forall, not_not] at hall
      obtain ⟨v, hv⟩ := hall
      have hsum := hψ v h
      rw [Finset.sum_eq_single (1 : H)] at hsum
      · simpa using hsum
      · intro c _ hc
        apply ih _ _ _ rfl
        rw [← hn]
        have hset : univ.filter (fun w => ((Pi.mulSingle v c : ι → H) * h) w = 1)
            = (univ.filter (fun w => h w = 1)).erase v := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hwv : w = v
          · subst hwv
            rw [mulSingle_mul_apply_self, hv, mul_one]
            simp [hc]
          · rw [mulSingle_mul_apply_ne v w c h hwv]
            simp [hwv]
        rw [hset]
        exact Finset.card_erase_lt_of_mem (by simp [hv])
      · intro h1
        exact absurd (Finset.mem_univ _) h1

end Core

section Main

variable {ι H X K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H]
  [Fintype X] [MulAction (ι → H) X] [Field K]

def restr (Q : Type) (e : Q × (ι → H) ≃ X) :
    ramSub ι H X K →ₗ[K] (Q × (ι → {c : H // c ≠ 1}) → K) where
  toFun φ p := (φ : X → K) (e (p.1, fun w => (p.2 w : H)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finrank_core (Q : Type) [Fintype Q] (e : Q × (ι → H) ≃ X)
    (he : ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g)) :
    Module.finrank K (ramSub ι H X K) = Fintype.card Q * (Fintype.card H - 1) ^ Fintype.card ι := by
  classical
  have hmem : ∀ φ : ramSub ι H X K, ∀ v x,
      ∑ c : H, (φ : X → K) ((Pi.mulSingle v c : ι → H) • x) = 0 := fun φ => φ.2
  have hinj : Function.Injective (restr (K := K) Q e) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext x
    obtain ⟨⟨ω, g⟩, rfl⟩ := e.surjective x
    have hz := inj_core (K := K) (fun h => (φ : X → K) (e (ω, h)))
      (fun v h => by simpa only [he] using hmem φ v (e (ω, h)))
      (fun a => congrFun hφ (ω, a)) g
    simpa using hz
  have hsurj : Function.Surjective (restr (K := K) Q e) := by
    intro f
    let φ0 : X → K := fun x =>
      ∑ a : ι → {c : H // c ≠ 1}, f ((e.symm x).1, a) * bas a (e.symm x).2
    have hφ0 : φ0 ∈ ramSub ι H X K := by
      show ∀ (v : ι) (x : X), ∑ c : H, φ0 ((Pi.mulSingle v c : ι → H) • x) = 0
      intro v x
      obtain ⟨⟨ω, g⟩, rfl⟩ := e.surjective x
      have hx : ∀ c : H, e.symm ((Pi.mulSingle v c : ι → H) • e (ω, g))
          = (ω, (Pi.mulSingle v c : ι → H) * g) := by
        intro c
        rw [← he, Equiv.symm_apply_apply]
      simp only [φ0, hx]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.mul_sum, sum_bas, mul_zero]
    refine ⟨⟨φ0, hφ0⟩, ?_⟩
    funext p
    obtain ⟨ω, a'⟩ := p
    show φ0 (e (ω, fun w => (a' w : H))) = f (ω, a')
    simp only [φ0, Equiv.symm_apply_apply, bas_avoid]
    simp
  have hc : Fintype.card {c : H // c ≠ 1} = Fintype.card H - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [(LinearEquiv.ofBijective (restr (K := K) Q e) ⟨hinj, hsurj⟩).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fun, hc]

end Main

/- English proof (translation)
Introduce a local definition for the expression. Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Substitute using the available equality.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_equiv (ι H X : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] (hfree : ∀ (g : ι → H) (x : X), g • x = x → g = 1) :
    ∃ (Q : Type) (_ : Fintype Q) (e : Q × (ι → H) ≃ X),
      ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g) := by
  classical
  let Q := MulAction.orbitRel.Quotient (ι → H) X
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → X := fun ω => Quotient.out ω
  have hrep : ∀ ω : Q, Quotient.mk (MulAction.orbitRel (ι → H) X) (rep ω) = ω :=
    fun ω => Quotient.out_eq ω
  let f : Q × (ι → H) → X := fun p => p.2 • rep p.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨ω, g⟩ ⟨ω', g'⟩ h
      change g • rep ω = g' • rep ω' at h
      have hω : ω = ω' := by
        rw [← hrep ω, ← hrep ω']
        apply Quotient.sound
        show rep ω ∈ MulAction.orbit (ι → H) (rep ω')
        refine ⟨g⁻¹ * g', ?_⟩
        show (g⁻¹ * g') • rep ω' = rep ω
        rw [mul_smul, ← h, inv_smul_smul]
      subst hω
      have hfix : (g'⁻¹ * g) • rep ω = rep ω := by rw [mul_smul, h, inv_smul_smul]
      have hg := hfree _ _ hfix
      rw [inv_mul_eq_one] at hg
      rw [hg]
    · intro x
      have hx : rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) ∈ MulAction.orbit (ι → H) x :=
        Quotient.exact (hrep _)
      obtain ⟨g, hg⟩ := hx
      refine ⟨(Quotient.mk (MulAction.orbitRel (ι → H) X) x, g⁻¹), ?_⟩
      show g⁻¹ • rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) = x
      rw [← hg, inv_smul_smul]
  refine ⟨Q, inferInstance, Equiv.ofBijective f hf, ?_⟩
  intro m ω g
  show (m * g) • rep ω = m • (g • rep ω)
  rw [mul_smul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrankFiberSumZero : FinrankFiberSumZero := by
  intro ι H X K _ _ _ _ _ _ _ hfree
  classical
  obtain ⟨Q, _, e, he⟩ := exists_equiv ι H X hfree
  rw [finrank_core (K := K) Q e he, ← Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun]
  ring

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
