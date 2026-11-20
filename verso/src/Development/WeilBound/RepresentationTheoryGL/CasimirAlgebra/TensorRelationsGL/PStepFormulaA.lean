import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace PStepFormula

/- English proof (translation)
Simplify using `only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, Tm, map_add, apply_ite f, AlgHom.commutes, map_zero]`.
-/
theorem qdet_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, Tm,
    map_add, apply_ite f, AlgHom.commutes, map_zero]

/- English proof (translation)
Introduce `a b c d`. Use `congrArg f (h a b c d)` as an intermediate fact. Simplify `this` using `only [map_sub, map_mul, apply_ite f, map_zero]`.
-/
theorem glRel_map {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    {E : Fin n → Fin n → A} (h : GlRel E) : GlRel (fun a b => f (E a b)) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa only [map_sub, map_mul, apply_ite f, map_zero] using this

section
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[LinearEquiv.conjAlgEquiv_apply, h]`.
-/
theorem conj_eq (e : V ≃ₗ[ℂ] W) {T : Module.End ℂ V} {T' : Module.End ℂ W}
    (h : ∀ x, e (T x) = T' (e x)) : e.conjAlgEquiv ℂ T = T' := by
  ext x
  simp [LinearEquiv.conjAlgEquiv_apply, h]
end

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftA_apply {P : Type} (B : Module.End ℂ M) : liftA n M P B = lift B := rfl

/- English proof (translation)
Rewrite using `[← liftA_apply]`. Simplify using `only [PiJ, map_list_prod, List.map_ofFn, Function.comp_def, map_add, AlgHom.commutes, liftA_apply]`.
-/
theorem lift_PiJ {m : ℕ} {P : Type} (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (lift (PiJ m E u) : Module.End ℂ (TV n (TV n M (Fin m)) P)) =
      (List.ofFn fun i => algebraMap ℂ _ u + lift (xJ E i)).prod := by
  rw [← liftA_apply]
  simp only [PiJ, map_list_prod, List.map_ofFn, Function.comp_def, map_add, AlgHom.commutes, liftA_apply]

/- English proof (translation)
Establish `: (Finset.univ.filter fun i : Fin 1 => i < 0) = ∅`. Use extensionality with `i`. Simplify using the standard rewrite rules. Simplify using `[PiJ, xJ]`.
-/
theorem PiJ_one (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (PiJ 1 E u : Module.End ℂ (TV n M (Fin 1))) = algebraMap ℂ _ u + Om E 0 := by
  have : (Finset.univ.filter fun i : Fin 1 => i < 0) = ∅ := by
    ext i; simp
  simp [PiJ, xJ]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) x` and prove the remaining obligations. Rewrite using `[Fin.append_left, Function.update_of_ne, Fin.append_left]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne, Fin.append_right, Fin.append_right, Function.update_of_ne h]`. Introduce `h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))`.
-/
theorem app_upd_r {α : Type} {m k : ℕ} (I : Fin m → α) (J : Fin k → α) (j : Fin k) (a : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) a = Fin.append I (Function.update J j a) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · rw [Fin.append_left, Function.update_of_ne, Fin.append_left]
    intro h; have := congrArg Fin.val h; simp at this; omega
  · by_cases h : i = j
    · subst h; simp
    · rw [Function.update_of_ne, Fin.append_right, Fin.append_right, Function.update_of_ne h]
      intro h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Fin.addCases (fun i' => ?_) (fun j => ?_) x` and prove the remaining obligations. Distinguish the cases in `h : i' = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne, Fin.append_left, Fin.append_left, Function.update_of_ne h]`. Introduce `h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))`. Rewrite using `[Fin.append_right, Function.update_of_ne, Fin.append_right]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem app_upd_l {α : Type} {m k : ℕ} (I : Fin m → α) (J : Fin k → α) (i : Fin m) (a : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) a = Fin.append (Function.update I i a) J := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) x
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne, Fin.append_left, Fin.append_left, Function.update_of_ne h]
      intro h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))
  · rw [Fin.append_right, Function.update_of_ne, Fin.append_right]
    intro h; have := congrArg Fin.val h; simp at this; omega

/- English proof (translation)
Use function extensionality and compare the values at `J I`. Simplify using `only [curF_apply, Om_apply, Fin.append_right, app_upd_r]`. Rewrite using `[Finset.sum_apply]`. Simplify using `[curF_apply]`.
-/
theorem curF_Om_r {m k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin k) (f : TV n M (Fin (m + k))) :
    curF n M m k (Om E (Fin.natAdd m j) f) = Om (fun a b => lift (E a b)) j (curF n M m k f) := by
  funext J I
  simp only [curF_apply, Om_apply, Fin.append_right, app_upd_r]
  rw [Finset.sum_apply]
  simp [curF_apply]

/- English proof (translation)
Use function extensionality and compare the values at `J I`. Simplify using `only [curF_apply, Om_apply, Fin.append_left, app_upd_l, lift_apply]`.
-/
theorem curF_Om_l {m k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (i : Fin m) (f : TV n M (Fin (m + k))) :
    curF n M m k (Om E (Fin.castAdd k i) f) = lift (Om E i) (curF n M m k f) := by
  funext J I
  simp only [curF_apply, Om_apply, Fin.append_left, app_upd_l, lift_apply]

/- English proof (translation)
Establish `h2 : (2 : ℂ) • x = 0`. Rewrite using `[two_smul]`. Use `nth_rewrite 2 [h]`. Conclude with `add_neg_cancel x`. Conclude with `(smul_eq_zero.mp h2).resolve_left two_ne_zero`.
-/
theorem eq_zero_of_eq_neg' {X : Type} [AddCommGroup X] [Module ℂ X] {x : X} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/- English proof (translation)
Rewrite using `[alt_apply, alt_apply, ← Finset.sum_neg_distrib]`. Use `Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap a b)) _ _ fun σ => ?_` and prove the remaining obligations. Establish `h1 : J ∘ ⇑(Equiv.swap a b * σ) = (J ∘ Equiv.swap a b) ∘ σ`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Simplify using `only [Equiv.coe_mulLeft, h1, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h]`. Use `push_cast`. Rewrite using `[neg_one_mul, neg_smul, neg_neg]`.
-/
theorem alt_swap {X : Type} [AddCommGroup X] [Module ℂ X] (g : TV n X (Fin n)) (J : Fin n → Fin n) (a b : Fin n)
    (h : a ≠ b) : alt Finset.univ g (J ∘ Equiv.swap a b) = -alt Finset.univ g J := by
  rw [alt_apply, alt_apply, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap a b)) _ _ fun σ => ?_
  have h1 : J ∘ ⇑(Equiv.swap a b * σ) = (J ∘ Equiv.swap a b) ∘ σ := by
    funext x; simp
  simp only [Equiv.coe_mulLeft, h1, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h]
  push_cast
  rw [neg_one_mul, neg_smul, neg_neg]

/- English proof (translation)
Establish `hz : ∀ K : Fin n → Fin n, ∀ a b, a ≠ b → K a = K b → h K = 0`. Introduce `K a b hab hK`. Establish `hc : K ∘ Equiv.swap a b = K`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_def]`.

Use `split_ifs with h1 h2`. Rewrite using `[h1, hK]`. Rewrite using `[h2, hK]`. Both sides reduce to the same expression. Use `hanti K a b hab` as an intermediate fact.

Rewrite `this` using `[hc]`. Use function extensionality and compare the values at `I`. Conclude with `eq_zero_of_eq_neg' (congrFun this I)`. Distinguish the cases in `hJ : Function.Injective J`. Take `⟨p, hp⟩` from `(Finite.injective_iff_surjective.mp hJ) (I 0)`.

Rewrite using `[Finset.sum_eq_single p]`. Rewrite using `[← hp, Function.update_eq_self, hp, Function.update_eq_self]`. Introduce `j _ hj`. Rewrite using `[hz (Function.update J j (I 0)) j p hj (by simp [Function.update_of_ne (Ne.symm hj), hp]), Pi.zero_apply]`. Simplify using the standard rewrite rules.

Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab, hne⟩ : ∃ a b, J a = J b ∧ a ≠ b := by`. Simplify using `only [Function.Injective, not_forall] at hJ`. Take `⟨a, b, h1, h2⟩` from `hJ`. Conclude with `⟨a, b, h1, h2⟩`. Rewrite using `[hz J a b hne hab, Pi.zero_apply, Fintype.sum_eq_add a b hne]`.

Establish `hc : Function.update J b (I 0) = Function.update J a (I 0) ∘ Equiv.swap a b`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_def]`. Distinguish the cases in `h1 : x = a`. Substitute `h1` using the available equality.

Rewrite using `[if_pos rfl, Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne), hab]`. Rewrite using `[if_neg h1]`. Distinguish the cases in `h2 : x = b`. Substitute `h2` using the available equality. Rewrite using `[if_pos rfl, Function.update_self, Function.update_self]`.

Rewrite using `[if_neg h2, Function.update_of_ne h2, Function.update_of_ne h1]`. Rewrite using `[hc, hanti _ a b hne, hab]`. Simplify using the standard rewrite rules. Introduce and unpack `c ⟨hca, hcb⟩`. Rewrite using `[hz _ a b hne (by simp [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb), hab]), Pi.zero_apply]`.
-/
theorem sum_swap {X : Type} [AddCommGroup X] [Module ℂ X] (h : (Fin n → Fin n) → (Fin 1 → Fin n) → X)
    (hanti : ∀ J a b, a ≠ b → h (J ∘ Equiv.swap a b) = -h J) (J : Fin n → Fin n) (I : Fin 1 → Fin n) :
    ∑ j, h (Function.update J j (I 0)) (Function.update I 0 (J j)) = h J I := by
  classical
  have hz : ∀ K : Fin n → Fin n, ∀ a b, a ≠ b → K a = K b → h K = 0 := by
    intro K a b hab hK
    have hc : K ∘ Equiv.swap a b = K := by
      funext x
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hK]
      · rw [h2, hK]
      · rfl
    have := hanti K a b hab
    rw [hc] at this
    funext I
    exact eq_zero_of_eq_neg' (congrFun this I)
  by_cases hJ : Function.Injective J
  · obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.mp hJ) (I 0)
    rw [Finset.sum_eq_single p]
    · rw [← hp, Function.update_eq_self, hp, Function.update_eq_self]
    · intro j _ hj
      rw [hz (Function.update J j (I 0)) j p hj (by simp [Function.update_of_ne (Ne.symm hj), hp]), Pi.zero_apply]
    · simp
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, J a = J b ∧ a ≠ b := by
      simp only [Function.Injective, not_forall] at hJ
      obtain ⟨a, b, h1, h2⟩ := hJ
      exact ⟨a, b, h1, h2⟩
    rw [hz J a b hne hab, Pi.zero_apply, Fintype.sum_eq_add a b hne]
    · have hc : Function.update J b (I 0) = Function.update J a (I 0) ∘ Equiv.swap a b := by
        funext x
        simp only [Function.comp_apply, Equiv.swap_apply_def]
        by_cases h1 : x = a
        · subst h1
          rw [if_pos rfl, Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne), hab]
        · rw [if_neg h1]
          by_cases h2 : x = b
          · subst h2
            rw [if_pos rfl, Function.update_self, Function.update_self]
          · rw [if_neg h2, Function.update_of_ne h2, Function.update_of_ne h1]
      rw [hc, hanti _ a b hne, hab]
      simp
    · rintro c ⟨hca, hcb⟩
      rw [hz _ a b hne (by simp [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb), hab]),
        Pi.zero_apply]

def rot (n : ℕ) : Equiv.Perm (Fin (1 + n)) where
  toFun k := if h : (k : ℕ) < n then ⟨k + 1, by omega⟩ else ⟨0, by omega⟩
  invFun k := if h : (k : ℕ) = 0 then ⟨n, by omega⟩ else ⟨k - 1, by omega⟩
  left_inv k := by
    apply Fin.ext; by_cases h : (k : ℕ) < n <;> simp [h] <;> omega
  right_inv k := by
    apply Fin.ext
    by_cases h : (k : ℕ) = 0
    · simp [h]
    · have h' : (k : ℕ) - 1 < n := by omega
      simp [h, h']; omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[rot, i.2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rot_nat (i : Fin n) (h : (i : ℕ) < 1 + n) : rot n ⟨i, h⟩ = Fin.natAdd 1 i := by
  apply Fin.ext; simp [rot, i.2]; omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[rot, h]`.
-/
theorem rot_last (k : Fin (1 + n)) (h : (k : ℕ) = n) : rot n k = Fin.castAdd n 0 := by
  apply Fin.ext; simp [rot, h]

/- English proof (translation)
Use `Finset.sum_bij' (fun a ha => ⟨a, ?_⟩) (fun b _ => ⟨b, by omega⟩) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at ha`. Use linear arithmetic over natural numbers and integers. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`.

Conclude with `ha`. Introduce `b hb`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢`. Conclude with `hb`. Introduce `a ha`.

Both sides reduce to the same expression. Introduce `b hb`. Both sides reduce to the same expression. Introduce `a ha`. Both sides reduce to the same expression.
-/
theorem sum_lt_cast {X : Type} [AddCommMonoid X] (k : Fin (1 + n)) (hk : (k : ℕ) ≤ n) (f : Fin (1 + n) → X) :
    ∑ i ∈ Finset.univ.filter (· < k), f i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), f ⟨i, by omega⟩ := by
  refine Finset.sum_bij' (fun a ha => ⟨a, ?_⟩) (fun b _ => ⟨b, by omega⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at ha; omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb
  · intro a ha; rfl
  · intro b hb; rfl
  · intro a ha; rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) x` and prove the remaining obligations. Establish `hi : i = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Simplify using `[Equiv.swap_apply_right, Fin.append_left, Fin.append_right]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Fin.append_left, Fin.append_right]`. Establish `h1 : Fin.natAdd 1 i ≠ Fin.natAdd 1 j` using `fun h' => h (Fin.ext (by`. Use `congrArg Fin.val h'` as an intermediate fact.

Simplify using `at this`. Use the proof step `omega))`. Establish `h2 : Fin.natAdd 1 i ≠ Fin.castAdd n 0` using `fun h' => by`. Use `congrArg Fin.val h'` as an intermediate fact. Simplify using `at this`.

Rewrite using `[Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right, Fin.append_right, Function.update_of_ne h]`.
-/
theorem app_swap (I : Fin 1 → Fin n) (J : Fin n → Fin n) (j : Fin n) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd 1 j) (Fin.castAdd n 0) =
      Fin.append (Function.update I 0 (J j)) (Function.update J j (I 0)) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Equiv.swap_apply_right, Fin.append_left, Fin.append_right]
  · by_cases h : i = j
    · subst h; simp [Fin.append_left, Fin.append_right]
    · have h1 : Fin.natAdd 1 i ≠ Fin.natAdd 1 j := fun h' => h (Fin.ext (by
        have := congrArg Fin.val h'; simp at this; omega))
      have h2 : Fin.natAdd 1 i ≠ Fin.castAdd n 0 := fun h' => by
        have := congrArg Fin.val h'; simp at this
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right, Fin.append_right,
        Function.update_of_ne h]

/- English proof (translation)
Establish `h4` using `(hT n M (Fin N) E hE Finset.univ).2.2.2`. Establish `hinv : (pm σ * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) = 1` using `by rw [← pm_mul, mul_inv_cancel, pm_one]`. Rewrite using `[xJ, mul_add, add_mul, h4, mul_assoc, hinv, mul_one, Finset.mul_sum, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← pm_mul, ← pm_mul, Equiv.swap_apply_apply]`.
-/
theorem conj_xJ {N : ℕ} (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E)
    (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    (pm σ * xJ E k * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) =
      Om E (σ k) + ∑ i ∈ Finset.univ.filter (· < k), pm (Equiv.swap (σ i) (σ k)) := by
  have h4 := (hT n M (Fin N) E hE Finset.univ).2.2.2
  have hinv : (pm σ * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) = 1 := by rw [← pm_mul, mul_inv_cancel, pm_one]
  rw [xJ, mul_add, add_mul, h4, mul_assoc, hinv, mul_one, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pm_mul, ← pm_mul, Equiv.swap_apply_apply]

/- English proof (translation)
Use extensionality with `w`. Set `g : TV n W (Fin n)` to `fun J => if J = id then w else 0`. Establish `hg : alt Finset.univ g id = w`. Rewrite using `[alt_apply, Finset.sum_eq_single 1]`. Simplify using `[g]`.

Introduce `σ _ hσ`. Establish `hs : (id ∘ ⇑σ) ≠ id` using `fun h' => hσ (Equiv.ext fun x => congrFun h' x)`. Simplify using `only [g, if_neg hs, smul_zero]`. Simplify using the standard rewrite rules. Use `congrArg (fun T : Module.End ℂ (TV n W (Fin n)) => T g id) h` as an intermediate fact.

Simplify `this` using `only [Module.End.mul_apply, lift_apply, hg]`.
-/
theorem ext_of_alt {W : Type} [AddCommGroup W] [Module ℂ W] {X Y : Module.End ℂ W}
    (h : (lift X : Module.End ℂ (TV n W (Fin n))) * alt Finset.univ = lift Y * alt Finset.univ) : X = Y := by
  classical
  ext w
  let g : TV n W (Fin n) := fun J => if J = id then w else 0
  have hg : alt Finset.univ g id = w := by
    rw [alt_apply, Finset.sum_eq_single 1]
    · simp [g]
    · intro σ _ hσ
      have hs : (id ∘ ⇑σ) ≠ id := fun h' => hσ (Equiv.ext fun x => congrFun h' x)
      simp only [g, if_neg hs, smul_zero]
    · simp
  have := congrArg (fun T : Module.End ℂ (TV n W (Fin n)) => T g id) h
  simpa only [Module.End.mul_apply, lift_apply, hg] using this

end PStepFormula

end PositivityTheory.Rg.Cz

end
