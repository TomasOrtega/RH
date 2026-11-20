import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpTanL
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFinrankTwoCocyclesCharRatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsSp4RootVectorUniqueOnWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedHomOfFrobeniusValue
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

section Core

variable {H E : Type} [Group H] [Field E]

/- English proof (translation)
Use `show adj X = -X ↔ _`. Rewrite using `[← Matrix.ext_iff]`. Both sides reduce to the same expression.
-/
private theorem mem_sp4_iff {X : M4 E} : X ∈ sp4 E ↔ ∀ a b, (sgn a * sgn b) • X b.rev a.rev = -X a b := by
  show adj X = -X ↔ _
  rw [← Matrix.ext_iff]
  rfl

/- English proof (translation)
Establish `key : ∀ (r : H → M4 (DualNumber E)), (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) → ∀ g h a b, (r (g * h) a b = (r g * r h) a b ↔ γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b)`. Introduce `r hr g h a b`. Establish `hf : ∀ g a b, (r g a b).fst = if a = b then (χ a g : E) else 0` using `fun g a b => by rw [hr]; rfl`. Establish `hs : ∀ g a b, (r g a b).snd = γ g a b * χ b g` using `fun g a b => by rw [hr]; rfl`. Establish `u1` using `Units.ne_zero (χ b g)`.

Establish `u2` using `Units.ne_zero (χ b h)`. Rewrite using `[TrivSqZeroExt.ext_iff, Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.fst_sum]`. Simplify using `only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, hf, hs, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, Units.val_mul]`. Apply the tactic sequence `rw [and_iff_right (by split_ifs with h <;> simp [h])]`. Prove the components needed by the constructor for the conclusion.

Introduce `e`. Clear the denominators using the available nonvanishing facts. Apply `mul_right_cancel₀ u2` to reduce the goal to its premises. Take the linear combination `e`. Introduce `e`.

Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun ⟨r, hr⟩ g h a b => (key r hr g h a b).1 (by rw [map_mul]), fun hz => ?_⟩` and prove the remaining obligations. Set `r : H → M4 (DualNumber E)` to `fun g => Matrix.of fun a b => ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩`.

Use `⟨⟨⟨r, ?_⟩, fun g h => Matrix.ext fun a b => (key r (fun _ _ _ => rfl) g h a b).2 (hz g h a b)⟩, fun _ _ _ => rfl⟩` and prove the remaining obligations. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `h1 : γ 1 a b = 0` using `by simpa using hz 1 1 a b`. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Use `show (if a = b then (χ a 1 : E) else 0) = _`.

Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Use `show γ 1 a b * χ b 1 = _`.

Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[h1]`. Simplify using `[h, h1]`.
-/
private theorem hom_iff (χ : Fin 4 → H →* Eˣ) (γ : H → M4 E) :
    (∃ r : H →* M4 (DualNumber E), ∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) ↔
      ∀ g h a b, γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b := by
  have key : ∀ (r : H → M4 (DualNumber E)),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) → ∀ g h a b,
      (r (g * h) a b = (r g * r h) a b ↔ γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b) := by
    intro r hr g h a b
    have hf : ∀ g a b, (r g a b).fst = if a = b then (χ a g : E) else 0 := fun g a b => by rw [hr]; rfl
    have hs : ∀ g a b, (r g a b).snd = γ g a b * χ b g := fun g a b => by rw [hr]; rfl
    have u1 := Units.ne_zero (χ b g)
    have u2 := Units.ne_zero (χ b h)
    rw [TrivSqZeroExt.ext_iff, Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.fst_sum]
    simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, hf, hs, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, Units.val_mul]
    rw [and_iff_right (by split_ifs with h <;> simp [h])]
    constructor
    · intro e
      field_simp
      apply mul_right_cancel₀ u2
      linear_combination e
    · intro e
      rw [e]
      field_simp
      ring
  refine ⟨fun ⟨r, hr⟩ g h a b => (key r hr g h a b).1 (by rw [map_mul]), fun hz => ?_⟩
  let r : H → M4 (DualNumber E) := fun g => Matrix.of fun a b => ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩
  refine ⟨⟨⟨r, ?_⟩, fun g h => Matrix.ext fun a b => (key r (fun _ _ _ => rfl) g h a b).2 (hz g h a b)⟩,
    fun _ _ _ => rfl⟩
  refine Matrix.ext fun a b => ?_
  have h1 : γ 1 a b = 0 := by simpa using hz 1 1 a b
  refine TrivSqZeroExt.ext ?_ ?_
  · show (if a = b then (χ a 1 : E) else 0) = _
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  · show γ 1 a b * χ b 1 = _
    by_cases h : a = b
    · subst h; simp [h1]
    · simp [h, h1]

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem wt_fib : ∀ a b a' b' : Fin 4, a ≠ b → wt a' b' = wt a b →
    (a' = a ∧ b' = b) ∨ (a' = b.rev ∧ b' = a.rev) := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem wt_cases : ∀ j ∈ wts, j = 0 ∨ (∃ a b : Fin 4, a < b ∧ wt a b = j ∧ dimsL j = 2) ∨
    ∃ a b : Fin 4, b < a ∧ wt a b = j ∧ dimsL j = 1 := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem wt_pos_ne : ∀ a b a' b' : Fin 4, a < b → b' ≤ a' → wt a' b' ≠ wt a b := by decide

/- English proof (translation)
Rewrite using `[dimsL, if_neg h, if_neg]`. Apply the tactic sequence `rintro (rfl | rfl | rfl | rfl | rfl) <;> exact h (by decide)`.
-/
private theorem dimsL_out (j : ℤ × ℤ) (h : j ∉ wts) : dimsL j = 0 := by
  rw [dimsL, if_neg h, if_neg]
  rintro (rfl | rfl | rfl | rfl | rfl) <;> exact h (by decide)

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem sgn_rev : ∀ a b : Fin 4, sgn b.rev * sgn a.rev = sgn a * sgn b := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem sgn_sq : ∀ a b : Fin 4, sgn a * sgn b * (sgn a * sgn b) = 1 := by decide

/- English proof (translation)
Use `⟨Matrix.single a b 1 - adj (Matrix.single a b 1), mem_sp4_iff.2 fun i j => ?_, ?_, fun i j h => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.sub_apply, adj_apply, Fin.rev_rev, sgn_rev, smul_sub, smul_smul, sgn_sq, one_smul, neg_sub]`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [adj_apply, sgn, Fin.rev, Matrix.single_apply] <;> norm_num`. Rewrite using `[Matrix.sub_apply, adj_apply, Matrix.single_apply_of_ne, Matrix.single_apply_of_ne, smul_zero, sub_zero]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `h (wt_rev _ _).symm`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `h rfl`.
-/
private theorem ex_root [CharZero E] (a b : Fin 4) :
    ∃ X ∈ sp4 E, X a b ≠ 0 ∧ ∀ a' b', wt a' b' ≠ wt a b → X a' b' = 0 := by
  refine ⟨Matrix.single a b 1 - adj (Matrix.single a b 1), mem_sp4_iff.2 fun i j => ?_, ?_, fun i j h => ?_⟩
  · simp only [Matrix.sub_apply, adj_apply, Fin.rev_rev, sgn_rev, smul_sub, smul_smul, sgn_sq, one_smul, neg_sub]
  · fin_cases a <;> fin_cases b <;> simp [adj_apply, sgn, Fin.rev, Matrix.single_apply] <;> norm_num
  · rw [Matrix.sub_apply, adj_apply, Matrix.single_apply_of_ne, Matrix.single_apply_of_ne, smul_zero, sub_zero]
    · rintro ⟨rfl, rfl⟩
      exact h (wt_rev _ _).symm
    · rintro ⟨rfl, rfl⟩
      exact h rfl

variable [TopologicalSpace H] [TopologicalSpace E] [IsTopologicalRing E]

private def Q (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (j : ℤ × ℤ) (γ : H → M4 E) : Prop :=
  (∀ g h a b, γ (g * h) a b = γ g a b + (χ a g : E) / χ b g * γ h a b) ∧ (∀ g, γ g ∈ sp4 E) ∧
    (∃ X ∈ sp4 E, ∀ g a b, b < a → γ g a b = (1 - (χ a g : E) / χ b g) * X a b) ∧ (∀ s, I s → ∀ a, γ s a a = 0) ∧
      (∀ a b, Continuous fun g => γ g a b) ∧ ∀ g a b, wt a b ≠ j → γ g a b = 0

/- English proof (translation)
Establish `hab : a ≠ b` using `hba.ne'`. Establish `hr : ∀ g a b, (χ b.rev g : E) / χ a.rev g = χ a g / χ b g` using `fun g a b => by`. Rewrite using `[div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), hθ, mul_comm, hθ]`. Establish `hw : ∀ a', wt a' a' ≠ wt a b` using `fun a' h => hab ((wt_eq_zero a b).1 (h.symm.trans ((wt_eq_zero _ _).2 rfl)))`. Take `⟨X, hX, hX0, hXw⟩` from `ex_root (E := E) a b`.

Set `v : H → M4 E` to `fun g => Matrix.of fun a b => (1 - (χ a g : E) / χ b g) * X a b`. Establish `hv : ∀ g a b, v g a b = (1 - (χ a g : E) / χ b g) * X a b` using `fun _ _ _ => rfl`. Establish `hvS : v ∈ S`. Use `(hS v).2 ⟨fun g h a b => ?_, fun g => mem_sp4_iff.2 fun a b => ?_, ⟨X, hX, fun g a b _ => rfl⟩, fun s _ a' => ?_, fun a b => ?_, fun g a' b' h => ?_⟩` and prove the remaining obligations. Establish `u1` using `Units.ne_zero (χ b g)`.

Establish `u2` using `Units.ne_zero (χ b h)`. Simplify using `only [hv, map_mul, Units.val_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hv, hv, hr, ← mul_smul_comm, mem_sp4_iff.1 hX, mul_neg]`.

Rewrite using `[hv, hXw _ _ (hw a'), mul_zero]`. Conclude with `(continuous_const.sub (hc a b)).mul continuous_const`. Rewrite using `[hv, hXw _ _ h, mul_zero]`. Establish `hk : 1 - (χ a g0 : E) / χ b g0 ≠ 0` using `fun h => h0 (Units.ext ((div_eq_one_iff_eq (Units.ne_zero _)).1 (sub_eq_zero.1 h).symm))`. Use `(finrank_eq_one_iff_of_nonzero' (⟨v, hvS⟩ : S) fun h => ?_).2 fun ⟨γ, hγ⟩ => ?_` and prove the remaining obligations.

Use `congrFun (congrFun (congrFun (congrArg Subtype.val h) g0) a) b` as an intermediate fact. Conclude with `mul_ne_zero hk hX0 this`. Take `⟨-, h1, ⟨Y, hY, h2⟩, -, -, h3⟩` from `(hS γ).1 hγ`. Use `⟨Y a b / X a b, Subtype.ext (funext fun g => Matrix.ext fun a' b' => ?_)⟩` and prove the remaining obligations. Use `show Y a b / X a b * v g a' b' = γ g a' b'`.

Establish `e : Y a b / X a b * v g a b = γ g a b`. Rewrite using `[hv, h2 g a b hba]`. Clear the denominators using the available nonvanishing facts. Distinguish the cases in `h : wt a' b' = wt a b`. Break down `wt_fib a b a' b' hab h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases.

Conclude with `e`. Establish `e1` using `mem_sp4_iff.1 (h1 g) b.rev a.rev`. Establish `e2` using `mem_sp4_iff.1 (((hS v).1 hvS).2.1 g) b.rev a.rev`. Rewrite `e1`, `e2` using `[Fin.rev_rev, Fin.rev_rev]`. Rewrite using `[← neg_inj, ← e1, ← mul_neg, ← e2, ← e, mul_smul_comm]`.

Rewrite using `[h3 g a' b' h, hv, hXw _ _ h, mul_zero, mul_zero]`.
-/
private theorem dim_root [CharZero E] (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (θ : H → E)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (hc : ∀ a b, Continuous fun g => (χ a g : E) / χ b g)
    (a b : Fin 4) (hba : b < a) (g0 : H) (h0 : χ a g0 ≠ χ b g0) (S : Submodule E (H → M4 E))
    (hS : ∀ γ, γ ∈ S ↔ Q χ I (wt a b) γ) : finrank E S = 1 := by
  have hab : a ≠ b := hba.ne'
  have hr : ∀ g a b, (χ b.rev g : E) / χ a.rev g = χ a g / χ b g := fun g a b => by
    rw [div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), hθ, mul_comm, hθ]
  have hw : ∀ a', wt a' a' ≠ wt a b := fun a' h => hab ((wt_eq_zero a b).1 (h.symm.trans ((wt_eq_zero _ _).2 rfl)))
  obtain ⟨X, hX, hX0, hXw⟩ := ex_root (E := E) a b
  let v : H → M4 E := fun g => Matrix.of fun a b => (1 - (χ a g : E) / χ b g) * X a b
  have hv : ∀ g a b, v g a b = (1 - (χ a g : E) / χ b g) * X a b := fun _ _ _ => rfl
  have hvS : v ∈ S := by
    refine (hS v).2 ⟨fun g h a b => ?_, fun g => mem_sp4_iff.2 fun a b => ?_, ⟨X, hX, fun g a b _ => rfl⟩,
      fun s _ a' => ?_, fun a b => ?_, fun g a' b' h => ?_⟩
    · have u1 := Units.ne_zero (χ b g)
      have u2 := Units.ne_zero (χ b h)
      simp only [hv, map_mul, Units.val_mul]
      field_simp
      ring
    · rw [hv, hv, hr, ← mul_smul_comm, mem_sp4_iff.1 hX, mul_neg]
    · rw [hv, hXw _ _ (hw a'), mul_zero]
    · exact (continuous_const.sub (hc a b)).mul continuous_const
    · rw [hv, hXw _ _ h, mul_zero]
  have hk : 1 - (χ a g0 : E) / χ b g0 ≠ 0 := fun h =>
    h0 (Units.ext ((div_eq_one_iff_eq (Units.ne_zero _)).1 (sub_eq_zero.1 h).symm))
  refine (finrank_eq_one_iff_of_nonzero' (⟨v, hvS⟩ : S) fun h => ?_).2 fun ⟨γ, hγ⟩ => ?_
  · have := congrFun (congrFun (congrFun (congrArg Subtype.val h) g0) a) b
    exact mul_ne_zero hk hX0 this
  · obtain ⟨-, h1, ⟨Y, hY, h2⟩, -, -, h3⟩ := (hS γ).1 hγ
    refine ⟨Y a b / X a b, Subtype.ext (funext fun g => Matrix.ext fun a' b' => ?_)⟩
    show Y a b / X a b * v g a' b' = γ g a' b'
    have e : Y a b / X a b * v g a b = γ g a b := by
      rw [hv, h2 g a b hba]
      field_simp
    by_cases h : wt a' b' = wt a b
    · rcases wt_fib a b a' b' hab h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact e
      · have e1 := mem_sp4_iff.1 (h1 g) b.rev a.rev
        have e2 := mem_sp4_iff.1 (((hS v).1 hvS).2.1 g) b.rev a.rev
        rw [Fin.rev_rev, Fin.rev_rev] at e1 e2
        rw [← neg_inj, ← e1, ← mul_neg, ← e2, ← e, mul_smul_comm]
    · rw [h3 g a' b' h, hv, hXw _ _ h, mul_zero, mul_zero]

/- English proof (translation)
Establish `hr : ∀ g a b, (χ b.rev g : E) / χ a.rev g = χ a g / χ b g` using `fun g a b => by`. Rewrite using `[div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), hθ, mul_comm, hθ]`. Take `⟨X, hX, hX1, hXw, hY⟩` from `UpperTheory.exists_sp4_root_vector_unique_on_weight E a b hab.ne`. Set `f : S →ₗ[E] T` to `{ toFun := fun γ => ⟨fun g => γ.1 g a b, (hT _).2 ⟨((hS _).1 γ.2).2.2.2.2.1 a b, fun g h => ((hS _).1 γ.2).1 g h a b⟩⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hf : Function.Bijective f`.

Use `⟨(injective_iff_map_eq_zero f).2 fun ⟨γ, hγ⟩ h => ?_, fun ⟨z, hz⟩ => ?_⟩` and prove the remaining obligations. Take `⟨-, h2, -, -, -, h5⟩` from `(hS γ).1 hγ`. Use `Subtype.ext (funext fun g => Matrix.ext fun a' b' => ?_)` and prove the remaining obligations. Use `show γ g a' b' = 0`. Establish `h0 : γ g a b = 0` using `congrFun (congrArg Subtype.val h) g`.

Distinguish the cases in `e : wt a' b' = wt a b`. Rewrite using `[hY _ (h2 g) a' b' e, h0, zero_mul]`. Conclude with `h5 g a' b' e`. Take `⟨z1, z2⟩` from `(hT z).1 hz`. Set `γ : H → M4 E` to `fun g => z g • X`.

Establish `hγ : ∀ g a b, γ g a b = z g * X a b` using `fun _ _ _ => rfl`. Use `⟨⟨γ, (hS γ).2 ⟨fun g h a' b' => ?_, fun g => Submodule.smul_mem _ _ hX, ⟨0, zero_mem _, fun g a' b' h => ?_⟩, fun s _ a' => ?_, fun a' b' => z1.mul continuous_const, fun g a' b' h => ?_⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hγ]`. Distinguish the cases in `e : wt a' b' = wt a b`. Break down `wt_fib a b a' b' hab.ne e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases.

Rewrite using `[z2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[z2, hr]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hXw _ _ e]`.

Rewrite using `[hγ, hXw _ _ (wt_pos_ne a b a' b' hab h.le), mul_zero, Matrix.zero_apply, mul_zero]`. Rewrite using `[hγ, hXw _ _ (wt_pos_ne a b a' a' hab le_rfl), mul_zero]`. Rewrite using `[hγ, hXw _ _ h, mul_zero]`. Conclude with `Subtype.ext (funext fun g => (hγ g a b).trans (by rw [hX1, mul_one]))`. Conclude with `(LinearEquiv.ofBijective f hf).finrank_eq`.
-/
private theorem dim_pos [CharZero E] (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (θ : H → E)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (a b : Fin 4) (hab : a < b) (T : Submodule E (H → E))
    (hT : ∀ z, z ∈ T ↔ Continuous z ∧ ∀ g h, z (g * h) = z g + (χ a g : E) / χ b g * z h)
    (S : Submodule E (H → M4 E)) (hS : ∀ γ, γ ∈ S ↔ Q χ I (wt a b) γ) : finrank E S = finrank E T := by
  have hr : ∀ g a b, (χ b.rev g : E) / χ a.rev g = χ a g / χ b g := fun g a b => by
    rw [div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), hθ, mul_comm, hθ]
  obtain ⟨X, hX, hX1, hXw, hY⟩ := UpperTheory.exists_sp4_root_vector_unique_on_weight E a b hab.ne
  let f : S →ₗ[E] T :=
    { toFun := fun γ => ⟨fun g => γ.1 g a b, (hT _).2
        ⟨((hS _).1 γ.2).2.2.2.2.1 a b, fun g h => ((hS _).1 γ.2).1 g h a b⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun ⟨γ, hγ⟩ h => ?_, fun ⟨z, hz⟩ => ?_⟩
    · obtain ⟨-, h2, -, -, -, h5⟩ := (hS γ).1 hγ
      refine Subtype.ext (funext fun g => Matrix.ext fun a' b' => ?_)
      show γ g a' b' = 0
      have h0 : γ g a b = 0 := congrFun (congrArg Subtype.val h) g
      by_cases e : wt a' b' = wt a b
      · rw [hY _ (h2 g) a' b' e, h0, zero_mul]
      · exact h5 g a' b' e
    · obtain ⟨z1, z2⟩ := (hT z).1 hz
      let γ : H → M4 E := fun g => z g • X
      have hγ : ∀ g a b, γ g a b = z g * X a b := fun _ _ _ => rfl
      refine ⟨⟨γ, (hS γ).2 ⟨fun g h a' b' => ?_, fun g => Submodule.smul_mem _ _ hX,
        ⟨0, zero_mem _, fun g a' b' h => ?_⟩, fun s _ a' => ?_, fun a' b' => z1.mul continuous_const,
        fun g a' b' h => ?_⟩⟩, ?_⟩
      · simp only [hγ]
        by_cases e : wt a' b' = wt a b
        · rcases wt_fib a b a' b' hab.ne e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [z2]; ring
          · rw [z2, hr]; ring
        · simp [hXw _ _ e]
      · rw [hγ, hXw _ _ (wt_pos_ne a b a' b' hab h.le), mul_zero, Matrix.zero_apply, mul_zero]
      · rw [hγ, hXw _ _ (wt_pos_ne a b a' a' hab le_rfl), mul_zero]
      · rw [hγ, hXw _ _ h, mul_zero]
      · exact Subtype.ext (funext fun g => (hγ g a b).trans (by rw [hX1, mul_one]))
  exact (LinearEquiv.ofBijective f hf).finrank_eq

/- English proof (translation)
Set `f : S →ₗ[E] E × E` to `{ toFun := fun γ => (γ.1 σ 0 0, γ.1 σ 1 1) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hf : Function.Bijective f`. Use `⟨(injective_iff_map_eq_zero f).2 fun ⟨γ, hγ⟩ h => ?_, fun ⟨x, y⟩ => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, -, h3, h4, h5⟩` from `(hS γ).1 hγ`. Establish `hd : ∀ a, γ σ a a = 0 → ∀ g, γ g a a = 0` using `fun a ha g => congrFun (hun (fun g => γ g a a) (h4 a a) (fun g h => by simpa using h1 g h a a) (fun g hg => h3 g hg a) ha) g`.

Establish `d0` using `hd 0 (congrArg Prod.fst h)`. Establish `d1` using `hd 1 (congrArg Prod.snd h)`. Use `Subtype.ext (funext fun g => Matrix.ext fun a b => ?_)` and prove the remaining obligations. Use `show γ g a b = 0`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Establish `e` using `mem_sp4_iff.1 (h2 g) a a`. Use `fin_cases a`. Conclude with `d0 g`. Conclude with `d1 g`.

Conclude with `neg_eq_zero.1 (e.symm.trans ((congrArg _ (d1 g)).trans (smul_zero _)))`. Conclude with `neg_eq_zero.1 (e.symm.trans ((congrArg _ (d0 g)).trans (smul_zero _)))`. Conclude with `h5 g a b fun e => hab ((wt_eq_zero a b).1 e)`. Take `⟨u, u1, u2, u3, u4⟩` from `hex x`. Take `⟨w, w1, w2, w3, w4⟩` from `hex y`.

Set `γ : H → M4 E` to `fun g => Matrix.diagonal ![u g, w g, -w g, -u g]`. Use `⟨⟨γ, (hS γ).2 ⟨fun g h a b => ?_, fun g => mem_sp4_iff.2 fun a b => ?_, ⟨0, zero_mem _, fun g a b h => by simp [γ, h.ne']⟩, fun s hs a => ?_, fun a b => ?_, fun g a b h => ?_⟩⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hab : a = b`. Apply the tactic sequence `subst hab fin_cases a <;> simp [γ, u2, w2, add_comm]`. Simplify using `[γ, hab]`.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [γ, sgn, Fin.rev, Matrix.diagonal_apply]`. Apply the tactic sequence `fin_cases a <;> simp [γ, u3 s hs, w3 s hs]`. Distinguish the cases in `hab : a = b`. Substitute `hab fin_cases a exacts [u1, w1, w1.neg, u1.neg]` using the available equality. Simplify using `[γ, hab, continuous_const]`.

Conclude with `Matrix.diagonal_apply_ne _ fun e => h ((wt_eq_zero a b).2 e)`. Conclude with `Prod.ext u4 w4`. Rewrite using `[(LinearEquiv.ofBijective f hf).finrank_eq]`. Simplify using the standard rewrite rules.
-/
private theorem dim_zero (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (σ : H)
    (hex : ∀ e : E, ∃ u : H → E, Continuous u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g, I g → u g = 0) ∧ u σ = e)
    (hun : ∀ u : H → E, Continuous u → (∀ g h, u (g * h) = u g + u h) → (∀ g, I g → u g = 0) → u σ = 0 → u = 0)
    (S : Submodule E (H → M4 E)) (hS : ∀ γ, γ ∈ S ↔ Q χ I 0 γ) : finrank E S = 2 := by
  let f : S →ₗ[E] E × E :=
    { toFun := fun γ => (γ.1 σ 0 0, γ.1 σ 1 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun ⟨γ, hγ⟩ h => ?_, fun ⟨x, y⟩ => ?_⟩
    · obtain ⟨h1, h2, -, h3, h4, h5⟩ := (hS γ).1 hγ
      have hd : ∀ a, γ σ a a = 0 → ∀ g, γ g a a = 0 := fun a ha g =>
        congrFun (hun (fun g => γ g a a) (h4 a a) (fun g h => by simpa using h1 g h a a) (fun g hg => h3 g hg a) ha) g
      have d0 := hd 0 (congrArg Prod.fst h)
      have d1 := hd 1 (congrArg Prod.snd h)
      refine Subtype.ext (funext fun g => Matrix.ext fun a b => ?_)
      show γ g a b = 0
      by_cases hab : a = b
      · subst hab
        have e := mem_sp4_iff.1 (h2 g) a a
        fin_cases a
        · exact d0 g
        · exact d1 g
        · exact neg_eq_zero.1 (e.symm.trans ((congrArg _ (d1 g)).trans (smul_zero _)))
        · exact neg_eq_zero.1 (e.symm.trans ((congrArg _ (d0 g)).trans (smul_zero _)))
      · exact h5 g a b fun e => hab ((wt_eq_zero a b).1 e)
    · obtain ⟨u, u1, u2, u3, u4⟩ := hex x
      obtain ⟨w, w1, w2, w3, w4⟩ := hex y
      let γ : H → M4 E := fun g => Matrix.diagonal ![u g, w g, -w g, -u g]
      refine ⟨⟨γ, (hS γ).2 ⟨fun g h a b => ?_, fun g => mem_sp4_iff.2 fun a b => ?_,
        ⟨0, zero_mem _, fun g a b h => by simp [γ, h.ne']⟩, fun s hs a => ?_, fun a b => ?_, fun g a b h => ?_⟩⟩, ?_⟩
      · by_cases hab : a = b
        · subst hab
          fin_cases a <;> simp [γ, u2, w2, add_comm]
        · simp [γ, hab]
      · fin_cases a <;> fin_cases b <;> simp [γ, sgn, Fin.rev, Matrix.diagonal_apply]
      · fin_cases a <;> simp [γ, u3 s hs, w3 s hs]
      · by_cases hab : a = b
        · subst hab
          fin_cases a
          exacts [u1, w1, w1.neg, u1.neg]
        · simp [γ, hab, continuous_const]
      · exact Matrix.diagonal_apply_ne _ fun e => h ((wt_eq_zero a b).2 e)
      · exact Prod.ext u4 w4
  rw [(LinearEquiv.ofBijective f hf).finrank_eq]
  simp

/- English proof (translation)
Set `m : (H → M4 E) ≃ₗ[E] (H → M4 E)` to `{ toFun := fun γ g => Matrix.of fun a b => γ g a b * χ b g invFun := fun γ g => Matrix.of fun a b => γ g a b * (χ b g : E)⁻¹ map_add' := fun x y => funext fun g => Matrix.ext fun a b => add_mul _ _ _ map_smul' := fun x y => funext fun g => Matrix.ext fun a b => mul_assoc _ _ _ le …`. Establish `hm : ∀ γ g a b, m γ g a b = γ g a b * χ b g` using `fun _ _ _ _ => rfl`. Establish `hQ : ∀ γ, γ ∈ S.comap (m : (H → M4 E) →ₗ[E] (H → M4 E)) ↔ Q χ I j γ` using `fun γ => by show m γ ∈ S ↔ _`. Rewrite using `[hS]`. Simplify using `only [hm]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨r, h1, h2⟩, h3, h4⟩`. Establish `h5 : ∀ a b, Continuous fun g => γ g a b` using `fun a b => ((h3 a b).mul (hci b)).congr fun g => mul_inv_cancel_right₀ (Units.ne_zero _) _`. Take `⟨h6, h7, h8⟩` from `(hP γ r h1 h5).1 h2`. Conclude with `⟨(hom_iff χ γ).1 ⟨r, h1⟩, h6, h7, h8, h5, fun g a b h => (mul_eq_zero.1 (h4 g a b h)).resolve_right (Units.ne_zero _)⟩`.

Introduce and unpack `⟨h1, h2, h3, h4, h5, h6⟩`. Take `⟨r, hr⟩` from `(hom_iff χ γ).2 h1`. Conclude with `⟨⟨r, hr, (hP γ r hr h5).2 ⟨h2, h3, h4⟩⟩, fun a b => (h5 a b).mul (hc b), fun g a b h => by rw [h6 g a b h, zero_mul]⟩`. Rewrite using `[← (m.ofSubmodule' S).finrank_eq]`. Distinguish the cases in `h1 : j ∈ wts`.

Break down `wt_cases j h1 with rfl | ⟨a, b, hab, rfl, e⟩ | ⟨a, b, hab, rfl, e⟩` into its components or cases. Conclude with `dim_zero χ I σ hex hun _ hQ`. Take `⟨T, hT, h2⟩` from `hpos a b hab`. Rewrite using `[e, ← h2]`. Conclude with `dim_pos χ I θ hθ a b hab T hT _ hQ`.

Take `⟨g, hg⟩` from `hne a b hab.ne'`. Rewrite using `[e]`. Conclude with `dim_root χ I θ hθ (fun a b => ((hc a).mul (hci b)).congr fun g => (div_eq_mul_inv _ _).symm) a b hab g hg _ hQ`. Rewrite using `[dimsL_out j h1]`. Use `(congrArg (fun T : Submodule E (H → M4 E) => finrank E T) (eq_bot_iff.2 fun γ hγ => ?_)).trans (finrank_bot _ _)` and prove the remaining obligations.

Conclude with `funext fun g => Matrix.ext fun a b => ((hQ γ).1 hγ).2.2.2.2.2 g a b fun h => h1 (h ▸ wt_mem a b)`.
-/
private theorem dim_core [CharZero E] (χ : Fin 4 → H →* Eˣ) (I : H → Prop) (θ : H → E) (σ : H)
    (hθ : ∀ g a, (χ a.rev g : E) * χ a g = θ g) (hc : ∀ a, Continuous fun g => (χ a g : E))
    (hci : ∀ a, Continuous fun g => (χ a g : E)⁻¹) (hne : ∀ a b, a ≠ b → ∃ g, χ a g ≠ χ b g)
    (hex : ∀ e : E, ∃ u : H → E, Continuous u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g, I g → u g = 0) ∧ u σ = e)
    (hun : ∀ u : H → E, Continuous u → (∀ g h, u (g * h) = u g + u h) → (∀ g, I g → u g = 0) → u σ = 0 → u = 0)
    (hpos : ∀ a b, a < b → ∃ T : Submodule E (H → E),
      (∀ z, z ∈ T ↔ Continuous z ∧ ∀ g h, z (g * h) = z g + (χ a g : E) / χ b g * z h) ∧ finrank E T = 2)
    (P : (H →* M4 (DualNumber E)) → Prop)
    (hP : ∀ (γ : H → M4 E) (r : H →* M4 (DualNumber E)),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, γ g a b * χ b g⟩) → (∀ a b, Continuous fun g => γ g a b) →
      (P r ↔ (∀ g, γ g ∈ sp4 E) ∧ (∃ X ∈ sp4 E, ∀ g a b, b < a → γ g a b = (1 - (χ a g : E) / χ b g) * X a b) ∧
        ∀ s, I s → ∀ a, γ s a a = 0))
    (j : ℤ × ℤ) (S : Submodule E (H → M4 E))
    (hS : ∀ s, s ∈ S ↔ (∃ r : H →* M4 (DualNumber E),
      (∀ g a b, r g a b = ⟨if a = b then (χ a g : E) else 0, s g a b⟩) ∧ P r) ∧
        (∀ a b, Continuous fun g => s g a b) ∧ ∀ g a b, wt a b ≠ j → s g a b = 0) : finrank E S = dimsL j := by
  let m : (H → M4 E) ≃ₗ[E] (H → M4 E) :=
    { toFun := fun γ g => Matrix.of fun a b => γ g a b * χ b g
      invFun := fun γ g => Matrix.of fun a b => γ g a b * (χ b g : E)⁻¹
      map_add' := fun x y => funext fun g => Matrix.ext fun a b => add_mul _ _ _
      map_smul' := fun x y => funext fun g => Matrix.ext fun a b => mul_assoc _ _ _
      left_inv := fun x => funext fun g => Matrix.ext fun a b => mul_inv_cancel_right₀ (Units.ne_zero _) _
      right_inv := fun x => funext fun g => Matrix.ext fun a b => inv_mul_cancel_right₀ (Units.ne_zero _) _ }
  have hm : ∀ γ g a b, m γ g a b = γ g a b * χ b g := fun _ _ _ _ => rfl
  have hQ : ∀ γ, γ ∈ S.comap (m : (H → M4 E) →ₗ[E] (H → M4 E)) ↔ Q χ I j γ := fun γ => by
    show m γ ∈ S ↔ _
    rw [hS]
    simp only [hm]
    constructor
    · rintro ⟨⟨r, h1, h2⟩, h3, h4⟩
      have h5 : ∀ a b, Continuous fun g => γ g a b := fun a b =>
        ((h3 a b).mul (hci b)).congr fun g => mul_inv_cancel_right₀ (Units.ne_zero _) _
      obtain ⟨h6, h7, h8⟩ := (hP γ r h1 h5).1 h2
      exact ⟨(hom_iff χ γ).1 ⟨r, h1⟩, h6, h7, h8, h5, fun g a b h =>
        (mul_eq_zero.1 (h4 g a b h)).resolve_right (Units.ne_zero _)⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      obtain ⟨r, hr⟩ := (hom_iff χ γ).2 h1
      exact ⟨⟨r, hr, (hP γ r hr h5).2 ⟨h2, h3, h4⟩⟩, fun a b => (h5 a b).mul (hc b),
        fun g a b h => by rw [h6 g a b h, zero_mul]⟩
  rw [← (m.ofSubmodule' S).finrank_eq]
  by_cases h1 : j ∈ wts
  · rcases wt_cases j h1 with rfl | ⟨a, b, hab, rfl, e⟩ | ⟨a, b, hab, rfl, e⟩
    · exact dim_zero χ I σ hex hun _ hQ
    · obtain ⟨T, hT, h2⟩ := hpos a b hab
      rw [e, ← h2]
      exact dim_pos χ I θ hθ a b hab T hT _ hQ
    · obtain ⟨g, hg⟩ := hne a b hab.ne'
      rw [e]
      exact dim_root χ I θ hθ (fun a b => ((hc a).mul (hci b)).congr fun g => (div_eq_mul_inv _ _).symm)
        a b hab g hg _ hQ
  · rw [dimsL_out j h1]
    refine (congrArg (fun T : Submodule E (H → M4 E) => finrank E T) (eq_bot_iff.2 fun γ hγ => ?_)).trans (finrank_bot _ _)
    exact funext fun g => Matrix.ext fun a b => ((hQ γ).1 hγ).2.2.2.2.2 g a b fun h => h1 (h ▸ wt_mem a b)

end Core

/- English proof (translation)
Establish `: IsLocallyConstant φ` using `(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' φ.ker, h.preimage (continuous_const.mul continuous_id), by simp, fun y hy => by`. Use `MonoidHom.mem_ker.1 hy` as an intermediate fact. Rewrite `this` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `this.symm⟩`. Conclude with `(this.comp f).continuous`.
-/
private theorem cont_of_open {H O E : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group O]
    [TopologicalSpace E] (φ : H →* O) (h : IsOpen (φ.ker : Set H)) (f : O → E) : Continuous fun g => f (φ g) := by
  have : IsLocallyConstant φ := (IsLocallyConstant.iff_exists_open _).2 fun x =>
    ⟨(fun y => x⁻¹ * y) ⁻¹' φ.ker, h.preimage (continuous_const.mul continuous_id), by simp, fun y hy => by
      have := MonoidHom.mem_ker.1 hy
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm⟩
  exact (this.comp f).continuous

/- English proof (translation)
Introduce `hL Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ j S hS`. Use `haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective`. Use `haveI : IsGalois ℚ Ω := {}`. Use `letI : TopologicalSpace E := moduleTopology ℚ_[l] E`. Use `haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩`.

Use `haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E`. Take `⟨-, f2, -, -, -, f4, f3, -, -, -, -, -, f5, -⟩` from `facts D hD`. Establish `hT : l ∈ D.T` using `Finset.mem_insert_self _ _`. Establish `hp : l.Prime` using `Fact.out`. Set `ι : c.Oˣ →* Eˣ` to `Units.map (algebraMap c.O E).toMonoidHom`.

Establish `hι : Function.Injective ι` using `Units.map_injective (IsFractionRing.injective c.O E)`. Establish `hdiv : ∀ (x y : c.Oˣ), algebraMap c.O E ((x * y⁻¹ : c.Oˣ) : c.O) = algebraMap c.O E x / algebraMap c.O E y` using `fun x y => by simp [div_eq_mul_inv]`. Set `χ : Fin 4 → D.Gp l →* Eˣ` to `fun a => ι.comp ((D.ps a).comp (D.Gp l).subtype)`. Establish `hχ' : ∀ a g, (χ a g : E) = algebraMap c.O E (D.ps a g : c.Oˣ)` using `fun _ _ => rfl`. Establish `hr0 : ∀ (g : D.Gp l) a b, algebraMap c.O E (D.r0At l g a b) = if a = b then (χ a g : E) else 0` using `fun g a b => by show algebraMap c.O E (Matrix.diagonal (fun a => ((D.ps a g : c.Oˣ) : c.O)) a b) = _`.

Rewrite using `[Matrix.diagonal_apply, hχ']`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hcy : Continuous fun g => algebraMap c.O E (chiO ℚ Ω l c.O g : c.Oˣ)`. Establish `h1 : Continuous (algebraMap ℚ_[l] E)` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)`. Establish `h2 : Continuous fun g : G ℚ Ω => ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])` using `Units.continuous_val.comp (continuous_cycZ ℚ Ω l)`.

Use `(h1.comp (continuous_subtype_val.comp h2)).congr fun g => ?_` and prove the remaining obligations. Use `show algebraMap ℚ_[l] E (algebraMap ℤ_[l] ℚ_[l] _) = algebraMap c.O E (algebraMap ℤ_[l] c.O _)`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Establish `hal : Continuous fun g => algebraMap c.O E (D.al g : c.Oˣ)` using `((hcy.mul (cont_of_open D.om f5 fun u => algebraMap c.O E (u⁻¹ : c.Oˣ))).mul (cont_of_open D.ξ hD.xi_open fun u => algebraMap c.O E u)).congr fun g => by`. Simplify using `only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul, Pi.mul_apply]`.

Establish `hPs : Continuous fun g => algebraMap c.O E (D.Psi g : c.Oˣ)` using `((hcy.pow D.e).mul (cont_of_open D.ψ hD.psi_open fun u => algebraMap c.O E u)).congr fun g => by`. Simplify using `only [Raw.Psi, UpperTheory.V.Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Pi.mul_apply, Pi.pow_apply]`. Establish `hps : ∀ a, Continuous fun g => algebraMap c.O E (D.ps a g : c.Oˣ)` using `fun a => by fin_cases a`. Conclude with `(hal.mul hPs).congr fun g => (map_mul _ _ _).symm`. Conclude with `hPs`.

Conclude with `hal`. Conclude with `continuous_const (y := algebraMap c.O E 1)`. Establish `hc : ∀ a, Continuous fun g => (χ a g : E)` using `fun a => (hps a).comp continuous_subtype_val`. Take `⟨hex, hun⟩` from `UpperTheory.exists_unique_unramified_hom_of_frobenius_value l l hp (D.pl l) (hD.pl_over l hp) ⟨D.sg l, (f2 l hT).1⟩ (hD.sg_frob l hT) E`. Use `dim_core χ (fun g => (g : G ℚ Ω) ∈ D.Ip l) (fun g => algebraMap c.O E (D.th g)) ⟨D.sg l, (f2 l hT).1⟩ (fun g a => ?_) hc (fun a => ?_) (fun a b hab => ?_) hex hun (fun a b hab => ?_) (EqL D) (fun γ r hr hγ => ?_) j S (fun s => by simpa only [hr0, QCont] using hS s)` and prove the remaining obligations.

Rewrite using `[hχ', hχ', ← map_mul, ← Units.val_mul, mul_comm, ← MonoidHom.mul_apply, f4]`. Conclude with `((hc a).comp continuous_inv).congr fun g => by simp`. Conclude with `⟨D.s0, fun e => hab (f3 (congrArg Units.val (hι e)))⟩`. Establish `key` using `UpperTheory.exists_finrank_two_cocycles_char_ratio hL D hD E a b hab`. Simplify using `only [hdiv] at key`.

Conclude with `key`. Establish `key` using `spTanL D hD E γ r (fun g a b => ?_) hγ`. Simplify using `only [hdiv] at key`. Conclude with `key`. Rewrite using `[hr, hr0]`.

Use `congr 1`. Use `show _ = (γ g * (Matrix.diagonal fun a => ((D.ps a g : c.Oˣ) : c.O)).map (algebraMap c.O E)) a b`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal, hχ']`.
-/
theorem UpperTheory.tangent_space_deformation_at_l :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (j : ℤ × ℤ) (S : Submodule E (D.Gp l → M4 E)), (∀ s, s ∈ S ↔ (∃ r' : D.Gp l →* M4 (DualNumber E), (∀ g a b, r' g a b = ⟨algebraMap c.O E (D.r0At l g a b), s g a b⟩) ∧ EqL D r') ∧ (∀ a b, QCont l fun g => s g a b) ∧ ∀ g a b, wt a b ≠ j → s g a b = 0) → finrank E ↥S = dimsL j := by
  intro hL Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ j S hS
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  haveI : IsGalois ℚ Ω := {}
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  obtain ⟨-, f2, -, -, -, f4, f3, -, -, -, -, -, f5, -⟩ := facts D hD
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  have hp : l.Prime := Fact.out
  let ι : c.Oˣ →* Eˣ := Units.map (algebraMap c.O E).toMonoidHom
  have hι : Function.Injective ι := Units.map_injective (IsFractionRing.injective c.O E)
  have hdiv : ∀ (x y : c.Oˣ), algebraMap c.O E ((x * y⁻¹ : c.Oˣ) : c.O) = algebraMap c.O E x / algebraMap c.O E y :=
    fun x y => by simp [div_eq_mul_inv]
  let χ : Fin 4 → D.Gp l →* Eˣ := fun a => ι.comp ((D.ps a).comp (D.Gp l).subtype)
  have hχ' : ∀ a g, (χ a g : E) = algebraMap c.O E (D.ps a g : c.Oˣ) := fun _ _ => rfl
  have hr0 : ∀ (g : D.Gp l) a b, algebraMap c.O E (D.r0At l g a b) = if a = b then (χ a g : E) else 0 :=
    fun g a b => by
      show algebraMap c.O E (Matrix.diagonal (fun a => ((D.ps a g : c.Oˣ) : c.O)) a b) = _
      rw [Matrix.diagonal_apply, hχ']
      split_ifs <;> simp
  have hcy : Continuous fun g => algebraMap c.O E (chiO ℚ Ω l c.O g : c.Oˣ) := by
    have h1 : Continuous (algebraMap ℚ_[l] E) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)
    have h2 : Continuous fun g : G ℚ Ω => ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
    refine (h1.comp (continuous_subtype_val.comp h2)).congr fun g => ?_
    show algebraMap ℚ_[l] E (algebraMap ℤ_[l] ℚ_[l] _) = algebraMap c.O E (algebraMap ℤ_[l] c.O _)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hal : Continuous fun g => algebraMap c.O E (D.al g : c.Oˣ) :=
    ((hcy.mul (cont_of_open D.om f5 fun u => algebraMap c.O E (u⁻¹ : c.Oˣ))).mul
      (cont_of_open D.ξ hD.xi_open fun u => algebraMap c.O E u)).congr fun g => by
        simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul, Pi.mul_apply]
  have hPs : Continuous fun g => algebraMap c.O E (D.Psi g : c.Oˣ) :=
    ((hcy.pow D.e).mul (cont_of_open D.ψ hD.psi_open fun u => algebraMap c.O E u)).congr fun g => by
      simp only [Raw.Psi, UpperTheory.V.Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, map_mul,
        Units.val_pow_eq_pow_val, map_pow, Pi.mul_apply, Pi.pow_apply]
  have hps : ∀ a, Continuous fun g => algebraMap c.O E (D.ps a g : c.Oˣ) := fun a => by
    fin_cases a
    · exact (hal.mul hPs).congr fun g => (map_mul _ _ _).symm
    · exact hPs
    · exact hal
    · exact continuous_const (y := algebraMap c.O E 1)
  have hc : ∀ a, Continuous fun g => (χ a g : E) := fun a => (hps a).comp continuous_subtype_val
  obtain ⟨hex, hun⟩ := UpperTheory.exists_unique_unramified_hom_of_frobenius_value l l hp (D.pl l) (hD.pl_over l hp) ⟨D.sg l, (f2 l hT).1⟩ (hD.sg_frob l hT) E
  refine dim_core χ (fun g => (g : G ℚ Ω) ∈ D.Ip l) (fun g => algebraMap c.O E (D.th g)) ⟨D.sg l, (f2 l hT).1⟩
    (fun g a => ?_) hc (fun a => ?_) (fun a b hab => ?_) hex hun (fun a b hab => ?_) (EqL D)
    (fun γ r hr hγ => ?_) j S
    (fun s => by simpa only [hr0, QCont] using hS s)
  · rw [hχ', hχ', ← map_mul, ← Units.val_mul, mul_comm, ← MonoidHom.mul_apply, f4]
  · exact ((hc a).comp continuous_inv).congr fun g => by simp
  · exact ⟨D.s0, fun e => hab (f3 (congrArg Units.val (hι e)))⟩
  · have key := UpperTheory.exists_finrank_two_cocycles_char_ratio hL D hD E a b hab
    simp only [hdiv] at key
    exact key
  · have key := spTanL D hD E γ r (fun g a b => ?_) hγ
    · simp only [hdiv] at key
      exact key
    · rw [hr, hr0]
      congr 1
      show _ = (γ g * (Matrix.diagonal fun a => ((D.ps a g : c.Oˣ) : c.O)).map (algebraMap c.O E)) a b
      rw [Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal, hχ']
