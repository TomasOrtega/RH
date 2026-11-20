import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ONLeaves

noncomputable section

open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree

namespace GlobalTheory.FiniteGL

section Radical

variable (k : Type) [Field k] {N : ℕ}

def IsStrictBlock {k : Type} [Field k] (b : Fin N → ℕ) (X : Matrix (Fin N) (Fin N) k) : Prop :=
  ∀ i j, b j ≤ b i → X i j = 0

variable {k}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem IsStrictBlock.mul_blockTriangular {b : Fin N → ℕ} {X Y : Matrix (Fin N) (Fin N) k}
    (hX : IsStrictBlock b X) (hY : Y.BlockTriangular b) : IsStrictBlock b (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b l ≤ b i
  · rw [hX i l hl, zero_mul]
  · rw [hY (lt_of_le_of_lt hij (not_le.mp hl)), mul_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem blockTriangular_of_sub_one {b : Fin N → ℕ} {X : Matrix (Fin N) (Fin N) k}
    (hX : IsStrictBlock b (X - 1)) : X.BlockTriangular b := by
  intro i j hij
  have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
  have h := hX i j hij.le
  rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h

variable (k)

def unipRadical (b : Fin N → ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {u | IsStrictBlock b ((u : Matrix (Fin N) (Fin N) k) - 1)}
  one_mem' := by
    intro i j _
    simp
  mul_mem' := by
    intro u v hu hv i j hij
    have e : ((u * v : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 =
        ((u : Matrix (Fin N) (Fin N) k) - 1) * (v : Matrix (Fin N) (Fin N) k) +
          ((v : Matrix (Fin N) (Fin N) k) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply, (IsStrictBlock.mul_blockTriangular hu (blockTriangular_of_sub_one hv)) i j hij,
      hv i j hij, add_zero]
  inv_mem' := by
    intro u hu i j hij
    letI := u.invertible
    have hi : ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular b := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_of_sub_one hu)
    have e : ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 =
        -(((u : Matrix (Fin N) (Fin N) k) - 1) * ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) := by
      rw [sub_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, neg_sub]
    rw [e, Matrix.neg_apply, (IsStrictBlock.mul_blockTriangular hu hi) i j hij, neg_zero]

variable {k}

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_unipRadical {b : Fin N → ℕ} {u : GL (Fin N) k} :
    u ∈ unipRadical k b ↔ ∀ i j, b j ≤ b i → ((u : Matrix (Fin N) (Fin N) k) - 1) i j = 0 := Iff.rfl

def IsCuspidal {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ b : Fin N → ℕ, Monotone b → (∃ i j, b i ≠ b j) →
    ∀ v : V, (∀ u ∈ unipRadical k b, ρ u v = v) → v = 0

def twoBlocks (N a : ℕ) : Fin N → ℕ := fun i => if (i : ℕ) < a then 0 else 1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Use linear arithmetic over natural numbers and integers.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem isCuspidal_iff_twoBlocks {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal ρ ↔ ∀ a : ℕ, 0 < a → a < N →
      ∀ v : V, (∀ u ∈ unipRadical k (twoBlocks N a), ρ u v = v) → v = 0 := by
  constructor
  · intro h a ha0 haN v hv
    refine h (twoBlocks N a) ?_ ⟨⟨0, by omega⟩, ⟨a, haN⟩, ?_⟩ v hv
    · intro i j hij
      have hij' : (i : ℕ) ≤ j := hij
      simp only [twoBlocks]
      split_ifs <;> omega
    · simp [twoBlocks, ha0]
  · intro h b hb hne v hv
    classical
    obtain ⟨i₁, j₁, h₁⟩ := hne
    have hN : 0 < N := i₁.pos
    let i0 : Fin N := ⟨0, hN⟩
    have hmin : ∀ i : Fin N, b i0 ≤ b i := fun i => hb (Fin.mk_le_of_le_val (Nat.zero_le _))
    have hex : ∃ m, ∃ hm : m < N, b i0 < b ⟨m, hm⟩ := by
      by_cases hi : b i0 < b i₁
      · exact ⟨i₁, i₁.isLt, hi⟩
      · refine ⟨j₁, j₁.isLt, lt_of_le_of_ne (hmin j₁) fun he => h₁ ?_⟩
        have := hmin i₁
        change b i0 = b j₁ at he
        omega
    obtain ⟨a, haN, key⟩ : ∃ a, a < N ∧ ∀ i : Fin N, (i : ℕ) < a ↔ ¬ b i0 < b i := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun i => ⟨fun hi hlt => ?_, fun hi => ?_⟩⟩
      · exact Nat.find_min hex hi ⟨i.isLt, hlt⟩
      · by_contra hge
        obtain ⟨_, hlt⟩ := Nat.find_spec hex
        exact hi (lt_of_lt_of_le hlt (hb (Fin.mk_le_of_le_val (not_lt.mp hge))))
    refine h a ((key i0).mpr (lt_irrefl _)) haN v fun u hu => hv u ?_
    rw [mem_unipRadical] at hu ⊢
    intro i j hij
    apply hu i j
    simp only [twoBlocks]
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := (key j).mpr fun hlt => (key i).mp hi (lt_of_lt_of_le hlt hij)
      simp [hi, hj]
    · simp only [hi, if_false]
      split_ifs <;> omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem not_isCuspidal_trivial (hN : 2 ≤ N) : ¬ IsCuspidal (Representation.trivial ℂ (GL (Fin N) k) ℂ) := by
  intro h
  exact one_ne_zero ((isCuspidal_iff_twoBlocks _).mp h 1 one_pos (by omega) (1 : ℂ) fun u _ => by simp)

end Radical

section Generic

variable {k : Type} [Field k] [Fintype k] (n : ℕ)

def genericChar (ψ₀ : AddChar k ℂ) : uniSub k n →* ℂ where
  toFun u := ψ₀ (supd (((u : mirabSub k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
  map_one' := by
    rw [OneMemClass.coe_one, OneMemClass.coe_one, Units.val_one, supd_one, AddChar.map_zero_eq_one]
  map_mul' u v := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, supd_mul _ _ u.2 v.2, AddChar.map_add_eq_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem genericChar_apply (ψ₀ : AddChar k ℂ) (u : uniSub k n) :
    genericChar n ψ₀ u =
      ψ₀ (supd (((u : mirabSub k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) := rfl

def genericLine (ψ₀ : AddChar k ℂ) : Representation ℂ (uniSub k n) ℂ :=
  (Algebra.lsmul ℂ ℂ ℂ).toMonoidHom.comp (genericChar n ψ₀)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem genericLine_apply (ψ₀ : AddChar k ℂ) (u : uniSub k n) (z : ℂ) :
    genericLine n ψ₀ u z = genericChar n ψ₀ u * z := rfl

abbrev MirabInducedSpace (ψ₀ : AddChar k ℂ) : Submodule ℂ (mirabSub k n → ℂ) :=
  Representation.coindV (uniSub k n).subtype (genericLine n ψ₀)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mem_mirabInducedSpace (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ) :
    f ∈ MirabInducedSpace n ψ₀ ↔
      ∀ (u : uniSub k n) (x : mirabSub k n), f ((u : mirabSub k n) * x) = genericChar n ψ₀ u * f x := by
  rw [Representation.mem_coindV]
  simp only [Subgroup.coe_subtype, genericLine_apply]

def mirabInduced (ψ₀ : AddChar k ℂ) : Representation ℂ (mirabSub k n) (MirabInducedSpace n ψ₀) :=
  Representation.coind (uniSub k n).subtype (genericLine n ψ₀)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem mirabInduced_apply (ψ₀ : AddChar k ℂ) (h x : mirabSub k n) (f : MirabInducedSpace n ψ₀) :
    (mirabInduced n ψ₀ h f : mirabSub k n → ℂ) x = (f : mirabSub k n → ℂ) (x * h) := rfl

def restrictMirab {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (n + 1)) k) V) :
    Representation ℂ (mirabSub k n) V :=
  ρ.comp (mirabSub k n).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem restrictMirab_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (n + 1)) k) V) (h : mirabSub k n) :
    restrictMirab n ρ h = ρ (h : GL (Fin (n + 1)) k) := rfl

end Generic

section Examples

def lineRep {G : Type} [Group G] (χ : G →* ℂ) : Representation ℂ G (Fin 1 → ℂ) :=
  (Algebra.lsmul ℂ ℂ (Fin 1 → ℂ)).toMonoidHom.comp χ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lineRep_apply {G : Type} [Group G] (χ : G →* ℂ) (g : G) (v : Fin 1 → ℂ) : lineRep χ g v = χ g • v := rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.

A detailed English derivation is pending.
-/
theorem lineRep_isIrreducible {G : Type} [Group G] (χ : G →* ℂ) : (lineRep χ).IsIrreducible := by
  have hs : IsSimpleOrder (Submodule ℂ (Fin 1 → ℂ)) :=
    is_simple_module_of_finrank_eq_one (K := ℂ) (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · rcases hs.eq_bot_or_eq_top W.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

def signGL₂ : GL (Fin 2) (ZMod 2) →* ℂ :=
  ((Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)).comp
    (Equiv.Perm.sign.comp (MulAction.toPermHom (GL (Fin 2) (ZMod 2)) (Fin 2 → ZMod 2)))

def transvGL₂ : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩

/- English proof (translation)
Establish an intermediate fact. Evaluate the decidable proposition. Simplify using the standard rewrite rules.
-/
theorem signGL₂_transv : signGL₂ transvGL₂ = -1 := by
  have h : Equiv.Perm.sign (MulAction.toPerm transvGL₂ : Equiv.Perm (Fin 2 → ZMod 2)) = -1 := by
    decide
  simp [signGL₂, h]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem signGL₂_cuspidal : (lineRep signGL₂).IsIrreducible ∧ IsCuspidal (lineRep signGL₂) := by
  refine ⟨lineRep_isIrreducible _, (isCuspidal_iff_twoBlocks _).mpr fun a ha0 ha2 v hv => ?_⟩
  obtain rfl : a = 1 := by omega
  have hmem : transvGL₂ ∈ unipRadical (ZMod 2) (twoBlocks 2 1) := by
    rw [mem_unipRadical]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [twoBlocks, transvGL₂]
  have h := hv transvGL₂ hmem
  rw [lineRep_apply, signGL₂_transv] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul] at hi
  simp only [Pi.zero_apply]
  linear_combination (-1 / 2 : ℂ) * hi

end Examples

end GlobalTheory.FiniteGL

namespace GlobalTheory.Published

open GlobalTheory.FiniteGL

def CuspidalExists : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n : ℕ),
    ∃ (d : ℕ) (ρ : Representation ℂ (GL (Fin (n + 1)) k) (Fin d → ℂ)), ρ.IsIrreducible ∧ IsCuspidal ρ

def CuspidalRestrictsToInduced : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (GL (Fin (n + 1)) k) V), ρ.IsIrreducible → IsCuspidal ρ →
      Nonempty ((restrictMirab n ρ).Equiv (mirabInduced n ψ₀))

def CuspidalMirabolic : Prop := CuspidalExists ∧ CuspidalRestrictsToInduced

end GlobalTheory.Published
