import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LenDev

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finite_mid [IsNoetherianRing R] {M₁ M₂ M₃ : Type 1} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (e : Function.Exact f g)
    [Module.Finite R M₁] [Module.Finite R M₃] : Module.Finite R M₂ := by
  have h₁ : Module.Finite R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.1 e]
    exact Module.Finite.range f
  have h₂ : Module.Finite R (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem H_subsingleton (F : C ⥤ ModuleCat.{0} R) (h : ∀ T, Subsingleton (F.obj T)) (n : ℕ) :
    Subsingleton (CH.H F n) := by
  have hX : Subsingleton ((CH.cx F).X n) := ⟨fun a b => funext fun s => (h _).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 y
  have e : a = b := hX.elim _ _
  subst e
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem sqM_rep (a b : IdF A) (T : C) (x : sqM a b T) :
    ∃ (y : A.obj T) (hy : y ∈ a.S T), x = sqMk a b y hy := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨y, hy, rfl⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem sq_self_subsingleton (a : IdF A) (T : C) : Subsingleton ((sq a a).obj T) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', hx, rfl⟩ := sqM_rep a a T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep a a T y
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ x' = Ideal.Quotient.mk _ y'
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, Ideal.Quotient.eq_zero_iff_mem.2 hy]

variable {a b c : IdF A}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem sq_inj (hba : ∀ T, b.S T ≤ a.S T) (T : C) :
    Function.Injective ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T) := by
  intro x y h
  obtain ⟨x', hx, rfl⟩ := sqM_rep b c T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep b c T y
  have h' := congrArg (fun z : sqM a c T => z.1) h
  exact Subtype.ext h'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem sq_exact (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a c T x
  constructor
  · intro h
    have h' : (Ideal.Quotient.mk (b.S T) x') = 0 := congrArg Subtype.val h
    exact ⟨sqMk b c x' (Ideal.Quotient.eq_zero_iff_mem.1 h'), rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y', hy', rfl⟩ := sqM_rep b c T y
    have e : (Ideal.Quotient.mk (c.S T) y') = Ideal.Quotient.mk (c.S T) x' := congrArg Subtype.val hy
    refine Subtype.ext ?_
    change Ideal.Quotient.mk (b.S T) x' = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := Ideal.Quotient.eq.1 e
    have h2 := hcb T this
    have h3 := (b.S T).sub_mem hy' h2
    simpa using h3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem sq_surj (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Surjective ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a b T x
  exact ⟨sqMk a c x' hx, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Apply function extensionality and compare values at an arbitrary argument. Assume the hypotheses and unpack their components. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem sq_les (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (n : ℕ) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).pull n)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).pull n) := by
  obtain ⟨δ, -, -, e, -⟩ := CrystallineSemistableComparison.P.les
    (sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).hom
    (sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).hom
    (fun n x y h => funext fun s => sq_inj hba _ (congrFun h s))
    (fun n y => ⟨fun hy => ⟨fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose,
        funext fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose_spec⟩, by
      rintro ⟨x, rfl⟩
      funext s
      exact (sq_exact hba hcb _ _).2 ⟨_, rfl⟩⟩)
    (fun n y => ⟨fun s => (sq_surj hcb _ (y s)).choose, funext fun s => (sq_surj hcb _ (y s)).choose_spec⟩)
  exact e n

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem finite_dev [IsNoetherianRing R] (a : ℕ → IdF A) (hanti : ∀ k l, k ≤ l → ∀ T, (a l).S T ≤ (a k).S T) (s n : ℕ)
    (hgr : ∀ r, r < s → Module.Finite R (CH.H (sq (a r) (a (r + 1))) n)) :
    ∀ (d r : ℕ), r + d = s → Module.Finite R (CH.H (sq (a r) (a s)) n) := by
  intro d
  induction d with
  | zero =>
    intro r h
    obtain rfl : r = s := by omega
    have := H_subsingleton _ (sq_self_subsingleton (a r)) n
    exact Module.Finite.of_finite
  | succ d ih =>
    intro r h
    have := ih (r + 1) (by omega)
    have := hgr r (by omega)
    exact finite_mid _ _ (sq_les (hanti r (r + 1) (by omega)) (hanti (r + 1) s (by omega)) n)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem finite_H_sq : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (Fil : ℤ → IdF A),
    (∀ r r' : ℤ, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T) → ∀ s : ℕ,
    (∀ r : ℕ, r < s → ∀ j, Module.Finite R (CH.H (sq (Fil r) (Fil ((r : ℤ) + 1))) j)) →
    ∀ j, Module.Finite R (CH.H (sq (Fil 0) (Fil s)) j) := by
  intro R _ _ C _ A Fil hanti s hgr j
  have key := finite_dev (fun r : ℕ => Fil (r : ℤ))
    (fun k l h T => hanti _ _ (by exact_mod_cast h) T) s j
    (fun r hr => by
      have h := hgr r hr j
      rw [← Nat.cast_succ] at h
      exact h) s 0 (by omega)
  beta_reduce at key
  rw [Nat.cast_zero] at key
  exact key

end GlobalTheory.CompanionTheory.LenDev
