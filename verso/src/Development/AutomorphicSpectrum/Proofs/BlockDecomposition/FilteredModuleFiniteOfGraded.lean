import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LenDev

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Establish `h₁ : Module.Finite R (LinearMap.ker g)`. Rewrite using `[LinearMap.exact_iff.1 e]`. Conclude with `Module.Finite.range f`. Establish `h₂ : Module.Finite R (M₂ ⧸ LinearMap.ker g)` using `Module.Finite.equiv g.quotKerEquivRange.symm`. Conclude with `Module.Finite.of_submodule_quotient (LinearMap.ker g)`.
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
Establish `hX : Subsingleton ((CH.cx F).X n)` using `⟨fun a b => funext fun s => (h _).elim _ _⟩`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x`. Take `⟨b, hb, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 y`. Establish `e : a = b` using `hX.elim _ _`.

Substitute `e` using the available equality. Both sides reduce to the same expression.
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
Take `⟨x, hx⟩` from `x`. Take `⟨y, hy, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx`. Conclude with `⟨y, hy, rfl⟩`.
-/
theorem sqM_rep (a b : IdF A) (T : C) (x : sqM a b T) :
    ∃ (y : A.obj T) (hy : y ∈ a.S T), x = sqMk a b y hy := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨y, hy, rfl⟩

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Take `⟨x', hx, rfl⟩` from `sqM_rep a a T x`. Take `⟨y', hy, rfl⟩` from `sqM_rep a a T y`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ x' = Ideal.Quotient.mk _ y'`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hx, Ideal.Quotient.eq_zero_iff_mem.2 hy]`.
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
Introduce `x y h`. Take `⟨x', hx, rfl⟩` from `sqM_rep b c T x`. Take `⟨y', hy, rfl⟩` from `sqM_rep b c T y`. Establish `h'` using `congrArg (fun z : sqM a c T => z.1) h`. Conclude with `Subtype.ext h'`.
-/
theorem sq_inj (hba : ∀ T, b.S T ≤ a.S T) (T : C) :
    Function.Injective ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T) := by
  intro x y h
  obtain ⟨x', hx, rfl⟩ := sqM_rep b c T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep b c T y
  have h' := congrArg (fun z : sqM a c T => z.1) h
  exact Subtype.ext h'

/- English proof (translation)
Introduce `x`. Take `⟨x', hx, rfl⟩` from `sqM_rep a c T x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : (Ideal.Quotient.mk (b.S T) x') = 0` using `congrArg Subtype.val h`.

Conclude with `⟨sqMk b c x' (Ideal.Quotient.eq_zero_iff_mem.1 h'), rfl⟩`. Introduce and unpack `⟨y, hy⟩`. Take `⟨y', hy', rfl⟩` from `sqM_rep b c T y`. Establish `e : (Ideal.Quotient.mk (c.S T) y') = Ideal.Quotient.mk (c.S T) x'` using `congrArg Subtype.val hy`. Use `Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (b.S T) x' = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `Ideal.Quotient.eq.1 e` as an intermediate fact. Establish `h2` using `hcb T this`. Establish `h3` using `(b.S T).sub_mem hy' h2`.

Simplify using `using h3`.
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
Introduce `x`. Take `⟨x', hx, rfl⟩` from `sqM_rep a b T x`. Conclude with `⟨sqMk a c x' hx, rfl⟩`.
-/
theorem sq_surj (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Surjective ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a b T x
  exact ⟨sqMk a c x' hx, rfl⟩

/- English proof (translation)
Take `⟨δ, -, -, e, -⟩` from `CrystallineSemistableComparison.P.les (sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).hom (sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).hom (fun n x y h => funext fun s => sq_inj hba _ (congrFun h s)) (fun n y => ⟨fun hy => ⟨fun s => ((sq_exa …`. Use function extensionality and compare the values at `fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose_spec⟩, by`. Introduce and unpack `⟨x, rfl⟩`. Use function extensionality and compare the values at `s`. Conclude with `(sq_exact hba hcb _ _).2 ⟨_, rfl⟩⟩)`.

Use the proof step `(fun n y => ⟨fun s => (sq_surj hcb _ (y s)).choose, funext fun s => (sq_surj hcb _ (y s)).choose_spec⟩)`. Conclude with `e n`.
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
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `r h`. Take `rfl : r = s` from `by omega`.

Use `H_subsingleton _ (sq_self_subsingleton (a r)) n` as an intermediate fact. Conclude with `Module.Finite.of_finite`. Consider the case `succ d ih`. Introduce `r h`. Use `ih (r + 1) (by omega)` as an intermediate fact.

Use `hgr r (by omega)` as an intermediate fact. Conclude with `finite_mid _ _ (sq_les (hanti r (r + 1) (by omega)) (hanti (r + 1) s (by omega)) n)`.
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
Introduce `R _ _ C _ A Fil hanti s hgr j`. Establish `key` using `finite_dev (fun r : ℕ => Fil (r : ℤ)) (fun k l h T => hanti _ _ (by exact_mod_cast h) T) s j (fun r hr => by`. Establish `h` using `hgr r hr j`. Rewrite `h` using `[← Nat.cast_succ]`. Conclude with `h) s 0 (by omega)`.

Use `beta_reduce at key`. Rewrite `key` using `[Nat.cast_zero]`. Conclude with `key`.
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
