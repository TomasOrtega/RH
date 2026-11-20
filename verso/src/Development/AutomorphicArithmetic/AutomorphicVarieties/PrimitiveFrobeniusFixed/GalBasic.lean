import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(Chr.clsFacts ℚ Ω N).2.2.1 g b h`. Introduce and unpack `rfl x hx`. Conclude with `Chr.cls_spec N g x hx`.
-/
private theorem lifts_cls {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (b : (ZMod N)ˣ)
    (g : G ℚ Ω) : Lifts N b g ↔ Chr.cls ℚ Ω N g = b := by
  constructor
  · intro h
    exact (Chr.clsFacts ℚ Ω N).2.2.1 g b h
  · rintro rfl x hx
    exact Chr.cls_spec N g x hx

/- English proof (translation)
Establish `hmod : ∀ x : Ω, x ^ N = 1 → ∀ k : ℕ, x ^ (k % N) = x ^ k`. Introduce `x hx k`. Use `conv_rhs => rw [← Nat.mod_add_div k N]`. Rewrite using `[pow_add, pow_mul, hx, one_pow, mul_one]`. Use extensionality with `g`.

Rewrite using `[MonoidHom.mem_ker, ← lifts_cls N 1 g]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : ∀ x : Ω, x ^ N = 1 → g x = x` using `h`. Use `show ∀ x : Ω, x ^ N = 1 → g x = x ^ ((1 : (ZMod N)ˣ) : ZMod N).val`.

Introduce `x hx`. Rewrite using `[h' x hx, Units.val_one, ZMod.val_one_eq_one_mod, hmod x hx, pow_one]`. Introduce `h`. Establish `h' : ∀ x : Ω, x ^ N = 1 → g x = x ^ ((1 : (ZMod N)ˣ) : ZMod N).val` using `h`. Use `show ∀ x : Ω, x ^ N = 1 → g x = x`.

Introduce `x hx`. Rewrite using `[h' x hx, Units.val_one, ZMod.val_one_eq_one_mod, hmod x hx, pow_one]`.
-/
private theorem fix_cls {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    fixMu ℚ Ω N = (Chr.cls ℚ Ω N).ker := by
  have hmod : ∀ x : Ω, x ^ N = 1 → ∀ k : ℕ, x ^ (k % N) = x ^ k := by
    intro x hx k
    conv_rhs => rw [← Nat.mod_add_div k N]
    rw [pow_add, pow_mul, hx, one_pow, mul_one]
  ext g
  rw [MonoidHom.mem_ker, ← lifts_cls N 1 g]
  constructor
  · intro h
    have h' : ∀ x : Ω, x ^ N = 1 → g x = x := h
    show ∀ x : Ω, x ^ N = 1 → g x = x ^ ((1 : (ZMod N)ˣ) : ZMod N).val
    intro x hx
    rw [h' x hx, Units.val_one, ZMod.val_one_eq_one_mod, hmod x hx, pow_one]
  · intro h
    have h' : ∀ x : Ω, x ^ N = 1 → g x = x ^ ((1 : (ZMod N)ˣ) : ZMod N).val := h
    show ∀ x : Ω, x ^ N = 1 → g x = x
    intro x hx
    rw [h' x hx, Units.val_one, ZMod.val_one_eq_one_mod, hmod x hx, pow_one]

/- English proof (translation)
Use `haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance`. Use `(Chr.clsOnto Ω N).1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `exact Subsingleton.elim (α := Algebra ℚ Ω) _ _`. Consider the case `(convert ‹IsAlgClosure ℚ Ω›; exact Subsingleton.elim (α := Algebra ℚ Ω) _ _)`.
-/
private theorem cls_onto {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    Function.Surjective (Chr.cls ℚ Ω N) := by
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  convert (Chr.clsOnto Ω N).1
  all_goals first
    | exact Subsingleton.elim (α := Algebra ℚ Ω) _ _
    | (convert ‹IsAlgClosure ℚ Ω›; exact Subsingleton.elim (α := Algebra ℚ Ω) _ _)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem act_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ} {x : Ω} (hx : ∀ g ∈ fixMu ℚ Ω N, g x = x)
    {g h : G ℚ Ω} (e : g⁻¹ * h ∈ fixMu ℚ Ω N) : g x = h x := by
  calc g x = g ((g⁻¹ * h) x) := by rw [hx _ e]
    _ = h x := by simp [AlgEquiv.mul_apply]

/- English proof (translation)
Introduce `Ω _ _ _ N hN`. Use `haveI : NeZero N := ⟨hN⟩`. Establish `hnorm : (fixMu ℚ Ω N).Normal`. Rewrite using `[fix_cls]`. Use `infer_instance`.

Establish `hopen : IsOpen (fixMu ℚ Ω N : Set (G ℚ Ω))`. Rewrite using `[fix_cls]`. Conclude with `(Chr.clsFacts ℚ Ω N).1`. Establish `hcomm : ∀ g h : G ℚ Ω, g * h * g⁻¹ * h⁻¹ ∈ fixMu ℚ Ω N`. Introduce `g h`.

Rewrite using `[fix_cls, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (Chr.cls ℚ Ω N g) (Chr.cls ℚ Ω N h), mul_inv_cancel_right, mul_inv_cancel]`. Establish `h4 : ∀ b : (ZMod N)ˣ, ∃ g : G ℚ Ω, Lifts N b g`. Introduce `b`. Take `⟨g, hg⟩` from `cls_onto (Ω := Ω) N b`. Conclude with `⟨g, (lifts_cls N b g).2 hg⟩`.

Establish `h5 : ∀ g : G ℚ Ω, ∃ b : (ZMod N)ˣ, Lifts N b g` using `fun g => ⟨_, (lifts_cls N _ g).2 rfl⟩`. Establish `h6 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ g h : G ℚ Ω, g (h x) = h (g x)`. Introduce `x hx g h`. Establish `e : (h * g)⁻¹ * (g * h) ∈ fixMu ℚ Ω N`. Use `hcomm g⁻¹ h⁻¹` as an intermediate fact.

Rewrite `this` using `[inv_inv, inv_inv, mul_assoc (g⁻¹ * h⁻¹), ← mul_inv_rev]`. Then use the resulting hypothesis. Use `act_eq hx e` as an intermediate fact. Simplify `this.symm` using `[AlgEquiv.mul_apply]`. Establish `h7 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ h : G ℚ Ω, ∀ g ∈ fixMu ℚ Ω N, g (h x) = h x`. Introduce `x hx h g hg`.

Establish `e : (g * h)⁻¹ * h ∈ fixMu ℚ Ω N`. Use `hnorm.conj_mem g⁻¹ (inv_mem hg) h⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv, ← mul_inv_rev]`. Then use the resulting hypothesis. Simplify `act_eq hx e` using `[AlgEquiv.mul_apply]`. Establish `h8 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ (k : ℕ) (g h : G ℚ Ω), Pows N k g → Pows N k h → g x = h x`.

Introduce `x hx k g h hg hh`. Apply `act_eq hx` to reduce the goal to its premises. Use `show ∀ ζ : Ω, ζ ^ N = 1 → (g⁻¹ * h) ζ = ζ`. Introduce `ζ hζ`. Rewrite using `[AlgEquiv.mul_apply, hh ζ hζ, ← hg ζ hζ]`.

Simplify using the standard rewrite rules. Establish `h9 : ∀ M : ℕ, M ∣ N → fixMu ℚ Ω N ≤ fixMu ℚ Ω M`. Introduce `M hM g hg`. Establish `hg' : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ` using `hg`. Use `show ∀ ζ : Ω, ζ ^ M = 1 → g ζ = ζ`.

Introduce `ζ hζ`. Take `⟨j, hj⟩` from `hM`. Conclude with `hg' ζ (by rw [hj, pow_mul, hζ, one_pow])`. Establish `h10 : ∀ (b c : (ZMod N)ˣ) (g h : G ℚ Ω), Lifts N b g → Lifts N c h → Lifts N (b * c) (g * h) ∧ Lifts N b⁻¹ g⁻¹ ∧ (b = c ↔ g⁻¹ * h ∈ fixMu ℚ Ω N)`. Introduce `b c g h hb hc`.

Rewrite `hb`, `hc` using `[lifts_cls]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[lifts_cls, map_mul, hb, hc]`. Rewrite using `[lifts_cls, map_inv, hb]`. Rewrite using `[fix_cls, MonoidHom.mem_ker, map_mul, map_inv, hb, hc, inv_mul_eq_one]`.

Conclude with `⟨hnorm, hopen, hcomm, h4, h5, h6, h7, h8, h9, h10⟩`.
-/
theorem UpperTheory.V.ML.galBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ), N ≠ 0 →
    (fixMu ℚ Ω N).Normal ∧ IsOpen (fixMu ℚ Ω N : Set (G ℚ Ω)) ∧ (∀ g h : G ℚ Ω, g * h * g⁻¹ * h⁻¹ ∈ fixMu ℚ Ω N) ∧
    (∀ b : (ZMod N)ˣ, ∃ g : G ℚ Ω, Lifts N b g) ∧ (∀ g : G ℚ Ω, ∃ b : (ZMod N)ˣ, Lifts N b g) ∧
    (∀ (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ g h : G ℚ Ω, g (h x) = h (g x)) ∧
    (∀ (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ h : G ℚ Ω, ∀ g ∈ fixMu ℚ Ω N, g (h x) = h x) ∧
    (∀ (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ (k : ℕ) (g h : G ℚ Ω), Pows N k g → Pows N k h → g x = h x) ∧
    (∀ (M : ℕ), M ∣ N → fixMu ℚ Ω N ≤ fixMu ℚ Ω M) ∧
    ∀ (b c : (ZMod N)ˣ) (g h : G ℚ Ω), Lifts N b g → Lifts N c h → Lifts N (b * c) (g * h) ∧ Lifts N b⁻¹ g⁻¹ ∧ (b = c ↔ g⁻¹ * h ∈ fixMu ℚ Ω N) := by
  intro Ω _ _ _ N hN
  haveI : NeZero N := ⟨hN⟩
  have hnorm : (fixMu ℚ Ω N).Normal := by
    rw [fix_cls]
    infer_instance
  have hopen : IsOpen (fixMu ℚ Ω N : Set (G ℚ Ω)) := by
    rw [fix_cls]
    exact (Chr.clsFacts ℚ Ω N).1
  have hcomm : ∀ g h : G ℚ Ω, g * h * g⁻¹ * h⁻¹ ∈ fixMu ℚ Ω N := by
    intro g h
    rw [fix_cls, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (Chr.cls ℚ Ω N g) (Chr.cls ℚ Ω N h), mul_inv_cancel_right, mul_inv_cancel]
  have h4 : ∀ b : (ZMod N)ˣ, ∃ g : G ℚ Ω, Lifts N b g := by
    intro b
    obtain ⟨g, hg⟩ := cls_onto (Ω := Ω) N b
    exact ⟨g, (lifts_cls N b g).2 hg⟩
  have h5 : ∀ g : G ℚ Ω, ∃ b : (ZMod N)ˣ, Lifts N b g := fun g => ⟨_, (lifts_cls N _ g).2 rfl⟩
  have h6 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ g h : G ℚ Ω, g (h x) = h (g x) := by
    intro x hx g h
    have e : (h * g)⁻¹ * (g * h) ∈ fixMu ℚ Ω N := by
      have := hcomm g⁻¹ h⁻¹
      rwa [inv_inv, inv_inv, mul_assoc (g⁻¹ * h⁻¹), ← mul_inv_rev] at this
    have := act_eq hx e
    simpa [AlgEquiv.mul_apply] using this.symm
  have h7 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ h : G ℚ Ω, ∀ g ∈ fixMu ℚ Ω N, g (h x) = h x := by
    intro x hx h g hg
    have e : (g * h)⁻¹ * h ∈ fixMu ℚ Ω N := by
      have := hnorm.conj_mem g⁻¹ (inv_mem hg) h⁻¹
      rwa [inv_inv, ← mul_inv_rev] at this
    simpa [AlgEquiv.mul_apply] using act_eq hx e
  have h8 : ∀ x : Ω, (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ (k : ℕ) (g h : G ℚ Ω), Pows N k g → Pows N k h → g x = h x := by
    intro x hx k g h hg hh
    apply act_eq hx
    show ∀ ζ : Ω, ζ ^ N = 1 → (g⁻¹ * h) ζ = ζ
    intro ζ hζ
    rw [AlgEquiv.mul_apply, hh ζ hζ, ← hg ζ hζ]
    simp
  have h9 : ∀ M : ℕ, M ∣ N → fixMu ℚ Ω N ≤ fixMu ℚ Ω M := by
    intro M hM g hg
    have hg' : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ := hg
    show ∀ ζ : Ω, ζ ^ M = 1 → g ζ = ζ
    intro ζ hζ
    obtain ⟨j, hj⟩ := hM
    exact hg' ζ (by rw [hj, pow_mul, hζ, one_pow])
  have h10 : ∀ (b c : (ZMod N)ˣ) (g h : G ℚ Ω), Lifts N b g → Lifts N c h →
      Lifts N (b * c) (g * h) ∧ Lifts N b⁻¹ g⁻¹ ∧ (b = c ↔ g⁻¹ * h ∈ fixMu ℚ Ω N) := by
    intro b c g h hb hc
    rw [lifts_cls] at hb hc
    refine ⟨?_, ?_, ?_⟩
    · rw [lifts_cls, map_mul, hb, hc]
    · rw [lifts_cls, map_inv, hb]
    · rw [fix_cls, MonoidHom.mem_ker, map_mul, map_inv, hb, hc, inv_mul_eq_one]
  exact ⟨hnorm, hopen, hcomm, h4, h5, h6, h7, h8, h9, h10⟩
