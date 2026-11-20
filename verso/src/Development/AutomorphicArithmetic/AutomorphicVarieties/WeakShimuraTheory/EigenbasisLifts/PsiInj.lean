import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ A w hA hw n κ m k hm hk h i i' e`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective`. Take `⟨j, rfl⟩` from `(Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hA hw`. Take `⟨-, φ, b1, -, -, b4, b5, -⟩` from `(Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j`. Take `⟨-, _, ⟨⟨g, rfl⟩, hg⟩, h2⟩` from `(Loc.cycInertia l).2 φ.range b1.isOpen_range`.

Rewrite `h2` using `[b5]`. Establish `h3 : ¬ IsOfFinOrder (cycBar L Ω l (g : G L Ω))` using `fun hf => by`. Take `⟨N, hN, h1⟩` from `isOfFinOrder_iff_pow_eq_one.1 hf`. Use `h2 (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, Units.ext (Subtype.ext ((algebraMap ℚ_[l] (PadicAlgCl l)).injective ?_))⟩)` and prove the remaining obligations. Establish `h4` using `congrArg Units.val h1`.

Simplify using `[cycBar] at h4 ⊢`. Conclude with `h4`. Establish `a1` using `h i g ((b4 g).1 hg)`. Establish `a2` using `h i' g ((b4 g).1 hg)`. Rewrite `a2` using `[← e]`.

Establish `a3` using `a1.trans a2.symm`. Rewrite `a3` using `[mul_pow, mul_pow, mul_right_inj, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul]`. Establish `a4` using `(injective_zpow_iff_not_isOfFinOrder.2 h3) a3`. Establish `a5 : (k : ℤ) ≠ 0` using `by exact_mod_cast hk.ne'`. Conclude with `hm (neg_injective (mul_right_cancel₀ a5 a4))`.
-/
theorem UpperTheory.V.Ws.Eb.psiInj :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → ((l : ℕ) : 𝓞 L) ∈ w.asIdeal →
        ∀ {n : ℕ} (κ : Fin n → Dec (F := L) A →* (PadicAlgCl l)ˣ) (m : Fin n → ℤ) (k : ℕ), Function.Injective m → 0 < k → (∀ i (g : Dec (F := L) A), (g : G L Ω) ∈ Ine (F := L) A → (κ i g * cycBar L Ω l g ^ (-m i)) ^ k = 1) → Function.Injective κ := by
  intro l _ L Ω _ _ _ _ _ A w hA hw n κ m k hm hk h i i' e
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hA hw
  obtain ⟨-, φ, b1, -, -, b4, b5, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, _, ⟨⟨g, rfl⟩, hg⟩, h2⟩ := (Loc.cycInertia l).2 φ.range b1.isOpen_range
  rw [b5] at h2
  have h3 : ¬ IsOfFinOrder (cycBar L Ω l (g : G L Ω)) := fun hf => by
    obtain ⟨N, hN, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    refine h2 (isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, Units.ext (Subtype.ext
      ((algebraMap ℚ_[l] (PadicAlgCl l)).injective ?_))⟩)
    have h4 := congrArg Units.val h1
    simp [cycBar] at h4 ⊢
    exact h4
  have a1 := h i g ((b4 g).1 hg)
  have a2 := h i' g ((b4 g).1 hg)
  rw [← e] at a2
  have a3 := a1.trans a2.symm
  rw [mul_pow, mul_pow, mul_right_inj, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul] at a3
  have a4 := (injective_zpow_iff_not_isOfFinOrder.2 h3) a3
  have a5 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  exact hm (neg_injective (mul_right_cancel₀ a5 a4))
