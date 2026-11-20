import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicAddStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicSmulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfBettiKummerRelationPadicZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaOneGammaZeroHomogeneousCocyclesFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBettiCocycleKummerRelationStatement

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ

/- English proof (translation)
Introduce `Ω _ _ _ ε X hε hj N l w _ hl2 hN hcop hw`. Establish `L1 : ∀ x : X.Khat l, (l : ℤ_[l]) • x = 0 → x = 0` using `fun x hx => GlobalTheory.T.kummerCompletion_no_prime_torsion X l x hx`. Establish `Ladd : ∀ b b' c c', BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c')` using `fun b b' c c' h h' => GlobalTheory.T.bettiKummerRelationPadic_add X N l b b' c c' h h'`. Establish `Lsmul : ∀ (r : ℤ_[l]) b c, BtZ X N l b c → BtZ X N l (r • b) (r • c)` using `fun r b c h => GlobalTheory.T.bettiKummerRelationPadic_smul X N l r b c h`. Establish `Lzero : BtZ X N l 0 0` using `btZ_zero X N l`.

Establish `L3 : ∀ b, BtZ X N l b 0 → b = 0` using `fun b h => GlobalTheory.T.eq_zero_of_bettiKummerRelationPadic_zero ε X hε hj N l (by omega) b h`. Establish `L4 : Module.Finite ℤ_[l] (Z1 N l w)` using `GlobalTheory.T.gammaOneGammaZeroHomogeneousCocycles_finite N l w (by omega)`. Establish `L5 : ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c` using `GlobalTheory.T.exists_betti_cocycle_kummer_relation ε X hε hj N l w hl2 hN hcop hw`. Set `S : Submodule ℤ_[l] (X.Fn l × Z1 N l w)` to `{ carrier := {p | BtZ X N l p.1 (p.2 : Gam N l → MvPolynomial (Fin 2) ℤ_[l])} add_mem' := fun {p q} hp hq => by simpa using Ladd _ _ _ _ hp hq zero_mem' := by simpa using Lzero smul_mem' := fun r p hp => by simpa using Lsmul r _ _ hp }`. Establish `hinj : Function.Injective ((LinearMap.snd ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype)`.

Introduce `p q hpq`. Establish `hd : (p : X.Fn l × Z1 N l w) - q ∈ S` using `S.sub_mem p.2 q.2`. Establish `h2 : ((p : X.Fn l × Z1 N l w) - q).2 = 0` using `by simpa [sub_eq_zero] using hpq`. Establish `h1 : ((p : X.Fn l × Z1 N l w) - q).1 = 0`. Apply `L3` to reduce the goal to its premises.

Use `hd` as an intermediate fact. Simplify using `only [S, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at this`. Rewrite `this` using `[h2]`. Then use the resulting hypothesis. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `sub_eq_zero.mp (Prod.ext h1 h2)`.

Use `haveI : IsNoetherian ℤ_[l] (Z1 N l w) := inferInstance`. Use `haveI hSf : Module.Finite ℤ_[l] S := Module.Finite.of_injective _ hinj`. Establish `hle : X.B N l w ≤ S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce `b hb`.

Take `⟨c, hc, hbc⟩` from `L5 b hb`. Conclude with `⟨(b, ⟨c, hc⟩), hbc, rfl⟩`. Establish `hfg : (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))).FG`. Establish `e : S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) = LinearMap.range ((LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`.

Rewrite using `[e]`. Conclude with `Module.Finite.iff_fg.mp inferInstance`. Establish `hB : (X.B N l w).FG` using `by haveI : IsNoetherian ℤ_[l] (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))) := isNoetherian_of_fg_of_noetherian _ hfg`. Use `(isNoetherian_submodule.mp this) (X.B N l w) ?_` as an intermediate fact. Conclude with `this`.

Conclude with `hle`. Use `haveI hBf : Module.Finite ℤ_[l] (X.B N l w) := Module.Finite.iff_fg.mpr hB`. Establish `Lpow : ∀ (k : ℕ) (x : X.Khat l), ((l : ℤ_[l]) ^ k) • x = 0 → x = 0`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro x hx`. Simplify using `using hx`. Consider the case `succ k ih`. Introduce `x hx`. Apply `ih` to reduce the goal to its premises.

Apply `L1` to reduce the goal to its premises. Rewrite using `[← mul_smul, ← pow_succ']`. Conclude with `hx`. Use `haveI : NoZeroSMulDivisors ℤ_[l] (X.B N l w) := by`. Use `⟨fun {r b} h => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`. Use `right`. Establish `hrw` using `PadicInt.unitCoeff_spec hr`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `u`. Establish `h' : (r • (b : X.Fn l)) u = 0`. Use `congrArg (fun y : X.B N l w => (y : X.Fn l) u) h` as an intermediate fact. Simplify using `using this`. Establish `h'' : ((l : ℤ_[l]) ^ r.valuation) • (((PadicInt.unitCoeff hr : ℤ_[l]ˣ) : ℤ_[l]) • (b : X.Fn l) u) = 0`.

Rewrite using `[smul_smul, mul_comm, ← hrw]`. Simplify using `using h'`. Use `Lpow _ _ h''` as an intermediate fact. Simplify using `using this`. Conclude with `⟨Module.free_of_finite_type_torsion_free', hBf⟩`.
-/
theorem B_free_finite : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → Module.Free ℤ_[l] (X.B N l w) ∧ Module.Finite ℤ_[l] (X.B N l w) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hcop hw
  have L1 : ∀ x : X.Khat l, (l : ℤ_[l]) • x = 0 → x = 0 := fun x hx => GlobalTheory.T.kummerCompletion_no_prime_torsion X l x hx
  have Ladd : ∀ b b' c c', BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := fun b b' c c' h h' => GlobalTheory.T.bettiKummerRelationPadic_add X N l b b' c c' h h'
  have Lsmul : ∀ (r : ℤ_[l]) b c, BtZ X N l b c → BtZ X N l (r • b) (r • c) := fun r b c h => GlobalTheory.T.bettiKummerRelationPadic_smul X N l r b c h
  have Lzero : BtZ X N l 0 0 := btZ_zero X N l
  have L3 : ∀ b, BtZ X N l b 0 → b = 0 := fun b h => GlobalTheory.T.eq_zero_of_bettiKummerRelationPadic_zero ε X hε hj N l (by omega) b h
  have L4 : Module.Finite ℤ_[l] (Z1 N l w) := GlobalTheory.T.gammaOneGammaZeroHomogeneousCocycles_finite N l w (by omega)
  have L5 : ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := GlobalTheory.T.exists_betti_cocycle_kummer_relation ε X hε hj N l w hl2 hN hcop hw

  let S : Submodule ℤ_[l] (X.Fn l × Z1 N l w) :=
    { carrier := {p | BtZ X N l p.1 (p.2 : Gam N l → MvPolynomial (Fin 2) ℤ_[l])}
      add_mem' := fun {p q} hp hq => by simpa using Ladd _ _ _ _ hp hq
      zero_mem' := by simpa using Lzero
      smul_mem' := fun r p hp => by simpa using Lsmul r _ _ hp }
  have hinj : Function.Injective ((LinearMap.snd ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype) := by
    intro p q hpq
    have hd : (p : X.Fn l × Z1 N l w) - q ∈ S := S.sub_mem p.2 q.2
    have h2 : ((p : X.Fn l × Z1 N l w) - q).2 = 0 := by simpa [sub_eq_zero] using hpq
    have h1 : ((p : X.Fn l × Z1 N l w) - q).1 = 0 := by
      apply L3
      have := hd
      simp only [S, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at this
      rwa [h2] at this
    apply Subtype.ext
    exact sub_eq_zero.mp (Prod.ext h1 h2)
  haveI : IsNoetherian ℤ_[l] (Z1 N l w) := inferInstance
  haveI hSf : Module.Finite ℤ_[l] S := Module.Finite.of_injective _ hinj
  have hle : X.B N l w ≤ S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) := by
    refine Submodule.span_le.mpr ?_
    intro b hb
    obtain ⟨c, hc, hbc⟩ := L5 b hb
    exact ⟨(b, ⟨c, hc⟩), hbc, rfl⟩
  have hfg : (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))).FG := by
    have e : S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) =
        LinearMap.range ((LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [e]
    exact Module.Finite.iff_fg.mp inferInstance
  have hB : (X.B N l w).FG := by
    haveI : IsNoetherian ℤ_[l] (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))) := isNoetherian_of_fg_of_noetherian _ hfg
    have := (isNoetherian_submodule.mp this) (X.B N l w) ?_
    · exact this
    · exact hle
  haveI hBf : Module.Finite ℤ_[l] (X.B N l w) := Module.Finite.iff_fg.mpr hB

  have Lpow : ∀ (k : ℕ) (x : X.Khat l), ((l : ℤ_[l]) ^ k) • x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      apply L1
      rw [← mul_smul, ← pow_succ']; exact hx
  haveI : NoZeroSMulDivisors ℤ_[l] (X.B N l w) := by
    refine ⟨fun {r b} h => ?_⟩
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hrw := PadicInt.unitCoeff_spec hr
    apply Subtype.ext
    funext u
    have h' : (r • (b : X.Fn l)) u = 0 := by
      have := congrArg (fun y : X.B N l w => (y : X.Fn l) u) h
      simpa using this
    have h'' : ((l : ℤ_[l]) ^ r.valuation) • (((PadicInt.unitCoeff hr : ℤ_[l]ˣ) : ℤ_[l]) • (b : X.Fn l) u) = 0 := by
      rw [smul_smul, mul_comm, ← hrw]; simpa using h'
    have := Lpow _ _ h''
    simpa using this
  exact ⟨Module.free_of_finite_type_torsion_free', hBf⟩

end GlobalTheory.KZ
