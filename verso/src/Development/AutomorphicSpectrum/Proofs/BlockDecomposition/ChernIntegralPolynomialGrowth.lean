import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetrics

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.ChernTwist

section Multi

variable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/- English proof (translation)
Consider the cases of `e with`. Consider the case `zero => exact a.elim0`. Consider the case `succ e`. Set `s : Equiv.Perm (Fin (e + 1))` to `Equiv.swap 0 a`. Set `τ : Fin e → LocPot X` to `Fin.tail (Φ ∘ s)`.

Establish `hτ : ∀ i, IsPotential A (τ i)` using `fun i => hΦ _`. Establish `key : ∀ T : LocPot X, mInt A (Function.update Φ a T) g = mInt A (Fin.cons T τ) g`. Introduce `T`. Rewrite using `[← mIntSymm A (Function.update Φ a T) s g]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[s]`. Establish `hne : s i.succ ≠ a`. Introduce `h`.

Establish `: i.succ = s a` using `by rw [← h]; simp [s]`. Simplify using `[s] at this`. Simplify using `[Function.update_of_ne hne, τ, Fin.tail]`. Establish `hc : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A ((Fin.cons T τ : Fin (e + 1) → LocPot X) i)` using `fun T hT i => Fin.cases hT hτ i`. Establish `hQt` using `isPotentialRsmul A t Q hQ`.

Rewrite using `[key, key, key, mIntAdd A P (Q.rsmul t) τ hP hQt hτ g (mIntegrableCont A _ (hc P hP) g hg) (mIntegrableCont A _ (hc _ hQt) g hg), mIntRsmul A t Q τ hQ hτ g]`.
-/
theorem mInt_update_add_rsmul (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (a : Fin e) (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q) (t : ℝ) (g : X → ℝ)
    (hg : Continuous g) :
    mInt A (Function.update Φ a (P + Q.rsmul t)) g =
      mInt A (Function.update Φ a P) g + t * mInt A (Function.update Φ a Q) g := by
  cases e with
  | zero => exact a.elim0
  | succ e =>
    let s : Equiv.Perm (Fin (e + 1)) := Equiv.swap 0 a
    let τ : Fin e → LocPot X := Fin.tail (Φ ∘ s)
    have hτ : ∀ i, IsPotential A (τ i) := fun i => hΦ _
    have key : ∀ T : LocPot X, mInt A (Function.update Φ a T) g = mInt A (Fin.cons T τ) g := by
      intro T
      rw [← mIntSymm A (Function.update Φ a T) s g]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [s]
      · have hne : s i.succ ≠ a := by
          intro h
          have : i.succ = s a := by rw [← h]; simp [s]
          simp [s] at this
        simp [Function.update_of_ne hne, τ, Fin.tail]
    have hc : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A ((Fin.cons T τ : Fin (e + 1) → LocPot X) i) :=
      fun T hT i => Fin.cases hT hτ i
    have hQt := isPotentialRsmul A t Q hQ
    rw [key, key, key, mIntAdd A P (Q.rsmul t) τ hP hQt hτ g (mIntegrableCont A _ (hc P hP) g hg)
      (mIntegrableCont A _ (hc _ hQt) g hg), mIntRsmul A t Q τ hQ hτ g]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `Φ _`. Conclude with `⟨Polynomial.C (mInt A Φ g), by simp, fun t => by simp⟩`. Consider the case `insert a S ha ih`.

Introduce `Φ hΦ`. Establish `hup : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A (Function.update Φ a T i)`. Introduce `T hT i`. Distinguish the cases in `e' : i = a`. Substitute `e'` using the available equality.

Simplify using `using hT`. Simplify `hΦ i` using `[Function.update_of_ne e']`. Take `⟨R₁, d₁, h₁⟩` from `ih _ (hup P hP)`. Take `⟨R₂, d₂, h₂⟩` from `ih _ (hup Q hQ)`. Use `⟨R₁ + Polynomial.X * R₂, ?_, fun t => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.card_insert_of_notMem ha]`. Use `Polynomial.natDegree_add_le_of_degree_le (d₁.trans (Nat.le_succ _)) ?_` and prove the remaining obligations. Use `Polynomial.natDegree_mul_le.trans ?_` and prove the remaining obligations. Use `Polynomial.natDegree_X_le (R := ℝ)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `set Ψ : Fin e → LocPot X := fun i => if i ∈ S then P + Q.rsmul t else Φ i with hΨ`. Establish `hΨp : ∀ i, IsPotential A (Ψ i)`. Introduce `i`. Simplify using `only [hΨ]`. Use `split_ifs`.

Conclude with `isPotentialAdd A _ _ hP (isPotentialRsmul A t Q hQ)`. Conclude with `hΦ i`. Establish `e₀ : (fun i => if i ∈ insert a S then P + Q.rsmul t else Φ i) = Function.update Ψ a (P + Q.rsmul t)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `e' : i = a`.

Substitute `e'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne e', hΨ, e']`. Establish `e₁ : ∀ T : LocPot X, Function.update Ψ a T = fun i => if i ∈ S then P + Q.rsmul t else Function.update Φ a T i`. Introduce `T`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `e' : i = a`. Substitute `e'` using the available equality. Simplify using `[ha]`. Simplify using `[Function.update_of_ne e', hΨ]`.

Rewrite using `[e₀, mInt_update_add_rsmul A Ψ hΨp a P Q hP hQ t g hg, e₁, e₁, h₁, h₂]`. Simplify using the standard rewrite rules.
-/
theorem exists_poly_mInt (A : FinHolAtlas e X) (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q)
    (g : X → ℝ) (hg : Continuous g) (S : Finset (Fin e)) :
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∃ R : Polynomial ℝ, R.natDegree ≤ S.card ∧
      ∀ t : ℝ, mInt A (fun i => if i ∈ S then P + Q.rsmul t else Φ i) g = R.eval t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨Polynomial.C (mInt A Φ g), by simp, fun t => by simp⟩
  | insert a S ha ih =>
    intro Φ hΦ
    have hup : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A (Function.update Φ a T i) := by
      intro T hT i
      by_cases e' : i = a
      · subst e'; simpa using hT
      · simpa [Function.update_of_ne e'] using hΦ i
    obtain ⟨R₁, d₁, h₁⟩ := ih _ (hup P hP)
    obtain ⟨R₂, d₂, h₂⟩ := ih _ (hup Q hQ)
    refine ⟨R₁ + Polynomial.X * R₂, ?_, fun t => ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      refine Polynomial.natDegree_add_le_of_degree_le (d₁.trans (Nat.le_succ _)) ?_
      refine Polynomial.natDegree_mul_le.trans ?_
      have := Polynomial.natDegree_X_le (R := ℝ)
      omega
    · set Ψ : Fin e → LocPot X := fun i => if i ∈ S then P + Q.rsmul t else Φ i with hΨ
      have hΨp : ∀ i, IsPotential A (Ψ i) := by
        intro i
        simp only [hΨ]
        split_ifs
        · exact isPotentialAdd A _ _ hP (isPotentialRsmul A t Q hQ)
        · exact hΦ i
      have e₀ : (fun i => if i ∈ insert a S then P + Q.rsmul t else Φ i) =
          Function.update Ψ a (P + Q.rsmul t) := by
        funext i
        by_cases e' : i = a
        · subst e'; simp
        · simp [Function.update_of_ne e', hΨ, e']
      have e₁ : ∀ T : LocPot X, Function.update Ψ a T =
          fun i => if i ∈ S then P + Q.rsmul t else Function.update Φ a T i := by
        intro T
        funext i
        by_cases e' : i = a
        · subst e'; simp [ha]
        · simp [Function.update_of_ne e', hΨ]
      rw [e₀, mInt_update_add_rsmul A Ψ hΨp a P Q hP hQ t g hg, e₁, e₁, h₁, h₂]
      simp

end Multi

/- English proof (translation)
Introduce `Y Δ Δ₀ L L₀ r r₀ h h₀ φ φ₀ hφ hφ₀`. Use `CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver` as an intermediate fact. Use `CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver` as an intermediate fact. Use `CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver` as an intermediate fact. Take `⟨R⟩` from `genSmooth_of_smooth Y.str Y.dim (RingHom.id ℂ)`.

Establish `hA` using `R.isAlgAtlas_finAtlas`. Establish `hP : IsPotential R.finAtlas φ.locPot` using `Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ)`. Establish `hQ : IsPotential R.finAtlas φ₀.locPot` using `Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ₀)`. Take `⟨Pol, hdeg, hev⟩` from `exists_poly_mInt R.finAtlas φ.locPot φ₀.locPot hP hQ (fun _ => 1) continuous_const Finset.univ (fun _ => φ.locPot) (fun _ => hP)`. Use `⟨Pol, by simpa using hdeg, fun m => ?_⟩` and prove the remaining obligations.

Establish `hpr` using `h.tens (GlobalTheory.CombChern.presents_zpow h₀ (m : ℤ))`. Rewrite `hpr` using `[natCast_zsmul]`. Establish `hψ : (φ.tens (φ₀.zpow (m : ℤ))).IsCInf` using `hφ.tens (hφ₀.zpow _)`. Use `⟨_, _, φ.tens (φ₀.zpow (m : ℤ)), hpr, hψ, ?_⟩` and prove the remaining obligations. Establish `hT` using `isPotentialAdd R.finAtlas _ _ hP (isPotentialRsmul R.finAtlas (m : ℝ) _ hQ)`.

Establish `hsf : SameForm R.finAtlas (φ.tens (φ₀.zpow (m : ℤ))).locPot (φ.locPot + φ₀.locPot.rsmul (m : ℝ))`. Use `Weight.sameForm_of_eq _ hA hT fun x => ?_` and prove the remaining obligations. Use `⟨(pick φ.isLB x, fun _ => pick φ₀.isLB x), mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick φ₀.isLB x)⟩, fun z => ?_⟩` and prove the remaining obligations. Establish `e` using `φ₀.zpow_φ (m : ℤ) (fun _ => pick φ₀.isLB x) z`. Express the relevant statement in the definitionally equal form `(φ.φ (pick φ.isLB x) z + (φ₀.zpow (m : ℤ)).φ (fun _ => pick φ₀.isLB x) z) / 2 = φ.φ (pick φ.isLB x) z / 2 + (m : ℝ) * (φ₀.φ (pick φ₀.isLB x) z / 2)`.

Rewrite using `[e]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[((Weight.chernInt_eq_mInt R hψ measurable_const).2 (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y _ hψ)), SameForm.mInt_eq (fun _ => hsf)]`. Simplify using `using hev (m : ℝ)`.
-/
theorem chernInt_twist_polynomial :
    ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv) (L L₀ : LB Y.X) (r : L.ι → Y.Fnˣ) (r₀ : L₀.ι → Y.Fnˣ), Presents Δ L r →
      Presents Δ₀ L₀ r₀ → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (φ₀ : Weight Y.str (RingHom.id ℂ) L₀), φ.IsCInf →
      φ₀.IsCInf → ∃ P : Polynomial ℝ, P.natDegree ≤ Y.dim ∧ ∀ m : ℕ, ∃ (L' : LB Y.X) (r' : L'.ι → Y.Fnˣ)
        (ψ : Weight Y.str (RingHom.id ℂ) L'), Presents (Δ + m • Δ₀) L' r' ∧ ψ.IsCInf ∧
          ψ.chernInt Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y Δ Δ₀ L L₀ r r₀ h h₀ φ φ₀ hφ hφ₀
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth Y.str Y.dim (RingHom.id ℂ)
  have hA := R.isAlgAtlas_finAtlas
  have hP : IsPotential R.finAtlas φ.locPot := Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ)
  have hQ : IsPotential R.finAtlas φ₀.locPot := Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ₀)
  obtain ⟨Pol, hdeg, hev⟩ := exists_poly_mInt R.finAtlas φ.locPot φ₀.locPot hP hQ (fun _ => 1) continuous_const
    Finset.univ (fun _ => φ.locPot) (fun _ => hP)
  refine ⟨Pol, by simpa using hdeg, fun m => ?_⟩
  have hpr := h.tens (GlobalTheory.CombChern.presents_zpow h₀ (m : ℤ))
  rw [natCast_zsmul] at hpr
  have hψ : (φ.tens (φ₀.zpow (m : ℤ))).IsCInf := hφ.tens (hφ₀.zpow _)
  refine ⟨_, _, φ.tens (φ₀.zpow (m : ℤ)), hpr, hψ, ?_⟩
  have hT := isPotentialAdd R.finAtlas _ _ hP (isPotentialRsmul R.finAtlas (m : ℝ) _ hQ)
  have hsf : SameForm R.finAtlas (φ.tens (φ₀.zpow (m : ℤ))).locPot (φ.locPot + φ₀.locPot.rsmul (m : ℝ)) := by
    refine Weight.sameForm_of_eq _ hA hT fun x => ?_
    refine ⟨(pick φ.isLB x, fun _ => pick φ₀.isLB x), mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick φ₀.isLB x)⟩,
      fun z => ?_⟩
    have e := φ₀.zpow_φ (m : ℤ) (fun _ => pick φ₀.isLB x) z
    change (φ.φ (pick φ.isLB x) z + (φ₀.zpow (m : ℤ)).φ (fun _ => pick φ₀.isLB x) z) / 2 =
      φ.φ (pick φ.isLB x) z / 2 + (m : ℝ) * (φ₀.φ (pick φ₀.isLB x) z / 2)
    rw [e]
    push_cast
    ring
  rw [((Weight.chernInt_eq_mInt R hψ measurable_const).2
    (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y _ hψ)), SameForm.mInt_eq (fun _ => hsf)]
  simpa using hev (m : ℝ)

end GlobalTheory.CompanionTheory.ChernTwist
