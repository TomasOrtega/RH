import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace UpperTheory.RealTr

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev UK (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

section U

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U))

def coef (w v : U) : Mat n → ℂ := fun g => ⟪w, piM π g v⟫_ℂ

def KSt (S : Submodule ℂ U) : Prop := ∀ k : UK n, ∀ v ∈ S, π (uG k) v ∈ S

def kfin : Submodule ℂ U where
  carrier := {v | ∃ S : Submodule ℂ U, FiniteDimensional ℂ S ∧ KSt π S ∧ v ∈ S}
  add_mem' := by
    rintro a b ⟨S, hS, kS, ha⟩ ⟨S', hS', kS', hb⟩
    refine ⟨S ⊔ S', inferInstance, fun k v hv => ?_, Submodule.add_mem_sup ha hb⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (kS k x hx) (kS' k y hy)
  zero_mem' := ⟨⊥, inferInstance, fun k v hv => by simp_all, Submodule.zero_mem _⟩
  smul_mem' := by
    rintro c a ⟨S, hS, kS, ha⟩
    exact ⟨S, hS, kS, S.smul_mem c ha⟩

/- English proof (translation)
Introduce and unpack `k v ⟨S, hS, kS, hv⟩`. Conclude with `⟨S, hS, kS, kS k v hv⟩`.
-/
theorem kfin_stable : KSt π (kfin π) := by
  rintro k v ⟨S, hS, kS, hv⟩
  exact ⟨S, hS, kS, kS k v hv⟩

/- English proof (translation)
The claim follows from `map_mul Unitary.toUnits k k'`.
-/
theorem uG_mul (k k' : UK n) : uG (k * k') = uG k * uG k' := map_mul Unitary.toUnits k k'

/- English proof (translation)
The claim follows from `map_one Unitary.toUnits`.
-/
theorem uG_one : uG (1 : UK n) = 1 := map_one Unitary.toUnits

def sig : UK n →* (kfin π →ₗ[ℂ] kfin π) where
  toFun k := (π (uG k) : U →ₗ[ℂ] U).restrict (kfin_stable π k)
  map_one' := by ext v; simp [uG_one]
  map_mul' k k' := by ext v; simp [uG_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem sig_coe (k : UK n) (v : kfin π) : (sig π k v : U) = π (uG k) v := rfl

def Smo : Prop := ∀ v ∈ kfin π, ∀ w, ContDiffOn ℝ ∞ (coef π w v) (GLs n)

/- English proof (translation)
Introduce and unpack `v ⟨S, hS, kS, hv⟩ w`. Conclude with `(h S hS kS v hv w).1`.
-/
theorem smo_of_hasInf {χ : Inf n} (h : HasInf π χ) : Smo π := by
  rintro v ⟨S, hS, kS, hv⟩ w
  exact (h S hS kS v hv w).1

def IsDer (X : Mat n) (v u : U) : Prop := ∀ w, ∀ g ∈ GLs n, Rd X (coef π w v) g = coef π w u g

def IsD (D : Mat n →ₗ[ℝ] Module.End ℂ (kfin π)) : Prop := ∀ X (v : kfin π), IsDer π X v (D X v)

def IsoFin : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (UK n) W),
    FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] U) (_ : ∀ k w, T (ρ k w) = π (uG k) (T w)), LinearMap.range T : Submodule ℂ U)

def Ana : Prop := ∀ v ∈ kfin π, ∀ (w : U) (X : Mat n),
  AnalyticOnNhd ℝ (fun t : ℝ => coef π w v (NormedSpace.exp (t • X))) Set.univ

def IsOpK [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (B : ((E.V →L[ℂ] ℂ) →L[ℂ] U) →ₗ[ℂ] ((E.V →L[ℂ] ℂ) →L[ℂ] U)) : Prop :=
  ∀ t ξ, B t ξ = ∫ y : G n, π y (t (ξ ∘L k y.val)) ∂μ

end U

def KerReg (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  Continuous (fun y : G n => k y.val) ∧ HasCompactSupport (fun y : G n => k y.val) ∧
    ∀ y ∈ GLs n, ∀ k₁ k₂ : UK n, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂

section Alg

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def e1 (D : Mat n →ₗ[ℝ] Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) - Complex.I • D (Matrix.single a b Complex.I))

def e2 (D : Mat n →ₗ[ℝ] Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  -((1 / 2 : ℂ) • (D (Matrix.single b a 1) + Complex.I • D (Matrix.single b a Complex.I)))

def Brk (D : Mat n →ₗ[ℝ] Module.End ℂ V) : Prop := ∀ X Y, D X * D Y - D Y * D X = D (X * Y - Y * X)

def Skw (D : Mat n →ₗ[ℝ] Module.End ℂ V) : Prop := ∀ X (x y : V), ⟪D X x, y⟫_ℂ = -⟪x, D X y⟫_ℂ

/- English proof (translation)
Introduce `_ _` and use `by simp`.
-/
theorem brk_zero : Brk (0 : Mat n →ₗ[ℝ] Module.End ℂ V) := fun _ _ => by simp

/- English proof (translation)
Introduce `_ _ _` and use `by simp`.
-/
theorem skw_zero : Skw (0 : Mat n →ₗ[ℝ] Module.End ℂ V) := fun _ _ _ => by simp

end Alg

def CoreAll : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsCoreMod (infOf lam) E1 E2 σ A →
      FiniteDimensional ℂ (invA σ E) → invA σ E ≠ ⊥ →
        ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ trOn (invA σ E) (flipA E A T) = s * 2 ^ n

/- English proof (translation)
Introduce `n lam hl` and use `h n lam hl.antitone`.
-/
theorem core_of_all (h : CoreAll) : Core := fun n lam hl => h n lam hl.antitone

/- English proof (translation)
Introduce `n lam hlam _ E T hT _ _ μ _ U _ _ _ π A hu hirr hth hA2 hinf ⟨t, ht, ht0⟩`. Take `⟨V, E1, E2, σ, A', hcore, hfin, hne, htr⟩` from `hB n lam U π A hu hirr hth hA2 hinf E T hT.1`. Take `⟨s, hs, hst⟩` from `hC n lam hlam E T hT V E1 E2 σ A' hcore hfin (hne ((Submodule.ne_bot_iff _).2 ⟨t, ht, ht0⟩))`. Use `⟨s, hs, fun k val T' hk => ?_⟩` and prove the remaining obligations. Establish `h` using `hP n lam E T hT μ U π A hu hirr hth hA2 hinf k val T' hk`.

Rewrite `h` using `[htr, hst, mul_comm]`. Then use the resulting hypothesis.
-/
theorem realTr_of_all (hP : TrPass) (hB : Bridge) (hC : CoreAll) (reg : Bool) : RealTr reg := by
  intro n lam hlam _ E T hT _ _ μ _ U _ _ _ π A hu hirr hth hA2 hinf ⟨t, ht, ht0⟩
  obtain ⟨V, E1, E2, σ, A', hcore, hfin, hne, htr⟩ := hB n lam U π A hu hirr hth hA2 hinf E T hT.1
  obtain ⟨s, hs, hst⟩ := hC n lam hlam E T hT V E1 E2 σ A' hcore hfin
    (hne ((Submodule.ne_bot_iff _).2 ⟨t, ht, ht0⟩))
  refine ⟨s, hs, fun k val T' hk => ?_⟩
  have h := hP n lam E T hT μ U π A hu hirr hth hA2 hinf k val T' hk
  rwa [htr, hst, mul_comm] at h

end UpperTheory.RealTr
