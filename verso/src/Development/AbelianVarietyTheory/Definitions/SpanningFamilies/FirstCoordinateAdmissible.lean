import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.SW

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsType (Ψ : Finset (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ

def ccT {α β : Type} (A : Matrix α β E) : Matrix β α E := (A.map cc)ᵀ

def imH {N : ℕ} (Z : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := (2 * I)⁻¹ • (Z - Zᴴ)

abbrev CM (Ψ : Finset (E →+* ℂ)) (a b : ℕ) : Type := Ψ → Matrix (Fin a) (Fin b) ℂ

def Hn (Ψ : Finset (E →+* ℂ)) (N : ℕ) : Set (CM Ψ N N) := {Z | ∀ τ, (imH (Z τ)).PosDef}

def HnGe (Ψ : Finset (E →+* ℂ)) (N : ℕ) (δ : ℝ) : Set (CM Ψ N N) :=
  {Z | ∀ τ, (imH (Z τ) - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef}

def detIm {Ψ : Finset (E →+* ℂ)} {N : ℕ} (Z : CM Ψ N N) : ℝ := ∏ τ, (imH (Z τ)).det.re

variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

def expo (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  ∑ τ : Ψ, ∑ k, ((fun a => τ.1 (x k a)) ⬝ᵥ Z τ *ᵥ (fun a => conj (τ.1 (x k a))) +
    (fun a => τ.1 (x k a)) ⬝ᵥ z τ k + z' τ k ⬝ᵥ fun a => conj (τ.1 (x k a)))

def thH (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  ∑' x : Matrix (Fin n) (Fin N) E, φ x * cexp (2 * Real.pi * I * expo Ψ x Z z z')

abbrev M2 (E : Type) (N : ℕ) : Type := Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) E

def UU (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) : Set (M2 E N) :=
  {γ | ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E}

def hDen (γ : M2 E N) (Z : CM Ψ N N) : CM Ψ N N := fun τ =>
  γ.toBlocks₂₁.map τ.1 * Z τ + γ.toBlocks₂₂.map τ.1

def hDen' (γ : M2 E N) (Z : CM Ψ N N) : CM Ψ N N := fun τ =>
  Z τ * (γ.toBlocks₂₁.map τ.1)ᴴ + (γ.toBlocks₂₂.map τ.1)ᴴ

def hAct (γ : M2 E N) (Z : CM Ψ N N) : CM Ψ N N := fun τ =>
  (γ.toBlocks₁₁.map τ.1 * Z τ + γ.toBlocks₁₂.map τ.1) * (hDen Ψ γ Z τ)⁻¹

def hFac (γ : M2 E N) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  ∏ τ : Ψ, (hDen Ψ γ Z τ).det ^ n * cexp (2 * Real.pi * I *
    ∑ k, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k)

def TransH (γ : M2 E N) (φ ψ : Matrix (Fin n) (Fin N) E → ℂ) : Prop :=
  ∀ Z ∈ Hn Ψ N, ∀ z z' : CM Ψ n N,
    thH Ψ ψ (hAct Ψ γ Z) (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
      (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = hFac Ψ γ Z z z' * thH Ψ φ Z z z'

open Classical in

def weil (γ : M2 E N) (φ : Matrix (Fin n) (Fin N) E → ℂ) : Matrix (Fin n) (Fin N) E → ℂ :=
  if h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ then h.choose else 0

def botSpan (γ : M2 E N) : Submodule E (Fin N ⊕ Fin N → E) :=
  Submodule.span E (Set.range fun a : Fin N => γ (Sum.inr a))

def Lag (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) : Type :=
  {U : Submodule E (Fin N ⊕ Fin N → E) // ∃ γ ∈ UU E N, botSpan γ = U}

def eisTerm (γ : M2 E N) (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  weil Ψ γ φ 0 * (hFac Ψ γ Z z z')⁻¹

def eis (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  ∑' U : Lag E N, eisTerm Ψ U.2.choose φ Z z z'

def heisH (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Matrix (Fin n) (Fin N) E → ℂ := fun x =>
  φ (x - d) * cexp (Real.pi * I *
    ((Algebra.trace ℚ E (∑ k, ∑ a, b k a * (2 * cc (x k a) - cc (d k a))) : ℚ) : ℂ))

def chiH (β : Matrix (Fin N) (Fin N) E) (x : Matrix (Fin n) (Fin N) E) : ℂ :=
  cexp (2 * Real.pi * I * ∑ τ : Ψ, τ.1 (x * β * ccT x).trace)

def Den {α β : Type} (c : ℕ) (γ : Matrix α β E) : Prop := IntM ((c : E) • γ)

abbrev QI (E : Type) [Field E] [NumberField E] (N : ℕ) : Type := Fin N × Fin (Module.finrank ℚ E)

def ofQ (m : Matrix (Fin n) (QI E N) ℚ) : Matrix (Fin n) (Fin N) E :=
  Matrix.of fun k a => ∑ j, m k (a, j) • Module.finBasis ℚ E j

def tauOf (Z : CM Ψ N N) : Matrix (QI E N) (QI E N) ℂ := Matrix.of fun p q => ∑ τ : Ψ,
  (τ.1 (Module.finBasis ℚ E p.2) * Z τ p.1 q.1 * conj (τ.1 (Module.finBasis ℚ E q.2)) +
    τ.1 (Module.finBasis ℚ E q.2) * Z τ q.1 p.1 * conj (τ.1 (Module.finBasis ℚ E p.2)))

def zetaOf (z z' : CM Ψ n N) : Fin n → QI E N → ℂ := fun k p => ∑ τ : Ψ,
  (τ.1 (Module.finBasis ℚ E p.2) * z τ k p.1 + z' τ k p.1 * conj (τ.1 (Module.finBasis ℚ E p.2)))

abbrev Lt (E : Type) [Field E] [NumberField E] (m : ℕ) : Type := Submodule (𝓞 E) (Fin m → E)

def stdL (E : Type) [Field E] [NumberField E] (m : ℕ) : Lt E m :=
  Submodule.span (𝓞 E) (Set.range fun a : Fin m => (Pi.single a 1 : Fin m → E))

def Agree {m : ℕ} (M : ℕ) (Λ Λ' : Lt E m) : Prop :=
  ∃ s : ℕ, 0 < s ∧ s.Coprime M ∧ (∀ v ∈ Λ, (s : E) • v ∈ Λ') ∧ ∀ v ∈ Λ', (s : E) • v ∈ Λ

def Vset (E : Type) [Field E] [NumberField E] [IsCMField E] (n M : ℕ) : Set (Lt E n) :=
  {Λ | Λ.FG ∧ (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧ Agree M Λ (stdL E n)}

def DH (E : Type) [Field E] [NumberField E] [IsCMField E] (n M : ℕ) :
    Set (Matrix (Fin n) (Fin n) E) :=
  {h | ccT h * h = 1 ∧ ∃ s : ℕ, 0 < s ∧ s.Coprime M ∧
    ∃ y : Matrix (Fin n) (Fin n) E, IntM y ∧ (s : E) • (h - 1) = (M : E) • y}

def Moves {m : ℕ} (h : Matrix (Fin m) (Fin m) E) (Λ Λ' : Lt E m) : Prop := ∀ v, v ∈ Λ ↔ h *ᵥ v ∈ Λ'

def Cls (E : Type) [Field E] [NumberField E] [IsCMField E] (n M : ℕ) : Type :=
  Quot fun Λ Λ' : Vset E n M => ∃ h ∈ DH E n M, Moves h Λ.1 Λ'.1

def wt (M : ℕ) (Λ : Lt E n) : ℝ := (({h ∈ DH E n M | Moves h Λ Λ}.ncard : ℕ) : ℝ)⁻¹

def IsClassFn (M : ℕ) (f : Lt E n → ℂ) : Prop :=
  ∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ

def classSum (M : ℕ) (f : Lt E n → ℂ) : ℂ :=
  ∑ᶠ c : Cls E n M, (wt M (Quot.out c).1 : ℂ) * f (Quot.out c).1

def ColsIn (Λ : Lt E n) (x : Matrix (Fin n) (Fin N) E) : Prop := ∀ a, xᵀ a ∈ Λ

abbrev Fam (E : Type) [Field E] [NumberField E] (n N : ℕ) : Type :=
  Lt E n → Matrix (Fin n) (Fin N) E → ℂ

structure admitted (M R : ℕ) (φ : Fam E n N) : Prop where
  pos : 0 < M ∧ 0 < R
  equiv : ∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' →
    ∀ x, φ Λ' (h * x) = φ Λ x
  supp : ∀ Λ ∈ Vset E n M, ∀ x, φ Λ x ≠ 0 → ColsIn Λ ((R : E) • x)
  per : ∀ Λ ∈ Vset E n M, ∀ x y, ColsIn Λ y → φ Λ (x + (R : E) • y) = φ Λ x
  loc : ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Agree (R * M) Λ Λ' → ∀ x,
    ColsIn Λ ((R : E) • x) → ColsIn Λ' ((R : E) • x) → φ Λ x = φ Λ' x

def swDiff (M : ℕ) (φ : Fam E n N) (Z : CM Ψ N N) : ℂ :=
  classSum M fun Λ => thH Ψ (φ Λ) Z 0 0 - eis Ψ (φ Λ) Z 0 0

def swd (M : ℕ) (φ : Fam E n N) (Z : CM Ψ N N) (z z' : CM Ψ n N) : ℂ :=
  classSum M fun Λ => thH Ψ (φ Λ) Z z z' - eis Ψ (φ Λ) Z z z'

open Classical in

def twist (R : ℕ) (𝔛 : Lt E N) (φ : Fam E n N) : Fam E n N := fun Λ x =>
  if h : (∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) ∧
      ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ stdL E N, (s : E) • v ∈ 𝔛 then
    φ Λ ((h.2.choose : E) • x) else 0

def gidx (𝔛 : Lt E N) : ℝ :=
  ((stdL E N).toAddSubgroup.relIndex 𝔛.toAddSubgroup : ℝ) /
    (𝔛.toAddSubgroup.relIndex (stdL E N).toAddSubgroup : ℝ)

def Nb (M : ℕ) (P : Ideal (𝓞 E)) (Λ : Lt E n) : Set (Lt E n) :=
  {Λ' | Λ' ∈ Vset E n M ∧ P • Λ ≤ Λ' ∧
    Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup = Ideal.absNorm P}

def conjI (P : Ideal (𝓞 E)) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ b ∈ P, ((a : 𝓞 E) : E) = cc ((b : 𝓞 E) : E)}

def GoodPrime (m q : ℕ) (P : Ideal (𝓞 E)) : Prop :=
  q.Prime ∧ q.Coprime m ∧ Ideal.absNorm P = q ∧ IsCoprime P (conjI P) ∧
    ¬ (q : ℤ) ∣ 2 * NumberField.discr E

def dropZ (Z : CM Ψ (N + 1) (N + 1)) : CM Ψ N N := fun τ => (Z τ).submatrix Fin.succ Fin.succ

def dropF (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ) : Matrix (Fin n) (Fin N) E → ℂ := fun x =>
  φ (Matrix.of fun k => Fin.cons 0 (x k))

def pushZ (Z : CM Ψ N N) (v : Fin N → E) (t : ℝ) : CM Ψ N N := fun τ =>
  Z τ + (I * t) • vecMulVec (fun a => τ.1 (v a)) fun a => conj (τ.1 (v a))

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨one_pos, one_pos⟩, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ h => (h rfl).elim, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩`.
-/
theorem first_coordinate_admissible : admitted 1 1 (0 : Fam E n N) :=
  ⟨⟨one_pos, one_pos⟩, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ h => (h rfl).elim,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩

namespace Base

/- English proof (translation)
The claim follows from `X.cmType`.
-/
theorem isType_data {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : IsType X.Ψ := X.cmType

/- English proof (translation)
Simplify using `[cc, IsCMField.complexEmbedding_complexConj]`.
-/
theorem map_cc (τ : E →+* ℂ) (t : E) : τ (cc t) = conj (τ t) := by
  simp [cc, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, map_cc, Matrix.conjTranspose_apply]`.
-/
theorem ccT_map {α β : Type} (τ : E →+* ℂ) (A : Matrix α β E) : (ccT A).map τ = (A.map τ)ᴴ := by
  ext i j; simp [ccT, map_cc, Matrix.conjTranspose_apply]

/- English proof (translation)
The claim follows from `hx.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)`.
-/
theorem isIntegral_cc {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)

/- English proof (translation)
Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]`.
-/
theorem ccT_one {α : Type} [DecidableEq α] : ccT (1 : Matrix α α E) = 1 := by
  ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, cc]`.
-/
theorem ccT_ccT {α β : Type} (A : Matrix α β E) : ccT (ccT A) = A := by
  ext i j; simp [ccT, cc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, cc, Matrix.mul_apply, mul_comm]`.
-/
theorem ccT_mul {α β γ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) :
    ccT (A * B) = ccT B * ccT A := by
  ext i j; simp [ccT, cc, Matrix.mul_apply, mul_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [ccT_one, one_mul], 1, one_pos, Nat.coprime_one_left M, 0, fun _ _ => isIntegral_zero, by simp⟩`.
-/
theorem one_mem_DH (M : ℕ) : (1 : Matrix (Fin n) (Fin n) E) ∈ DH E n M :=
  ⟨by rw [ccT_one, one_mul], 1, one_pos, Nat.coprime_one_left M, 0, fun _ _ => isIntegral_zero,
    by simp⟩

/- English proof (translation)
Take `⟨hu, s, hs, hsM, y, hy, e⟩` from `hh`. Use `⟨by rw [ccT_ccT]; exact mul_eq_one_comm.1 hu, s, hs, hsM, ccT y, fun i j => isIntegral_cc (hy j i), ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `congrArg cc (congrFun (congrFun e j) i)` as an intermediate fact. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify `this` using `[ccT, cc]`. Simplify `this` using `[ccT, cc, Matrix.one_apply, hij, Ne.symm hij]`.
-/
theorem ccT_mem_DH {M : ℕ} {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n M) :
    ccT h ∈ DH E n M := by
  obtain ⟨hu, s, hs, hsM, y, hy, e⟩ := hh
  refine ⟨by rw [ccT_ccT]; exact mul_eq_one_comm.1 hu, s, hs, hsM, ccT y,
    fun i j => isIntegral_cc (hy j i), ?_⟩
  ext i j
  have := congrArg cc (congrFun (congrFun e j) i)
  by_cases hij : i = j
  · subst hij; simpa [ccT, cc] using this
  · simpa [ccT, cc, Matrix.one_apply, hij, Ne.symm hij] using this

/- English proof (translation)
Take `⟨hu, s, hs, hsM, y, hy, e⟩` from `hh`. Take `⟨gu, t, ht, htM, w, hw, f⟩` from `hg`. Use `⟨?_, s * t, Nat.mul_pos hs ht, Nat.Coprime.mul_left hsM htM, (M : E) • (y * w) + (t : E) • y + (s : E) • w, fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ccT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ccT h), hu, one_mul, gu]`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]`.

Establish `c : ∀ k : ℕ, IsIntegral ℤ (k : E)` using `fun k => by`. Simplify using `using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))`. Conclude with `(((c M).mul (IsIntegral.sum _ fun k _ => (hy i k).mul (hw k j))).add ((c t).mul (hy i j))).add ((c s).mul (hw i j))`. Establish `: ((s * t : ℕ) : E) • (h * g - 1) = ((s : E) • (h - 1)) * ((t : E) • (g - 1)) + (t : E) • ((s : E) • (h - 1)) + (s : E) • ((t : E) • (g - 1))`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul, mul_comm (t : E) s, ← smul_add]`.

Use `congr 1`. Use `noncomm_ring`. Rewrite using `[this, e, f]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, mul_comm (M : E)]`.
-/
theorem mul_mem_DH {M : ℕ} {h g : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n M)
    (hg : g ∈ DH E n M) : h * g ∈ DH E n M := by
  obtain ⟨hu, s, hs, hsM, y, hy, e⟩ := hh
  obtain ⟨gu, t, ht, htM, w, hw, f⟩ := hg
  refine ⟨?_, s * t, Nat.mul_pos hs ht, Nat.Coprime.mul_left hsM htM,
    (M : E) • (y * w) + (t : E) • y + (s : E) • w, fun i j => ?_, ?_⟩
  · rw [ccT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ccT h), hu, one_mul, gu]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    have c : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
      simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
    exact (((c M).mul (IsIntegral.sum _ fun k _ => (hy i k).mul (hw k j))).add
      ((c t).mul (hy i j))).add ((c s).mul (hw i j))
  · have : ((s * t : ℕ) : E) • (h * g - 1) = ((s : E) • (h - 1)) * ((t : E) • (g - 1)) +
        (t : E) • ((s : E) • (h - 1)) + (s : E) • ((t : E) • (g - 1)) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul, mul_comm (t : E) s,
        ← smul_add]
      congr 1
      noncomm_ring
    rw [this, e, f]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, mul_comm (M : E)]

omit [IsCMField E] in

/- English proof (translation)
Introduce `v` and use `by rw [Matrix.one_mulVec]`.
-/
theorem moves_one (Λ : Lt E n) : Moves 1 Λ Λ := fun v => by rw [Matrix.one_mulVec]

omit [IsCMField E] in

/- English proof (translation)
Introduce `v` and use `by rw [h1, h2, Matrix.mulVec_mulVec]`.
-/
theorem moves_mul {h g : Matrix (Fin n) (Fin n) E} {Λ Λ' Λ'' : Lt E n} (h1 : Moves g Λ Λ')
    (h2 : Moves h Λ' Λ'') : Moves (h * g) Λ Λ'' := fun v => by
  rw [h1, h2, Matrix.mulVec_mulVec]

/- English proof (translation)
Introduce `v` and use `by rw [h1, Matrix.mulVec_mulVec, mul_eq_one_comm.1 hu, Matrix.one_mulVec]`.
-/
theorem moves_ccT {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) {Λ Λ' : Lt E n}
    (h1 : Moves h Λ Λ') : Moves (ccT h) Λ' Λ := fun v => by
  rw [h1, Matrix.mulVec_mulVec, mul_eq_one_comm.1 hu, Matrix.one_mulVec]

/- English proof (translation)
Establish `: Equivalence fun Λ Λ' : Vset E n M => ∃ h ∈ DH E n M, Moves h Λ.1 Λ'.1` using `⟨fun Λ => ⟨1, one_mem_DH M, moves_one _⟩, fun ⟨h, hh, m⟩ => ⟨ccT h, ccT_mem_DH hh, moves_ccT hh.1 m⟩, fun ⟨g, hg, m⟩ ⟨h, hh, m'⟩ => ⟨h * g, mul_mem_DH hh hg, moves_mul m m'⟩⟩`. Conclude with `Quot.eq.trans this.eqvGen_iff`.
-/
theorem cls_eq_iff {M : ℕ} (Λ Λ' : Vset E n M) :
    (Quot.mk _ Λ : Cls E n M) = Quot.mk _ Λ' ↔ ∃ h ∈ DH E n M, Moves h Λ.1 Λ'.1 := by
  have : Equivalence fun Λ Λ' : Vset E n M => ∃ h ∈ DH E n M, Moves h Λ.1 Λ'.1 :=
    ⟨fun Λ => ⟨1, one_mem_DH M, moves_one _⟩,
      fun ⟨h, hh, m⟩ => ⟨ccT h, ccT_mem_DH hh, moves_ccT hh.1 m⟩,
      fun ⟨g, hg, m⟩ ⟨h, hh, m'⟩ => ⟨h * g, mul_mem_DH hh hg, moves_mul m m'⟩⟩
  exact Quot.eq.trans this.eqvGen_iff

/- English proof (translation)
Establish `hu : ccT h * h = 1` using `hh.1`. Establish `hu' : h * ccT h = 1` using `mul_eq_one_comm.1 hu`. Unfold `wt`. Use `congr 2`. Use `Set.ncard_congr (fun g _ => ccT h * g * h) (fun g hg => ?_) (fun g g' _ _ e => ?_) (fun g hg => ⟨h * g * ccT h, ?_, ?_⟩)` and prove the remaining obligations.

Conclude with `⟨mul_mem_DH (mul_mem_DH (ccT_mem_DH hh) hg.1) hh, moves_mul m (moves_mul hg.2 (moves_ccT hu m))⟩`. Establish `k : ∀ g : Matrix (Fin n) (Fin n) E, h * (ccT h * g * h) * ccT h = g` using `fun g => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hu', one_mul, Matrix.mul_assoc, hu', mul_one]`. Rewrite using `[← k g, ← k g']`. Conclude with `congrArg (fun a => h * a * ccT h) e`.

Conclude with `⟨mul_mem_DH (mul_mem_DH hh hg.1) (ccT_mem_DH hh), moves_mul (moves_ccT hu m) (moves_mul hg.2 m)⟩`. Express the relevant statement in the definitionally equal form `ccT h * (h * g * ccT h) * h = g`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, one_mul, Matrix.mul_assoc, hu, mul_one]`.
-/
theorem wt_moves {M : ℕ} {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n M) {Λ Λ' : Lt E n}
    (m : Moves h Λ Λ') : wt M Λ' = wt M Λ := by
  have hu : ccT h * h = 1 := hh.1
  have hu' : h * ccT h = 1 := mul_eq_one_comm.1 hu
  unfold wt
  congr 2
  refine Set.ncard_congr (fun g _ => ccT h * g * h) (fun g hg => ?_) (fun g g' _ _ e => ?_)
    (fun g hg => ⟨h * g * ccT h, ?_, ?_⟩)
  · exact ⟨mul_mem_DH (mul_mem_DH (ccT_mem_DH hh) hg.1) hh,
      moves_mul m (moves_mul hg.2 (moves_ccT hu m))⟩
  · have k : ∀ g : Matrix (Fin n) (Fin n) E, h * (ccT h * g * h) * ccT h = g := fun g => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu', one_mul, Matrix.mul_assoc, hu', mul_one]
    rw [← k g, ← k g']
    exact congrArg (fun a => h * a * ccT h) e
  · exact ⟨mul_mem_DH (mul_mem_DH hh hg.1) (ccT_mem_DH hh),
      moves_mul (moves_ccT hu m) (moves_mul hg.2 m)⟩
  · change ccT h * (h * g * ccT h) * h = g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, one_mul, Matrix.mul_assoc, hu, mul_one]

/- English proof (translation)
Use `finsum_congr fun c => ?_` and prove the remaining obligations. Take `⟨h, hh, m⟩` from `(cls_eq_iff (s c) (Quot.out c)).1 ((hs c).trans (Quot.out_eq c).symm)`. Rewrite using `[wt_moves hh m, hf h hh _ (s c).2 _ (Quot.out c).2 m]`.
-/
theorem classSum_eq {M : ℕ} {f : Lt E n → ℂ} (hf : IsClassFn M f) (s : Cls E n M → Vset E n M)
    (hs : ∀ c, Quot.mk _ (s c) = c) :
    classSum M f = ∑ᶠ c : Cls E n M, (wt M (s c).1 : ℂ) * f (s c).1 := by
  refine finsum_congr fun c => ?_
  obtain ⟨h, hh, m⟩ := (cls_eq_iff (s c) (Quot.out c)).1 ((hs c).trans (Quot.out_eq c).symm)
  rw [wt_moves hh m, hf h hh _ (s c).2 _ (Quot.out c).2 m]

/- English proof (translation)
The claim follows from `finsum_congr fun c => by rw [h _ (Quot.out c).2]`.
-/
theorem classSum_congr {M : ℕ} {f g : Lt E n → ℂ} (h : ∀ Λ ∈ Vset E n M, f Λ = g Λ) :
    classSum M f = classSum M g :=
  finsum_congr fun c => by rw [h _ (Quot.out c).2]

omit [IsCMField E] in

/- English proof (translation)
Unfold `expo`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.trace, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc]`.

Both sides reduce to the same expression.
-/
theorem expo_eq_trace (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    expo Ψ x Z z z' = ∑ τ : Ψ, ((x.map τ.1 * Z τ * (x.map τ.1)ᴴ).trace +
      (x.map τ.1 * (z τ)ᵀ).trace + (z' τ * (x.map τ.1)ᴴ).trace) := by
  unfold expo
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.trace, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_assoc]
  rfl

/- English proof (translation)
Rewrite using `[expo_eq_trace, expo_eq_trace]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `e : (h.map τ.1)ᴴ * h.map τ.1 = 1`. Rewrite using `[← ccT_map, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[Matrix.map_mul, Matrix.conjTranspose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`.

Generalize the expression as in `h.map τ.1 = H at e ⊢`. Generalize the expression as in `x.map τ.1 = X`. Use `congr 1`. Use `congr 1`. Rewrite using `[← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]`.
-/
theorem expo_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    expo Ψ (h * x) Z z z' =
      expo Ψ x Z (fun τ => (h.map τ.1)ᵀ * z τ) (fun τ => (h.map τ.1)ᴴ * z' τ) := by
  rw [expo_eq_trace, expo_eq_trace]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : (h.map τ.1)ᴴ * h.map τ.1 = 1 := by
    rw [← ccT_map, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_mul, Matrix.conjTranspose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  generalize h.map τ.1 = H at e ⊢
  generalize x.map τ.1 = X
  congr 1
  · congr 1
    · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, e, Matrix.one_mul]
    · rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swd_zero (M : ℕ) (φ : Fam E n N) (Z : CM Ψ N N) : swd Ψ M φ Z 0 0 = swDiff Ψ M φ Z := rfl

omit [IsCMField E] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`.

Introduce `a`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[Pi.single_apply, h]`.

Consider the case `zero => intro a`. Conclude with `isIntegral_zero`. Consider the case `add x y _ _ hx hy => intro a`. Conclude with `(hx a).add (hy a)`. Consider the case `smul c x _ hx`.

Introduce `a`. Establish `: (c • x) a = (c : E) * x a` using `rfl`. Rewrite using `[this]`. Conclude with `c.isIntegral_coe.mul (hx a)`. Introduce `hx`.

Establish `: x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin m → E)`. Use extensionality with `b`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single b]`. Express the relevant statement in the definitionally equal form `x b = x b * (Pi.single b (1 : E) : Fin m → E) b`. Simplify using the standard rewrite rules.

Introduce `a _ h`. Express the relevant statement in the definitionally equal form `x a * (Pi.single a (1 : E) : Fin m → E) b = 0`. Simplify using `[Ne.symm h]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem mem_stdL {m : ℕ} (x : Fin m → E) : x ∈ stdL E m ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      by_cases h : a = b
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx =>
      intro a
      have : (c • x) a = (c : E) * x a := rfl
      rw [this]; exact c.isIntegral_coe.mul (hx a)
  · intro hx
    have : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin m → E) := by
      ext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · change x b = x b * (Pi.single b (1 : E) : Fin m → E) b
        simp
      · intro a _ h
        change x a * (Pi.single a (1 : E) : Fin m → E) b = 0
        simp [Ne.symm h]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Unfold `herm`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rw [Finset.sum_eq_single a] <;> simp +contextual [Matrix.one_apply, eq_comm]`.
-/
theorem herm_one {m : ℕ} (x y : Fin m → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  unfold herm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a] <;> simp +contextual [Matrix.one_apply, eq_comm]

/- English proof (translation)
Use `⟨Submodule.fg_span (Set.finite_range _), fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩, 1, one_pos, Nat.coprime_one_left M, by simp, by simp⟩` and prove the remaining obligations. Rewrite using `[herm_one]`. Rewrite `hx`, `hy` using `[mem_stdL]`. Conclude with `IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc (hy a))`. Rewrite using `[mem_stdL]`.

Introduce `a`. Use `h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)` as an intermediate fact. Rewrite `this` using `[herm_one, Finset.sum_eq_single a]`. Simplify `this` using `[cc]`. Introduce `b _ hb`.

Simplify using `[hb, cc]`. Simplify using the standard rewrite rules.
-/
theorem stdL_mem_Vset (n M : ℕ) : stdL E n ∈ Vset E n M := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩,
    1, one_pos, Nat.coprime_one_left M, by simp, by simp⟩
  · rw [herm_one]
    rw [mem_stdL] at hx hy
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc (hy a))
  · rw [mem_stdL]
    intro a
    have := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [herm_one, Finset.sum_eq_single a] at this
    · simpa [cc] using this
    · intro b _ hb; simp [hb, cc]
    · simp

omit [IsCMField E] in

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `Λ.toAddSubgroup.nsmul_mem hv s`.
-/
theorem nat_smul_mem {m : ℕ} (Λ : Lt E m) (s : ℕ) {v : Fin m → E} (hv : v ∈ Λ) :
    (s : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact Λ.toAddSubgroup.nsmul_mem hv s

omit [IsCMField E] in

/- English proof (translation)
Take `⟨a, b, hab⟩ : IsCoprime (s : ℤ) (R : ℤ)` from `Nat.isCoprime_iff_coprime.2 h`. Establish `e : v = a • ((s : E) • v) + b • ((R : E) • v)`. Rewrite using `[← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]`. Establish `: (a : E) * s + b * R = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → E) hab`. Rewrite using `[this, one_smul]`.

Rewrite using `[e]`. Conclude with `Λ.add_mem (Λ.toAddSubgroup.zsmul_mem h1 a) (Λ.toAddSubgroup.zsmul_mem h2 b)`.
-/
theorem mem_of_coprime {m : ℕ} (Λ : Lt E m) {s R : ℕ} (h : s.Coprime R) {v : Fin m → E}
    (h1 : (s : E) • v ∈ Λ) (h2 : (R : E) • v ∈ Λ) : v ∈ Λ := by
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) (R : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have e : v = a • ((s : E) • v) + b • ((R : E) • v) := by
    rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]
    have : (a : E) * s + b * R = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → E) hab
    rw [this, one_smul]
  rw [e]
  exact Λ.add_mem (Λ.toAddSubgroup.zsmul_mem h1 a) (Λ.toAddSubgroup.zsmul_mem h2 b)

open Classical in

def indF (E : Type) [Field E] [NumberField E] (n N : ℕ) : Fam E n N := fun Λ x =>
  if ColsIn Λ x then 1 else 0

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `τ`. Establish `: imH (I • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1`. Unfold `imH`. Rewrite using `[conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul]`. Establish `: (2 * I)⁻¹ * (I - star I) = 1`.

Establish `: star I = -I` using `conj_I`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, one_smul]`.

Simplify `Matrix.PosDef.one` using `[this]`.
-/
theorem I_mem_Hn : (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) : CM Ψ N N) ∈ Hn Ψ N := by
  intro τ
  have : imH (I • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 := by
    unfold imH
    rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul]
    have : (2 * I)⁻¹ * (I - star I) = 1 := by
      have : star I = -I := conj_I
      rw [this]; field_simp; ring
    rw [this, one_smul]
  simpa [this] using Matrix.PosDef.one

/- English proof (translation)
Establish `: (Matrix.J (Fin N) E).map cc = Matrix.J (Fin N) E`. Apply the tactic sequence `ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [Matrix.J, cc, h]`. Rewrite using `[ccT, this, Matrix.J_transpose]`.
-/
theorem ccT_J : ccT (Matrix.J (Fin N) E) = -Matrix.J (Fin N) E := by
  have : (Matrix.J (Fin N) E).map cc = Matrix.J (Fin N) E := by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [Matrix.J, cc, h]
  rw [ccT, this, Matrix.J_transpose]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `ccT _ * _ * _ = _`. Rewrite using `[ccT_J, neg_mul, Matrix.J_squared]`. Simplify using the standard rewrite rules.
-/
theorem J_mem_UU : Matrix.J (Fin N) E ∈ UU E N := by
  change ccT _ * _ * _ = _
  rw [ccT_J, neg_mul, Matrix.J_squared]; simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `ccT _ * _ * _ = _`. Rewrite using `[ccT_one]`. Simplify using the standard rewrite rules.
-/
theorem one_mem_UU : (1 : M2 E N) ∈ UU E N := by
  change ccT _ * _ * _ = _
  rw [ccT_one]; simp

omit [IsCMField E] in

/- English proof (translation)
Introduce `Z _ z z'`. Establish `h11 : (1 : M2 E N).toBlocks₁₁ = 1` using `by rw [← Matrix.fromBlocks_one]; rfl`. Establish `h12 : (1 : M2 E N).toBlocks₁₂ = 0` using `by rw [← Matrix.fromBlocks_one]; rfl`. Establish `h21 : (1 : M2 E N).toBlocks₂₁ = 0` using `by rw [← Matrix.fromBlocks_one]; rfl`. Establish `h22 : (1 : M2 E N).toBlocks₂₂ = 1` using `by rw [← Matrix.fromBlocks_one]; rfl`.

Establish `d1 : ∀ τ, hDen Ψ (1 : M2 E N) Z τ = 1` using `fun τ => by simp [hDen, h21, h22]`. Establish `d2 : ∀ τ, hDen' Ψ (1 : M2 E N) Z τ = 1` using `fun τ => by simp [hDen', h21, h22]`. Establish `a : hAct Ψ (1 : M2 E N) Z = Z` using `by funext τ; simp [hAct, d1, h11, h12]`. Establish `f : hFac Ψ (1 : M2 E N) Z z z' = 1` using `by simp [hFac, d1, h21]`. Rewrite using `[a, f, one_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `τ`. Use extensionality with `k i`. Simplify using `[d2]`. Use function extensionality and compare the values at `τ`.

Use extensionality with `k i`. Simplify using `[d1]`.
-/
theorem transH_one (φ : Matrix (Fin n) (Fin N) E → ℂ) : TransH Ψ (1 : M2 E N) φ φ := by
  intro Z _ z z'
  have h11 : (1 : M2 E N).toBlocks₁₁ = 1 := by rw [← Matrix.fromBlocks_one]; rfl
  have h12 : (1 : M2 E N).toBlocks₁₂ = 0 := by rw [← Matrix.fromBlocks_one]; rfl
  have h21 : (1 : M2 E N).toBlocks₂₁ = 0 := by rw [← Matrix.fromBlocks_one]; rfl
  have h22 : (1 : M2 E N).toBlocks₂₂ = 1 := by rw [← Matrix.fromBlocks_one]; rfl
  have d1 : ∀ τ, hDen Ψ (1 : M2 E N) Z τ = 1 := fun τ => by simp [hDen, h21, h22]
  have d2 : ∀ τ, hDen' Ψ (1 : M2 E N) Z τ = 1 := fun τ => by simp [hDen', h21, h22]
  have a : hAct Ψ (1 : M2 E N) Z = Z := by funext τ; simp [hAct, d1, h11, h12]
  have f : hFac Ψ (1 : M2 E N) Z z z' = 1 := by simp [hFac, d1, h21]
  rw [a, f, one_mul]
  congr 1
  · funext τ; ext k i; simp [d2]
  · funext τ; ext k i; simp [d1]

omit [IsCMField E] in

/- English proof (translation)
Simplify using `[gidx]`.
-/
theorem gidx_stdL : gidx (stdL E N) = 1 := by simp [gidx]

omit [IsCMField E] in

/- English proof (translation)
Unfold `thH`. Rewrite using `[tsum_eq_single 0 fun x hx => (hx (Subsingleton.elim _ _)).elim]`. Simplify using `[expo, dotProduct]`.
-/
theorem thH_deg_zero (φ : Matrix (Fin n) (Fin 0) E → ℂ) (Z : CM Ψ 0 0) (z z' : CM Ψ n 0) :
    thH Ψ φ Z z z' = φ 0 := by
  unfold thH
  rw [tsum_eq_single 0 fun x hx => (hx (Subsingleton.elim _ _)).elim]
  simp [expo, dotProduct]

omit [IsCMField E] in

/- English proof (translation)
Establish `f : ∀ Z z z', hFac Ψ γ Z (n` using `n) z z' = 1 := fun Z z z' => by simp [hFac, dotProduct]`. Establish `h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ` using `⟨φ, ⟨1, one_pos, fun _ _ _ i => i.elim0, fun _ _ _ => congrArg φ (Subsingleton.elim _ _)⟩, fun Z _ z z' => by rw [f, thH_deg_zero, thH_deg_zero, one_mul]⟩`. Use `h.choose_spec.2 _ (I_mem_Hn Ψ) 0 0` as an intermediate fact. Rewrite `this` using `[f, thH_deg_zero, thH_deg_zero, one_mul]`. Rewrite using `[weil, dif_pos h, this]`.
-/
theorem weil_deg_zero (γ : M2 E 0) (φ : Matrix (Fin n) (Fin 0) E → ℂ) : weil Ψ γ φ 0 = φ 0 := by
  have f : ∀ Z z z', hFac Ψ γ Z (n := n) z z' = 1 := fun Z z z' => by simp [hFac, dotProduct]
  have h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ :=
    ⟨φ, ⟨1, one_pos, fun _ _ _ i => i.elim0, fun _ _ _ => congrArg φ (Subsingleton.elim _ _)⟩,
      fun Z _ z z' => by rw [f, thH_deg_zero, thH_deg_zero, one_mul]⟩
  have := h.choose_spec.2 _ (I_mem_Hn Ψ) 0 0
  rw [f, thH_deg_zero, thH_deg_zero, one_mul] at this
  rw [weil, dif_pos h, this]

/- English proof (translation)
Set `U : Lag E 0` to `⟨_, 1, one_mem_UU, rfl⟩`. Unfold `eis`. Rewrite using `[tsum_eq_single U fun V hV => (hV (Subtype.ext (Subsingleton.elim _ _))).elim]`. Simplify using `[eisTerm, weil_deg_zero, hFac, dotProduct]`.
-/
theorem eis_deg_zero (φ : Matrix (Fin n) (Fin 0) E → ℂ) (Z : CM Ψ 0 0) (z z' : CM Ψ n 0) :
    eis Ψ φ Z z z' = φ 0 := by
  let U : Lag E 0 := ⟨_, 1, one_mem_UU, rfl⟩
  unfold eis
  rw [tsum_eq_single U fun V hV => (hV (Subtype.ext (Subsingleton.elim _ _))).elim]
  simp [eisTerm, weil_deg_zero, hFac, dotProduct]

/- English proof (translation)
Simplify using `[swDiff, classSum, thH_deg_zero, eis_deg_zero]`.
-/
theorem swDiff_deg_zero (M : ℕ) (φ : Fam E n 0) (Z : CM Ψ 0 0) : swDiff Ψ M φ Z = 0 := by
  simp [swDiff, classSum, thH_deg_zero, eis_deg_zero]

end Base

end

end GlobalTheory.SW
