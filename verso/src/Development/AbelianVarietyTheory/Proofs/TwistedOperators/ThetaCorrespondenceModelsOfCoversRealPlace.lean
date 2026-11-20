import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.Lift

/- English proof (translation)
Establish `hJ : Jm p q * Jm p q = 1`. Simplify using `[Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]`. Establish `h : Zᴴ * Jm p q + Jm p q * Z = 0` using `hZ`. Establish `h2` using `congrArg (fun X => Matrix.trace (X * Jm p q)) h`. Simplify using `only [Matrix.add_mul, Matrix.trace_add, Matrix.zero_mul, Matrix.trace_zero] at h2`.

Rewrite `h2` using `[Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.trace_conjTranspose]`. Conclude with `eq_neg_of_add_eq_zero_left h2`.
-/
theorem star_trace {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : conj Z.trace = -Z.trace := by
  have hJ : Jm p q * Jm p q = 1 := by
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ
  have h2 := congrArg (fun X => Matrix.trace (X * Jm p q)) h
  simp only [Matrix.add_mul, Matrix.trace_add, Matrix.zero_mul, Matrix.trace_zero] at h2
  rw [Matrix.mul_assoc, hJ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJ, Matrix.one_mul,
    Matrix.trace_conjTranspose] at h2
  exact eq_neg_of_add_eq_zero_left h2

/- English proof (translation)
Rewrite using `[map_mul, star_trace hZ, map_ratCast, mul_neg]`.
-/
theorem star_shift {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) (c : ℚ) :
    conj ((c : ℂ) * Z.trace) = -((c : ℂ) * Z.trace) := by
  rw [map_mul, star_trace hZ, map_ratCast, mul_neg]

/- English proof (translation)
Apply the tactic sequence `cases br <;> ext i j <;> simp [phi, plainMat, barMat]`.
-/
theorem phi_add {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (X Y : Mat p q) :
    phi br e (X + Y) = phi br e X + phi br e Y := by
  cases br <;> ext i j <;> simp [phi, plainMat, barMat]

/- English proof (translation)
Apply the tactic sequence `cases br <;> ext i j <;> simp [phi, plainMat, barMat]`.
-/
theorem phi_sub {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (X Y : Mat p q) :
    phi br e (X - Y) = phi br e X - phi br e Y := by
  cases br <;> ext i j <;> simp [phi, plainMat, barMat]

/- English proof (translation)
Apply the tactic sequence `cases br <;> ext i j <;> simp [phi, plainMat, barMat]`.
-/
theorem phi_smul {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (c : ℝ) (X : Mat p q) :
    phi br e (c • X) = c • phi br e X := by
  cases br <;> ext i j <;> simp [phi, plainMat, barMat]

/- English proof (translation)
Apply the tactic sequence `cases br <;> ext i j <;> simp [phi, plainMat, barMat, Matrix.mul_apply, ← e.sum_comp]`.
-/
theorem phi_mul {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (X Y : Mat p q) :
    phi br e (X * Y) = phi br e X * phi br e Y := by
  cases br <;> ext i j <;> simp [phi, plainMat, barMat, Matrix.mul_apply, ← e.sum_comp]

/- English proof (translation)
Simplify using `only [phiFr, phi_add, Matrix.mul_add, Matrix.add_mul]`.
-/
theorem phiFr_add {p q n : ℕ} (fr : Mn n) (br : Bool) (e : Ix p q ≃ Fin n) (X Y : Mat p q) :
    phiFr fr br e (X + Y) = phiFr fr br e X + phiFr fr br e Y := by
  simp only [phiFr, phi_add, Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Simplify using `only [phiFr, phi_sub, Matrix.mul_sub, Matrix.sub_mul]`.
-/
theorem phiFr_sub {p q n : ℕ} (fr : Mn n) (br : Bool) (e : Ix p q ≃ Fin n) (X Y : Mat p q) :
    phiFr fr br e (X - Y) = phiFr fr br e X - phiFr fr br e Y := by
  simp only [phiFr, phi_sub, Matrix.mul_sub, Matrix.sub_mul]

/- English proof (translation)
Simplify using `only [phiFr, phi_smul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem phiFr_smul {p q n : ℕ} (fr : Mn n) (br : Bool) (e : Ix p q ≃ Fin n) (c : ℝ) (X : Mat p q) :
    phiFr fr br e (c • X) = c • phiFr fr br e X := by
  simp only [phiFr, phi_smul, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Establish `h1 : fr * fr⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h)`. Simplify using `only [phiFr, phi_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc fr, h1, Matrix.one_mul]`.
-/
theorem phiFr_mul {p q n : ℕ} {fr : Mn n} (h : IsUnit fr) (br : Bool) (e : Ix p q ≃ Fin n) (X Y : Mat p q) :
    phiFr fr br e (X * Y) = phiFr fr br e X * phiFr fr br e Y := by
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h)
  simp only [phiFr, phi_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc fr, h1, Matrix.one_mul]

/- English proof (translation)
Establish `hm : ∀ Z ∈ upq r s, phiFr fr br e Z ∈ L` using `fun Z hZ => hL ▸ Set.mem_image_of_mem _ hZ`. Use `⟨fun X hX Y hY => ?_, fun t X hX => ?_, fun X hX Y hY => ?_, fun X hX x y => ?_⟩` and prove the remaining obligations. Rewrite using `[phiFr_add, ha.add _ (hm X hX) _ (hm Y hY), Matrix.trace_add, mul_add, add_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[phiFr_smul, ha.smul _ _ (hm X hX), Matrix.trace_smul, smul_sub, smul_smul]`.

Use `congr 2`. Rewrite using `[Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[phiFr_sub, phiFr_mul h, phiFr_mul h, ha.lie _ (hm X hX) _ (hm Y hY), Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, mul_zero, zero_smul, sub_zero]`. Simplify using `only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul, mul_comm ((c : ℂ) * X.trace) ((c : ℂ) * Y.trace)]`.

Normalize the expressions using the abelian group laws. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, star_shift hX, ha.skew _ (hm X hX)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isUAct_shift {r s n : ℕ} {fr : Mn n} (h : IsUnit fr) (br : Bool) (e : Ix r s ≃ Fin n) (c : ℚ)
    {L : Set (Mn n)} (hL : phiFr fr br e '' upq r s = L) {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    {a : Mn n → Module.End ℂ U} (ha : IsUnitLieAct L a) :
    IsUAct (fun Z : Mat r s => a (phiFr fr br e Z) - ((c : ℂ) * Z.trace) • (1 : Module.End ℂ U)) := by
  have hm : ∀ Z ∈ upq r s, phiFr fr br e Z ∈ L := fun Z hZ => hL ▸ Set.mem_image_of_mem _ hZ
  refine ⟨fun X hX Y hY => ?_, fun t X hX => ?_, fun X hX Y hY => ?_, fun X hX x y => ?_⟩
  · rw [phiFr_add, ha.add _ (hm X hX) _ (hm Y hY), Matrix.trace_add, mul_add, add_smul]
    abel
  · rw [phiFr_smul, ha.smul _ _ (hm X hX), Matrix.trace_smul, smul_sub, smul_smul]
    congr 2
    rw [Complex.real_smul]; ring
  · rw [phiFr_sub, phiFr_mul h, phiFr_mul h, ha.lie _ (hm X hX) _ (hm Y hY), Matrix.trace_sub,
      Matrix.trace_mul_comm X Y, sub_self, mul_zero, zero_smul, sub_zero]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul,
      mul_comm ((c : ℂ) * X.trace) ((c : ℂ) * Y.trace)]
    abel
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, star_shift hX, ha.skew _ (hm X hX)]
    ring

section Tr

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau} {p q : ℕ} {T : GrpData p q}
  {R : DSRep T} {l : Ix p q → ℚ} {c : ℚ} {b : Bool} {e : Ix p q ≃ Fin V.rank} {u : kfin M τ → R.HK.V}

def barEquiv (h : KTie R M τ l c b true e u) : kfin M τ ≃ₛₗ[starRingEnd ℂ] R.HK.V :=
  LinearEquiv.ofBijective
    ({ toFun := u, map_add' := h.add, map_smul' := fun z x => by simpa [cjc] using h.smul z x } :
      kfin M τ →ₛₗ[starRingEnd ℂ] R.HK.V) h.bij

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem barEquiv_apply (h : KTie R M τ l c b true e u) (v) : barEquiv h v = u v := rfl

def linEquiv (h : KTie R M τ l c b false e u) : kfin M τ ≃ₗ[ℂ] R.HK.V :=
  LinearEquiv.ofBijective
    ({ toFun := u, map_add' := h.add, map_smul' := fun z x => by simpa [cjc] using h.smul z x } :
      kfin M τ →ₗ[ℂ] R.HK.V) h.bij

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem linEquiv_apply (h : KTie R M τ l c b false e u) (v) : linEquiv h v = u v := rfl

variable {ι σ Z : Type} {A : Mn V.rank → (Z → ℂ) → (Z → ℂ)} {pt : MvPolynomial ι ℂ → (Z → ℂ)}
  (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) {a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
  {U : Type} [AddCommGroup U] [Module ℂ U]

/- English proof (translation)
Use `⟨(f ∘ₗ κ.symm.toLinearMap).compl₂ (barEquiv h).symm.toLinearMap, fun P v => ?_⟩` and prove the remaining obligations. Simplify using `[← barEquiv_apply h]`.
-/
theorem ex_pair (h : KTie R M τ l c b true e u) (f : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U) :
    ∃ B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, ∀ P v, B (κ P) (u v) = f P v := by
  refine ⟨(f ∘ₗ κ.symm.toLinearMap).compl₂ (barEquiv h).symm.toLinearMap, fun P v => ?_⟩
  simp [← barEquiv_apply h]

/- English proof (translation)
Use `⟨(B ∘ₗ κ.toLinearMap).compl₂ (barEquiv h).toLinearMap, fun P v => ?_⟩` and prove the remaining obligations. Simplify using `[← barEquiv_apply h]`.
-/
theorem ex_map (h : KTie R M τ l c b true e u) (B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) :
    ∃ f : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U, ∀ P v, B (κ P) (u v) = f P v := by
  refine ⟨(B ∘ₗ κ.toLinearMap).compl₂ (barEquiv h).toLinearMap, fun P v => ?_⟩
  simp [← barEquiv_apply h]

variable {κ}

/- English proof (translation)
Establish `key : ∀ Y ∈ upq p q, ∀ P v, B (a Y P + ((c : ℂ) * Y.trace) • P) v + B P (R.HK.act Y v + ((c : ℂ) * Y.trace) • v) = B (a Y P) v + B P (R.HK.act Y v)`. Introduce `Y hY P v`. Rewrite using `[map_add, map_add, map_smul, LinearMap.map_smulₛₗ, star_shift hY, LinearMap.add_apply, LinearMap.smul_apply, neg_smul]`. Normalize the expressions using the abelian group laws. Prove the components needed by the constructor for the conclusion.

Introduce `hi Y hY P v`. Take `⟨P, rfl⟩` from `κ.surjective P`. Take `⟨v, rfl⟩` from `h.bij.2 v`. Take `⟨P', hP'⟩` from `κ.surjective (a Y (κ P) + ((c : ℂ) * Y.trace) • κ P)`. Take `⟨v', hv'⟩` from `h.bij.2 (R.HK.act Y (u v) + ((c : ℂ) * Y.trace) • u v)`.

Use `hi _ (h.lie ▸ Set.mem_image_of_mem _ hY) P P' v v' ((hs.der Y hY P P').2 hP') ((h.der Y hY v v').2 hv')` as an intermediate fact. Rewrite `this` using `[← hB, ← hB, hP', hv', key Y hY]`. Conclude with `this`. Introduce `hi X hX P P' v v' hP hv`. Rewrite `hX` using `[← h.lie]`.

Take `⟨Y, hY, rfl⟩` from `hX`. Rewrite using `[← hB, ← hB, (hs.der Y hY P P').1 hP, (h.der Y hY v v').1 hv, key Y hY]`. Conclude with `hi Y hY _ _`.
-/
theorem isInv_iff (h : KTie R M τ l c b true e u) (hs : Side A pt κ (phiFr (M.fr τ) b e) c a)
    {f : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U} {B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U}
    (hB : ∀ P v, B (κ P) (u v) = f P v) : IsInv M τ A pt f ↔ PInv a R B := by
  have key : ∀ Y ∈ upq p q, ∀ P v, B (a Y P + ((c : ℂ) * Y.trace) • P) v +
      B P (R.HK.act Y v + ((c : ℂ) * Y.trace) • v) = B (a Y P) v + B P (R.HK.act Y v) := by
    intro Y hY P v
    rw [map_add, map_add, map_smul, LinearMap.map_smulₛₗ, star_shift hY, LinearMap.add_apply, LinearMap.smul_apply,
      neg_smul]
    abel
  constructor
  · intro hi Y hY P v
    obtain ⟨P, rfl⟩ := κ.surjective P
    obtain ⟨v, rfl⟩ := h.bij.2 v
    obtain ⟨P', hP'⟩ := κ.surjective (a Y (κ P) + ((c : ℂ) * Y.trace) • κ P)
    obtain ⟨v', hv'⟩ := h.bij.2 (R.HK.act Y (u v) + ((c : ℂ) * Y.trace) • u v)
    have := hi _ (h.lie ▸ Set.mem_image_of_mem _ hY) P P' v v' ((hs.der Y hY P P').2 hP') ((h.der Y hY v v').2 hv')
    rw [← hB, ← hB, hP', hv', key Y hY] at this
    exact this
  · intro hi X hX P P' v v' hP hv
    rw [← h.lie] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    rw [← hB, ← hB, (hs.der Y hY P P').1 hP, (h.der Y hY v v').1 hv, key Y hY]
    exact hi Y hY _ _

/- English proof (translation)
Use `LinearMap.ext fun P => LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨P, rfl⟩` from `κ.surjective P`. Take `⟨v, rfl⟩` from `h.bij.2 v`. Conclude with `H P v`.
-/
theorem pair_ext (h : KTie R M τ l c b true e u)
    {B B' : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U} (H : ∀ P v, B (κ P) (u v) = B' (κ P) (u v)) :
    B = B' := by
  refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
  obtain ⟨P, rfl⟩ := κ.surjective P
  obtain ⟨v, rfl⟩ := h.bij.2 v
  exact H P v

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hi Y hY P v`. Take `⟨P, rfl⟩` from `κ.surjective P`. Take `⟨v, rfl⟩` from `h.bij.2 v`. Take `⟨P', hP'⟩` from `κ.surjective (a' Y (κ P) + ((c' : ℂ) * Y.trace) • κ P)`.

Use `(hR Y hY _ _).1 (hi _ (hL ▸ Set.mem_image_of_mem _ hY) P P' ((hs.der Y hY P P').2 hP') v)` as an intermediate fact. Rewrite `this` using `[← hB, ← hB, hP', map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]`. Conclude with `add_right_cancel this`. Introduce `hi X hX P P' hP v`. Rewrite `hX` using `[← hL]`.

Take `⟨Y, hY, rfl⟩` from `hX`. Rewrite using `[hR Y hY, ← hB, ← hB, (hs.der Y hY P P').1 hP, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hi Y hY]`.
-/
theorem equiv_iff (h : KTie R M τ l c b true e u) {r s n : ℕ} {A' : Mn n → (Z → ℂ) → (Z → ℂ)} {φ : Mat r s → Mn n}
    {c' : ℚ} {a' : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} (hs : Side A' pt κ φ c' a') {L : Set (Mn n)}
    (hL : φ '' upq r s = L) {U' : Type} (Rel : Mn n → U' → U' → Prop) (w : U' → U) (β : Mat r s → Module.End ℂ U)
    (hR : ∀ Y ∈ upq r s, ∀ x y, Rel (φ Y) x y ↔ w y = β Y (w x) + ((c' : ℂ) * Y.trace) • w x)
    {f : MvPolynomial ι ℂ → kfin M τ → U'} {B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U}
    (hB : ∀ P v, B (κ P) (u v) = w (f P v)) :
    (∀ Y ∈ L, ∀ P P', PolDer A' pt Y P P' → ∀ v, Rel Y (f P v) (f P' v)) ↔
      ∀ Y ∈ upq r s, ∀ P v, B (a' Y P) v = β Y (B P v) := by
  constructor
  · intro hi Y hY P v
    obtain ⟨P, rfl⟩ := κ.surjective P
    obtain ⟨v, rfl⟩ := h.bij.2 v
    obtain ⟨P', hP'⟩ := κ.surjective (a' Y (κ P) + ((c' : ℂ) * Y.trace) • κ P)
    have := (hR Y hY _ _).1 (hi _ (hL ▸ Set.mem_image_of_mem _ hY) P P' ((hs.der Y hY P P').2 hP') v)
    rw [← hB, ← hB, hP', map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at this
    exact add_right_cancel this
  · intro hi X hX P P' hP v
    rw [← hL] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    rw [hR Y hY, ← hB, ← hB, (hs.der Y hY P P').1 hP, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hi Y hY]

end Tr

/- English proof (translation)
Introduce `D V S M W S' N τ ι σ Z A B pt κ p q r s T₁ T₂ R₁ R₂ a₁ a₂ l₁ l₂ c₁ c₂ b₁ b₂ e₁ e₂ u₁ u₂ h₁ h₂ s₁ s₂ hJ hP`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨Φ, hΦ⟩` from `hP.ex`. Take `⟨Φ, rfl⟩` from `κ.surjective Φ`. Conclude with `⟨Φ, (hJ Φ).2 hΦ⟩`.

Introduce `Φ Φ' h h'`. Take `⟨c, hc⟩` from `hP.uniq _ _ ((hJ Φ).1 h) ((hJ Φ').1 h')`. Conclude with `⟨c, κ.injective (by rw [hc, map_smul])⟩`. Introduce `U _ _ a ha f hf hf0`. Establish `hb` using `isUAct_shift (N.fr_unit τ) b₂ e₂ c₂ h₂.lie ha`.

Establish `tr : ∀ {g : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U} {C : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U}, (∀ P v, C (κ P) (u₁ v) = g P v) → IsLiftMap M τ A pt B (fun Y x y => y = a Y x) g → PLift a₁ a₂ R₁ (fun Y : Mat r s => a (phiFr (N.fr τ) b₂ e₂ Y) - ((c₂ : ℂ) * Y.trace) …` using `fun {g C} hC hg => ⟨(isInv_iff h₁ s₁ hC).1 hg.1, (equiv_iff h₁ s₂ h₂.lie (fun Y x y => y = a Y x) id _ (fun Y _ x y => by simp) (f := fun P v => g P v) hC).1 hg.2⟩`. Take `⟨C, hC⟩` from `ex_pair κ h₁ f`. Establish `hC0 : C ≠ 0`. Introduce and unpack `rfl`. Conclude with `hf0 (LinearMap.ext fun P => LinearMap.ext fun v => by simpa using (hC P v).symm)`.

Take `⟨⟨e, he, hei, her⟩, hrest⟩` from `hP.unit U _ hb C (tr hC hf) hC0`. Use `⟨⟨e ∘ₗ (linEquiv h₂).toLinearMap, he.comp (linEquiv h₂).injective, ?_, ?_⟩, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Introduce `X hX x x' hx`. Rewrite `hX` using `[← h₂.lie]`. Take `⟨Y, hY, rfl⟩` from `hX`.

Use `(h₂.der Y hY x x').1 hx` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, linEquiv_apply]`. Rewrite using `[this, map_add, map_smul, hei Y hY]`. Simplify using the standard rewrite rules. Rewrite using `[LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), her]`.

Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, v, rfl⟩`. Take `⟨P, rfl⟩` from `κ.surjective P`.

Take `⟨v, rfl⟩` from `h₁.bij.2 v`. Conclude with `⟨P, v, hC P v⟩`. Introduce and unpack `⟨P, v, rfl⟩`. Conclude with `⟨κ P, u₁ v, (hC P v).symm⟩`. Take `⟨hne, hu⟩` from `hrest _ ((hJ Φ).1 hΦ)`.

Use `⟨fun v hv => ?_, fun f' hf' hΦ' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hC]`. Conclude with `hne _ ((h₁.hi v).1 hv)`. Take `⟨C', hC'⟩` from `ex_pair κ h₁ f'`. Establish `: C' = C` using `hu C' (tr hC' hf') (LinearMap.ext fun v => by`.

Take `⟨v, rfl⟩` from `h₁.bij.2 v`. Rewrite using `[hC, hC', hΦ'])`. Use `LinearMap.ext fun P => LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[← hC, ← hC', this]`. Take `⟨C₀, hC0, hl, hu⟩` from `hP.line`.

Establish `tr : ∀ {g : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] kfin N τ} {C : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] R₂.HK.V}, (∀ P v, C (κ P) (u₁ v) = u₂ (g P v)) → (IsLiftMap M τ A pt B (VecDer N τ) g ↔ PLift a₁ a₂ R₁ (fun Y => R₂.HK.act Y) C)`. Introduce `g C hC`. Use `and_congr ?_ (equiv_iff h₁ s₂ h₂.lie (VecDer N τ) u₂ _ h₂.der (f := fun P v => g P v) hC)` and prove the remaining obligations. Use `Iff.trans ?_ (isInv_iff h₁ s₁ (f := g.compr₂ (linEquiv h₂).toLinearMap) hC)` and prove the remaining obligations. Use `forall₂_congr fun X _ => forall₄_congr fun P P' v v' => forall₂_congr fun _ _ => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.compr₂_apply, LinearEquiv.coe_coe]`. Rewrite using `[← map_add, LinearEquiv.map_eq_zero_iff]`. Take `⟨g, hg⟩` from `ex_map κ h₁ C₀`. Establish `hg' : ∀ P v, C₀ (κ P) (u₁ v) = u₂ (g.compr₂ (linEquiv h₂).symm.toLinearMap P v)`. Introduce `P v`.

Simplify using `[hg, ← linEquiv_apply h₂]`. Use `⟨g.compr₂ (linEquiv h₂).symm.toLinearMap, fun h0 => hC0 (pair_ext (κ := κ) h₁ fun P v => ?_), (tr hg').2 hl, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[hg', h0, ← linEquiv_apply h₂]`. Simplify using the standard rewrite rules. Take `⟨C, hC⟩` from `ex_pair κ h₁ (f.compr₂ (linEquiv h₂).toLinearMap)`.

Take `⟨c, hc⟩` from `hu C ((tr hC).1 hf)`. Use `⟨c, LinearMap.ext fun P => LinearMap.ext fun v => (linEquiv h₂).injective ?_⟩` and prove the remaining obligations. Use `hC P v` as an intermediate fact. Rewrite `this` using `[hc]`. Simplify using `only [LinearMap.smul_apply, LinearMap.compr₂_apply, LinearEquiv.coe_coe, hg] at this`.

Simplify using `[← this]`.
-/
theorem liftLaw_of_pairLaw : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (l₂ : Ix r s → ℚ) (c₁ c₂ : ℚ) (b₁ b₂ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (e₂ : Ix r s ≃ Fin W.rank) (u₁ : kfin M τ → R₁.HK.V) (u₂ : kfin N τ → R₂.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → KTie R₂ N τ l₂ c₂ b₂ false e₂ u₂ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → Side B pt κ (phiFr (N.fr τ) b₂ e₂) c₂ a₂ → (∀ Φ, IsJoint M τ A pt N B Φ ↔ CJoint a₁ a₂ (blattner l₁) (blattner l₂) (κ Φ)) → PairLaw a₁ a₂ R₁ R₂ (blattner l₁) (blattner l₂) → LiftLaw M τ A pt N B := by
  intro D V S M W S' N τ ι σ Z A B pt κ p q r s T₁ T₂ R₁ R₂ a₁ a₂ l₁ l₂ c₁ c₂ b₁ b₂ e₁ e₂ u₁ u₂ h₁ h₂ s₁ s₂ hJ hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨Φ, hΦ⟩ := hP.ex
    obtain ⟨Φ, rfl⟩ := κ.surjective Φ
    exact ⟨Φ, (hJ Φ).2 hΦ⟩
  · intro Φ Φ' h h'
    obtain ⟨c, hc⟩ := hP.uniq _ _ ((hJ Φ).1 h) ((hJ Φ').1 h')
    exact ⟨c, κ.injective (by rw [hc, map_smul])⟩
  · intro U _ _ a ha f hf hf0
    have hb := isUAct_shift (N.fr_unit τ) b₂ e₂ c₂ h₂.lie ha
    have tr : ∀ {g : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U}
        {C : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U}, (∀ P v, C (κ P) (u₁ v) = g P v) →
        IsLiftMap M τ A pt B (fun Y x y => y = a Y x) g →
        PLift a₁ a₂ R₁ (fun Y : Mat r s => a (phiFr (N.fr τ) b₂ e₂ Y) - ((c₂ : ℂ) * Y.trace) • (1 : Module.End ℂ U)) C :=
      fun {g C} hC hg => ⟨(isInv_iff h₁ s₁ hC).1 hg.1,
        (equiv_iff h₁ s₂ h₂.lie (fun Y x y => y = a Y x) id _ (fun Y _ x y => by simp)
          (f := fun P v => g P v) hC).1 hg.2⟩
    obtain ⟨C, hC⟩ := ex_pair κ h₁ f
    have hC0 : C ≠ 0 := by
      rintro rfl
      exact hf0 (LinearMap.ext fun P => LinearMap.ext fun v => by simpa using (hC P v).symm)
    obtain ⟨⟨e, he, hei, her⟩, hrest⟩ := hP.unit U _ hb C (tr hC hf) hC0
    refine ⟨⟨e ∘ₗ (linEquiv h₂).toLinearMap, he.comp (linEquiv h₂).injective, ?_, ?_⟩, fun Φ hΦ => ?_⟩
    · intro X hX x x' hx
      rw [← h₂.lie] at hX
      obtain ⟨Y, hY, rfl⟩ := hX
      have := (h₂.der Y hY x x').1 hx
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, linEquiv_apply]
      rw [this, map_add, map_smul, hei Y hY]
      simp
    · rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), her]
      congr 1
      ext y
      constructor
      · rintro ⟨P, v, rfl⟩
        obtain ⟨P, rfl⟩ := κ.surjective P
        obtain ⟨v, rfl⟩ := h₁.bij.2 v
        exact ⟨P, v, hC P v⟩
      · rintro ⟨P, v, rfl⟩
        exact ⟨κ P, u₁ v, (hC P v).symm⟩
    · obtain ⟨hne, hu⟩ := hrest _ ((hJ Φ).1 hΦ)
      refine ⟨fun v hv => ?_, fun f' hf' hΦ' => ?_⟩
      · rw [← hC]
        exact hne _ ((h₁.hi v).1 hv)
      · obtain ⟨C', hC'⟩ := ex_pair κ h₁ f'
        have : C' = C := hu C' (tr hC' hf') (LinearMap.ext fun v => by
          obtain ⟨v, rfl⟩ := h₁.bij.2 v
          rw [hC, hC', hΦ'])
        refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
        rw [← hC, ← hC', this]
  · obtain ⟨C₀, hC0, hl, hu⟩ := hP.line
    have tr : ∀ {g : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] kfin N τ}
        {C : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] R₂.HK.V}, (∀ P v, C (κ P) (u₁ v) = u₂ (g P v)) →
        (IsLiftMap M τ A pt B (VecDer N τ) g ↔ PLift a₁ a₂ R₁ (fun Y => R₂.HK.act Y) C) := by
      intro g C hC
      refine and_congr ?_ (equiv_iff h₁ s₂ h₂.lie (VecDer N τ) u₂ _ h₂.der (f := fun P v => g P v) hC)
      refine Iff.trans ?_ (isInv_iff h₁ s₁ (f := g.compr₂ (linEquiv h₂).toLinearMap) hC)
      refine forall₂_congr fun X _ => forall₄_congr fun P P' v v' => forall₂_congr fun _ _ => ?_
      simp only [LinearMap.compr₂_apply, LinearEquiv.coe_coe]
      rw [← map_add, LinearEquiv.map_eq_zero_iff]
    obtain ⟨g, hg⟩ := ex_map κ h₁ C₀
    have hg' : ∀ P v, C₀ (κ P) (u₁ v) = u₂ (g.compr₂ (linEquiv h₂).symm.toLinearMap P v) := by
      intro P v
      simp [hg, ← linEquiv_apply h₂]
    refine ⟨g.compr₂ (linEquiv h₂).symm.toLinearMap, fun h0 => hC0 (pair_ext (κ := κ) h₁ fun P v => ?_),
      (tr hg').2 hl, fun f hf => ?_⟩
    · rw [hg', h0, ← linEquiv_apply h₂]
      simp
    · obtain ⟨C, hC⟩ := ex_pair κ h₁ (f.compr₂ (linEquiv h₂).toLinearMap)
      obtain ⟨c, hc⟩ := hu C ((tr hC).1 hf)
      refine ⟨c, LinearMap.ext fun P => LinearMap.ext fun v => (linEquiv h₂).injective ?_⟩
      have := hC P v
      rw [hc] at this
      simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, LinearEquiv.coe_coe, hg] at this
      simp [← this]

end GlobalTheory.ArchRec.Lift

end
