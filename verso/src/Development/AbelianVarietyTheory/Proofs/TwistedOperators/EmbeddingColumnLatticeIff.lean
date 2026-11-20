import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UnitaryEmbeddingLine

variable {D : D7}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(α ⊗ₜ[D.host.F] b) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`.
-/
theorem tmul_mul_inc (α : AF D.host.F) (b x : D.host.E) :
    (α ⊗ₜ[D.host.F] b : AE D) * incA D x = α ⊗ₜ[D.host.F] (b * x) := by
  change (α ⊗ₜ[D.host.F] b) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/- English proof (translation)
Establish `hG : B.gramᴴ = B.gram` using `Matrix.ext fun i j => B.herm.eq _ _`. Establish `h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε` using `d.gram`. Establish `h2 : (frameMat B A d.ι)ᴴ * B.gram * d.a = 0` using `d.perp`. Establish `h3 : d.aᴴ * B.gram * frameMat B A d.ι = 0`. Use `congrArg Matrix.conjTranspose h2` as an intermediate fact.

Rewrite `this` using `[Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc]`. Conclude with `this`. Establish `hκ : antiDiagonalSignGramMatrix c ε p.rev p ≠ 0`. Use `p.2` as an intermediate fact. Establish `e : p.rev.1 + p.1 + 1 = c` using `by rw [Fin.val_rev]; omega`.

Simplify using `only [antiDiagonalSignGramMatrix, if_pos e]`. Use `split_ifs`. Conclude with `hε`. Conclude with `one_ne_zero`. Use `⟨(antiDiagonalSignGramMatrix c ε p.rev p)⁻¹ • (d.aᴴ * B.gram) p.rev, fun y u => ?_⟩` and prove the remaining obligations.

Establish `e : (d.aᴴ * B.gram) p.rev ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = ((d.aᴴ * B.gram) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u)) p.rev` using `rfl`. Rewrite using `[smul_dotProduct, e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h3, zero_mulVec, zero_add]`. Establish `e2 : (antiDiagonalSignGramMatrix c ε *ᵥ u) p.rev = antiDiagonalSignGramMatrix c ε p.rev p * u p` using `by show ∑ q, antiDiagonalSignGramMatrix c ε p.rev q * u q = _`. Use `Finset.sum_eq_single p (fun q _ hq => ?_) (by simp)` and prove the remaining obligations. Use `p.2` as an intermediate fact.

Establish `hne : ¬ (p.rev.1 + q.1 + 1 = c)`. Introduce `h`. Apply `hq` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Rewrite `h` using `[Fin.val_rev]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [antiDiagonalSignGramMatrix, if_neg hne, zero_mul]`. Rewrite using `[e2, smul_eq_mul, inv_mul_cancel_left₀ hκ]`.
-/
theorem exists_coeff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (p : Fin c) :
    ∃ r : Fin B.rank → D.host.E, ∀ (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E),
      r ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = u p := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have h2 : (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 := d.perp
  have h3 : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at this
    exact this
  have hκ : antiDiagonalSignGramMatrix c ε p.rev p ≠ 0 := by
    have := p.2
    have e : p.rev.1 + p.1 + 1 = c := by rw [Fin.val_rev]; omega
    simp only [antiDiagonalSignGramMatrix, if_pos e]
    split_ifs
    · exact hε
    · exact one_ne_zero
  refine ⟨(antiDiagonalSignGramMatrix c ε p.rev p)⁻¹ • (d.aᴴ * B.gram) p.rev, fun y u => ?_⟩
  have e : (d.aᴴ * B.gram) p.rev ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) =
      ((d.aᴴ * B.gram) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u)) p.rev := rfl
  rw [smul_dotProduct, e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h3, zero_mulVec, zero_add]
  have e2 : (antiDiagonalSignGramMatrix c ε *ᵥ u) p.rev = antiDiagonalSignGramMatrix c ε p.rev p * u p := by
    show ∑ q, antiDiagonalSignGramMatrix c ε p.rev q * u q = _
    refine Finset.sum_eq_single p (fun q _ hq => ?_) (by simp)
    have := p.2
    have hne : ¬ (p.rev.1 + q.1 + 1 = c) := by
      intro h; apply hq; apply Fin.ext; rw [Fin.val_rev] at h; omega
    simp only [antiDiagonalSignGramMatrix, if_neg hne, zero_mul]
  rw [e2, smul_eq_mul, inv_mul_cancel_left₀ hκ]

def formHom {R : Type} [CommRing R] {n : ℕ} (r : Fin n → R) : (Fin n → R) →+ R where
  toFun y := ∑ k, y k * r k
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

def lineHom {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) : R →+ (Fin n → R) where
  toFun s := fun k => s * a k
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp only [Pi.add_apply, add_mul]

/- English proof (translation)
Use `show ∑ k, s * f (a k) * f (r k) = s`. Simplify using `only [mul_assoc, ← map_mul]`. Rewrite using `[← Finset.mul_sum, ← map_sum]`. Establish `: ∑ k, a k * r k = 1`. Rewrite using `[← h, dotProduct]`.

Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Rewrite using `[this, map_one, mul_one]`.
-/
theorem form_line {K R : Type} [CommRing K] [CommRing R] (f : K →+* R) {n : ℕ} (r a : Fin n → K) (h : r ⬝ᵥ a = 1) (s : R) :
    formHom (fun k => f (r k)) (fun k => s * f (a k)) = s := by
  show ∑ k, s * f (a k) * f (r k) = s
  simp only [mul_assoc, ← map_mul]
  rw [← Finset.mul_sum, ← map_sum]
  have : ∑ k, a k * r k = 1 := by
    rw [← h, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this, map_one, mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[mul_comm]`.
-/
theorem col_eq {K : Type} [CommRing K] {n k c : ℕ} (M : Matrix (Fin n) (Fin k) K) (a : Matrix (Fin n) (Fin c) K) (p : Fin c)
    (b : K) : (fun i => b * a i p) = M *ᵥ 0 + a *ᵥ Pi.single p b := by
  funext k; simp [mul_comm]

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_coeff d hε p`. Establish `key : GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ≤ (GlobalTheory.SeeSaw.idV I v).comap (formHom fun k => incA D (r k))`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, hαv, a, ha, x, ⟨y0, -, u, hu, hx⟩, rfl⟩`. Establish `e : ∑ k, ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x k) : AE D) * incA D (r k) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p)`.

Rewrite using `[Finset.sum_congr rfl fun k _ => tmul_mul_inc (pairA D.host.F 0 α) (a * x k) (r k), ← TensorProduct.tmul_sum, ← hr y0 u, ← hx, dotProduct, Finset.mul_sum]`. Conclude with `congrArg _ (Finset.sum_congr rfl fun k _ => by ring)`. Establish `h2 : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) ∈ GlobalTheory.SeeSaw.idV I v` using `AddSubgroup.subset_closure ⟨α, hα, hαv, _, hI a ha _ (hu p), rfl⟩`. Rewrite `h2` using `[← e]`. Conclude with `h2`.

Establish `h1` using `hr 0 (Pi.single p 1)`. Rewrite `h1` using `[← col_eq, Pi.single_eq_same]`. Simplify using `only [one_mul] at h1`. Use `AddSubgroup.mem_comap.1 (key h)` as an intermediate fact. Rewrite `this` using `[form_line (incA D) r (fun k => d.a k p) h1 s]`. Then use the resulting hypothesis.
-/
theorem line_mp {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I) (s : AE D)
    (h : (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)) : s ∈ GlobalTheory.SeeSaw.idV I v := by
  obtain ⟨r, hr⟩ := exists_coeff d hε p
  have key : GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ≤ (GlobalTheory.SeeSaw.idV I v).comap (formHom fun k => incA D (r k)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, a, ha, x, ⟨y0, -, u, hu, hx⟩, rfl⟩
    have e : ∑ k, ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x k) : AE D) * incA D (r k) =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) := by
      rw [Finset.sum_congr rfl fun k _ => tmul_mul_inc (pairA D.host.F 0 α) (a * x k) (r k),
        ← TensorProduct.tmul_sum, ← hr y0 u, ← hx, dotProduct, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    have h2 : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) ∈ GlobalTheory.SeeSaw.idV I v :=
      AddSubgroup.subset_closure ⟨α, hα, hαv, _, hI a ha _ (hu p), rfl⟩
    rw [← e] at h2
    exact h2
  have h1 := hr 0 (Pi.single p 1)
  rw [← col_eq, Pi.single_eq_same] at h1
  simp only [one_mul] at h1
  have := AddSubgroup.mem_comap.1 (key h)
  rwa [form_line (incA D) r (fun k => d.a k p) h1 s] at this

/- English proof (translation)
Establish `key : GlobalTheory.SeeSaw.idV I v ≤ (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p))`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, hαv, z, hz, rfl⟩`. Use `hI' (fun z => ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] z : AE D) ∈ (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p))) ?_ ?_ z hz` and prove the remaining obligations. Introduce `a ha b hb`.

Use `AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, fun k => b * d.a k p, ⟨0, Λ.zero_mem, Pi.single p b, fun q => ?_, col_eq _ _ p b⟩, ?_⟩)` and prove the remaining obligations. Distinguish the cases in `hq : q = p`. Substitute `hq` using the available equality. Rewrite using `[Pi.single_eq_same]` and apply the resulting hypothesis. Rewrite using `[Pi.single_eq_of_ne hq]`.

Conclude with `(𝔟 q).zero_mem`. Use function extensionality and compare the values at `k`. Conclude with `(tmul_mul_inc _ _ _).trans (congrArg _ (mul_assoc _ _ _))`. Introduce `x y hx hy`. Rewrite using `[TensorProduct.tmul_add]`.

Conclude with `add_mem hx hy`. Conclude with `AddSubgroup.mem_comap.1 (key h)`.
-/
theorem line_mpr {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) (h : s ∈ GlobalTheory.SeeSaw.idV I v) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) := by
  have key : GlobalTheory.SeeSaw.idV I v ≤ (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, z, hz, rfl⟩
    refine hI' (fun z => ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] z : AE D) ∈
      (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p))) ?_ ?_ z hz
    · intro a ha b hb
      refine AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, fun k => b * d.a k p,
        ⟨0, Λ.zero_mem, Pi.single p b, fun q => ?_, col_eq _ _ p b⟩, ?_⟩)
      · by_cases hq : q = p
        · subst hq; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
      · funext k
        exact (tmul_mul_inc _ _ _).trans (congrArg _ (mul_assoc _ _ _))
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
  exact AddSubgroup.mem_comap.1 (key h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨line_mp d Λ 𝔟 p v S I hε hI s, line_mpr d Λ 𝔟 p v S I hI' s⟩`.
-/
theorem line_gen {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV I v :=
  ⟨line_mp d Λ 𝔟 p v S I hε hI s, line_mpr d Λ 𝔟 p v S I hI' s⟩

/- English proof (translation)
Introduce `D A B c ε d hε Λ 𝔟 p v s`. Use `⟨line_gen d Λ 𝔟 p v {1} (𝔟 p) hε ?_ ?_ s, line_gen d Λ 𝔟 p v {a | a ∈ D.host.AA} _ hε ?_ ?_ s⟩` and prove the remaining obligations. Introduce and unpack `a rfl b hb`. Rewrite using `[one_mul]` and apply the resulting hypothesis. Introduce `C h _ z hz`.

Use `h 1 rfl z hz` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Introduce `a ha b hb`. Conclude with `FractionalIdeal.mul_mem_mul ha hb`. Introduce `C h h' z hz`.

Conclude with `FractionalIdeal.mul_induction_on hz h h'`.
-/
theorem embedding_line_mem_lattice_iff : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D) (s : AE D), (((fun k => s * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (𝔟 p) v) ∧ ((fun k => s * incA D (d.a k p)) ∈ latA B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA * 𝔟 p) v)) := by
  intro D A B c ε d hε Λ 𝔟 p v s
  refine ⟨line_gen d Λ 𝔟 p v {1} (𝔟 p) hε ?_ ?_ s, line_gen d Λ 𝔟 p v {a | a ∈ D.host.AA} _ hε ?_ ?_ s⟩
  · rintro a rfl b hb; rwa [one_mul]
  · intro C h _ z hz
    have := h 1 rfl z hz
    rwa [one_mul] at this
  · intro a ha b hb; exact FractionalIdeal.mul_mem_mul ha hb
  · intro C h h' z hz
    exact FractionalIdeal.mul_induction_on hz h h'

end GlobalTheory.AscFin.UnitaryEmbeddingLine

end
