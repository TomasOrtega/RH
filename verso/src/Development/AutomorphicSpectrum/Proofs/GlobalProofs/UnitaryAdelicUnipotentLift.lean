import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviEqISupParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange

open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm

section Abstract

variable {R : Type} [CommRing R] {n d : ℕ}

/- English proof (translation)
Establish `hQs : Formalism.UG.cT s (1 - (Xb * LY + Yb * LX)) * J = J * (1 - (Xb * LY + Yb * LX))`. Rewrite using `[Comm.cT_sub, Formalism.UG.cT_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]`. Establish `hQg` using `Comm.mul_eq_of_unitary hJ hg hQs hQ`. Establish `hgP : g * (Xb * LY + Yb * LX) = (Xb * LY + Yb * LX) * g`. Use `hQ.trans hQg.symm` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]`. Conclude with `sub_right_injective this`. Establish `hPX : (Xb * LY + Yb * LX) * Xb = Xb`. Rewrite using `[Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, yx, xx, Matrix.mul_one, Matrix.mul_zero, add_zero]`. Establish `hPY : (Xb * LY + Yb * LX) * Yb = Yb`.

Rewrite using `[Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, yy, xy, Matrix.mul_one, Matrix.mul_zero, zero_add]`. Establish `hgX : g * Xb = Xb * (LY * (g * Xb))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = Xb * (LY * (g * Xb)) := by rw [h1, Matrix.mul_zero, add_zero]`.

Establish `hgY : g * Yb = Yb * (LX * (g * Yb))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = Yb * (LX * (g * Yb)) := by rw [h2, Matrix.mul_zero, zero_add]`. Generalize the expression as in `LY * (g * Xb) = A at hgX ⊢`.

Generalize the expression as in `LX * (g * Yb) = A' at hgY ⊢`. Establish `gP : g * (Xb * LY + Yb * LX) = Xb * A * LY + Yb * A' * LX`. Rewrite using `[Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgX, hgY]`. Establish `c1 : Formalism.UG.cT s (g * Yb) * J * (g * Xb) = LY * Xb`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Formalism.UG.cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = LY * Xb := by rw [hg, eY]`. Establish `c2 : Formalism.UG.cT s (g * Xb) * J * (g * Yb) = LX * Yb`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Formalism.UG.cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = LX * Yb := by rw [hg, eX]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : g * (1 - (Xb * LY + Yb * LX)) + g * (Xb * LY + Yb * LX) = g`.

Rewrite using `[← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]`. Rewrite `e` using `[hQ, gP]`. Rewrite using `[Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one]`. Rewrite using `[← e]`. Normalize the expressions using the abelian group laws.

Rewrite `c2` using `[hgY, hgX, Formalism.UG.cT_mul]`. Establish `: Formalism.UG.cT s A * (Formalism.UG.cT s Xb * J * Yb) * A' = LX * Yb`. Rewrite using `[← c2]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite `this` using `[eX, xy, Matrix.mul_one]`. Then use the resulting hypothesis.

Rewrite `c1` using `[hgY, hgX, Formalism.UG.cT_mul]`. Establish `: Formalism.UG.cT s A' * (Formalism.UG.cT s Yb * J * Xb) * A = LY * Xb`. Rewrite using `[← c1]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite `this` using `[eY, yx, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem block_form {s : R →+* R} {g J : Matrix (Fin n) (Fin n) R} {Xb Yb : Matrix (Fin n) (Fin d) R}
    {LX LY : Matrix (Fin d) (Fin n) R} (hJ : IsUnit J.det)
    (hg : Formalism.UG.cT s g * J * g = J) (eX : Formalism.UG.cT s Xb * J = LX) (eY : Formalism.UG.cT s Yb * J = LY)
    (xx : LX * Xb = 0) (xy : LX * Yb = 1) (yx : LY * Xb = 1) (yy : LY * Yb = 0)
    (hP : Formalism.UG.cT s (Xb * LY + Yb * LX) * J = J * (Xb * LY + Yb * LX))
    (hQ : g * (1 - (Xb * LY + Yb * LX)) = 1 - (Xb * LY + Yb * LX))
    (h1 : LX * (g * Xb) = 0) (h2 : LY * (g * Yb) = 0) :
    g = 1 + Xb * (LY * (g * Xb) - 1) * LY + Yb * (LX * (g * Yb) - 1) * LX ∧
      Formalism.UG.cT s (LY * (g * Xb)) * (LX * (g * Yb)) = 1 ∧
      Formalism.UG.cT s (LX * (g * Yb)) * (LY * (g * Xb)) = 1 := by
  have hQs : Formalism.UG.cT s (1 - (Xb * LY + Yb * LX)) * J = J * (1 - (Xb * LY + Yb * LX)) := by
    rw [Comm.cT_sub, Formalism.UG.cT_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]
  have hQg := Comm.mul_eq_of_unitary hJ hg hQs hQ
  have hgP : g * (Xb * LY + Yb * LX) = (Xb * LY + Yb * LX) * g := by
    have := hQ.trans hQg.symm
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact sub_right_injective this
  have hPX : (Xb * LY + Yb * LX) * Xb = Xb := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, yx, xx, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hPY : (Xb * LY + Yb * LX) * Yb = Yb := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, yy, xy, Matrix.mul_one, Matrix.mul_zero, zero_add]
  have hgX : g * Xb = Xb * (LY * (g * Xb)) := by
    calc g * Xb = (Xb * LY + Yb * LX) * g * Xb := by rw [← hgP, Matrix.mul_assoc, hPX]
      _ = Xb * (LY * (g * Xb)) + Yb * (LX * (g * Xb)) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = Xb * (LY * (g * Xb)) := by rw [h1, Matrix.mul_zero, add_zero]
  have hgY : g * Yb = Yb * (LX * (g * Yb)) := by
    calc g * Yb = (Xb * LY + Yb * LX) * g * Yb := by rw [← hgP, Matrix.mul_assoc, hPY]
      _ = Xb * (LY * (g * Yb)) + Yb * (LX * (g * Yb)) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = Yb * (LX * (g * Yb)) := by rw [h2, Matrix.mul_zero, zero_add]
  generalize LY * (g * Xb) = A at hgX ⊢
  generalize LX * (g * Yb) = A' at hgY ⊢
  have gP : g * (Xb * LY + Yb * LX) = Xb * A * LY + Yb * A' * LX := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgX, hgY]
  have c1 : Formalism.UG.cT s (g * Yb) * J * (g * Xb) = LY * Xb := by
    calc Formalism.UG.cT s (g * Yb) * J * (g * Xb) = Formalism.UG.cT s Yb * (Formalism.UG.cT s g * J * g) * Xb := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = LY * Xb := by rw [hg, eY]
  have c2 : Formalism.UG.cT s (g * Xb) * J * (g * Yb) = LX * Yb := by
    calc Formalism.UG.cT s (g * Xb) * J * (g * Yb) = Formalism.UG.cT s Xb * (Formalism.UG.cT s g * J * g) * Yb := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = LX * Yb := by rw [hg, eX]
  refine ⟨?_, ?_, ?_⟩
  · have e : g * (1 - (Xb * LY + Yb * LX)) + g * (Xb * LY + Yb * LX) = g := by
      rw [← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
    rw [hQ, gP] at e
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one]
    rw [← e]
    abel
  · rw [hgY, hgX, Formalism.UG.cT_mul] at c2
    have : Formalism.UG.cT s A * (Formalism.UG.cT s Xb * J * Yb) * A' = LX * Yb := by
      rw [← c2]; simp only [Matrix.mul_assoc]
    rwa [eX, xy, Matrix.mul_one] at this
  · rw [hgY, hgX, Formalism.UG.cT_mul] at c1
    have : Formalism.UG.cT s A' * (Formalism.UG.cT s Yb * J * Xb) * A = LY * Xb := by
      rw [← c1]; simp only [Matrix.mul_assoc]
    rwa [eY, yx, Matrix.mul_one] at this

end Abstract

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

/- English proof (translation)
Establish `hL' : adMat F L * adMat F (initCols Z k) = 1`. Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `key : ∀ u : GAd σ J, (∀ y ∈ colSpan F Z {i | i ≤ k}, (GlobalTheory.AdelicU.matHom (AF F) σ J u).1 *ᵥ y ∈ colSpan F Z {i | i ≤ k}) → ∃ B : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) (AF F ⊗[F] E), (GlobalTheory.AdelicU.matHom (AF F) σ J u).1 * adMat F (initCols Z k) = adMat F (ini …` using `fun u hu => by`. Use `⟨adMat F L * ((GlobalTheory.AdelicU.matHom (AF F) σ J u).1 * adMat F (initCols Z k)), ?_⟩` and prove the remaining obligations. Use extensionality with `p i`.

Establish `hc : adMat F (initCols Z k) *ᵥ Pi.single i 1 ∈ colSpan F Z {i | i ≤ k}` using `mem_colSpan_iff.2 ⟨_, rfl⟩`. Take `⟨a, ha⟩` from `mem_colSpan_iff.1 (hu _ hc)`. Establish `e1 : ((GlobalTheory.AdelicU.matHom (AF F) σ J u).1 * adMat F (initCols Z k)) *ᵥ Pi.single i 1 = adMat F (initCols Z k) *ᵥ a`. Rewrite using `[ha, mulVec_mulVec]`. Establish `e2 : (adMat F (initCols Z k) * (adMat F L * ((GlobalTheory.AdelicU.matHom (AF F) σ J u).1 * adMat F (initCols Z k)))) *ᵥ Pi.single i 1 = adMat F (initCols Z k) *ᵥ a`.

Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, e1, mulVec_mulVec a (adMat F L), hL', one_mulVec]`. Use `congrFun (e1.trans e2.symm) p` as an intermediate fact. Rewrite `this` using `[mulVec_single_one, mulVec_single_one]`. Then use the resulting hypothesis. Take `⟨B, a1⟩` from `key g h1`. Take `⟨B', a2⟩` from `key g⁻¹ h2`.

Establish `e3 : (GlobalTheory.AdelicU.matHom (AF F) σ J g⁻¹).1 * (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 = 1`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `e4 : (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 * (GlobalTheory.AdelicU.matHom (AF F) σ J g⁻¹).1 = 1`. Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`. Establish `canc : ∀ D : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) (AF F ⊗[F] E), adMat F (initCols Z k) * D = adMat F (initCols Z k) → D = 1` using `fun D e => by`.

Establish `: adMat F L * (adMat F (initCols Z k) * D) = adMat F L * adMat F (initCols Z k)` using `by rw [e]`. Rewrite `this` using `[← Matrix.mul_assoc, hL', Matrix.one_mul]`. Then use the resulting hypothesis. Establish `hB'B : B' * B = 1` using `canc _ (by`. Rewrite using `[← Matrix.mul_assoc, ← a2, Matrix.mul_assoc, ← a1, ← Matrix.mul_assoc, e3, Matrix.one_mul])`. Establish `hBB' : B * B' = 1` using `canc _ (by`.

Rewrite using `[← Matrix.mul_assoc, ← a1, Matrix.mul_assoc, ← a2, ← Matrix.mul_assoc, e4, Matrix.one_mul])`. Conclude with `⟨⟨B, B', hBB', hB'B⟩, trivial, a1⟩`.
-/
theorem mem_frameStab_of_stable {Z : Matrix (Fin n) (Fin r) E} {k : Fin r} {L : Matrix (Fin (k.val + 1)) (Fin n) E}
    (hL : L * initCols Z k = 1) {g : GAd σ J}
    (h1 : ∀ y ∈ colSpan F Z {i | i ≤ k}, (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 *ᵥ y ∈ colSpan F Z {i | i ≤ k})
    (h2 : ∀ y ∈ colSpan F Z {i | i ≤ k}, (GlobalTheory.AdelicU.matHom (AF F) σ J g⁻¹).1 *ᵥ y ∈ colSpan F Z {i | i ≤ k}) :
    g ∈ frameStab σ J (initCols Z k) ⊤ := by
  have hL' : adMat F L * adMat F (initCols Z k) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ u : GAd σ J, (∀ y ∈ colSpan F Z {i | i ≤ k}, (GlobalTheory.AdelicU.matHom (AF F) σ J u).1 *ᵥ y ∈ colSpan F Z {i | i ≤ k}) →
      ∃ B : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) (AF F ⊗[F] E),
        (GlobalTheory.AdelicU.matHom (AF F) σ J u).1 * adMat F (initCols Z k) = adMat F (initCols Z k) * B := fun u hu => by
    refine ⟨adMat F L * ((GlobalTheory.AdelicU.matHom (AF F) σ J u).1 * adMat F (initCols Z k)), ?_⟩
    ext p i
    have hc : adMat F (initCols Z k) *ᵥ Pi.single i 1 ∈ colSpan F Z {i | i ≤ k} := mem_colSpan_iff.2 ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := mem_colSpan_iff.1 (hu _ hc)
    have e1 : ((GlobalTheory.AdelicU.matHom (AF F) σ J u).1 * adMat F (initCols Z k)) *ᵥ Pi.single i 1 = adMat F (initCols Z k) *ᵥ a := by
      rw [ha, mulVec_mulVec]
    have e2 : (adMat F (initCols Z k) * (adMat F L * ((GlobalTheory.AdelicU.matHom (AF F) σ J u).1 * adMat F (initCols Z k)))) *ᵥ Pi.single i 1 =
        adMat F (initCols Z k) *ᵥ a := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, e1, mulVec_mulVec a (adMat F L), hL', one_mulVec]
    have := congrFun (e1.trans e2.symm) p
    rwa [mulVec_single_one, mulVec_single_one] at this
  obtain ⟨B, a1⟩ := key g h1
  obtain ⟨B', a2⟩ := key g⁻¹ h2
  have e3 : (GlobalTheory.AdelicU.matHom (AF F) σ J g⁻¹).1 * (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have e4 : (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 * (GlobalTheory.AdelicU.matHom (AF F) σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have canc : ∀ D : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) (AF F ⊗[F] E),
      adMat F (initCols Z k) * D = adMat F (initCols Z k) → D = 1 := fun D e => by
    have : adMat F L * (adMat F (initCols Z k) * D) = adMat F L * adMat F (initCols Z k) := by rw [e]
    rwa [← Matrix.mul_assoc, hL', Matrix.one_mul] at this
  have hB'B : B' * B = 1 := canc _ (by
    rw [← Matrix.mul_assoc, ← a2, Matrix.mul_assoc, ← a1, ← Matrix.mul_assoc, e3, Matrix.one_mul])
  have hBB' : B * B' = 1 := canc _ (by
    rw [← Matrix.mul_assoc, ← a1, Matrix.mul_assoc, ← a2, ← Matrix.mul_assoc, e4, Matrix.one_mul])
  exact ⟨⟨B, B', hBB', hB'B⟩, trivial, a1⟩

variable {X Y : Matrix (Fin n) (Fin r) E} {l d : ℕ}

def bIdx (h : l + d ≤ r) (a : Fin d) : Fin r := ⟨l + a.val, by omega⟩

/- English proof (translation)
Introduce `a b e` and use `Fin.ext (by have := congrArg Fin.val e; simp only [bIdx] at this; omega)`.
-/
theorem bIdx_injective (h : l + d ≤ r) : Function.Injective (bIdx h) := fun a b e =>
  Fin.ext (by have := congrArg Fin.val e; simp only [bIdx] at this; omega)

/- English proof (translation)
Use extensionality with `i`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : i.val ≤ k.val` using `h1`. Establish `hli : l ≤ i.val`.

Break down `hl with rfl | ⟨p, hp, e⟩` into its components or cases. Use linear arithmetic over natural numbers and integers. Establish `: p.val < i.val` using `h2 p hp (Fin.lt_def.2 (by omega))`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨⟨i.val - l, by omega⟩, Fin.ext (by simp only [bIdx]; omega)⟩`.

Introduce and unpack `⟨a, rfl⟩`. Establish `ha` using `a.2`. Use `⟨Fin.le_def.2 (by simp only [bIdx]; omega), fun t ht htk => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `hc' : ¬ (t.val < l + a.val)` using `hc`.

Establish `htk' : t.val < k.val` using `htk`. Conclude with `hT t (by omega) (by omega) ht`.
-/
theorem block_eq {T : Finset (Fin r)} {k : Fin r} (h : l + d ≤ r) (hk : k.val + 1 = l + d) (hd : 1 ≤ d)
    (hT : ∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ T) (hl : l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) :
    block T k = Set.range (bIdx h) := by
  ext i
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : i.val ≤ k.val := h1
    have hli : l ≤ i.val := by
      rcases hl with rfl | ⟨p, hp, e⟩
      · omega
      · have : p.val < i.val := h2 p hp (Fin.lt_def.2 (by omega))
        omega
    exact ⟨⟨i.val - l, by omega⟩, Fin.ext (by simp only [bIdx]; omega)⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    refine ⟨Fin.le_def.2 (by simp only [bIdx]; omega), fun t ht htk => ?_⟩
    by_contra hc
    have hc' : ¬ (t.val < l + a.val) := hc
    have htk' : t.val < k.val := htk
    exact hT t (by omega) (by omega) ht

/- English proof (translation)
Use extensionality with `p q`. Establish `hD : ∀ i, (Z * Comm.blockDiag (E` using `E) (Set.range (bIdx h))) p i = Z p i * (Set.range (bIdx h)).indicator 1 i := fun i => by rw [Comm.blockDiag, Matrix.mul_diagonal]`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Use `symm`. Use `Fintype.sum_of_injective (bIdx h) (bIdx_injective h) _ _ (fun i hi => ?_) (fun a => ?_)` and prove the remaining obligations.

Rewrite using `[hD, Set.indicator_of_notMem hi]`. Simplify using the standard rewrite rules. Rewrite using `[hD, Set.indicator_of_mem (Set.mem_range_self a)]`. Express the relevant statement in the definitionally equal form `Z p (bIdx h a) * N (bIdx h a) q = _`. Simplify using the standard rewrite rules.
-/
theorem mul_blockDiag (h : l + d ≤ r) (Z : Matrix (Fin n) (Fin r) E) (N : Matrix (Fin r) (Fin n) E) :
    Z * Comm.blockDiag (E := E) (Set.range (bIdx h)) * N = GlobalTheory.BlockForms.blkCols h Z * N.submatrix (bIdx h) id := by
  ext p q
  have hD : ∀ i, (Z * Comm.blockDiag (E := E) (Set.range (bIdx h))) p i = Z p i * (Set.range (bIdx h)).indicator 1 i :=
    fun i => by rw [Comm.blockDiag, Matrix.mul_diagonal]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (bIdx h) (bIdx_injective h) _ _ (fun i hi => ?_) (fun a => ?_)
  · rw [hD, Set.indicator_of_notMem hi]
    simp
  · rw [hD, Set.indicator_of_mem (Set.mem_range_self a)]
    change Z p (bIdx h a) * N (bIdx h a) q = _
    simp

/- English proof (translation)
Use `ext`. Both sides reduce to the same expression.
-/
theorem blk_adj (h : l + d ≤ r) (Z : Matrix (Fin n) (Fin r) E) :
    (Formalism.UG.cT (σ : E →+* E) Z * J).submatrix (bIdx h) id = Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J := by
  ext; rfl

/- English proof (translation)
Rewrite using `[frameProj, mul_blockDiag, mul_blockDiag, blk_adj, blk_adj]`.
-/
theorem frameProj_eq (h : l + d ≤ r) :
    frameProj σ J X Y (Set.range (bIdx h)) =
      GlobalTheory.BlockForms.blkCols h X * (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) +
        GlobalTheory.BlockForms.blkCols h Y * (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J) := by
  rw [frameProj, mul_blockDiag, mul_blockDiag, blk_adj, blk_adj]

/- English proof (translation)
Use `ext`. Both sides reduce to the same expression.
-/
theorem blk_pair (h : l + d ≤ r) (Z W : Matrix (Fin n) (Fin r) E) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J * GlobalTheory.BlockForms.blkCols h W =
      (Formalism.UG.cT (σ : E →+* E) Z * J * W).submatrix (bIdx h) (bIdx h) := by
  ext; rfl

variable (σ J X Y) in

def IsBlockPoint (h : l + d ≤ r) (u : GAd σ J) : Prop :=
  ∃ P Q : Matrix (Fin d) (Fin d) (AF F ⊗[F] E), (GlobalTheory.AdelicU.matHom (AF F) σ J u).1 =
    1 + adMat F (GlobalTheory.BlockForms.blkCols h X) * P * adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) +
      adMat F (GlobalTheory.BlockForms.blkCols h Y) * Q * adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J)

/- English proof (translation)
Rewrite using `[← e]`. Conclude with `(Matrix.map_mul).symm`.
-/
theorem ad_rel {Z W : Matrix (Fin n) (Fin r) E} {c : Matrix (Fin r) (Fin r) E}
    (e : Formalism.UG.cT (σ : E →+* E) Z * J * W = c) :
    adMat F (Formalism.UG.cT (σ : E →+* E) Z * J) * adMat F W = c.map (inclR (F := F) (AF F)) := by
  rw [← e]
  exact (Matrix.map_mul).symm

/- English proof (translation)
The claim follows from `Matrix.map_zero _ (map_zero _)`.
-/
theorem zero_map : (0 : Matrix (Fin r) (Fin r) E).map (inclR (F := F) (AF F)) = 0 := Matrix.map_zero _ (map_zero _)

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem one_map : (1 : Matrix (Fin r) (Fin r) E).map (inclR (F := F) (AF F)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Rewrite using `[← blk_pair]`. Conclude with `(Matrix.map_mul).symm`.
-/
theorem ad_blk (h : l + d ≤ r) (Z W : Matrix (Fin n) (Fin r) E) :
    adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J) * adMat F (GlobalTheory.BlockForms.blkCols h W) =
      ((Formalism.UG.cT (σ : E →+* E) Z * J * W).submatrix (bIdx h) (bIdx h)).map (inclR (F := F) (AF F)) := by
  rw [← blk_pair]
  exact (Matrix.map_mul).symm

/- English proof (translation)
Rewrite using `[ad_blk, e]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem ad_blk_zero (h : l + d ≤ r) {Z W : Matrix (Fin n) (Fin r) E} (e : Formalism.UG.cT (σ : E →+* E) Z * J * W = 0) :
    adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J) * adMat F (GlobalTheory.BlockForms.blkCols h W) = 0 := by
  rw [ad_blk, e]
  ext i j
  simp

/- English proof (translation)
Rewrite using `[ad_blk, e, Matrix.submatrix_one _ (bIdx_injective h)]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem ad_blk_one (h : l + d ≤ r) {Z W : Matrix (Fin n) (Fin r) E} (e : Formalism.UG.cT (σ : E →+* E) Z * J * W = 1) :
    adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J) * adMat F (GlobalTheory.BlockForms.blkCols h W) = 1 := by
  rw [ad_blk, e, Matrix.submatrix_one _ (bIdx_injective h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Set `e' : Fin d → Fin (k.val + 1)` to `fun a => ⟨l + a.val, by omega⟩`. Establish `h1 : g * adMat F (GlobalTheory.BlockForms.blkCols h Z) = (adMat F (initCols Z k) * B).submatrix id e'`. Rewrite using `[← e]`. Use `ext`. Both sides reduce to the same expression.

Establish `h2 : adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J) * adMat F (initCols Z k) = 0`. Establish `: Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J * initCols Z k = 0`. Use extensionality with `a b`. Conclude with `congrFun (congrFun hZ (bIdx h a)) (b.castLE k.2)`. Rewrite using `[← Matrix.map_mul, this]`.

Conclude with `Matrix.map_zero _ (map_zero _)`. Establish `h3 : (adMat F (initCols Z k) * B).submatrix id e' = adMat F (initCols Z k) * B.submatrix id e'`. Use `ext`. Both sides reduce to the same expression. Rewrite using `[h1, h3, ← Matrix.mul_assoc, h2, Matrix.zero_mul]`.
-/
theorem block_kills (h : l + d ≤ r) {k : Fin r} (hk : k.val + 1 = l + d) {Z : Matrix (Fin n) (Fin r) E}
    (hZ : Formalism.UG.cT (σ : E →+* E) Z * J * Z = 0) {g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    {B : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) (AF F ⊗[F] E)}
    (e : g * adMat F (initCols Z k) = adMat F (initCols Z k) * B) :
    adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J) * (g * adMat F (GlobalTheory.BlockForms.blkCols h Z)) = 0 := by
  let e' : Fin d → Fin (k.val + 1) := fun a => ⟨l + a.val, by omega⟩
  have h1 : g * adMat F (GlobalTheory.BlockForms.blkCols h Z) = (adMat F (initCols Z k) * B).submatrix id e' := by
    rw [← e]
    ext
    rfl
  have h2 : adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J) * adMat F (initCols Z k) = 0 := by
    have : Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Z) * J * initCols Z k = 0 := by
      ext a b
      exact congrFun (congrFun hZ (bIdx h a)) (b.castLE k.2)
    rw [← Matrix.map_mul, this]
    exact Matrix.map_zero _ (map_zero _)
  have h3 : (adMat F (initCols Z k) * B).submatrix id e' = adMat F (initCols Z k) * B.submatrix id e' := by
    ext
    rfl
  rw [h1, h3, ← Matrix.mul_assoc, h2, Matrix.zero_mul]

variable (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include hCM hJ hW

/- English proof (translation)
Take `⟨P, Q, e⟩` from `hu`. Rewrite using `[e]`. Conclude with `GlobalTheory.BlockForms.Norm.blk_span (Y := adMat F Y) (K := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)) (L := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) (bIdx h) P Q ((ad_rel hW.xx).trans zero_map) ((ad_rel (yx hCM hJ hW)).trans one_map) hI hy`.
-/
theorem stableX {h : l + d ≤ r} {u : GAd σ J} (hu : IsBlockPoint σ J X Y h u) {I : Set (Fin r)}
    (hI : (∀ a, bIdx h a ∈ I) ∨ ∀ a, bIdx h a ∉ I) {y} (hy : y ∈ colSpan F X I) :
    (GlobalTheory.AdelicU.matHom (AF F) σ J u).1 *ᵥ y ∈ colSpan F X I := by
  obtain ⟨P, Q, e⟩ := hu
  rw [e]
  exact GlobalTheory.BlockForms.Norm.blk_span (Y := adMat F Y) (K := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J))
    (L := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) (bIdx h) P Q ((ad_rel hW.xx).trans zero_map)
    ((ad_rel (yx hCM hJ hW)).trans one_map) hI hy

/- English proof (translation)
Take `⟨P, Q, e⟩` from `hu`. Rewrite using `[e, add_right_comm]`. Conclude with `GlobalTheory.BlockForms.Norm.blk_span (X := adMat F Y) (Y := adMat F X) (K := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) (L := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)) (bIdx h) Q P ((ad_rel hW.yy).trans zero_map) ((ad_rel hW.xy).trans one_map) hI hy`.
-/
theorem stableY {h : l + d ≤ r} {u : GAd σ J} (hu : IsBlockPoint σ J X Y h u) {I : Set (Fin r)}
    (hI : (∀ a, bIdx h a ∈ I) ∨ ∀ a, bIdx h a ∉ I) {y} (hy : y ∈ colSpan F Y I) :
    (GlobalTheory.AdelicU.matHom (AF F) σ J u).1 *ᵥ y ∈ colSpan F Y I := by
  obtain ⟨P, Q, e⟩ := hu
  rw [e, add_right_comm]
  exact GlobalTheory.BlockForms.Norm.blk_span (X := adMat F Y) (Y := adMat F X) (K := adMat F (Formalism.UG.cT (σ : E →+* E) X * J))
    (L := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)) (bIdx h) Q P ((ad_rel hW.yy).trans zero_map)
    ((ad_rel hW.xy).trans one_map) hI hy

omit hCM hJ hW in
/- English proof (translation)
Take `⟨P, Q, e⟩` from `hu`. Simplify using `only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hx hy`. Establish `z1 : (fun a => (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ y) (bIdx h a)) = 0`. Use function extensionality and compare the values at `fun a => hy _ ⟨a, rfl⟩`. Establish `z2 : (fun a => (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) (bIdx h a)) = 0`.

Use function extensionality and compare the values at `fun a => hx _ ⟨a, rfl⟩`. Rewrite using `[e]`. Use `(GlobalTheory.BlockForms.Norm.blk_mulVec (X := adMat F X) (Y := adMat F Y) (K := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)) (L := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) (bIdx h) P Q y).trans ?_` and prove the remaining obligations. Rewrite using `[z1, z2]`. Simplify using the standard rewrite rules.
-/
theorem fixes {h : l + d ≤ r} {u : GAd σ J} (hu : IsBlockPoint σ J X Y h u) {y}
    (hx : y ∈ colPerp σ J X (Set.range (bIdx h))) (hy : y ∈ colPerp σ J Y (Set.range (bIdx h))) :
    (GlobalTheory.AdelicU.matHom (AF F) σ J u).1 *ᵥ y = y := by
  obtain ⟨P, Q, e⟩ := hu
  simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hx hy
  have z1 : (fun a => (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ y) (bIdx h a)) = 0 :=
    funext fun a => hy _ ⟨a, rfl⟩
  have z2 : (fun a => (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) (bIdx h a)) = 0 :=
    funext fun a => hx _ ⟨a, rfl⟩
  rw [e]
  refine (GlobalTheory.BlockForms.Norm.blk_mulVec (X := adMat F X) (Y := adMat F Y) (K := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J))
    (L := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) (bIdx h) P Q y).trans ?_
  rw [z1, z2]
  simp

/- English proof (translation)
Use `Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun k' => Subgroup.mem_iInf.2 fun hk' => Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hI : (∀ a, bIdx h a ∈ {i | i ≤ k'}) ∨ ∀ a, bIdx h a ∉ {i | i ≤ k'}`. Break down `hT k' hk' with c | c` into its components or cases. Conclude with `Or.inr fun a ha => by`. Establish `: l + a.val ≤ k'.val` using `ha`.

Use linear arithmetic over natural numbers and integers. Conclude with `Or.inl fun a => by`. Use `a.2` as an intermediate fact. Conclude with `Fin.le_def.2 (by simp only [bIdx]; omega)`. Use `mem_frameStab_of_stable (L := (Formalism.UG.cT (σ : E →+* E) Y * J).submatrix (Fin.castLE k'.2) id) (Matrix.ext fun i j => (congrFun (congrFun (yx hCM hJ hW) (i.castLE k'.2)) (j.castLE k'.2)).trans (by simp [Matrix.one_apply])) (fun y hy => stableX hCM hJ hW hu hI hy) (fun y hy = …` and prove the remaining obligations.

Establish `hI : (∀ a, bIdx h a ∈ {i | i ≤ k'}) ∨ ∀ a, bIdx h a ∉ {i | i ≤ k'}`. Break down `hT k' hk' with c | c` into its components or cases. Conclude with `Or.inr fun a ha => by`. Establish `: l + a.val ≤ k'.val` using `ha`. Use linear arithmetic over natural numbers and integers.

Conclude with `Or.inl fun a => by`. Use `a.2` as an intermediate fact. Conclude with `Fin.le_def.2 (by simp only [bIdx]; omega)`. Use `mem_frameStab_of_stable (L := (Formalism.UG.cT (σ : E →+* E) X * J).submatrix (Fin.castLE k'.2) id) (Matrix.ext fun i j => (congrFun (congrFun hW.xy (i.castLE k'.2)) (j.castLE k'.2)).trans (by simp [Matrix.one_apply])) (fun y hy => stableY hCM hJ hW hu hI hy) (fun y hy => stableY …` and prove the remaining obligations. Introduce `y hy`.

Rewrite `hy` using `[hB]`. Conclude with `fixes hu (Submodule.mem_inf.1 hy).1 (Submodule.mem_inf.1 hy).2`.
-/
theorem mem_glPart {h : l + d ≤ r} {T : Finset (Fin r)} {k : Fin r} (hB : block T k = Set.range (bIdx h))
    (hT : ∀ k' ∈ T, k'.val + 1 ≤ l ∨ l + d ≤ k'.val + 1) {u : GAd σ J} (hu : IsBlockPoint σ J X Y h u)
    (hu' : IsBlockPoint σ J X Y h u⁻¹) : u ∈ glPart σ J X Y T k := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun k' => Subgroup.mem_iInf.2 fun hk' => Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · have hI : (∀ a, bIdx h a ∈ {i | i ≤ k'}) ∨ ∀ a, bIdx h a ∉ {i | i ≤ k'} := by
      rcases hT k' hk' with c | c
      · exact Or.inr fun a ha => by
          have : l + a.val ≤ k'.val := ha
          omega
      · exact Or.inl fun a => by
          have := a.2
          exact Fin.le_def.2 (by simp only [bIdx]; omega)
    refine mem_frameStab_of_stable (L := (Formalism.UG.cT (σ : E →+* E) Y * J).submatrix (Fin.castLE k'.2) id)
      (Matrix.ext fun i j => (congrFun (congrFun (yx hCM hJ hW) (i.castLE k'.2)) (j.castLE k'.2)).trans (by simp [Matrix.one_apply]))
      (fun y hy => stableX hCM hJ hW hu hI hy) (fun y hy => stableX hCM hJ hW hu' hI hy)
  · have hI : (∀ a, bIdx h a ∈ {i | i ≤ k'}) ∨ ∀ a, bIdx h a ∉ {i | i ≤ k'} := by
      rcases hT k' hk' with c | c
      · exact Or.inr fun a ha => by
          have : l + a.val ≤ k'.val := ha
          omega
      · exact Or.inl fun a => by
          have := a.2
          exact Fin.le_def.2 (by simp only [bIdx]; omega)
    refine mem_frameStab_of_stable (L := (Formalism.UG.cT (σ : E →+* E) X * J).submatrix (Fin.castLE k'.2) id)
      (Matrix.ext fun i j => (congrFun (congrFun hW.xy (i.castLE k'.2)) (j.castLE k'.2)).trans (by simp [Matrix.one_apply]))
      (fun y hy => stableY hCM hJ hW hu hI hy) (fun y hy => stableY hCM hJ hW hu' hI hy)
  · intro y hy
    rw [hB] at hy
    exact fixes hu (Submodule.mem_inf.1 hy).1 (Submodule.mem_inf.1 hy).2

/- English proof (translation)
Take `⟨hlevi, hfix⟩` from `Subgroup.mem_inf.1 hm`. Establish `hst` using `Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hlevi k) hkT)`. Take `⟨BX, -, eBX⟩` from `hst.1`. Take `⟨BY, -, eBY⟩` from `hst.2`. Establish `hgx : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (GlobalTheory.AdelicU.matHom (AF F) σ J m).1 * JR (F` using `F) (AF F) J * (GlobalTheory.AdelicU.matHom (AF F) σ J m).1 = JR (F := F) (AF F) J := (show HR (AF F) σ J from m).2`.

Establish `hJR : JR (F` using `F) (AF F) J = J.map (inclR (F := F) (AF F)) := rfl`. Establish `hJu : IsUnit (JR (F` using `F) (AF F) J).det := by`. Rewrite using `[hJR, show (J.map (inclR (F := F) (E := E) (AF F))).det = inclR (F := F) (E := E) (AF F) J.det from (RingHom.map_det (inclR (F := F) (E := E) (AF F)) J).symm]`. Conclude with `(isUnit_iff_ne_zero.2 hJ.2).map (inclR (F := F) (E := E) (AF F))`. Establish `hP' : (frameProj σ J X Y (block T k)).map (inclR (F` using `F) (AF F)) = adMat F (GlobalTheory.BlockForms.blkCols h X) * adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) + adMat F (GlobalTheory.BlockForms.blkCols h Y) * adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J) := by`.

Rewrite using `[hB, frameProj_eq]`. Use `(Matrix.map_add _ (map_add (inclR (F := F) (E := E) (AF F))) _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg₂ (· + ·) Matrix.map_mul Matrix.map_mul`. Establish `hPs : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) ((frameProj σ J X Y (block T k)).map (inclR (F` using `F) (AF F))) * JR (F := F) (AF F) J = JR (F := F) (AF F) J * (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) := by`. Rewrite using `[Comm.cT_map, hJR, ← Matrix.map_mul, ← Matrix.map_mul, frameProj_selfAdj hCM hJ]`.

Establish `hQ : (GlobalTheory.AdelicU.matHom (AF F) σ J m).1 * (1 - (frameProj σ J X Y (block T k)).map (inclR (F` using `F) (AF F))) = 1 - (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) := by`. Establish `hQm : 1 - (frameProj σ J X Y (block T k)).map (inclR (F` using `F) (AF F)) = (1 - frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) := by`. Rewrite using `[Matrix.map_sub _ (map_sub (inclR (F := F) (E := E) (AF F))), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[hQm]`. Use `fix_of_perp hfix _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_sub, Matrix.mul_one, xJ_frameProj hW]`. Conclude with `blockDiag_cancel _`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, yJ_frameProj hCM hJ hW]`. Conclude with `blockDiag_cancel _`. Rewrite `hPs`, `hQ` using `[hP']`.

Establish `eX : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (GlobalTheory.BlockForms.blkCols h X)) * JR (F` using `F) (AF F) J = adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J) := by`. Rewrite using `[Comm.cT_map, hJR]`. Conclude with `(Matrix.map_mul).symm`. Establish `eY : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (GlobalTheory.BlockForms.blkCols h Y)) * JR (F` using `F) (AF F) J = adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) := by`. Rewrite using `[Comm.cT_map, hJR]`.

Conclude with `(Matrix.map_mul).symm`. Take `⟨f1, f2, f3⟩` from `block_form hJu hgx eX eY (ad_blk_zero h hW.xx) (ad_blk_one h hW.xy) (ad_blk_one h (yx hCM hJ hW)) (ad_blk_zero h hW.yy) hPs hQ (block_kills h hk hW.xx eBX) (block_kills h hk hW.yy eBY)`. Generalize the expression as in `adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) * ((GlobalTheory.AdelicU.matHom (AF F) σ J m).1 * adMat F (GlobalTheory.BlockForms.blkCols h X)) = A at f1 f2 f3`. Generalize the expression as in `adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J) * ((GlobalTheory.AdelicU.matHom (AF F) σ J m).1 * adMat F (GlobalTheory.BlockForms.blkCols h Y)) = A' at f1 f2 f3`. Set `Au : GL (Fin d) (AF F ⊗[F] E)` to `⟨A, Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) A', mul_eq_one_comm.1 f3, f3⟩`.

Establish `i0 : A * (Au⁻¹).1 = 1` using `Units.mul_inv Au`. Establish `i1 : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Au⁻¹).1 * Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) A = 1`. Rewrite using `[← Formalism.UG.cT_mul, i0, Formalism.UG.cT_one]`. Establish `i2 : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Au⁻¹).1 = A'`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[f2, Matrix.mul_one]`. Use `_ = A' := by rw [← Matrix.mul_assoc, i1, Matrix.one_mul]`. Conclude with `⟨Au, by rw [i2]; exact f1⟩`.
-/
theorem exists_of_mem {h : l + d ≤ r} {T : Finset (Fin r)} {k : Fin r} (hkT : k ∈ T) (hk : k.val + 1 = l + d)
    (hB : block T k = Set.range (bIdx h)) {m : GAd σ J} (hm : m ∈ glPart σ J X Y T k) :
    ∃ A : GL (Fin d) (AF F ⊗[F] E), (GlobalTheory.AdelicU.matHom (AF F) σ J m).1 =
      1 + adMat F (GlobalTheory.BlockForms.blkCols h X) * (A.1 - 1) * adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) +
        adMat F (GlobalTheory.BlockForms.blkCols h Y) * (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (A⁻¹).1 - 1) *
          adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J) := by
  obtain ⟨hlevi, hfix⟩ := Subgroup.mem_inf.1 hm
  have hst := Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hlevi k) hkT)
  obtain ⟨BX, -, eBX⟩ := hst.1
  obtain ⟨BY, -, eBY⟩ := hst.2
  have hgx : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (GlobalTheory.AdelicU.matHom (AF F) σ J m).1 * JR (F := F) (AF F) J * (GlobalTheory.AdelicU.matHom (AF F) σ J m).1 = JR (F := F) (AF F) J :=
    (show HR (AF F) σ J from m).2
  have hJR : JR (F := F) (AF F) J = J.map (inclR (F := F) (AF F)) := rfl
  have hJu : IsUnit (JR (F := F) (AF F) J).det := by
    rw [hJR, show (J.map (inclR (F := F) (E := E) (AF F))).det = inclR (F := F) (E := E) (AF F) J.det from
      (RingHom.map_det (inclR (F := F) (E := E) (AF F)) J).symm]
    exact (isUnit_iff_ne_zero.2 hJ.2).map (inclR (F := F) (E := E) (AF F))
  have hP' : (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) =
      adMat F (GlobalTheory.BlockForms.blkCols h X) * adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) +
        adMat F (GlobalTheory.BlockForms.blkCols h Y) * adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J) := by
    rw [hB, frameProj_eq]
    refine (Matrix.map_add _ (map_add (inclR (F := F) (E := E) (AF F))) _ _).trans ?_
    exact congrArg₂ (· + ·) Matrix.map_mul Matrix.map_mul
  have hPs : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) ((frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F))) *
      JR (F := F) (AF F) J = JR (F := F) (AF F) J * (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) := by
    rw [Comm.cT_map, hJR, ← Matrix.map_mul, ← Matrix.map_mul, frameProj_selfAdj hCM hJ]
  have hQ : (GlobalTheory.AdelicU.matHom (AF F) σ J m).1 * (1 - (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F))) =
      1 - (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) := by
    have hQm : 1 - (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) =
        (1 - frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) := by
      rw [Matrix.map_sub _ (map_sub (inclR (F := F) (E := E) (AF F))), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hQm]
    refine fix_of_perp hfix _ ?_ ?_
    · rw [Matrix.mul_sub, Matrix.mul_one, xJ_frameProj hW]
      exact blockDiag_cancel _
    · rw [Matrix.mul_sub, Matrix.mul_one, yJ_frameProj hCM hJ hW]
      exact blockDiag_cancel _
  rw [hP'] at hPs hQ
  have eX : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (GlobalTheory.BlockForms.blkCols h X)) * JR (F := F) (AF F) J =
      adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J) := by
    rw [Comm.cT_map, hJR]
    exact (Matrix.map_mul).symm
  have eY : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (GlobalTheory.BlockForms.blkCols h Y)) * JR (F := F) (AF F) J =
      adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) := by
    rw [Comm.cT_map, hJR]
    exact (Matrix.map_mul).symm
  obtain ⟨f1, f2, f3⟩ := block_form hJu hgx eX eY (ad_blk_zero h hW.xx) (ad_blk_one h hW.xy)
    (ad_blk_one h (yx hCM hJ hW)) (ad_blk_zero h hW.yy) hPs hQ (block_kills h hk hW.xx eBX) (block_kills h hk hW.yy eBY)
  generalize adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) *
    ((GlobalTheory.AdelicU.matHom (AF F) σ J m).1 * adMat F (GlobalTheory.BlockForms.blkCols h X)) = A at f1 f2 f3
  generalize adMat F (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J) *
    ((GlobalTheory.AdelicU.matHom (AF F) σ J m).1 * adMat F (GlobalTheory.BlockForms.blkCols h Y)) = A' at f1 f2 f3
  let Au : GL (Fin d) (AF F ⊗[F] E) := ⟨A, Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) A', mul_eq_one_comm.1 f3, f3⟩
  have i0 : A * (Au⁻¹).1 = 1 := Units.mul_inv Au
  have i1 : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Au⁻¹).1 * Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) A = 1 := by
    rw [← Formalism.UG.cT_mul, i0, Formalism.UG.cT_one]
  have i2 : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Au⁻¹).1 = A' := by
    calc Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Au⁻¹).1
        = Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Au⁻¹).1 * (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) A * A') := by
          rw [f2, Matrix.mul_one]
      _ = A' := by rw [← Matrix.mul_assoc, i1, Matrix.one_mul]
  exact ⟨Au, by rw [i2]; exact f1⟩

end Adelic

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hCM n J hJ r X Y hW T k hkT l d h ι hemb hk hd hT hl`. Take `⟨Φ, jj, _, _, _, _, hι⟩` from `hemb`. Establish `hB : block T k = Set.range (bIdx h)` using `block_eq h hk hd hT hl`. Establish `hT1 : ∀ k' ∈ T, k'.val + 1 ≤ l ∨ l + d ≤ k'.val + 1` using `fun k' hk' => by`. Assume the negation of the conclusion as `c`.

Use `push_neg at c`. Conclude with `hT k' (by omega) (by omega) hk'`. Establish `hblk : ∀ g, IsBlockPoint σ J X Y h (ι g)` using `fun g => ⟨_, _, hι g⟩`. Use `le_antisymm (fun m hm => ?_) ?_` and prove the remaining obligations. Take `⟨A, hA⟩` from `exists_of_mem hCM hJ hW hkT hk hB hm`.

Establish `hmap : ∀ C : GL (Fin d) (AF F ⊗[F] E), (Matrix.GeneralLinearGroup.map (Φ : AF F ⊗[F] E →+* _) C).1.map Φ.symm = C.1` using `fun C => Matrix.ext fun i j => Φ.symm_apply_apply _`. Use `⟨Matrix.GeneralLinearGroup.map (Φ : AF F ⊗[F] E →+* _) A, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.AdelicU.matHom_injective (AF F) σ J (Units.ext ?_)` and prove the remaining obligations. Rewrite using `[hι, hA, ← map_inv, hmap, hmap]`. Introduce and unpack `_ ⟨g, rfl⟩`.

Conclude with `mem_glPart hCM hJ hW hB hT1 (hblk g) (map_inv ι g ▸ hblk g⁻¹)`.
-/
theorem glPart_eq_range : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (k : Fin r), k ∈ T → ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J),
      GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι → k.val + 1 = l + d → 1 ≤ d →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ T) → (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) →
      glPart σ J X Y T k = ι.range := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r X Y hW T k hkT l d h ι hemb hk hd hT hl
  obtain ⟨Φ, jj, _, _, _, _, hι⟩ := hemb
  have hB : block T k = Set.range (bIdx h) := block_eq h hk hd hT hl
  have hT1 : ∀ k' ∈ T, k'.val + 1 ≤ l ∨ l + d ≤ k'.val + 1 := fun k' hk' => by
    by_contra c
    push_neg at c
    exact hT k' (by omega) (by omega) hk'
  have hblk : ∀ g, IsBlockPoint σ J X Y h (ι g) := fun g => ⟨_, _, hι g⟩
  refine le_antisymm (fun m hm => ?_) ?_
  · obtain ⟨A, hA⟩ := exists_of_mem hCM hJ hW hkT hk hB hm
    have hmap : ∀ C : GL (Fin d) (AF F ⊗[F] E),
        (Matrix.GeneralLinearGroup.map (Φ : AF F ⊗[F] E →+* _) C).1.map Φ.symm = C.1 := fun C =>
      Matrix.ext fun i j => Φ.symm_apply_apply _
    refine ⟨Matrix.GeneralLinearGroup.map (Φ : AF F ⊗[F] E →+* _) A, ?_⟩
    refine GlobalTheory.AdelicU.matHom_injective (AF F) σ J (Units.ext ?_)
    rw [hι, hA, ← map_inv, hmap, hmap]
  · rintro _ ⟨g, rfl⟩
    exact mem_glPart hCM hJ hW hB hT1 (hblk g) (map_inv ι g ▸ hblk g⁻¹)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange
