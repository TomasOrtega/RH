import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.parahoric_le_integral_gl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, s, -, h⟩`. Establish `hs : ∀ b, s b = 0`. Introduce `b`. Establish `h1` using `congrFun h (Fin.natAdd n b)`.

Establish `hq` using `Proof.NormalFormAtPrime.qOf_ne_zero P`. Establish `h2 : ∀ (y : Fin n → E), Loc.inX E n c y (Fin.natAdd n b) = 0` using `fun y => by`. Rewrite using `[inX_apply, dif_neg (by simp)]`. Establish `h3 : ∀ i : Fin c, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen (qOf P) n c e z i (Fin.natAdd n b) = if b = i then ((qOf P : E) ^ e i) else 0`. Introduce `i`.

Unfold `IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen`. Rewrite using `[Pi.smul_apply, Pi.add_apply]`. Establish `h4 : (if i.1 = 0 then Loc.inX E n c z else 0 : Sp E (n + c)) (Fin.natAdd n b) = 0` using `by split_ifs`. Conclude with `h2 z`. Both sides reduce to the same expression.

Rewrite using `[h4]`. Simplify using `[Loc.eN, Fin.val_inj]`. Rewrite `h1` using `[Pi.add_apply, h2, h2, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, h3, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add] at h1`. Conclude with `(mul_eq_zero.1 h1.symm).resolve_right (zpow_ne_zero _ hq)`.

Simplify using `only [hs, zero_smul, Finset.sum_const_zero, add_zero] at h`. Rewrite using `[inX_injective h]` and apply the resulting hypothesis. Introduce `hx`. Conclude with `⟨x, hx, 0, fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P, by simp⟩`.
-/
theorem inX_mem_nfLat_iff {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ)
    (e : Fin c → ℤ) (z : Sp E n) (x : Sp E n) :
    Loc.inX E n c x ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z ↔ x ∈ stdAt E n P := by
  constructor
  · rintro ⟨l, hl, s, -, h⟩
    have hs : ∀ b, s b = 0 := by
      intro b
      have h1 := congrFun h (Fin.natAdd n b)
      have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
      have h2 : ∀ (y : Fin n → E), Loc.inX E n c y (Fin.natAdd n b) = 0 := fun y => by
        rw [inX_apply, dif_neg (by simp)]
      have h3 : ∀ i : Fin c, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen (qOf P) n c e z i (Fin.natAdd n b) =
          if b = i then ((qOf P : E) ^ e i) else 0 := by
        intro i
        unfold IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen
        rw [Pi.smul_apply, Pi.add_apply]
        have h4 : (if i.1 = 0 then Loc.inX E n c z else 0 : Sp E (n + c)) (Fin.natAdd n b) = 0 := by
          split_ifs
          · exact h2 z
          · rfl
        rw [h4]
        simp [Loc.eN, Fin.val_inj]
      rw [Pi.add_apply, h2, h2, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, h3, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right (zpow_ne_zero _ hq)
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at h
    rwa [inX_injective h]
  · intro hx
    exact ⟨x, hx, 0, fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P, by simp⟩

/- English proof (translation)
Introduce and unpack `X Pr R sharp j P hP h ⟨e, z, -, -, hnf⟩ g ⟨r, ⟨-, hr⟩, hrg⟩ x`. Establish `hJ : h⁻¹ * r * h ∈ Jat (Pr` using `Pr) (R := R) sharp j P := by`. Use `Subgroup.mem_comap.1 hr` as an intermediate fact. Simplify using `using this`. Unfold `Jat at hJ`.

Rewrite `hJ` using `[if_neg hP]`. Establish `hk` using `hJ.1`. Establish `key : ∀ y, y ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z ↔ h⁻¹ y ∈ stdAt X.E _ P`. Introduce `y`. Rewrite using `[← hnf, mem_stdAt_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Establish `: h⁻¹ (h w) = w` using `h.symm_apply_apply w`. Rewrite using `[this]`. Conclude with `(IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP w).1 hw`.

Introduce `hy`. Conclude with `⟨h⁻¹ y, (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP _).2 hy, h.apply_symm_apply y⟩`. Rewrite using `[← inX_mem_nfLat_iff P _ (cOf R j) e z, ← inX_mem_nfLat_iff P _ (cOf R j) e z, ← hrg, key, key, ← hk (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x))]`. Establish `: (h⁻¹ * r * h) (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x)) = h⁻¹ (r (Loc.inX X.E (R.N j) (cOf R j) x))`. Express the relevant statement in the definitionally equal form `h⁻¹ (r (h (h.symm _))) = _`.

Rewrite using `[h.apply_symm_apply]`. Rewrite using `[this]`.
-/
theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  rintro X Pr R sharp j P hP h ⟨e, z, -, -, hnf⟩ g ⟨r, ⟨-, hr⟩, hrg⟩ x
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) sharp j P := by
    have := Subgroup.mem_comap.1 hr
    simpa using this
  unfold Jat at hJ
  rw [if_neg hP] at hJ
  have hk := hJ.1
  have key : ∀ y, y ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z ↔ h⁻¹ y ∈ stdAt X.E _ P := by
    intro y
    rw [← hnf, mem_stdAt_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : h⁻¹ (h w) = w := h.symm_apply_apply w
      rw [this]
      exact (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP w).1 hw
    · intro hy
      exact ⟨h⁻¹ y, (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP _).2 hy, h.apply_symm_apply y⟩
  rw [← inX_mem_nfLat_iff P _ (cOf R j) e z, ← inX_mem_nfLat_iff P _ (cOf R j) e z, ← hrg, key, key,
    ← hk (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x))]
  have : (h⁻¹ * r * h) (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x)) = h⁻¹ (r (Loc.inX X.E (R.N j) (cOf R j) x)) := by
    change h⁻¹ (r (h (h.symm _))) = _
    rw [h.apply_symm_apply]
  rw [this]

end GlobalTheory.Proof.parahoric_le_integral_gl
