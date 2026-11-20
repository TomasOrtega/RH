import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OmpCofLPd

namespace Formalism.FourierDecayAlt.P.TLC

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec_add, dotProduct_add]`.
-/
lemma om_herm_add (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v w u : Fin (2 * r + k + 1) → ℂ) :
    herm H (v + w) u = herm H v u + herm H w u := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
lemma om_herm_smul (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm H (c • v) u = c * herm H v u := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [herm]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, om_herm_add, ih]`.
-/
lemma om_herm_sum {ι : Type*} (s : Finset ι) (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (v : ι → Fin (2 * r + k + 1) → ℂ) (u : Fin (2 * r + k + 1) → ℂ) :
    herm H (∑ i ∈ s, v i) u = ∑ i ∈ s, herm H (v i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, om_herm_add, ih]

/- English proof (translation)
Simplify using `only [herm, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def]`.
-/
lemma om_herm_smul_right (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : ℂ) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm H v (c • u) = conj c * herm H v u := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def]

/- English proof (translation)
Simplify using `only [herm, star_sum, sum_dotProduct]`.
-/
lemma om_herm_sum_right {ι : Type*} (s : Finset ι) (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) (u : ι → Fin (2 * r + k + 1) → ℂ) :
    herm H v (∑ i ∈ s, u i) = ∑ i ∈ s, herm H v (u i) := by
  simp only [herm, star_sum, sum_dotProduct]

/- English proof (translation)
Establish `hH : Hpk k r * Hpk k r = 1` using `(hpkFacts k r).2.1`. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Use `symm`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
lemma om_inv_eq {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r = g⁻¹ := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  symm
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hH]

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r` using `(hpkFacts k r).1`. Unfold `herm`. Rewrite using `[← Complex.star_def, ← star_dotProduct_star, star_star, Matrix.star_mulVec, hH, ← Matrix.dotProduct_mulVec]`.
-/
private lemma herm_swap_eq_zero_of_eq_zero (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w v = conj (herm (Hpk k r) v w) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  unfold herm
  rw [← Complex.star_def, ← star_dotProduct_star, star_star, Matrix.star_mulVec, hH,
    ← Matrix.dotProduct_mulVec]

/- English proof (translation)
Establish `hd : IsUnit g.det` using `Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg`. Establish `hZ : ∀ a b, herm (Hpk k r) (g⁻¹ *ᵥ fvec k r Bs.z a) (fvec k r Bs.z' b) = starRingEnd ℂ (Zhat k r Bs.z Bs.z' g a b)`. Introduce `a b`. Rewrite using `[← Formalism.FourierDecayAlt.P.Qx2.herm_uh hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec, herm_swap_eq_zero_of_eq_zero]`. Both sides reduce to the same expression.

Establish `hM : (Matrix.of fun a b => herm (Hpk k r) (g⁻¹ *ᵥ fvec k r Bs.z a) (fvec k r Bs.z' b)) = (Zhat k r Bs.z Bs.z' g).map (starRingEnd ℂ)`. Use extensionality with `a b`. Simplify using `[hZ]`. Unfold `HermitianLatticeCounting.ExpansionTerms.formalDeterminantVectorOnGroup D.cofL`. Rewrite using `[hM, show ((Zhat k r Bs.z Bs.z' g).map (starRingEnd ℂ)).adjugate = (Zhat k r Bs.z Bs.z' g).adjugate.map (starRingEnd ℂ) from (RingHom.map_adjugate (starRingEnd ℂ) _).symm, Matrix.mulVec_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Both sides reduce to the same expression.
-/
lemma om_N3xM_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : HermitianLatticeCounting.ExpansionTerms.formalDeterminantVectorOnGroup k r Bs.z Bs.z' g = g⁻¹ *ᵥ D.cofL Bs g := by
  have hd : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hZ : ∀ a b, herm (Hpk k r) (g⁻¹ *ᵥ fvec k r Bs.z a) (fvec k r Bs.z' b) =
      starRingEnd ℂ (Zhat k r Bs.z Bs.z' g a b) := by
    intro a b
    rw [← Formalism.FourierDecayAlt.P.Qx2.herm_uh hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec,
      herm_swap_eq_zero_of_eq_zero]
    rfl
  have hM : (Matrix.of fun a b => herm (Hpk k r) (g⁻¹ *ᵥ fvec k r Bs.z a) (fvec k r Bs.z' b)) =
      (Zhat k r Bs.z Bs.z' g).map (starRingEnd ℂ) := by
    ext a b
    simp [hZ]
  unfold HermitianLatticeCounting.ExpansionTerms.formalDeterminantVectorOnGroup D.cofL
  rw [hM, show ((Zhat k r Bs.z Bs.z' g).map (starRingEnd ℂ)).adjugate =
      (Zhat k r Bs.z Bs.z' g).adjugate.map (starRingEnd ℂ) from
      (RingHom.map_adjugate (starRingEnd ℂ) _).symm, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec_smul]
  rfl

/- English proof (translation)
Unfold `herm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`. Establish `: (Hpk k r *ᵥ v) i = 0`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`. Simplify using `[hv j hj.1 hj.2]`.

Establish `: Hpk k r i j = 0`. Unfold `Hpk`. Establish `hij : i ≠ j` using `fun h => hj (h ▸ hi)`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | exact absurd ‹_› (by tauto)`. Simplify using `[this]`.

Simplify using `[this]`. Establish `: w i = 0` using `hw i (by omega)`. Simplify using `[this]`.
-/
lemma om_herm_wb_zero {v w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w)
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) : herm (Hpk k r) v w = 0 := by
  unfold herm
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · have : (Hpk k r *ᵥ v) i = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
      · simp [hv j hj.1 hj.2]
      · have : Hpk k r i j = 0 := by
          unfold Hpk
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          split_ifs <;> first | rfl | omega | exact absurd ‹_› (by tauto)
        simp [this]
    simp [this]
  · have : w i = 0 := hw i (by omega)
    simp [this]

/- English proof (translation)
Unfold `fvec`. Use `split_ifs with hb`. Apply `om_herm_wb_zero hw` to reduce the goal to its premises. Introduce `i hi1 _`. Simplify using `only [bvec, eI, Pi.single_apply]`.

Rewrite using `[if_neg]`. Introduce `h`. Rewrite `hi1` using `[h]`. Simplify using `at hi1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[herm_swap_eq_zero_of_eq_zero, hz'w, map_zero]`.
-/
lemma om_fvec_wb_zero (z' : Fin (2 * r + k + 1) → ℂ) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w)
    (hz'w : herm (Hpk k r) w z' = 0) (b : Fin (r + 1)) : herm (Hpk k r) (fvec k r z' b) w = 0 := by
  unfold fvec
  split_ifs with hb
  · apply om_herm_wb_zero hw
    intro i hi1 _
    simp only [bvec, eI, Pi.single_apply]
    rw [if_neg]
    intro h
    rw [h] at hi1
    simp at hi1
    omega
  · rw [herm_swap_eq_zero_of_eq_zero, hz'w, map_zero]

/- English proof (translation)
Use `show herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ D.cofL Bs g) (B0 j) = _`. Rewrite using `[om_inv_eq hg, ← om_N3xM_eq Bs hg]`. Take `⟨-, -, co, hco⟩` from `HermitianLatticeCounting.P.omega_decomposition k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem Bs.T'_pos.ne' g hg`. Establish `h0 : ∀ b, herm (Hpk k r) (co b • fvec k r Bs.z' b) (B0 j) = 0` using `fun b => by`. Rewrite using `[om_herm_smul, om_fvec_wb_zero Bs.z' (hB.1 j) (hB.2.2 j Bs.z' (by simp)) b, mul_zero]`.

Rewrite using `[hco, om_herm_add, om_herm_sum]`. Simplify using `[h0]`.
-/
lemma om_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (j : Fin k) :
    omC Bs B0 g j = herm (Hpk k r) (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) (B0 j) := by
  show herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ D.cofL Bs g) (B0 j) = _
  rw [om_inv_eq hg, ← om_N3xM_eq Bs hg]
  obtain ⟨-, -, co, hco⟩ := HermitianLatticeCounting.P.omega_decomposition k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem
    Bs.T'_pos.ne' g hg
  have h0 : ∀ b, herm (Hpk k r) (co b • fvec k r Bs.z' b) (B0 j) = 0 := fun b => by
    rw [om_herm_smul, om_fvec_wb_zero Bs.z' (hB.1 j) (hB.2.2 j Bs.z' (by simp)) b, mul_zero]
  rw [hco, om_herm_add, om_herm_sum]
  simp [h0]

/- English proof (translation)
Set `e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ` to `fun i => if h : i.val < k then B0 ⟨i.val, h⟩ else z'`. Establish `he_wb : ∀ i, inWb k r (e i)`. Introduce `i`. Simplify using `only [e]`. Use `split_ifs`.

Use `exacts [hB.1 _, hz']`. Establish `hzz : herm (Hpk k r) z' z' ≠ 0`. Introduce `h0`. Simplify using `[Tz, h0] at hT'`. Establish `horth : ∀ i j, i ≠ j → herm (Hpk k r) (e i) (e j) = 0`.

Introduce `i j hij`. Simplify using `only [e]`. Use `split_ifs with hi hj hj`. Rewrite using `[hB.2.1, if_neg]`. Introduce `h`.

Conclude with `hij (Fin.ext (by simpa using congrArg Fin.val h))`. Conclude with `hB.2.2 _ z' (by simp)`. Rewrite using `[herm_swap_eq_zero_of_eq_zero, hB.2.2 _ z' (by simp), map_zero]`. Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact.

Conclude with `absurd (Fin.ext (by omega)) hij`. Establish `hn : ∀ i, herm (Hpk k r) (e i) (e i) ≠ 0`. Introduce `i`. Simplify using `only [e]`. Use `split_ifs`.

Rewrite using `[hB.2.1, if_pos rfl]`. Conclude with `one_ne_zero`. Conclude with `hzz`. Establish `key : ∀ (b : Fin (k + 1) → ℂ) (j : Fin (k + 1)), herm (Hpk k r) (∑ i, b i • e i) (e j) = b j * herm (Hpk k r) (e j) (e j)`. Introduce `b j`.

Rewrite using `[om_herm_sum, Finset.sum_eq_single j]`. Rewrite using `[om_herm_smul]`. Introduce `i _ hij`. Rewrite using `[om_herm_smul, horth i j hij, mul_zero]`. Simplify using the standard rewrite rules.

Establish `mid : ∀ u : Fin (2 * r + k + 1) → ℂ, inWb k r u → (∀ t : Fin (k + 1), u ⟨r + t.val, by omega⟩ = 0) → u = 0`. Introduce `u hu ht`. Use function extensionality and compare the values at `i`. Use `show u i = 0`. Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`.

Establish `h1 : u ⟨r + (i.val - r), by omega⟩ = 0` using `ht ⟨i.val - r, by omega⟩`. Establish `e1 : (⟨r + (i.val - r), by omega⟩ : Fin (2 * r + k + 1)) = i` using `Fin.ext (by simp; omega)`. Rewrite `h1` using `[e1]`. Then use the resulting hypothesis. Conclude with `hu i (by omega)`. Establish `sum_wb : ∀ b : Fin (k + 1) → ℂ, inWb k r (∑ i, b i • e i)`.

Introduce `b i hi`. Simplify using `[Finset.sum_apply, he_wb _ i hi]`. Set `A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ` to `Matrix.of fun t i => e i ⟨r + t.val, by omega⟩`. Establish `hA : ∀ b t, (A *ᵥ b) t = (∑ i, b i • e i) ⟨r + t.val, by omega⟩`. Introduce `b t`.

Simplify using `[A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Establish `hinj : Function.Injective A.mulVec`. Introduce `b1 b2 h12`. Establish `h0 : A *ᵥ (b1 - b2) = 0` using `by rw [Matrix.mulVec_sub, h12, sub_self]`. Establish `hu : ∑ i, (b1 - b2) i • e i = 0` using `mid _ (sum_wb _) (fun t => by rw [← hA, h0]; rfl)`.

Use function extensionality and compare the values at `j`. Establish `h1` using `key (b1 - b2) j`. Establish `h00 : herm (Hpk k r) 0 (e j) = 0` using `by simp [herm]`. Rewrite `h1` using `[hu, h00]`. Establish `h2` using `(mul_eq_zero.mp h1.symm).resolve_right (hn j)`.

Simplify `h2` using `[sub_eq_zero]`. Establish `hsurj : Function.Surjective A.mulVec` using `Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)`. Establish `hsub : ∀ x y u, herm (Hpk k r) (x - y) u = herm (Hpk k r) x u - herm (Hpk k r) y u`. Introduce `x y u`. Simplify using `only [herm, Matrix.mulVec_sub, dotProduct_sub]`.

Use `set w := v - ∑ j, herm (Hpk k r) v (B0 j) • B0 j with hw`. Establish `hwwb : inWb k r w`. Introduce `i hi`. Simplify using `[hw, Finset.sum_apply, hv i hi, (hB.1 _) i hi]`. Establish `hwe : ∀ j, herm (Hpk k r) w (e j) = 0`.

Introduce `j`. Rewrite using `[hw, hsub, om_herm_sum]`. Simplify using `only [om_herm_smul]`. Simplify using `only [e]`. Use `split_ifs with hj`.

Simplify using `[hB.2.1]`. Simplify using `[hB.2.2 _ z' (by simp), hvz]`. Take `⟨b, hb⟩` from `hsurj (fun t => w ⟨r + t.val, by omega⟩)`. Establish `huw : ∑ i, b i • e i = w`. Establish `h1` using `mid (∑ i, b i • e i - w) (fun i hi => by rw [Pi.sub_apply, sum_wb b i hi, hwwb i hi, sub_zero]) (fun t => by`.

Establish `h2` using `hA b t`. Rewrite `h2` using `[hb]`. Rewrite using `[Pi.sub_apply, ← h2, sub_self])`. Conclude with `sub_eq_zero.mp h1`. Establish `hb0 : ∀ j, b j = 0`.

Introduce `j`. Establish `h1` using `key b j`. Rewrite `h1` using `[huw, hwe]`. Conclude with `(mul_eq_zero.mp h1.symm).resolve_right (hn j)`. Establish `hw0 : w = 0`.

Rewrite using `[← huw]`. Simplify using `[hb0]`. Rewrite `hw0` using `[hw, sub_eq_zero]`. Conclude with `hw0.symm`.
-/
lemma om_complete {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z'] B0) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : inWb k r v) (hvz : herm (Hpk k r) v z' = 0) : ∑ j, herm (Hpk k r) v (B0 j) • B0 j = v := by
  classical
  let e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ := fun i => if h : i.val < k then B0 ⟨i.val, h⟩ else z'
  have he_wb : ∀ i, inWb k r (e i) := by
    intro i
    simp only [e]
    split_ifs
    exacts [hB.1 _, hz']
  have hzz : herm (Hpk k r) z' z' ≠ 0 := by
    intro h0
    simp [Tz, h0] at hT'
  have horth : ∀ i j, i ≠ j → herm (Hpk k r) (e i) (e j) = 0 := by
    intro i j hij
    simp only [e]
    split_ifs with hi hj hj
    · rw [hB.2.1, if_neg]
      intro h
      exact hij (Fin.ext (by simpa using congrArg Fin.val h))
    · exact hB.2.2 _ z' (by simp)
    · rw [herm_swap_eq_zero_of_eq_zero, hB.2.2 _ z' (by simp), map_zero]
    · have := i.isLt
      have := j.isLt
      exact absurd (Fin.ext (by omega)) hij
  have hn : ∀ i, herm (Hpk k r) (e i) (e i) ≠ 0 := by
    intro i
    simp only [e]
    split_ifs
    · rw [hB.2.1, if_pos rfl]
      exact one_ne_zero
    · exact hzz
  have key : ∀ (b : Fin (k + 1) → ℂ) (j : Fin (k + 1)),
      herm (Hpk k r) (∑ i, b i • e i) (e j) = b j * herm (Hpk k r) (e j) (e j) := by
    intro b j
    rw [om_herm_sum, Finset.sum_eq_single j]
    · rw [om_herm_smul]
    · intro i _ hij
      rw [om_herm_smul, horth i j hij, mul_zero]
    · simp
  have mid : ∀ u : Fin (2 * r + k + 1) → ℂ, inWb k r u →
      (∀ t : Fin (k + 1), u ⟨r + t.val, by omega⟩ = 0) → u = 0 := by
    intro u hu ht
    funext i
    show u i = 0
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · have h1 : u ⟨r + (i.val - r), by omega⟩ = 0 := ht ⟨i.val - r, by omega⟩
      have e1 : (⟨r + (i.val - r), by omega⟩ : Fin (2 * r + k + 1)) = i := Fin.ext (by simp; omega)
      rwa [e1] at h1
    · exact hu i (by omega)
  have sum_wb : ∀ b : Fin (k + 1) → ℂ, inWb k r (∑ i, b i • e i) := by
    intro b i hi
    simp [Finset.sum_apply, he_wb _ i hi]
  let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.of fun t i => e i ⟨r + t.val, by omega⟩
  have hA : ∀ b t, (A *ᵥ b) t = (∑ i, b i • e i) ⟨r + t.val, by omega⟩ := by
    intro b t
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinj : Function.Injective A.mulVec := by
    intro b1 b2 h12
    have h0 : A *ᵥ (b1 - b2) = 0 := by rw [Matrix.mulVec_sub, h12, sub_self]
    have hu : ∑ i, (b1 - b2) i • e i = 0 :=
      mid _ (sum_wb _) (fun t => by rw [← hA, h0]; rfl)
    funext j
    have h1 := key (b1 - b2) j
    have h00 : herm (Hpk k r) 0 (e j) = 0 := by simp [herm]
    rw [hu, h00] at h1
    have h2 := (mul_eq_zero.mp h1.symm).resolve_right (hn j)
    simpa [sub_eq_zero] using h2
  have hsurj : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hsub : ∀ x y u, herm (Hpk k r) (x - y) u = herm (Hpk k r) x u - herm (Hpk k r) y u := by
    intro x y u
    simp only [herm, Matrix.mulVec_sub, dotProduct_sub]
  set w := v - ∑ j, herm (Hpk k r) v (B0 j) • B0 j with hw
  have hwwb : inWb k r w := by
    intro i hi
    simp [hw, Finset.sum_apply, hv i hi, (hB.1 _) i hi]
  have hwe : ∀ j, herm (Hpk k r) w (e j) = 0 := by
    intro j
    rw [hw, hsub, om_herm_sum]
    simp only [om_herm_smul]
    simp only [e]
    split_ifs with hj
    · simp [hB.2.1]
    · simp [hB.2.2 _ z' (by simp), hvz]
  obtain ⟨b, hb⟩ := hsurj (fun t => w ⟨r + t.val, by omega⟩)
  have huw : ∑ i, b i • e i = w := by
    have h1 := mid (∑ i, b i • e i - w)
      (fun i hi => by rw [Pi.sub_apply, sum_wb b i hi, hwwb i hi, sub_zero])
      (fun t => by
        have h2 := hA b t
        rw [hb] at h2
        rw [Pi.sub_apply, ← h2, sub_self])
    exact sub_eq_zero.mp h1
  have hb0 : ∀ j, b j = 0 := by
    intro j
    have h1 := key b j
    rw [huw, hwe] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (hn j)
  have hw0 : w = 0 := by
    rw [← huw]
    simp [hb0]
  rw [hw, sub_eq_zero] at hw0
  exact hw0.symm

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `HermitianLatticeCounting.P.omega_decomposition k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem Bs.T'_pos.ne' g hg`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Simplify `h2 (Fin.last r)` using `[fvec]`.
-/
lemma om_N3om_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) :
    inWb k r (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) ∧ herm (Hpk k r) (HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g) Bs.z' = 0 := by
  obtain ⟨h1, h2, -⟩ := HermitianLatticeCounting.P.omega_decomposition k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem
    Bs.T'_pos.ne' g hg
  refine ⟨h1, ?_⟩
  simpa [fvec] using h2 (Fin.last r)

/- English proof (translation)
Repeatedly rewrite using `[om_eq Bs hB hg]`. Conclude with `om_complete Bs.z'_mem Bs.T'_pos hB (om_N3om_mem Bs hg).1 (om_N3om_mem Bs hg).2`.
-/
lemma om_expand {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : ∑ j, omC Bs B0 g j • B0 j = HermitianLatticeCounting.ExpansionTerms.N3om k r Bs.z Bs.z' g := by
  simp_rw [om_eq Bs hB hg]
  exact om_complete Bs.z'_mem Bs.T'_pos hB (om_N3om_mem Bs hg).1 (om_N3om_mem Bs hg).2

/- English proof (translation)
Establish `hm` using `(HermitianLatticeCounting.P.dual_vector_norm_on_group k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem Bs.T'_pos g hg).1`. Rewrite `hm` using `[← om_expand Bs hB hg]`. Simplify using `only [om_herm_sum, om_herm_smul, om_herm_sum_right, om_herm_smul_right, hB.2.1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hm`. Simplify using `only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hm`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Rewrite using `[← hm]`. Simplify using `only [C6.sq2, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]`.
-/
theorem om_norm {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : C6.sq2 (omC Bs B0 g) = Gf k r Bs.z Bs.z' g / Tz k r Bs.z' := by
  have hm := (HermitianLatticeCounting.P.dual_vector_norm_on_group k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem Bs.T'_pos g hg).1
  rw [← om_expand Bs hB hg] at hm
  simp only [om_herm_sum, om_herm_smul, om_herm_sum_right, om_herm_smul_right, hB.2.1,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hm
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hm
  apply Complex.ofReal_injective
  rw [← hm]
  simp only [C6.sq2, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]

/- English proof (translation)
Take `⟨hA, hN1, hD, hN2⟩` from `hp`. Establish `hA'` using `Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hA`. Establish `hN1'` using `Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hN1`. Establish `hsg : B.sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1`. Simplify using `only [B.sgs, Matrix.mul_assoc]`.

Establish `hm : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ UH (Hpk k r)` using `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hN1'.1 hg) hN2.1`. Establish `hsU : B.sgs p g ∈ UH (Hpk k r)`. Rewrite using `[hsg]`. Conclude with `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hA'.1 hm) hD.1`. Rewrite using `[om_expand Bs hB hsU, om_expand Bs hB hg, hsg, HermitianLatticeCounting.P.dual_vector_equivariant k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem _ hm _ hA' _ hD, HermitianLatticeCounting.P.dual_vector_unipotent_invariant k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg _ hN1' _ hN2]`.
-/
theorem om_equiv {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : Q.IsFrameOf k r [Bs.z'] B0) (p : B.SS k r) (hp : Bs.inSS p)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    ∑ j, omC Bs B0 (B.sgs p g) j • B0 j = (Matrix.of p.2.1)⁻¹ *ᵥ ∑ j, omC Bs B0 g j • B0 j := by
  obtain ⟨hA, hN1, hD, hN2⟩ := hp
  have hA' := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hA
  have hN1' := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hN1
  have hsg : B.sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) *
      Matrix.of p.2.1 := by
    simp only [B.sgs, Matrix.mul_assoc]
  have hm : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hN1'.1 hg) hN2.1
  have hsU : B.sgs p g ∈ UH (Hpk k r) := by
    rw [hsg]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hA'.1 hm) hD.1
  rw [om_expand Bs hB hsU, om_expand Bs hB hg, hsg,
    HermitianLatticeCounting.P.dual_vector_equivariant k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem _ hm _ hA' _ hD,
    HermitianLatticeCounting.P.dual_vector_unipotent_invariant k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg _ hN1' _ hN2]

def OmPolyP : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ),
    Q.IsFrameOf k r [Bs.z'] B0 → ∀ j, U.IsPolyDeg (r + 1) fun g => omC Bs B0 g j

def OmCellP : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ),
    Q.IsFrameOf k r [Bs.z'] B0 → ∀ x ∈ Q.DomR k r Bs.z Bs.z', ∀ j, omC Bs B0 (Q.wCell k r (Fin.last r) x.1 * x.2) j =
      conj (∏ a, x.1 a) * herm (Hpk k r) (x.2⁻¹ *ᵥ Bs.z) (B0 j)

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ Bs B0 hB`. Conclude with `⟨h1 k r Wp Wq Bs B0 hB, fun g hg => om_norm Bs hB hg, fun p hp g hg => om_equiv Bs hB p hp hg.1, h4 k r Wp Wq Bs B0 hB⟩`.
-/
theorem om_facts_of (h1 : OmPolyP) (h4 : OmCellP) : OmFacts := by
  intro k r Wp Wq _ _ _ _ _ Bs B0 hB
  exact ⟨h1 k r Wp Wq Bs B0 hB, fun g hg => om_norm Bs hB hg,
    fun p hp g hg => om_equiv Bs hB p hp hg.1, h4 k r Wp Wq Bs B0 hB⟩

/- English proof (translation)
Rewrite using `[← Finset.compl_singleton, ← Fin.image_castSucc, Finset.prod_image (fun a _ b _ h => Fin.castSucc_injective _ h)]`. Simplify using the standard rewrite rules.
-/
lemma om_prod_erase (r : ℕ) (c : Fin r → ℂ) (ζ : ℂ) :
    ∏ j ∈ Finset.univ.erase (Fin.last r), (if h : j.val < r then c ⟨j.val, h⟩ else ζ) = ∏ a, c a := by
  rw [← Finset.compl_singleton, ← Fin.image_castSucc, Finset.prod_image (fun a _ b _ h => Fin.castSucc_injective _ h)]
  simp

/- English proof (translation)
Establish `hWd : IsUnit W.det`. Rewrite `hG` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_left hG`. Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]`. Use `congr 1`.

Use `conv_lhs => rw [← hW]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hWd, Matrix.one_mulVec]`.
-/
lemma inv_mulVec_of_fixed_vector {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (hM : IsUnit M.det)
    (hG : IsUnit (W * M).det) (hW : W *ᵥ z = z) : (W * M)⁻¹ *ᵥ z = M⁻¹ *ᵥ z := by
  have hWd : IsUnit W.det := by
    rw [Matrix.det_mul] at hG
    exact isUnit_of_mul_isUnit_left hG
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  congr 1
  conv_lhs => rw [← hW]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hWd, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨hc, hM, -⟩` from `hx`. Establish `hWU : bigCell k r x.1 1 ∈ UH (Hpk k r)` using `Formalism.QuantumDeterminants.big_cell_mem_holds k r x.1 1 hc (by simp)`. Establish `hgU : bigCell k r x.1 1 * x.2 ∈ UH (Hpk k r)` using `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hWU hM.1`. Establish `hfix : ∀ b, (bigCell k r x.1 1 * x.2) *ᵥ fvec k r Bs.z' b = bigCell k r x.1 1 *ᵥ fvec k r (x.2 *ᵥ Bs.z') b`. Introduce `b`.

Rewrite using `[← Matrix.mulVec_mulVec]`. Use `congr 1`. Unfold `fvec`. Use `split_ifs with hb`. Conclude with `(hM.2 ⟨b.val, hb⟩ (by simp only [Fin.val_last]; exact hb)).1`.

Both sides reduce to the same expression. Establish `hZ : Zhat k r Bs.z Bs.z' (bigCell k r x.1 1 * x.2) = Zhat k r Bs.z (x.2 *ᵥ Bs.z') (bigCell k r x.1 1)`. Use extensionality with `a b`. Simplify using `only [Zhat, hfix]`. Establish `hMz'` using `(Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb hM Bs.z'_mem).1`.

Rewrite `hZ` using `[Formalism.QuantumDeterminants.big_cell_coordinate_holds k r _ _ x.1 1 Bs.z_mem hMz']`. Establish `hcof : D.cofL Bs (bigCell k r x.1 1 * x.2) = conj (∏ a, x.1 a) • Bs.z`. Unfold `D.cofL`. Rewrite using `[hZ, Matrix.adjugate_diagonal, Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[Matrix.diagonal_apply_eq, om_prod_erase]`.

Use `congr 1`. Simplify using `[fvec]`. Introduce `b _ hb`. Rewrite using `[Matrix.diagonal_apply_ne _ (Ne.symm hb), map_zero, zero_smul]`. Simplify using the standard rewrite rules.

Establish `hWz : bigCell k r x.1 1 *ᵥ Bs.z = Bs.z`. Rewrite using `[← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Matrix.one_mulVec]`. Rewrite using `[Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]`. Use `show herm (Hpk k r) ((Hpk k r * (bigCell k r x.1 1 * x.2)ᴴ * Hpk k r) *ᵥ D.cofL Bs (bigCell k r x.1 1 * x.2)) (B0 j) = _`. Rewrite using `[om_inv_eq hgU, hcof, Matrix.mulVec_smul, om_herm_smul, inv_mulVec_of_fixed_vector _ _ _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hM.1) (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hgU) hWz]`.
-/
theorem om_cell {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (x : (Fin r → ℂ) × Q.Mx k r) (hx : x ∈ Q.DomR k r Bs.z Bs.z') (j : Fin k) :
    omC Bs B0 (Q.wCell k r (Fin.last r) x.1 * x.2) j = conj (∏ a, x.1 a) * herm (Hpk k r) (x.2⁻¹ *ᵥ Bs.z) (B0 j) := by
  obtain ⟨hc, hM, -⟩ := hx
  have hWU : bigCell k r x.1 1 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.big_cell_mem_holds k r x.1 1 hc (by simp)
  have hgU : bigCell k r x.1 1 * x.2 ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hWU hM.1
  have hfix : ∀ b, (bigCell k r x.1 1 * x.2) *ᵥ fvec k r Bs.z' b =
      bigCell k r x.1 1 *ᵥ fvec k r (x.2 *ᵥ Bs.z') b := by
    intro b
    rw [← Matrix.mulVec_mulVec]
    congr 1
    unfold fvec
    split_ifs with hb
    · exact (hM.2 ⟨b.val, hb⟩ (by simp only [Fin.val_last]; exact hb)).1
    · rfl
  have hZ : Zhat k r Bs.z Bs.z' (bigCell k r x.1 1 * x.2) = Zhat k r Bs.z (x.2 *ᵥ Bs.z') (bigCell k r x.1 1) := by
    ext a b
    simp only [Zhat, hfix]
  have hMz' := (Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb hM Bs.z'_mem).1
  rw [Formalism.QuantumDeterminants.big_cell_coordinate_holds k r _ _ x.1 1 Bs.z_mem hMz'] at hZ
  have hcof : D.cofL Bs (bigCell k r x.1 1 * x.2) = conj (∏ a, x.1 a) • Bs.z := by
    unfold D.cofL
    rw [hZ, Matrix.adjugate_diagonal, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.diagonal_apply_eq, om_prod_erase]
      congr 1
      simp [fvec]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), map_zero, zero_smul]
    · simp
  have hWz : bigCell k r x.1 1 *ᵥ Bs.z = Bs.z := by
    rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Matrix.one_mulVec]
  rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  show herm (Hpk k r) ((Hpk k r * (bigCell k r x.1 1 * x.2)ᴴ * Hpk k r) *ᵥ
    D.cofL Bs (bigCell k r x.1 1 * x.2)) (B0 j) = _
  rw [om_inv_eq hgU, hcof, Matrix.mulVec_smul, om_herm_smul,
    inv_mulVec_of_fixed_vector _ _ _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hM.1) (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hgU) hWz]

end

end Formalism.FourierDecayAlt.P.TLC

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.TLC

/- English proof (translation)
Conclude with `om_facts_of (fun k r Wp Wq _ _ _ _ _ Bs B0 _ j => omp_poly Bs B0 j) (fun k r Wp Wq _ _ _ _ _ Bs B0 _ x hx j => om_cell Bs x hx j)`.
-/
theorem omega_polynomial_facts : TL.OmFacts := by
  exact om_facts_of (fun k r Wp Wq _ _ _ _ _ Bs B0 _ j => omp_poly Bs B0 j)
    (fun k r Wp Wq _ _ _ _ _ Bs B0 _ x hx j => om_cell Bs x hx j)

end Formalism.FourierDecayAlt.P
