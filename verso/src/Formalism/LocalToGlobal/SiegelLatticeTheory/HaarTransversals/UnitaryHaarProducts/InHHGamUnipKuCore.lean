import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut.GU

open Formalism.L2.SG.Pf.Level

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Level

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Take `⟨s, hs, rfl⟩` from `ht`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `intsmul_mem X hs (unitaryCongruence.smul_mem_mL X.B.I hb)`.
-/
theorem zs_mL {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : ZMod' X.B.I X.B.g t) {b : VA X.B.I}
    (hb : b ∈ X.B.I.Lf) : t • b ∈ mL X.B.I X.B.g := by
  obtain ⟨s, hs, rfl⟩ := ht
  rw [mul_comm, mul_smul]
  exact intsmul_mem X hs (unitaryCongruence.smul_mem_mL X.B.I hb)

/- English proof (translation)
The claim follows from `sup_le (Submodule.span_le.mpr fun s hs => hT s hs) (unitaryCongruence.mL_Qs X.B.I X.B.g hf)`.
-/
theorem Mo_le_Qs {f : VA X.B.I} (hf : f ∈ X.B.I.Lf) (T : Set (VA X.B.I))
    (hT : ∀ s ∈ T, ZMod' X.B.I X.B.g (hA X.B.I f s)) :
    unitaryCongruence.Mo X.B.I X.B.g T ≤ unitaryCongruence.Qs X.B.I X.B.g f :=
  sup_le (Submodule.span_le.mpr fun s hs => hT s hs) (unitaryCongruence.mL_Qs X.B.I X.B.g hf)

def Gm (m : ℕ) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) :=
  unitaryCongruence.Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < m})

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _ w hw`. Rewrite using `[pow_zero, one_mulVec]` and apply the resulting hypothesis. Consider the case `succ m ih`.

Introduce `hm w hw`. Rewrite using `[pow_succ, ← mulVec_mulVec]`. Apply `ih (Nat.le_of_succ_le hm)` to reduce the goal to its premises. Conclude with `unitaryCongruence.b_step X.B.I X.B.g X.e0 X.z0 X.bw hκ.1 hκ.2 ⟨m, hm⟩ w hw`.
-/
theorem flag {κ : X.B.I.Gf} (hκ : κ ∈ X.K2) :
    ∀ m, m ≤ D.R.k → ∀ w ∈ Gm X m, ((X.B.I.fmat κ - 1) ^ m) *ᵥ w ∈ Gm X 0 := by
  intro m
  induction m with
  | zero => intro _ w hw; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro hm w hw
    rw [pow_succ, ← mulVec_mulVec]
    apply ih (Nat.le_of_succ_le hm)
    exact unitaryCongruence.b_step X.B.I X.B.g X.e0 X.z0 X.bw hκ.1 hκ.2 ⟨m, hm⟩ w hw

/- English proof (translation)
The claim follows from `unitaryCongruence.sub_Mo X.B.I (Or.inr ⟨j, j.2, rfl⟩)`.
-/
theorem bw_Gk (j : Fin D.R.k) : X.bw j ∈ Gm X D.R.k :=
  unitaryCongruence.sub_Mo X.B.I (Or.inr ⟨j, j.2, rfl⟩)

/- English proof (translation)
Establish `h0 : hA X.B.I a (X.B.I.fmat κ *ᵥ b) = hA X.B.I (X.B.I.fmat κ⁻¹ *ᵥ a) b`. Use `hA_fmat X κ (X.B.I.fmat κ⁻¹ *ᵥ a) b` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, fmat_mul_inv, one_mulVec]`. Then use the resulting hypothesis. Rewrite using `[sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, unitaryCongruence.hA_sub_right, hA_sub_left, h0]`.
-/
theorem adj1 (κ : X.B.I.Gf) (a b : VA X.B.I) :
    hA X.B.I a ((X.B.I.fmat κ - 1) *ᵥ b) = hA X.B.I ((X.B.I.fmat κ⁻¹ - 1) *ᵥ a) b := by
  have h0 : hA X.B.I a (X.B.I.fmat κ *ᵥ b) = hA X.B.I (X.B.I.fmat κ⁻¹ *ᵥ a) b := by
    have := hA_fmat X κ (X.B.I.fmat κ⁻¹ *ᵥ a) b
    rwa [mulVec_mulVec, fmat_mul_inv, one_mulVec] at this
  rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, unitaryCongruence.hA_sub_right, hA_sub_left, h0]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro a b`. Simplify using `only [pow_zero, one_mulVec]`. Consider the case `succ m ih`.

Introduce `a b`. Rewrite using `[pow_succ, ← mulVec_mulVec, ih, adj1, pow_succ', ← mulVec_mulVec]`.
-/
theorem adj (κ : X.B.I.Gf) : ∀ m (a b : VA X.B.I),
    hA X.B.I a (((X.B.I.fmat κ - 1) ^ m) *ᵥ b) = hA X.B.I (((X.B.I.fmat κ⁻¹ - 1) ^ m) *ᵥ a) b := by
  intro m
  induction m with
  | zero => intro a b; simp only [pow_zero, one_mulVec]
  | succ m ih =>
    intro a b
    rw [pow_succ, ← mulVec_mulVec, ih, adj1, pow_succ', ← mulVec_mulVec]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro y hy`. Rewrite using `[pow_zero, one_mulVec]` and apply the resulting hypothesis. Consider the case `succ m ih`.

Introduce `y hy`. Rewrite using `[pow_succ, ← mulVec_mulVec]`. Conclude with `ih _ (unitaryCongruence.K_sub_mv X.B.I hκ hy)`.
-/
theorem pow_Lf {κ : X.B.I.Gf} (hκ : κ ∈ X.B.I.Kset) :
    ∀ m, ∀ y ∈ X.B.I.Lf, ((X.B.I.fmat κ - 1) ^ m) *ᵥ y ∈ X.B.I.Lf := by
  intro m
  induction m with
  | zero => intro y hy; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro y hy
    rw [pow_succ, ← mulVec_mulVec]
    exact ih _ (unitaryCongruence.K_sub_mv X.B.I hκ hy)

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro y hy`. Rewrite using `[pow_zero, one_mulVec]` and apply the resulting hypothesis. Consider the case `succ m ih`.

Introduce `y hy`. Rewrite using `[pow_succ, ← mulVec_mulVec]`. Apply `ih` to reduce the goal to its premises. Rewrite using `[sub_mulVec, one_mulVec]`. Conclude with `Y.sub_mem (hYM y hy) hy`.
-/
theorem pow_Y (κ : X.B.I.Gf) (Y : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I))
    (hYM : ∀ v ∈ Y, X.B.I.fmat κ *ᵥ v ∈ Y) :
    ∀ m, ∀ y ∈ Y, ((X.B.I.fmat κ - 1) ^ m) *ᵥ y ∈ Y := by
  intro m
  induction m with
  | zero => intro y hy; rwa [pow_zero, one_mulVec]
  | succ m ih =>
    intro y hy
    rw [pow_succ, ← mulVec_mulVec]
    apply ih
    rw [sub_mulVec, one_mulVec]
    exact Y.sub_mem (hYM y hy) hy

/- English proof (translation)
Establish `hA' : ∑ a, hA X.B.I (X.f0 a) v • X.e0 a ∈ mL X.B.I X.B.g` using `Submodule.sum_mem _ fun a _ => zs_mL X (ho.1 a).2 (X.vectorsInLattice.1 a).1`. Establish `hB' : ∑ a, hA X.B.I (X.e0 a) v • X.f0 a ∈ mL X.B.I X.B.g` using `Submodule.sum_mem _ fun a _ => zs_mL X (ho.1 a).1 (X.vectorsInLattice.1 a).2`. Establish `hC' : hA X.B.I X.z0 v • X.z0 ∈ mL X.B.I X.B.g` using `zs_mL X ho.2 X.vectorsInLattice.2.1`. Establish `he : v - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i = piG X v + ∑ a, hA X.B.I (X.f0 a) v • X.e0 a + ∑ a, hA X.B.I (X.e0 a) v • X.f0 a - hA X.B.I X.z0 v • X.z0`. Unfold `piG`.

Normalize the expressions using the abelian group laws. Rewrite using `[he]`. Conclude with `Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (hP v hv) hA') hB') hC'`.
-/
theorem decomp (hP : ProjModG X) {v : VA X.B.I} (hv : v ∈ X.B.I.Lf)
    (ho : (∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v) ∧ ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) v)) ∧
      ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) :
    v - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i ∈ mL X.B.I X.B.g := by
  have hA' : ∑ a, hA X.B.I (X.f0 a) v • X.e0 a ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun a _ => zs_mL X (ho.1 a).2 (X.vectorsInLattice.1 a).1
  have hB' : ∑ a, hA X.B.I (X.e0 a) v • X.f0 a ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun a _ => zs_mL X (ho.1 a).1 (X.vectorsInLattice.1 a).2
  have hC' : hA X.B.I X.z0 v • X.z0 ∈ mL X.B.I X.B.g := zs_mL X ho.2 X.vectorsInLattice.2.1
  have he : v - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i =
      piG X v + ∑ a, hA X.B.I (X.f0 a) v • X.e0 a + ∑ a, hA X.B.I (X.e0 a) v • X.f0 a -
        hA X.B.I X.z0 v • X.z0 := by
    unfold piG; abel
  rw [he]
  exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (hP v hv) hA') hB') hC'

/- English proof (translation)
Establish `h1 : hA X.B.I (sigA X.B.I X.ew • X.bwd i) w = X.ew * hA X.B.I (X.bwd i) w`. Rewrite using `[unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]`. Rewrite `h1` using `[← X.bwd_w i]`. Establish `h2 : hA X.B.I (X.bwd i) w = sigA X.B.I X.ew * hA X.B.I (X.bwd i) w` using `by conv_lhs => rw [hw]`. Rewrite using `[unitaryCongruence.hA_smul_right]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem dual_zero (i : Fin D.R.k) (w : VA X.B.I) (hw : w = sigA X.B.I X.ew • w) :
    hA X.B.I (X.bwd i) w = 0 := by
  have h1 : hA X.B.I (sigA X.B.I X.ew • X.bwd i) w = X.ew * hA X.B.I (X.bwd i) w := by
    rw [unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  rw [← X.bwd_w i] at h1
  have h2 : hA X.B.I (X.bwd i) w = sigA X.B.I X.ew * hA X.B.I (X.bwd i) w := by
    conv_lhs => rw [hw]
    rw [unitaryCongruence.hA_smul_right]
  calc hA X.B.I (X.bwd i) w = X.ew * (sigA X.B.I X.ew * hA X.B.I (X.bwd i) w) := by rw [← h2, ← h1]
    _ = (X.ew * sigA X.B.I X.ew) * hA X.B.I (X.bwd i) w := by ring
    _ = 0 := by rw [X.ew_orth, zero_mul]

/- English proof (translation)
Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [X.bwd_w j]`. Rewrite using `[smul_comm]`.
-/
theorem sigA_smul_bwd_sum_eq (c : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    ∑ j, c j • X.bwd j = sigA X.B.I X.ew • ∑ j, c j • X.bwd j := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [X.bwd_w j]
  rw [smul_comm]

/- English proof (translation)
Introduce `hP κ hκ hκi Y hYL hYM hYo v hv`. Use `set M := X.B.I.fmat κ with hMdef`. Establish `hvL : v ∈ X.B.I.Lf` using `hYL hv`. Use `set z := ((M - 1) ^ D.R.k) *ᵥ v with hzdef`. Establish `hzY : z ∈ Y` using `pow_Y X κ Y hYM _ v hv`.

Establish `hzL : z ∈ X.B.I.Lf` using `hYL hzY`. Establish `ha : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.bw i) z)`. Introduce `i`. Rewrite using `[hzdef, adj X κ]`. Establish `hG : ((X.B.I.fmat κ⁻¹ - 1) ^ D.R.k) *ᵥ X.bw i ∈ Gm X 0` using `flag X hκi D.R.k le_rfl (X.bw i) (bw_Gk X i)`.

Establish `hle : Gm X 0 ≤ unitaryCongruence.Qs X.B.I X.B.g v`. Use `Mo_le_Qs X hvL _ ?_` and prove the remaining obligations. Introduce and unpack `s (⟨a, rfl⟩ | ⟨j, hj, _⟩)`. Rewrite using `[unitaryCongruence.hA_symm X.B.I (X.e0 a) v]`. Conclude with `unitaryCongruence.Z_sig X.B.I X.B.g ((hYo v hv).1 a).1`.

Conclude with `absurd hj (Nat.not_lt_zero _)`. Establish `hq : ZMod' X.B.I X.B.g (hA X.B.I v (((X.B.I.fmat κ⁻¹ - 1) ^ D.R.k) *ᵥ X.bw i))` using `hle hG`. Rewrite using `[unitaryCongruence.hA_symm X.B.I v]`. Conclude with `unitaryCongruence.Z_sig X.B.I X.B.g hq`. Establish `hb : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) z)`.

Introduce `i`. Use `set v1 := ∑ j, hA X.B.I (X.bwd j) v • X.bw j with hv1`. Use `set v2 := ∑ j, hA X.B.I (X.bw j) v • X.bwd j with hv2`. Establish `hm : v - v1 - v2 ∈ mL X.B.I X.B.g` using `decomp X hP hvL (hYo v hv)`. Establish `hsplit : z = ((M - 1) ^ D.R.k) *ᵥ v1 + ((M - 1) ^ D.R.k) *ᵥ v2 + ((M - 1) ^ D.R.k) *ᵥ (v - v1 - v2)`.

Rewrite using `[hzdef, ← mulVec_add, ← mulVec_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[hsplit, unitaryCongruence.hA_add_right, unitaryCongruence.hA_add_right]`. Use `unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g ?_ ?_) ?_` and prove the remaining obligations.

Establish `hv1G : v1 ∈ Gm X D.R.k` using `Submodule.sum_mem _ fun j _ => intsmul_mem X (unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 j).2 hvL) (bw_Gk X j)`. Establish `hG` using `flag X hκ D.R.k le_rfl v1 hv1G`. Establish `hle : Gm X 0 ≤ unitaryCongruence.Qs X.B.I X.B.g (X.bwd i)`. Use `Mo_le_Qs X (X.vectorsInLattice.2.2 i).2 _ ?_` and prove the remaining obligations. Introduce and unpack `s (⟨a, rfl⟩ | ⟨j, hj, _⟩)`.

Conclude with `(reference_frame_congruences X).2.2.1 i a`. Conclude with `absurd hj (Nat.not_lt_zero _)`. Conclude with `hle hG`. Rewrite using `[dual_zero X i _ (by rw [hv2, ← mulVec_smul, ← sigA_smul_bwd_sum_eq X])]`. Conclude with `unitaryCongruence.Z_zero X.B.I X.B.g`.

Conclude with `Z_right X (X.vectorsInLattice.2.2 i).2 (mL_pres X _ (pow_Lf X hκ.1 D.R.k) _ hm)`. Establish `hd` using `decomp X hP hzL (hYo z hzY)`. Establish `h1 : ∑ i, hA X.B.I (X.bwd i) z • X.bw i ∈ mL X.B.I X.B.g` using `Submodule.sum_mem _ fun i _ => zs_mL X (hb i) (X.vectorsInLattice.2.2 i).1`. Establish `h2 : ∑ i, hA X.B.I (X.bw i) z • X.bwd i ∈ mL X.B.I X.B.g` using `Submodule.sum_mem _ fun i _ => zs_mL X (ha i) (X.vectorsInLattice.2.2 i).2`. Establish `he : z = (z - ∑ i, hA X.B.I (X.bwd i) z • X.bw i - ∑ i, hA X.B.I (X.bw i) z • X.bwd i) + ∑ i, hA X.B.I (X.bwd i) z • X.bw i + ∑ i, hA X.B.I (X.bw i) z • X.bwd i` using `by abel`.

Rewrite using `[he]`. Conclude with `Submodule.add_mem _ (Submodule.add_mem _ hd h1) h2`.
-/
theorem coreOfProj {D : D7} (X : HidaSetting D) : CoreOfProj X := by
  intro hP κ hκ hκi Y hYL hYM hYo v hv
  set M := X.B.I.fmat κ with hMdef
  have hvL : v ∈ X.B.I.Lf := hYL hv
  set z := ((M - 1) ^ D.R.k) *ᵥ v with hzdef
  have hzY : z ∈ Y := pow_Y X κ Y hYM _ v hv
  have hzL : z ∈ X.B.I.Lf := hYL hzY

  have ha : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.bw i) z) := by
    intro i
    rw [hzdef, adj X κ]
    have hG : ((X.B.I.fmat κ⁻¹ - 1) ^ D.R.k) *ᵥ X.bw i ∈ Gm X 0 :=
      flag X hκi D.R.k le_rfl (X.bw i) (bw_Gk X i)
    have hle : Gm X 0 ≤ unitaryCongruence.Qs X.B.I X.B.g v := by
      refine Mo_le_Qs X hvL _ ?_
      rintro s (⟨a, rfl⟩ | ⟨j, hj, _⟩)
      · rw [unitaryCongruence.hA_symm X.B.I (X.e0 a) v]
        exact unitaryCongruence.Z_sig X.B.I X.B.g ((hYo v hv).1 a).1
      · exact absurd hj (Nat.not_lt_zero _)
    have hq : ZMod' X.B.I X.B.g (hA X.B.I v (((X.B.I.fmat κ⁻¹ - 1) ^ D.R.k) *ᵥ X.bw i)) := hle hG
    rw [unitaryCongruence.hA_symm X.B.I v]
    exact unitaryCongruence.Z_sig X.B.I X.B.g hq

  have hb : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) z) := by
    intro i
    set v1 := ∑ j, hA X.B.I (X.bwd j) v • X.bw j with hv1
    set v2 := ∑ j, hA X.B.I (X.bw j) v • X.bwd j with hv2
    have hm : v - v1 - v2 ∈ mL X.B.I X.B.g := decomp X hP hvL (hYo v hv)
    have hsplit : z = ((M - 1) ^ D.R.k) *ᵥ v1 + ((M - 1) ^ D.R.k) *ᵥ v2 +
        ((M - 1) ^ D.R.k) *ᵥ (v - v1 - v2) := by
      rw [hzdef, ← mulVec_add, ← mulVec_add]; congr 1; abel
    rw [hsplit, unitaryCongruence.hA_add_right, unitaryCongruence.hA_add_right]
    refine unitaryCongruence.Z_add X.B.I X.B.g (unitaryCongruence.Z_add X.B.I X.B.g ?_ ?_) ?_
    · have hv1G : v1 ∈ Gm X D.R.k :=
        Submodule.sum_mem _ fun j _ =>
          intsmul_mem X (unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 j).2 hvL) (bw_Gk X j)
      have hG := flag X hκ D.R.k le_rfl v1 hv1G
      have hle : Gm X 0 ≤ unitaryCongruence.Qs X.B.I X.B.g (X.bwd i) := by
        refine Mo_le_Qs X (X.vectorsInLattice.2.2 i).2 _ ?_
        rintro s (⟨a, rfl⟩ | ⟨j, hj, _⟩)
        · exact (reference_frame_congruences X).2.2.1 i a
        · exact absurd hj (Nat.not_lt_zero _)
      exact hle hG
    · rw [dual_zero X i _ (by rw [hv2, ← mulVec_smul, ← sigA_smul_bwd_sum_eq X])]
      exact unitaryCongruence.Z_zero X.B.I X.B.g
    · exact Z_right X (X.vectorsInLattice.2.2 i).2
        (mL_pres X _ (pow_Lf X hκ.1 D.R.k) _ hm)

  have hd := decomp X hP hzL (hYo z hzY)
  have h1 : ∑ i, hA X.B.I (X.bwd i) z • X.bw i ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun i _ => zs_mL X (hb i) (X.vectorsInLattice.2.2 i).1
  have h2 : ∑ i, hA X.B.I (X.bw i) z • X.bwd i ∈ mL X.B.I X.B.g :=
    Submodule.sum_mem _ fun i _ => zs_mL X (ha i) (X.vectorsInLattice.2.2 i).2
  have he : z = (z - ∑ i, hA X.B.I (X.bwd i) z • X.bw i - ∑ i, hA X.B.I (X.bw i) z • X.bwd i) +
      ∑ i, hA X.B.I (X.bwd i) z • X.bw i + ∑ i, hA X.B.I (X.bw i) z • X.bwd i := by abel
  rw [he]
  exact Submodule.add_mem _ (Submodule.add_mem _ hd h1) h2

end Formalism.L2.SG.PoincareInHH.Cut.GU
