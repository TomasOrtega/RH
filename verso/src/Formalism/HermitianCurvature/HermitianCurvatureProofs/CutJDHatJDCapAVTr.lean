import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRModelV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRDrTr

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Gauge Gauge.VLem

noncomputable section

section model

variable (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r)

def capaVpM (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => L.Tvl Y l).prod

/- English proof (translation)
Simplify using `[capaVpM]`.
-/
theorem capaVpM_zero (Y : ℂ) : capaVpM P L Y 0 = 1 := by
  simp [capaVpM]

/- English proof (translation)
Simplify using `[capaVpM, List.take_add_one, h]`.
-/
theorem capaVpM_succ (Y : ℂ) (i : ℕ) (h : i < P.r) :
    capaVpM P L Y (i + 1) = L.Tvl Y ⟨i, h⟩ * capaVpM P L Y i := by
  simp [capaVpM, List.take_add_one, h]

/- English proof (translation)
Simplify using `[R.LevelData.Tvprod, capaVpM, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]`.
-/
theorem capa_tvprod (Y : ℂ) : L.Tvprod Y = capaVpM P L Y P.r := by
  simp [R.LevelData.Tvprod, capaVpM, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

/- English proof (translation)
Simplify using `[R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem capa_Tvl_mul_0 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y - L.pb l) * V 0 0 + -L.cb l * V 1 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem capa_Tvl_mul_1 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 1 0 = L.cbi l * V 0 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Use `show MA.actA P (MA.sc P (MA.DQ P) _) f = _`. Rewrite using `[actA_sc]`. Both sides reduce to the same expression.
-/
theorem capa_actA_pb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.pbA P (MA.DQ P) l) f = fun ρ => MA.eulerQ (TT := P.TT) (M.vcb l) (f ρ) := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

/- English proof (translation)
Use `show MA.actA P (MA.sc P (MA.DQ P) _) f = _`. Rewrite using `[actA_sc]`. Both sides reduce to the same expression.
-/
theorem capa_actA_cb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

/- English proof (translation)
Use `show MA.actA P (MA.sc P (MA.DQ P) _) f = _`. Rewrite using `[actA_sc]`. Both sides reduce to the same expression.
-/
theorem capa_actA_cbi (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbiA P (MA.DQ P) l) f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb l)) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

end model

section ind

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ Dc Φ hΦ`. Establish `h0 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 0) Φ = Φ` using `rfl`.

Establish `h1 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 1) Φ = 0` using `rfl`. Establish `v0 : Vp P Y 0 0 0 = 1` using `by simp [Vp_zero]`. Establish `v1 : Vp P Y 0 1 0 = 0` using `by simp [Vp_zero]`. Rewrite using `[h0, h1, v0, v1, actA_one, actA_zero, trR_zero]`. Use `⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩` and prove the remaining obligations.

Use `famR_smul hΦ 0` as an intermediate fact. Rewrite `this` using `[zero_smul]`. Then use the resulting hypothesis. Consider the case `succ i ih`. Introduce `hi Dc Φ hΦ`. Establish `h : i < P.r` using `hi`.

Take `⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩` from `ih (Nat.le_of_lt h) Dc Φ hΦ`. Use `set ΦA := Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ with hΦA`. Use `set ΦB := Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ with hΦB`. Establish `hv : Q.vAB (E` using `Wq →L[ℂ] Wp) P.r Y (i + 1) = (fun f => Y • (Q.vAB P.r Y i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f) - cOp ⟨i, h⟩ ((Q.vAB P.r Y i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f)) := by`. Simplify using `only [Q.vAB, dif_pos h]`.

Establish `e0 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 0) Φ = Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB`. Rewrite using `[hv]`. Both sides reduce to the same expression. Establish `e1 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA`. Rewrite using `[hv]`.

Both sides reduce to the same expression. Establish `hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA)` using `famR_opL hA ⟨i, h⟩ 0`. Establish `hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB)` using `famR_opL hB ⟨i, h⟩ 1`. Establish `hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA)` using `famR_opL hA ⟨i, h⟩ 2`. Establish `hsum : FamR P Bs Dc (Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA)` using `famR_add (famR_smul hA _) hpA`.

Establish `tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) = fun ρ => MA.coordQ (TT` using `P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ := trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)`. Establish `tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) = fun ρ => Ring.inverse (MA.coordQ (TT` using `P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ := trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by`. Rewrite using `[inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])`. Use `⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[e0]`.

Conclude with `famR_sub hsum hcB`. Rewrite using `[e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ), trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul, trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul, actA …`. Rewrite using `[e1]`. Conclude with `hciA`. Rewrite using `[e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]`.
-/
theorem capa_vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (Q.vAB P.r Y i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r Y i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 0) Φ =
        Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc (Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

/- English proof (translation)
Take `⟨-, hpb, -, -, hcb, hcbi, -⟩` from `hL`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ Dc Φ hΦ`.

Establish `h0 : Q.crd (Q.cmp (vABm P.r Y 0) 0) Φ = Φ` using `rfl`. Establish `h1 : Q.crd (Q.cmp (vABm P.r Y 0) 1) Φ = 0` using `rfl`. Establish `v0 : capaVpM P L Y 0 0 0 = 1` using `by simp [capaVpM_zero]`. Establish `v1 : capaVpM P L Y 0 1 0 = 0` using `by simp [capaVpM_zero]`. Rewrite using `[h0, h1, v0, v1, actA_one, actA_zero, trR_zero]`.

Use `⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩` and prove the remaining obligations. Use `famR_smul hΦ 0` as an intermediate fact. Rewrite `this` using `[zero_smul]`. Then use the resulting hypothesis. Consider the case `succ i ih`. Introduce `hi Dc Φ hΦ`.

Establish `h : i < P.r` using `hi`. Take `⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩` from `ih (Nat.le_of_lt h) Dc Φ hΦ`. Use `set ΦA := Q.crd (Q.cmp (vABm P.r Y i) 0) Φ with hΦA`. Use `set ΦB := Q.crd (Q.cmp (vABm P.r Y i) 1) Φ with hΦB`. Establish `hv : vABm (X` using `Wq →L[ℂ] Wp) P.r Y (i + 1) = (fun f => Y • (vABm P.r Y i).1 f - pbOp ⟨i, h⟩ ((vABm P.r Y i).1 f) - cbOp ⟨i, h⟩ ((vABm P.r Y i).2 f), fun f => cbiOp ⟨i, h⟩ ((vABm P.r Y i).1 f)) := by`.

Simplify using `only [vABm, dif_pos h]`. Establish `e0 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 0) Φ = Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA - Q.crd (cbOp ⟨i, h⟩) ΦB`. Rewrite using `[hv]`. Both sides reduce to the same expression. Establish `e1 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 1) Φ = Q.crd (cbiOp ⟨i, h⟩) ΦA`.

Rewrite using `[hv]`. Both sides reduce to the same expression. Establish `hpA : FamR P Bs Dc (Q.crd (pbOp ⟨i, h⟩) ΦA)` using `famR_opL hA ⟨i, h⟩ 3`. Establish `hcB : FamR P Bs Dc (Q.crd (cbOp ⟨i, h⟩) ΦB)` using `famR_opL hB ⟨i, h⟩ 4`. Establish `hciA : FamR P Bs Dc (Q.crd (cbiOp ⟨i, h⟩) ΦA)` using `famR_opL hA ⟨i, h⟩ 5`.

Establish `hdif : FamR P Bs Dc (Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA)` using `famR_sub (famR_smul hA _) hpA`. Establish `tc : trR P Bs.μsec e (Q.crd (cbOp ⟨i, h⟩) ΦB) = fun ρ => MA.coordQ (TT` using `P.TT) (M.vcb ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ := trR_mul hpl hk he hB _ hcB (fun c => star (c ⟨i, h⟩)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)`. Establish `tci : trR P Bs.μsec e (Q.crd (cbiOp ⟨i, h⟩) ΦA) = fun ρ => Ring.inverse (MA.coordQ (TT` using `P.TT) (M.vcb ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ := trR_mul hpl hk he hA _ hciA (fun c => (star (c ⟨i, h⟩))⁻¹) (fun _ _ => rfl) _ (fun q => by`. Rewrite using `[inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])`. Use `⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[e0]`. Conclude with `famR_sub hdif hcB`. Rewrite using `[e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hdif ρ) (fun ρ => smR hpl hk he hcB ρ), trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul, trR_pb hpl hk he hA, tc, tA, tB, capaVpM_succ P L Y i h, capa_Tvl_mul_0, hpb, hcb, actA_add, …`. Rewrite using `[e1]`. Conclude with `hciA`.

Rewrite using `[e1, tci, tA, capaVpM_succ P L Y i h, capa_Tvl_mul_1, actA_mul, hcbi, capa_actA_cbi]`.
-/
theorem capa_vabm_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) =
          MA.actA P (capaVpM P L Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) =
          MA.actA P (capaVpM P L Y i 1 0) (trR P Bs.μsec e Φ)) := by
  obtain ⟨-, hpb, -, -, hcb, hcbi, -⟩ := hL
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (vABm P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (vABm P.r Y 0) 1) Φ = 0 := rfl
    have v0 : capaVpM P L Y 0 0 0 = 1 := by simp [capaVpM_zero]
    have v1 : capaVpM P L Y 0 1 0 = 0 := by simp [capaVpM_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (vABm P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (vABm P.r Y i) 1) Φ with hΦB
    have hv : vABm (X := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (vABm P.r Y i).1 f - pbOp ⟨i, h⟩ ((vABm P.r Y i).1 f) -
          cbOp ⟨i, h⟩ ((vABm P.r Y i).2 f), fun f => cbiOp ⟨i, h⟩ ((vABm P.r Y i).1 f)) := by
      simp only [vABm, dif_pos h]
    have e0 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 0) Φ =
        Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA - Q.crd (cbOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 1) Φ = Q.crd (cbiOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 3
    have hcB : FamR P Bs Dc (Q.crd (cbOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 4
    have hciA : FamR P Bs Dc (Q.crd (cbiOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 5
    have hdif : FamR P Bs Dc (Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_sub (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cbOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => star (c ⟨i, h⟩)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)
    have tci : trR P Bs.μsec e (Q.crd (cbiOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (star (c ⟨i, h⟩))⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hdif hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hdif ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_pb hpl hk he hA, tc, tA, tB, capaVpM_succ P L Y i h, capa_Tvl_mul_0, hpb, hcb, actA_add, actA_mul,
        actA_mul, actA_neg, sub_eq_add_neg ((algebraMap ℂ (MA.A P (MA.DQ P))) Y), actA_add, actA_algebraMap, actA_neg,
        capa_actA_pb, capa_actA_cb, sub_eq_add_neg, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, capaVpM_succ P L Y i h, capa_Tvl_mul_1, actA_mul, hcbi, capa_actA_cbi]

end ind

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ y`. Establish `hA` using `(capa_vab_ind hpl hk he y P.r le_rfl Dc Φ hΦ).1`. Establish `hAv` using `(capa_vabm_ind hpl hk he L hL y P.r le_rfl Dc Φ hΦ).1`. Use `⟨⟨hA.1, ?_⟩, ⟨hAv.1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hA.2, R.LevelData.Ar, ← site_vector_eq_tensor_product P L hL y 0, sitesCommonSpace_v0_eq_Vp]`.

Rewrite using `[hAv.2, R.LevelData.Avr, capa_tvprod]`.
-/
theorem capelli_transition_holds : JDAVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ y
  have hA := (capa_vab_ind hpl hk he y P.r le_rfl Dc Φ hΦ).1
  have hAv := (capa_vabm_ind hpl hk he L hL y P.r le_rfl Dc Φ hΦ).1
  refine ⟨⟨hA.1, ?_⟩, ⟨hAv.1, ?_⟩⟩
  · rw [hA.2, R.LevelData.Ar, ← site_vector_eq_tensor_product P L hL y 0, sitesCommonSpace_v0_eq_Vp]
  · rw [hAv.2, R.LevelData.Avr, capa_tvprod]

/- English proof (translation)
The claim follows from `jDCapA_of_parts hG capelli_transition_holds residue_derivative_transition`.
-/
theorem jDCapA_of_grp (hG : JDAGrp) : JDCapA := jDCapA_of_parts hG capelli_transition_holds residue_derivative_transition

end

end Formalism.FourierDecayAlt.P.CutMP
