import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

/- English proof (translation)
Establish `hc : x * a = a * x`. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using `[Matrix.mul_apply, mul_comm]`.

Rewrite using `[hc, mul_inv_cancel_right]`.
-/
theorem gl_one_conj {R : Type} [CommRing R] (x a : GL (Fin 1) R) : x * a * x⁻¹ = a := by
  have hc : x * a = a * x := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  rw [hc, mul_inv_cancel_right]

/- English proof (translation)
Simplify using `only [Pair.toQr, carry, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype, Prod.fst_mul, Prod.fst_inv]`. Rewrite using `[gl_one_conj]`. Establish `e1 : (locC G w).1 = Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom (w : G.Cˣ × ℚˣ).2` using `rfl`. Establish `e2 : ((inclG G r) ((locC G) ↑w)).1 = GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom (locC G w).1)` using `rfl`. Rewrite using `[e2, e1]`.

Simplify using `[GeneralLinearGroup.scalar]`.
-/
theorem toQr_fst_entry {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (r : ℕ) (z : Gr G r) (w : P.cent) :
    (((P.toQr r z w).1 : GL (Fin 1) (Qr p r)) : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 =
      algebraMap ℚ_[p] (Qr p r) ((((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])) := by
  simp only [Pair.toQr, carry, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype, Prod.fst_mul, Prod.fst_inv]
  rw [gl_one_conj]
  have e1 : (locC G w).1 = Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom (w : G.Cˣ × ℚˣ).2 := rfl
  have e2 : ((inclG G r) ((locC G) ↑w)).1 =
      GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom (locC G w).1) := rfl
  rw [e2, e1]
  simp [GeneralLinearGroup.scalar]

/- English proof (translation)
Introduce `p _ G P r z K g _ hK w hw`. Take `⟨m, hm0, hmem⟩` from `exists_pow_mem_conj K (KHT p G.m G.n r G.Fw) g _ hK hw`. Rewrite `hmem` using `[← map_pow]`. Take `⟨k, hk, hkeq⟩` from `hmem`. Establish `hk1 : k.1 = (P.toQr r z (w ^ m)).1`.

Establish `h` using `congrArg Prod.fst hkeq`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Prod.fst_mul, Prod.fst_inv] at h`. Rewrite using `[← h, gl_one_conj]`. Apply the tactic sequence `have hent := toQr_fst_entry P r z (w ^ m)`. Rewrite `hent` using `[← hk1]`.

Take `⟨M, hM⟩` from `(Subgroup.mem_prod.1 hk).1`. Establish `h00 : (((M : Matrix (Fin 1) (Fin 1) _) 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) r) : Qr p r) = ((k.1 : GL (Fin 1) (Qr p r)) : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0`. Rewrite using `[← hM]`. Both sides reduce to the same expression. Establish `hO : algebraMap (Qr p r) (PadicAlgCl p) (((M : Matrix (Fin 1) (Fin 1) _) 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) r) : Qr p r) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p` using `((M : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) r)) 0 0).2`.

Rewrite `hO` using `[h00, hent, ← IsScalarTower.algebraMap_apply, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff, PadicAlgCl.norm_extends]`. Establish `hpow : ((((w ^ m : P.cent) : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p]) = ((((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])) ^ m` using `by push_cast; rfl`. Rewrite `hO` using `[hpow, norm_pow]`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 hO`.
-/
theorem sim_norm_le_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r)
    (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) →
    ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom →
      ‖(((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  intro p _ G P r z K g _ hK w hw
  obtain ⟨m, hm0, hmem⟩ := exists_pow_mem_conj K (KHT p G.m G.n r G.Fw) g _ hK hw
  rw [← map_pow] at hmem
  obtain ⟨k, hk, hkeq⟩ := hmem
  have hk1 : k.1 = (P.toQr r z (w ^ m)).1 := by
    have h := congrArg Prod.fst hkeq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Prod.fst_mul, Prod.fst_inv] at h
    rw [← h, gl_one_conj]
  have hent := toQr_fst_entry P r z (w ^ m)
  rw [← hk1] at hent
  obtain ⟨M, hM⟩ := (Subgroup.mem_prod.1 hk).1
  have h00 : (((M : Matrix (Fin 1) (Fin 1) _) 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) r) : Qr p r) =
      ((k.1 : GL (Fin 1) (Qr p r)) : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 := by
    rw [← hM]; rfl
  have hO : algebraMap (Qr p r) (PadicAlgCl p)
      (((M : Matrix (Fin 1) (Fin 1) _) 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) r) : Qr p r) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p :=
    ((M : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) r)) 0 0).2
  rw [h00, hent, ← IsScalarTower.algebraMap_apply, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff,
    PadicAlgCl.norm_extends] at hO
  have hpow : ((((w ^ m : P.cent) : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p]) = ((((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])) ^ m := by
    push_cast; rfl
  rw [hpow, norm_pow] at hO
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 hO

end GlobalTheory.StabFin
