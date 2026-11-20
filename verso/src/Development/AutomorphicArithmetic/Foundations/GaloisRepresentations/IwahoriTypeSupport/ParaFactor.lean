import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

/- English proof (translation)
Introduce `k _ _ _ _ α n m _ _ _ _ _ _ e`. Prove the components needed by the constructor for the conclusion. Introduce `g`. Take `⟨x, hx⟩` from `redLevi_surjective (k := k) (m := m) (parahoricProj k e g)`. Establish `hq` using `leviEmb_mem_parahoric (k := k) e x`.

Establish `hqp` using `parahoricProj_leviEmb (k := k) e x`. Use `set q : parahoric k e := ⟨leviEmb k e (x : Levi k m), hq⟩ with hqdef`. Establish `hr : ((q⁻¹ * g : parahoric k e) : GL n k) ∈ proRad k e`. Rewrite using `[← parahoricProj_eq_one_iff, map_mul, map_inv, hqp, hx, inv_mul_cancel]`. Take `⟨u, hu, c, hc, hrc⟩` from `IwahoriFactor.exists_jPlus_mul_KOne e hr`.

Establish `huR : u ∈ unipRad k e` using `hu.1`. Establish `huP : u ∈ parab k e` using `unipRad_le_parab k e huR`. Establish `hqP : (q : GL n k) ∈ parab k e` using `leviEmb_mem_parab k e _`. Use `⟨⟨(q : GL n k) * u, mul_mem hqP huP⟩, x, ?_, ?_, hx, c, hc, ?_⟩` and prove the remaining obligations. Conclude with `mul_mem (leviEmb_mem_KO e x.2) hu.2`.

Establish `hsplit : (⟨(q : GL n k) * u, mul_mem hqP huP⟩ : parab k e) = ⟨q, hqP⟩ * ⟨u, huP⟩` using `rfl`. Rewrite using `[hsplit, map_mul, (coe_mem_unipRad k ⟨u, huP⟩).1 huR, mul_one]`. Conclude with `leviProj_leviEmb k e _`. Establish `h2 : (g : GL n k) = (q : GL n k) * ((q⁻¹ * g : parahoric k e) : GL n k)`. Simplify using the standard rewrite rules.

Rewrite using `[h2, hrc, mul_assoc]`. Introduce `p hp`. Take `⟨d, hd, u, hu, hpdu⟩` from `IwahoriFactor.exists_jLevi_mul_jPlus e p.2 hp`. Take `⟨y, hy, rfl⟩` from `Subgroup.mem_map.1 hd`. Establish `huR : u ∈ unipRad k e` using `hu.1`.

Establish `huP : u ∈ parab k e` using `unipRad_le_parab k e huR`. Establish `hdP : leviEmb k e y ∈ parab k e` using `leviEmb_mem_parab k e y`. Establish `hsplit : p = ⟨leviEmb k e y, hdP⟩ * ⟨u, huP⟩` using `Subtype.ext hpdu`. Rewrite using `[hsplit, map_mul, (coe_mem_unipRad k ⟨u, huP⟩).1 huR, mul_one, leviProj_leviEmb]`. Conclude with `hy`.
-/
theorem paraFactor : ParaFactor := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e
  constructor
  · intro g
    obtain ⟨x, hx⟩ := redLevi_surjective (k := k) (m := m) (parahoricProj k e g)
    have hq := leviEmb_mem_parahoric (k := k) e x
    have hqp := parahoricProj_leviEmb (k := k) e x
    set q : parahoric k e := ⟨leviEmb k e (x : Levi k m), hq⟩ with hqdef
    have hr : ((q⁻¹ * g : parahoric k e) : GL n k) ∈ proRad k e := by
      rw [← parahoricProj_eq_one_iff, map_mul, map_inv, hqp, hx, inv_mul_cancel]
    obtain ⟨u, hu, c, hc, hrc⟩ := IwahoriFactor.exists_jPlus_mul_KOne e hr
    have huR : u ∈ unipRad k e := hu.1
    have huP : u ∈ parab k e := unipRad_le_parab k e huR
    have hqP : (q : GL n k) ∈ parab k e := leviEmb_mem_parab k e _
    refine ⟨⟨(q : GL n k) * u, mul_mem hqP huP⟩, x, ?_, ?_, hx, c, hc, ?_⟩
    · exact mul_mem (leviEmb_mem_KO e x.2) hu.2
    · have hsplit : (⟨(q : GL n k) * u, mul_mem hqP huP⟩ : parab k e) = ⟨q, hqP⟩ * ⟨u, huP⟩ := rfl
      rw [hsplit, map_mul, (coe_mem_unipRad k ⟨u, huP⟩).1 huR, mul_one]
      exact leviProj_leviEmb k e _
    · have h2 : (g : GL n k) = (q : GL n k) * ((q⁻¹ * g : parahoric k e) : GL n k) := by
        simp
      rw [h2, hrc, mul_assoc]
  · intro p hp
    obtain ⟨d, hd, u, hu, hpdu⟩ := IwahoriFactor.exists_jLevi_mul_jPlus e p.2 hp
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hd
    have huR : u ∈ unipRad k e := hu.1
    have huP : u ∈ parab k e := unipRad_le_parab k e huR
    have hdP : leviEmb k e y ∈ parab k e := leviEmb_mem_parab k e y
    have hsplit : p = ⟨leviEmb k e y, hdP⟩ * ⟨u, huP⟩ := Subtype.ext hpdu
    rw [hsplit, map_mul, (coe_mem_unipRad k ⟨u, huP⟩).1 huR, mul_one, leviProj_leviEmb]
    exact hy

end UpperTheory.Gal.TypesAndIwahori
