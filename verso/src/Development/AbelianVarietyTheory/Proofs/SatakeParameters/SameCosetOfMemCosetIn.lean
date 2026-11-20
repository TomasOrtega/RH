import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsStd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue GlobalTheory.TwU.AtTrue.Cl
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue.Cl

open Classical in

/- English proof (translation)
Take `⟨w, hw, hzw⟩` from `hz`. Take `⟨w', hw', hzw'⟩` from `hz'`. Take `⟨y, -, hY⟩` from `p.mem_ybSet h`. Rewrite `hw`, `hw'` using `[hY]`. Establish `hww : w - w' ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))`.

Establish `e1 : w - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))` using `hw`. Establish `e2 : w' - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))` using `hw'`. Use `sub_mem e1 e2` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Establish `h1` using `(mem_locLat _ _ _ _).1 hww P`.

Use `set F := frsF sel mu p.1.1 P with hF`. Use `set c : X.E := ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ with hc`. Establish `hc' : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ = c`. Apply the tactic sequence `rw [hc]; split_ifs <;> simp`. Simplify using `only [hc'] at h1`.

Establish `hFm : ∀ x, F x ∈ p.1.1.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1`. Introduce `x`. Rewrite using `[hF]`. Unfold `frsF`. Use `split_ifs with hP`.

Conclude with `(Deco.liftFr_spec (Deco.Ok.hasLift p.1.1.deco.2 ⟨P.1, hP⟩)).1 x`. Conclude with `p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ x`. Establish `h2 : c • (F.symm w - F.symm w') ∈ stdAt X.E (R.N j) P.1`. Rewrite using `[← map_sub, ← map_smul]`. Apply `(hFm _).1` to reduce the goal to its premises.

Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `h1`. Establish `h3 : c • (z - z') = c • (z - F.symm w) - c • (z' - F.symm w') + c • (F.symm w - F.symm w')`. Rewrite using `[← smul_sub, ← smul_add]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Establish `h4 : c • (z - z') ∈ stdAt X.E (R.N j) P.1`. Rewrite using `[h3]`. Conclude with `add_mem (sub_mem hzw hzw') h2`. Introduce `l`.

Establish `h5` using `(ciMem_stdAt _ _).1 h4 l`. Rewrite `h5` using `[Pi.smul_apply, smul_eq_mul]`. Conclude with `h5`.
-/
theorem sameCoset_of_mem_cosetIn {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p : PtAt R sel mu cst u j)
    (h : j + 1 = R.m) (P : rowSG Pr sel mu) {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P) (hz' : z' ∈ cosetIn p P) :
    SameCoset sel mu cst P z z' := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨w', hw', hzw'⟩ := hz'
  obtain ⟨y, -, hY⟩ := p.mem_ybSet h
  rw [hY] at hw hw'
  have hww : w - w' ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    have e1 : w - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw
    have e2 : w' - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw'
    have := sub_mem e1 e2
    rwa [sub_sub_sub_cancel_right] at this
  have h1 := (mem_locLat _ _ _ _).1 hww P
  set F := frsF sel mu p.1.1 P with hF
  set c : X.E := ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ with hc
  have hc' : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ = c := by
    rw [hc]; split_ifs <;> simp
  simp only [hc'] at h1
  have hFm : ∀ x, F x ∈ p.1.1.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
    intro x
    rw [hF]
    unfold frsF
    split_ifs with hP
    · exact (Deco.liftFr_spec (Deco.Ok.hasLift p.1.1.deco.2 ⟨P.1, hP⟩)).1 x
    · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ x
  have h2 : c • (F.symm w - F.symm w') ∈ stdAt X.E (R.N j) P.1 := by
    rw [← map_sub, ← map_smul]
    apply (hFm _).1
    rw [LinearEquiv.apply_symm_apply]
    exact h1
  have h3 : c • (z - z') = c • (z - F.symm w) - c • (z' - F.symm w') + c • (F.symm w - F.symm w') := by
    rw [← smul_sub, ← smul_add]
    congr 1
    abel
  have h4 : c • (z - z') ∈ stdAt X.E (R.N j) P.1 := by
    rw [h3]
    exact add_mem (sub_mem hzw hzw') h2
  intro l
  have h5 := (ciMem_stdAt _ _).1 h4 l
  rw [Pi.smul_apply, smul_eq_mul] at h5
  exact h5

end GlobalTheory.TwU.AtTrue.Cl

namespace GlobalTheory.TwU.AtTrue.Cl

end GlobalTheory.TwU.AtTrue.Cl
