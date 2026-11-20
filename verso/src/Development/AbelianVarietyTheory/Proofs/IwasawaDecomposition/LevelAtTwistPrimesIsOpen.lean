import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Formalism.LocalToGlobal.Columns.ThetaOpenTwLevQ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

open Classical in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst L G m2 hL hQg j b P`. Establish `hc : cst.Ok` using `hL.cst_ok`. Set `P' : rowSG Pr sel mu` to `⟨P.1, Finset.mem_union_right _ P.2⟩`. Set `h : AutY X R j` to `L.h j b P'`. Establish `hPg` using `hQg P.1 P.2`.

Establish `hq` using `ciQ_mem P.1`. Establish `hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0`. Rewrite using `[Nat.cast_ne_zero]`. Introduce `h0`. Conclude with `P.1.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0)`.

Take `⟨a, ha⟩` from `qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)`. Take `⟨b', hb⟩` from `qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h⁻¹ : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)`. Take `⟨e, he⟩` from `qth_exists_e P.1 hq0`. Use `⟨a + b' + e + 1, by omega, fun g hg => ?_⟩` and prove the remaining obligations. Set `r : AutY X R j` to `twZrExt (c := cOf R j) g.1`.

Establish `hr` using `qth_ext_close (c := cOf R j) P.1 g.1 _ hg`. Establish `hrinv : r⁻¹ = twZrExt (c` using `cOf R j) (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 := LinearEquiv.ext fun v => rfl`. Establish `hr'` using `qth_ext_close (c := cOf R j) P.1 (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 _ (qth_princ_inv P.1 g hg)`. Establish `hy : QClose P.1 (qOf P.1) (h⁻¹ * r * h)` using `qth_conj_close P.1 (qOf P.1) h r a b' _ e ha hb hr he (by omega)`. Establish `hy' : QClose P.1 (qOf P.1) (h⁻¹ * r * h)⁻¹`.

Establish `e3 : (h⁻¹ * r * h)⁻¹ = h⁻¹ * r⁻¹ * h` using `by simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]`. Rewrite using `[e3, hrinv]`. Conclude with `qth_conj_close P.1 (qOf P.1) h _ a b' _ e ha hb hr' he (by omega)`. Establish `hJ : h⁻¹ * r * h ∈ Jat (Pr` using `Pr) (R := R) cst.sharp j P.1 := by`. Rewrite using `[twJat_Q cst.sharp j hPg]`.

Conclude with `qth_mem_JQ P.1 (qOf P.1) hq0 (R.k + j) _ hy hy'`. Establish `hC : r ∈ Loc.Cbe (Jat (Pr` using `Pr) (R := R) cst.sharp j P.1) h := by`. Use `⟨zeroExtension_mem_R1 g.1, ?_⟩` and prove the remaining obligations. Use `show (MulAut.conj h⁻¹) r ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1`. Simplify `hJ` using `[MulAut.conj_apply]`.

Establish `hmem : g.1 ∈ prCat (Pr` using `Pr) cst.sharp j P.1 h := ⟨r, hC, twZrExt_inX g.1⟩`. Establish `hH : g ∈ (L.levQ j b P).H`. Rewrite using `[hL.grpQ j b P]`. Conclude with `Subgroup.mem_subgroupOf.2 hmem`. Use `⟨hH, ?_⟩` and prove the remaining obligations.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hL.chrQ j b P ⟨g, hH⟩ r hC (fun x => twZrExt_inX g.1 x)]`. Establish `hstd : r ∈ stabL X.E (R.N j + cOf R j) (stdAt X.E (R.N j + cOf R j) P.1)` using `twZrExt_stab P.1 _ (fun v => ciMem_stdAt P.1 v) g.2`. Establish `hint : IntAt P.1 (Loc.n1Arg r)`. Unfold `Loc.n1Arg`.

Use `ciIntAt_sum _ _ fun i _ => ?_` and prove the remaining obligations. Establish `hv : r (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) ∈ stdAt X.E (R.N j + cOf R j) P.1` using `(hstd _).2 (twZr_eN_mem P.1 _ _)`. Rewrite `hv` using `[ciMem_stdAt]`. Unfold `Loc.atN`. Use `split_ifs`.

Conclude with `hv _`. Conclude with `ciIntAt_zero`. Unfold `chiInv`. Rewrite using `[hc.psi_int P' _ hint, inv_one, one_mul]`. Unfold `lamRow`.

Rewrite using `[if_neg hPg]`. Conclude with `qth_lamQB_one hq hq0 _ _ hy`.
-/
theorem thetaOpen_levQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}, L.Ok Ch sel mu cst G m2 → (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (j : ℕ) (b : L.β j), ThetaOpen (L.levQ j b) := by
  intro X Pr R Ch sel S mu cst L G m2 hL hQg j b P
  have hc : cst.Ok := hL.cst_ok
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  let h : AutY X R j := L.h j b P'
  have hPg := hQg P.1 P.2
  have hq := ciQ_mem P.1
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    exact P.1.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0)
  obtain ⟨a, ha⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨b', hb⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h⁻¹ : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨e, he⟩ := qth_exists_e P.1 hq0
  refine ⟨a + b' + e + 1, by omega, fun g hg => ?_⟩
  let r : AutY X R j := twZrExt (c := cOf R j) g.1
  have hr := qth_ext_close (c := cOf R j) P.1 g.1 _ hg
  have hrinv : r⁻¹ = twZrExt (c := cOf R j) (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 := LinearEquiv.ext fun v => rfl
  have hr' := qth_ext_close (c := cOf R j) P.1 (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 _ (qth_princ_inv P.1 g hg)
  have hy : QClose P.1 (qOf P.1) (h⁻¹ * r * h) := qth_conj_close P.1 (qOf P.1) h r a b' _ e ha hb hr he (by omega)
  have hy' : QClose P.1 (qOf P.1) (h⁻¹ * r * h)⁻¹ := by
    have e3 : (h⁻¹ * r * h)⁻¹ = h⁻¹ * r⁻¹ * h := by simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e3, hrinv]
    exact qth_conj_close P.1 (qOf P.1) h _ a b' _ e ha hb hr' he (by omega)
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1 := by
    rw [twJat_Q cst.sharp j hPg]
    exact qth_mem_JQ P.1 (qOf P.1) hq0 (R.k + j) _ hy hy'
  have hC : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := R) cst.sharp j P.1) h := by
    refine ⟨zeroExtension_mem_R1 g.1, ?_⟩
    show (MulAut.conj h⁻¹) r ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1
    simpa [MulAut.conj_apply] using hJ
  have hmem : g.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 h := ⟨r, hC, twZrExt_inX g.1⟩
  have hH : g ∈ (L.levQ j b P).H := by
    rw [hL.grpQ j b P]
    exact Subgroup.mem_subgroupOf.2 hmem
  refine ⟨hH, ?_⟩
  apply Units.ext
  rw [hL.chrQ j b P ⟨g, hH⟩ r hC (fun x => twZrExt_inX g.1 x)]
  have hstd : r ∈ stabL X.E (R.N j + cOf R j) (stdAt X.E (R.N j + cOf R j) P.1) :=
    twZrExt_stab P.1 _ (fun v => ciMem_stdAt P.1 v) g.2
  have hint : IntAt P.1 (Loc.n1Arg r) := by
    unfold Loc.n1Arg
    refine ciIntAt_sum _ _ fun i _ => ?_
    have hv : r (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) ∈ stdAt X.E (R.N j + cOf R j) P.1 :=
      (hstd _).2 (twZr_eN_mem P.1 _ _)
    rw [ciMem_stdAt] at hv
    unfold Loc.atN
    split_ifs
    · exact hv _
    · exact ciIntAt_zero
  unfold chiInv
  rw [hc.psi_int P' _ hint, inv_one, one_mul]
  unfold lamRow
  rw [if_neg hPg]
  exact qth_lamQB_one hq hq0 _ _ hy

end GlobalTheory.Mem.Col2.ChEx
