import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSumOfNoConj
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec

noncomputable section

namespace Formalism.IndefR.FWT

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intVec (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

end Gen

section Map

open MvPolynomial

end Map

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

/- English proof (translation)
Use `Finset.eq_empty_of_forall_notMem fun PP hPP => ?_` and prove the remaining obligations. Establish `h` using `(hL.Q_ram A.μ0 PP).2 (Or.inl hPP)`. Rewrite `h` using `[hL.xi_base]`. Conclude with `h fun x _ => rfl`.
-/
theorem Q_base_empty (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h := (hL.Q_ram A.μ0 PP).2 (Or.inl hPP)
  rw [hL.xi_base] at h
  exact h fun x _ => rfl

section Phi

variable (R : RealDat D A Ks) (i : Fin D.R.m) {K' : Type} [Field K'] (σ' : K' →+* ℂ) (t : T0)
  {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
  (N : Submodule (𝓞 D.host.E) La)

def phiVal (e : AE D) (x : Fin (Vc D i).rank → La) : ℂ :=
  omegaK R.Pg (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b))) *
    omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1)
      (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)))

end Phi

section Reps

variable (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

def LemmaR (bad : ℕ) : Prop :=
  ∃ (Cl : Type) (_ : Fintype Cl) (h : Cl → GA D (Vc D i)),
    Bridge.IsReps (Bridge.ratF (Vc D i)) (levJ R i t) (fun k => fin _ (h k)) ∧ ∀ k, SplitOffBad (Vc D i) bad (h k)

end Reps

section Place

variable (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  {K' : Type} [Field K'] {jL : D.what₂.LL →+* K'} {σ' : K' →+* ℂ}

/- English proof (translation)
Unfold `Formalism.L2.DIV.levFn`. Simplify using `only [Units.val_mul, Units.coe_prod]`. Use `S.mul_mem (S.mul_mem ?_ (S.prod_mem fun PP hPP => S.prod_mem fun c _ => hcg _ _ hPP _)) (S.prod_mem fun PP hPP => hxq _ hPP _)` and prove the remaining obligations. Unfold `Formalism.L2.DIV.ext1`. Use `split_ifs`.

Establish `e : (Lev.flag1L L).P.chi = 1` using `rfl`. Rewrite using `[e, MonoidHom.one_apply, Units.val_one]`. Conclude with `S.one_mem`. Simplify using `only [Units.val_one]`. Conclude with `S.one_mem`.
-/
theorem levFn_flag1_mem {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (S : Subfield ℂ)
    (hcg : ∀ c, ∀ PP ∈ L.Pg, ∀ u, ((L.cg c PP u : ℂˣ) : ℂ) ∈ S) (hxq : ∀ PP ∈ L.Q, ∀ u, ((L.xq PP u : ℂˣ) : ℂ) ∈ S)
    (x : GL (Fin n) (Lev.EAf D)) :
    ((Formalism.L2.DIV.levFn β (Lev.flag1L L) x : ℂˣ) : ℂ) ∈ S := by
  unfold Formalism.L2.DIV.levFn
  simp only [Units.val_mul, Units.coe_prod]
  refine S.mul_mem (S.mul_mem ?_ (S.prod_mem fun PP hPP => S.prod_mem fun c _ => hcg _ _ hPP _))
    (S.prod_mem fun PP hPP => hxq _ hPP _)
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · have e : (Lev.flag1L L).P.chi = 1 := rfl
    rw [e, MonoidHom.one_apply, Units.val_one]
    exact S.one_mem
  · simp only [Units.val_one]
    exact S.one_mem

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `k`. Establish `hcg : ∀ c, ∀ PP ∈ (R.toLevCh.datVt i t).Pg, ∀ u, (((R.toLevCh.datVt i t).cg c PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange`. Introduce `c PP hPP u`. Establish `e : (R.toLevCh.datVt i t).cg c PP u = (R.chi ((i : ℕ) + 1) PP u)⁻¹`. Simplify using `[LevCh.datVt, Lev.datY]`.

Rewrite using `[e, Units.val_inv_eq_inv_val]`. Take `⟨a, ha⟩` from `hchi PP hPP u`. Conclude with `Subfield.inv_mem _ ⟨a, ha.symm⟩`. Establish `hxq : ∀ PP ∈ (R.toLevCh.datVt i t).Q, ∀ u, (((R.toLevCh.datVt i t).xq PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange`. Introduce `PP hPP u`.

Establish `e : (R.toLevCh.datVt i t).xq PP u = R.xiR t PP u`. Simplify using `[LevCh.datVt, Lev.datY]`. Rewrite using `[e]`. Take `⟨a, ha⟩` from `hxi PP hPP u`. Conclude with `⟨a, ha.symm⟩`.

Take `⟨a, ha⟩` from `levFn_flag1_mem (R.βV i) (R.toLevCh.datVt i t) D.what₂.embLL.fieldRange hcg hxq _`. Conclude with `⟨a, ha.symm⟩`.
-/
theorem hχ_of (hchi : ∀ PP ∈ R.Pg, ∀ u, ∃ a, ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = D.what₂.embLL a)
    (hxi : ∀ PP ∈ R.Q t, ∀ u, ∃ a, ((R.xiR t PP u : ℂˣ) : ℂ) = D.what₂.embLL a) :
    ∀ k, ∃ a, (((levEnvOf (Vc D i) (R.βV i) (R.toLevCh.datVt i t) R.pl (A.ok t)).lev.χ k : ℂˣ) : ℂ) = D.what₂.embLL a := by
  intro k
  have hcg : ∀ c, ∀ PP ∈ (R.toLevCh.datVt i t).Pg, ∀ u,
      (((R.toLevCh.datVt i t).cg c PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    intro c PP hPP u
    have e : (R.toLevCh.datVt i t).cg c PP u = (R.chi ((i : ℕ) + 1) PP u)⁻¹ := by
      simp [LevCh.datVt, Lev.datY]
    rw [e, Units.val_inv_eq_inv_val]
    obtain ⟨a, ha⟩ := hchi PP hPP u
    exact Subfield.inv_mem _ ⟨a, ha.symm⟩
  have hxq : ∀ PP ∈ (R.toLevCh.datVt i t).Q, ∀ u,
      (((R.toLevCh.datVt i t).xq PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    intro PP hPP u
    have e : (R.toLevCh.datVt i t).xq PP u = R.xiR t PP u := by
      simp [LevCh.datVt, Lev.datY]
    rw [e]
    obtain ⟨a, ha⟩ := hxi PP hPP u
    exact ⟨a, ha.symm⟩
  obtain ⟨a, ha⟩ := levFn_flag1_mem (R.βV i) (R.toLevCh.datVt i t) D.what₂.embLL.fieldRange hcg hxq _
  exact ⟨a, ha.symm⟩

end Place

section Assemble

end Assemble

end Formalism.IndefR.FWT

end
