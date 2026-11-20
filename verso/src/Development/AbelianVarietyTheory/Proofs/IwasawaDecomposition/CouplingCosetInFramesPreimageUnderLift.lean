import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open Classical GlobalTheory.TopStep in

/- English proof (translation)
Establish `hq0 : (qOf P : E) ≠ 0` using `qOf_ne_zero`. Establish `hk0` using `glint_mem m hx`. Use `mem_stdAt.2 fun j => ?_` and prove the remaining obligations. Establish `hi1` using `mem_stdAt.1 hk0 j`. Establish `hi2` using `mem_stdAt.1 hx j`.

Establish `hr : redP P ((m.1 ((qOf P : E) • x) - (qOf P : E) • x) j) = 0`. Rewrite using `[Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]`. Conclude with `congrFun (hred _ hx) j`. Use `intAt_div_of_redP hq (intAt_sub hi1 hi2) hr` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[LinearEquiv.map_smul]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem sub_mem_stdAt_of_redV {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (m : GLint E n P) (x : Sp E n)
    (hx : (qOf P : E) • x ∈ stdAt E n P) (hred : ∀ v ∈ stdAt E n P, redV P (m.1 v) = redV P v) :
    m.1 x - x ∈ stdAt E n P := by
  have hq0 : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hk0 := glint_mem m hx
  refine mem_stdAt.2 fun j => ?_
  have hi1 := mem_stdAt.1 hk0 j
  have hi2 := mem_stdAt.1 hx j
  have hr : redP P ((m.1 ((qOf P : E) • x) - (qOf P : E) • x) j) = 0 := by
    rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
    exact congrFun (hred _ hx) j
  have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
  convert this using 1
  rw [LinearEquiv.map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

set_option maxHeartbeats 1600000 in
open Classical GlobalTheory.TopStep in

/- English proof (translation)
Introduce `B X I _ u a i b κ p P g hgam hL z`. Establish `hX : B.fields.Ok` using `GlobalTheory.Mem.FieldsLaws.fields_ok B`. Establish `hPr : (B.primes X).Ok` using `(GlobalTheory.BasePrimes.primes_ok B X).1`. Take `⟨γ, h, c⟩` from `κ`. Establish `hγ : γ = 1`.

Establish `e : ufGL B.fields.E (B.R.N i) γ = 1` using `hgam`. Establish `e2 : (toGLm B.fields.E (B.R.N i)) γ.1 = (toGLm B.fields.E (B.R.N i)) 1`. Rewrite using `[map_one]`. Conclude with `e`. Conclude with `Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective e2)`.

Substitute `hγ` using the available equality. Use `set p' := (I.stp u a i).act b ((1 : UF B.fields.E (B.R.N i)), h, c) p with hp'`. Establish `hys : p'.1.2 = p.1.2` using `by show (fun v => ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) v) '' p.1.2 = p.1.2`. Simplify using the standard rewrite rules. Establish `hg : ∀ x, g x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1` using `hL.1`.

Establish `key : ∀ y ∈ p.1.2, ((qOf P.1 : B.fields.E) ^ (if P.1 ∈ (B.primes X).vGs then 0 else (I.cst a).M))⁻¹ • (g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈ stdAt B.fields.E (B.R.N i) P.1`. Introduce `y hy`. Distinguish the cases in `hP : P.1 ∈ (B.primes X).vGs`. Rewrite using `[if_pos hP, pow_zero, inv_one, one_smul]`. Distinguish the cases in `hj : i + 1 = B.R.m`.

Use `swap`. Establish `h0 : p.1.2 = ∅`. Use `p.2` as an intermediate fact. Rewrite `this` using `[ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj]`. Conclude with `this`.

Rewrite `hy` using `[h0]`. Conclude with `absurd hy (Set.notMem_empty y)`. Take `⟨y0, hy0, hY⟩` from `PtAt.mem_ybSet p hj`. Establish `hy' : y - y0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) p.1.1.deco.1.N (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ))`. Rewrite `hy` using `[hY]`.

Conclude with `hy`. Establish `hA : (qOf P.1 : B.fields.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N`. Use `Submodule.mem_iInf _ |>.1 hy0 P` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap]`. Simplify `this` using `[hP]`.

Establish `hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N`. Use `Submodule.mem_iInf _ |>.1 hy' P` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap]`. Simplify `this` using `[hP]`. Establish `hx : (qOf P.1 : B.fields.E) • y ∈ p.1.1.deco.1.at P.1`.

Establish `e : (qOf P.1 : B.fields.E) • y = (qOf P.1 : B.fields.E) • y0 + (qOf P.1 : B.fields.E) • (y - y0)`. Rewrite using `[← smul_add, add_sub_cancel]`. Rewrite using `[e]`. Conclude with `add_mem hA (smul_mem_locP (intAt_nat _) hB)`. Set `w : (B.primes X).vGs` to `⟨P.1, hP⟩`.

Establish `hd : p'.1.1.deco.1 = p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1` using `rfl`. Establish `hf : IsLiftFr p.1.1.deco.1 w (p.1.1.deco.1.liftFr w)` using `liftFr_spec p.1.1.deco.2 w`. Establish `hf' : IsLiftFr (p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1) w (p'.1.1.deco.1.liftFr w)`. Rewrite using `[← hd]`. Conclude with `liftFr_spec p'.1.1.deco.2 w`.

Establish `e1 : frsF I.sel (I.tup a) p.1.1 P = p.1.1.deco.1.liftFr w`. Unfold `frsF`. Rewrite using `[dif_pos hP]`. Establish `e2 : frsF I.sel (I.tup a) p'.1.1 P = p'.1.1.deco.1.liftFr w`. Unfold `frsF`.

Rewrite using `[dif_pos hP]`. Rewrite using `[e1, e2]`. Establish `e3 : (p'.1.1.deco.1.liftFr w).symm y = (passFr (w` using `w) _ h.1 hf hf').1 ((p.1.1.deco.1.liftFr w).symm y) := by show _ = (p'.1.1.deco.1.liftFr w).symm (((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) ((p.1.1.deco.1.liftFr w) ((p.1.1.deco.1.liftFr w).symm y)))`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Rewrite using `[e3]`. Establish `hv0 : (qOf P.1 : B.fields.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt B.fields.E (B.R.N i) P.1`. Rewrite using `[← LinearEquiv.map_smul, ← hf.1, LinearEquiv.apply_symm_apply]`. Conclude with `hx`. Establish `hκ : GlobalTheory.TopStep.redGL (B.R.N i) P.1 (passFr (w` using `w) _ h.1 hf hf') = h.1 w := redGL_passFr (w := w) _ h.1 hf hf'`.

Establish `hq` using `(degOneUnram_of_mem_vGs hX hPr hP).2`. Establish `hred : ∀ v ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g ((passFr (w` using `w) _ h.1 hf hf').1 v)) = redV P.1 v := by`. Introduce `v hv`. Rewrite using `[hL.2.1 hP _ (glint_mem _ hv), redV_redGL _ hv, hκ, Matrix.mulVec_mulVec]`. Use `show ((h.1 w)⁻¹.1 * (h.1 w).1).mulVec _ = _`.

Rewrite using `[Units.inv_mul, Matrix.one_mulVec]`. Establish `hm` using `sub_mem_stdAt_of_redV P.1 hq (⟨g, hL.1⟩ * passFr (w := w) _ h.1 hf hf') _ hv0 hred`. Conclude with `hm`. Rewrite using `[if_neg hP]`. Establish `hQ : P.1 ∈ I.Q a` using `(Finset.mem_union.mp P.2).resolve_left hP`.

Establish `hF' : frsF I.sel (I.tup a) p'.1.1 P = frsF I.sel (I.tup a) p.1.1 P * g`. Unfold `frsF`. Rewrite using `[dif_neg hP, dif_neg hP, hL.2.2 hQ]`. Conclude with `LinearEquiv.ext fun x => rfl`. Establish `e : g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) = (frsF I.sel (I.tup a) p.1.1 P).symm y`.

Rewrite using `[eq_comm, LinearEquiv.symm_apply_eq]`. Rewrite using `[hF']`. Conclude with `((frsF I.sel (I.tup a) p.1.1 P * g).apply_symm_apply y).symm`. Rewrite using `[e, sub_self, smul_zero]`. Conclude with `zero_mem _`.

Simplify using `only [cosetIn, Set.mem_ofPred_eq]`. Rewrite using `[hys]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hz⟩`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Use `add_mem ((hg _).2 hz) (key y hy)` as an intermediate fact. Rewrite `this` using `[map_smul, map_sub, ← smul_add, sub_add_sub_cancel]`. Then use the resulting hypothesis. Introduce and unpack `⟨y, hy, hz⟩`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Use `sub_mem hz (key y hy)` as an intermediate fact.

Rewrite `this` using `[← smul_sub, sub_sub_sub_cancel_right, ← map_sub, ← map_smul]`. Conclude with `(hg _).1 this`.
-/
theorem cosetIn_act_of_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), (I.stp u a i).gam b κ = 1 → LiftsInv I κ P g → ∀ z, z ∈ cosetIn ((I.stp u a i).act b κ p) P ↔ g z ∈ cosetIn p P := by
  intro B X I _ u a i b κ p P g hgam hL z
  have hX : B.fields.Ok := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hPr : (B.primes X).Ok := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨γ, h, c⟩ := κ
  have hγ : γ = 1 := by
    have e : ufGL B.fields.E (B.R.N i) γ = 1 := hgam
    have e2 : (toGLm B.fields.E (B.R.N i)) γ.1 = (toGLm B.fields.E (B.R.N i)) 1 := by
      rw [map_one]; exact e
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective e2)
  subst hγ
  set p' := (I.stp u a i).act b ((1 : UF B.fields.E (B.R.N i)), h, c) p with hp'
  have hys : p'.1.2 = p.1.2 := by
    show (fun v => ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) v) '' p.1.2 = p.1.2
    simp
  have hg : ∀ x, g x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := hL.1
  have key : ∀ y ∈ p.1.2, ((qOf P.1 : B.fields.E) ^ (if P.1 ∈ (B.primes X).vGs then 0 else (I.cst a).M))⁻¹ •
      (g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : i + 1 = B.R.m
      swap
      · have h0 : p.1.2 = ∅ := by
          have := p.2
          rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet p hj
      have hy' : y - y0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) p.1.1.deco.1.N
          (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : B.fields.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : B.fields.E) • y ∈ p.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : B.fields.E) • y = (qOf P.1 : B.fields.E) • y0 + (qOf P.1 : B.fields.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : (B.primes X).vGs := ⟨P.1, hP⟩
      have hd : p'.1.1.deco.1 = p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1 := rfl
      have hf : IsLiftFr p.1.1.deco.1 w (p.1.1.deco.1.liftFr w) := liftFr_spec p.1.1.deco.2 w
      have hf' : IsLiftFr (p.1.1.deco.1.act ((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) h.1) w (p'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec p'.1.1.deco.2 w
      have e1 : frsF I.sel (I.tup a) p.1.1 P = p.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dif_pos hP]
      have e2 : frsF I.sel (I.tup a) p'.1.1 P = p'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dif_pos hP]
      rw [e1, e2]
      have e3 : (p'.1.1.deco.1.liftFr w).symm y = (passFr (w := w) _ h.1 hf hf').1 ((p.1.1.deco.1.liftFr w).symm y) := by
        show _ = (p'.1.1.deco.1.liftFr w).symm (((1 : UF B.fields.E (B.R.N i)) : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) ((p.1.1.deco.1.liftFr w) ((p.1.1.deco.1.liftFr w).symm y)))
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [e3]
      have hv0 : (qOf P.1 : B.fields.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        rw [← LinearEquiv.map_smul, ← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      have hκ : GlobalTheory.TopStep.redGL (B.R.N i) P.1 (passFr (w := w) _ h.1 hf hf') = h.1 w := redGL_passFr (w := w) _ h.1 hf hf'
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hred : ∀ v ∈ stdAt B.fields.E (B.R.N i) P.1, redV P.1 (g ((passFr (w := w) _ h.1 hf hf').1 v)) = redV P.1 v := by
        intro v hv
        rw [hL.2.1 hP _ (glint_mem _ hv), redV_redGL _ hv, hκ, Matrix.mulVec_mulVec]
        show ((h.1 w)⁻¹.1 * (h.1 w).1).mulVec _ = _
        rw [Units.inv_mul, Matrix.one_mulVec]
      have hm := sub_mem_stdAt_of_redV P.1 hq (⟨g, hL.1⟩ * passFr (w := w) _ h.1 hf hf') _ hv0 hred
      exact hm
    · rw [if_neg hP]
      have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      have hF' : frsF I.sel (I.tup a) p'.1.1 P = frsF I.sel (I.tup a) p.1.1 P * g := by
        unfold frsF
        rw [dif_neg hP, dif_neg hP, hL.2.2 hQ]
        exact LinearEquiv.ext fun x => rfl
      have e : g ((frsF I.sel (I.tup a) p'.1.1 P).symm y) = (frsF I.sel (I.tup a) p.1.1 P).symm y := by
        rw [eq_comm, LinearEquiv.symm_apply_eq]
        rw [hF']
        exact ((frsF I.sel (I.tup a) p.1.1 P * g).apply_symm_apply y).symm
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  simp only [cosetIn, Set.mem_ofPred_eq]
  rw [hys]
  constructor
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem ((hg _).2 hz) (key y hy)
    rwa [map_smul, map_sub, ← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have := sub_mem hz (key y hy)
    rw [← smul_sub, sub_sub_sub_cancel_right, ← map_sub, ← map_smul] at this
    exact (hg _).1 this

end GlobalTheory.Mem.Col2.AdT

end
