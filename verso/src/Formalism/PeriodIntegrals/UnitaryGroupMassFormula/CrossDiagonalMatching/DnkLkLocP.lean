import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Common
import Formalism.LocalToGlobal.GlobalTheory.GL6.PKerAtP

noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Establish `hLd` using `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.dual_class_lattice_eq_global T.cls0 c`. Establish `hfin` using `tld_isLat (u := u) 0 (Nat.zero_le _) c`. Establish `hone` using `Formalism.L2.GlobalTheoryTheory.Comp.glob_one (F := D.host.F) hfin`. Establish `hdl : ∀ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb, ((D.mem u).A.T : ℕ) • x ∈ T.cls0.lev.Lb`.

Introduce `x hx`. Unfold `Formalism.L2.GlobalTheoryTheory.Comp.dl at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => rw [← Nat.cast_smul_eq_nsmul D.host.E]`. Conclude with `T.cls0.lev.Lb_dual x hx`.

Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ ihx ihy => rw [smul_add]`. Conclude with `add_mem ihx ihy`. Consider the case `smul a x _ ih => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ a ih`. Establish `hkey : ∀ w ∈ latS (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb), ((D.mem u).A.T : ℕ) • w ∈ latS (F := …`. Introduce `w hw`. Unfold `latS at hw ⊢`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨x, hx, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨_, hdl x hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, map_nsmul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ ihx ihy => rw [smul_add]`. Conclude with `add_mem ihx ihy`.

Consider the case `smul a x _ ih => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ a ih`. Establish `hmem : ∀ (g : GL (Fin (D.R.N 0)) (TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) (Λ : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (x : Fin (D.R.N 0) → D.host.E), x ∈ Formalism.UG.CS.globLat g Λ ↔ ((g⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ (fun i => inclE …` using `D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) Λ := fun _ _ _ => Iff.rfl`. Rewrite `hy` using `[hLd, hmem]`. Rewrite using `[← hone, hmem, inv_one, Units.val_one, Matrix.one_mulVec, T.cls0.y_lat c]`.

Establish `e : (fun i => inclE (F` using `D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ((((D.mem u).A.T : ℕ) • y) i)) = ((D.mem u).A.T : ℕ) • (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (y i)) := by`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, map_nsmul]`. Rewrite using `[e, Matrix.mulVec_smul]`. Conclude with `hkey _ hy`.
-/
theorem dnk_tld (T : Forms0 D u) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → D.host.E)
    (hy : y ∈ Ld D u 0 (Nat.zero_le _) c) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y ∈ clsCrd D u 0 (Nat.zero_le _) c := by
  rw [Nat.cast_smul_eq_nsmul]
  have hLd := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.dual_class_lattice_eq_global T.cls0 c
  have hfin := tld_isLat (u := u) 0 (Nat.zero_le _) c
  have hone := Formalism.L2.GlobalTheoryTheory.Comp.glob_one (F := D.host.F) hfin
  have hdl : ∀ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb,
      ((D.mem u).A.T : ℕ) • x ∈ T.cls0.lev.Lb := by
    intro x hx
    unfold Formalism.L2.GlobalTheoryTheory.Comp.dl at hx
    induction hx using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact T.cls0.lev.Lb_dual x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ ihx ihy => rw [smul_add]; exact add_mem ihx ihy
    | smul a x _ ih => rw [smul_comm]; exact Submodule.smul_mem _ a ih
  have hkey : ∀ w ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb),
      ((D.mem u).A.T : ℕ) • w ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) T.cls0.lev.Lb := by
    intro w hw
    unfold latS at hw ⊢
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨_, hdl x hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, map_nsmul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ ihx ihy => rw [smul_add]; exact add_mem ihx ihy
    | smul a x _ ih => rw [smul_comm]; exact Submodule.smul_mem _ a ih
  have hmem : ∀ (g : GL (Fin (D.R.N 0)) (TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Λ : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (x : Fin (D.R.N 0) → D.host.E),
      x ∈ Formalism.UG.CS.globLat g Λ ↔ ((g⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ
        (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) Λ :=
    fun _ _ _ => Iff.rfl
  rw [hLd, hmem] at hy
  rw [← hone, hmem, inv_one, Units.val_one, Matrix.one_mulVec, T.cls0.y_lat c]
  have e : (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ((((D.mem u).A.T : ℕ) • y) i)) =
      ((D.mem u).A.T : ℕ) • (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (y i)) := by
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  rw [e, Matrix.mulVec_smul]
  exact hkey _ hy

/- English proof (translation)
The claim follows from `sup_le (cls_le_ld T c) Submodule.smul_le_right`.
-/
theorem dnk_lk_le (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    Lk T.atT 0 (Nat.zero_le _) v c ≤ Ld D u 0 (Nat.zero_le _) c := sup_le (cls_le_ld T c) Submodule.smul_le_right

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `x hx`. Establish `hx' : ∃ s ∈ (T.atT.Pv v).primeCompl, s • x ∈ Lk T.atT 0 (Nat.zero_le _) v c` using `hx`. Take `⟨s, hs, hsx⟩` from `hx'`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp hsx`. Take `⟨t, ht, y, hy, hty⟩` from `exists_smul_eq_smul_of_mem_ideal_smul T.atT v (Ld D u 0 (Nat.zero_le _) c) b hb`.

Use `show ∃ r ∈ (T.atT.Pv v).primeCompl, r • x ∈ clsCrd D u 0 (Nat.zero_le _) c`. Use `⟨t * s, Submonoid.mul_mem _ (Ideal.mem_primeCompl_iff.mpr ht) hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← hab, smul_add, hty]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ t ha) (dnk_tld T c y hy)`.
-/
theorem dnk_lk_locP (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Lk T.atT 0 (Nat.zero_le _) v c) ≤
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
  intro x hx
  have hx' : ∃ s ∈ (T.atT.Pv v).primeCompl, s • x ∈ Lk T.atT 0 (Nat.zero_le _) v c := hx
  obtain ⟨s, hs, hsx⟩ := hx'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsx
  obtain ⟨t, ht, y, hy, hty⟩ := exists_smul_eq_smul_of_mem_ideal_smul T.atT v (Ld D u 0 (Nat.zero_le _) c) b hb
  show ∃ r ∈ (T.atT.Pv v).primeCompl, r • x ∈ clsCrd D u 0 (Nat.zero_le _) c
  refine ⟨t * s, Submonoid.mul_mem _ (Ideal.mem_primeCompl_iff.mpr ht) hs, ?_⟩
  rw [mul_smul, ← hab, smul_add, hty]
  exact Submodule.add_mem _ (Submodule.smul_mem _ t ha) (dnk_tld T c y hy)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `memP : ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E), z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) L ↔ ∃ s ∈ (T.atT.Pv v).primeCompl, s • z ∈ L` using `fun _ _ => Iff.rfl`. Establish `memM : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E), z ∈ mulLat M L ↔ ∃ x ∈ L, M *ᵥ x = z` using `fun _ _ _ => Iff.rfl`. Establish `hsm : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (t : 𝓞 D.host.E) (x : Fin (D.R.N 0) → D.host.E), M *ᵥ (t • x) = t • (M *ᵥ x)` using `fun M t x => Matrix.mulVec_smul M t x`. Establish `hPc : ∀ {a b : 𝓞 D.host.E}, a ∈ (T.atT.Pv v).primeCompl → b ∈ (T.atT.Pv v).primeCompl → a * b ∈ (T.atT.Pv v).primeCompl` using `fun ha hb => Submonoid.mul_mem _ ha hb`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨s, hs, hsy⟩` from `(memP _ _).mp hy`. Take `⟨x, hx, hxy⟩` from `(memM _ _ _).mp hsy`. Establish `hxd : x ∈ Ld D u 0 (Nat.zero_le _) c1` using `dnk_lk_le T v c1 hx`. Establish `h1 : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c)`.

Rewrite using `[← hl]`. Conclude with `(memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨x, hxd, rfl⟩⟩`. Take `⟨t, ht, htx⟩` from `(memP _ _).mp h1`. Establish `htx' : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (t • x) ∈ Lk T.atT 0 (Nat.zero_le _) v c`. Rewrite using `[hsm]`.

Conclude with `Submodule.mem_sup_left htx`. Establish `hfx : (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨t • x, Submodule.smul_mem _ t hxd⟩) = 0` using `(T.lv0.fv_ker v c1 _).mpr (Submodule.smul_mem _ t hx)`. Establish `hmem : (t * s) • y ∈ Lk T.atT 0 (Nat.zero_le _) v c`. Rewrite using `[mul_smul, ← hxy, ← hsm]`. Conclude with `htx'`.

Use `⟨t * s, Ideal.mem_primeCompl_iff.mp (hPc ht hs), hmem, ?_⟩` and prove the remaining obligations. Establish `e : (⟨(t * s) • y, hmem⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, htx'⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (t * s) • y = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (t • x)`. Rewrite using `[mul_smul, ← hxy, hsm]`.

Rewrite using `[e]`. Conclude with `(hfun ⟨t • x, Submodule.smul_mem _ t hxd⟩ htx').symm.trans hfx`. Introduce and unpack `⟨s, hs, hsy, hg⟩`. Establish `h1 : s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c)` using `dnk_lk_locP T v c ((memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hsy⟩)`. Rewrite `h1` using `[← hl]`.

Take `⟨t, ht, htm⟩` from `(memP _ _).mp h1`. Take `⟨x, hx, hxe⟩` from `(memM _ _ _).mp htm`. Establish `hxk : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Lk T.atT 0 (Nat.zero_le _) v c`. Rewrite using `[hxe]`. Conclude with `Submodule.smul_mem _ t hsy`.

Establish `hf : (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨x, hx⟩) = g (T.lv0.prk v c ⟨_, hxk⟩)` using `hfun ⟨x, hx⟩ hxk`. Establish `e : (⟨_, hxk⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = t • ⟨s • y, hsy⟩` using `Subtype.ext hxe`. Rewrite `hf` using `[e, T.lv0.prk_smul, map_smul, hg, smul_zero]`. Establish `hxk1 : x ∈ Lk T.atT 0 (Nat.zero_le _) v c1` using `(T.lv0.fv_ker v c1 ⟨x, hx⟩).mp hf`. Conclude with `(memP _ _).mpr ⟨t * s, hPc ht (Ideal.mem_primeCompl_iff.mpr hs), (memM _ _ _).mpr ⟨x, hxk1, by rw [hxe, mul_smul]⟩⟩`.
-/
theorem dnk_char (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (y : Fin (D.R.N 0) → D.host.E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) ↔
      ∃ s : 𝓞 D.host.E, s ∉ T.atT.Pv v ∧ ∃ h : s • y ∈ Lk T.atT 0 (Nat.zero_le _) v c,
        g (T.lv0.prk v c ⟨_, h⟩) = 0 := by
  have memP : ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) L ↔ ∃ s ∈ (T.atT.Pv v).primeCompl, s • z ∈ L := fun _ _ => Iff.rfl
  have memM : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ mulLat M L ↔ ∃ x ∈ L, M *ᵥ x = z := fun _ _ _ => Iff.rfl
  have hsm : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (t : 𝓞 D.host.E) (x : Fin (D.R.N 0) → D.host.E), M *ᵥ (t • x) = t • (M *ᵥ x) :=
    fun M t x => Matrix.mulVec_smul M t x
  have hPc : ∀ {a b : 𝓞 D.host.E}, a ∈ (T.atT.Pv v).primeCompl → b ∈ (T.atT.Pv v).primeCompl →
      a * b ∈ (T.atT.Pv v).primeCompl := fun ha hb => Submonoid.mul_mem _ ha hb
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := (memP _ _).mp hy
    obtain ⟨x, hx, hxy⟩ := (memM _ _ _).mp hsy
    have hxd : x ∈ Ld D u 0 (Nat.zero_le _) c1 := dnk_lk_le T v c1 hx
    have h1 : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
      rw [← hl]
      exact (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨x, hxd, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp h1
    have htx' : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (t • x) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [hsm]; exact Submodule.mem_sup_left htx
    have hfx : (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨t • x, Submodule.smul_mem _ t hxd⟩) = 0 :=
      (T.lv0.fv_ker v c1 _).mpr (Submodule.smul_mem _ t hx)
    have hmem : (t * s) • y ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [mul_smul, ← hxy, ← hsm]; exact htx'
    refine ⟨t * s, Ideal.mem_primeCompl_iff.mp (hPc ht hs), hmem, ?_⟩
    have e : (⟨(t * s) • y, hmem⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, htx'⟩ := by
      apply Subtype.ext
      show (t * s) • y = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (t • x)
      rw [mul_smul, ← hxy, hsm]
    rw [e]
    exact (hfun ⟨t • x, Submodule.smul_mem _ t hxd⟩ htx').symm.trans hfx
  · rintro ⟨s, hs, hsy, hg⟩
    have h1 : s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
      dnk_lk_locP T v c ((memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hsy⟩)
    rw [← hl] at h1
    obtain ⟨t, ht, htm⟩ := (memP _ _).mp h1
    obtain ⟨x, hx, hxe⟩ := (memM _ _ _).mp htm
    have hxk : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [hxe]; exact Submodule.smul_mem _ t hsy
    have hf : (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨x, hx⟩) = g (T.lv0.prk v c ⟨_, hxk⟩) := hfun ⟨x, hx⟩ hxk
    have e : (⟨_, hxk⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = t • ⟨s • y, hsy⟩ := Subtype.ext hxe
    rw [e, T.lv0.prk_smul, map_smul, hg, smul_zero] at hf
    have hxk1 : x ∈ Lk T.atT 0 (Nat.zero_le _) v c1 := (T.lv0.fv_ker v c1 ⟨x, hx⟩).mp hf
    exact (memP _ _).mpr ⟨t * s, hPc ht (Ideal.mem_primeCompl_iff.mpr hs),
      (memM _ _ _).mpr ⟨x, hxk1, by rw [hxe, mul_smul]⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `memP : ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E), z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) L ↔ ∃ s ∈ (T.atT.Pv v).primeCompl, s • z ∈ L` using `fun _ _ => Iff.rfl`. Establish `memM : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E), z ∈ mulLat M L ↔ ∃ x ∈ L, M *ᵥ x = z` using `fun _ _ _ => Iff.rfl`. Establish `hsm : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (t : 𝓞 D.host.E) (x : Fin (D.R.N 0) → D.host.E), M *ᵥ (t • x) = t • (M *ᵥ x)` using `fun M t x => Matrix.mulVec_smul M t x`. Establish `hPc : ∀ {a b : 𝓞 D.host.E}, a ∈ (T.atT.Pv v).primeCompl → b ∈ (T.atT.Pv v).primeCompl → a * b ∈ (T.atT.Pv v).primeCompl` using `fun ha hb => Submonoid.mul_mem _ ha hb`. Establish `hloc : ∀ (c' : (D.mem u).C.cls 0) (w : Fin (D.R.N 0) → D.host.E), w ∈ Lk T.atT 0 (Nat.zero_le _) v c' → ∃ r ∈ (T.atT.Pv v).primeCompl, r • w ∈ clsCrd D u 0 (Nat.zero_le _) c'` using `fun c' w hw => (memP _ _).mp (dnk_lk_locP T v c' ((memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hw⟩))`.

Establish `hA : ∀ y, y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) ↔ y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin …` using `fun y => (dnk_char T v c c1 g γ hl hfun y).trans (dnk_char T v c c2 g γ' hl' hfun' y).symm`. Establish `hcomp : ∀ x : Fin (D.R.N 0) → D.host.E, ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x = ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.h …` using `fun x => by rw [Units.val_mul, Matrix.mulVec_mulVec]`. Establish `hinv : ∀ w : Fin (D.R.N 0) → D.host.E, ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) = w` using `fun w => by`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Establish `hinv' : ∀ w : Fin (D.R.N 0) → D.host.E, (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) = w` using `fun w => by`.

Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hinj : ∀ a b : Fin (D.R.N 0) → D.host.E, (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ a = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ b → a = b` using `fun a b h => (hinv a).symm.trans ((congrArg (fun w => ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) h).trans (hinv b))`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Take `⟨s, hs, hsz⟩` from `(memP _ _).mp hz`. Take `⟨x, hx, hxz⟩` from `(memM _ _ _).mp hsz`. Establish `hx2 : x ∈ Lk T.atT 0 (Nat.zero_le _) v c2` using `Submodule.mem_sup_left hx`. Establish `hA2 : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2))` using `(memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨x, hx2, rfl⟩⟩`. Take `⟨t, ht, htx⟩` from `(memP _ _).mp ((hA _).mpr hA2)`.

Take `⟨w, hw, hwx⟩` from `(memM _ _ _).mp htx`. Establish `hx' : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • z)` using `by rw [← hxz, hcomp, hinv']`. Establish `hwz : w = (t * s) • z`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hwx, hx', mul_smul, hsm _ t (s • z)]`.

Take `⟨r, hr, hrw⟩` from `hloc c1 w hw`. Conclude with `(memP _ _).mpr ⟨r * (t * s), hPc hr (hPc ht hs), by rw [mul_smul, ← hwz]; exact hrw⟩`. Introduce `hz`. Take `⟨s, hs, hsz⟩` from `(memP _ _).mp hz`. Establish `hk1 : s • z ∈ Lk T.atT 0 (Nat.zero_le _) v c1` using `Submodule.mem_sup_left hsz`.

Establish `hA1 : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • z) ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1))` using `(memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨_, hk1, rfl⟩⟩`. Take `⟨t, ht, htx⟩` from `(memP _ _).mp ((hA _).mp hA1)`. Take `⟨w, hw, hwx⟩` from `(memM _ _ _).mp htx`. Take `⟨r, hr, hrw⟩` from `hloc c2 w hw`. Use `(memP _ _).mpr ⟨r * (t * s), hPc hr (hPc ht hs), (memM _ _ _).mpr ⟨r • w, hrw, ?_⟩⟩` and prove the remaining obligations.

Simplify using `only [hcomp, hsm, hwx, hinv, mul_smul]`.
-/
theorem dnk_latP (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (γ γ' : GL (Fin (D.R.N 0)) D.host.E)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun' : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c2)) (hx : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c2 (T.lv0.pr v c2 x) = g (T.lv0.prk v c ⟨_, hx⟩)) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) := by
  have memP : ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) L ↔ ∃ s ∈ (T.atT.Pv v).primeCompl, s • z ∈ L := fun _ _ => Iff.rfl
  have memM : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ mulLat M L ↔ ∃ x ∈ L, M *ᵥ x = z := fun _ _ _ => Iff.rfl
  have hsm : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (t : 𝓞 D.host.E) (x : Fin (D.R.N 0) → D.host.E), M *ᵥ (t • x) = t • (M *ᵥ x) :=
    fun M t x => Matrix.mulVec_smul M t x
  have hPc : ∀ {a b : 𝓞 D.host.E}, a ∈ (T.atT.Pv v).primeCompl → b ∈ (T.atT.Pv v).primeCompl →
      a * b ∈ (T.atT.Pv v).primeCompl := fun ha hb => Submonoid.mul_mem _ ha hb
  have hloc : ∀ (c' : (D.mem u).C.cls 0) (w : Fin (D.R.N 0) → D.host.E), w ∈ Lk T.atT 0 (Nat.zero_le _) v c' →
      ∃ r ∈ (T.atT.Pv v).primeCompl, r • w ∈ clsCrd D u 0 (Nat.zero_le _) c' := fun c' w hw =>
    (memP _ _).mp (dnk_lk_locP T v c' ((memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hw⟩))
  have hA : ∀ y, y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) ↔
      y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) := fun y =>
    (dnk_char T v c c1 g γ hl hfun y).trans (dnk_char T v c c2 g γ' hl' hfun' y).symm
  have hcomp : ∀ x : Fin (D.R.N 0) → D.host.E, ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x = ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x) :=
    fun x => by rw [Units.val_mul, Matrix.mulVec_mulVec]
  have hinv : ∀ w : Fin (D.R.N 0) → D.host.E, ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ w : Fin (D.R.N 0) → D.host.E, (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinj : ∀ a b : Fin (D.R.N 0) → D.host.E, (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ a = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ b → a = b := fun a b h =>
    (hinv a).symm.trans ((congrArg (fun w => ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) h).trans (hinv b))
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs, hsz⟩ := (memP _ _).mp hz
    obtain ⟨x, hx, hxz⟩ := (memM _ _ _).mp hsz
    have hx2 : x ∈ Lk T.atT 0 (Nat.zero_le _) v c2 := Submodule.mem_sup_left hx
    have hA2 : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) :=
      (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨x, hx2, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp ((hA _).mpr hA2)
    obtain ⟨w, hw, hwx⟩ := (memM _ _ _).mp htx
    have hx' : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • z) := by rw [← hxz, hcomp, hinv']
    have hwz : w = (t * s) • z := by
      apply hinj
      rw [hwx, hx', mul_smul, hsm _ t (s • z)]
    obtain ⟨r, hr, hrw⟩ := hloc c1 w hw
    exact (memP _ _).mpr ⟨r * (t * s), hPc hr (hPc ht hs), by rw [mul_smul, ← hwz]; exact hrw⟩
  · intro hz
    obtain ⟨s, hs, hsz⟩ := (memP _ _).mp hz
    have hk1 : s • z ∈ Lk T.atT 0 (Nat.zero_le _) v c1 := Submodule.mem_sup_left hsz
    have hA1 : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • z) ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) :=
      (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨_, hk1, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp ((hA _).mp hA1)
    obtain ⟨w, hw, hwx⟩ := (memM _ _ _).mp htx
    obtain ⟨r, hr, hrw⟩ := hloc c2 w hw
    refine (memP _ _).mpr ⟨r * (t * s), hPc hr (hPc ht hs), (memM _ _ _).mpr ⟨r • w, hrw, ?_⟩⟩
    simp only [hcomp, hsm, hwx, hinv, mul_smul]

end CrossDiaZero

end
