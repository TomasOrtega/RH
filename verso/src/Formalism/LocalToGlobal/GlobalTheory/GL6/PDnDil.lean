import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusNoKernelOfHeckeRamified
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section DdlGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Substitute `hWe` using the available equality. Establish `hκ` using `(S.U_eq _).1 κ.2`. Establish `hκ'` using `(S.U_eq _).1 κ'.2`. Establish `hWU : κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)` using `mul_mem (mul_mem (mul_mem (inv_mem hκ.1) (inv_mem η.2)) η'.2) hκ'.1`. Establish `hDW : δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1) ∈ S.U`.

Rewrite using `[S.U_eq]`. Use `⟨mul_mem (inv_mem δ.2) hWU, fun v' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : v' = v`. Substitute `h` using the available equality. Rewrite using `[S.UlocAlt _ hv]`.

Take `⟨h1, h2, hg, h3⟩` from `hδ`. Rewrite using `[map_mul, map_inv]`. Use `Subgroup.mem_inf.2 ⟨(levelVL σ J v' S.Lb).mul_mem ((levelVL σ J v' S.Lb).inv_mem h2) (Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem _ _ _ _ hWU, hL⟩), ?_⟩` and prove the remaining obligations. Establish `hgg` using `(stabGL _).mul_mem ((stabGL _).inv_mem hg) hgW`. Use `⟨hgg, fun x => ?_⟩` and prove the remaining obligations.

Use `set y : latS (F := F) (v'.adicCompletion F) (intV E v') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := ⟨((bc (prV (E := E) v') δ.1)⁻¹ * bc (prV (E := E) v') (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)).1 *ᵥ x.1, (hgg x.1).1 x.2⟩ with hy`. Establish `e1 : (⟨(bc (prV (E` using `E) v') δ.1).1 *ᵥ y.1, (hg y.1).1 y.2⟩ : latS (F := F) (v'.adicCompletion F) (intV E v') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) = ⟨(bc (prV (E := E) v') (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)).1 *ᵥ x.1, (hgW x.1).1 x.2⟩ := by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hy, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc]`. Rewrite using `[Units.mul_inv, Matrix.one_mul]`.

Establish `A` using `h3 y`. Rewrite `A` using `[e1, hfW x]`. Conclude with `A.symm`. Establish `e : bc (prV (E` using `E) v') (δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)) = (bc (prV (E := E) v') κ.1)⁻¹ * bc (prV (E := E) v') κ'.1 := by`. Simplify using `only [map_mul, map_inv, hδ.1 v' h, hη v' h, hη' v' h, inv_one, one_mul, mul_one]`.

Rewrite using `[e]`. Conclude with `mul_mem (inv_mem (hκ.2 v')) (hκ'.2 v')`. Establish `e : δ.1⁻¹ * η.1⁻¹ * η'.1 = (δ.1⁻¹ * κ.1 * δ.1) * (δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)) * κ'.1⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem (diamond_conj_mem_level S v hv hδ κ) hDW) (inv_mem κ'.2)`.
-/
theorem ddl_core (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (hδ : IsDia S v hv k δ)
    (η η' : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hη : ∀ v', v' ≠ v → bc (prV (E := E) v') η.1 = 1) (hη' : ∀ v', v' ≠ v → bc (prV (E := E) v') η'.1 = 1)
    (κ κ' : S.U) (W : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hWe : bc (prV (E := E) v) (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1) = W)
    (hL : W ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb))
    (hgW : W ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))))
    (hfW : ∀ x : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        k • S.fT v hv ⟨W.1 *ᵥ x.1, (hgW x.1).1 x.2⟩ = S.fT v hv x) :
    δ.1⁻¹ * η.1⁻¹ * η'.1 ∈ S.U := by
  subst hWe
  have hκ := (S.U_eq _).1 κ.2
  have hκ' := (S.U_eq _).1 κ'.2
  have hWU : κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    mul_mem (mul_mem (mul_mem (inv_mem hκ.1) (inv_mem η.2)) η'.2) hκ'.1
  have hDW : δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1) ∈ S.U := by
    rw [S.U_eq]
    refine ⟨mul_mem (inv_mem δ.2) hWU, fun v' => ?_⟩
    by_cases h : v' = v
    · subst h
      rw [S.UlocAlt _ hv]
      obtain ⟨h1, h2, hg, h3⟩ := hδ
      rw [map_mul, map_inv]
      refine Subgroup.mem_inf.2 ⟨(levelVL σ J v' S.Lb).mul_mem ((levelVL σ J v' S.Lb).inv_mem h2)
        (Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem _ _ _ _ hWU, hL⟩), ?_⟩
      have hgg := (stabGL _).mul_mem ((stabGL _).inv_mem hg) hgW
      refine ⟨hgg, fun x => ?_⟩
      set y : latS (F := F) (v'.adicCompletion F) (intV E v')
          (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) :=
        ⟨((bc (prV (E := E) v') δ.1)⁻¹ * bc (prV (E := E) v') (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)).1 *ᵥ x.1,
          (hgg x.1).1 x.2⟩ with hy
      have e1 : (⟨(bc (prV (E := E) v') δ.1).1 *ᵥ y.1, (hg y.1).1 y.2⟩ :
          latS (F := F) (v'.adicCompletion F) (intV E v') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
          ⟨(bc (prV (E := E) v') (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)).1 *ᵥ x.1, (hgW x.1).1 x.2⟩ := by
        apply Subtype.ext
        simp only [hy, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc]
        rw [Units.mul_inv, Matrix.one_mul]
      have A := h3 y
      rw [e1, hfW x] at A
      exact A.symm
    · have e : bc (prV (E := E) v') (δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)) =
          (bc (prV (E := E) v') κ.1)⁻¹ * bc (prV (E := E) v') κ'.1 := by
        simp only [map_mul, map_inv, hδ.1 v' h, hη v' h, hη' v' h, inv_one, one_mul, mul_one]
      rw [e]
      exact mul_mem (inv_mem (hκ.2 v')) (hκ'.2 v')
  have e : δ.1⁻¹ * η.1⁻¹ * η'.1 = (δ.1⁻¹ * κ.1 * δ.1) * (δ.1⁻¹ * (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1)) * κ'.1⁻¹ := by
    group
  rw [e]
  exact mul_mem (mul_mem (diamond_conj_mem_level S v hv hδ κ) hDW) (inv_mem κ'.2)

/- English proof (translation)
Establish `e1 : η * κ = y⁻¹ * g * y'` using `by rw [mul_assoc y⁻¹, h1]; group`. Establish `e2 : η' * κ' = y⁻¹ * g' * y''` using `by rw [mul_assoc y⁻¹, h2]; group`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ddl_comp_eq {G : Type} [Group G] (y y' y'' η κ η' κ' g g' : G)
    (h1 : g * y' = y * η * κ) (h2 : g' * y'' = y * η' * κ') :
    κ⁻¹ * η⁻¹ * η' * κ' = y'⁻¹ * (g⁻¹ * g') * y'' := by
  have e1 : η * κ = y⁻¹ * g * y' := by rw [mul_assoc y⁻¹, h1]; group
  have e2 : η' * κ' = y⁻¹ * g' * y'' := by rw [mul_assoc y⁻¹, h2]; group
  calc κ⁻¹ * η⁻¹ * η' * κ' = (η * κ)⁻¹ * (η' * κ') := by group
    _ = _ := by rw [e1, e2]; group

end DdlGen

section DdlLoc

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.one_mulVec]`. Conclude with `⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩`.
-/
theorem ddl_mulLat_one {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  ext x
  simp only [mulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.one_mulVec]
  exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/- English proof (translation)
Establish `k1` using `rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge`. Establish `k2` using `rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le`. Rewrite `k1`, `k2` using `[← rlv_mulLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ddl_mulLat_one]`. Conclude with `le_antisymm k1 k2`.
-/
theorem localization_inv_smul_eq {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g : GL (Fin n) E) {A B : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) A) = Formalism.HermitianLatticesTheory.localization₂ P B) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P A := by
  have k1 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
  have k2 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
  rw [← rlv_mulLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ddl_mulLat_one] at k1 k2
  exact le_antisymm k1 k2

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Introduce `x hx`. Take `⟨s, hs, hsx⟩` from `(rlv_mem_locP _ _ _).1 hx`. Conclude with `(rlv_mem_locP _ _ _).2 ⟨s, hs, h hsx⟩`.
-/
theorem localization_mono₂ (P : Ideal (𝓞 E)) [P.IsPrime] {n : ℕ} {M N : Submodule (𝓞 E) (Fin n → E)} (h : M ≤ N) :
    Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (rlv_mem_locP _ _ _).1 hx
  exact (rlv_mem_locP _ _ _).2 ⟨s, hs, h hsx⟩

/- English proof (translation)
The claim follows from `(rlv_mem_locP _ _ _).2 ⟨1, P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance), by rw [one_smul]; exact h⟩`.
-/
theorem mem_localization_of_mem₂ (P : Ideal (𝓞 E)) [P.IsPrime] {n : ℕ} {M : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (h : x ∈ M) : x ∈ Formalism.HermitianLatticesTheory.localization₂ P M :=
  (rlv_mem_locP _ _ _).2 ⟨1, P.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance), by rw [one_smul]; exact h⟩

/- English proof (translation)
Establish `k1` using `rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le`. Establish `k2` using `rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge`. Establish `e1 : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (g : Matrix (Fin n) (Fin n) E) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Rewrite `k1`, `k2` using `[← rlv_mulLat_mul, ← rlv_mulLat_mul, e1, ddl_mulLat_one, ← Units.val_mul]`.

Conclude with `le_antisymm k1 k2`.
-/
theorem localization_smul_cancel {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime] (g g' : GL (Fin n) E) {A B : Submodule (𝓞 E) (Fin n → E)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g' : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P (mulLat (g : Matrix (Fin n) (Fin n) E) A)) :
    Formalism.HermitianLatticesTheory.localization₂ P (mulLat ((g⁻¹ * g' : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) B) = Formalism.HermitianLatticesTheory.localization₂ P A := by
  have k1 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.le
  have k2 := rlv_locP_mulLat_le P ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) h.ge
  have e1 : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (g : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← rlv_mulLat_mul, ← rlv_mulLat_mul, e1, ddl_mulLat_one, ← Units.val_mul] at k1 k2
  exact le_antisymm k1 k2

end DdlLoc

section DdlTied

variable {D : D7} {u : D.what₂.Word}

def ddlW (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c1 c2 : (D.mem u).C.cls i)
    (g : GL (Fin (D.R.N i)) D.host.E) :
    GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] (Tf.atT.eV v).1.adicCompletion D.host.F) :=
  bc (prV (E := D.host.E) (Tf.atT.eV v).1) (((Tf.cls i hi).y c1).1⁻¹ *
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g * ((Tf.cls i hi).y c2).1)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def DnDilLocV (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ),
    (k : (D.mem u).A.Fv v) = a → g ≠ 0 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = ((a : (D.mem u).A.Fv v) • g) ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1⁻¹ * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
              Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi ((D.fm u).dn i v c g)) ∧
    Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (γ.1⁻¹ * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
              Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi ((D.fm u).dn i v c g)) ∧
    ∃ hg : ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1) ∈
        stabGL (latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (Tf.cls i hi).lev.Lb))),
      ∀ x : latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (Tf.cls i hi).lev.Lb)),
        k • (Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2
            ⟨(ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1)).1 *ᵥ x.1,
              (hg x.1).1 x.2⟩ =
          (Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2 x

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `i hi v c g a k hk hg δ hδ γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'`. Take `⟨hP, hQ, hW, hf⟩` from `h i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'`. Establish `heq` using `ddl_comp_eq ((Tf.cls i hi).y c).1 ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 η.1 κ.1 η'.1 κ'.1 (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1) (bc (inclE (F := D.host.F) (FiniteAdeleRing …`. Rewrite `heq` using `[← map_inv, ← map_mul]`. Establish `e : bc (prV (E` using `D.host.E) (Tf.atT.eV v).1) (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1) = ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1) := by`.

Unfold `ddlW`. Rewrite using `[heq]`. Use `ddl_core (Tf.cls i hi).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 hδ η η' hsup hsup' κ κ' _ e ?_ hW hf` and prove the remaining obligations. Unfold `ddlW`. Conclude with `rlv_stabT Tf i hi v _ _ (γ.1⁻¹ * γ'.1) hP hQ`.
-/
theorem dnDilLoc_of_V (Tf : FormsTied D u) (h : DnDilLocV Tf) : DnDilLoc Tf := by
  intro i hi v c g a k hk hg δ hδ γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'
  obtain ⟨hP, hQ, hW, hf⟩ := h i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'
  have heq := ddl_comp_eq ((Tf.cls i hi).y c).1 ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1
    ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 η.1 κ.1 η'.1 κ'.1
    (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1)
    (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1) hrel hrel'
  rw [← map_inv, ← map_mul] at heq
  have e : bc (prV (E := D.host.E) (Tf.atT.eV v).1) (κ.1⁻¹ * η.1⁻¹ * η'.1 * κ'.1) =
      ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1) := by
    unfold ddlW; rw [heq]
  refine ddl_core (Tf.cls i hi).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 hδ η η' hsup hsup' κ κ' _ e ?_ hW hf
  unfold ddlW
  exact rlv_stabT Tf i hi v _ _ (γ.1⁻¹ * γ'.1) hP hQ

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

/- English proof (translation)
Rewrite using `[Units.val_mul]`. Conclude with `rlv_chainP _ _ _ (localization_inv_smul_eq _ γ.1 hl) hl'`.
-/
theorem ddl_dualP (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls i)
    (γ γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c)) :
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1⁻¹ * γ'.1).1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c1) := by
  rw [Units.val_mul]
  exact rlv_chainP _ _ _ (localization_inv_smul_eq _ γ.1 hl) hl'

def LocalToGlobal₂ (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c, Lk Tf.atT i hi v c ≤ Ld D u i hi c ∧
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `hP : (Tf.atT.Pv v).IsPrime` using `inferInstance`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨s, hs, hsy⟩` from `(rlv_mem_locP _ _ _).1 hy`. Take `⟨x, hx, hxe⟩` from `Submodule.mem_map.1 hsy`.

Simplify using `only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe`. Establish `hxd : x ∈ Ld D u i hi c1` using `hK1 hx`. Establish `hγx : γ.1.1 *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c)`. Rewrite using `[← hl]`. Conclude with `mem_localization_of_mem₂ _ (Submodule.mem_map.2 ⟨x, hxd, rfl⟩)`.

Take `⟨t, ht, htx⟩` from `(rlv_mem_locP _ _ _).1 hγx`. Establish `hsm : γ.1.1 *ᵥ (t • x) = t • (γ.1.1 *ᵥ x)` using `Matrix.mulVec_smul _ _ _`. Establish `hmem : γ.1.1 *ᵥ ((t • (⟨x, hxd⟩ : ↥(Ld D u i hi c1)) : ↥(Ld D u i hi c1)) : Fin (D.R.N i) → D.host.E) ∈ Lk Tf.atT i hi v c` using `by show γ.1.1 *ᵥ (t • x) ∈ _`. Rewrite using `[hsm]`. Conclude with `Submodule.mem_sup_left htx`.

Establish `h1` using `hfun (t • ⟨x, hxd⟩) hmem`. Rewrite `h1` using `[(Tf.lv i hi).pr_smul, map_smul, ((Tf.lv i hi).fv_ker v c1 ⟨x, hxd⟩).2 hx, smul_zero]`. Establish `hts : (t * s) • y ∈ Lk Tf.atT i hi v c`. Rewrite using `[mul_smul, ← hxe]`. Conclude with `Submodule.mem_sup_left htx`.

Use `⟨t * s, fun h => (hP.mem_or_mem h).elim ht hs, hts, ?_⟩` and prove the remaining obligations. Establish `e : (⟨(t * s) • y, hts⟩ : ↥(Lk Tf.atT i hi v c)) = ⟨_, hmem⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (t * s) • y = γ.1.1 *ᵥ (t • x)`. Rewrite using `[hsm, hxe, mul_smul]`.

Rewrite using `[e]`. Conclude with `h1.symm`. Introduce and unpack `⟨s, hs, h, h0⟩`. Establish `h2 : s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c)` using `hKc (mem_localization_of_mem₂ _ h)`. Take `⟨r, hr, hry⟩` from `(rlv_mem_locP _ _ _).1 h2`.

Establish `h3 : r • s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1))`. Rewrite using `[hl]`. Conclude with `mem_localization_of_mem₂ _ hry`. Take `⟨t, ht, hty⟩` from `(rlv_mem_locP _ _ _).1 h3`. Take `⟨x, hx, hxe⟩` from `Submodule.mem_map.1 hty`.

Simplify using `only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe`. Establish `hmem : γ.1.1 *ᵥ (⟨x, hx⟩ : ↥(Ld D u i hi c1)).1 ∈ Lk Tf.atT i hi v c` using `by show γ.1.1 *ᵥ x ∈ _`. Rewrite using `[hxe]`. Conclude with `Submodule.mem_sup_left (Submodule.smul_mem _ t hry)`. Establish `h1` using `hfun ⟨x, hx⟩ hmem`.

Establish `e : (⟨γ.1.1 *ᵥ (⟨x, hx⟩ : ↥(Ld D u i hi c1)).1, hmem⟩ : ↥(Lk Tf.atT i hi v c)) = (t * r) • ⟨s • y, h⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show γ.1.1 *ᵥ x = (t * r) • (s • y)`. Rewrite using `[hxe, mul_smul]`. Rewrite `h1` using `[e, (Tf.lv i hi).prk_smul, map_smul, h0, smul_zero]`.

Establish `hxk : x ∈ Lk Tf.atT i hi v c1` using `((Tf.lv i hi).fv_ker v c1 ⟨x, hx⟩).1 h1`. Use `(rlv_mem_locP _ _ _).2 ⟨t * r * s, fun hh => (hP.mem_or_mem hh).elim (fun hh' => (hP.mem_or_mem hh').elim ht hr) hs, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_map.2 ⟨x, hxk, ?_⟩` and prove the remaining obligations. Use `show γ.1.1 *ᵥ x = (t * r * s) • y`. Rewrite using `[hxe, mul_smul, mul_smul]`.
-/
theorem ddk_char (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c1 : (D.mem u).C.cls i)
    (hKc : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hK1 : Lk Tf.atT i hi v c1 ≤ Ld D u i hi c1)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hfun : ∀ (x : ↥(Ld D u i hi c1)) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
      (D.fm u).fv i v c1 ((Tf.lv i hi).pr v c1 x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩))
    (y : Fin (D.R.N i) → D.host.E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Lk Tf.atT i hi v c1)) ↔
      ∃ s : 𝓞 D.host.E, s ∉ Tf.atT.Pv v ∧ ∃ h : s • y ∈ Lk Tf.atT i hi v c, g ((Tf.lv i hi).prk v c ⟨_, h⟩) = 0 := by
  have hP : (Tf.atT.Pv v).IsPrime := inferInstance
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := (rlv_mem_locP _ _ _).1 hy
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hsy
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe
    have hxd : x ∈ Ld D u i hi c1 := hK1 hx
    have hγx : γ.1.1 *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) := by
      rw [← hl]
      exact mem_localization_of_mem₂ _ (Submodule.mem_map.2 ⟨x, hxd, rfl⟩)
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hγx
    have hsm : γ.1.1 *ᵥ (t • x) = t • (γ.1.1 *ᵥ x) := Matrix.mulVec_smul _ _ _
    have hmem : γ.1.1 *ᵥ ((t • (⟨x, hxd⟩ : ↥(Ld D u i hi c1)) : ↥(Ld D u i hi c1)) : Fin (D.R.N i) → D.host.E) ∈
        Lk Tf.atT i hi v c := by
      show γ.1.1 *ᵥ (t • x) ∈ _
      rw [hsm]
      exact Submodule.mem_sup_left htx
    have h1 := hfun (t • ⟨x, hxd⟩) hmem
    rw [(Tf.lv i hi).pr_smul, map_smul, ((Tf.lv i hi).fv_ker v c1 ⟨x, hxd⟩).2 hx, smul_zero] at h1
    have hts : (t * s) • y ∈ Lk Tf.atT i hi v c := by
      rw [mul_smul, ← hxe]
      exact Submodule.mem_sup_left htx
    refine ⟨t * s, fun h => (hP.mem_or_mem h).elim ht hs, hts, ?_⟩
    have e : (⟨(t * s) • y, hts⟩ : ↥(Lk Tf.atT i hi v c)) = ⟨_, hmem⟩ := by
      apply Subtype.ext
      show (t * s) • y = γ.1.1 *ᵥ (t • x)
      rw [hsm, hxe, mul_smul]
    rw [e]
    exact h1.symm
  · rintro ⟨s, hs, h, h0⟩
    have h2 : s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) := hKc (mem_localization_of_mem₂ _ h)
    obtain ⟨r, hr, hry⟩ := (rlv_mem_locP _ _ _).1 h2
    have h3 : r • s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1)) := by
      rw [hl]; exact mem_localization_of_mem₂ _ hry
    obtain ⟨t, ht, hty⟩ := (rlv_mem_locP _ _ _).1 h3
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hty
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hxe
    have hmem : γ.1.1 *ᵥ (⟨x, hx⟩ : ↥(Ld D u i hi c1)).1 ∈ Lk Tf.atT i hi v c := by
      show γ.1.1 *ᵥ x ∈ _
      rw [hxe]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ t hry)
    have h1 := hfun ⟨x, hx⟩ hmem
    have e : (⟨γ.1.1 *ᵥ (⟨x, hx⟩ : ↥(Ld D u i hi c1)).1, hmem⟩ : ↥(Lk Tf.atT i hi v c)) = (t * r) • ⟨s • y, h⟩ := by
      apply Subtype.ext
      show γ.1.1 *ᵥ x = (t * r) • (s • y)
      rw [hxe, mul_smul]
    rw [e, (Tf.lv i hi).prk_smul, map_smul, h0, smul_zero] at h1
    have hxk : x ∈ Lk Tf.atT i hi v c1 := ((Tf.lv i hi).fv_ker v c1 ⟨x, hx⟩).1 h1
    refine (rlv_mem_locP _ _ _).2 ⟨t * r * s, fun hh => (hP.mem_or_mem hh).elim
      (fun hh' => (hP.mem_or_mem hh').elim ht hr) hs, ?_⟩
    refine Submodule.mem_map.2 ⟨x, hxk, ?_⟩
    show γ.1.1 *ᵥ x = (t * r * s) • y
    rw [hxe, mul_smul, mul_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Establish `eq1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Lk Tf.atT i hi v c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Lk Tf.atT i hi v c1))`. Use extensionality with `y`. Rewrite using `[ddk_char Tf i hi v c c2 hKc hK2 _ γ' hl' hfun' y, ddk_char Tf i hi v c c1 hKc hK1 g γ hl hfun y]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, Units.ne_zero, false_or]`. Establish `L1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c1) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c1)` using `le_antisymm hK1' (localization_mono₂ _ le_sup_left)`.

Establish `L2 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c2) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c2)` using `le_antisymm hK2' (localization_mono₂ _ le_sup_left)`. Establish `M1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Lk Tf.atT i hi v c1)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi c1))` using `le_antisymm (rlv_locP_mulLat_le _ _ L1.le) (rlv_locP_mulLat_le _ _ L1.ge)`. Establish `M2 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Lk Tf.atT i hi v c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (clsCrd D u i hi c2))` using `le_antisymm (rlv_locP_mulLat_le _ _ L2.le) (rlv_locP_mulLat_le _ _ L2.ge)`. Rewrite `eq1` using `[M1, M2]`. Conclude with `localization_smul_cancel _ γ.1 γ'.1 eq1`.
-/
theorem ddk_latP (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls i)
    (hKc : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hK1 : Lk Tf.atT i hi v c1 ≤ Ld D u i hi c1) (hK2 : Lk Tf.atT i hi v c2 ≤ Ld D u i hi c2)
    (hK1' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c1) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c1))
    (hK2' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c2) ≤ Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c2))
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (a : ((D.mem u).A.Fv v)ˣ)
    (γ γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi c1)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hfun : ∀ (x : ↥(Ld D u i hi c1)) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
      (D.fm u).fv i v c1 ((Tf.lv i hi).pr v c1 x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi c2)) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c))
    (hfun' : ∀ (x : ↥(Ld D u i hi c2)) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
      (D.fm u).fv i v c2 ((Tf.lv i hi).pr v c2 x) = ((a : (D.mem u).A.Fv v) • g) ((Tf.lv i hi).prk v c ⟨_, hx⟩)) :
    Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat (γ.1⁻¹ * γ'.1).1 (clsCrd D u i hi c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c1) := by
  have eq1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Lk Tf.atT i hi v c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Lk Tf.atT i hi v c1)) := by
    ext y
    rw [ddk_char Tf i hi v c c2 hKc hK2 _ γ' hl' hfun' y, ddk_char Tf i hi v c c1 hKc hK1 g γ hl hfun y]
    simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, Units.ne_zero, false_or]
  have L1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c1) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c1) :=
    le_antisymm hK1' (localization_mono₂ _ le_sup_left)
  have L2 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Lk Tf.atT i hi v c2) = Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c2) :=
    le_antisymm hK2' (localization_mono₂ _ le_sup_left)
  have M1 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Lk Tf.atT i hi v c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi c1)) :=
    le_antisymm (rlv_locP_mulLat_le _ _ L1.le) (rlv_locP_mulLat_le _ _ L1.ge)
  have M2 : Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Lk Tf.atT i hi v c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (clsCrd D u i hi c2)) :=
    le_antisymm (rlv_locP_mulLat_le _ _ L2.le) (rlv_locP_mulLat_le _ _ L2.ge)
  rw [M1, M2] at eq1
  exact localization_smul_cancel _ γ.1 γ'.1 eq1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def DnDilLocW (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ),
    (k : (D.mem u).A.Fv v) = a → g ≠ 0 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g))).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = ((a : (D.mem u).A.Fv v) • g) ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (mulLat (γ.1⁻¹ * γ'.1).1 (clsCrd D u i hi ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)))) =
              Formalism.HermitianLatticesTheory.localization₂ (rlvQ Tf.atT v) (clsCrd D u i hi ((D.fm u).dn i v c g)) ∧
    ∃ hg : ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1) ∈
        stabGL (latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (Tf.cls i hi).lev.Lb))),
      ∀ x : latS (F := D.host.F) ((Tf.atT.eV v).1.adicCompletion D.host.F) (intV D.host.E (Tf.atT.eV v).1)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (Tf.cls i hi).lev.Lb)),
        k • (Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2
            ⟨(ddlW Tf i hi v ((D.fm u).dn i v c g) ((D.fm u).dn i v c ((a : (D.mem u).A.Fv v) • g)) (γ.1⁻¹ * γ'.1)).1 *ᵥ x.1,
              (hg x.1).1 x.2⟩ =
          (Tf.cls i hi).lev.fT (Tf.atT.eV v).1 (Tf.atT.eV v).2 x

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'`. Conclude with `⟨ddk_latP Tf i hi v c _ _ (hK i hi v c).2 (hK i hi v _).1 (hK i hi v _).1 (hK i hi v _).2 (hK i hi v _).2 g a γ γ' hl hfun hl' hfun', h i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'⟩`.
-/
theorem dilation_local_v_of_kernel_and_local_w (Tf : FormsTied D u) (hK : LocalToGlobal₂ Tf) (h : DnDilLocW Tf) : DnDilLocV Tf := by
  intro i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'
  exact ⟨ddk_latP Tf i hi v c _ _ (hK i hi v c).2 (hK i hi v _).1 (hK i hi v _).1 (hK i hi v _).2 (hK i hi v _).2 g a γ γ'
    hl hfun hl' hfun', h i hi v c g a k hk hg γ η κ hsup hrel hl hfun γ' η' κ' hsup' hrel' hl' hfun'⟩

/- English proof (translation)
The claim follows from `dnDilLoc_of_V Tf (dilation_local_v_of_kernel_and_local_w Tf hK h)`.
-/
theorem dilation_local_of_kernel_and_local_w (Tf : FormsTied D u) (hK : LocalToGlobal₂ Tf) (h : DnDilLocW Tf) : DnDilLoc Tf :=
  dnDilLoc_of_V Tf (dilation_local_v_of_kernel_and_local_w Tf hK h)

/- English proof (translation)
The claim follows from `frobenius_no_kernel_of_hecke_relations h1 (fun D u Tf hc => dilation_local_of_kernel_and_local_w Tf (hL D u Tf hc).1 (hL D u Tf hc).2)`.
-/
theorem frobeniusNoKernelFamily_of_hecke_kerAtP (h1 : HeckeRelationsFamily)
    (hL : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → LocalToGlobal₂ Tf ∧ DnDilLocW Tf) : FrobeniusNoKernelFamily :=
  frobenius_no_kernel_of_hecke_relations h1 (fun D u Tf hc => dilation_local_of_kernel_and_local_w Tf (hL D u Tf hc).1 (hL D u Tf hc).2)

end DdlTied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
