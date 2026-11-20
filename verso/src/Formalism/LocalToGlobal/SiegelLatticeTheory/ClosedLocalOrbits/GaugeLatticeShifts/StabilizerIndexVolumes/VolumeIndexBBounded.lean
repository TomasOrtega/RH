import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexFiniteNonzero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DiagMulOfBt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexAStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.NatSmulMem

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {n : ℕ}

def Xi (Λ : Submodule (𝓞 E) S.V) (f : Fin n → S.V) (x : Fin n → E) : Prop := ∑ c, x c • f c ∈ Λ

def Pres (Λ : Submodule (𝓞 E) S.V) (f : Fin n → S.V) (g : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ x, Xi Λ f x → Xi Λ f (g *ᵥ x)

/- English proof (translation)
Rewrite using `[map_sum]`. Simplify using `only [LinearEquiv.map_smul, hu, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]`.
-/
theorem comp_sum (f : Fin n → S.V) (s : S.V ≃ₗ[E] S.V) (uu : Matrix (Fin n) (Fin n) E)
    (hu : ∀ b, s (f b) = ∑ c, uu c b • f c) (y : Fin n → E) :
    ∑ c, (uu *ᵥ y) c • f c = s (∑ b, y b • f b) := by
  rw [map_sum]
  simp only [LinearEquiv.map_smul, hu, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/- English proof (translation)
Introduce `x hx`. Simplify using `using hx`.
-/
theorem pres_one (Λ : Submodule (𝓞 E) S.V) (f : Fin n → S.V) : Pres Λ f 1 := by
  intro x hx; simpa using hx

/- English proof (translation)
Introduce `x hx`. Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `hA _ (hB _ hx)`.
-/
theorem pres_mul (Λ : Submodule (𝓞 E) S.V) (f : Fin n → S.V) {A B : Matrix (Fin n) (Fin n) E}
    (hA : Pres Λ f A) (hB : Pres Λ f B) : Pres Λ f (A * B) := by
  intro x hx; rw [← Matrix.mulVec_mulVec]; exact hA _ (hB _ hx)

/- English proof (translation)
Use `⟨fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Unfold `Xi at hx ⊢`. Rewrite using `[comp_sum f s uu hu x, ← hs]`. Conclude with `Submodule.mem_map_of_mem hx`. Unfold `Xi at hx ⊢`.

Rewrite `hx` using `[← hs]`. Take `⟨w, hw, hsw⟩` from `Submodule.mem_map.mp hx`. Establish `h1 : s (∑ c, (uu⁻¹ *ᵥ x) c • f c) = s w`. Rewrite using `[← comp_sum f s uu hu, Matrix.mulVec_mulVec, mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Conclude with `hsw.symm`.

Rewrite using `[s.injective h1]`. Conclude with `hw`.
-/
theorem pres_of_aut (Λ : Submodule (𝓞 E) S.V) (f : Fin n → S.V) (s : S.V ≃ₗ[E] S.V)
    (hs : Formalism.HermitianLatticesTheory.gmap s Λ = Λ) (uu : Matrix (Fin n) (Fin n) E) (hu : ∀ b, s (f b) = ∑ c, uu c b • f c)
    (hdet : IsUnit uu.det) : Pres Λ f uu ∧ Pres Λ f uu⁻¹ := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · unfold Xi at hx ⊢
    rw [comp_sum f s uu hu x, ← hs]
    exact Submodule.mem_map_of_mem hx
  · unfold Xi at hx ⊢
    rw [← hs] at hx
    obtain ⟨w, hw, hsw⟩ := Submodule.mem_map.mp hx
    have h1 : s (∑ c, (uu⁻¹ *ᵥ x) c • f c) = s w := by
      rw [← comp_sum f s uu hu, Matrix.mulVec_mulVec, mul_nonsing_inv _ hdet, Matrix.one_mulVec]
      exact hsw.symm
    rw [s.injective h1]; exact hw

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `hyps _ t w F' L U _ _ hN _`. Take `⟨_, _, hL, _, _⟩` from `hN`. Establish `hT : ((Tu D u : ℕ) : D.host.E) ≠ 0`. Use `hyps.2.2.2.1.1.pos` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions.

Establish `hlat : Submodule.IsLattice D.host.E t.lam` using `(hyps.2.2.2.2.2.1 t.lam t.mem).1.1`. Establish `hf` using `frame_indep F0 hT`. Establish `hLi : L⁻¹ * L = 1` using `nonsing_inv_mul _ (by rw [lo_det hL]; exact isUnit_one)`. Establish `hLL : L * L⁻¹ = 1` using `mul_nonsing_inv _ (by rw [lo_det hL]; exact isUnit_one)`. Establish `key : ∀ a ∈ stabAut D u u' F0 what₂ t F' L, ∃ g : GLR D, Pres t.lam F0.fvec (g : MatR D) ∧ Pres t.lam F0.fvec ((g⁻¹ : GLR D) : MatR D) ∧ (a : MatR D) = L⁻¹ * (g : MatR D).conjTranspose * L`.

Introduce `a ha`. Proceed by induction on `ha using Subgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨s, ⟨hsF, _⟩, uu, huu, hx⟩` from `hx`. Take `⟨⟨_, hgm⟩, hf1, hf2⟩` from `hsF`.

Take `⟨uu0, huu0, hu0⟩` from `tri_exists F0 s hf1 hf2`. Establish `heq : uu = uu0` using `coef_unique hf (fun b => s (F0.fvec b)) uu uu0 huu hu0`. Substitute `heq` using the available equality. Establish `hdet : IsUnit uu.det` using `by rw [up_det huu0]; exact isUnit_one`. Take `⟨h1, h2⟩` from `pres_of_aut t.lam F0.fvec s hgm uu huu hdet`.

Use `⟨Matrix.nonsingInvUnit uu hdet, h1, ?_, hx⟩` and prove the remaining obligations. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `h2`. Consider the case `one`. Use `⟨1, pres_one _ _, by simpa using pres_one t.lam F0.fvec, ?_⟩` and prove the remaining obligations.

Simplify using `[hLi]`. Consider the case `mul x y _ _ hx hy`. Take `⟨g1, h11, h12, e1⟩` from `hx`. Take `⟨g2, h21, h22, e2⟩` from `hy`. Use `⟨g2 * g1, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul]`. Conclude with `pres_mul _ _ h21 h11`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul]`. Conclude with `pres_mul _ _ h12 h22`. Rewrite using `[Units.val_mul, Units.val_mul, e1, e2, Matrix.conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = L⁻¹ * ((g1 : MatR D).conjTranspose * (g2 : MatR D).conjTranspose) * L := by`. Rewrite using `[hLL, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`.

Consider the case `inv x _ hx`. Take `⟨g, h1, h2, e⟩` from `hx`. Use `⟨g⁻¹, h2, by rw [inv_inv]; exact h1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.coe_units_inv, e]`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Establish `hg : ((g⁻¹ : GLR D) : MatR D).conjTranspose * (g : MatR D).conjTranspose = 1`. Rewrite using `[← Matrix.conjTranspose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = L⁻¹ * (((g⁻¹ : GLR D) : MatR D).conjTranspose * (g : MatR D).conjTranspose) * L := by`.

Rewrite using `[hLL, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hg, Matrix.mul_one, hLi]`. Take `⟨φ, hφ⟩` from `coord_exists hf`. Take `⟨m1, hm1, hb1⟩` from `lat_fun_bdd t.lam hlat φ`.

Establish `hmc : ∀ c, ∃ m : ℕ, m ≠ 0 ∧ (m : D.host.E) • F0.fvec c ∈ t.lam` using `fun c => lat_smul_mem t.lam hlat _`. Use `choose mc hmc0 hmcL using hmc`. Use `set m2 : ℕ := ∏ c, mc c with hm2`. Establish `hm20 : m2 ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun c _ => hmc0 c`. Establish `hm2L : ∀ c, (m2 : D.host.E) • F0.fvec c ∈ t.lam`.

Introduce `c`. Establish `: (m2 : D.host.E) • F0.fvec c = ((∏ j ∈ Finset.univ.erase c, mc j : ℕ) : D.host.E) • ((mc c : D.host.E) • F0.fvec c)`. Rewrite using `[smul_smul, hm2, ← Finset.mul_prod_erase Finset.univ mc (Finset.mem_univ c)]`. Use `push_cast`. Put the polynomial expressions in normal form.

Rewrite using `[this]`. Conclude with `nat_smul_mem _ _ (hmcL c)`. Establish `hcoord : ∀ y : Fin (D.R.rS + 1) → D.host.E, ∀ i, φ i (∑ c, y c • F0.fvec c) = y i`. Introduce `y i`. Simplify using `[map_sum, hφ]`.

Take `⟨mL, hmL, hbL⟩` from `den_mat L`. Take `⟨mL', hmL', hbL'⟩` from `den_mat L⁻¹`. Use `⟨mL' * (m1 * m2) * mL, by positivity, ?_⟩` and prove the remaining obligations. Introduce `a ha i j`. Take `⟨g, hg, _, hag⟩` from `key a ha`.

Establish `hgb : ∀ i j, IntE (((m1 * m2 : ℕ) : D.host.E) * (g : MatR D) i j)`. Introduce `i j`. Set `x : Fin (D.R.rS + 1) → D.host.E` to `fun k => if k = j then (m2 : D.host.E) else 0`. Establish `hx : Xi t.lam F0.fvec x`. Unfold `Xi`.

Simplify using `only [x, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `hm2L j`. Establish `h1` using `hb1 _ (hg x hx) i`. Rewrite `h1` using `[hcoord]`. Establish `h2 : ((g : MatR D) *ᵥ x) i = (g : MatR D) i j * (m2 : D.host.E)`.

Simplify using `[x, Matrix.mulVec, dotProduct]`. Rewrite `h1` using `[h2]`. Establish `h3 : ((m1 * m2 : ℕ) : D.host.E) * (g : MatR D) i j = (m1 : D.host.E) * ((g : MatR D) i j * (m2 : D.host.E))` using `by push_cast; ring`. Rewrite using `[h3]`. Conclude with `h1`.

Establish `hgt : ∀ i j, IntE (((m1 * m2 : ℕ) : D.host.E) * (g : MatR D).conjTranspose i j)`. Introduce `i j`. Use `intE_star (hgb j i)` as an intermediate fact. Rewrite `this` using `[star_mul', star_natCast]`. Simplify `this` using `[Matrix.conjTranspose_apply]`.

Establish `h4` using `intE_matmul (intE_matmul hbL' hgt) hbL i j`. Rewrite using `[hag]`. Conclude with `h4`.
-/
theorem volume_index_b_bounded (D : D7) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    BBdd D u u' F0 what₂ δ M := by
  intro hyps _ t w F' L U _ _ hN _
  obtain ⟨_, _, hL, _, _⟩ := hN
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by
    have := hyps.2.2.2.1.1.pos
    exact_mod_cast this.ne'
  have hlat : Submodule.IsLattice D.host.E t.lam := (hyps.2.2.2.2.2.1 t.lam t.mem).1.1
  have hf := frame_indep F0 hT
  have hLi : L⁻¹ * L = 1 := nonsing_inv_mul _ (by rw [lo_det hL]; exact isUnit_one)
  have hLL : L * L⁻¹ = 1 := mul_nonsing_inv _ (by rw [lo_det hL]; exact isUnit_one)

  have key : ∀ a ∈ stabAut D u u' F0 what₂ t F' L, ∃ g : GLR D, Pres t.lam F0.fvec (g : MatR D) ∧
      Pres t.lam F0.fvec ((g⁻¹ : GLR D) : MatR D) ∧ (a : MatR D) = L⁻¹ * (g : MatR D).conjTranspose * L := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨s, ⟨hsF, _⟩, uu, huu, hx⟩ := hx
      obtain ⟨⟨_, hgm⟩, hf1, hf2⟩ := hsF
      obtain ⟨uu0, huu0, hu0⟩ := tri_exists F0 s hf1 hf2
      have heq : uu = uu0 := coef_unique hf (fun b => s (F0.fvec b)) uu uu0 huu hu0
      subst heq
      have hdet : IsUnit uu.det := by rw [up_det huu0]; exact isUnit_one
      obtain ⟨h1, h2⟩ := pres_of_aut t.lam F0.fvec s hgm uu huu hdet
      refine ⟨Matrix.nonsingInvUnit uu hdet, h1, ?_, hx⟩
      rw [Matrix.coe_units_inv]; exact h2
    | one =>
      refine ⟨1, pres_one _ _, by simpa using pres_one t.lam F0.fvec, ?_⟩
      simp [hLi]
    | mul x y _ _ hx hy =>
      obtain ⟨g1, h11, h12, e1⟩ := hx
      obtain ⟨g2, h21, h22, e2⟩ := hy
      refine ⟨g2 * g1, ?_, ?_, ?_⟩
      · rw [Units.val_mul]; exact pres_mul _ _ h21 h11
      · rw [_root_.mul_inv_rev, Units.val_mul]; exact pres_mul _ _ h12 h22
      · rw [Units.val_mul, Units.val_mul, e1, e2, Matrix.conjTranspose_mul]
        calc L⁻¹ * (g1 : MatR D).conjTranspose * L * (L⁻¹ * (g2 : MatR D).conjTranspose * L)
            = L⁻¹ * (g1 : MatR D).conjTranspose * (L * L⁻¹) * (g2 : MatR D).conjTranspose * L := by
              simp only [Matrix.mul_assoc]
          _ = L⁻¹ * ((g1 : MatR D).conjTranspose * (g2 : MatR D).conjTranspose) * L := by
              rw [hLL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    | inv x _ hx =>
      obtain ⟨g, h1, h2, e⟩ := hx
      refine ⟨g⁻¹, h2, by rw [inv_inv]; exact h1, ?_⟩
      rw [Matrix.coe_units_inv, e]
      apply Matrix.inv_eq_left_inv
      have hg : ((g⁻¹ : GLR D) : MatR D).conjTranspose * (g : MatR D).conjTranspose = 1 := by
        rw [← Matrix.conjTranspose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.conjTranspose_one]
      calc L⁻¹ * ((g⁻¹ : GLR D) : MatR D).conjTranspose * L * (L⁻¹ * (g : MatR D).conjTranspose * L)
          = L⁻¹ * ((g⁻¹ : GLR D) : MatR D).conjTranspose * (L * L⁻¹) * (g : MatR D).conjTranspose * L := by
            simp only [Matrix.mul_assoc]
        _ = L⁻¹ * (((g⁻¹ : GLR D) : MatR D).conjTranspose * (g : MatR D).conjTranspose) * L := by
            rw [hLL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hg, Matrix.mul_one, hLi]

  obtain ⟨φ, hφ⟩ := coord_exists hf
  obtain ⟨m1, hm1, hb1⟩ := lat_fun_bdd t.lam hlat φ
  have hmc : ∀ c, ∃ m : ℕ, m ≠ 0 ∧ (m : D.host.E) • F0.fvec c ∈ t.lam := fun c => lat_smul_mem t.lam hlat _
  choose mc hmc0 hmcL using hmc
  set m2 : ℕ := ∏ c, mc c with hm2
  have hm20 : m2 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hmc0 c
  have hm2L : ∀ c, (m2 : D.host.E) • F0.fvec c ∈ t.lam := by
    intro c
    have : (m2 : D.host.E) • F0.fvec c = ((∏ j ∈ Finset.univ.erase c, mc j : ℕ) : D.host.E) • ((mc c : D.host.E) • F0.fvec c) := by
      rw [smul_smul, hm2, ← Finset.mul_prod_erase Finset.univ mc (Finset.mem_univ c)]; push_cast; ring_nf
    rw [this]; exact nat_smul_mem _ _ (hmcL c)
  have hcoord : ∀ y : Fin (D.R.rS + 1) → D.host.E, ∀ i, φ i (∑ c, y c • F0.fvec c) = y i := by
    intro y i
    simp [map_sum, hφ]
  obtain ⟨mL, hmL, hbL⟩ := den_mat L
  obtain ⟨mL', hmL', hbL'⟩ := den_mat L⁻¹
  refine ⟨mL' * (m1 * m2) * mL, by positivity, ?_⟩
  intro a ha i j
  obtain ⟨g, hg, _, hag⟩ := key a ha
  have hgb : ∀ i j, IntE (((m1 * m2 : ℕ) : D.host.E) * (g : MatR D) i j) := by
    intro i j
    let x : Fin (D.R.rS + 1) → D.host.E := fun k => if k = j then (m2 : D.host.E) else 0
    have hx : Xi t.lam F0.fvec x := by
      unfold Xi
      simp only [x, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hm2L j
    have h1 := hb1 _ (hg x hx) i
    rw [hcoord] at h1
    have h2 : ((g : MatR D) *ᵥ x) i = (g : MatR D) i j * (m2 : D.host.E) := by
      simp [x, Matrix.mulVec, dotProduct]
    rw [h2] at h1
    have h3 : ((m1 * m2 : ℕ) : D.host.E) * (g : MatR D) i j = (m1 : D.host.E) * ((g : MatR D) i j * (m2 : D.host.E)) := by
      push_cast; ring
    rw [h3]; exact h1
  have hgt : ∀ i j, IntE (((m1 * m2 : ℕ) : D.host.E) * (g : MatR D).conjTranspose i j) := by
    intro i j
    have := intE_star (hgb j i)
    rw [star_mul', star_natCast] at this
    simpa [Matrix.conjTranspose_apply] using this
  have h4 := intE_matmul (intE_matmul hbL' hgt) hbL i j
  rw [hag]; exact h4

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
