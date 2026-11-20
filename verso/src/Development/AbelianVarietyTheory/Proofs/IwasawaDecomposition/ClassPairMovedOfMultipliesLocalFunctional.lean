import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLatticesStatement

noncomputable section

namespace GlobalTheory.LevelHecke.MovePair

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

/- English proof (translation)
Establish `key : ∀ z, z ∈ loc res M' ↔ g z ∈ loc res M`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨s, hs0, h⟩` from `(mem_loc _ _ _).1 hz`.

Use `loc_sat res M s _ hs0 ?_` and prove the remaining obligations. Rewrite using `[← map_smul]`. Conclude with `(mem_loc _ _ _).2 (h1 _ h)`. Introduce `hz`. Take `⟨s, hs0, h⟩` from `(mem_loc _ _ _).1 hz`.

Rewrite `h` using `[← map_smul]`. Conclude with `loc_sat res M' s _ hs0 ((mem_loc _ _ _).2 (h2 _ h))`. Use extensionality with `x`. Rewrite using `[Pr.mem_act] show g.symm x ∈ loc res M' ↔ x ∈ loc res M`. Rewrite using `[key, g.apply_symm_apply]`.

Take `⟨z, rfl⟩` from `g.surjective x show φ' (locExt res M' pr' (g.symm (g z))) = a * φ (locExt res M pr (g z))`. Rewrite using `[g.symm_apply_apply]`. Distinguish the cases in `hz : z ∈ loc res M'`. Establish `hz'` using `(key z).1 hz`. Take `⟨s, hs0, h⟩` from `(mem_loc _ _ _).1 hz`.

Take `⟨t, ht0, h'⟩` from `(mem_loc _ _ _).1 hz'`. Establish `e1 : (t * s) • z ∈ M'` using `by rw [mul_smul]; exact M'.smul_mem _ h`. Establish `e2 : (t * s) • g z ∈ M` using `by rw [mul_comm, mul_smul]; exact M.smul_mem _ h'`. Establish `e3 : g ((t * s) • z) ∈ M` using `by rw [map_smul]; exact e2`. Establish `hne : res (t * s) ≠ 0` using `by rw [map_mul]; exact mul_ne_zero ht0 hs0`.

Establish `e4` using `h3 _ e1 e3`. Establish `e5 : (⟨g ((t * s) • z), e3⟩ : M) = ⟨(t * s) • g z, e2⟩` using `Subtype.ext (map_smul _ _ _)`. Rewrite `e4` using `[e5, locExt_spec res M' pr' hs' z hz _ e1, locExt_spec res M pr hs _ hz' _ e2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[e4]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[locExt_off _ _ _ _ hz, locExt_off _ _ _ _ (fun h => hz ((key z).2 h)), map_zero, map_zero, mul_zero]`.
-/
theorem pairOf_act {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W'] (res : R →+* k) (M M' : Submodule R V)
    (pr : M →+ W) (pr' : M' →+ W') (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (g : V ≃ₗ[R] V) (a : k)
    (h1 : ∀ z ∈ M', ∃ s, res s ≠ 0 ∧ s • g z ∈ M)
    (h2 : ∀ z, g z ∈ M → ∃ s, res s ≠ 0 ∧ s • z ∈ M')
    (h3 : ∀ z (hz : z ∈ M') (hg : g z ∈ M), φ' (pr' ⟨z, hz⟩) = a * φ (pr ⟨g z, hg⟩)) :
    (pairOf res M' pr' φ').act g = (pairOf res M pr φ).dil a := by
  have key : ∀ z, z ∈ loc res M' ↔ g z ∈ loc res M := by
    intro z
    constructor
    · intro hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      refine loc_sat res M s _ hs0 ?_
      rw [← map_smul]
      exact (mem_loc _ _ _).2 (h1 _ h)
    · intro hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      rw [← map_smul] at h
      exact loc_sat res M' s _ hs0 ((mem_loc _ _ _).2 (h2 _ h))
  ext x
  · rw [Pr.mem_act]
    show g.symm x ∈ loc res M' ↔ x ∈ loc res M
    rw [key, g.apply_symm_apply]
  · obtain ⟨z, rfl⟩ := g.surjective x
    show φ' (locExt res M' pr' (g.symm (g z))) = a * φ (locExt res M pr (g z))
    rw [g.symm_apply_apply]
    by_cases hz : z ∈ loc res M'
    · have hz' := (key z).1 hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      obtain ⟨t, ht0, h'⟩ := (mem_loc _ _ _).1 hz'
      have e1 : (t * s) • z ∈ M' := by rw [mul_smul]; exact M'.smul_mem _ h
      have e2 : (t * s) • g z ∈ M := by rw [mul_comm, mul_smul]; exact M.smul_mem _ h'
      have e3 : g ((t * s) • z) ∈ M := by rw [map_smul]; exact e2
      have hne : res (t * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero ht0 hs0
      have e4 := h3 _ e1 e3
      have e5 : (⟨g ((t * s) • z), e3⟩ : M) = ⟨(t * s) • g z, e2⟩ := Subtype.ext (map_smul _ _ _)
      rw [e5, locExt_spec res M' pr' hs' z hz _ e1, locExt_spec res M pr hs _ hz' _ e2, map_smul, map_smul,
        smul_eq_mul, smul_eq_mul] at e4
      apply mul_left_cancel₀ hne
      rw [e4]; ring
    · rw [locExt_off _ _ _ _ hz, locExt_off _ _ _ _ (fun h => hz ((key z).2 h)), map_zero, map_zero, mul_zero]

/- English proof (translation)
Establish `e : (fun a => inclE (F` using `F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) = (γ.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) := by`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ _`. Rewrite using `[e, mulVec_mulVec, ← Units.val_mul, map_mul, mul_inv_cancel_right, map_mul, map_inv, Units.val_mul, ← mulVec_mulVec]`. Both sides reduce to the same expression.
-/
theorem mov_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (z : Fin n → E) :
    (bc (prV (E := E) v) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y')).1 *ᵥ
      (((bc (prV (E := E) v) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a))) =
    ((bc (prV (E := E) v) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) := by
  have e : (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) =
      (γ.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  rw [e, mulVec_mulVec, ← Units.val_mul, map_mul, mul_inv_cancel_right, map_mul, map_inv, Units.val_mul,
    ← mulVec_mulVec]
  rfl

/- English proof (translation)
Substitute `e` using the available equality. Take `⟨hg, hf⟩` from `hM`. Use `⟨hg x, fun hx hx' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hf ⟨x, hx⟩, map_zsmul, zsmul_eq_mul]`.
-/
theorem mulsF_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hM : MulsF S v hv a h) {k : Type} [Ring k] (φ : S.fM v hv ≃+ k)
    (x x' : Fin n → E ⊗[F] v.adicCompletion F) (e : h.1 *ᵥ x = x') :
    (x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) ↔
      x' ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) ∧
    ∀ hx hx', φ (S.fT v hv ⟨x, hx⟩) = (a : k) * φ (S.fT v hv ⟨x', hx'⟩) := by
  subst e
  obtain ⟨hg, hf⟩ := hM
  refine ⟨hg x, fun hx hx' => ?_⟩
  rw [← hf ⟨x, hx⟩, map_zsmul, zsmul_eq_mul]

section Tied

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

/- English proof (translation)
Establish `hL` using `bwB_clsCrd_lat D u i hi c`. Take `⟨d, hd, hle⟩` from `LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hL`. Conclude with `⟨LocB.fg_of_le_bnd hd hle, LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _ hL⟩`.
-/
theorem ld_lattice (c : (D.mem u).C.cls i) : Submodule.IsLattice D.host.E (Ld D u i hi c) := by
  have hL := bwB_clsCrd_lat D u i hi c
  obtain ⟨d, hd, hle⟩ := LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hL
  exact ⟨LocB.fg_of_le_bnd hd hle, LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _ hL⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `GlobalTheory.T.unitary_completion_maps_dualLattices D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi c) K.lev.Lb (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) (bwB_clsCrd_lat D u i hi c) ⟨Module.Finite.iff_fg.1 K.lev.Lb_fin, K.lev.Lb_span⟩ (Formalism …` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `rlv_yloc v (K.y c).1 (K.y_lat c) x`.
-/
theorem ld_loc (K : ClsTied u i hi) (v : HeightOneSpectrum (𝓞 D.host.F)) (c : (D.mem u).C.cls i)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi c) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈ dualV K v := by
  refine GlobalTheory.T.unitary_completion_maps_dualLattices D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi c) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) (bwB_clsCrd_lat D u i hi c)
    ⟨Module.Finite.iff_fg.1 K.lev.Lb_fin, K.lev.Lb_span⟩
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x

end Tied

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D u A i hi P K fMe hT v c c' γ a hM`. Establish `hin : ∀ c (z : Fin (D.R.N i) → D.host.E), z ∈ Ld D u i hi c → ((bc (prV (E` using `D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 := fun c z hz => (ld_loc K _ c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)`. Establish `hout : ∀ c (z : Fin (D.R.N i) → D.host.E), ((bc (prV (E` using `D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 → ∃ s, A.res v s ≠ 0 ∧ s • z ∈ Ld D u i hi c := by`. Introduce `c z hz`. Take `⟨r, hr, h⟩` from `GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion D.host.F D.host.E (A.eV v).1 _ _ (ld_lattice c) z ((ld_loc K _ c _).2 hz)`.

Conclude with `⟨_, fun h0 => hr ((A.res_v v r).2 h0), h⟩`. Establish `hst` using `fun z => mulsF_apply K.lev _ _ a _ hM (fMe v) _ _ (mov_mulVec (A.eV v).1 (K.y c).1 (K.y c').1 γ z)`. Use `pairOf_act _ _ _ _ _ _ _ (P.pr_smul v c) (P.pr_smul v c') (glE γ) _ (fun z hz => hout c (γ.1 *ᵥ z) ((hst z).1.1 (hin c' z hz))) (fun z hz => hout c' z ((hst z).1.2 (hin c (γ.1 *ᵥ z) hz))) (fun z hz hz' => ?_)` and prove the remaining obligations. Establish `hz2 : γ.1 *ᵥ z ∈ Ld D u i hi c` using `hz'`. Establish `hT' : ∀ c (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c), (D.fm u).fv i v c (P.pr v c ⟨z, hz⟩) = fMe v (K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, hin c z hz⟩)` using `fun c z hz => hT v c ⟨z, hz⟩ (hin c z hz)`.

Establish `e1` using `hT' c' z hz`. Establish `e2` using `hT' c _ hz2`. Conclude with `e1.trans (((hst z).2 _ _).trans (congrArg (fun t => (a : (D.mem u).A.Fv v) * t) e2.symm))`.
-/
theorem pc_act_of_mulsF : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (a : ℤ), MulsF K.lev (A.eV v).1 (A.eV v).2 a (mov K (A.eV v).1 c γ c') → (pc P v c').act (glE γ) = (pc P v c).dil (a : (D.mem u).A.Fv v) := by
  intro D u A i hi P K fMe hT v c c' γ a hM
  have hin : ∀ c (z : Fin (D.R.N i) → D.host.E), z ∈ Ld D u i hi c →
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 :=
    fun c z hz => (ld_loc K _ c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hout : ∀ c (z : Fin (D.R.N i) → D.host.E),
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 →
      ∃ s, A.res v s ≠ 0 ∧ s • z ∈ Ld D u i hi c := by
    intro c z hz
    obtain ⟨r, hr, h⟩ := GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion D.host.F D.host.E (A.eV v).1 _ _ (ld_lattice c) z ((ld_loc K _ c _).2 hz)
    exact ⟨_, fun h0 => hr ((A.res_v v r).2 h0), h⟩
  have hst := fun z => mulsF_apply K.lev _ _ a _ hM (fMe v) _ _
    (mov_mulVec (A.eV v).1 (K.y c).1 (K.y c').1 γ z)
  refine pairOf_act _ _ _ _ _ _ _ (P.pr_smul v c) (P.pr_smul v c') (glE γ) _
    (fun z hz => hout c (γ.1 *ᵥ z) ((hst z).1.1 (hin c' z hz)))
    (fun z hz => hout c' z ((hst z).1.2 (hin c (γ.1 *ᵥ z) hz))) (fun z hz hz' => ?_)
  · have hz2 : γ.1 *ᵥ z ∈ Ld D u i hi c := hz'
    have hT' : ∀ c (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c), (D.fm u).fv i v c (P.pr v c ⟨z, hz⟩) =
        fMe v (K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, hin c z hz⟩) := fun c z hz => hT v c ⟨z, hz⟩ (hin c z hz)
    have e1 := hT' c' z hz
    have e2 := hT' c _ hz2
    exact e1.trans (((hst z).2 _ _).trans (congrArg (fun t => (a : (D.mem u).A.Fv v) * t) e2.symm))

end GlobalTheory.LevelHecke.MovePair

end
