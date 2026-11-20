import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `u hu`. Establish `h` using `GlobalTheory.InertDetChr.at_inFin_one (F := F) v u hu`. Rewrite `h`, the goal using `[smul_eq_mul]`. Rewrite using `[show a = 1 * a from (one_mul a).symm, inFin_mul, ← mul_assoc, h, zero_mul]`.
-/
theorem at_inFin (v : Pl F) (a : Fv F v) : At (evFin F v) (inFin v a) := by
  intro u hu
  have h := GlobalTheory.InertDetChr.at_inFin_one (F := F) v u hu
  rw [smul_eq_mul] at h ⊢
  rw [show a = 1 * a from (one_mul a).symm, inFin_mul, ← mul_assoc, h, zero_mul]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul, GlobalTheory.InertDetChr.compFin_algebraMap]`. Establish `: compFin F E v (inclR (F` using `F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Simplify using `[Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem compFin_smul_inclR (v : Pl F) (a : AF F) (y : E) :
    compFin F E v (a • inclR (F := F) (AF F) y) = evFin F v a ⊗ₜ[F] y := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.InertDetChr.compFin_algebraMap]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this]
  simp [Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, -, ha, y, hy, rfl⟩` from `hz`. Use `tmul_mem_latLoc ha hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Conclude with `compFin_smul_inclR v a (y i)`. Consider the case `zero`. Use `zero_mem (latLoc F W.L v) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_zero _`.

Consider the case `add x y _ _ hx hy`. Use `add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_add _ _ _`. Consider the case `neg x _ hx`.

Use `neg_mem hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_neg _ _`.
-/
theorem comp_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl F) {z : Fin d → AE F E}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : compFin F E v ∘ z ∈ latLoc F W.L v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    convert tmul_mem_latLoc ha hy using 1
    funext i
    exact compFin_smul_inclR v a (y i)
  | zero =>
    convert zero_mem (latLoc F W.L v) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

/- English proof (translation)
Introduce `y hy`. Use `latLoc_induction (p := fun y => (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v) (fun a ha x hx => ?_) (by rw [Matrix.mulVec_zero]; exact zero_mem _) (fun _ _ h h' => by rw [Matrix.mulVec_add]; exact add_mem h h') (fun _ h => by rw [Matrix.mulVec_neg]; exact neg_mem h) hy` and prove the remaining obligations. Establish `hz : (inFin v a • fun i => inclR (F` using `F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt W v := AddSubgroup.subset_closure ⟨inFin v a, at_inFin v a, by rwa [GlobalTheory.InertDetChr.evFin_inFin_self], x, hx, rfl⟩`. Establish `e1 : (fun i => a ⊗ₜ[F] x i) = compFin F E v ∘ (inFin v a • fun i => inclR (F` using `F) (AF F) (x i)) := by`. Use function extensionality and compare the values at `i`.

Use `show _ = compFin F E v (inFin v a • inclR (F := F) (AF F) (x i))`. Rewrite using `[compFin_smul_inclR, GlobalTheory.InertDetChr.evFin_inFin_self]`. Rewrite using `[e1]`. Establish `e2 : (compFin F E v).mapMatrix g *ᵥ (compFin F E v ∘ (inFin v a • fun i => inclR (F` using `F) (AF F) (x i))) = compFin F E v ∘ (g *ᵥ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) :=`. Use function extensionality and compare the values at `fun i => (RingHom.map_mulVec (compFin F E v) g _ i).symm`.

Rewrite using `[e2]`. Conclude with `comp_mem_latLoc W v (hg _ hz)`.
-/
theorem mulVec_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl F) (g : Matrix (Fin d) (Fin d) (AE F E))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ y ∈ latLoc F W.L v, (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v := by
  intro y hy
  refine latLoc_induction (p := fun y => (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v)
    (fun a ha x hx => ?_) (by rw [Matrix.mulVec_zero]; exact zero_mem _)
    (fun _ _ h h' => by rw [Matrix.mulVec_add]; exact add_mem h h')
    (fun _ h => by rw [Matrix.mulVec_neg]; exact neg_mem h) hy
  have hz : (inFin v a • fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt W v :=
    AddSubgroup.subset_closure ⟨inFin v a, at_inFin v a, by rwa [GlobalTheory.InertDetChr.evFin_inFin_self], x, hx, rfl⟩
  have e1 : (fun i => a ⊗ₜ[F] x i) = compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i)) := by
    funext i
    show _ = compFin F E v (inFin v a • inclR (F := F) (AF F) (x i))
    rw [compFin_smul_inclR, GlobalTheory.InertDetChr.evFin_inFin_self]
  rw [e1]
  have e2 : (compFin F E v).mapMatrix g *ᵥ (compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) =
      compFin F E v ∘ (g *ᵥ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) :=
    funext fun i => (RingHom.map_mulVec (compFin F E v) g _ i).symm
  rw [e2]
  exact comp_mem_latLoc W v (hg _ hz)

/- English proof (translation)
Use `set Q : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E) := (P⁻¹ * g * P).1 with hQ`. Establish `hent : ∀ i j, Q i j ∈ intLoc F E v`. Introduce `i j`. Establish `h1 : P.1 *ᵥ (Pi.single j 1) ∈ latLoc F L v` using `(hP _).1 (fun k => by`. Distinguish the cases in `e : k = j`.

Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[e])`. Establish `h2` using `(hP (Q *ᵥ Pi.single j 1)).2 (by`. Rewrite using `[hQ, Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, ← Matrix.mulVec_mulVec]`.

Conclude with `hg _ h1)`. Use `h2 i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one, Matrix.col_apply]`. Then use the resulting hypothesis. Set `Q' : Matrix (Fin d) (Fin d) (intLoc F E v)` to `fun i j => ⟨Q i j, hent i j⟩`. Establish `hQ' : (intLoc F E v).subtype.mapMatrix Q' = Q` using `rfl`.

Establish `hdet : Q.det = ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)`. Rewrite using `[hQ, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det P), ← mul_assoc, mul_inv_cancel, one_mul]`. Rewrite using `[← hdet, ← hQ', ← RingHom.map_det]`. Conclude with `(Matrix.det Q').2`.
-/
theorem det_mem_intLoc {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl F} (P : GL (Fin d) (Fv F v ⊗[F] E))
    (hP : ∀ y : Fin d → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ P.1 *ᵥ y ∈ latLoc F L v)
    (g : GL (Fin d) (Fv F v ⊗[F] E)) (hg : ∀ y ∈ latLoc F L v, g.1 *ᵥ y ∈ latLoc F L v) :
    ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  set Q : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E) := (P⁻¹ * g * P).1 with hQ
  have hent : ∀ i j, Q i j ∈ intLoc F E v := by
    intro i j
    have h1 : P.1 *ᵥ (Pi.single j 1) ∈ latLoc F L v := (hP _).1 (fun k => by
      by_cases e : k = j
      · subst e; simp
      · simp [e])
    have h2 := (hP (Q *ᵥ Pi.single j 1)).2 (by
      rw [hQ, Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul,
        ← Matrix.mulVec_mulVec]
      exact hg _ h1)
    have := h2 i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  let Q' : Matrix (Fin d) (Fin d) (intLoc F E v) := fun i j => ⟨Q i j, hent i j⟩
  have hQ' : (intLoc F E v).subtype.mapMatrix Q' = Q := rfl
  have hdet : Q.det = ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    rw [hQ, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      mul_comm _ (Matrix.GeneralLinearGroup.det P), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← hdet, ← hQ', ← RingHom.map_det]
  exact (Matrix.det Q').2

end GlobalTheory.SplitDetChr

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hvT _ _ _ t ht`. Take `⟨ht1, ht2⟩` from `ht`. Establish `e1` using `GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)`. Use `haveI : Submodule.IsLattice E G.W.L := hTr.geo.hW.lat`. Take `⟨P0, h1, h2⟩` from `GlobalTheory.AdelicU.Frames.exists_rational_frame G.W.L v`.

Establish `hP` using `GlobalTheory.AdelicU.Frames.frame_of_rational P0 h1 h2`. Use `set T := Formalism.UG.bc (compFin F E v) t with hTdef`. Establish `hT : ∀ y ∈ latLoc F G.W.L v, T.1 *ᵥ y ∈ latLoc F G.W.L v` using `GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).1)`. Establish `hT' : ∀ y ∈ latLoc F G.W.L v, (T⁻¹).1 *ᵥ y ∈ latLoc F G.W.L v`. Rewrite using `[hTdef, ← map_inv]`.

Conclude with `GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).2)`. Establish `hd : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = Matrix.GeneralLinearGroup.det T`. Use `Units.ext ?_` and prove the remaining obligations. Use `show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = _`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]`.

Both sides reduce to the same expression. Establish `hy` using `GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T hT`. Establish `hy'` using `GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T⁻¹ hT'`. Rewrite using `[e1]`. Use `show GlobalTheory.Doubling.charAt X.α v _ = 1`.

Rewrite using `[hd]`. Use `GlobalTheory.LFun.charAt_eq_one_of_unrAt X.α v _ hy (by rwa [← map_inv]) (fun w hw => hTr.chars.unrα w ?_)` and prove the remaining obligations. Use `show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))`. Rewrite using `[hw]`. Conclude with `hvT` after adjusting the coercions.
-/
theorem GlobalTheory.SplitDetChr.alpha_det_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hvT _ _ _ t ht
  obtain ⟨ht1, ht2⟩ := ht
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  haveI : Submodule.IsLattice E G.W.L := hTr.geo.hW.lat
  obtain ⟨P0, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame G.W.L v
  have hP := GlobalTheory.AdelicU.Frames.frame_of_rational P0 h1 h2
  set T := Formalism.UG.bc (compFin F E v) t with hTdef
  have hT : ∀ y ∈ latLoc F G.W.L v, T.1 *ᵥ y ∈ latLoc F G.W.L v :=
    GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).1)
  have hT' : ∀ y ∈ latLoc F G.W.L v, (T⁻¹).1 *ᵥ y ∈ latLoc F G.W.L v := by
    rw [hTdef, ← map_inv]
    exact GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).2)
  have hd : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = Matrix.GeneralLinearGroup.det T := by
    refine Units.ext ?_
    show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = _
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  have hy := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T hT
  have hy' := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T⁻¹ hT'
  rw [e1]
  show GlobalTheory.Doubling.charAt X.α v _ = 1
  rw [hd]
  refine GlobalTheory.LFun.charAt_eq_one_of_unrAt X.α v _ hy (by rwa [← map_inv]) (fun w hw => hTr.chars.unrα w ?_)
  show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))
  rw [hw]; exact_mod_cast hvT
