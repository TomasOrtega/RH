import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.ValNatCastLtOne

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

/- English proof (translation)
Rewrite using `[← map_mul, Rf.ew_idem]`.
-/
theorem eps_idem {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) :
    PI.FinKW.psiV I v Rf.ew * PI.FinKW.psiV I v Rf.ew = PI.FinKW.psiV I v Rf.ew := by
  rw [← map_mul, Rf.ew_idem]

/- English proof (translation)
Rewrite using `[← PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR, ← map_mul]`. Establish `h` using `Rf.ew_orth`. Establish `h' : Rf.ew * Formalism.UG.sigR I.cm.sig (Af I.F) Rf.ew = 0` using `h`. Rewrite using `[h', map_zero]`.
-/
theorem eps_orth {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) :
    PI.FinKW.psiV I v Rf.ew * PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) = 0 := by
  rw [← PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR, ← map_mul]
  have h := Rf.ew_orth
  have h' : Rf.ew * Formalism.UG.sigR I.cm.sig (Af I.F) Rf.ew = 0 := h
  rw [h', map_zero]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩`.
-/
theorem incl_mem_Lf (I : AutInst) (l : Fin I.n → I.E) (hl : l ∈ I.L) :
    (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ I.Lf :=
  Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [PI.FinKW.vecV, PI.FinKW.LocTo.psiV_inclE]`. Both sides reduce to the same expression.
-/
theorem vecV_incl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (l : Fin I.n → I.E) :
    PI.FinKW.vecV I v (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) =
      Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l := by
  funext i
  simp only [PI.FinKW.vecV, PI.FinKW.LocTo.psiV_inclE]
  rfl

/- English proof (translation)
Use `map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (A := KV I v) (B := I.E)) m` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem natCast_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) :
    ((m : KV I v) ⊗ₜ[I.F] (1 : I.E)) = (m : RV I v) := by
  have := map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (A := KV I v) (B := I.E)) m
  rw [← this]
  rfl

/- English proof (translation)
Use `set c := (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) with hc`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hy`. Establish `hy` using `Rf.ew_full _ (incl_mem_Lf I l hl)`.

Take `⟨w, hw, hw'⟩` from `vecV_mL I v g _ hy`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw', vecV_smul', vecV_incl, map_sub, map_sub, map_one]`. Establish `: PI.FinKW.psiV I v (sigA I Rf.ew) = PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)` using `PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR I v Rf.ew`. Rewrite using `[this]`.

Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨w1, hw1, h1⟩` from `hx`. Take `⟨w2, hw2, h2⟩` from `hy`. Conclude with `⟨w1 + w2, Submodule.add_mem _ hw1 hw2, by rw [smul_add, h1, h2, smul_add]⟩`.

Consider the case `smul o x _ hx`. Take `⟨w, hw, h⟩` from `hx`. Use `⟨o • w, Submodule.smul_mem _ o hw, ?_⟩` and prove the remaining obligations. Rewrite using `[PI.FinKW.LocTo.ov_smul_vec, PI.FinKW.LocTo.ov_smul_vec, smul_comm, h, smul_comm]`.
-/
theorem full_loc {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (x : Fin I.n → RV I v)
    (hx : x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) • x =
        (g : RV I v) • w := by
  set c := (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) with hc
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hy := Rf.ew_full _ (incl_mem_Lf I l hl)
    obtain ⟨w, hw, hw'⟩ := vecV_mL I v g _ hy
    refine ⟨w, hw, ?_⟩
    rw [← hw', vecV_smul', vecV_incl, map_sub, map_sub, map_one]
    have : PI.FinKW.psiV I v (sigA I Rf.ew) = PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) :=
      PI.UnitaryGroupMassFormula.AdIndexEq.psiV_sigR I v Rf.ew
    rw [this]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w1, hw1, h1⟩ := hx
    obtain ⟨w2, hw2, h2⟩ := hy
    exact ⟨w1 + w2, Submodule.add_mem _ hw1 hw2, by rw [smul_add, h1, h2, smul_add]⟩
  | smul o x _ hx =>
    obtain ⟨w, hw, h⟩ := hx
    refine ⟨o • w, Submodule.smul_mem _ o hw, ?_⟩
    rw [PI.FinKW.LocTo.ov_smul_vec, PI.FinKW.LocTo.ov_smul_vec, smul_comm, h, smul_comm]

/- English proof (translation)
Establish `hL : (I.L.restrictScalars ℤ).FG` using `I.L_fg.restrictScalars`. Take `⟨S, hS⟩` from `hL`. Establish `hSL : ∀ s ∈ S, s ∈ I.L`. Introduce `s hs`. Establish `: s ∈ I.L.restrictScalars ℤ` using `hS ▸ Submodule.subset_span hs`.

Conclude with `this`. Use `⟨S.image (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)), ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `y hy`.

Simplify using `only [Finset.coe_image] at hy`. Take `⟨s, hs, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨s, hSL s hs, rfl⟩`. Rewrite using `[Formalism.L2.SG.Sub.latLoc, Submodule.span_le]`. Introduce and unpack `_ ⟨l, hl, rfl⟩`.

Establish `hl' : l ∈ Submodule.span ℤ (S : Set (Fin I.n → I.E))`. Rewrite using `[hS]`. Conclude with `hl`. Use `clear hl`. Proceed by induction on `hl' using Submodule.span_induction with`.

Consider the case `mem s hs => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨s, hs, rfl⟩)`. Consider the case `zero`. Establish `: Formalism.L2.SG.Sub.ratV (F` using `I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (0 : Fin I.n → I.E) = 0 := by`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.L2.SG.Sub.ratV]`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: Formalism.L2.SG.Sub.ratV (F` using `I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (x + y) = Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x + Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMass …`. Use function extensionality and compare the values at `i`.

Simplify using `[Formalism.L2.SG.Sub.ratV]`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Establish `: Formalism.L2.SG.Sub.ratV (F` using `I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (a • x) = a • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x := by`.

Use function extensionality and compare the values at `i`. Simplify using `[Formalism.L2.SG.Sub.ratV]`. Rewrite using `[this]`. Conclude with `Submodule.smul_of_tower_mem _ a hx`.
-/
theorem latLoc_fg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).FG := by
  classical
  have hL : (I.L.restrictScalars ℤ).FG := I.L_fg.restrictScalars
  obtain ⟨S, hS⟩ := hL
  have hSL : ∀ s ∈ S, s ∈ I.L := by
    intro s hs
    have : s ∈ I.L.restrictScalars ℤ := hS ▸ Submodule.subset_span hs
    exact this
  refine ⟨S.image (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact Submodule.subset_span ⟨s, hSL s hs, rfl⟩
  · rw [Formalism.L2.SG.Sub.latLoc, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l ∈ Submodule.span ℤ (S : Set (Fin I.n → I.E)) := by
      rw [hS]; exact hl
    clear hl
    induction hl' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨s, hs, rfl⟩)
    | zero =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (0 : Fin I.n → I.E) = 0 := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (x + y) =
          Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x +
            Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) y := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (a • x) =
          a • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x := by
        funext i; simp [Formalism.L2.SG.Sub.ratV]
      rw [this]; exact Submodule.smul_of_tower_mem _ a hx

end PI.UnitaryGroupMassFormula.ScXuExists
