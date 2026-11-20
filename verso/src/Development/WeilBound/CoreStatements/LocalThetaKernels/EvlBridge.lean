import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.LagrangianStabilizerCharacterTrivial

noncomputable section

namespace PositivityTheory.ThKH.Evl

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.LatVac (liftV psiAt locCo evFin_liftV at_liftV)
open PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

open Classical in
/- English proof (translation)
Set `b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `h1 : HasCompactSupport fun x => (b x : ℂ)` using `b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)`. Use `⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩` and prove the remaining obligations. Use `show (b 0 : ℂ) = 1`. Rewrite using `[b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]`.
-/
theorem exists_bump {κ : Type} [Fintype κ] : ∃ f : SInf F κ, f 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  show (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), Complex.ofReal_one]

/- English proof (translation)
Take `⟨f, hf⟩` from `exists_bump (F := F) (κ := κ)`. Set `s : ∀ u : Pl F, (κ → Fv F u) → ℂ` to `fun u => Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1`. Take `⟨r, hr, ht⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f s (Filter.Eventually.of_forall fun _ => rfl)`. Establish `hS : ∀ u, Function.update s v φ u ∈ SB _` using `fun u => by`. Break down `eq_or_ne u v with rfl | hu` into its components or cases.

Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne hu]`. Conclude with `GlobalTheory.StdVacuum.indicator_mem_SB u`. Establish `hc : ∀ᶠ u in Filter.cofinite, Function.update s v φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1` using `by filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with u hu`. Rewrite using `[Function.update_of_ne hu]`.

Use `⟨r, ⟨hr, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ht]`. Conclude with `Submodule.subset_span ⟨f, _, ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ hS hc, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ hS hc⟩, rfl⟩`. Establish `h` using `congrFun (ht 1) 0`. Simplify using `only [tens, Pi.one_apply, one_mul] at h`.

Rewrite using `[h]`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure`. Rewrite using `[finprod_eq_one_of_forall_eq_one, mul_one, ← hf]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Introduce `u`. Distinguish the cases in `h : u = v`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne h]`. Simplify using `only [s]`. Rewrite using `[Set.indicator_of_mem (fun i => by simp)]; rfl`.
-/
theorem exists_rest {κ : Type} [Fintype κ] (v : Pl F) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) :
    ∃ r, Rest (evFin F v) φ r ∧ r 0 = 1 := by
  classical
  obtain ⟨f, hf⟩ := exists_bump (F := F) (κ := κ)
  let s : ∀ u : Pl F, (κ → Fv F u) → ℂ := fun u => Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1
  obtain ⟨r, hr, ht⟩ := GlobalTheory.PureFactor.exists_rest_factor v f s (Filter.Eventually.of_forall fun _ => rfl)
  have hS : ∀ u, Function.update s v φ u ∈ SB _ := fun u => by
    rcases eq_or_ne u v with rfl | hu
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hu]
      exact GlobalTheory.StdVacuum.indicator_mem_SB u
  have hc : ∀ᶠ u in Filter.cofinite, Function.update s v φ u =
      Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1 := by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with u hu
    rw [Function.update_of_ne hu]
  refine ⟨r, ⟨hr, ?_⟩, ?_⟩
  · rw [ht]
    exact Submodule.subset_span ⟨f, _, ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ hS hc,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ hS hc⟩, rfl⟩
  · have h := congrFun (ht 1) 0
    simp only [tens, Pi.one_apply, one_mul] at h
    rw [h]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    rw [finprod_eq_one_of_forall_eq_one, mul_one, ← hf]
    · congr 1
      funext i
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · intro u
      by_cases h : u = v
      · subst h; simp
      · rw [Function.update_of_ne h]
        simp only [s]
        rw [Set.indicator_of_mem (fun i => by simp)]; rfl

/- English proof (translation)
Take `⟨r, hr, h0⟩` from `exists_rest v hφ`. Establish `h` using `(h₁ r hr).symm.trans (h₂ r hr)`. Use function extensionality and compare the values at `t`. Establish `h'` using `congrFun h fun i => liftV v (t i)`. Establish `e : r (fun i => liftV v (t i)) = 1`.

Rewrite using `[← h0, ← hr.1 0 _ (GlobalTheory.VacAny.at_pi fun i => at_liftV v (t i)), zero_add]`. Simplify `h'` using `only [tens, evFin_liftV, e, mul_one]`.
-/
theorem acts_unique {κ : Type} [Fintype κ] {v : Pl F} {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) :
    φ₁ = φ₂ := by
  obtain ⟨r, hr, h0⟩ := exists_rest v hφ
  have h := (h₁ r hr).symm.trans (h₂ r hr)
  funext t
  have h' := congrFun h fun i => liftV v (t i)
  have e : r (fun i => liftV v (t i)) = 1 := by
    rw [← h0, ← hr.1 0 _ (GlobalTheory.VacAny.at_pi fun i => at_liftV v (t i)), zero_add]
  simpa only [tens, evFin_liftV, e, mul_one] using h'

section Co

variable {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
  {v : Pl F}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => acts_unique hφ h (GlobalTheory.VacBridge.rho_acts_locCo co ψ v u hu φ), fun h => h ▸ GlobalTheory.VacBridge.rho_acts_locCo co ψ v u hu φ⟩`.
-/
theorem acts_iff (ψ : AddChar (AF F) ℂ) {u : V} (hu : At (evFin F v) u) {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) :
    Acts (evFin F v) (co.rho ψ u) φ φ₁ ↔ φ₁ = schr (psiAt ψ v) (locCo co v u) φ :=
  ⟨fun h => acts_unique hφ h (GlobalTheory.VacBridge.rho_acts_locCo co ψ v u hu φ),
    fun h => h ▸ GlobalTheory.VacBridge.rho_acts_locCo co ψ v u hu φ⟩

/- English proof (translation)
Rewrite using `[co.form]`. Simplify using `only [dotProduct, map_sub, map_sum, map_mul]`. Both sides reduce to the same expression.
-/
theorem ev_form (u u' : V) : evFin F v (Bf u u') =
    (locCo co v u).1 ⬝ᵥ (locCo co v u').2 - (locCo co v u').1 ⬝ᵥ (locCo co v u).2 := by
  rw [co.form]
  simp only [dotProduct, map_sub, map_sum, map_mul]
  rfl

/- English proof (translation)
Rewrite using `[← ev_form, GlobalTheory.LatVac.psiAt_apply, ← GlobalTheory.StdVacuum.psi_eq_psiLoc]`. Introduce `t ht`. Establish `h : co.e (t • u) = 0` using `by rw [hu t ht, map_zero]`. Rewrite `h` using `[map_smul]`. Establish `h1 : t • (co.e u).1 = 0` using `congrArg Prod.fst h`.

Establish `h2 : t • (co.e u).2 = 0` using `congrArg Prod.snd h`. Rewrite using `[co.form, smul_sub, ← smul_dotProduct, ← dotProduct_smul, h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem psi_form (ψ : AddChar (AF F) ℂ) {u : V} (hu : At (evFin F v) u) (u' : V) : ψ (Bf u u') =
    psiAt ψ v ((locCo co v u).1 ⬝ᵥ (locCo co v u').2 - (locCo co v u').1 ⬝ᵥ (locCo co v u).2) := by
  rw [← ev_form, GlobalTheory.LatVac.psiAt_apply, ← GlobalTheory.StdVacuum.psi_eq_psiLoc]
  intro t ht
  have h : co.e (t • u) = 0 := by rw [hu t ht, map_zero]
  rw [map_smul] at h
  have h1 : t • (co.e u).1 = 0 := congrArg Prod.fst h
  have h2 : t • (co.e u).2 = 0 := congrArg Prod.snd h
  rw [co.form, smul_sub, ← smul_dotProduct, ← dotProduct_smul, h1, h2]
  simp

/- English proof (translation)
Use `⟨co.e.symm (fun k => liftV v (w.1 k), fun k => liftV v (w.2 k)), ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LatOpenCpt.locCo_smul, evFin_liftV, one_smul]`. Apply the tactic sequence `ext k <;> simp [locCo, evFin_liftV]`.
-/
theorem exists_locCo (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : V, locCo co v (liftV v 1 • u) = w := by
  refine ⟨co.e.symm (fun k => liftV v (w.1 k), fun k => liftV v (w.2 k)), ?_⟩
  rw [GlobalTheory.LatOpenCpt.locCo_smul, evFin_liftV, one_smul]
  ext k <;> simp [locCo, evFin_liftV]

end Co

section Lag

variable {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {v : Pl F} {m : ℕ}

/- English proof (translation)
Introduce `t ht` and use `by rw [← Matrix.mul_smul, ← Matrix.transpose_smul, h t ht, Matrix.transpose_zero, Matrix.mul_zero]`.
-/
theorem at_mul {Cy : Matrix (Fin d) (Fin m) (AE F E)} (h : At (evFin F v) Cy) (z : Matrix (Fin n) (Fin m) (AE F E)) :
    At (evFin F v) (z * Cyᵀ) := fun t ht => by
  rw [← Matrix.mul_smul, ← Matrix.transpose_smul, h t ht, Matrix.transpose_zero, Matrix.mul_zero]

/- English proof (translation)
Rewrite using `[symp, GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero (cA σ) _ h.iso, mul_zero, map_zero]`.
-/
theorem symp_lag {Cy : Matrix (Fin d) (Fin m) (AE F E)} (h : IsLagAt σ W v Cy) (ξ : AE F E)
    (z z' : Matrix (Fin n) (Fin m) (AE F E)) :
    symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (z * Cyᵀ) (z' * Cyᵀ) = 0 := by
  rw [symp, GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero (cA σ) _ h.iso, mul_zero, map_zero]

variable (v) in

def lagr (Cy : Matrix (Fin d) (Fin m) (AE F E)) :
    Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) where
  carrier := {w | ∃ z : Matrix (Fin n) (Fin m) (AE F E), locCo M.co v (z * Cyᵀ) = w}
  zero_mem' := ⟨0, by rw [Matrix.zero_mul, map_zero]⟩
  add_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
    exact ⟨z + z', by rw [Matrix.add_mul, map_add]⟩
  smul_mem' := by
    rintro a _ ⟨z, rfl⟩
    exact ⟨liftV v a • z, by rw [Matrix.smul_mul, GlobalTheory.LatOpenCpt.locCo_smul, evFin_liftV]⟩

/- English proof (translation)
Introduce and unpack `_ ⟨z, rfl⟩ _ ⟨z', rfl⟩`. Rewrite using `[← sub_eq_zero, ← ev_form, symp_lag h, map_zero]`.
-/
theorem lagr_iso {Cy : Matrix (Fin d) (Fin m) (AE F E)} (h : IsLagAt σ W v Cy) :
    ∀ w ∈ lagr M v Cy, ∀ w' ∈ lagr M v Cy, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2 := by
  rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩
  rw [← sub_eq_zero, ← ev_form, symp_lag h, map_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `hl _ ⟨z, rfl⟩ φ hφ`. Conclude with `hl z φ hφ _ ((acts_iff M.co ψ (at_mul h.supp z) hφ).2 rfl)`. Introduce `hl z φ hφ φ₁ h₁`. Rewrite using `[(acts_iff M.co ψ (at_mul h.supp z) hφ).1 h₁]`.

Conclude with `hl _ ⟨z, rfl⟩ φ hφ`.
-/
theorem isEvAt_iff {Cy : Matrix (Fin d) (Fin m) (AE F E)} (h : IsLagAt σ W v Cy) (ψ : AddChar (AF F) ℂ)
    (l : Fn F n d v →ₗ[ℂ] ℂ) :
    IsEvAt M ψ v Cy l ↔ ∀ w ∈ lagr M v Cy, ∀ φ ∈ SB _, l (schr (psiAt ψ v) w φ) = l φ := by
  constructor
  · rintro hl _ ⟨z, rfl⟩ φ hφ
    exact hl z φ hφ _ ((acts_iff M.co ψ (at_mul h.supp z) hφ).2 rfl)
  · intro hl z φ hφ φ₁ h₁
    rw [(acts_iff M.co ψ (at_mul h.supp z) hφ).1 h₁]
    exact hl _ ⟨z, rfl⟩ φ hφ

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hav, y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, hav, x, hx, y, hy, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[incM, Matrix.vecMulVec_apply]`. Consider the case `zero`. Establish `e : Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by`. Use extensionality with `i j`. Conclude with `mul_zero _`.

Rewrite using `[e]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [Matrix.vecMulVec_add]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [Matrix.vecMulVec_neg]`.

Conclude with `neg_mem ha`.
-/
theorem vecMulVec_mem {x : Fin n → E} (hx : x ∈ X.L) {y : Fin d → AE F E} (hy : y ∈ latW W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) y ∈ latAtV X W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, x, hx, y, hy, ?_⟩
    ext i j
    simp [incM, Matrix.vecMulVec_apply]
  | zero =>
    have e : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j
      exact mul_zero _
    rw [e]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.vecMulVec_add]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.vecMulVec_neg]; exact neg_mem ha

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]`.
-/
theorem vecMulVec_mulVec {R : Type} [CommRing R] (x : Fin n → R) (C : Matrix (Fin d) (Fin m) R) (s : Fin m → R) :
    Matrix.vecMulVec x (C *ᵥ s) = Matrix.vecMulVec x s * Cᵀ := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

/- English proof (translation)
Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hav, x, hx, y, hy, rfl⟩` from `hz`. Take `⟨s, t, hs, -, e⟩` from `h _ (AddSubgroup.subset_closure ⟨a, ha, hav, y, hy, rfl⟩)`. Use `⟨Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) s, Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) t, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← vecMulVec_mulVec]`. Conclude with `vecMulVec_mem hx hs`. Rewrite using `[← vecMulVec_mulVec, ← vecMulVec_mulVec, ← Matrix.vecMulVec_add, ← e]`. Use extensionality with `i j`. Simplify using `[incM, Matrix.vecMulVec_apply]`.

Consider the case `zero => exact ⟨0, 0, by rw [Matrix.zero_mul]; exact zero_mem _, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨z₁, z₁', h₁, rfl⟩` from `ha`. Take `⟨z₂, z₂', h₂, rfl⟩` from `hb`. Conclude with `⟨z₁ + z₂, z₁' + z₂', by rw [Matrix.add_mul]; exact add_mem h₁ h₂, by simp only [Matrix.add_mul]; abel⟩`.

Consider the case `neg a _ ha`. Take `⟨z₁, z₁', h₁, rfl⟩` from `ha`. Conclude with `⟨-z₁, -z₁', by rw [Matrix.neg_mul]; exact neg_mem h₁, by simp only [Matrix.neg_mul]; abel⟩`.
-/
theorem lat_split {Cy Cx : Matrix (Fin d) (Fin m) (AE F E)}
    (h : ∀ y ∈ latW W v, ∃ s t : Fin m → AE F E, Cy *ᵥ s ∈ latW W v ∧ Cx *ᵥ t ∈ latW W v ∧ y = Cy *ᵥ s + Cx *ᵥ t)
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    ∃ z z' : Matrix (Fin n) (Fin m) (AE F E), z * Cyᵀ ∈ latAtV X W v ∧ γ = z * Cyᵀ + z' * Cxᵀ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨s, t, hs, -, e⟩ := h _ (AddSubgroup.subset_closure ⟨a, ha, hav, y, hy, rfl⟩)
    refine ⟨Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) s,
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) t, ?_, ?_⟩
    · rw [← vecMulVec_mulVec]; exact vecMulVec_mem hx hs
    · rw [← vecMulVec_mulVec, ← vecMulVec_mulVec, ← Matrix.vecMulVec_add, ← e]
      ext i j
      simp [incM, Matrix.vecMulVec_apply]
  | zero => exact ⟨0, 0, by rw [Matrix.zero_mul]; exact zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨z₁, z₁', h₁, rfl⟩ := ha
    obtain ⟨z₂, z₂', h₂, rfl⟩ := hb
    exact ⟨z₁ + z₂, z₁' + z₂', by rw [Matrix.add_mul]; exact add_mem h₁ h₂, by simp only [Matrix.add_mul]; abel⟩
  | neg a _ ha =>
    obtain ⟨z₁, z₁', h₁, rfl⟩ := ha
    exact ⟨-z₁, -z₁', by rw [Matrix.neg_mul]; exact neg_mem h₁, by simp only [Matrix.neg_mul]; abel⟩

/- English proof (translation)
Establish `hu` using `GlobalTheory.LatOpenCpt.span_top (F := F) hX hW (fun p : X.L × W.L => Matrix.vecMulVec p.1.1 p.2.1) (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩) u`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨p, rfl⟩` from `hz`. Take `⟨z, z', -, e⟩` from `lat_split (X := X) h (AddSubgroup.subset_closure ⟨liftV v 1, at_liftV v 1, by rw [evFin_liftV]; exact one_mem _, p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩)`.

Conclude with `⟨z, z', e⟩`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨z₁, z₁', h₁⟩` from `ha`. Take `⟨z₂, z₂', h₂⟩` from `hb`.

Conclude with `⟨z₁ + z₂, z₁' + z₂', by rw [smul_add, h₁, h₂]; simp only [Matrix.add_mul]; abel⟩`. Consider the case `smul a x _ hx`. Take `⟨z₁, z₁', h₁⟩` from `hx`. Conclude with `⟨a • z₁, a • z₁', by rw [smul_comm, h₁, smul_add, Matrix.smul_mul, Matrix.smul_mul]⟩`.
-/
theorem space_split (hX : X.L.IsLattice E) (hW : W.L.IsLattice E) {Cy Cx : Matrix (Fin d) (Fin m) (AE F E)}
    (h : ∀ y ∈ latW W v, ∃ s t : Fin m → AE F E, Cy *ᵥ s ∈ latW W v ∧ Cx *ᵥ t ∈ latW W v ∧ y = Cy *ᵥ s + Cx *ᵥ t)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ z z' : Matrix (Fin n) (Fin m) (AE F E), liftV v 1 • u = z * Cyᵀ + z' * Cxᵀ := by
  have hu := GlobalTheory.LatOpenCpt.span_top (F := F) hX hW (fun p : X.L × W.L => Matrix.vecMulVec p.1.1 p.2.1)
    (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩) u
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, rfl⟩ := hz
    obtain ⟨z, z', -, e⟩ := lat_split (X := X) h (AddSubgroup.subset_closure
      ⟨liftV v 1, at_liftV v 1, by rw [evFin_liftV]; exact one_mem _, p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩)
    exact ⟨z, z', e⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨z₁, z₁', h₁⟩ := ha
    obtain ⟨z₂, z₂', h₂⟩ := hb
    exact ⟨z₁ + z₂, z₁' + z₂', by rw [smul_add, h₁, h₂]; simp only [Matrix.add_mul]; abel⟩
  | smul a x _ hx =>
    obtain ⟨z₁, z₁', h₁⟩ := hx
    exact ⟨a • z₁, a • z₁', by rw [smul_comm, h₁, smul_add, Matrix.smul_mul, Matrix.smul_mul]⟩

end Lag

end PositivityTheory.ThKH.Evl
