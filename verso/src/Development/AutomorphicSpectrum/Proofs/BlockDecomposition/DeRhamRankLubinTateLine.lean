import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.CoeTo1
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitDetEmbMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.TiedAInvOfTheta
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTRead

open Module TensorProduct GlobalTheory.CompanionTheory.DeRhamChar

/- English proof (translation)
Set `e : A ≃ₐ[F] α.fieldRange` to `AlgEquiv.ofInjectiveField α`. Take `⟨φ, hφ⟩` from `IntermediateField.exists_algHom_of_adjoin_splits (F := F) (E := B) (K := C) (S := Set.univ) (fun s _ => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (β.comp e.symm.toAlgHom) (IntermediateField.adjoin_univ F B)`. Use `⟨φ, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `DFunLike.congr_fun hφ (e x)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_lift {F A B C : Type} [Field F] [Field A] [Field B] [Field C] [Algebra F A] [Algebra F B]
    [Algebra F C] [Algebra.IsAlgebraic F B] [IsAlgClosed C] (α : A →ₐ[F] B) (β : A →ₐ[F] C) :
    ∃ φ : B →ₐ[F] C, ∀ x, φ (α x) = β x := by
  let e : A ≃ₐ[F] α.fieldRange := AlgEquiv.ofInjectiveField α
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_adjoin_splits (F := F) (E := B) (K := C)
    (S := Set.univ) (fun s _ => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩)
    (β.comp e.symm.toAlgHom) (IntermediateField.adjoin_univ F B)
  refine ⟨φ, fun x => ?_⟩
  have h1 := DFunLike.congr_fun hφ (e x)
  calc φ (α x) = (φ.comp α.fieldRange.val) (e x) := rfl
    _ = (β.comp e.symm.toAlgHom) (e x) := h1
    _ = β (e.symm (e x)) := rfl
    _ = β x := by rw [e.symm_apply_apply]

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h` using `(P.PD K).Fil_mul 0 a _ _ ((GlobalTheory.DeRhamSymbol.mem_iff K 0 _).2 (GlobalTheory.DeRhamSymbol.om_mem (P := P) c)) hb`. Rewrite `h` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem om_mul_mem (P : LocPrime l) (K : FinExt l) (a : ℤ) (c : Om l) {b : P.R.BdR}
    (hb : b ∈ (P.PD K).Fil a) : algebraMap (Om l) P.R.BdR c * b ∈ (P.PD K).Fil a := by
  have h := (P.PD K).Fil_mul 0 a _ _
    ((GlobalTheory.DeRhamSymbol.mem_iff K 0 _).2 (GlobalTheory.DeRhamSymbol.om_mem (P := P) c)) hb
  rwa [zero_add] at h

/- English proof (translation)
The claim follows from `(GlobalTheory.DeRhamSymbol.mem_iff K a _).2 (GlobalTheory.DeRhamSymbol.act_mem g ((GlobalTheory.DeRhamSymbol.mem_iff K a _).1 hb))`.
-/
theorem act_mem (P : LocPrime l) (K : FinExt l) (a : ℤ) (g : GQ l) {b : P.R.BdR}
    (hb : b ∈ (P.PD K).Fil a) : P.actQdR g b ∈ (P.PD K).Fil a :=
  (GlobalTheory.DeRhamSymbol.mem_iff K a _).2
    (GlobalTheory.DeRhamSymbol.act_mem g ((GlobalTheory.DeRhamSymbol.mem_iff K a _).1 hb))

/- English proof (translation)
Establish `J` using `PositivityTheory.LocInh.thetaL T`. Establish `tr` using `fun (b : ℤ) (w : P.R.BdR) => GlobalTheory.DeRhamSymbol.mem_iff (P := P) K b w`. Use `set τ : P.R.BdR := ((GlobalTheory.DeRhamSymbol.tU P ^ (-d) : P.R.BdRˣ) : P.R.BdR) with hτ`. Establish `h0 : τ * y ∈ (P.PD K).Fil 0`. Rewrite using `[tr, hτ, GlobalTheory.DeRhamSymbol.shift_iff J, add_zero, ← tr]`.

Conclude with `hy`. Establish `h1 : τ * y ∉ (P.PD K).Fil 1`. Rewrite using `[tr, hτ, GlobalTheory.DeRhamSymbol.shift_iff J, ← tr]`. Conclude with `hy'`. Take `⟨w, hw, hyw⟩` from `(PositivityTheory.LocInh.tied_field l P AI T).2.2.2.2 K _ h0 h1`.

Establish `e : u = τ * w`. Combine the equalities or inequalities in the displayed calculation. Establish `hτm : τ ∈ (P.PD K).Fil (-d)` using `(tr _ _).2 (GlobalTheory.DeRhamSymbol.zpow_mem J (-d))`. Prove the components needed by the constructor for the conclusion. Rewrite using `[e]`.

Use `(P.PD K).Fil_mul _ _ _ _ hτm hw` as an intermediate fact. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis. Introduce `hu1`. Establish `h2` using `(P.PD K).Fil_mul _ _ _ _ hy hu1`. Rewrite `h2` using `[hu, show d + (-d + 1) = 1 by ring]`.

Apply `(P.PD K).not_mem_filtration_two` to reduce the goal to its premises. Use `(P.PD K).Fil_mul 1 1 _ _ (P.PD K).mem_filtration_one h2` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem inv_fil {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) (K : FinExt l) (d : ℤ)
    {y u : P.R.BdR} (hy : y ∈ (P.PD K).Fil d) (hy' : y ∉ (P.PD K).Fil (d + 1)) (hu : y * u = 1) :
    u ∈ (P.PD K).Fil (-d) ∧ u ∉ (P.PD K).Fil (-d + 1) := by
  have J := PositivityTheory.LocInh.thetaL T
  have tr := fun (b : ℤ) (w : P.R.BdR) => GlobalTheory.DeRhamSymbol.mem_iff (P := P) K b w
  set τ : P.R.BdR := ((GlobalTheory.DeRhamSymbol.tU P ^ (-d) : P.R.BdRˣ) : P.R.BdR) with hτ
  have h0 : τ * y ∈ (P.PD K).Fil 0 := by
    rw [tr, hτ, GlobalTheory.DeRhamSymbol.shift_iff J, add_zero, ← tr]
    exact hy
  have h1 : τ * y ∉ (P.PD K).Fil 1 := by
    rw [tr, hτ, GlobalTheory.DeRhamSymbol.shift_iff J, ← tr]
    exact hy'
  obtain ⟨w, hw, hyw⟩ := (PositivityTheory.LocInh.tied_field l P AI T).2.2.2.2 K _ h0 h1
  have e : u = τ * w := by
    calc u = (τ * y * w) * u := by rw [hyw, one_mul]
      _ = (y * u) * (τ * w) := by ring
      _ = τ * w := by rw [hu, one_mul]
  have hτm : τ ∈ (P.PD K).Fil (-d) := (tr _ _).2 (GlobalTheory.DeRhamSymbol.zpow_mem J (-d))
  constructor
  · rw [e]
    have := (P.PD K).Fil_mul _ _ _ _ hτm hw
    rwa [add_zero] at this
  · intro hu1
    have h2 := (P.PD K).Fil_mul _ _ _ _ hy hu1
    rw [hu, show d + (-d + 1) = 1 by ring] at h2
    apply (P.PD K).not_mem_filtration_two
    have := (P.PD K).Fil_mul 1 1 _ _ (P.PD K).mem_filtration_one h2
    rwa [mul_one] at this

section Coord

variable (P : LocPrime l) (K LL : FinExt l)

/- English proof (translation)
Use `haveI := LL.2`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩ σ`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul v b`. Rewrite using `[AlgebraTensorModule.map_tmul]`. Simplify using `only [LinearMap.id_apply, ev_tmul]`. Conclude with `om_mul_mem P K a _ b.2`. Consider the case `add x y hx hy`.

Rewrite using `[map_add, map_add]`. Conclude with `(P.PD K).Fil a |>.add_mem hx hy`. Introduce `h`. Rewrite using `[← coordInv_ev (Om := Om l) z]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Use `⟨(fun _ => embBasis ℚ_[l] (Om l) ↥LL.1 i) ⊗ₜ ⟨_, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun j _ => om_mul_mem P K a _ (h j)`.
-/
theorem mem_filV_iff (a : ℤ) (z : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    z ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) a ↔
      ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, ev σ z ∈ (P.PD K).Fil a := by
  haveI := LL.2
  constructor
  · rintro ⟨x, rfl⟩ σ
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [AlgebraTensorModule.map_tmul]
      simp only [LinearMap.id_apply, ev_tmul]
      exact om_mul_mem P K a _ b.2
    | add x y hx hy =>
      rw [map_add, map_add]
      exact (P.PD K).Fil a |>.add_mem hx hy
  · intro h
    rw [← coordInv_ev (Om := Om l) z]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine ⟨(fun _ => embBasis ℚ_[l] (Om l) ↥LL.1 i) ⊗ₜ ⟨_, ?_⟩, rfl⟩
    exact Submodule.sum_mem _ fun j _ => om_mul_mem P K a _ (h j)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Rewrite using `[GlobalTheory.DeRhamSplit.mulVdR_tmul]`. Simplify using `only [ev_tmul]`.

Express the relevant statement in the definitionally equal form `_ * (algebraMap (Om l) P.R.BdR (c : Om l) * b) = _`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy => simp only [map_add, hx, hy, mul_add]`.
-/
theorem ev_mulVdR (c : ↥K.1) (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (z : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    ev σ (mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := Fin 1 → ↥LL.1) (LL := ↥LL.1) c z) =
      algebraMap (Om l) P.R.BdR (c : Om l) * ev σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [GlobalTheory.DeRhamSplit.mulVdR_tmul]
    simp only [ev_tmul]
    change _ * (algebraMap (Om l) P.R.BdR (c : Om l) * b) = _
    ring
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

variable {K LL}

/- English proof (translation)
Use extensionality with `i`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Simplify using `[lineRep, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]`.
-/
theorem lineRep_apply (ψ : ↥(GK K) →* (↥LL.1)ˣ) (g : ↥(GK K)) (v : Fin 1 → ↥LL.1) :
    lineRep ψ g v = ((ψ g : (↥LL.1)ˣ) : ↥LL.1) • v := by
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [lineRep, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

def gc (g : ↥(GK K)) (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →ₐ[ℚ_[l]] Om l :=
  ((g : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp σ

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem gc_apply (g : ↥(GK K)) (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (x : ↥LL.1) :
    gc g σ x = (g : GQ l) (σ x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gc_mul (g h : ↥(GK K)) (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l) : gc (g * h) σ = gc g (gc h σ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gc_one (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l) : gc (1 : ↥(GK K)) σ = σ := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Establish `h1 : actVdR (P.PD K) (lineRep ψ) g (v ⊗ₜ b) = lineRep ψ g v ⊗ₜ (P.PD K).actdR g b`. Simplify using `[actVdR]`.

Rewrite using `[h1, ev_tmul, ev_tmul, lineRep_apply, P.PD_actdR, map_mul, P.actQdR_Om]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, gc_apply, mul_assoc]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, mul_add]`.
-/
theorem ev_act (ψ : ↥(GK K) →* (↥LL.1)ˣ) (g : ↥(GK K)) (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l)
    (z : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    ev (gc g σ) (actVdR (P.PD K) (lineRep ψ) g z) =
      algebraMap (Om l) P.R.BdR (gc g σ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) (ev σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    have h1 : actVdR (P.PD K) (lineRep ψ) g (v ⊗ₜ b) = lineRep ψ g v ⊗ₜ (P.PD K).actdR g b := by
      simp [actVdR]
    rw [h1, ev_tmul, ev_tmul, lineRep_apply, P.PD_actdR, map_mul, P.actQdR_Om]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, gc_apply, mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

end Coord

section Line

variable (P : LocPrime l) {K LL : FinExt l}

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_lift σ₀ σ`. Establish `hb : Function.Bijective φ` using `Algebra.IsAlgebraic.algHom_bijective φ`. Set `g : GQ l` to `AlgEquiv.ofBijective φ hb`. Establish `hg : ∀ x, g x = φ x` using `fun _ => rfl`. Use `⟨⟨g, ?_⟩, AlgHom.ext fun x => hφ x⟩` and prove the remaining obligations.

Introduce `c`. Express the relevant statement in the definitionally equal form `g (c : Om l) = c`. Rewrite using `[← h₀ c, hg, hφ, h₀, h]`.
-/
theorem exists_conj (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) {σ₀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l}
    (h₀ : ∀ c : ↥K.1, σ₀ (τ' c) = c) (h : ∀ c : ↥K.1, σ (τ' c) = c) :
    ∃ g : ↥(GK K), gc g σ₀ = σ := by
  obtain ⟨φ, hφ⟩ := exists_lift σ₀ σ
  have hb : Function.Bijective φ := Algebra.IsAlgebraic.algHom_bijective φ
  let g : GQ l := AlgEquiv.ofBijective φ hb
  have hg : ∀ x, g x = φ x := fun _ => rfl
  refine ⟨⟨g, ?_⟩, AlgHom.ext fun x => hφ x⟩
  intro c
  change g (c : Om l) = c
  rw [← h₀ c, hg, hφ, h₀, h]

/- English proof (translation)
Rewrite using `[map_mul, P.actQdR_Om]`.
-/
theorem act_om_mul (g : GQ l) (x : Om l) (b : P.R.BdR) :
    P.actQdR g (algebraMap (Om l) P.R.BdR x * b) = algebraMap (Om l) P.R.BdR (g x) * P.actQdR g b := by
  rw [map_mul, P.actQdR_Om]

def genCoord (ψ : ↥(GK K) →* (↥LL.1)ˣ) (σ₀ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (u : P.R.BdR)
    (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l) : P.R.BdR :=
  if h : ∃ g : ↥(GK K), gc g σ₀ = σ then
    algebraMap (Om l) P.R.BdR (σ ((ψ h.choose : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (h.choose : GQ l) u
  else 0

/- English proof (translation)
Establish `h : ∃ g' : ↥(GK K), gc g' σ₀ = gc g σ₀` using `⟨g, rfl⟩`. Rewrite using `[genCoord, dif_pos h]`. Establish `hs` using `h.choose_spec`. Take `⟨k, hk⟩ : ∃ k, h.choose = g * k` from `⟨g⁻¹ * h.choose, by group⟩`. Rewrite `hs`, the goal using `[hk]`.

Establish `hk' : gc k σ₀ = σ₀`. Use `congrArg (gc g⁻¹) hs` as an intermediate fact. Rewrite `this` using `[← gc_mul, ← gc_mul, inv_mul_cancel_left, inv_mul_cancel, gc_one]`. Then use the resulting hypothesis. Establish `key` using `hu k hk'`. Use `conv_rhs => rw [← key]`.

Rewrite using `[act_om_mul]`. Simplify using `only [map_mul, Units.val_mul, gc_apply, Subgroup.coe_mul, AlgEquiv.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genCoord_orbit (ψ : ↥(GK K) →* (↥LL.1)ˣ) {σ₀ : ↥LL.1 →ₐ[ℚ_[l]] Om l} {u : P.R.BdR}
    (hu : ∀ g : ↥(GK K), gc g σ₀ = σ₀ →
      algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) u = u)
    (g : ↥(GK K)) :
    genCoord P ψ σ₀ u (gc g σ₀) =
      algebraMap (Om l) P.R.BdR (gc g σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) u := by
  have h : ∃ g' : ↥(GK K), gc g' σ₀ = gc g σ₀ := ⟨g, rfl⟩
  rw [genCoord, dif_pos h]
  have hs := h.choose_spec
  obtain ⟨k, hk⟩ : ∃ k, h.choose = g * k := ⟨g⁻¹ * h.choose, by group⟩
  rw [hk] at hs ⊢
  have hk' : gc k σ₀ = σ₀ := by
    have := congrArg (gc g⁻¹) hs
    rwa [← gc_mul, ← gc_mul, inv_mul_cancel_left, inv_mul_cancel, gc_one] at this
  have key := hu k hk'
  conv_rhs => rw [← key]
  rw [act_om_mul]
  simp only [map_mul, Units.val_mul, gc_apply, Subgroup.coe_mul, AlgEquiv.mul_apply]
  ring

/- English proof (translation)
Distinguish the cases in `hσ : ∃ g₁ : ↥(GK K), gc g₁ σ₀ = σ`. Take `⟨g₁, rfl⟩` from `hσ`. Rewrite using `[← gc_mul, genCoord_orbit P ψ hu, genCoord_orbit P ψ hu, act_om_mul]`. Simplify using `only [map_mul, Units.val_mul, gc_apply, Subgroup.coe_mul, AlgEquiv.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : ¬ ∃ g' : ↥(GK K), gc g' σ₀ = gc g σ`. Introduce and unpack `⟨g', h⟩`. Use `hσ ⟨g⁻¹ * g', ?_⟩` and prove the remaining obligations. Rewrite using `[gc_mul, h, ← gc_mul, inv_mul_cancel, gc_one]`. Rewrite using `[genCoord, dif_neg h2, genCoord, dif_neg hσ, map_zero, mul_zero]`.
-/
theorem genCoord_law (ψ : ↥(GK K) →* (↥LL.1)ˣ) {σ₀ : ↥LL.1 →ₐ[ℚ_[l]] Om l} {u : P.R.BdR}
    (hu : ∀ g : ↥(GK K), gc g σ₀ = σ₀ →
      algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) u = u)
    (g : ↥(GK K)) (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l) :
    genCoord P ψ σ₀ u (gc g σ) =
      algebraMap (Om l) P.R.BdR (gc g σ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) *
        P.actQdR (g : GQ l) (genCoord P ψ σ₀ u σ) := by
  by_cases hσ : ∃ g₁ : ↥(GK K), gc g₁ σ₀ = σ
  · obtain ⟨g₁, rfl⟩ := hσ
    rw [← gc_mul, genCoord_orbit P ψ hu, genCoord_orbit P ψ hu, act_om_mul]
    simp only [map_mul, Units.val_mul, gc_apply, Subgroup.coe_mul, AlgEquiv.mul_apply]
    ring
  · have h2 : ¬ ∃ g' : ↥(GK K), gc g' σ₀ = gc g σ := by
      rintro ⟨g', h⟩
      refine hσ ⟨g⁻¹ * g', ?_⟩
      rw [gc_mul, h, ← gc_mul, inv_mul_cancel, gc_one]
    rw [genCoord, dif_neg h2, genCoord, dif_neg hσ, map_zero, mul_zero]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use `haveI := LL.2`. Establish `hF` using `(PositivityTheory.LocInh.tied_field l P AI T).1`. Use `haveI : IsDomain P.R.BdR := hF.isDomain`. Establish `hy0 : y ≠ 0` using `fun h => hd2 (h ▸ Submodule.zero_mem _)`. Take `⟨u, hyu⟩` from `hF.mul_inv_cancel hy0`.

Take `⟨hu1, hu2⟩` from `inv_fil T K d hd1 hd2 hyu`. Establish `hlaw : ∀ g : ↥(GK K), gc g σ₀ = σ₀ → algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) u = u`. Introduce `g hg`. Establish `h1 : P.actQdR (g : GQ l) y * P.actQdR (g : GQ l) u = 1`. Rewrite using `[← map_mul, hyu, map_one]`.

Rewrite `h1` using `[hact g hg]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hyu, one_mul]`. Use `_ = (algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * y * P.actQdR (g : GQ l) u) * u := by ring`. Use `_ = u := by rw [h1, one_mul]`.

Use `set f := genCoord P ψ σ₀ u with hf`. Use `set z : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR := coordInv (Om := Om l) f with hzdef`. Establish `hz : ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, ev σ z = f σ` using `fun σ => ev_coordInv f σ`. Establish `hoff : ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, (¬ ∃ g : ↥(GK K), gc g σ₀ = σ) → f σ = 0` using `fun σ h => dif_neg h`. Establish `hinv : ∀ g, actVdR (P.PD K) (lineRep ψ) g z = z` using `fun g => ev_injective (Om := Om l) fun σ => by`.

Take `⟨σ', rfl⟩ : ∃ σ', gc g σ' = σ` from `⟨gc g⁻¹ σ, by rw [← gc_mul, mul_inv_cancel, gc_one]⟩`. Rewrite using `[ev_act, hz, hz, hf, genCoord_law P ψ hlaw]`. Establish `hS : ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, (∀ c : ↥K.1, σ (τ' c) = c) ↔ ∃ g : ↥(GK K), gc g σ₀ = σ` using `fun σ => ⟨fun h => exists_conj τ' h₀ h, by`. Introduce and unpack `⟨g, rfl⟩ c`. Rewrite using `[gc_apply, h₀]`.

Conclude with `g.2 c⟩`. Establish `hzE : z ∈ DdRE (P.PD K) (lineRep ψ) τ'`. Rewrite using `[mem_DdRE_iff]`. Use `⟨(mem_DdR_iff _ _ _).2 hinv, fun c => ev_injective (Om := Om l) fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[ev_mulVdR, ev_smul, hz]`.

Distinguish the cases in `h : ∃ g : ↥(GK K), gc g σ₀ = σ`. Rewrite using `[(hS σ).2 h c]`. Rewrite using `[hoff σ h, mul_zero, mul_zero]`. Use `⟨z, hzE, fun w hw => ?_, (mem_filV_iff P K LL _ _).2 fun σ => ?_, fun hmem => ?_⟩` and prove the remaining obligations. Take `⟨hwD, hwc⟩` from `(mem_DdRE_iff _ _ _ _).1 hw`.

Establish `hwi` using `(mem_DdR_iff _ _ _).1 hwD`. Establish `hlaww : ∀ (g : ↥(GK K)) (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l), ev (gc g σ) w = algebraMap (Om l) P.R.BdR (gc g σ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) (ev σ w)` using `fun g σ => by rw [← ev_act P ψ g σ w, hwi g]`. Establish `hzero : ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, (¬ ∃ g : ↥(GK K), gc g σ₀ = σ) → ev σ w = 0`. Introduce `σ h`. Assume the negation of the conclusion as `hne`.

Use `h ((hS σ).1 fun c => ?_)` and prove the remaining obligations. Establish `h1 : algebraMap (Om l) P.R.BdR (c : Om l) * ev σ w = algebraMap (Om l) P.R.BdR (σ (τ' c)) * ev σ w`. Rewrite using `[← ev_mulVdR P K LL c σ w, ← ev_smul σ (τ' c) w]`. Conclude with `congrArg (ev σ) (hwc c)`. Conclude with `((algebraMap (Om l) P.R.BdR).injective (mul_right_cancel₀ hne h1)).symm`.

Establish `hfin : FiniteDimensional ℚ_[l] σ₀.fieldRange` using `LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField σ₀).toLinearEquiv`. Take `⟨L, hL⟩ : ∃ L : FinExt l, L.1 = σ₀.fieldRange` from `⟨⟨_, hfin⟩, rfl⟩`. Establish `hLm : ∀ x : ↥LL.1, σ₀ x ∈ L.1` using `fun x => hL ▸ ⟨x, rfl⟩`. Take `⟨c₀, hc₀⟩` from `(P.PD L).invdR (ev σ₀ w * y) (fun g => by`. Establish `hgK : (g : GQ l) ∈ GK K` using `fun c => by`.

Establish `hc : (c : Om l) ∈ L.1` using `h₀ c ▸ hLm (τ' c)`. Conclude with `g.2 ⟨_, hc⟩`. Take `⟨g', hg'⟩ : ∃ g' : ↥(GK K), (g' : GQ l) = g` from `⟨⟨g, hgK⟩, rfl⟩`. Establish `hs : gc g' σ₀ = σ₀` using `AlgHom.ext fun x => by`. Rewrite using `[gc_apply, hg']`.

Conclude with `g.2 ⟨σ₀ x, hLm x⟩`. Establish `h1` using `hlaww g' σ₀`. Rewrite `h1` using `[hs]`. Rewrite using `[P.PD_actdR, ← hg', map_mul, hact g' hs]`. Use `conv_rhs => rw [h1]`.

Use the proof step `ring)`. Establish `hLr : ∀ x ∈ L.1, ∃ c' : ↥LL.1, σ₀ c' = x` using `fun x hx => by`. Rewrite `hx` using `[hL]`. Conclude with `hx`. Take `⟨c', hc'⟩` from `hLr _ c₀.2`.

Establish `hb0 : ev σ₀ w = algebraMap (Om l) P.R.BdR (σ₀ c') * u`. Establish `h1 : algebraMap (Om l) P.R.BdR (σ₀ c') = ev σ₀ w * y`. Rewrite using `[hc']`. Conclude with `hc₀`. Rewrite using `[h1, mul_assoc, hyu, mul_one]`.

Use `⟨c', ev_injective (Om := Om l) fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[ev_smul, hz]`. Distinguish the cases in `h : ∃ g : ↥(GK K), gc g σ₀ = σ`. Take `⟨g, rfl⟩` from `h`. Rewrite using `[hlaww, hb0, hf, genCoord_orbit P ψ hlaw, act_om_mul]`.

Simplify using `only [gc_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hzero σ h, hoff σ h, mul_zero]`. Rewrite using `[hz]`. Distinguish the cases in `h : ∃ g : ↥(GK K), gc g σ₀ = σ`.

Take `⟨g, rfl⟩` from `h`. Rewrite using `[hf, genCoord_orbit P ψ hlaw]`. Conclude with `om_mul_mem P K _ _ (act_mem P K _ _ hu1)`. Rewrite using `[hoff σ h]`. Conclude with `Submodule.zero_mem _`.

Establish `h1` using `(mem_filV_iff P K LL _ _).1 hmem σ₀`. Rewrite `h1` using `[hz]`. Establish `e : f σ₀ = u`. Establish `h2` using `genCoord_orbit P ψ hlaw (1 : ↥(GK K))`. Rewrite `h2` using `[gc_one]`.

Rewrite using `[hf, h2]`. Simplify using the standard rewrite rules. Conclude with `hu2 (e ▸ h1)`.
-/
theorem component_line {AI : LocAinf l P} (T : LocTied6 l P AI) (ψ : ↥(GK K) →* (↥LL.1)ˣ)
    (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (σ₀ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (h₀ : ∀ c : ↥K.1, σ₀ (τ' c) = c)
    (y : P.R.BdR)
    (hact : ∀ g : ↥(GK K), gc g σ₀ = σ₀ →
      P.actQdR (g : GQ l) y = algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * y)
    (d : ℤ) (hd1 : y ∈ (P.PD K).Fil d) (hd2 : y ∉ (P.PD K).Fil (d + 1)) :
    ∃ z ∈ DdRE (P.PD K) (lineRep ψ) τ', (∀ w ∈ DdRE (P.PD K) (lineRep ψ) τ', ∃ c : ↥LL.1, w = c • z) ∧
      z ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) (-d) ∧
      z ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) (-d + 1) := by
  haveI := LL.2
  have hF := (PositivityTheory.LocInh.tied_field l P AI T).1
  haveI : IsDomain P.R.BdR := hF.isDomain
  have hy0 : y ≠ 0 := fun h => hd2 (h ▸ Submodule.zero_mem _)
  obtain ⟨u, hyu⟩ := hF.mul_inv_cancel hy0
  obtain ⟨hu1, hu2⟩ := inv_fil T K d hd1 hd2 hyu
  have hlaw : ∀ g : ↥(GK K), gc g σ₀ = σ₀ →
      algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) u = u := by
    intro g hg
    have h1 : P.actQdR (g : GQ l) y * P.actQdR (g : GQ l) u = 1 := by
      rw [← map_mul, hyu, map_one]
    rw [hact g hg] at h1
    calc _ = (y * u) * (algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) u) := by
            rw [hyu, one_mul]
      _ = (algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * y * P.actQdR (g : GQ l) u) * u := by ring
      _ = u := by rw [h1, one_mul]
  set f := genCoord P ψ σ₀ u with hf
  set z : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR := coordInv (Om := Om l) f with hzdef
  have hz : ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, ev σ z = f σ := fun σ => ev_coordInv f σ
  have hoff : ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, (¬ ∃ g : ↥(GK K), gc g σ₀ = σ) → f σ = 0 :=
    fun σ h => dif_neg h
  have hinv : ∀ g, actVdR (P.PD K) (lineRep ψ) g z = z := fun g => ev_injective (Om := Om l) fun σ => by
    obtain ⟨σ', rfl⟩ : ∃ σ', gc g σ' = σ := ⟨gc g⁻¹ σ, by rw [← gc_mul, mul_inv_cancel, gc_one]⟩
    rw [ev_act, hz, hz, hf, genCoord_law P ψ hlaw]
  have hS : ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, (∀ c : ↥K.1, σ (τ' c) = c) ↔ ∃ g : ↥(GK K), gc g σ₀ = σ := fun σ =>
    ⟨fun h => exists_conj τ' h₀ h, by
      rintro ⟨g, rfl⟩ c
      rw [gc_apply, h₀]
      exact g.2 c⟩
  have hzE : z ∈ DdRE (P.PD K) (lineRep ψ) τ' := by
    rw [mem_DdRE_iff]
    refine ⟨(mem_DdR_iff _ _ _).2 hinv, fun c => ev_injective (Om := Om l) fun σ => ?_⟩
    rw [ev_mulVdR, ev_smul, hz]
    by_cases h : ∃ g : ↥(GK K), gc g σ₀ = σ
    · rw [(hS σ).2 h c]
    · rw [hoff σ h, mul_zero, mul_zero]
  refine ⟨z, hzE, fun w hw => ?_, (mem_filV_iff P K LL _ _).2 fun σ => ?_, fun hmem => ?_⟩
  · obtain ⟨hwD, hwc⟩ := (mem_DdRE_iff _ _ _ _).1 hw
    have hwi := (mem_DdR_iff _ _ _).1 hwD
    have hlaww : ∀ (g : ↥(GK K)) (σ : ↥LL.1 →ₐ[ℚ_[l]] Om l), ev (gc g σ) w =
        algebraMap (Om l) P.R.BdR (gc g σ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * P.actQdR (g : GQ l) (ev σ w) :=
      fun g σ => by rw [← ev_act P ψ g σ w, hwi g]
    have hzero : ∀ σ : ↥LL.1 →ₐ[ℚ_[l]] Om l, (¬ ∃ g : ↥(GK K), gc g σ₀ = σ) → ev σ w = 0 := by
      intro σ h
      by_contra hne
      refine h ((hS σ).1 fun c => ?_)
      have h1 : algebraMap (Om l) P.R.BdR (c : Om l) * ev σ w =
          algebraMap (Om l) P.R.BdR (σ (τ' c)) * ev σ w := by
        rw [← ev_mulVdR P K LL c σ w, ← ev_smul σ (τ' c) w]
        exact congrArg (ev σ) (hwc c)
      exact ((algebraMap (Om l) P.R.BdR).injective (mul_right_cancel₀ hne h1)).symm
    have hfin : FiniteDimensional ℚ_[l] σ₀.fieldRange :=
      LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField σ₀).toLinearEquiv
    obtain ⟨L, hL⟩ : ∃ L : FinExt l, L.1 = σ₀.fieldRange := ⟨⟨_, hfin⟩, rfl⟩
    have hLm : ∀ x : ↥LL.1, σ₀ x ∈ L.1 := fun x => hL ▸ ⟨x, rfl⟩
    obtain ⟨c₀, hc₀⟩ := (P.PD L).invdR (ev σ₀ w * y) (fun g => by
      have hgK : (g : GQ l) ∈ GK K := fun c => by
        have hc : (c : Om l) ∈ L.1 := h₀ c ▸ hLm (τ' c)
        exact g.2 ⟨_, hc⟩
      obtain ⟨g', hg'⟩ : ∃ g' : ↥(GK K), (g' : GQ l) = g := ⟨⟨g, hgK⟩, rfl⟩
      have hs : gc g' σ₀ = σ₀ := AlgHom.ext fun x => by
        rw [gc_apply, hg']
        exact g.2 ⟨σ₀ x, hLm x⟩
      have h1 := hlaww g' σ₀
      rw [hs] at h1
      rw [P.PD_actdR, ← hg', map_mul, hact g' hs]
      conv_rhs => rw [h1]
      ring)
    have hLr : ∀ x ∈ L.1, ∃ c' : ↥LL.1, σ₀ c' = x := fun x hx => by
      rw [hL] at hx
      exact hx
    obtain ⟨c', hc'⟩ := hLr _ c₀.2
    have hb0 : ev σ₀ w = algebraMap (Om l) P.R.BdR (σ₀ c') * u := by
      have h1 : algebraMap (Om l) P.R.BdR (σ₀ c') = ev σ₀ w * y := by
        rw [hc']
        exact hc₀
      rw [h1, mul_assoc, hyu, mul_one]
    refine ⟨c', ev_injective (Om := Om l) fun σ => ?_⟩
    rw [ev_smul, hz]
    by_cases h : ∃ g : ↥(GK K), gc g σ₀ = σ
    · obtain ⟨g, rfl⟩ := h
      rw [hlaww, hb0, hf, genCoord_orbit P ψ hlaw, act_om_mul]
      simp only [gc_apply]
      ring
    · rw [hzero σ h, hoff σ h, mul_zero]
  · rw [hz]
    by_cases h : ∃ g : ↥(GK K), gc g σ₀ = σ
    · obtain ⟨g, rfl⟩ := h
      rw [hf, genCoord_orbit P ψ hlaw]
      exact om_mul_mem P K _ _ (act_mem P K _ _ hu1)
    · rw [hoff σ h]
      exact Submodule.zero_mem _
  · have h1 := (mem_filV_iff P K LL _ _).1 hmem σ₀
    rw [hz] at h1
    have e : f σ₀ = u := by
      have h2 := genCoord_orbit P ψ hlaw (1 : ↥(GK K))
      rw [gc_one] at h2
      rw [hf, h2]
      simp
    exact hu2 (e ▸ h1)

end Line

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce and unpack `l _ P AI ⟨T⟩ K LL hsplit χ hP τ`. Use `haveI := K.2`. Use `haveI := LL.2`. Use `set ψ : ↥(GK K) →* (↥LL.1)ˣ := (Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ with hψ`. Establish `key : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ z ∈ DdRE (P.PD K) (lineRep ψ) τ', (∀ w ∈ DdRE (P.PD K) (lineRep ψ) τ', ∃ c : ↥LL.1, w = c • z) ∧ z ∈ FilV (P.PD K) (LL` using `↥LL.1) (V := Fin 1 → ↥LL.1) (if τ' = τ then (-1 : ℤ) else 0) ∧ z ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) ((if τ' = τ then (-1 : ℤ) else 0) + 1) := by`.

Introduce `τ'`. Take `⟨σ₀, h₀⟩` from `exists_lift τ' K.1.val`. Take `⟨y, hyact, h1, h2⟩` from `hP (σ₀.comp τ)`. Establish `hact : ∀ g : ↥(GK K), gc g σ₀ = σ₀ → P.actQdR (g : GQ l) y = algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * y` using `fun g hg => hyact g.1 g.2 fun x => DFunLike.congr_fun hg (τ x)`. Distinguish the cases in `hτ : τ' = τ`.

Establish `hμ : σ₀.comp τ = K.1.val` using `AlgHom.ext fun x => by`. Rewrite using `[AlgHom.comp_apply, ← hτ]`. Conclude with `h₀ x`. Take `⟨m1, m2⟩` from `h1 hμ`. Rewrite using `[if_pos hτ]`.

Establish `m2' : y ∉ (P.PD K).Fil (1 + 1)`. Rewrite using `[show (1 + 1 : ℤ) = 2 by norm_num]`. Conclude with `m2`. Conclude with `component_line P T ψ τ' σ₀ h₀ y hact 1 m1 m2'`. Establish `hμ : σ₀.comp τ ≠ K.1.val` using `fun h => hτ (AlgHom.ext fun x => σ₀.toRingHom.injective ((h₀ x).trans (DFunLike.congr_fun h x).symm))`.

Take `⟨m1, m2⟩` from `h2 hμ`. Rewrite using `[if_neg hτ]`. Establish `m2' : y ∉ (P.PD K).Fil (0 + 1)`. Rewrite using `[zero_add]`. Conclude with `m2`.

Establish `h3` using `component_line P T ψ τ' σ₀ h₀ y hact 0 m1 m2'`. Rewrite `h3` using `[neg_zero]`. Conclude with `h3`. Use `⟨?_, fun τ' a => ?_⟩` and prove the remaining obligations. Establish `hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1`.

Rewrite using `[← GlobalTheory.DeRhamSplit.card_emb K LL hsplit, Nat.card_eq_fintype_card]`. Use `haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (PositivityTheory.LocInh.tied_field l P AI T).1 (lineRep ψ)).1`. Take `⟨e1, -⟩` from `GlobalTheory.DeRhamSplit.finrank_DdR (P.PD K) (lineRep ψ) hc 0`. Establish `hone : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) (lineRep ψ) τ') = 1`. Introduce `τ'`.

Take `⟨z, hz, hgen, -, h2⟩` from `key τ'`. Establish `hz0 : z ≠ 0` using `fun h => h2 (h ▸ Submodule.zero_mem _)`. Establish `hspan : DdRE (P.PD K) (lineRep ψ) τ' = ↥LL.1 ∙ z`. Use `le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hz)` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hgen w hw`.

Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)`. Rewrite using `[hspan]`. Conclude with `finrank_span_singleton hz0`. Rewrite using `[e1, Finset.sum_congr rfl fun τ' _ => hone τ']`. Simplify using `[hc]`.

Take `⟨z, hz, hgen, h1, h2⟩` from `key τ'`. Conclude with `multV_of_gen (P.PD K) (lineRep ψ) τ' _ z hz hgen h1 h2 a`.
-/
theorem jumps_of_periods : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (K LL : FinExt l), (∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ LL.1) →
    ∀ (χ : ↥(GK K) →* (↥K.1)ˣ), HasPeriods P K χ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      Module.finrank ↥LL.1 ↥(DdR (P.PD K) (lineRep ((Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ))) =
        Module.finrank ℚ_[l] ↥K.1 * 1 ∧
      ∀ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
        multV (P.PD K) (lineRep ((Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ)) τ' a =
          if a = (if τ' = τ then (-1 : ℤ) else 0) then 1 else 0 := by
  rintro l _ P AI ⟨T⟩ K LL hsplit χ hP τ
  haveI := K.2
  haveI := LL.2
  set ψ : ↥(GK K) →* (↥LL.1)ˣ := (Units.map ((τ : ↥K.1 →+* ↥LL.1) : ↥K.1 →* ↥LL.1)).comp χ with hψ
  have key : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ z ∈ DdRE (P.PD K) (lineRep ψ) τ',
      (∀ w ∈ DdRE (P.PD K) (lineRep ψ) τ', ∃ c : ↥LL.1, w = c • z) ∧
      z ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) (if τ' = τ then (-1 : ℤ) else 0) ∧
      z ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) ((if τ' = τ then (-1 : ℤ) else 0) + 1) := by
    intro τ'
    obtain ⟨σ₀, h₀⟩ := exists_lift τ' K.1.val
    obtain ⟨y, hyact, h1, h2⟩ := hP (σ₀.comp τ)
    have hact : ∀ g : ↥(GK K), gc g σ₀ = σ₀ →
        P.actQdR (g : GQ l) y = algebraMap (Om l) P.R.BdR (σ₀ ((ψ g : (↥LL.1)ˣ) : ↥LL.1)) * y :=
      fun g hg => hyact g.1 g.2 fun x => DFunLike.congr_fun hg (τ x)
    by_cases hτ : τ' = τ
    · have hμ : σ₀.comp τ = K.1.val := AlgHom.ext fun x => by
        rw [AlgHom.comp_apply, ← hτ]
        exact h₀ x
      obtain ⟨m1, m2⟩ := h1 hμ
      rw [if_pos hτ]
      have m2' : y ∉ (P.PD K).Fil (1 + 1) := by
        rw [show (1 + 1 : ℤ) = 2 by norm_num]
        exact m2
      exact component_line P T ψ τ' σ₀ h₀ y hact 1 m1 m2'
    · have hμ : σ₀.comp τ ≠ K.1.val := fun h => hτ (AlgHom.ext fun x =>
        σ₀.toRingHom.injective ((h₀ x).trans (DFunLike.congr_fun h x).symm))
      obtain ⟨m1, m2⟩ := h2 hμ
      rw [if_neg hτ]
      have m2' : y ∉ (P.PD K).Fil (0 + 1) := by
        rw [zero_add]
        exact m2
      have h3 := component_line P T ψ τ' σ₀ h₀ y hact 0 m1 m2'
      rw [neg_zero] at h3
      exact h3
  refine ⟨?_, fun τ' a => ?_⟩
  · have hc : Fintype.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
      rw [← GlobalTheory.DeRhamSplit.card_emb K LL hsplit, Nat.card_eq_fintype_card]
    haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (PositivityTheory.LocInh.tied_field l P AI T).1 (lineRep ψ)).1
    obtain ⟨e1, -⟩ := GlobalTheory.DeRhamSplit.finrank_DdR (P.PD K) (lineRep ψ) hc 0
    have hone : ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) (lineRep ψ) τ') = 1 := by
      intro τ'
      obtain ⟨z, hz, hgen, -, h2⟩ := key τ'
      have hz0 : z ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
      have hspan : DdRE (P.PD K) (lineRep ψ) τ' = ↥LL.1 ∙ z := by
        refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hz)
        obtain ⟨c, rfl⟩ := hgen w hw
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
      rw [hspan]
      exact finrank_span_singleton hz0
    rw [e1, Finset.sum_congr rfl fun τ' _ => hone τ']
    simp [hc]
  · obtain ⟨z, hz, hgen, h1, h2⟩ := key τ'
    exact multV_of_gen (P.PD K) (lineRep ψ) τ' _ z hz hgen h1 h2 a

end GlobalTheory.CompanionTheory.LTRead
