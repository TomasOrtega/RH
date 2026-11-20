import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.ConstantCoeffAlgHom

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.GS

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem γA_apply (g : W.Gam) (a : LetA O n) (i : ZMod n) : W.γA g a i = W.γ₀ g (a i) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[γA_apply, γA_apply, γA_apply, map_mul]`. Both sides reduce to the same expression.
-/
theorem γA_mul (g h : W.Gam) (a : LetA O n) : W.γA (g * h) a = W.γA g (W.γA h a) := by
  funext i
  rw [γA_apply, γA_apply, γA_apply, map_mul]
  rfl

/- English proof (translation)
Rewrite using `[← γA_mul, mul_comm, γA_mul]`.
-/
theorem γA_comm (g h : W.Gam) (a : LetA O n) : W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  rw [← γA_mul, mul_comm, γA_mul]

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[γA_comm, ha δ hδ]`.
-/
theorem γA_mem (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA g a ∈ W.AΔ := by
  intro δ hδ
  rw [γA_comm, ha δ hδ]

/- English proof (translation)
Rewrite using `[W.DelF_def, isOfFinOrder_iff_pow_eq_one]`.
-/
theorem delF_iff (g : W.Gam) : g ∈ W.DelF ↔ IsOfFinOrder g := by
  rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]

/- English proof (translation)
Introduce `δ hδ`. Establish `hδ' : IsOfFinOrder δ` using `(delF_iff W δ).1 hδ`. Use function extensionality and compare the values at `i`. Rewrite using `[γA_apply]`. Use `show W.γ₀ δ W.π₀₁ = W.π₀₁`.

Unfold `LocWach.π₀₁`. Rewrite using `[map_add, map_sub, map_one, map_natCast, map_sum]`. Use `congr 1`. Use `Finset.sum_equiv (Equiv.mulLeft δ) (fun g => ?_) (fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[delF_iff, delF_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Conclude with `hδ'.mul hg`. Introduce `hg`. Use `hδ'.inv.mul hg` as an intermediate fact.

Simplify using `using this`. Use `show W.γ₀ δ (W.γ₀ g (1 + X)) = W.γ₀ (δ * g) (1 + X)`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem π₀_mem : W.π₀ ∈ W.AΔ := by
  intro δ hδ
  have hδ' : IsOfFinOrder δ := (delF_iff W δ).1 hδ
  funext i
  rw [γA_apply]
  show W.γ₀ δ W.π₀₁ = W.π₀₁
  unfold LocWach.π₀₁
  rw [map_add, map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_equiv (Equiv.mulLeft δ) (fun g => ?_) (fun g _ => ?_)
  · rw [delF_iff, delF_iff]
    constructor
    · intro hg
      exact hδ'.mul hg
    · intro hg
      have := hδ'.inv.mul hg
      simpa using this
  · show W.γ₀ δ (W.γ₀ g (1 + X)) = W.γ₀ (δ * g) (1 + X)
    rw [map_mul]
    rfl

/- English proof (translation)
The claim follows from `W.AΔ.add_mem (π₀_mem W) (natCast_mem _ _)`.
-/
theorem qA_mem : qA W ∈ W.AΔ :=
  W.AΔ.add_mem (π₀_mem W) (natCast_mem _ _)

/- English proof (translation)
Proceed by induction on `t generalizing a with`. Consider the case `zero => simp`. Consider the case `succ t ih => rw [pow_succ, AlgHom.mul_apply, AlgHom.mul_apply, W.φA_γA, ih]`.
-/
theorem φpow_γA (t : ℕ) (g : W.Gam) (a : LetA O n) :
    (W.φA ^ t) (W.γA g a) = W.γA g ((W.φA ^ t) a) := by
  induction t generalizing a with
  | zero => simp
  | succ t ih => rw [pow_succ, AlgHom.mul_apply, AlgHom.mul_apply, W.φA_γA, ih]

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[← φpow_γA, ha δ hδ]`.
-/
theorem φpow_mem (t : ℕ) {a : LetA O n} (ha : a ∈ W.AΔ) : (W.φA ^ t) a ∈ W.AΔ := by
  intro δ hδ
  rw [← φpow_γA, ha δ hδ]

/- English proof (translation)
The claim follows from `φpow_mem W s (qA_mem W)`.
-/
theorem ps_mem (s : ℕ) : ps W s ∈ W.AΔ := φpow_mem W s (qA_mem W)

/- English proof (translation)
Establish `h : insert W.π₀ (Set.range (ps W)) ⊆ (W.AΔ.toSubmonoid : Set (LetA O n))` using `Set.insert_subset_iff.2 ⟨π₀_mem W, Set.range_subset_iff.2 fun s => ps_mem W s⟩`. Conclude with `(Submonoid.closure_le.2 h) hf`.
-/
theorem piPs_mem {f : LetA O n} (hf : f ∈ PiPs W) : f ∈ W.AΔ := by
  have h : insert W.π₀ (Set.range (ps W)) ⊆ (W.AΔ.toSubmonoid : Set (LetA O n)) :=
    Set.insert_subset_iff.2 ⟨π₀_mem W, Set.range_subset_iff.2 fun s => ps_mem W s⟩
  exact (Submonoid.closure_le.2 h) hf

/- English proof (translation)
Rewrite using `[← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]`. Both sides reduce to the same expression.
-/
theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

/- English proof (translation)
Use `⟨(W.N T).smul_mem a hy.1, fun δ hδ => ?_⟩` and prove the remaining obligations. Rewrite using `[γD_smulA, ha δ hδ, hy.2 δ hδ]`.
-/
theorem smul_mem_NΔ (T : LocLat G Qp LL O) {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T}
    (hy : y ∈ W.NΔ T) : a • y ∈ W.NΔ T := by
  refine ⟨(W.N T).smul_mem a hy.1, fun δ hδ => ?_⟩
  rw [γD_smulA, ha δ hδ, hy.2 δ hδ]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i`. Distinguish the cases in `h : i = c`. Substitute `h` using the available equality. Simplify using `[letE]`.

Simplify using `[letE, Pi.single_eq_of_ne h]`.
-/
theorem γA_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c) = letE c := by
  funext i
  change W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

/- English proof (translation)
The claim follows from `W.γE_ext g a`.
-/
theorem γE_ι (g : W.Gam) (a : LetA O n) :
    W.γE g (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE (W.γA g a) := W.γE_ext g a

/- English proof (translation)
Proceed by induction on `t generalizing a with`. Consider the case `zero => simp`. Consider the case `succ t ih`. Rewrite using `[pow_succ, AlgHom.mul_apply, ih, pow_succ, AlgHom.mul_apply]`. Use `congr 1`.

Conclude with `(W.φE_ext a).symm`.
-/
theorem ι_φpow (t : ℕ) (a : LetA O n) :
    algebraMap (LetA O n) W.EE ((W.φA ^ t) a) = (W.φE ^ t) (algebraMap (LetA O n) W.EE a) := by
  induction t generalizing a with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, AlgHom.mul_apply, ih, pow_succ, AlgHom.mul_apply]
    congr 1
    exact (W.φE_ext a).symm

/- English proof (translation)
Use `W.EE_complete` as an intermediate fact. Establish `h : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson` using `IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) (Ideal.subset_span rfl)`. Conclude with `Ideal.mem_jacobson_bot.1 h x`.
-/
theorem isUnit_p_add (x : W.EE) : IsUnit (((PD.p : ℕ) : W.EE) * x + 1) := by
  have := W.EE_complete
  have h : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) (Ideal.subset_span rfl)
  exact Ideal.mem_jacobson_bot.1 h x

/- English proof (translation)
Apply `W.EE_inj` to reduce the goal to its premises. Use `congrArg (algebraMap (LetA O n) W.EE) h` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Conclude with `hc.mul_left_cancel this`.
-/
theorem cancelE {c a b : LetA O n} (hc : IsUnit (algebraMap (LetA O n) W.EE c)) (h : c * a = c * b) :
    a = b := by
  apply W.EE_inj
  have := congrArg (algebraMap (LetA O n) W.EE) h
  rw [map_mul, map_mul] at this
  exact hc.mul_left_cancel this

/- English proof (translation)
Introduce `δ hδ`. Apply `cancelE W hcu` to reduce the goal to its premises. Establish `h1 : W.γA δ (c * x) = c * x` using `h δ hδ`. Rewrite `h1` using `[map_mul, hc δ hδ]`. Conclude with `h1`.
-/
theorem quot_mem {c x : LetA O n} (hc : c ∈ W.AΔ) (hcu : IsUnit (algebraMap (LetA O n) W.EE c))
    (h : c * x ∈ W.AΔ) : x ∈ W.AΔ := by
  intro δ hδ
  apply cancelE W hcu
  have h1 : W.γA δ (c * x) = c * x := h δ hδ
  rw [map_mul, hc δ hδ] at h1
  exact h1

def RD : Prop :=
  (∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) ∧
  (∃ w : (LetA O n)ˣ, W.φA W.π₀ = (w : LetA O n) * W.π₀ * qA W ^ (PD.p - 1)) ∧
  (∃ w : (LetA O n)ˣ, W.γA W.gam W.π₀ - W.π₀ = (w : LetA O n) * W.π₀ * qA W) ∧
  (∀ a ∈ W.AΔ, ∃ F : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (W.π₀ i) (F i))

/- English proof (translation)
Establish `hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = qA W`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]`. Take `⟨-, hsub, hπ, -, -, hφ, hγ, -⟩` from `h`. Rewrite `hφ`, `hγ` using `[hE]`.

Use `⟨hπ, hφ, hγ, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨F, hF, -⟩` from `hsub a ha`. Conclude with `⟨F, hF⟩`.
-/
theorem rd_of (h : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
    (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) : RD W := by
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      qA W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  obtain ⟨-, hsub, hπ, -, -, hφ, hγ, -⟩ := h
  rw [hE] at hφ hγ
  refine ⟨hπ, hφ, hγ, fun a ha => ?_⟩
  obtain ⟨F, hF, -⟩ := hsub a ha
  exact ⟨F, hF⟩

section RDsec

variable {W}

/- English proof (translation)
Use `PD.hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem p_sub_one_pos : 1 ≤ PD.p - 1 := by
  have := PD.hp.two_le
  omega

/- English proof (translation)
Take `⟨⟨w, hw⟩, -⟩` from `id hR`. Conclude with `⟨(w : LetA O n) 0, congrFun hw 0⟩`.
-/
theorem π₀₁_eq (hR : RD W) : ∃ c : PowerSeries O, W.π₀₁ = c * X ^ (PD.p - 1) := by
  obtain ⟨⟨w, hw⟩, -⟩ := id hR
  exact ⟨(w : LetA O n) 0, congrFun hw 0⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `π₀₁_eq hR`. Establish `h1 : PD.p - 1 ≠ 0` using `by have := p_sub_one_pos (PD := PD); omega`. Rewrite using `[hc, map_mul, map_pow, constantCoeff_X, zero_pow h1, mul_zero]`.
-/
theorem π₀₁_cc (hR : RD W) : constantCoeff W.π₀₁ = 0 := by
  obtain ⟨c, hc⟩ := π₀₁_eq hR
  have h1 : PD.p - 1 ≠ 0 := by have := p_sub_one_pos (PD := PD); omega
  rw [hc, map_mul, map_pow, constantCoeff_X, zero_pow h1, mul_zero]

/- English proof (translation)
Take `⟨⟨w, hw⟩, -⟩` from `id hR`. Rewrite using `[hw, map_mul, map_pow]`. Conclude with `(w.isUnit.map _).mul (W.EE_π.pow _)`.
-/
theorem isUnit_π₀ (hR : RD W) : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
  obtain ⟨⟨w, hw⟩, -⟩ := id hR
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

/- English proof (translation)
Take `⟨u, hu⟩` from `isUnit_π₀ hR`. Establish `e : algebraMap (LetA O n) W.EE (qA W) = (u : W.EE) * (((PD.p : ℕ) : W.EE) * ((u⁻¹ : W.EEˣ) : W.EE) + 1)`. Rewrite using `[mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one, hu, qA, lA, map_add, map_natCast, add_comm]`. Rewrite using `[e]`. Conclude with `u.isUnit.mul (isUnit_p_add W _)`.
-/
theorem isUnit_qA (hR : RD W) : IsUnit (algebraMap (LetA O n) W.EE (qA W)) := by
  obtain ⟨u, hu⟩ := isUnit_π₀ hR
  have e : algebraMap (LetA O n) W.EE (qA W) =
      (u : W.EE) * (((PD.p : ℕ) : W.EE) * ((u⁻¹ : W.EEˣ) : W.EE) + 1) := by
    rw [mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one, hu, qA, lA, map_add, map_natCast,
      add_comm]
  rw [e]
  exact u.isUnit.mul (isUnit_p_add W _)

/- English proof (translation)
Rewrite using `[map_mul]`. Conclude with `(isUnit_π₀ hR).mul (isUnit_qA hR)`.
-/
theorem isUnit_π₀qA (hR : RD W) : IsUnit (algebraMap (LetA O n) W.EE (W.π₀ * qA W)) := by
  rw [map_mul]
  exact (isUnit_π₀ hR).mul (isUnit_qA hR)

/- English proof (translation)
The claim follows from `W.AΔ.mul_mem (π₀_mem W) (qA_mem W)`.
-/
theorem π₀qA_mem : W.π₀ * qA W ∈ W.AΔ := W.AΔ.mul_mem (π₀_mem W) (qA_mem W)

/- English proof (translation)
Take `⟨-, -, ⟨w, hw⟩, -⟩` from `id hR`. Use `⟨w, quot_mem W π₀qA_mem (isUnit_π₀qA hR) ?_, by linear_combination hw⟩` and prove the remaining obligations. Establish `: W.π₀ * qA W * (w : LetA O n) = W.γA W.gam W.π₀ - W.π₀` using `by rw [hw]; ring`. Rewrite using `[this]`. Conclude with `W.AΔ.sub_mem (γA_mem W _ (π₀_mem W)) (π₀_mem W)`.
-/
theorem gamma_pi0_eq_pi0_mul_unit (hR : RD W) :
    ∃ w : (LetA O n)ˣ, (w : LetA O n) ∈ W.AΔ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + w * qA W) := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := id hR
  refine ⟨w, quot_mem W π₀qA_mem (isUnit_π₀qA hR) ?_, by linear_combination hw⟩
  have : W.π₀ * qA W * (w : LetA O n) = W.γA W.gam W.π₀ - W.π₀ := by rw [hw]; ring
  rw [this]
  exact W.AΔ.sub_mem (γA_mem W _ (π₀_mem W)) (π₀_mem W)

/- English proof (translation)
Take `⟨c, hc⟩` from `π₀₁_eq hR`. Establish `h1 : PD.p - 1 ≠ 0` using `by have := p_sub_one_pos (PD := PD); omega`. Rewrite using `[hc, map_mul, map_pow, map_mul, map_pow, (W.γ₀_X W.gam).1, zero_pow h1, mul_zero]`.
-/
theorem γ₀π₀₁_cc (hR : RD W) : constantCoeff (W.γ₀ W.gam W.π₀₁) = 0 := by
  obtain ⟨c, hc⟩ := π₀₁_eq hR
  have h1 : PD.p - 1 ≠ 0 := by have := p_sub_one_pos (PD := PD); omega
  rw [hc, map_mul, map_pow, map_mul, map_pow, (W.γ₀_X W.gam).1, zero_pow h1, mul_zero]

/- English proof (translation)
Establish `hR'` using `id hR`. Take `⟨-, -, ⟨w, hw⟩, hsub⟩` from `hR'`. Take `⟨F, hF⟩` from `hsub f hf`. Establish `hcc` using `π₀₁_cc hR`. Establish `hγcc` using `γ₀π₀₁_cc hR`.

Establish `hs : HasSubst W.π₀₁` using `HasSubst.of_constantCoeff_zero' hcc`. Establish `hdiv : ∀ i, ∃ c : PowerSeries O, (W.γA W.gam f - f) i = (W.γA W.gam W.π₀ - W.π₀) i * c`. Introduce `i`. Set `ψ : PowerSeries O →ₐ[O] PowerSeries O` to `(W.γ₀ W.gam).comp (substAlgHom hs)`. Establish `hψX : ψ X = W.γ₀ W.gam W.π₀₁` using `by show W.γ₀ W.gam (substAlgHom hs X) = _`.

Rewrite using `[coe_substAlgHom, subst_X hs]`. Establish `hψ : ψ (F i) = (F i).subst (W.γ₀ W.gam W.π₀₁)`. Rewrite using `[Formalism.MainNotions.N.WachTwistedLattices.PowerSeriesTruncation.algHom_eq_subst ψ (by rw [hψX]; exact hγcc), hψX]`. Establish `e1 : (W.γA W.gam f - f) i = (F i).subst (W.γ₀ W.gam W.π₀₁) - (F i).subst W.π₀₁`. Rewrite using `[Pi.sub_apply, γA_apply, hF i, ← hψ]`.

Use `show _ = (W.γ₀ W.gam) (substAlgHom hs (F i)) - _`. Rewrite using `[coe_substAlgHom]`. Both sides reduce to the same expression. Take `⟨c, hc⟩` from `Formalism.MainNotions.N.WachTwistedLattices.PowerSeriesTruncation.subst_sub_subst_dvd hγcc hcc (F i)`. Conclude with `⟨c, by rw [e1, hc]; rfl⟩`.

Use `choose c hc using hdiv`. Establish `hfc : W.γA W.gam f - f = (W.γA W.gam W.π₀ - W.π₀) * c` using `funext hc`. Use `⟨(w : LetA O n) * c, quot_mem W π₀qA_mem (isUnit_π₀qA hR) ?_, ?_⟩` and prove the remaining obligations. Establish `: W.π₀ * qA W * ((w : LetA O n) * c) = W.γA W.gam f - f` using `by rw [hfc, hw]; ring`. Rewrite using `[this]`.

Conclude with `W.AΔ.sub_mem (γA_mem W _ hf) hf`. Rewrite using `[hfc, hw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gam_A_core (hR : RD W) {f : LetA O n} (hf : f ∈ W.AΔ) :
    ∃ g ∈ W.AΔ, W.γA W.gam f - f = W.π₀ * qA W * g := by
  have hR' := id hR
  obtain ⟨-, -, ⟨w, hw⟩, hsub⟩ := hR'
  obtain ⟨F, hF⟩ := hsub f hf
  have hcc := π₀₁_cc hR
  have hγcc := γ₀π₀₁_cc hR
  have hs : HasSubst W.π₀₁ := HasSubst.of_constantCoeff_zero' hcc
  have hdiv : ∀ i, ∃ c : PowerSeries O,
      (W.γA W.gam f - f) i = (W.γA W.gam W.π₀ - W.π₀) i * c := by
    intro i
    let ψ : PowerSeries O →ₐ[O] PowerSeries O := (W.γ₀ W.gam).comp (substAlgHom hs)
    have hψX : ψ X = W.γ₀ W.gam W.π₀₁ := by
      show W.γ₀ W.gam (substAlgHom hs X) = _
      rw [coe_substAlgHom, subst_X hs]
    have hψ : ψ (F i) = (F i).subst (W.γ₀ W.gam W.π₀₁) := by
      rw [Formalism.MainNotions.N.WachTwistedLattices.PowerSeriesTruncation.algHom_eq_subst ψ (by rw [hψX]; exact hγcc), hψX]
    have e1 : (W.γA W.gam f - f) i = (F i).subst (W.γ₀ W.gam W.π₀₁) - (F i).subst W.π₀₁ := by
      rw [Pi.sub_apply, γA_apply, hF i, ← hψ]
      show _ = (W.γ₀ W.gam) (substAlgHom hs (F i)) - _
      rw [coe_substAlgHom]
      rfl
    obtain ⟨c, hc⟩ := Formalism.MainNotions.N.WachTwistedLattices.PowerSeriesTruncation.subst_sub_subst_dvd hγcc hcc (F i)
    exact ⟨c, by rw [e1, hc]; rfl⟩
  choose c hc using hdiv
  have hfc : W.γA W.gam f - f = (W.γA W.gam W.π₀ - W.π₀) * c := funext hc
  refine ⟨(w : LetA O n) * c, quot_mem W π₀qA_mem (isUnit_π₀qA hR) ?_, ?_⟩
  · have : W.π₀ * qA W * ((w : LetA O n) * c) = W.γA W.gam f - f := by rw [hfc, hw]; ring
    rw [this]
    exact W.AΔ.sub_mem (γA_mem W _ hf) hf
  · rw [hfc, hw]; ring

/- English proof (translation)
Take `⟨-, ⟨w, hw⟩, -⟩` from `id hR`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ, AlgHom.mul_apply, hw, map_mul, map_mul]`.

Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_left ih _) _`.
-/
theorem π₀_dvd_φpow (hR : RD W) (m : ℕ) : W.π₀ ∣ (W.φA ^ m) W.π₀ := by
  obtain ⟨-, ⟨w, hw⟩, -⟩ := id hR
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, AlgHom.mul_apply, hw, map_mul, map_mul]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ih _) _

/- English proof (translation)
Take `⟨a, ha⟩` from `π₀_dvd_φpow hR t`. Take `⟨-, ⟨w, hw⟩, -⟩` from `id hR`. Take `⟨k, hk⟩ : ∃ k, PD.p - 1 = k + 1` from `⟨PD.p - 1 - 1, by have := p_sub_one_pos (PD := PD); omega⟩`. Use `⟨w * qA W ^ k * W.φA a, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', AlgHom.mul_apply, ha, map_mul, hw, hk, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem φpow_π₀ (hR : RD W) (t : ℕ) :
    ∃ h : LetA O n, (W.φA ^ (t + 1)) W.π₀ = W.π₀ * qA W * h := by
  obtain ⟨a, ha⟩ := π₀_dvd_φpow hR t
  obtain ⟨-, ⟨w, hw⟩, -⟩ := id hR
  obtain ⟨k, hk⟩ : ∃ k, PD.p - 1 = k + 1 := ⟨PD.p - 1 - 1, by have := p_sub_one_pos (PD := PD); omega⟩
  refine ⟨w * qA W ^ k * W.φA a, ?_⟩
  rw [pow_succ', AlgHom.mul_apply, ha, map_mul, hw, hk, pow_succ]
  ring

/- English proof (translation)
Establish `: W.γA W.gam (qA W) = W.γA W.gam W.π₀ + lA W`. Simplify using `only [qA, lA, map_add, map_natCast]`. Rewrite using `[this, hw]`. Simplify using `only [qA]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem γqA {w : LetA O n} (hw : W.γA W.gam W.π₀ = W.π₀ * (1 + w * qA W)) :
    W.γA W.gam (qA W) = qA W * (1 + w * W.π₀) := by
  have : W.γA W.gam (qA W) = W.γA W.gam W.π₀ + lA W := by
    simp only [qA, lA, map_add, map_natCast]
  rw [this, hw]
  simp only [qA]
  ring

/- English proof (translation)
Take `⟨t, rfl⟩ : ∃ t, s = t + 1` from `⟨s - 1, by omega⟩`. Take `⟨w, hwΔ, hw⟩` from `gamma_pi0_eq_pi0_mul_unit hR`. Take `⟨h, hh⟩` from `φpow_π₀ hR t`. Establish `hγ : W.γA W.gam (ps W (t + 1)) = ps W (t + 1) * (1 + (W.φA ^ (t + 1)) (w : LetA O n) * (W.φA ^ (t + 1)) W.π₀)` using `by show W.γA W.gam ((W.φA ^ (t + 1)) (qA W)) = (W.φA ^ (t + 1)) (qA W) * _`. Rewrite using `[← φpow_γA, γqA hw, map_mul, map_add, map_one, map_mul]`.

Use `⟨(W.φA ^ (t + 1)) (w : LetA O n) * h, quot_mem W π₀qA_mem (isUnit_π₀qA hR) ?_, ?_⟩` and prove the remaining obligations. Establish `: W.π₀ * qA W * ((W.φA ^ (t + 1)) (w : LetA O n) * h) = (W.φA ^ (t + 1)) (w : LetA O n) * (W.φA ^ (t + 1)) W.π₀` using `by rw [hh]; ring`. Rewrite using `[this]`. Conclude with `W.AΔ.mul_mem (φpow_mem W _ hwΔ) (φpow_mem W _ (π₀_mem W))`. Rewrite using `[hγ, hh]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gam_ps_core (hR : RD W) (s : ℕ) (hs : 1 ≤ s) :
    ∃ g ∈ W.AΔ, W.γA W.gam (ps W s) = ps W s * (1 + W.π₀ * qA W * g) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  obtain ⟨w, hwΔ, hw⟩ := gamma_pi0_eq_pi0_mul_unit hR
  obtain ⟨h, hh⟩ := φpow_π₀ hR t
  have hγ : W.γA W.gam (ps W (t + 1)) =
      ps W (t + 1) * (1 + (W.φA ^ (t + 1)) (w : LetA O n) * (W.φA ^ (t + 1)) W.π₀) := by
    show W.γA W.gam ((W.φA ^ (t + 1)) (qA W)) = (W.φA ^ (t + 1)) (qA W) * _
    rw [← φpow_γA, γqA hw, map_mul, map_add, map_one, map_mul]
  refine ⟨(W.φA ^ (t + 1)) (w : LetA O n) * h, quot_mem W π₀qA_mem (isUnit_π₀qA hR) ?_, ?_⟩
  · have : W.π₀ * qA W * ((W.φA ^ (t + 1)) (w : LetA O n) * h) =
        (W.φA ^ (t + 1)) (w : LetA O n) * (W.φA ^ (t + 1)) W.π₀ := by rw [hh]; ring
    rw [this]
    exact W.AΔ.mul_mem (φpow_mem W _ hwΔ) (φpow_mem W _ (π₀_mem W))
  · rw [hγ, hh]; ring

end RDsec

def S1 : Submonoid (LetA O n) where
  carrier := {r | ∃ y ∈ W.AΔ, r = 1 + W.π₀ * y}
  one_mem' := ⟨0, W.AΔ.zero_mem, by ring⟩
  mul_mem' := by
    rintro a b ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y + z + W.π₀ * y * z, W.AΔ.add_mem (W.AΔ.add_mem hy hz)
      (W.AΔ.mul_mem (W.AΔ.mul_mem (π₀_mem W) hy) hz), by ring⟩

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hr`. Conclude with `W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem (π₀_mem W) hy)`.
-/
theorem mem_invariants_of_mem_S1 {r : LetA O n} (hr : r ∈ S1 W) : r ∈ W.AΔ := by
  obtain ⟨y, hy, rfl⟩ := hr
  exact W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem (π₀_mem W) hy)

section RDsec2

variable {W}

/- English proof (translation)
Establish `hrΔ` using `mem_invariants_of_mem_S1 W hr`. Take `⟨y, hy, rfl⟩` from `hr`. Establish `hcc` using `π₀₁_cc hR`. Establish `hu : IsUnit (1 + W.π₀ * y)`. Rewrite using `[Pi.isUnit_iff]`.

Introduce `i`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Use `show IsUnit (constantCoeff (1 + W.π₀₁ * y i))`. Rewrite using `[map_add, map_mul, hcc, zero_mul, add_zero, map_one]`. Conclude with `isUnit_one`.

Use `set z : LetA O n := ((hu.unit⁻¹ : (LetA O n)ˣ) : LetA O n) with hzdef`. Establish `hz : (1 + W.π₀ * y) * z = 1` using `hu.mul_val_inv`. Establish `hzΔ : z ∈ W.AΔ`. Introduce `δ hδ`. Establish `h1 : (1 + W.π₀ * y) * W.γA δ z = 1`.

Use `congrArg (W.γA δ) hz` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, hrΔ δ hδ]`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Use `⟨z, ⟨-(y * z), W.AΔ.neg_mem (W.AΔ.mul_mem hy hzΔ), ?_⟩, hz⟩` and prove the remaining obligations.

Take the linear combination `hz`.
-/
theorem exists_inverse_in_S1 (hR : RD W) {r : LetA O n} (hr : r ∈ S1 W) : ∃ r' ∈ S1 W, r * r' = 1 := by
  have hrΔ := mem_invariants_of_mem_S1 W hr
  obtain ⟨y, hy, rfl⟩ := hr
  have hcc := π₀₁_cc hR
  have hu : IsUnit (1 + W.π₀ * y) := by
    rw [Pi.isUnit_iff]
    intro i
    rw [PowerSeries.isUnit_iff_constantCoeff]
    show IsUnit (constantCoeff (1 + W.π₀₁ * y i))
    rw [map_add, map_mul, hcc, zero_mul, add_zero, map_one]
    exact isUnit_one
  set z : LetA O n := ((hu.unit⁻¹ : (LetA O n)ˣ) : LetA O n) with hzdef
  have hz : (1 + W.π₀ * y) * z = 1 := hu.mul_val_inv
  have hzΔ : z ∈ W.AΔ := by
    intro δ hδ
    have h1 : (1 + W.π₀ * y) * W.γA δ z = 1 := by
      have := congrArg (W.γA δ) hz
      rw [map_mul, map_one, hrΔ δ hδ] at this
      exact this
    calc W.γA δ z = (1 + W.π₀ * y) * z * W.γA δ z := by rw [hz, one_mul]
      _ = z * ((1 + W.π₀ * y) * W.γA δ z) := by ring
      _ = z := by rw [h1, mul_one]
  refine ⟨z, ⟨-(y * z), W.AΔ.neg_mem (W.AΔ.mul_mem hy hzΔ), ?_⟩, hz⟩
  linear_combination hz

/- English proof (translation)
Take `⟨w, hwΔ, hw⟩` from `gamma_pi0_eq_pi0_mul_unit hR`. Take `⟨a, ha⟩` from `π₀_dvd_φpow hR t`. Establish `hyΔ : (W.φA ^ t) (w : LetA O n) * a ∈ W.AΔ`. Use `quot_mem W (π₀_mem W) (isUnit_π₀ hR) ?_` and prove the remaining obligations. Establish `: W.π₀ * ((W.φA ^ t) (w : LetA O n) * a) = (W.φA ^ t) (w : LetA O n) * (W.φA ^ t) W.π₀` using `by rw [ha]; ring`.

Rewrite using `[this]`. Conclude with `W.AΔ.mul_mem (φpow_mem W _ hwΔ) (φpow_mem W _ (π₀_mem W))`. Establish `hS : 1 + W.π₀ * ((W.φA ^ t) (w : LetA O n) * a) ∈ S1 W` using `⟨_, hyΔ, rfl⟩`. Take `⟨r', hr', hrr⟩` from `exists_inverse_in_S1 hR hS`. Use `⟨_, hS, r', hr', hrr, ?_⟩` and prove the remaining obligations.

Use `show W.γA W.gam ((W.φA ^ t) (qA W)) = _ * (W.φA ^ t) (qA W)`. Rewrite using `[← φpow_γA, γqA hw, map_mul, map_add, map_one, map_mul, ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psγ (hR : RD W) (t : ℕ) :
    ∃ r ∈ S1 W, ∃ r' ∈ S1 W, r * r' = 1 ∧ W.γA W.gam (ps W t) = r * ps W t := by
  obtain ⟨w, hwΔ, hw⟩ := gamma_pi0_eq_pi0_mul_unit hR
  obtain ⟨a, ha⟩ := π₀_dvd_φpow hR t
  have hyΔ : (W.φA ^ t) (w : LetA O n) * a ∈ W.AΔ := by
    refine quot_mem W (π₀_mem W) (isUnit_π₀ hR) ?_
    have : W.π₀ * ((W.φA ^ t) (w : LetA O n) * a) =
        (W.φA ^ t) (w : LetA O n) * (W.φA ^ t) W.π₀ := by rw [ha]; ring
    rw [this]
    exact W.AΔ.mul_mem (φpow_mem W _ hwΔ) (φpow_mem W _ (π₀_mem W))
  have hS : 1 + W.π₀ * ((W.φA ^ t) (w : LetA O n) * a) ∈ S1 W := ⟨_, hyΔ, rfl⟩
  obtain ⟨r', hr', hrr⟩ := exists_inverse_in_S1 hR hS
  refine ⟨_, hS, r', hr', hrr, ?_⟩
  show W.γA W.gam ((W.φA ^ t) (qA W)) = _ * (W.φA ^ t) (qA W)
  rw [← φpow_γA, γqA hw, map_mul, map_add, map_one, map_mul, ha]
  ring

/- English proof (translation)
Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, hγ, mul_pow]`.
-/
theorem γ_prod (r : ℕ → LetA O n) (hγ : ∀ t, W.γA W.gam (ps W t) = r t * ps W t) (e : ℕ)
    (k : ℕ → ℕ) :
    W.γA W.gam (∏ s ∈ Finset.range e, ps W s ^ k s) =
      (∏ s ∈ Finset.range e, r s ^ k s) * ∏ s ∈ Finset.range e, ps W s ^ k s := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, hγ, mul_pow]

/- English proof (translation)
Take `⟨u, hu, hfu⟩` from `hf`. Use `choose r hr r' hr' hrr hγ using psγ hR`. Use `set num := ∏ s ∈ Finset.range e, ps W s ^ (α s).toNat with hnum`. Use `set den := ∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat with hden`. Use `set R := ∏ s ∈ Finset.range e, r s ^ (α s).toNat with hRdef`.

Use `set Rd := ∏ s ∈ Finset.range e, r s ^ (-(α s)).toNat with hRddef`. Use `set Rd' := ∏ s ∈ Finset.range e, r' s ^ (-(α s)).toNat with hRd'def`. Establish `hRS : R ∈ S1 W` using `Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _ (hr s) _`. Establish `hRd'S : Rd' ∈ S1 W` using `Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _ (hr' s) _`. Establish `hRdd : Rd * Rd' = 1`.

Rewrite using `[hRddef, hRd'def, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun s _ => by rw [← mul_pow, hrr, one_pow]`. Establish `hγn : W.γA W.gam num = R * num` using `γ_prod r hγ e _`. Establish `hγd : W.γA W.gam den = Rd * den` using `γ_prod r hγ e _`. Establish `h1 : algebraMap (LetA O n) W.EE (W.γA W.gam den) * W.γE W.gam f = algebraMap (LetA O n) W.EE (W.γA W.gam (letE a * num * u))`.

Rewrite using `[← γE_ι, ← γE_ι, ← map_mul, hfu]`. Establish `e1 : W.γA W.gam (letE a * num * u) = letE a * (R * num) * W.γA W.gam u`. Rewrite using `[map_mul, map_mul, γA_letE, hγn]`. Rewrite `h1` using `[e1, hγd]`. Establish `key : algebraMap (LetA O n) W.EE den * W.γE W.gam f = algebraMap (LetA O n) W.EE (letE a * num * (Rd' * R * W.γA W.gam u))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm Rd' Rd, hRdd, map_one, one_mul]`. Use `_ = algebraMap (LetA O n) W.EE Rd' * (algebraMap (LetA O n) W.EE (Rd * den) * W.γE W.gam f) := by`. Rewrite using `[map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = algebraMap (LetA O n) W.EE Rd' * algebraMap (LetA O n) W.EE (letE a * (R * num) * W.γA W.gam u) := by`. Rewrite using `[h1]`. Use `_ = _ := by rw [← map_mul]; congr 1; ring`. Take `⟨y, hy, hyR⟩ : Rd' * R ∈ S1 W` from `(S1 W).mul_mem hRd'S hRS`. Take `⟨g, hg, hgu⟩` from `gam_A_core hR hu`.

Establish `hγu` using `γA_mem W W.gam hu`. Use `⟨⟨Rd' * R * W.γA W.gam u, W.AΔ.mul_mem (mem_invariants_of_mem_S1 W ((S1 W).mul_mem hRd'S hRS)) hγu, key⟩, ⟨qA W * g + y * W.γA W.gam u, W.AΔ.add_mem (W.AΔ.mul_mem (qA_mem W) hg) (W.AΔ.mul_mem hy hγu), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mul_sub, key, hfu, ← map_sub]`. Use `congr 1`. Rewrite using `[hyR]`.

Take the linear combination `(letE a * num) * hgu`.
-/
theorem gam_frac_core (hR : RD W) (a : ZMod n) (e : ℕ) (α : ℕ → ℤ) (f : W.EE)
    (hf : InId W a e α f) :
    InId W a e α (W.γE W.gam f) ∧
      InFr W a (W.π₀ * ∏ s ∈ Finset.range e, ps W s ^ (α s).toNat)
        (∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat) (W.γE W.gam f - f) := by
  obtain ⟨u, hu, hfu⟩ := hf
  choose r hr r' hr' hrr hγ using psγ hR
  set num := ∏ s ∈ Finset.range e, ps W s ^ (α s).toNat with hnum
  set den := ∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat with hden
  set R := ∏ s ∈ Finset.range e, r s ^ (α s).toNat with hRdef
  set Rd := ∏ s ∈ Finset.range e, r s ^ (-(α s)).toNat with hRddef
  set Rd' := ∏ s ∈ Finset.range e, r' s ^ (-(α s)).toNat with hRd'def
  have hRS : R ∈ S1 W := Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _ (hr s) _
  have hRd'S : Rd' ∈ S1 W := Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _ (hr' s) _
  have hRdd : Rd * Rd' = 1 := by
    rw [hRddef, hRd'def, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun s _ => by rw [← mul_pow, hrr, one_pow]
  have hγn : W.γA W.gam num = R * num := γ_prod r hγ e _
  have hγd : W.γA W.gam den = Rd * den := γ_prod r hγ e _
  have h1 : algebraMap (LetA O n) W.EE (W.γA W.gam den) * W.γE W.gam f =
      algebraMap (LetA O n) W.EE (W.γA W.gam (letE a * num * u)) := by
    rw [← γE_ι, ← γE_ι, ← map_mul, hfu]
  have e1 : W.γA W.gam (letE a * num * u) = letE a * (R * num) * W.γA W.gam u := by
    rw [map_mul, map_mul, γA_letE, hγn]
  rw [e1, hγd] at h1
  have key : algebraMap (LetA O n) W.EE den * W.γE W.gam f =
      algebraMap (LetA O n) W.EE (letE a * num * (Rd' * R * W.γA W.gam u)) := by
    calc algebraMap (LetA O n) W.EE den * W.γE W.gam f
        = algebraMap (LetA O n) W.EE (Rd' * Rd) * (algebraMap (LetA O n) W.EE den * W.γE W.gam f) := by
          rw [mul_comm Rd' Rd, hRdd, map_one, one_mul]
      _ = algebraMap (LetA O n) W.EE Rd' *
            (algebraMap (LetA O n) W.EE (Rd * den) * W.γE W.gam f) := by
          rw [map_mul, map_mul]; ring
      _ = algebraMap (LetA O n) W.EE Rd' * algebraMap (LetA O n) W.EE (letE a * (R * num) * W.γA W.gam u) := by
          rw [h1]
      _ = _ := by rw [← map_mul]; congr 1; ring
  obtain ⟨y, hy, hyR⟩ : Rd' * R ∈ S1 W := (S1 W).mul_mem hRd'S hRS
  obtain ⟨g, hg, hgu⟩ := gam_A_core hR hu
  have hγu := γA_mem W W.gam hu
  refine ⟨⟨Rd' * R * W.γA W.gam u, W.AΔ.mul_mem (mem_invariants_of_mem_S1 W ((S1 W).mul_mem hRd'S hRS)) hγu, key⟩,
    ⟨qA W * g + y * W.γA W.gam u, W.AΔ.add_mem (W.AΔ.mul_mem (qA_mem W) hg) (W.AΔ.mul_mem hy hγu), ?_⟩⟩
  rw [mul_sub, key, hfu, ← map_sub]
  congr 1
  rw [hyR]
  linear_combination (letE a * num) * hgu

end RDsec2

end Formalism.MainNotions.N.FrobeniusPowerSeries.GS
