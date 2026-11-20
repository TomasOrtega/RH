import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section PS

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `hpoly : ∀ p : Polynomial R, f (p : PowerSeries R) = g (p : PowerSeries R)`. Establish `hc : f.comp (Polynomial.coeToPowerSeries.algHom R) = g.comp (Polynomial.coeToPowerSeries.algHom R)`. Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using `using h`. Introduce `p`.

Simplify using `using AlgHom.congr_fun hc p`. Use `AlgHom.ext fun a => PowerSeries.ext fun k => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨t, b, ha⟩ : ∃ (t : Polynomial R) (b : PowerSeries R), a = (t : PowerSeries R) + PowerSeries.X ^ (k + 1) * b := by`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : PowerSeries.X ^ (k + 1) ∣ a - (PowerSeries.trunc (k + 1) a : PowerSeries R) := by`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`.

Introduce `m hm`. Rewrite using `[map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]`. Conclude with `⟨_, b, by rw [← hb]; ring⟩`. Take `⟨c, hcX⟩` from `PowerSeries.X_dvd_iff.mpr h0`. Establish `hcX' : g PowerSeries.X = PowerSeries.X * c` using `by rw [← h]; exact hcX`.

Substitute `ha` using the available equality. Simplify using `[hcX, hcX', hpoly t, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul']`.
-/
theorem algHom_ext_X (f g : PowerSeries R →ₐ[R] PowerSeries R)
    (h : f PowerSeries.X = g PowerSeries.X)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) : f = g := by
  have hpoly : ∀ p : Polynomial R, f (p : PowerSeries R) = g (p : PowerSeries R) := by
    have hc : f.comp (Polynomial.coeToPowerSeries.algHom R) =
        g.comp (Polynomial.coeToPowerSeries.algHom R) := by
      apply Polynomial.algHom_ext
      simpa using h
    intro p
    simpa using AlgHom.congr_fun hc p
  refine AlgHom.ext fun a => PowerSeries.ext fun k => ?_
  obtain ⟨t, b, ha⟩ : ∃ (t : Polynomial R) (b : PowerSeries R),
      a = (t : PowerSeries R) + PowerSeries.X ^ (k + 1) * b := by
    obtain ⟨b, hb⟩ : PowerSeries.X ^ (k + 1) ∣ a - (PowerSeries.trunc (k + 1) a : PowerSeries R) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
    exact ⟨_, b, by rw [← hb]; ring⟩
  obtain ⟨c, hcX⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hcX' : g PowerSeries.X = PowerSeries.X * c := by rw [← h]; exact hcX
  subst ha
  simp [hcX, hcX', hpoly t, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul']

/- English proof (translation)
Take `⟨c, hcX⟩` from `PowerSeries.X_dvd_iff.mpr h0`. Establish `hC : ∀ r : R, f (PowerSeries.C r) = PowerSeries.C r`. Introduce `r`. Rewrite using `[← mul_one (PowerSeries.C r), ← PowerSeries.smul_eq_C_mul, map_smul, map_one]`. Use `conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a]`.

Simplify using `[hC, hcX]`.
-/
theorem constCoeff_algHom (f : PowerSeries R →ₐ[R] PowerSeries R)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) (a : PowerSeries R) :
    PowerSeries.constantCoeff (f a) = PowerSeries.constantCoeff a := by
  obtain ⟨c, hcX⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hC : ∀ r : R, f (PowerSeries.C r) = PowerSeries.C r := by
    intro r
    rw [← mul_one (PowerSeries.C r), ← PowerSeries.smul_eq_C_mul, map_smul, map_one]
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a]
  simp [hC, hcX]

end PS

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

variable (W) in

abbrev Ring9 : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))

variable (W) in

def Inv1 (a : PowerSeries O) : Prop := ∀ δ ∈ W.DelF, W.γ₀ δ a = a

/- English proof (translation)
Use `show ∀ δ ∈ W.DelF, W.γA δ (fun _ => a) = fun _ => a`. Introduce `δ hδ`. Use function extensionality and compare the values at `i`. Use `first`. Consider the case `exact h δ hδ`.

Consider the case `simp [Formalism.BasicNotions.LocWach.γA, Formalism.BasicNotions.letγ, h δ hδ]`.
-/
theorem diag_mem_AΔ {a : PowerSeries O} (h : Inv1 W a) : (fun _ => a : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (fun _ => a) = fun _ => a
  intro δ hδ
  funext i
  first
    | exact h δ hδ
    | simp [Formalism.BasicNotions.LocWach.γA, Formalism.BasicNotions.letγ, h δ hδ]

/- English proof (translation)
Use `PD.hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem p_sub_one_ne (PD : PeriodData G Qp K₀ K B BdR) : PD.p - 1 ≠ 0 := by
  have := PD.hp.two_le
  omega

/- English proof (translation)
Take `⟨-, -, ⟨w, hw⟩, -⟩` from `hR`. Use `⟨(w : LetA O n) 0, w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) 0), ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `exact congrFun hw 0`. Consider the case `simpa [Formalism.BasicNotions.LocWach.π₀, Formalism.BasicNotions.letπ] using congrFun hw 0`.
-/
theorem π₀₁_eq (hR : Ring9 W) : ∃ w : PowerSeries O, IsUnit w ∧
    W.π₀₁ = w * PowerSeries.X ^ (PD.p - 1) := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hR
  refine ⟨(w : LetA O n) 0, w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) 0), ?_⟩
  first
    | exact congrFun hw 0
    | simpa [Formalism.BasicNotions.LocWach.π₀, Formalism.BasicNotions.letπ] using congrFun hw 0

/- English proof (translation)
Take `⟨w, -, hw⟩` from `π₀₁_eq hR`. Rewrite using `[hw, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (p_sub_one_ne PD), mul_zero]`.
-/
theorem π₀₁_const (hR : Ring9 W) : PowerSeries.constantCoeff W.π₀₁ = 0 := by
  obtain ⟨w, -, hw⟩ := π₀₁_eq hR
  rw [hw, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (p_sub_one_ne PD), mul_zero]

/- English proof (translation)
Take `⟨h1, -⟩` from `hR`. Establish `h1' : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀` using `h1`. Introduce `δ hδ`. Conclude with `congrFun (h1' δ hδ) 0`.
-/
theorem π₀₁_inv (hR : Ring9 W) : Inv1 W W.π₀₁ := by
  obtain ⟨h1, -⟩ := hR
  have h1' : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := h1
  intro δ hδ
  exact congrFun (h1' δ hδ) 0

def ιOf (hR : Ring9 W) : PowerSeries O →ₐ[O] PowerSeries O :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (π₀₁_const hR))

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [ιOf, PowerSeries.coe_substAlgHom]`.
-/
theorem ιOf_apply (hR : Ring9 W) (a : PowerSeries O) : ιOf hR a = PowerSeries.subst W.π₀₁ a := by
  first
    | rfl
    | simp [ιOf, PowerSeries.coe_substAlgHom]

/- English proof (translation)
Rewrite using `[ιOf_apply]`. Conclude with `PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (π₀₁_const hR))`.
-/
theorem ιOf_X (hR : Ring9 W) : ιOf hR PowerSeries.X = W.π₀₁ := by
  rw [ιOf_apply]
  exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (π₀₁_const hR))

/- English proof (translation)
Conclude with `constCoeff_algHom (ιOf hR) (by rw [ιOf_X]; exact π₀₁_const hR) a`.
-/
theorem ιOf_const (hR : Ring9 W) (a : PowerSeries O) :
    PowerSeries.constantCoeff (ιOf hR a) = PowerSeries.constantCoeff a := by
  exact constCoeff_algHom (ιOf hR) (by rw [ιOf_X]; exact π₀₁_const hR) a

/- English proof (translation)
Introduce `δ hδ`. Establish `hX : ((W.γ₀ δ).comp (ιOf hR)) PowerSeries.X = (ιOf hR) PowerSeries.X`. Rewrite using `[AlgHom.comp_apply, ιOf_X]`. Conclude with `π₀₁_inv hR δ hδ`. Establish `h0 : PowerSeries.constantCoeff (((W.γ₀ δ).comp (ιOf hR)) PowerSeries.X) = 0`.

Rewrite using `[hX, ιOf_X]`. Conclude with `π₀₁_const hR`. Conclude with `AlgHom.congr_fun (algHom_ext_X _ _ hX h0) a`.
-/
theorem ιOf_inv (hR : Ring9 W) (a : PowerSeries O) : Inv1 W (ιOf hR a) := by
  intro δ hδ
  have hX : ((W.γ₀ δ).comp (ιOf hR)) PowerSeries.X = (ιOf hR) PowerSeries.X := by
    rw [AlgHom.comp_apply, ιOf_X]
    exact π₀₁_inv hR δ hδ
  have h0 : PowerSeries.constantCoeff (((W.γ₀ δ).comp (ιOf hR)) PowerSeries.X) = 0 := by
    rw [hX, ιOf_X]
    exact π₀₁_const hR
  exact AlgHom.congr_fun (algHom_ext_X _ _ hX h0) a

/- English proof (translation)
Establish `hR' : Ring9 W` using `hR`. Take `⟨-, h2, -⟩` from `hR'`. Take `⟨f, hf, -⟩` from `h2 (fun _ => a) (diag_mem_AΔ ha)`. Use `⟨f 0, ?_⟩` and prove the remaining obligations. Rewrite using `[ιOf_apply]`.

Conclude with `(hf 0).symm`.
-/
theorem ιOf_full (hR : Ring9 W) (a : PowerSeries O) (ha : Inv1 W a) : ∃ f, ιOf hR f = a := by
  have hR' : Ring9 W := hR
  obtain ⟨-, h2, -⟩ := hR'
  obtain ⟨f, hf, -⟩ := h2 (fun _ => a) (diag_mem_AΔ ha)
  refine ⟨f 0, ?_⟩
  rw [ιOf_apply]
  exact (hf 0).symm

/- English proof (translation)
Introduce `f g hfg`. Establish `hR' : Ring9 W` using `hR`. Take `⟨-, h2, -⟩` from `hR'`. Take `⟨F, -, hF⟩` from `h2 (fun _ => ιOf hR f) (diag_mem_AΔ (ιOf_inv hR f))`. Establish `e1` using `hF (fun _ => f) (fun i => by show ιOf hR f = PowerSeries.subst W.π₀₁ f`.

Conclude with `ιOf_apply hR f)`. Establish `e2` using `hF (fun _ => g) (fun i => by show ιOf hR f = PowerSeries.subst W.π₀₁ g`. Rewrite using `[hfg]`. Conclude with `ιOf_apply hR g)`. Conclude with `congrFun (e1.trans e2.symm) 0`.
-/
theorem ιOf_inj (hR : Ring9 W) : Function.Injective (ιOf hR) := by
  intro f g hfg
  have hR' : Ring9 W := hR
  obtain ⟨-, h2, -⟩ := hR'
  obtain ⟨F, -, hF⟩ := h2 (fun _ => ιOf hR f) (diag_mem_AΔ (ιOf_inv hR f))
  have e1 := hF (fun _ => f) (fun i => by
    show ιOf hR f = PowerSeries.subst W.π₀₁ f
    exact ιOf_apply hR f)
  have e2 := hF (fun _ => g) (fun i => by
    show ιOf hR f = PowerSeries.subst W.π₀₁ g
    rw [hfg]
    exact ιOf_apply hR g)
  exact congrFun (e1.trans e2.symm) 0

def pre (hR : Ring9 W) (a : PowerSeries O) (ha : Inv1 W a) : PowerSeries O :=
  Classical.choose (ιOf_full hR a ha)

/- English proof (translation)
Conclude with `Classical.choose_spec (ιOf_full hR a ha)`.
-/
theorem ι_pre (hR : Ring9 W) (a : PowerSeries O) (ha : Inv1 W a) : ιOf hR (pre hR a ha) = a := by
  exact Classical.choose_spec (ιOf_full hR a ha)

structure ComΔ (W : LocWach PD LL O v n) (ψ : PowerSeries O →ₐ[O] PowerSeries O) : Prop where
  const : PowerSeries.constantCoeff (ψ PowerSeries.X) = 0
  comm : ∀ δ ∈ W.DelF, ∀ a, W.γ₀ δ (ψ a) = ψ (W.γ₀ δ a)

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[hψ.comm δ hδ a, ha δ hδ]`.
-/
theorem ComΔ.inv {ψ : PowerSeries O →ₐ[O] PowerSeries O} (hψ : ComΔ W ψ) {a : PowerSeries O}
    (ha : Inv1 W a) : Inv1 W (ψ a) := by
  intro δ hδ
  rw [hψ.comm δ hδ a, ha δ hδ]

/- English proof (translation)
Rewrite using `[W.φ₀_X, map_mul, PowerSeries.constantCoeff_X, zero_mul] comm δ _ a := (W.γ₀_comm δ a).symm`.
-/
theorem comΔ_φ : ComΔ W W.φ₀ where
  const := by rw [W.φ₀_X, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  comm δ _ a := (W.γ₀_comm δ a).symm

/- English proof (translation)
The claim follows from `(W.γ₀_X g).1 comm δ _ a := by rw [← AlgHom.mul_apply, ← AlgHom.mul_apply, ← map_mul, ← map_mul, mul_comm]`.
-/
theorem comΔ_γ (g : W.Gam) : ComΔ W (W.γ₀ g) where
  const := (W.γ₀_X g).1
  comm δ _ a := by
    rw [← AlgHom.mul_apply, ← AlgHom.mul_apply, ← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Rewrite using `[← ιOf_const hR, ι_pre, constCoeff_algHom ψ hψ.const, π₀₁_const hR]`.
-/
theorem pre_const (hR : Ring9 W) {ψ : PowerSeries O →ₐ[O] PowerSeries O} (hψ : ComΔ W ψ) :
    PowerSeries.constantCoeff (pre hR (ψ W.π₀₁) (hψ.inv (π₀₁_inv hR))) = 0 := by
  rw [← ιOf_const hR, ι_pre, constCoeff_algHom ψ hψ.const, π₀₁_const hR]

def liftOf (hR : Ring9 W) {ψ : PowerSeries O →ₐ[O] PowerSeries O} (hψ : ComΔ W ψ) :
    PowerSeries O →ₐ[O] PowerSeries O :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (pre_const hR hψ))

/- English proof (translation)
Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero' (pre_const hR hψ)`. Use `first`. Consider the case `exact PowerSeries.subst_X hs`. Consider the case `(simp only [liftOf, PowerSeries.coe_substAlgHom]; exact PowerSeries.subst_X hs)`.
-/
theorem liftOf_X (hR : Ring9 W) {ψ : PowerSeries O →ₐ[O] PowerSeries O} (hψ : ComΔ W ψ) :
    liftOf hR hψ PowerSeries.X = pre hR (ψ W.π₀₁) (hψ.inv (π₀₁_inv hR)) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' (pre_const hR hψ)
  first
    | exact PowerSeries.subst_X hs
    | (simp only [liftOf, PowerSeries.coe_substAlgHom]; exact PowerSeries.subst_X hs)

/- English proof (translation)
Establish `hX : ((ιOf hR).comp (liftOf hR hψ)) PowerSeries.X = (ψ.comp (ιOf hR)) PowerSeries.X`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, liftOf_X, ι_pre, ιOf_X]`. Establish `h0 : PowerSeries.constantCoeff (((ιOf hR).comp (liftOf hR hψ)) PowerSeries.X) = 0`. Rewrite using `[hX, AlgHom.comp_apply, ιOf_X, constCoeff_algHom ψ hψ.const, π₀₁_const hR]`. Conclude with `AlgHom.congr_fun (algHom_ext_X _ _ hX h0) a`.
-/
theorem ι_liftOf (hR : Ring9 W) {ψ : PowerSeries O →ₐ[O] PowerSeries O} (hψ : ComΔ W ψ)
    (a : PowerSeries O) : ιOf hR (liftOf hR hψ a) = ψ (ιOf hR a) := by
  have hX : ((ιOf hR).comp (liftOf hR hψ)) PowerSeries.X = (ψ.comp (ιOf hR)) PowerSeries.X := by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, liftOf_X, ι_pre, ιOf_X]
  have h0 : PowerSeries.constantCoeff (((ιOf hR).comp (liftOf hR hψ)) PowerSeries.X) = 0 := by
    rw [hX, AlgHom.comp_apply, ιOf_X, constCoeff_algHom ψ hψ.const, π₀₁_const hR]
  exact AlgHom.congr_fun (algHom_ext_X _ _ hX h0) a

def baseIdOf (hR : Ring9 W) : BaseId W where
  Bs :=
    { ℓ := PD.p
      φ := liftOf hR comΔ_φ
      γ := liftOf hR (comΔ_γ W.gamK)
      comm := fun a => by
        apply ιOf_inj hR
        rw [ι_liftOf, ι_liftOf, ι_liftOf, ι_liftOf, W.γ₀_comm] }
  ι := ιOf hR
  ι_X := ιOf_X hR
  ι_φ := ι_liftOf hR comΔ_φ
  ι_γ := ι_liftOf hR (comΔ_γ W.gamK)
  ι_Δ := fun δ hδ a => ιOf_inv hR a δ hδ
  ℓ_eq := rfl

/- English proof (translation)
Introduce `x y hxy`. Conclude with `ιOf_inj hR hxy`.
-/
theorem baseIdOf_inj (hR : Ring9 W) : (baseIdOf hR).Inj := by
  intro x y hxy
  exact ιOf_inj hR hxy

/- English proof (translation)
Introduce `a ha`. Conclude with `ιOf_full hR a ha`.
-/
theorem baseIdOf_full (hR : Ring9 W) : (baseIdOf hR).Full := by
  intro a ha
  exact ιOf_full hR a ha

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[map_mul, ha δ hδ, hb δ hδ]`.
-/
theorem Inv1.mul {a b : PowerSeries O} (ha : Inv1 W a) (hb : Inv1 W b) : Inv1 W (a * b) := by
  intro δ hδ
  rw [map_mul, ha δ hδ, hb δ hδ]

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[map_add, ha δ hδ, hb δ hδ]`.
-/
theorem Inv1.add {a b : PowerSeries O} (ha : Inv1 W a) (hb : Inv1 W b) : Inv1 W (a + b) := by
  intro δ hδ
  rw [map_add, ha δ hδ, hb δ hδ]

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[map_sub, ha δ hδ, hb δ hδ]`.
-/
theorem Inv1.sub {a b : PowerSeries O} (ha : Inv1 W a) (hb : Inv1 W b) : Inv1 W (a - b) := by
  intro δ hδ
  rw [map_sub, ha δ hδ, hb δ hδ]

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[map_pow, ha δ hδ]`.
-/
theorem Inv1.pow {a : PowerSeries O} (ha : Inv1 W a) (k : ℕ) : Inv1 W (a ^ k) := by
  intro δ hδ
  rw [map_pow, ha δ hδ]

/- English proof (translation)
Introduce `δ _`. Conclude with `map_natCast _ k`.
-/
theorem invariant_natCast (k : ℕ) : Inv1 W ((k : ℕ) : PowerSeries O) := by
  intro δ _
  exact map_natCast _ k

variable (W) in

def qP₁ : PowerSeries O := W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)

/- English proof (translation)
Rewrite using `[qP₁]`. Conclude with `(π₀₁_inv hR).add (invariant_natCast _)`.
-/
theorem qP₁_inv (hR : Ring9 W) : Inv1 W (qP₁ W) := by
  rw [qP₁]
  exact (π₀₁_inv hR).add (invariant_natCast _)

/- English proof (translation)
Use `show ιOf hR (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)`. Rewrite using `[map_add, ιOf_X, map_natCast, map_natCast]`.
-/
theorem ι_q (hR : Ring9 W) : ιOf hR (baseIdOf hR).Bs.q = qP₁ W := by
  show ιOf hR (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)
  rw [map_add, ιOf_X, map_natCast, map_natCast]

section Dom

variable [IsDomain O]

/- English proof (translation)
Take `⟨w, hw, he⟩` from `π₀₁_eq hR`. Rewrite using `[he]`. Conclude with `mul_ne_zero hw.ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)`.
-/
theorem π₀₁_ne (hR : Ring9 W) : W.π₀₁ ≠ 0 := by
  obtain ⟨w, hw, he⟩ := π₀₁_eq hR
  rw [he]
  exact mul_ne_zero hw.ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg PowerSeries.constantCoeff h`. Rewrite `h1` using `[qP₁, map_add, π₀₁_const hR, zero_add, map_natCast, map_zero]`. Establish `h2` using `W.v_l`. Establish `h3 : ((PD.p : ℕ) : LL) = 0`.

Rewrite using `[← map_natCast (algebraMap O LL), h1, map_zero]`. Rewrite `h2` using `[h3, AddValuation.map_zero]`. Use `first`. Consider the case `exact absurd h2 (by simp)`. Consider the case `exact WithTop.top_ne_coe h2`.
-/
theorem qP₁_ne (hR : Ring9 W) : qP₁ W ≠ 0 := by
  intro h
  have h1 := congrArg PowerSeries.constantCoeff h
  rw [qP₁, map_add, π₀₁_const hR, zero_add, map_natCast, map_zero] at h1
  have h2 := W.v_l
  have h3 : ((PD.p : ℕ) : LL) = 0 := by
    rw [← map_natCast (algebraMap O LL), h1, map_zero]
  rw [h3, AddValuation.map_zero] at h2
  first
    | exact absurd h2 (by simp)
    | exact WithTop.top_ne_coe h2

/- English proof (translation)
Take `⟨w', rfl⟩` from `hw`. Establish `hwinv : Inv1 W (w' : PowerSeries O)`. Introduce `δ hδ`. Establish `e : W.γ₀ δ b = W.γ₀ δ ((w' : PowerSeries O) * c)` using `by rw [h]`. Rewrite `e` using `[hb δ hδ, map_mul, hc δ hδ]`.

Rewrite `e` using `[h]`. Conclude with `(mul_right_cancel₀ hc0 e).symm`. Establish `hwinv' : Inv1 W ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O)`. Introduce `δ hδ`. Establish `e1 : W.γ₀ δ ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) * (w' : PowerSeries O) = 1`.

Rewrite using `[← hwinv δ hδ, ← map_mul, Units.inv_mul, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, Units.mul_inv, mul_one]`. Use `_ = ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) := by rw [e1, one_mul]`. Take `⟨f, hf⟩` from `ιOf_full hR _ hwinv`.

Take `⟨g, hg⟩` from `ιOf_full hR _ hwinv'`. Establish `hfg : f * g = 1` using `ιOf_inj hR (by rw [map_mul, map_one, hf, hg, Units.mul_inv])`. Conclude with `⟨⟨f, g, hfg, by rw [mul_comm, hfg]⟩, hf⟩`.
-/
theorem unit_desc (hR : Ring9 W) {w b c : PowerSeries O} (hw : IsUnit w) (hb : Inv1 W b)
    (hc : Inv1 W c) (hc0 : c ≠ 0) (h : b = w * c) :
    ∃ u : (PowerSeries O)ˣ, ιOf hR (u : PowerSeries O) = w := by
  obtain ⟨w', rfl⟩ := hw
  have hwinv : Inv1 W (w' : PowerSeries O) := by
    intro δ hδ
    have e : W.γ₀ δ b = W.γ₀ δ ((w' : PowerSeries O) * c) := by rw [h]
    rw [hb δ hδ, map_mul, hc δ hδ] at e
    rw [h] at e
    exact (mul_right_cancel₀ hc0 e).symm
  have hwinv' : Inv1 W ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) := by
    intro δ hδ
    have e1 : W.γ₀ δ ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) * (w' : PowerSeries O) = 1 := by
      rw [← hwinv δ hδ, ← map_mul, Units.inv_mul, map_one]
    calc W.γ₀ δ ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O)
        = W.γ₀ δ ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) * (w' : PowerSeries O) *
            ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = ((w'⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) := by rw [e1, one_mul]
  obtain ⟨f, hf⟩ := ιOf_full hR _ hwinv
  obtain ⟨g, hg⟩ := ιOf_full hR _ hwinv'
  have hfg : f * g = 1 := ιOf_inj hR (by rw [map_mul, map_one, hf, hg, Units.mul_inv])
  exact ⟨⟨f, g, hfg, by rw [mul_comm, hfg]⟩, hf⟩

/- English proof (translation)
Establish `hR' : Ring9 W` using `hR`. Take `⟨-, -, -, -, -, ⟨w, hw⟩, -⟩` from `hR'`. Establish `hw0 : IsUnit ((w : LetA O n) 0)` using `w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) 0)`. Establish `e : Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) = qP₁ W`. Rewrite using `[qP₁, map_add, Polynomial.aeval_X, Polynomial.aeval_C, map_natCast]`.

Establish `key : W.φ₀ W.π₀₁ = (w : LetA O n) 0 * (W.π₀₁ * qP₁ W ^ (PD.p - 1))`. Establish `h0 : W.φ₀ W.π₀₁ = (w : LetA O n) 0 * W.π₀₁ * Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) ^ (PD.p - 1)` using `by first`. Consider the case `exact congrFun hw 0`. Consider the case `simpa [Formalism.BasicNotions.LocWach.φA, Formalism.BasicNotions.letφ, Formalism.BasicNotions.LocWach.π₀, Formalism.MainNotions.DeltaInvariantLattices.Eat] using congrFun hw 0`. Rewrite using `[h0, e, mul_assoc]`.

Establish `hφX : ιOf hR ((baseIdOf hR).Bs.φ PowerSeries.X) = W.φ₀ W.π₀₁` using `by show ιOf hR (liftOf hR comΔ_φ PowerSeries.X) = _`. Rewrite using `[ι_liftOf, ιOf_X]`. Establish `hc : ιOf hR (PowerSeries.X * (baseIdOf hR).Bs.q ^ (PD.p - 1)) = W.π₀₁ * qP₁ W ^ (PD.p - 1)`. Rewrite using `[map_mul, map_pow, ιOf_X, ι_q]`. Take `⟨u, hu⟩` from `unit_desc hR (b := ιOf hR ((baseIdOf hR).Bs.φ PowerSeries.X)) (c := ιOf hR (PowerSeries.X * (baseIdOf hR).Bs.q ^ (PD.p - 1))) hw0 (ιOf_inv hR _) (ιOf_inv hR _) (by rw [hc]; exact mul_ne_zero (π₀₁_ne hR) (pow_ne_zero _ (qP₁_ne hR))) (by rw [hφX, hc, key])`.

Use `show ∃ u : (PowerSeries O)ˣ, (baseIdOf hR).Bs.φ PowerSeries.X = (u : PowerSeries O) * PowerSeries.X * (baseIdOf hR).Bs.q ^ (PD.p - 1)`. Use `⟨u, ιOf_inj hR ?_⟩` and prove the remaining obligations. Establish `hr : ιOf hR ((u : PowerSeries O) * PowerSeries.X * (baseIdOf hR).Bs.q ^ (PD.p - 1)) = (w : LetA O n) 0 * (W.π₀₁ * qP₁ W ^ (PD.p - 1))`. Rewrite using `[mul_assoc, map_mul, hu, hc]`. Rewrite using `[hr, hφX, key]`.
-/
theorem frobenius_uniformizer_identity (hR : Ring9 W) : (baseIdOf hR).Bs.E3 := by
  have hR' : Ring9 W := hR
  obtain ⟨-, -, -, -, -, ⟨w, hw⟩, -⟩ := hR'
  have hw0 : IsUnit ((w : LetA O n) 0) :=
    w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) 0)
  have e : Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) = qP₁ W := by
    rw [qP₁, map_add, Polynomial.aeval_X, Polynomial.aeval_C, map_natCast]
  have key : W.φ₀ W.π₀₁ = (w : LetA O n) 0 * (W.π₀₁ * qP₁ W ^ (PD.p - 1)) := by
    have h0 : W.φ₀ W.π₀₁ = (w : LetA O n) 0 * W.π₀₁ *
        Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) ^ (PD.p - 1) := by
      first
        | exact congrFun hw 0
        | simpa [Formalism.BasicNotions.LocWach.φA, Formalism.BasicNotions.letφ, Formalism.BasicNotions.LocWach.π₀, Formalism.MainNotions.DeltaInvariantLattices.Eat] using
            congrFun hw 0
    rw [h0, e, mul_assoc]
  have hφX : ιOf hR ((baseIdOf hR).Bs.φ PowerSeries.X) = W.φ₀ W.π₀₁ := by
    show ιOf hR (liftOf hR comΔ_φ PowerSeries.X) = _
    rw [ι_liftOf, ιOf_X]
  have hc : ιOf hR (PowerSeries.X * (baseIdOf hR).Bs.q ^ (PD.p - 1)) =
      W.π₀₁ * qP₁ W ^ (PD.p - 1) := by
    rw [map_mul, map_pow, ιOf_X, ι_q]
  obtain ⟨u, hu⟩ := unit_desc hR (b := ιOf hR ((baseIdOf hR).Bs.φ PowerSeries.X))
    (c := ιOf hR (PowerSeries.X * (baseIdOf hR).Bs.q ^ (PD.p - 1))) hw0 (ιOf_inv hR _)
    (ιOf_inv hR _) (by rw [hc]; exact mul_ne_zero (π₀₁_ne hR) (pow_ne_zero _ (qP₁_ne hR)))
    (by rw [hφX, hc, key])
  show ∃ u : (PowerSeries O)ˣ, (baseIdOf hR).Bs.φ PowerSeries.X =
    (u : PowerSeries O) * PowerSeries.X * (baseIdOf hR).Bs.q ^ (PD.p - 1)
  refine ⟨u, ιOf_inj hR ?_⟩
  have hr : ιOf hR ((u : PowerSeries O) * PowerSeries.X * (baseIdOf hR).Bs.q ^ (PD.p - 1)) =
      (w : LetA O n) 0 * (W.π₀₁ * qP₁ W ^ (PD.p - 1)) := by
    rw [mul_assoc, map_mul, hu, hc]
  rw [hr, hφX, key]

/- English proof (translation)
Establish `hR' : Ring9 W` using `hR`. Take `⟨-, -, -, -, -, -, ⟨w, hw⟩, -⟩` from `hR'`. Establish `hw0 : IsUnit ((w : LetA O n) 0)` using `w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) 0)`. Establish `e : Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) = qP₁ W`. Rewrite using `[qP₁, map_add, Polynomial.aeval_X, Polynomial.aeval_C, map_natCast]`.

Establish `key : W.γ₀ W.gamK W.π₀₁ - W.π₀₁ = (w : LetA O n) 0 * (W.π₀₁ * qP₁ W)`. Establish `h0 : W.γ₀ W.gam W.π₀₁ - W.π₀₁ = (w : LetA O n) 0 * W.π₀₁ * Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))` using `by first`. Consider the case `exact congrFun hw 0`. Consider the case `simpa [Formalism.BasicNotions.LocWach.γA, Formalism.BasicNotions.letγ, Formalism.BasicNotions.LocWach.π₀, Formalism.MainNotions.DeltaInvariantLattices.Eat] using congrFun hw 0`. Rewrite using `[hγ, h0, e, mul_assoc]`.

Establish `hγX : ιOf hR ((baseIdOf hR).Bs.γ PowerSeries.X) = W.γ₀ W.gamK W.π₀₁` using `by show ιOf hR (liftOf hR (comΔ_γ W.gamK) PowerSeries.X) = _`. Rewrite using `[ι_liftOf, ιOf_X]`. Establish `hc : ιOf hR (PowerSeries.X * (baseIdOf hR).Bs.q) = W.π₀₁ * qP₁ W`. Rewrite using `[map_mul, ιOf_X, ι_q]`. Take `⟨u, hu⟩` from `unit_desc hR (b := ιOf hR ((baseIdOf hR).Bs.γ PowerSeries.X - PowerSeries.X)) (c := ιOf hR (PowerSeries.X * (baseIdOf hR).Bs.q)) hw0 (ιOf_inv hR _) (ιOf_inv hR _) (by rw [hc]; exact mul_ne_zero (π₀₁_ne hR) (qP₁_ne hR)) (by rw [map_sub, hγX, ιOf_X, hc, key])`.

Use `show ∃ e : (PowerSeries O)ˣ, (baseIdOf hR).Bs.γ PowerSeries.X = PowerSeries.X * (1 + (e : PowerSeries O) * (baseIdOf hR).Bs.q)`. Use `⟨u, ιOf_inj hR ?_⟩` and prove the remaining obligations. Establish `hr : ιOf hR (PowerSeries.X * (1 + (u : PowerSeries O) * (baseIdOf hR).Bs.q)) = W.π₀₁ * (1 + (w : LetA O n) 0 * qP₁ W)`. Rewrite using `[map_mul, map_add, map_one, map_mul, hu, ιOf_X, ι_q]`. Rewrite using `[hγX, hr]`.

Take the linear combination `key`.
-/
theorem fourth_lefschetz_of_first (hR : Ring9 W) (hγ : W.gamK = W.gam) : (baseIdOf hR).Bs.E4 := by
  have hR' : Ring9 W := hR
  obtain ⟨-, -, -, -, -, -, ⟨w, hw⟩, -⟩ := hR'
  have hw0 : IsUnit ((w : LetA O n) 0) :=
    w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) 0)
  have e : Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) = qP₁ W := by
    rw [qP₁, map_add, Polynomial.aeval_X, Polynomial.aeval_C, map_natCast]
  have key : W.γ₀ W.gamK W.π₀₁ - W.π₀₁ = (w : LetA O n) 0 * (W.π₀₁ * qP₁ W) := by
    have h0 : W.γ₀ W.gam W.π₀₁ - W.π₀₁ = (w : LetA O n) 0 * W.π₀₁ *
        Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) := by
      first
        | exact congrFun hw 0
        | simpa [Formalism.BasicNotions.LocWach.γA, Formalism.BasicNotions.letγ, Formalism.BasicNotions.LocWach.π₀, Formalism.MainNotions.DeltaInvariantLattices.Eat] using
            congrFun hw 0
    rw [hγ, h0, e, mul_assoc]
  have hγX : ιOf hR ((baseIdOf hR).Bs.γ PowerSeries.X) = W.γ₀ W.gamK W.π₀₁ := by
    show ιOf hR (liftOf hR (comΔ_γ W.gamK) PowerSeries.X) = _
    rw [ι_liftOf, ιOf_X]
  have hc : ιOf hR (PowerSeries.X * (baseIdOf hR).Bs.q) = W.π₀₁ * qP₁ W := by
    rw [map_mul, ιOf_X, ι_q]
  obtain ⟨u, hu⟩ := unit_desc hR
    (b := ιOf hR ((baseIdOf hR).Bs.γ PowerSeries.X - PowerSeries.X))
    (c := ιOf hR (PowerSeries.X * (baseIdOf hR).Bs.q)) hw0 (ιOf_inv hR _) (ιOf_inv hR _)
    (by rw [hc]; exact mul_ne_zero (π₀₁_ne hR) (qP₁_ne hR))
    (by rw [map_sub, hγX, ιOf_X, hc, key])
  show ∃ e : (PowerSeries O)ˣ, (baseIdOf hR).Bs.γ PowerSeries.X =
    PowerSeries.X * (1 + (e : PowerSeries O) * (baseIdOf hR).Bs.q)
  refine ⟨u, ιOf_inj hR ?_⟩
  have hr : ιOf hR (PowerSeries.X * (1 + (u : PowerSeries O) * (baseIdOf hR).Bs.q)) =
      W.π₀₁ * (1 + (w : LetA O n) 0 * qP₁ W) := by
    rw [map_mul, map_add, map_one, map_mul, hu, ιOf_X, ι_q]
  rw [hγX, hr]
  linear_combination key

/- English proof (translation)
The claim follows from `PD.hp three_le := h3 one_le_e := he assoc := hass complete := hcomp e3 := frobenius_uniformizer_identity hR e4 := fourth_lefschetz_of_first hR hγ`.
-/
theorem primBase_of (hR : Ring9 W) (hγ : W.gamK = W.gam) (h3 : 3 ≤ PD.p) {ϖ : O} {eO : ℕ}
    (he : 1 ≤ eO) (hass : Associated (((PD.p : ℕ) : O)) (ϖ ^ eO))
    (hcomp : IsAdicComplete (Ideal.span {(((PD.p : ℕ) : O))}) O) :
    Formalism.ExponentWindows.E.PrimBase (baseIdOf hR).Bs ϖ eO where
  prime := PD.hp
  three_le := h3
  one_le_e := he
  assoc := hass
  complete := hcomp
  e3 := frobenius_uniformizer_identity hR
  e4 := fourth_lefschetz_of_first hR hγ

end Dom

/- English proof (translation)
Introduce `h`. Establish `h1` using `W.v_l`. Establish `h2 : ((PD.p : ℕ) : LL) = 0`. Rewrite using `[← map_natCast (algebraMap O LL), h, map_zero]`. Rewrite `h1` using `[h2, AddValuation.map_zero]`.

Use `first`. Consider the case `exact absurd h1 (by simp)`. Consider the case `exact WithTop.top_ne_coe h1`.
-/
theorem p_ne_zero_O (W : LocWach PD LL O v n) : (((PD.p : ℕ) : O)) ≠ 0 := by
  intro h
  have h1 := W.v_l
  have h2 : ((PD.p : ℕ) : LL) = 0 := by
    rw [← map_natCast (algebraMap O LL), h, map_zero]
  rw [h2, AddValuation.map_zero] at h1
  first
    | exact absurd h1 (by simp)
    | exact WithTop.top_ne_coe h1

/- English proof (translation)
Take `⟨m, hm⟩` from `IsDiscreteValuationRing.associated_pow_irreducible (p_ne_zero_O W) hϖ`. Use `⟨m, Nat.one_le_iff_ne_zero.mpr ?_, hm⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hu (hm.isUnit_iff.mpr (by rw [pow_zero]; exact isUnit_one))`.
-/
theorem exists_eO [IsDomain O] [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) {ϖ : O}
    (hϖ : Irreducible ϖ) (hu : ¬ IsUnit (((PD.p : ℕ) : O))) :
    ∃ eO : ℕ, 1 ≤ eO ∧ Associated (((PD.p : ℕ) : O)) (ϖ ^ eO) := by
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible (p_ne_zero_O W) hϖ
  refine ⟨m, Nat.one_le_iff_ne_zero.mpr ?_, hm⟩
  rintro rfl
  exact hu (hm.isUnit_iff.mpr (by rw [pow_zero]; exact isUnit_one))

/- English proof (translation)
Conclude with `(LinearEquiv.ofBijective (Algebra.linearMap K₀ K) h).finrank_eq.symm.trans (Module.finrank_self K₀)`.
-/
theorem finrank_one_of_bij (h : Function.Bijective (algebraMap K₀ K)) : Module.finrank K₀ K = 1 := by
  exact (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) h).finrank_eq.symm.trans
    (Module.finrank_self K₀)

/- English proof (translation)
Take `⟨-, -, h⟩` from `h9 hs hp`. Conclude with `(h hK).1`.
-/
theorem ring_condition_of_delta_invariants {T : LocLat G Qp LL O} (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T) (hs : W.s = 1) (hp : PD.p ≠ 2)
    (hK : Module.finrank K₀ K = 1) : Ring9 W := by
  obtain ⟨-, -, h⟩ := h9 hs hp
  exact (h hK).1

def ValRing (O : Type) [CommRing O] [Algebra O LL] (v : AddValuation LL (WithTop ℚ)) : Prop :=
  Function.Injective (algebraMap O LL) ∧ (∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) ∧
    ∀ o : O, 0 ≤ v (algebraMap O LL o)

/- English proof (translation)
Take `⟨-, -, hpos⟩` from `hV`. Introduce and unpack `⟨u, hu⟩`. Establish `hv` using `hpos ((u⁻¹ : Oˣ) : O)`. Establish `e : algebraMap O LL ((u⁻¹ : Oˣ) : O) * ((PD.p : ℕ) : LL) = 1`. Rewrite using `[← map_natCast (algebraMap O LL), ← map_mul, ← hu, Units.inv_mul, map_one]`.

Establish `e2` using `congrArg v e`. Rewrite `e2` using `[AddValuation.map_mul, AddValuation.map_one, W.v_l]`. Use `revert hv e2`. Generalize the expression as in `v (algebraMap O LL ((u⁻¹ : Oˣ) : O)) = x`. Introduce `hv e2`.

Proceed by induction on `x using WithTop.recTopCoe with`. Consider the case `top => simp at e2`. Consider the case `coe r`. Establish `h1 : r + 1 = 0` using `by exact_mod_cast e2`. Establish `h2 : (0 : ℚ) ≤ r` using `by exact_mod_cast hv`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_isUnit_p (W : LocWach PD LL O v n) (hV : ValRing O v) :
    ¬ IsUnit (((PD.p : ℕ) : O)) := by
  obtain ⟨-, -, hpos⟩ := hV
  rintro ⟨u, hu⟩
  have hv := hpos ((u⁻¹ : Oˣ) : O)
  have e : algebraMap O LL ((u⁻¹ : Oˣ) : O) * ((PD.p : ℕ) : LL) = 1 := by
    rw [← map_natCast (algebraMap O LL), ← map_mul, ← hu, Units.inv_mul, map_one]
  have e2 := congrArg v e
  rw [AddValuation.map_mul, AddValuation.map_one, W.v_l] at e2
  revert hv e2
  generalize v (algebraMap O LL ((u⁻¹ : Oˣ) : O)) = x
  intro hv e2
  induction x using WithTop.recTopCoe with
  | top => simp at e2
  | coe r =>
    have h1 : r + 1 = 0 := by exact_mod_cast e2
    have h2 : (0 : ℚ) ≤ r := by exact_mod_cast hv
    linarith

/- English proof (translation)
Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top => exact absurd rfl ha`. Consider the case `coe r`. Proceed by induction on `b using WithTop.recTopCoe with`. Consider the case `top => simp at h`.

Consider the case `coe s`. Establish `h1 : r + s = r` using `by exact_mod_cast h`. Establish `h2 : s = 0` using `by linarith`. Simplify using `[h2]`.
-/
theorem add_eq_self_WithTop {a b : WithTop ℚ} (ha : a ≠ ⊤) (h : a + b = a) : b = 0 := by
  induction a using WithTop.recTopCoe with
  | top => exact absurd rfl ha
  | coe r =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe s =>
      have h1 : r + s = r := by exact_mod_cast h
      have h2 : s = 0 := by linarith
      simp [h2]

/- English proof (translation)
Take `⟨hinj, hsurj, -⟩` from `hV`. Establish `hne : algebraMap O LL o ≠ 0`. Introduce `h`. Rewrite `ho` using `[h, AddValuation.map_zero]`. Conclude with `absurd ho (by simp)`.

Establish `hv : v (algebraMap O LL o)⁻¹ = 0`. Establish `h1` using `congrArg v (mul_inv_cancel₀ hne)`. Rewrite `h1` using `[AddValuation.map_mul, AddValuation.map_one, ho, zero_add]`. Then use the resulting hypothesis. Take `⟨o', ho'⟩` from `hsurj _ hv.ge`. Establish `hmul : o * o' = 1` using `hinj (by rw [map_mul, ho', map_one, mul_inv_cancel₀ hne])`.

Conclude with `⟨⟨o, o', hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩`.
-/
theorem isUnit_of_v_zero (hV : ValRing O v) (o : O) (ho : v (algebraMap O LL o) = 0) : IsUnit o := by
  obtain ⟨hinj, hsurj, -⟩ := hV
  have hne : algebraMap O LL o ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at ho
    exact absurd ho (by simp)
  have hv : v (algebraMap O LL o)⁻¹ = 0 := by
    have h1 := congrArg v (mul_inv_cancel₀ hne)
    rwa [AddValuation.map_mul, AddValuation.map_one, ho, zero_add] at h1
  obtain ⟨o', ho'⟩ := hsurj _ hv.ge
  have hmul : o * o' = 1 := hinj (by rw [map_mul, ho', map_one, mul_inv_cancel₀ hne])
  exact ⟨⟨o, o', hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

/- English proof (translation)
Establish `hV' : ValRing O v` using `hV`. Take `⟨hinj, hsurj, -⟩` from `hV'`. Establish `hpne : ((PD.p : ℕ) : LL) ≠ 0`. Introduce `h`. Establish `h1` using `W.v_l`.

Rewrite `h1` using `[h, AddValuation.map_zero]`. Conclude with `absurd h1 (by simp)`. Establish `hvy : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)) = 1`. Rewrite using `[map_sub, map_one, W.gam_gen, hs, Nat.cast_one]`. Establish `e : ((PD.p : ℕ) : LL) * (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1) / ((PD.p : ℕ) : LL)) = algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)`.

Rewrite using `[mul_div_assoc', mul_comm, mul_div_assoc, div_self hpne, mul_one]`. Establish `hz : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1) / ((PD.p : ℕ) : LL)) = 0`. Establish `h2` using `congrArg v e`. Rewrite `h2` using `[AddValuation.map_mul, W.v_l, hvy]`. Conclude with `add_eq_self_WithTop (by simp) h2`.

Take `⟨x, hx⟩` from `hsurj _ hz.ge`. Establish `hxu : IsUnit x` using `isUnit_of_v_zero hV x (by rw [hx, hz])`. Use `⟨hxu.unit, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, map_add, map_one, map_mul, map_natCast, hx, e, map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem u_eq_of (W : LocWach PD LL O v n) (hV : ValRing O v) (hs : W.s = 1) :
    ∃ x : Oˣ, ((W.χΓ W.gam : Oˣ) : O) = 1 + ((PD.p : ℕ) : O) * (x : O) := by
  have hV' : ValRing O v := hV
  obtain ⟨hinj, hsurj, -⟩ := hV'
  have hpne : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h
    have h1 := W.v_l
    rw [h, AddValuation.map_zero] at h1
    exact absurd h1 (by simp)
  have hvy : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)) = 1 := by
    rw [map_sub, map_one, W.gam_gen, hs, Nat.cast_one]
  have e : ((PD.p : ℕ) : LL) * (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1) / ((PD.p : ℕ) : LL)) =
      algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1) := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hpne, mul_one]
  have hz : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1) / ((PD.p : ℕ) : LL)) = 0 := by
    have h2 := congrArg v e
    rw [AddValuation.map_mul, W.v_l, hvy] at h2
    exact add_eq_self_WithTop (by simp) h2
  obtain ⟨x, hx⟩ := hsurj _ hz.ge
  have hxu : IsUnit x := isUnit_of_v_zero hV x (by rw [hx, hz])
  refine ⟨hxu.unit, hinj ?_⟩
  rw [IsUnit.unit_spec, map_add, map_one, map_mul, map_natCast, hx, e, map_sub, map_one]
  ring

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨eO, he, hass⟩` from `exists_eO W hϖ (not_isUnit_p W hV)`. Take `⟨x, hx⟩` from `u_eq_of W hV hs`. Establish `hγ : W.gamK = W.gam` using `W.gamK_eq_one hs (by omega)`. Conclude with `⟨ϖ, eO, x, hϖ, primBase_of hR hγ h3 he hass hcomp, hx⟩`.
-/
theorem ground_of [IsDomain O] [IsDiscreteValuationRing O] (hR : Ring9 W) (hs : W.s = 1)
    (h3 : 3 ≤ PD.p) (hV : ValRing O v)
    (hcomp : IsAdicComplete (Ideal.span {(((PD.p : ℕ) : O))}) O) :
    ∃ (ϖ : O) (eO : ℕ) (x : Oˣ), Irreducible ϖ ∧ Formalism.ExponentWindows.E.PrimBase (baseIdOf hR).Bs ϖ eO ∧
      ((W.χΓ W.gam : Oˣ) : O) = 1 + ((baseIdOf hR).Bs.ℓ : O) * (x : O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨eO, he, hass⟩ := exists_eO W hϖ (not_isUnit_p W hV)
  obtain ⟨x, hx⟩ := u_eq_of W hV hs
  have hγ : W.gamK = W.gam := W.gamK_eq_one hs (by omega)
  exact ⟨ϖ, eO, x, hϖ, primBase_of hR hγ h3 he hass hcomp, hx⟩

section Complete

variable {R : Type} [CommRing R] (J : Ideal R)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hle : (J • ⊤ : Submodule R (Fin k → R)) ≤ Submodule.pi Set.univ (fun _ => (J : Submodule R R))`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr m _`.

Rewrite using `[Submodule.mem_pi]`. Introduce `j _`. Simplify `J.mul_mem_right (m j) hr` using `[smul_eq_mul]`. Introduce `i`. Conclude with `(Submodule.mem_pi.mp (hle hx)) i (Set.mem_univ i)`.

Introduce `hx`. Rewrite using `[pi_eq_sum_univ x]`. Conclude with `sum_mem fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top`.
-/
theorem mem_smul_top_pi (k : ℕ) (x : Fin k → R) :
    x ∈ (J • ⊤ : Submodule R (Fin k → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    have hle : (J • ⊤ : Submodule R (Fin k → R)) ≤
        Submodule.pi Set.univ (fun _ => (J : Submodule R R)) := by
      rw [Submodule.smul_le]
      intro r hr m _
      rw [Submodule.mem_pi]
      intro j _
      simpa [smul_eq_mul] using J.mul_mem_right (m j) hr
    intro i
    exact (Submodule.mem_pi.mp (hle hx)) i (Set.mem_univ i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact sum_mem fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

/- English proof (translation)
Establish `key : ∀ (m : ℕ) (y : Fin k → R), y ∈ (J ^ m • ⊤ : Submodule R (Fin k → R)) ↔ ∀ i, y i ∈ (J ^ m • ⊤ : Submodule R R)`. Introduce `m y`. Rewrite using `[mem_smul_top_pi]`. Simplify using `only [Ideal.smul_eq_mul, Ideal.mul_top]`. Use `⟨fun f hf => ?_⟩` and prove the remaining obligations.

Establish `hfi : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (J ^ n • ⊤ : Submodule R R)]`. Introduce `i`. Use `IsPrecomplete.prec' (I := J) (fun m => f m i) (fun {m n} hmn => ?_)` and prove the remaining obligations. Establish `h1` using `hf hmn`. Rewrite `h1` using `[SModEq.sub_mem, key]`.

Rewrite using `[SModEq.sub_mem]`. Conclude with `h1 i`. Use `choose L hL using hfi`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, key]`.

Introduce `i`. Establish `h2` using `hL i n`. Rewrite `h2` using `[SModEq.sub_mem]`. Conclude with `h2`.
-/
theorem precomplete_pi [IsPrecomplete J R] (k : ℕ) : IsPrecomplete J (Fin k → R) := by
  have key : ∀ (m : ℕ) (y : Fin k → R), y ∈ (J ^ m • ⊤ : Submodule R (Fin k → R)) ↔
      ∀ i, y i ∈ (J ^ m • ⊤ : Submodule R R) := by
    intro m y
    rw [mem_smul_top_pi]
    simp only [Ideal.smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have hfi : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (J ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (I := J) (fun m => f m i) (fun {m n} hmn => ?_)
    have h1 := hf hmn
    rw [SModEq.sub_mem, key] at h1
    rw [SModEq.sub_mem]
    exact h1 i
  choose L hL using hfi
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  have h2 := hL i n
  rw [SModEq.sub_mem] at h2
  exact h2

/- English proof (translation)
Establish `hmap : ∀ m : ℕ, ∀ y ∈ (J ^ m • ⊤ : Submodule R N), ∃ x ∈ (J ^ m • ⊤ : Submodule R M), f x = y`. Introduce `m y hy`. Establish `hs : (J ^ m • ⊤ : Submodule R N) = (J ^ m • ⊤ : Submodule R M).map f`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]`. Rewrite `hy` using `[hs]`.

Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`. Conclude with `⟨x, hx, rfl⟩`. Establish `hmapsto : ∀ m : ℕ, ∀ x ∈ (J ^ m • ⊤ : Submodule R M), f x ∈ (J ^ m • ⊤ : Submodule R N)`. Introduce `m x hx`. Establish `hle : (J ^ m • ⊤ : Submodule R M).map f ≤ (J ^ m • ⊤ : Submodule R N)`.

Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_le.mpr fun r hr n _ => Submodule.smul_mem_smul hr Submodule.mem_top`. Conclude with `hle (Submodule.mem_map_of_mem hx)`. Use `⟨fun g hg => ?_⟩` and prove the remaining obligations. Establish `hd : ∀ k : ℕ, ∃ d ∈ (J ^ k • ⊤ : Submodule R M), f d = g (k + 1) - g k`.

Introduce `k`. Apply `hmap` to reduce the goal to its premises. Establish `h1` using `hg (Nat.le_succ k)`. Rewrite `h1` using `[SModEq.sub_mem]`. Rewrite using `[← neg_sub]`.

Conclude with `neg_mem h1`. Use `choose d hdJ hdf using hd`. Take `⟨x0, hx0⟩` from `hf (g 0)`. Take `⟨h, hh⟩ : ∃ h : ℕ → M, ∀ n, h n = x0 + ∑ k ∈ Finset.range n, d k` from `⟨_, fun _ => rfl⟩`. Establish `hfh : ∀ n, f (h n) = g n`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [hh, Finset.sum_range_zero, add_zero, hx0]`. Consider the case `succ n ih`. Rewrite using `[hh, Finset.sum_range_succ, ← add_assoc, map_add, ← hh, ih, hdf]`.

Normalize the expressions using the abelian group laws. Establish `hcauchy : ∀ {m n : ℕ}, m ≤ n → h m ≡ h n [SMOD (J ^ m • ⊤ : Submodule R M)]`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, hh, hh, ← Finset.sum_range_add_sum_Ico d hmn]`. Establish `hs : x0 + ∑ k ∈ Finset.range m, d k - (x0 + (∑ k ∈ Finset.range m, d k + ∑ k ∈ Finset.Ico m n, d k)) = -∑ k ∈ Finset.Ico m n, d k` using `by abel`.

Rewrite using `[hs]`. Use `neg_mem (sum_mem fun k hk => ?_)` and prove the remaining obligations. Conclude with `Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1) (hdJ k)`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := J) h hcauchy`. Use `⟨f L, fun n => ?_⟩` and prove the remaining obligations.

Establish `h3` using `hL n`. Rewrite `h3`, the goal using `[SModEq.sub_mem]`. Rewrite using `[← hfh n, ← map_sub]`. Conclude with `hmapsto n _ h3`.
-/
theorem precomplete_of_surj {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) [IsPrecomplete J M] : IsPrecomplete J N := by
  have hmap : ∀ m : ℕ, ∀ y ∈ (J ^ m • ⊤ : Submodule R N),
      ∃ x ∈ (J ^ m • ⊤ : Submodule R M), f x = y := by
    intro m y hy
    have hs : (J ^ m • ⊤ : Submodule R N) = (J ^ m • ⊤ : Submodule R M).map f := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    rw [hs] at hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨x, hx, rfl⟩
  have hmapsto : ∀ m : ℕ, ∀ x ∈ (J ^ m • ⊤ : Submodule R M), f x ∈ (J ^ m • ⊤ : Submodule R N) := by
    intro m x hx
    have hle : (J ^ m • ⊤ : Submodule R M).map f ≤ (J ^ m • ⊤ : Submodule R N) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_le.mpr fun r hr n _ => Submodule.smul_mem_smul hr Submodule.mem_top
    exact hle (Submodule.mem_map_of_mem hx)
  refine ⟨fun g hg => ?_⟩
  have hd : ∀ k : ℕ, ∃ d ∈ (J ^ k • ⊤ : Submodule R M), f d = g (k + 1) - g k := by
    intro k
    apply hmap
    have h1 := hg (Nat.le_succ k)
    rw [SModEq.sub_mem] at h1
    rw [← neg_sub]
    exact neg_mem h1
  choose d hdJ hdf using hd
  obtain ⟨x0, hx0⟩ := hf (g 0)
  obtain ⟨h, hh⟩ : ∃ h : ℕ → M, ∀ n, h n = x0 + ∑ k ∈ Finset.range n, d k := ⟨_, fun _ => rfl⟩
  have hfh : ∀ n, f (h n) = g n := by
    intro n
    induction n with
    | zero => rw [hh, Finset.sum_range_zero, add_zero, hx0]
    | succ n ih =>
      rw [hh, Finset.sum_range_succ, ← add_assoc, map_add, ← hh, ih, hdf]
      abel
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → h m ≡ h n [SMOD (J ^ m • ⊤ : Submodule R M)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hh, hh, ← Finset.sum_range_add_sum_Ico d hmn]
    have hs : x0 + ∑ k ∈ Finset.range m, d k -
        (x0 + (∑ k ∈ Finset.range m, d k + ∑ k ∈ Finset.Ico m n, d k)) =
        -∑ k ∈ Finset.Ico m n, d k := by abel
    rw [hs]
    refine neg_mem (sum_mem fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1) (hdJ k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) h hcauchy
  refine ⟨f L, fun n => ?_⟩
  have h3 := hL n
  rw [SModEq.sub_mem] at h3 ⊢
  rw [← hfh n, ← map_sub]
  exact hmapsto n _ h3

end Complete

section Rec

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hfd : FiniteDimensional ℚ_[l] ↥LL.1` using `LL.2`. Establish `hfin : Module.Finite ℤ_[l] ↥(OL LL)` using `IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)`. Take `⟨k, f, hf⟩` from `Module.Finite.exists_fin' ℤ_[l] ↥(OL LL)`. Establish `h1 : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[l]) (Fin k → ℤ_[l])` using `precomplete_pi _ k`. Establish `h2 : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL)` using `precomplete_of_surj _ f hf`.

Establish `h3 : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL)` using `{ }`. Establish `h4` using `(IsAdicComplete.map_algebraMap_iff (S := ↥(OL LL)) (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL)).2 h3`. Rewrite `h4` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]`. Conclude with `h4`.
-/
theorem complete_OL (LL : FinExt l) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hfin : Module.Finite ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' ℤ_[l] ↥(OL LL)
  have h1 : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[l]) (Fin k → ℤ_[l]) := precomplete_pi _ k
  have h2 : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL) := precomplete_of_surj _ f hf
  have h3 : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL) := { }
  have h4 := (IsAdicComplete.map_algebraMap_iff (S := ↥(OL LL)) (IsLocalRing.maximalIdeal ℤ_[l]) ↥(OL LL)).2 h3
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at h4
  exact h4

/- English proof (translation)
Unfold `ValRing`. Conclude with `⟨Subtype.val_injective, fun x hx => ⟨⟨x, (P.v_O LL x).mp hx⟩, rfl⟩, fun o => (P.v_O LL _).mpr o.2⟩`.
-/
theorem valRing_rec (P : LocPrime l) (LL : FinExt l) : ValRing (LL := ↥LL.1) ↥(OL LL) (P.v LL) := by
  unfold ValRing
  exact ⟨Subtype.val_injective, fun x hx => ⟨⟨x, (P.v_O LL x).mp hx⟩, rfl⟩,
    fun o => (P.v_O LL _).mpr o.2⟩

end Rec

end Formalism.MainNotions.WachCoordinates.Br
