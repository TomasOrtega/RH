import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.PullHermitian in

/- English proof (translation)
Introduce `A _ L₀ g u L hL ht0 U H χ' hU hF hH0 m l hm`. Use `set φ := (lift (𝟙 A) (1 : A ⟶ A)).left with hφ`. Take `⟨t, ht⟩` from `ht0`. Establish `e0 : u.ex 0 = 1`. Establish `h` using `u.ex_add 0 0`.

Simplify using `using h`. Establish `comp1 : ∀ {X : Over (Sp ℂ)} (f : X ⟶ A), f ≫ (1 : A ⟶ A) = 1` using `fun f => by`. Rewrite using `[Hom.one_def, Hom.one_def]`. Simplify using the standard rewrite rules. Establish `hx : ∀ z, (U.ex (Fin.append z 0)).left = (u.ex z).left ≫ φ` using `fun z => by`.

Rewrite using `[hU, e0, hφ, ← Over.comp_left, comp_lift, Category.comp_id, comp1]`. Establish `hmem : ∀ l' : Fin g → ℂ, Fin.append l' 0 ∈ U.Λ ↔ l' ∈ u.Λ`. Introduce `l'`. Rewrite using `[← U.ker, ← u.ker, hU, e0]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `congrArg (· ≫ fst A A) h` as an intermediate fact. Simplify using `using this`. Introduce `h`. Rewrite using `[h]`.

Apply the tactic sequence `first | simp | (ext <;> simp) | rfl`. Establish `hper : ∀ (l' : u.Λ) z, u.ex (z + l') = u.ex z` using `fun l' z => by`. Rewrite using `[u.ex_add, (u.ker l').2 l'.2, _root_.mul_one]`. Establish `happ : ∀ z w : Fin g → ℂ, Fin.append z 0 + Fin.append w 0 = Fin.append (z + w) (0 : Fin g → ℂ)`. Introduce `z w`.

Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.append_left, Pi.add_apply]`. Simplify using `only [Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero]`. Establish `hapd : Differentiable ℂ (fun z : Fin g → ℂ => Fin.append z (0 : Fin g → ℂ))`.

Use `differentiable_pi.2 fun i => ?_` and prove the remaining obligations. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations. Simplify `differentiable_apply j` using `only [Fin.append_left]`. Simplify `differentiable_const (0 : ℂ)` using `only [Fin.append_right, Pi.zero_apply]`. Use `set V : L.ι → Set (Fin g → ℂ) := fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull φ).U (fun _ => p)} with hV`.

Establish `hVsub' : ∀ p z, z ∈ V p → ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ L.U p` using `fun p z hz q hq => Set.mem_iInter.1 (hz hq) PUnit.unit`. Establish `hVsub : ∀ p z, z ∈ V p → ⊤ ≤ (U.ex (Fin.append z 0)).left ⁻¹ᵁ L.U p` using `fun p z hz => by`. Rewrite using `[hx]`. Conclude with `hVsub' p z hz`. Establish `hVof : ∀ p z, ⊤ ≤ (U.ex (Fin.append z 0)).left ⁻¹ᵁ L.U p → z ∈ V p` using `fun p z h => wchart_of (u.ex z).left L φ p (hx z ▸ h)`.

Take `⟨r, hr, hrφ⟩` from `exists_glue V (fun p => (u.hol _ 0).1) (fun z => by`. Take `⟨p, hp⟩` from `exists_chart (U.ex (Fin.append z 0)).left hL`. Conclude with `⟨p, hVof p z hp⟩)`. Use the proof step `(fun p z => valAt' (u.ex z).left ((L.pull φ).U (fun _ => p)) (t.s (fun _ => p)).val / U.fr p (Fin.append z 0))`. Use the proof step `(fun p => by`.

Establish `d1` using `(u.hol ((L.pull φ).U (fun _ => p)) (t.s (fun _ => p)).val).2`. Establish `d2 : DifferentiableOn ℂ (fun z => U.fr p (Fin.append z 0)) (V p)` using `(U.fr_hol p).comp (s := V p) hapd.differentiableOn fun z hz => hVsub p z hz`. Simplify using `only [div_eq_mul_inv]`. Conclude with `d1.mul (d2.inv fun z hz => U.fr_ne p _ (hVsub p z hz)))`. Use the proof step `(fun p q z hp hq => by`.

Establish `hpq` using `inf_of (u.ex z).left hp hq`. Establish `h1` using `ht (fun _ => p) (fun _ => q)`. Establish `h2` using `congrArg (unitVal (u.ex z).left hpq) h1`. Rewrite `h2` using `[map_mul, unitVal_res (u.ex z).left _ hpq hp, unitVal_res (u.ex z).left _ hpq hq]`. Establish `h3` using `unitVal_linComb (u.ex z).left L φ 1 p q hpq (inf_of _ (hVsub' p z hp) (hVsub' q z hq))`.

Establish `h4` using `U.fr_compat p q (Fin.append z 0) (inf_of _ (hVsub p z hp) (hVsub q z hq))`. Rewrite `h4` using `[hx]`. Rewrite using `[valAt'_eq_unitVal _ hp, valAt'_eq_unitVal _ hq, h4, valAt'_eq_unitVal _ (inf_of _ (hVsub' p z hp) (hVsub' q z hq)), h2, h3]`. Establish `h5` using `U.fr_ne q _ (hVsub q z hq)`. Simplify using `only [Units.val_mul, zpow_one]`.

Use the proof step `field_simp)`. Use `haveI := u.discrete`. Establish `key` using `appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0 (fun l' => χ' ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩) r Matrix.isHermitian_zero (fun l' => hF.2.1 _) hr (fun z => by`. Take `⟨p, hp⟩` from `exists_chart (U.ex (Fin.append z 0)).left hL`. Establish `hp'` using `hVof p z hp`.

Rewrite using `[hrφ p z hp', valAt'_eq_unitVal _ hp']`. Conclude with `div_ne_zero (Units.ne_zero _) (U.fr_ne p _ hp))`. Use the proof step `(fun l' z => by`. Take `⟨p, hp⟩` from `exists_chart (U.ex (Fin.append z 0)).left hL`. Establish `hz` using `hVof p z hp`.

Establish `hz' : z + l' ∈ V p` using `by show ⊤ ≤ (u.ex (z + l')).left ⁻¹ᵁ _`. Rewrite using `[hper]`. Conclude with `hz`. Rewrite using `[hrφ p _ hz', hrφ p z hz, hper]`. Establish `hf` using `hF.2.2 ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩ p (Fin.append z 0) hp`.

Establish `e1 : Fin.append z 0 ⬝ᵥ H.mulVec (star (Fin.append (l' : Fin g → ℂ) 0)) = 0` using `hH0 z l'`. Establish `e2 : Fin.append (l' : Fin g → ℂ) 0 ⬝ᵥ H.mulVec (star (Fin.append (l' : Fin g → ℂ) 0)) = 0` using `hH0 l' l'`. Simplify using `only [e1, e2, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one, happ] at hf`. Establish `hc : χ' ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩ ≠ 0` using `norm_ne_zero_iff.1 (by rw [hF.2.1]; exact one_ne_zero)`. Establish `h6` using `U.fr_ne p _ (hVsub p _ hz')`.

Simplify using `only [hermForm, Matrix.zero_mulVec, dotProduct_zero, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one]`. Rewrite using `[hf]`. Use the proof step `field_simp)`. Establish `hm' : m = ⟨Fin.append l 0, hm ▸ m.2⟩` using `Subtype.ext hm`. Rewrite using `[hm']`.

Conclude with `key.2.1 ⟨l, (hmem l).1 (hm ▸ m.2)⟩`.
-/
theorem GlobalTheory.TorusRM.char_axis_eq_one_of_herm_axis_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left), L.IsLB → HasGen (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∀ (U : HolUnif (A ⊗ A) L (g + g)) (H : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) (χ' : U.Λ → ℂ),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → GlobalTheory.TorusRM.IsFactorAH U H χ' →
    (∀ z w : Fin g → ℂ, hermForm H (Fin.append z 0) (Fin.append w 0) = 0) →
    ∀ (m : U.Λ) (l : Fin g → ℂ), (m : Fin (g + g) → ℂ) = Fin.append l 0 → χ' m = 1 := by
  intro A _ L₀ g u L hL ht0 U H χ' hU hF hH0 m l hm
  set φ := (lift (𝟙 A) (1 : A ⟶ A)).left with hφ
  obtain ⟨t, ht⟩ := ht0
  have e0 : u.ex 0 = 1 := by
    have h := u.ex_add 0 0
    simpa using h
  have comp1 : ∀ {X : Over (Sp ℂ)} (f : X ⟶ A), f ≫ (1 : A ⟶ A) = 1 := fun f => by
    rw [Hom.one_def, Hom.one_def]; simp
  have hx : ∀ z, (U.ex (Fin.append z 0)).left = (u.ex z).left ≫ φ := fun z => by
    rw [hU, e0, hφ, ← Over.comp_left, comp_lift, Category.comp_id, comp1]
  have hmem : ∀ l' : Fin g → ℂ, Fin.append l' 0 ∈ U.Λ ↔ l' ∈ u.Λ := by
    intro l'
    rw [← U.ker, ← u.ker, hU, e0]
    constructor
    · intro h
      have := congrArg (· ≫ fst A A) h
      simpa using this
    · intro h
      rw [h]
      first | simp | (ext <;> simp) | rfl
  have hper : ∀ (l' : u.Λ) z, u.ex (z + l') = u.ex z := fun l' z => by
    rw [u.ex_add, (u.ker l').2 l'.2, _root_.mul_one]
  have happ : ∀ z w : Fin g → ℂ, Fin.append z 0 + Fin.append w 0 = Fin.append (z + w) (0 : Fin g → ℂ) := by
    intro z w
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.add_apply]
    · simp only [Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero]
  have hapd : Differentiable ℂ (fun z : Fin g → ℂ => Fin.append z (0 : Fin g → ℂ)) := by
    refine differentiable_pi.2 fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using differentiable_apply j
    · simpa only [Fin.append_right, Pi.zero_apply] using differentiable_const (0 : ℂ)
  set V : L.ι → Set (Fin g → ℂ) := fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull φ).U (fun _ => p)} with hV
  have hVsub' : ∀ p z, z ∈ V p → ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ L.U p := fun p z hz q hq =>
    Set.mem_iInter.1 (hz hq) PUnit.unit
  have hVsub : ∀ p z, z ∈ V p → ⊤ ≤ (U.ex (Fin.append z 0)).left ⁻¹ᵁ L.U p := fun p z hz => by
    rw [hx]; exact hVsub' p z hz
  have hVof : ∀ p z, ⊤ ≤ (U.ex (Fin.append z 0)).left ⁻¹ᵁ L.U p → z ∈ V p := fun p z h =>
    wchart_of (u.ex z).left L φ p (hx z ▸ h)
  obtain ⟨r, hr, hrφ⟩ := exists_glue V
    (fun p => (u.hol _ 0).1)
    (fun z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      exact ⟨p, hVof p z hp⟩)
    (fun p z => valAt' (u.ex z).left ((L.pull φ).U (fun _ => p)) (t.s (fun _ => p)).val /
      U.fr p (Fin.append z 0))
    (fun p => by
      have d1 := (u.hol ((L.pull φ).U (fun _ => p)) (t.s (fun _ => p)).val).2
      have d2 : DifferentiableOn ℂ (fun z => U.fr p (Fin.append z 0)) (V p) := (U.fr_hol p).comp (s := V p) hapd.differentiableOn fun z hz => hVsub p z hz
      simp only [div_eq_mul_inv]
      exact d1.mul (d2.inv fun z hz => U.fr_ne p _ (hVsub p z hz)))
    (fun p q z hp hq => by
      have hpq := inf_of (u.ex z).left hp hq
      have h1 := ht (fun _ => p) (fun _ => q)
      have h2 := congrArg (unitVal (u.ex z).left hpq) h1
      rw [map_mul, unitVal_res (u.ex z).left _ hpq hp, unitVal_res (u.ex z).left _ hpq hq] at h2
      have h3 := unitVal_linComb (u.ex z).left L φ 1 p q hpq (inf_of _ (hVsub' p z hp) (hVsub' q z hq))
      have h4 := U.fr_compat p q (Fin.append z 0) (inf_of _ (hVsub p z hp) (hVsub q z hq))
      rw [hx] at h4
      rw [valAt'_eq_unitVal _ hp, valAt'_eq_unitVal _ hq, h4,
        valAt'_eq_unitVal _ (inf_of _ (hVsub' p z hp) (hVsub' q z hq)), h2, h3]
      have h5 := U.fr_ne q _ (hVsub q z hq)
      simp only [Units.val_mul, zpow_one]
      field_simp)
  haveI := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0
    (fun l' => χ' ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩) r Matrix.isHermitian_zero
    (fun l' => hF.2.1 _) hr
    (fun z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      have hp' := hVof p z hp
      rw [hrφ p z hp', valAt'_eq_unitVal _ hp']
      exact div_ne_zero (Units.ne_zero _) (U.fr_ne p _ hp))
    (fun l' z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      have hz := hVof p z hp
      have hz' : z + l' ∈ V p := by
        show ⊤ ≤ (u.ex (z + l')).left ⁻¹ᵁ _
        rw [hper]; exact hz
      rw [hrφ p _ hz', hrφ p z hz, hper]
      have hf := hF.2.2 ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩ p (Fin.append z 0) hp
      have e1 : Fin.append z 0 ⬝ᵥ H.mulVec (star (Fin.append (l' : Fin g → ℂ) 0)) = 0 := hH0 z l'
      have e2 : Fin.append (l' : Fin g → ℂ) 0 ⬝ᵥ H.mulVec (star (Fin.append (l' : Fin g → ℂ) 0)) = 0 :=
        hH0 l' l'
      simp only [e1, e2, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one, happ] at hf
      have hc : χ' ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩ ≠ 0 :=
        norm_ne_zero_iff.1 (by rw [hF.2.1]; exact one_ne_zero)
      have h6 := U.fr_ne p _ (hVsub p _ hz')
      simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero, mul_zero, add_zero, Complex.exp_zero,
        _root_.mul_one]
      rw [hf]
      field_simp)
  have hm' : m = ⟨Fin.append l 0, hm ▸ m.2⟩ := Subtype.ext hm
  rw [hm']
  exact key.2.1 ⟨l, (hmem l).1 (hm ▸ m.2)⟩
