import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproximationModConductorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleClearDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMultipleMemSublatticeStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjUnifLattice

/- English proof (translation)
Introduce `_ _ _ K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hio c y hc 𝔠 T X' p hp u' H`. Establish `hex0 : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {m : ℕ} (u : HolUnif A L m), u.ex 0 = 1`. Introduce `A _ L m u`. Establish `h` using `u.ex_add 0 0`. Rewrite `h` using `[add_zero]`.

Simplify using `using h`. Establish `hpb : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ X'.A, a.left ≫ p = b.left ≫ p → a = b`. Introduce `a b h`. Conclude with `Over.OverMorphism.ext (hp.grp.1.hom_ext h (by rw [Over.w a, Over.w b]))`. Establish `hepi : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ T.X.A, spMap (g : ℂ →+* ℂ) ≫ a.left = spMap (g : ℂ →+* ℂ) ≫ b.left → a = b`.

Introduce `a b h`. Use `haveI : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) := (RingEquiv.toCommRingCatIso g).isIso_hom`. Use `haveI : IsIso (spMap (g : ℂ →+* ℂ)) := by unfold spMap; infer_instance`. Conclude with `Over.OverMorphism.ext ((cancel_epi _).1 h)`. Establish `H0 : (u'.ex 0).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex 0).left`.

Use `H 0 0 (by simp)` as an intermediate fact. Simplify using `only [map_zero] at this`. Conclude with `this`. Establish `hmemL : ∀ x' : E, x' ∈ lattice c (y * (upIdele K E t)⁻¹) ↔ ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) 0) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c`. Introduce `x'`.

Establish `e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹` using `by rw [mul_inv_rev, inv_inv]`. Use `show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c ↔ _`. Rewrite using `[e, Units.val_mul, map_zero, sub_zero]`. Apply the tactic sequence `constructor <;> intro h <;> convert h using 1 <;> ring`. Establish `hdef : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) = fun j ↦ g (φ (T.U.e j) x)`.

Introduce `x`. Use function extensionality and compare the values at `j`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]`. Establish `hdef0 : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (T.U.e j)) = fun j ↦ φ (T.U.e j) x`. Introduce `x`.

Use function extensionality and compare the values at `j`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]`. Establish `hsup : ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹), (fun j ↦ g (φ (T.U.e j) x')) ∈ u'.Λ`. Introduce `x' hx'`. Establish `h1` using `H 0 x' ((hmemL x').1 hx')`.

Simplify using `only [map_zero] at h1`. Rewrite using `[← u'.ker, ← hex0 u']`. Use `hpb _ _ ?_` and prove the remaining obligations. Rewrite using `[H0]`. Conclude with `h1`.

Establish `hsubL : ∀ y₁ : (Af E)ˣ, ∃ S : AddSubgroup E, (S : Set E) = lattice c y₁`. Introduce `y₁`. Use `⟨{ carrier := lattice c y₁, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, rfl⟩` and prove the remaining obligations. Introduce `a b ha hb show _ ∈ hatO c`. Rewrite using `[map_add, add_mul]`.

Conclude with `add_mem ha hb`. Use `show _ ∈ hatO c`. Rewrite using `[map_zero, zero_mul]`. Conclude with `zero_mem _`. Introduce `a ha show _ ∈ hatO c`.

Rewrite using `[map_neg, neg_mul]`. Conclude with `neg_mem ha`. Take `⟨SL, hSL⟩` from `hsubL y`. Take `⟨SL', hSL'⟩` from `hsubL (y * (upIdele K E t)⁻¹)`. Establish `hpos : 0 < Module.finrank ℚ (FR E)` using `Module.finrank_pos`.

Set `j₀ : Fin (Module.finrank ℚ (FR E))` to `⟨0, hpos⟩`. Set `Φ : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ)` to `{ toFun := fun x j ↦ φ (T.U.e j) x map_add' := by intros; funext j; simp map_smul' := by intros; funext j; simp }`. Set `Φ' : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ)` to `{ toFun := fun x j ↦ g (φ (T.U.e j) x) map_add' := by intros; funext j; simp map_smul' := by intros; funext j; simp }`. Establish `hΦinj : Function.Injective Φ` using `fun a b h ↦ (φ (T.U.e j₀)).injective (congrFun h j₀)`. Establish `hΦ'inj : Function.Injective Φ'` using `fun a b h ↦ (φ (T.U.e j₀)).injective (g.injective (congrFun h j₀))`.

Establish `hΛ : T.U.u.Λ = SL.toIntSubmodule.map Φ`. Use extensionality with `w`. Rewrite using `[T.U.lat, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Use `show x ∈ (SL : Set E)`. Rewrite using `[hSL]`. Conclude with `hx`. Rewrite using `[hdef0]`.

Both sides reduce to the same expression. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hSL]`. Conclude with `hx`.

Rewrite using `[hdef0]`. Both sides reduce to the same expression. Set `M : Submodule ℤ (Fin (Module.finrank ℚ (FR E)) → ℂ)` to `SL'.toIntSubmodule.map Φ'`. Establish `hMle : M ≤ u'.Λ`. Introduce and unpack `w ⟨x', hx', rfl⟩`.

Conclude with `hsup x' (by rw [← hSL']; exact hx')`. Take `⟨m, hm0, hm⟩` from `GlobalTheory.T.finite_adele_clear_denominator E c hc (upIdele K E t : Af E)`. Establish `hrank : Module.rank ℤ T.U.u.Λ ≤ Module.rank ℤ M`. Rewrite using `[hΛ, ← (Submodule.equivMapOfInjective _ hΦinj _).rank_eq, ← (Submodule.equivMapOfInjective _ hΦ'inj _).rank_eq]`. Set `mulm : E →ₗ[ℤ] E` to `(AddMonoidHom.mulLeft m).toIntLinearMap`.

Establish `hmulm : Function.Injective mulm` using `mul_right_injective₀ hm0`. Combine the equalities or inequalities in the displayed calculation. Use `Submodule.rank_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : x ∈ lattice c y` using `by rw [← hSL]; exact hx`.

Use `show m * x ∈ (SL' : Set E)`. Rewrite using `[hSL']`. Establish `e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹` using `by rw [mul_inv_rev, inv_inv]`. Use `show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c`. Rewrite using `[e, Units.val_mul, map_mul]`.

Use `mul_mem hm hx'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce `w`. Prove the components needed by the constructor for the conclusion.

Introduce `hw`. Take `⟨k, hk, hkw⟩` from `GlobalTheory.T.lattice_multiple_mem_sublattice _ u'.Λ T.U.u.Λ M u'.discrete T.U.u.discrete u'.full T.U.u.full hMle hrank w hw`. Take `⟨x'', hx'', hx''e⟩` from `Submodule.mem_map.1 hkw`. Establish `hk' : (k : E) ≠ 0` using `Int.cast_ne_zero.2 hk`. Establish `hw' : w = Φ' (x'' / k)`.

Apply `smul_right_injective (Fin (Module.finrank ℚ (FR E)) → ℂ) hk` to reduce the goal to its premises. Use `show k • w = k • Φ' (x'' / k)`. Rewrite using `[← map_zsmul, ← hx''e]`. Use `congr 1`. Rewrite using `[zsmul_eq_mul, mul_div_cancel₀ _ hk']`.

Use `set x' := x'' / k`. Take `⟨x, hx⟩` from `GlobalTheory.T.finite_adele_approximation_mod_conductor E c hc y ((upIdele K E t : Af E) * algebraMap E (Af E) x')`. Establish `h1` using `H x x' hx`. Establish `hw1 : u'.ex (fun j ↦ g (φ (T.U.e j) x')) = 1` using `(u'.ker _).2 (by rw [hw'] at hw; exact hw)`. Rewrite `h1` using `[hw1, ← hex0 u', H0]`.

Establish `h2` using `hepi _ _ h1`. Establish `h3 : (fun j ↦ φ (T.U.e j) x) ∈ T.U.u.Λ` using `(T.U.u.ker _).1 (by rw [← h2, hex0])`. Rewrite `h3` using `[T.U.lat]`. Take `⟨x₀, hx₀, he⟩` from `h3`. Rewrite `he` using `[hdef0]`.

Establish `hxx : x = x₀` using `(φ (T.U.e j₀)).injective (congrFun he j₀)`. Substitute `hxx` using the available equality. Use `⟨x', ?_, by rw [hdef]; exact hw'⟩` and prove the remaining obligations. Rewrite using `[hmemL, map_zero, sub_zero]`. Use `add_mem hx hx₀` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨x', hx', rfl⟩`. Rewrite using `[hdef]`. Conclude with `hsup x' hx'`.
-/
theorem lattice_of_conj_unif : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) → (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) := by
  intro _ _ _ K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hio c y hc 𝔠 T X' p hp u' H

  have hex0 : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {m : ℕ} (u : HolUnif A L m), u.ex 0 = 1 := by
    intro A _ L m u
    have h := u.ex_add 0 0
    rw [add_zero] at h
    simpa using h

  have hpb : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ X'.A, a.left ≫ p = b.left ≫ p → a = b := by
    intro a b h
    exact Over.OverMorphism.ext (hp.grp.1.hom_ext h (by rw [Over.w a, Over.w b]))

  have hepi : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ T.X.A, spMap (g : ℂ →+* ℂ) ≫ a.left = spMap (g : ℂ →+* ℂ) ≫ b.left → a = b := by
    intro a b h
    haveI : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) := (RingEquiv.toCommRingCatIso g).isIso_hom
    haveI : IsIso (spMap (g : ℂ →+* ℂ)) := by unfold spMap; infer_instance
    exact Over.OverMorphism.ext ((cancel_epi _).1 h)
  have H0 : (u'.ex 0).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex 0).left := by
    have := H 0 0 (by simp)
    simp only [map_zero] at this
    exact this

  have hmemL : ∀ x' : E, x' ∈ lattice c (y * (upIdele K E t)⁻¹) ↔
      ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) 0) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro x'
    have e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹ := by rw [mul_inv_rev, inv_inv]
    show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c ↔ _
    rw [e, Units.val_mul, map_zero, sub_zero]
    constructor <;> intro h <;> convert h using 1 <;> ring
  have hdef : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) =
      fun j ↦ g (φ (T.U.e j) x) := by
    intro x; funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hdef0 : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (T.U.e j)) = fun j ↦ φ (T.U.e j) x := by
    intro x; funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]

  have hsup : ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹), (fun j ↦ g (φ (T.U.e j) x')) ∈ u'.Λ := by
    intro x' hx'
    have h1 := H 0 x' ((hmemL x').1 hx')
    simp only [map_zero] at h1
    rw [← u'.ker, ← hex0 u']
    refine hpb _ _ ?_
    rw [H0]
    exact h1

  have hsubL : ∀ y₁ : (Af E)ˣ, ∃ S : AddSubgroup E, (S : Set E) = lattice c y₁ := by
    intro y₁
    refine ⟨{ carrier := lattice c y₁, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, rfl⟩
    · intro a b ha hb
      show _ ∈ hatO c
      rw [map_add, add_mul]
      exact add_mem ha hb
    · show _ ∈ hatO c
      rw [map_zero, zero_mul]
      exact zero_mem _
    · intro a ha
      show _ ∈ hatO c
      rw [map_neg, neg_mul]
      exact neg_mem ha
  obtain ⟨SL, hSL⟩ := hsubL y
  obtain ⟨SL', hSL'⟩ := hsubL (y * (upIdele K E t)⁻¹)
  have hpos : 0 < Module.finrank ℚ (FR E) := Module.finrank_pos
  let j₀ : Fin (Module.finrank ℚ (FR E)) := ⟨0, hpos⟩
  let Φ : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j ↦ φ (T.U.e j) x
      map_add' := by intros; funext j; simp
      map_smul' := by intros; funext j; simp }
  let Φ' : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j ↦ g (φ (T.U.e j) x)
      map_add' := by intros; funext j; simp
      map_smul' := by intros; funext j; simp }
  have hΦinj : Function.Injective Φ := fun a b h ↦ (φ (T.U.e j₀)).injective (congrFun h j₀)
  have hΦ'inj : Function.Injective Φ' := fun a b h ↦ (φ (T.U.e j₀)).injective (g.injective (congrFun h j₀))
  have hΛ : T.U.u.Λ = SL.toIntSubmodule.map Φ := by
    ext w
    rw [T.U.lat, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · show x ∈ (SL : Set E)
        rw [hSL]; exact hx
      · rw [hdef0]; rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · rw [← hSL]; exact hx
      · rw [hdef0]; rfl
  let M : Submodule ℤ (Fin (Module.finrank ℚ (FR E)) → ℂ) := SL'.toIntSubmodule.map Φ'
  have hMle : M ≤ u'.Λ := by
    rintro w ⟨x', hx', rfl⟩
    exact hsup x' (by rw [← hSL']; exact hx')
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.T.finite_adele_clear_denominator E c hc (upIdele K E t : Af E)
  have hrank : Module.rank ℤ T.U.u.Λ ≤ Module.rank ℤ M := by
    rw [hΛ, ← (Submodule.equivMapOfInjective _ hΦinj _).rank_eq,
      ← (Submodule.equivMapOfInjective _ hΦ'inj _).rank_eq]
    let mulm : E →ₗ[ℤ] E := (AddMonoidHom.mulLeft m).toIntLinearMap
    have hmulm : Function.Injective mulm := mul_right_injective₀ hm0
    calc Module.rank ℤ SL.toIntSubmodule = Module.rank ℤ (SL.toIntSubmodule.map mulm) :=
          (Submodule.equivMapOfInjective _ hmulm _).rank_eq
      _ ≤ Module.rank ℤ SL'.toIntSubmodule := by
          refine Submodule.rank_mono ?_
          rintro _ ⟨x, hx, rfl⟩
          have hx' : x ∈ lattice c y := by rw [← hSL]; exact hx
          show m * x ∈ (SL' : Set E)
          rw [hSL']
          have e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹ := by rw [mul_inv_rev, inv_inv]
          show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c
          rw [e, Units.val_mul, map_mul]
          have := mul_mem hm hx'
          convert this using 1
          ring
  intro w
  constructor
  · intro hw
    obtain ⟨k, hk, hkw⟩ := GlobalTheory.T.lattice_multiple_mem_sublattice _ u'.Λ T.U.u.Λ M u'.discrete T.U.u.discrete u'.full T.U.u.full hMle hrank w hw
    obtain ⟨x'', hx'', hx''e⟩ := Submodule.mem_map.1 hkw
    have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
    have hw' : w = Φ' (x'' / k) := by
      apply smul_right_injective (Fin (Module.finrank ℚ (FR E)) → ℂ) hk
      show k • w = k • Φ' (x'' / k)
      rw [← map_zsmul, ← hx''e]
      congr 1
      rw [zsmul_eq_mul, mul_div_cancel₀ _ hk']
    set x' := x'' / k
    obtain ⟨x, hx⟩ := GlobalTheory.T.finite_adele_approximation_mod_conductor E c hc y ((upIdele K E t : Af E) * algebraMap E (Af E) x')
    have h1 := H x x' hx
    have hw1 : u'.ex (fun j ↦ g (φ (T.U.e j) x')) = 1 := (u'.ker _).2 (by rw [hw'] at hw; exact hw)
    rw [hw1, ← hex0 u', H0] at h1
    have h2 := hepi _ _ h1
    have h3 : (fun j ↦ φ (T.U.e j) x) ∈ T.U.u.Λ := (T.U.u.ker _).1 (by rw [← h2, hex0])
    rw [T.U.lat] at h3
    obtain ⟨x₀, hx₀, he⟩ := h3
    rw [hdef0] at he
    have hxx : x = x₀ := (φ (T.U.e j₀)).injective (congrFun he j₀)
    subst hxx
    refine ⟨x', ?_, by rw [hdef]; exact hw'⟩
    rw [hmemL, map_zero, sub_zero]
    have := add_mem hx hx₀
    convert this using 1
    ring
  · rintro ⟨x', hx', rfl⟩
    rw [hdef]
    exact hsup x' hx'

end GlobalTheory.ConjUnifLattice
