import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdFMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceUnitsBasisOfNbhdsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitsFiniteCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFiniteIdeleFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalIdeleIntegralIffUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNormsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.LKTorus

/- English proof (translation)
Set `pick : ι → G` to `fun i => if h : ∃ y ∈ X, y ∈ T ∧ lab y i then h.choose else 1`. Establish `hpick : ∀ i, (∃ y ∈ X, y ∈ T ∧ lab y i) → pick i ∈ X ∧ pick i ∈ T ∧ lab (pick i) i`. Introduce `i h`. Simplify using `only [pick, dif_pos h]`. Conclude with `h.choose_spec`.

Use `⟨S.image pick, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hs`. Distinguish the cases in `h : ∃ y ∈ X, y ∈ T ∧ lab y i`. Conclude with `(hpick i h).2.1`.

Simplify using `only [pick, dif_neg h]`. Conclude with `one_mem T`. Introduce `x hx hxT`. Take `⟨i, hi, hl⟩` from `hlab x hx hxT`. Take `⟨h1, h2, h3⟩` from `hpick i ⟨x, hx, hxT, hl⟩`.

Conclude with `⟨pick i, Finset.mem_image_of_mem _ hi, hB x (pick i) i hx h1 hxT h2 hl h3, mul_mem (inv_mem h2) hxT⟩`.
-/
theorem cover_of_label {G : Type} [Group G] {ι : Type} (S : Finset ι) (T B : Subgroup G) (X : Set G)
    (lab : G → ι → Prop) (hlab : ∀ x ∈ X, x ∈ T → ∃ i ∈ S, lab x i)
    (hB : ∀ x y i, x ∈ X → y ∈ X → x ∈ T → y ∈ T → lab x i → lab y i → y⁻¹ * x ∈ B) :
    ∃ S' : Finset G, (∀ s ∈ S', s ∈ T) ∧ ∀ x ∈ X, x ∈ T → ∃ s ∈ S', s⁻¹ * x ∈ B ∧ s⁻¹ * x ∈ T := by
  classical
  let pick : ι → G := fun i => if h : ∃ y ∈ X, y ∈ T ∧ lab y i then h.choose else 1
  have hpick : ∀ i, (∃ y ∈ X, y ∈ T ∧ lab y i) → pick i ∈ X ∧ pick i ∈ T ∧ lab (pick i) i := by
    intro i h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  refine ⟨S.image pick, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    by_cases h : ∃ y ∈ X, y ∈ T ∧ lab y i
    · exact (hpick i h).2.1
    · simp only [pick, dif_neg h]; exact one_mem T
  · intro x hx hxT
    obtain ⟨i, hi, hl⟩ := hlab x hx hxT
    obtain ⟨h1, h2, h3⟩ := hpick i ⟨x, hx, hxT, hl⟩
    exact ⟨pick i, Finset.mem_image_of_mem _ hi, hB x (pick i) i hx h1 hxT h2 hl h3,
      mul_mem (inv_mem h2) hxT⟩

/- English proof (translation)
Use `letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra`. Use `letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)`. Introduce `U hU`. Take `⟨V, hV, hVU⟩` from `isOpen_induced_iff.1 hU`. Establish `h1V : (1 : (AfE ℚ L)ˣ) ∈ V`.

Establish `h : (1 : simTA L c) ∈ (U : Set (simTA L c))` using `one_mem U`. Rewrite `h` using `[← hVU]`. Conclude with `h`. Take `⟨N, hN, hNV⟩` from `GlobalTheory.T.congruence_units_basis_of_nbhds L V hV h1V`. Establish `hcongU : ∀ (x : (AfE ℚ L)ˣ) (hx : x ∈ simTA L c), x ∈ congN ℚ L N → (⟨x, hx⟩ : simTA L c) ∈ U`.

Introduce `x hx hxN`. Establish `h : (⟨x, hx⟩ : simTA L c) ∈ Subtype.val ⁻¹' V` using `hNV x hxN`. Rewrite `h` using `[hVU]`. Conclude with `h`. Take `⟨S₃, hS₃⟩` from `GlobalTheory.T.ideles_finite_class_decomposition L`.

Set `B1 : Subgroup (AfE ℚ L)ˣ` to `(ratId ℚ L).range ⊔ intU ℚ L`. Take `⟨S₁, hS₁T, hS₁⟩` from `cover_of_label S₃ (simTA L c) B1 Set.univ (fun x s => s⁻¹ * x ∈ B1) (fun x _ _ => by`. Take `⟨s, hs, a, k, hk, rfl⟩` from `hS₃ x`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, inv_mul_cancel_left]`.

Conclude with `mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right hk))`. Use the proof step `(fun x y s _ _ _ _ hx hy => by`. Establish `e : y⁻¹ * x = (s⁻¹ * y)⁻¹ * (s⁻¹ * x)` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem (inv_mem hy) hx)`.

Take `⟨S₆, hS₆⟩` from `GlobalTheory.T.fixed_units_finitely_many_norms L c hc`. Set `B2 : Subgroup (AfE ℚ L)ˣ` to `(simT ℚ c).map (ratId ℚ L) ⊔ intU ℚ L`. Set `lab : (AfE ℚ L)ˣ → L → Prop` to `fun y f => ∃ (a : Lˣ) (k : (AfE ℚ L)ˣ) (r : ℚˣ) (η : Lˣ), k ∈ intU ℚ L ∧ IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ y = ratId ℚ L a * k ∧ (a : L) * c a = algebraMap ℚ L r * (f * ((η : L) * c η))`. Establish `hlab : ∀ y ∈ (B1 : Set (AfE ℚ L)ˣ), y ∈ simTA L c → ∃ f ∈ S₆, lab y f`. Introduce `y hy hyT`.

Take `⟨z, ⟨a, rfl⟩, k, hk, rfl⟩` from `Subgroup.mem_sup.1 hy`. Take `⟨t, ht⟩` from `hyT`. Take `⟨r, u, hu1, hu2, rfl⟩` from `GlobalTheory.T.rational_finite_idele_factorization t`. Set `ε : Lˣ` to `a * Units.map (c : L →+* L).toMonoidHom a * (Units.map (algebraMap ℚ L).toMonoidHom r)⁻¹`. Establish `key : ratId ℚ L ε = idF ℚ L u * (k * conjId c k)⁻¹`.

Rewrite using `[eq_mul_inv_iff_mul_eq]`. Establish `e1 : ratId ℚ L ε * (k * conjId c k) = (ratId ℚ L a * k * conjId c (ratId ℚ L a * k)) * (ratId ℚ L (Units.map (algebraMap ℚ L).toMonoidHom r))⁻¹`. Simplify using `only [ε, map_mul, map_inv, conjId_ratId]`. Simplify using `only [mul_comm, mul_left_comm, mul_assoc]`. Rewrite using `[e1, ht, map_mul, idF_map_algebraMap, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]`.

Establish `hεU : ratId ℚ L ε ∈ intU ℚ L`. Rewrite using `[key]`. Conclude with `mul_mem (idF_mem_intU L hu1 hu2) (inv_mem (mul_mem hk (conjId_mem_intU L c hk)))`. Take `⟨hε1, hε2⟩` from `(GlobalTheory.T.principal_idele_integral_iff_unit L ε).1 hεU`. Establish `hεc : c (ε : L) = ε`.

Simplify using `only [ε, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_inv₀, hc, AlgHom.commutes]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨f, hf, η, hη1, hη2, hεf⟩` from `hS₆ ε hε1 hε2 hεc`. Use `⟨f, hf, a, k, r, η, hk, hη1, hη2, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← hεf]`.

Establish `hr : algebraMap ℚ L (r : ℚ) ≠ 0` using `by simp`. Simplify using `only [ε, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Clear the denominators using the available nonvanishing facts. Establish `hB : ∀ x y f, x ∈ (B1 : Set (AfE ℚ L)ˣ) → y ∈ (B1 : Set (AfE ℚ L)ˣ) → x ∈ simTA L c → y ∈ simTA L c → lab x f → lab y f → y⁻¹ * x ∈ B2`. Introduce and unpack `x y f - - - - ⟨a, k, r, η, hk, hη1, hη2, rfl, ha⟩ ⟨a', k', r', η', hk', hη1', hη2', rfl, ha'⟩`.

Establish `hf : f ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[zero_mul, mul_zero]`. Conclude with `mul_ne_zero a.ne_zero ((map_ne_zero c).2 a.ne_zero) ha`. Set `b : Lˣ` to `a * a'⁻¹ * η' * η⁻¹`.

Establish `hb : b ∈ simT ℚ c`. Use `⟨r * r'⁻¹, ?_⟩` and prove the remaining obligations. Establish `hη0 : (η : L) * c η ≠ 0` using `mul_ne_zero η.ne_zero ((map_ne_zero c).2 η.ne_zero)`. Establish `hη0' : (η' : L) * c η' ≠ 0` using `mul_ne_zero η'.ne_zero ((map_ne_zero c).2 η'.ne_zero)`. Establish `hr' : algebraMap ℚ L (r' : ℚ) ≠ 0` using `by simp`.

Establish `e : (b : L) * c b = ((a : L) * c a) * ((a' : L) * c a')⁻¹ * ((η' : L) * c η') * ((η : L) * c η)⁻¹`. Simplify using `only [b, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ha, ha']`. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]`.

Clear the denominators using the available nonvanishing facts. Establish `hab : a = b * (η * η'⁻¹) * a'`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [b, Units.val_mul, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.

Establish `hint : ratId ℚ L (η * η'⁻¹) ∈ intU ℚ L`. Rewrite using `[GlobalTheory.T.principal_idele_integral_iff_unit]`. Prove the components needed by the constructor for the conclusion. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val] at hη2' ⊢`. Conclude with `hη1.mul hη2'`.

Simplify using `only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hη2 ⊢`. Conclude with `hη1'.mul hη2`. Establish `e2 : (ratId ℚ L a' * k')⁻¹ * (ratId ℚ L a * k) = ratId ℚ L b * (ratId ℚ L (η * η'⁻¹) * (k'⁻¹ * k))`. Rewrite using `[hab, map_mul, map_mul]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Rewrite using `[e2]`. Conclude with `mul_mem (Subgroup.mem_sup_left ⟨b, hb, rfl⟩) (Subgroup.mem_sup_right (mul_mem hint (mul_mem (inv_mem hk') hk)))`. Take `⟨S₂, hS₂T, hS₂⟩` from `cover_of_label S₆ (simTA L c) B2 (B1 : Set (AfE ℚ L)ˣ) lab hlab hB`.

Take `⟨S₄, hS₄⟩` from `GlobalTheory.T.integral_units_finite_cosets L N hN`. Take `⟨S₅, hS₅T, hS₅⟩` from `cover_of_label S₄ (simTA L c) (congN ℚ L N) (intU ℚ L : Set (AfE ℚ L)ˣ) (fun k s => s⁻¹ * k ∈ congN ℚ L N) (fun k hk _ => hS₄ k hk) (fun x y s _ _ _ _ hx hy => by`. Establish `e : y⁻¹ * x = (s⁻¹ * y)⁻¹ * (s⁻¹ * x)` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem (inv_mem hy) hx)`.

Set `rep : (S₁ × S₂ × S₅) → DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c))` to `fun p => DoubleCoset.mk (ratT L c) U ⟨p.1.1 * p.2.1.1 * p.2.2.1, mul_mem (mul_mem (hS₁T _ p.1.2) (hS₂T _ p.2.1.2)) (hS₅T _ p.2.2.2)⟩`. Use `Finite.of_surjective rep ?_` and prove the remaining obligations. Introduce `q`. Proceed by induction on `q using Quotient.inductionOn' with`. Consider the case `h x`.

Take `⟨x, hxT⟩` from `x`. Take `⟨s₁, hs₁, hy1, hyT⟩` from `hS₁ x (Set.mem_univ _) hxT`. Take `⟨s₂, hs₂, hz2, hzT⟩` from `hS₂ _ hy1 hyT`. Take `⟨γ, ⟨b, hb, rfl⟩, k, hk, hγk⟩` from `Subgroup.mem_sup.1 hz2`. Establish `hγT : ratId ℚ L b ∈ simTA L c` using `ratId_mem_simTA L c hb`.

Establish `hkT : k ∈ simTA L c`. Establish `e : k = (ratId ℚ L b)⁻¹ * (s₂⁻¹ * (s₁⁻¹ * x))` using `by rw [← hγk, inv_mul_cancel_left]`. Rewrite using `[e]`. Conclude with `mul_mem (inv_mem hγT) hzT`. Take `⟨s₅, hs₅, hw, hwT⟩` from `hS₅ k hk hkT`.

Use `⟨(⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩, ⟨s₅, hs₅⟩), ?_⟩` and prove the remaining obligations. Use `show DoubleCoset.mk (ratT L c) U _ = DoubleCoset.mk (ratT L c) U _`. Rewrite using `[DoubleCoset.eq]`. Use `⟨⟨ratId ℚ L b, hγT⟩, (Subgroup.mem_subgroupOf).2 ⟨b, hb, rfl⟩, ⟨s₅⁻¹ * k, hwT⟩, hcongU _ hwT hw, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hx : x = s₁ * (s₂ * (ratId ℚ L b * k))`. Rewrite using `[hγk]`. Use `group`. Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[hx]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem finite_doubleCoset_of_involutive (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ x, c (c x) = x) :
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ U : Subgroup (simTA L c), IsOpen (U : Set (simTA L c)) →
      Finite (DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c))) := by
  letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
  intro U hU
  classical

  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.1 hU
  have h1V : (1 : (AfE ℚ L)ˣ) ∈ V := by
    have h : (1 : simTA L c) ∈ (U : Set (simTA L c)) := one_mem U
    rw [← hVU] at h
    exact h
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.T.congruence_units_basis_of_nbhds L V hV h1V
  have hcongU : ∀ (x : (AfE ℚ L)ˣ) (hx : x ∈ simTA L c), x ∈ congN ℚ L N → (⟨x, hx⟩ : simTA L c) ∈ U := by
    intro x hx hxN
    have h : (⟨x, hx⟩ : simTA L c) ∈ Subtype.val ⁻¹' V := hNV x hxN
    rw [hVU] at h
    exact h

  obtain ⟨S₃, hS₃⟩ := GlobalTheory.T.ideles_finite_class_decomposition L
  let B1 : Subgroup (AfE ℚ L)ˣ := (ratId ℚ L).range ⊔ intU ℚ L
  obtain ⟨S₁, hS₁T, hS₁⟩ := cover_of_label S₃ (simTA L c) B1 Set.univ (fun x s => s⁻¹ * x ∈ B1)
    (fun x _ _ => by
      obtain ⟨s, hs, a, k, hk, rfl⟩ := hS₃ x
      refine ⟨s, hs, ?_⟩
      rw [mul_assoc, inv_mul_cancel_left]
      exact mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right hk))
    (fun x y s _ _ _ _ hx hy => by
      have e : y⁻¹ * x = (s⁻¹ * y)⁻¹ * (s⁻¹ * x) := by group
      rw [e]
      exact mul_mem (inv_mem hy) hx)

  obtain ⟨S₆, hS₆⟩ := GlobalTheory.T.fixed_units_finitely_many_norms L c hc
  let B2 : Subgroup (AfE ℚ L)ˣ := (simT ℚ c).map (ratId ℚ L) ⊔ intU ℚ L
  let lab : (AfE ℚ L)ˣ → L → Prop := fun y f => ∃ (a : Lˣ) (k : (AfE ℚ L)ˣ) (r : ℚˣ) (η : Lˣ),
    k ∈ intU ℚ L ∧ IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ y = ratId ℚ L a * k ∧
      (a : L) * c a = algebraMap ℚ L r * (f * ((η : L) * c η))
  have hlab : ∀ y ∈ (B1 : Set (AfE ℚ L)ˣ), y ∈ simTA L c → ∃ f ∈ S₆, lab y f := by
    intro y hy hyT
    obtain ⟨z, ⟨a, rfl⟩, k, hk, rfl⟩ := Subgroup.mem_sup.1 hy
    obtain ⟨t, ht⟩ := hyT
    obtain ⟨r, u, hu1, hu2, rfl⟩ := GlobalTheory.T.rational_finite_idele_factorization t
    let ε : Lˣ := a * Units.map (c : L →+* L).toMonoidHom a * (Units.map (algebraMap ℚ L).toMonoidHom r)⁻¹
    have key : ratId ℚ L ε = idF ℚ L u * (k * conjId c k)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      have e1 : ratId ℚ L ε * (k * conjId c k) =
          (ratId ℚ L a * k * conjId c (ratId ℚ L a * k)) * (ratId ℚ L (Units.map (algebraMap ℚ L).toMonoidHom r))⁻¹ := by
        simp only [ε, map_mul, map_inv, conjId_ratId]
        simp only [mul_comm, mul_left_comm, mul_assoc]
      rw [e1, ht, map_mul, idF_map_algebraMap, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    have hεU : ratId ℚ L ε ∈ intU ℚ L := by
      rw [key]
      exact mul_mem (idF_mem_intU L hu1 hu2) (inv_mem (mul_mem hk (conjId_mem_intU L c hk)))
    obtain ⟨hε1, hε2⟩ := (GlobalTheory.T.principal_idele_integral_iff_unit L ε).1 hεU
    have hεc : c (ε : L) = ε := by
      simp only [ε, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
        RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_inv₀, hc,
        AlgHom.commutes]
      ring
    obtain ⟨f, hf, η, hη1, hη2, hεf⟩ := hS₆ ε hε1 hε2 hεc
    refine ⟨f, hf, a, k, r, η, hk, hη1, hη2, rfl, ?_⟩
    rw [← hεf]
    have hr : algebraMap ℚ L (r : ℚ) ≠ 0 := by simp
    simp only [ε, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    field_simp

  have hB : ∀ x y f, x ∈ (B1 : Set (AfE ℚ L)ˣ) → y ∈ (B1 : Set (AfE ℚ L)ˣ) → x ∈ simTA L c → y ∈ simTA L c →
      lab x f → lab y f → y⁻¹ * x ∈ B2 := by
    rintro x y f - - - - ⟨a, k, r, η, hk, hη1, hη2, rfl, ha⟩ ⟨a', k', r', η', hk', hη1', hη2', rfl, ha'⟩
    have hf : f ≠ 0 := by
      rintro rfl
      rw [zero_mul, mul_zero] at ha
      exact mul_ne_zero a.ne_zero ((map_ne_zero c).2 a.ne_zero) ha
    let b : Lˣ := a * a'⁻¹ * η' * η⁻¹
    have hb : b ∈ simT ℚ c := by
      refine ⟨r * r'⁻¹, ?_⟩
      have hη0 : (η : L) * c η ≠ 0 := mul_ne_zero η.ne_zero ((map_ne_zero c).2 η.ne_zero)
      have hη0' : (η' : L) * c η' ≠ 0 := mul_ne_zero η'.ne_zero ((map_ne_zero c).2 η'.ne_zero)
      have hr' : algebraMap ℚ L (r' : ℚ) ≠ 0 := by simp
      have e : (b : L) * c b = ((a : L) * c a) * ((a' : L) * c a')⁻¹ * ((η' : L) * c η') * ((η : L) * c η)⁻¹ := by
        simp only [b, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
        ring
      rw [e, ha, ha']
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
      field_simp
    have hab : a = b * (η * η'⁻¹) * a' := by
      apply Units.ext
      simp only [b, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    have hint : ratId ℚ L (η * η'⁻¹) ∈ intU ℚ L := by
      rw [GlobalTheory.T.principal_idele_integral_iff_unit]
      constructor
      · simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hη2' ⊢
        exact hη1.mul hη2'
      · simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hη2 ⊢
        exact hη1'.mul hη2
    have e2 : (ratId ℚ L a' * k')⁻¹ * (ratId ℚ L a * k) = ratId ℚ L b * (ratId ℚ L (η * η'⁻¹) * (k'⁻¹ * k)) := by
      rw [hab, map_mul, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e2]
    exact mul_mem (Subgroup.mem_sup_left ⟨b, hb, rfl⟩)
      (Subgroup.mem_sup_right (mul_mem hint (mul_mem (inv_mem hk') hk)))
  obtain ⟨S₂, hS₂T, hS₂⟩ := cover_of_label S₆ (simTA L c) B2 (B1 : Set (AfE ℚ L)ˣ) lab hlab hB

  obtain ⟨S₄, hS₄⟩ := GlobalTheory.T.integral_units_finite_cosets L N hN
  obtain ⟨S₅, hS₅T, hS₅⟩ := cover_of_label S₄ (simTA L c) (congN ℚ L N) (intU ℚ L : Set (AfE ℚ L)ˣ)
    (fun k s => s⁻¹ * k ∈ congN ℚ L N) (fun k hk _ => hS₄ k hk)
    (fun x y s _ _ _ _ hx hy => by
      have e : y⁻¹ * x = (s⁻¹ * y)⁻¹ * (s⁻¹ * x) := by group
      rw [e]
      exact mul_mem (inv_mem hy) hx)

  let rep : (S₁ × S₂ × S₅) → DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c)) :=
    fun p => DoubleCoset.mk (ratT L c) U ⟨p.1.1 * p.2.1.1 * p.2.2.1,
      mul_mem (mul_mem (hS₁T _ p.1.2) (hS₂T _ p.2.1.2)) (hS₅T _ p.2.2.2)⟩
  refine Finite.of_surjective rep ?_
  intro q
  induction q using Quotient.inductionOn' with
  | h x =>
  obtain ⟨x, hxT⟩ := x
  obtain ⟨s₁, hs₁, hy1, hyT⟩ := hS₁ x (Set.mem_univ _) hxT
  obtain ⟨s₂, hs₂, hz2, hzT⟩ := hS₂ _ hy1 hyT
  obtain ⟨γ, ⟨b, hb, rfl⟩, k, hk, hγk⟩ := Subgroup.mem_sup.1 hz2
  have hγT : ratId ℚ L b ∈ simTA L c := ratId_mem_simTA L c hb
  have hkT : k ∈ simTA L c := by
    have e : k = (ratId ℚ L b)⁻¹ * (s₂⁻¹ * (s₁⁻¹ * x)) := by rw [← hγk, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hγT) hzT
  obtain ⟨s₅, hs₅, hw, hwT⟩ := hS₅ k hk hkT
  refine ⟨(⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩, ⟨s₅, hs₅⟩), ?_⟩
  show DoubleCoset.mk (ratT L c) U _ = DoubleCoset.mk (ratT L c) U _
  rw [DoubleCoset.eq]
  refine ⟨⟨ratId ℚ L b, hγT⟩, (Subgroup.mem_subgroupOf).2 ⟨b, hb, rfl⟩, ⟨s₅⁻¹ * k, hwT⟩, hcongU _ hwT hw, ?_⟩
  apply Subtype.ext
  have hx : x = s₁ * (s₂ * (ratId ℚ L b * k)) := by
    rw [hγk]
    group
  simp only [Subgroup.coe_mul]
  rw [hx]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Establish `hinv : ∀ x, c (c x) = x`. Set `τ : L →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := L)).toRingHom`. Introduce `x`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hc, hc, Complex.conj_conj]`.

Conclude with `finite_doubleCoset_of_involutive L c hinv`.
-/
theorem finite_doubleCoset (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ (τ : L →+* ℂ) (x : L), τ (c x) = (starRingEnd ℂ) (τ x)) :
    letI : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L) := Algebra.TensorProduct.rightAlgebra
    letI : TopologicalSpace (AfE ℚ L) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AfE ℚ L)
    ∀ U : Subgroup (simTA L c), IsOpen (U : Set (simTA L c)) →
      Finite (DoubleCoset.Quotient (ratT L c : Set (simTA L c)) (U : Set (simTA L c))) := by
  have hinv : ∀ x, c (c x) = x := by
    let τ : L →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := L)).toRingHom
    intro x
    apply τ.injective
    rw [hc, hc, Complex.conj_conj]
  exact finite_doubleCoset_of_involutive L c hinv

end GlobalTheory.LKTorus
