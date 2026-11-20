import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HomCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FinChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' N)` using `hN.preimage (by fun_prop)`. Use `filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' N by simpa using h1)] with y hy`. Use `h x (x⁻¹ * y)` as an intermediate fact.

Rewrite `this` using `[h0 _ hy, add_zero, mul_inv_cancel_left]`. Conclude with `this`.
-/
private theorem aH_lc {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) (N : Set H) (hN : IsOpen N) (h1 : (1 : H) ∈ N)
    (h0 : ∀ u ∈ N, φ u = 0) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' N) := hN.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' N by simpa using h1)] with y hy
  have := h x (x⁻¹ * y)
  rw [h0 _ hy, add_zero, mul_inv_cancel_left] at this
  exact this

/- English proof (translation)
Use `h 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `left_eq_add.1 this`.
-/
private theorem aH_one {H M : Type} [Group H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) : φ 1 = 0 := by
  have := h 1 1
  rw [mul_one] at this
  exact left_eq_add.1 this

/- English proof (translation)
Use `h a⁻¹ a` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel, aH_one φ h]`. Conclude with `eq_neg_of_add_eq_zero_left this.symm`.
-/
private theorem aH_inv {H M : Type} [Group H] [AddCommGroup M]
    (φ : H → M) (h : ∀ a b, φ (a * b) = φ a + φ b) (a : H) : φ a⁻¹ = -φ a := by
  have := h a⁻¹ a
  rw [inv_mul_cancel, aH_one φ h] at this
  exact eq_neg_of_add_eq_zero_left this.symm

/- English proof (translation)
Rewrite using `[EqHom, Submodule.mem_inf, Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2, h3, -⟩, h4⟩`. Use `⟨h1, h2, h3, fun g u => ?_⟩` and prove the remaining obligations. Use `h4 g u ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ (fun x => by show g (u.1 (g.symm (g x))) = g (u.1 x)` as an intermediate fact.

Rewrite using `[AlgEquiv.symm_apply_apply])`. Rewrite using `[this, scalRep_apply]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨h1, h2, h3, h4⟩`. Use `⟨⟨h1, h2, h3, fun A hA => ?_⟩, fun g u u' h => ?_⟩` and prove the remaining obligations.

Simplify using `at hA`. Rewrite using `[scalRep_apply, ← h4 g u]`. Establish `: u' = ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩` using `Subtype.ext (AlgEquiv.ext fun x => by`. Use `h (g.symm x)` as an intermediate fact. Rewrite `this` using `[show g.toRingEquiv (g.symm x) = x from g.apply_symm_apply x]`.

Conclude with `this)`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
private theorem aH_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ)
    (U : Subgroup (G F Ω)) [hU : U.Normal] (φ : U → ZMod l) :
    φ ∈ EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) ↔
      IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
        (∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → φ u = 0) ∧
        ∀ (g : G F Ω) (u : U), φ ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ = φ u := by
  rw [EqHom, Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨⟨h1, h2, h3, -⟩, h4⟩
    refine ⟨h1, h2, h3, fun g u => ?_⟩
    have := h4 g u ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ (fun x => by
      show g (u.1 (g.symm (g x))) = g (u.1 x)
      rw [AlgEquiv.symm_apply_apply])
    rw [this, scalRep_apply]
    simp
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2, h3, fun A hA => ?_⟩, fun g u u' h => ?_⟩
    · simp at hA
    · rw [scalRep_apply, ← h4 g u]
      have : u' = ⟨g * u * g⁻¹, hU.conj_mem _ u.2 g⟩ := Subtype.ext (AlgEquiv.ext fun x => by
        have := h (g.symm x)
        rw [show g.toRingEquiv (g.symm x) = x from g.apply_symm_apply x] at this
        exact this)
      rw [this]
      simp

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ K _ _ _ _ _ _ _ l hl ζ hζ hc hI hfin`. Use `haveI : IsGalois F Ω := {}`. Establish `hUo : IsOpen (galOf F K Ω : Set (G F Ω))` using `(galEmbTop F K Ω).2.1`. Establish `hcyc : IsCyclic (G F Ω ⧸ galOf F K Ω)`. Take `⟨q1, q2, -⟩` from `galQuot F K Ω`.

Establish `e` using `(QuotientGroup.quotientMulEquivOfEq q2.symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ q1)`. Conclude with `isCyclic_of_surjective e.symm e.symm.surjective`. Establish `hn : (galOf F K Ω).Normal` using `inferInstance`. Use `set U := galOf F K Ω with hUdef`. Establish `hm` using `aH_mem l U`.

Use `set E := EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) with hE`. Set `N : Subgroup (G F Ω)` to `{ carrier := {g | ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0} one_mem' := ⟨U.one_mem, fun φ => aH_one φ.1 ((hm _).1 φ.2).2.1⟩ mul_mem' := by`. Introduce and unpack `a b ⟨ha, ha'⟩ ⟨hb, hb'⟩`. Use `⟨U.mul_mem ha hb, fun φ => ?_⟩` and prove the remaining obligations. Use `((hm _).1 φ.2).2.1 ⟨a, ha⟩ ⟨b, hb⟩` as an intermediate fact.

Rewrite `this` using `[ha', hb', add_zero]`. Conclude with `this`. Use the proof step `inv_mem' := by`. Introduce and unpack `a ⟨ha, ha'⟩`. Use `⟨U.inv_mem ha, fun φ => ?_⟩` and prove the remaining obligations.

Use `aH_inv φ.1 ((hm _).1 φ.2).2.1 ⟨a, ha⟩` as an intermediate fact. Rewrite `this` using `[ha', neg_zero]`. Conclude with `this }`. Establish `hN : ∀ g, g ∈ N ↔ ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0` using `fun _ => Iff.rfl`. Use `haveI : N.Normal := ⟨fun u ⟨hu, hu'⟩ g => ⟨hn.conj_mem u hu g, fun φ => (((hm _).1 φ.2).2.2.2 g ⟨u, hu⟩).trans (hu' φ)⟩⟩`.

Establish `hNo : IsOpen (N : Set (G F Ω))`. Establish `: (N : Set (G F Ω)) = Subtype.val '' (⋂ φ : E, φ.1 ⁻¹' {0})`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, hN, Set.mem_image, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]`. Conclude with `⟨fun ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩, fun ⟨u, h, e⟩ => e ▸ ⟨u.2, h⟩⟩`.

Rewrite using `[this]`. Conclude with `hUo.isOpenMap_subtype_val _ (isOpen_iInter_of_finite fun φ => ((hm _).1 φ.2).1 _)`. Use `haveI : Finite (G F Ω ⧸ N) := N.quotient_finite_of_isOpen hNo`. Use `haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Establish `hcomm : ∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N` using `fun g u hu => by`.

Use `⟨U.mul_mem (hn.conj_mem u hu g) (U.inv_mem hu), fun φ => ?_⟩` and prove the remaining obligations. Take `⟨-, h2, -, h4⟩` from `(hm _).1 φ.2`. Use `h2 ⟨g * u * g⁻¹, hn.conj_mem u hu g⟩ (⟨u, hu⟩ : U)⁻¹` as an intermediate fact. Rewrite `this` using `[aH_inv φ.1 h2, h4 g ⟨u, hu⟩, add_neg_cancel]`. Conclude with `this`.

Establish `hIN : ∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F` using `F) A → u.1 ∈ N := fun A u hu => ⟨u.2, fun φ => ((hm _).1 φ.2).2.2.1 A u hu⟩`. Establish `key` using `homCyc l (G F Ω) U N (fun g h => h.1) hcyc hcomm`. Establish `e1 : Nat.card E = Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0}`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun φ => ⟨fun h => ⟨((hm _).1 h).2.1, fun u hu => hu.2 ⟨φ, h⟩⟩, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨h2, h0⟩`.

Use `(hm _).2 ⟨aH_lc φ h2 (Subtype.val ⁻¹' N) (hNo.preimage continuous_subtype_val) N.one_mem h0, h2, fun A u hu => h0 u (hIN A u hu), fun g u => ?_⟩` and prove the remaining obligations. Use `h2 ⟨g * u * g⁻¹, hn.conj_mem u u.2 g⟩ u⁻¹` as an intermediate fact. Rewrite `this` using `[aH_inv φ h2, h0 _ (hcomm g u u.2)]`. Conclude with `add_neg_eq_zero.1 this.symm`. Establish `hf` using `finChar F Ω l l ζ hl.out.ne_zero hl.out.ne_zero hζ`.

Rewrite using `[e1]`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[← Nat.card_coe_set_eq]`. Use `haveI := hf.to_subtype`. Use `Nat.card_le_card_of_injective (fun φ => ⟨φ.1, aH_lc φ.1 φ.2.1 N hNo N.one_mem φ.2.2, φ.2.1, fun A hA g hg => φ.2.2 g (hIN A ⟨g, hI A hA hg⟩ hg)⟩) fun a b h => Subtype.ext (Subtype.mk.inj h)` and prove the remaining obligations.
-/
theorem UpperTheory.V.FW.ambHom :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] [IsGalois F K] (l : ℕ) [Fact l.Prime] (ζ : F), IsPrimitiveRoot ζ l → IsCyclic Gal(K/F) → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ galOf F K Ω) → Finite (EqHom 1 (galOf F K Ω) (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ))) → Nat.card (EqHom 1 (galOf F K Ω) (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ))) ≤ Set.ncard {φ : G F Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := F) A, φ g = 0} := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ _ l hl ζ hζ hc hI hfin
  haveI : IsGalois F Ω := {}
  have hUo : IsOpen (galOf F K Ω : Set (G F Ω)) := (galEmbTop F K Ω).2.1
  have hcyc : IsCyclic (G F Ω ⧸ galOf F K Ω) := by
    obtain ⟨q1, q2, -⟩ := galQuot F K Ω
    have e := (QuotientGroup.quotientMulEquivOfEq q2.symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ q1)
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have hn : (galOf F K Ω).Normal := inferInstance
  set U := galOf F K Ω with hUdef
  have hm := aH_mem l U
  set E := EqHom 1 U (Formalism.GaloisCohomology.scalRep (ZMod l) (1 : G F Ω →* (ZMod l)ˣ)) with hE
  let N : Subgroup (G F Ω) :=
    { carrier := {g | ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0}
      one_mem' := ⟨U.one_mem, fun φ => aH_one φ.1 ((hm _).1 φ.2).2.1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨U.mul_mem ha hb, fun φ => ?_⟩
        have := ((hm _).1 φ.2).2.1 ⟨a, ha⟩ ⟨b, hb⟩
        rw [ha', hb', add_zero] at this
        exact this
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨U.inv_mem ha, fun φ => ?_⟩
        have := aH_inv φ.1 ((hm _).1 φ.2).2.1 ⟨a, ha⟩
        rw [ha', neg_zero] at this
        exact this }
  have hN : ∀ g, g ∈ N ↔ ∃ h : g ∈ U, ∀ φ : E, φ.1 ⟨g, h⟩ = 0 := fun _ => Iff.rfl
  haveI : N.Normal := ⟨fun u ⟨hu, hu'⟩ g => ⟨hn.conj_mem u hu g, fun φ =>
    (((hm _).1 φ.2).2.2.2 g ⟨u, hu⟩).trans (hu' φ)⟩⟩
  have hNo : IsOpen (N : Set (G F Ω)) := by
    have : (N : Set (G F Ω)) = Subtype.val '' (⋂ φ : E, φ.1 ⁻¹' {0}) := by
      ext g
      simp only [SetLike.mem_coe, hN, Set.mem_image, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩, fun ⟨u, h, e⟩ => e ▸ ⟨u.2, h⟩⟩
    rw [this]
    exact hUo.isOpenMap_subtype_val _ (isOpen_iInter_of_finite fun φ => ((hm _).1 φ.2).1 _)
  haveI : Finite (G F Ω ⧸ N) := N.quotient_finite_of_isOpen hNo
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcomm : ∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N := fun g u hu => by
    refine ⟨U.mul_mem (hn.conj_mem u hu g) (U.inv_mem hu), fun φ => ?_⟩
    obtain ⟨-, h2, -, h4⟩ := (hm _).1 φ.2
    have := h2 ⟨g * u * g⁻¹, hn.conj_mem u hu g⟩ (⟨u, hu⟩ : U)⁻¹
    rw [aH_inv φ.1 h2, h4 g ⟨u, hu⟩, add_neg_cancel] at this
    exact this
  have hIN : ∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → u.1 ∈ N := fun A u hu =>
    ⟨u.2, fun φ => ((hm _).1 φ.2).2.2.1 A u hu⟩
  have key := homCyc l (G F Ω) U N (fun g h => h.1) hcyc hcomm
  have e1 : Nat.card E = Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun φ => ⟨fun h => ⟨((hm _).1 h).2.1, fun u hu => hu.2 ⟨φ, h⟩⟩, ?_⟩)
    rintro ⟨h2, h0⟩
    refine (hm _).2 ⟨aH_lc φ h2 (Subtype.val ⁻¹' N) (hNo.preimage continuous_subtype_val) N.one_mem h0, h2,
      fun A u hu => h0 u (hIN A u hu), fun g u => ?_⟩
    have := h2 ⟨g * u * g⁻¹, hn.conj_mem u u.2 g⟩ u⁻¹
    rw [aH_inv φ h2, h0 _ (hcomm g u u.2)] at this
    exact add_neg_eq_zero.1 this.symm
  have hf := finChar F Ω l l ζ hl.out.ne_zero hl.out.ne_zero hζ
  rw [e1]
  refine key.trans ?_
  rw [← Nat.card_coe_set_eq]
  haveI := hf.to_subtype
  refine Nat.card_le_card_of_injective (fun φ => ⟨φ.1, aH_lc φ.1 φ.2.1 N hNo N.one_mem φ.2.2, φ.2.1,
    fun A hA g hg => φ.2.2 g (hIN A ⟨g, hI A hA hg⟩ hg)⟩) fun a b h => Subtype.ext (Subtype.mk.inj h)
