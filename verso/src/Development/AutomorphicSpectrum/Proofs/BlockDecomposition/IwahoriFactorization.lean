import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import GroundTheory.LocalFields.Integers

open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix

namespace GlobalTheory.CompanionTheory.TfLoc.Iw

section Entries

variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩`. Use `⟨fun i j => (h.val i j).2, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `((h⁻¹).val i j).2`.

Introduce and unpack `⟨h1, h2⟩`. Set `f` to `(Valuation.integer (valuation F)).subtype`. Set `A : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F))` to `fun i j => ⟨_, h1 i j⟩`. Set `B : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F))` to `fun i j => ⟨_, h2 i j⟩`. Establish `hA : A.map f = (g : Matrix (Fin m) (Fin m) F)` using `by ext i j; rfl`.

Establish `hB : B.map f = ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)` using `by ext i j; rfl`. Establish `inj : Function.Injective (fun M : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F)) => M.map f)` using `Matrix.map_injective Subtype.val_injective`. Establish `hAB : A * B = 1` using `inj (by show (A * B).map f = (1 : Matrix (Fin m) (Fin m) _).map f`. Rewrite using `[Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero f) (map_one f)]`. Conclude with `Units.mul_inv g)`.

Establish `hBA : B * A = 1` using `inj (by show (B * A).map f = (1 : Matrix (Fin m) (Fin m) _).map f`. Rewrite using `[Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero f) (map_one f)]`. Conclude with `Units.inv_mul g)`. Conclude with `⟨⟨A, B, hAB, hBA⟩, Units.ext (by ext i j; rfl)⟩`.
-/
theorem mem_unitGL_iff (g : GL (Fin m) F) :
    g ∈ unitGL (n := Fin m) F ↔
      (∀ i j, valuation F ((g : Matrix (Fin m) (Fin m) F) i j) ≤ 1) ∧
      (∀ i j, valuation F (((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j) ≤ 1) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => (h.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((h⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let f := (Valuation.integer (valuation F)).subtype
    let A : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F)) := fun i j => ⟨_, h1 i j⟩
    let B : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F)) := fun i j => ⟨_, h2 i j⟩
    have hA : A.map f = (g : Matrix (Fin m) (Fin m) F) := by ext i j; rfl
    have hB : B.map f = ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F)) => M.map f) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := inj (by
      show (A * B).map f = (1 : Matrix (Fin m) (Fin m) _).map f
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero f) (map_one f)]
      exact Units.mul_inv g)
    have hBA : B * A = 1 := inj (by
      show (B * A).map f = (1 : Matrix (Fin m) (Fin m) _).map f
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero f) (map_one f)]
      exact Units.inv_mul g)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext (by ext i j; rfl)⟩

/- English proof (translation)
The claim follows from `lt_of_le_of_lt (mul_le_of_le_one_left' ha) hb`.
-/
theorem mul_lt_one_of_le_of_lt_alt {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≤ 1)
    (hb : b < 1) : a * b < 1 :=
  lt_of_le_of_lt (mul_le_of_le_one_left' ha) hb

def ltIdeal (F : Type*) [Field F] [ValuativeRel F] : Ideal (Valuation.integer (valuation F)) where
  carrier := {x | valuation F (x : F) < 1}
  add_mem' := fun {a b} ha hb => (valuation F).map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    show valuation F ((c : F) * (x : F)) < 1
    rw [map_mul]
    exact mul_lt_one_of_le_of_lt_alt c.2 hx

/- English proof (translation)
Use `⟨mul_mem hg.1 hh.1, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `hg1` using `((mem_unitGL_iff g).1 hg.1).1`. Establish `hh1` using `((mem_unitGL_iff h).1 hh.1).1`. Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Use `(valuation F).map_sum_lt one_ne_zero fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Break down `lt_or_ge l i with hl | hl` into its components or cases. Rewrite using `[mul_comm]`. Conclude with `mul_lt_one_of_le_of_lt_alt (hh1 l j) (hg.2 i l hl)`. Conclude with `mul_lt_one_of_le_of_lt_alt (hg1 i l) (hh.2 l j (lt_of_lt_of_le hij hl))`.
-/
theorem iwahori_mul {g h : GL (Fin m) F} (hg : g ∈ iwahori (m := m) F) (hh : h ∈ iwahori (m := m) F) :
    g * h ∈ iwahori (m := m) F := by
  refine ⟨mul_mem hg.1 hh.1, fun i j hij => ?_⟩
  have hg1 := ((mem_unitGL_iff g).1 hg.1).1
  have hh1 := ((mem_unitGL_iff h).1 hh.1).1
  rw [Units.val_mul, Matrix.mul_apply]
  refine (valuation F).map_sum_lt one_ne_zero fun l _ => ?_
  rw [map_mul]
  rcases lt_or_ge l i with hl | hl
  · rw [mul_comm]
    exact mul_lt_one_of_le_of_lt_alt (hh1 l j) (hg.2 i l hl)
  · exact mul_lt_one_of_le_of_lt_alt (hg1 i l) (hh.2 l j (lt_of_lt_of_le hij hl))

/- English proof (translation)
Use `⟨inv_mem hg.1, fun i j hij => ?_⟩` and prove the remaining obligations. Take `⟨h, rfl⟩` from `hg.1`. Set `φ` to `Ideal.Quotient.mk (ltIdeal F)`. Set `M : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F) ⧸ ltIdeal F)` to `(h : Matrix (Fin m) (Fin m) _).map φ`. Set `N : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F) ⧸ ltIdeal F)` to `((h⁻¹ : GL (Fin m) _) : Matrix (Fin m) (Fin m) _).map φ`.

Establish `hMN : M * N = 1` using `by show Matrix.map _ φ * Matrix.map _ φ = 1`. Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Establish `hNM : N * M = 1` using `by show Matrix.map _ φ * Matrix.map _ φ = 1`. Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Use `letI : Invertible M := ⟨N, hNM, hMN⟩`.

Establish `htri : M.BlockTriangular id`. Introduce `a b hab`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hg.2 a b hab)`. Establish `hinv` using `Matrix.blockTriangular_inv_of_blockTriangular htri`. Establish `hN : M⁻¹ = N` using `Matrix.inv_eq_right_inv hMN`.

Rewrite `hinv` using `[hN]`. Establish `h0 : N i j = 0` using `hinv (show id j < id i from hij)`. Rewrite using `[← map_inv]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h0`.
-/
theorem iwahori_inv {g : GL (Fin m) F} (hg : g ∈ iwahori (m := m) F) : g⁻¹ ∈ iwahori (m := m) F := by
  refine ⟨inv_mem hg.1, fun i j hij => ?_⟩
  obtain ⟨h, rfl⟩ := hg.1
  let φ := Ideal.Quotient.mk (ltIdeal F)
  let M : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F) ⧸ ltIdeal F) :=
    (h : Matrix (Fin m) (Fin m) _).map φ
  let N : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F) ⧸ ltIdeal F) :=
    ((h⁻¹ : GL (Fin m) _) : Matrix (Fin m) (Fin m) _).map φ
  have hMN : M * N = 1 := by
    show Matrix.map _ φ * Matrix.map _ φ = 1
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hNM : N * M = 1 := by
    show Matrix.map _ φ * Matrix.map _ φ = 1
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]
  letI : Invertible M := ⟨N, hNM, hMN⟩
  have htri : M.BlockTriangular id := by
    intro a b hab
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hg.2 a b hab)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular htri
  have hN : M⁻¹ = N := Matrix.inv_eq_right_inv hMN
  rw [hN] at hinv
  have h0 : N i j = 0 := hinv (show id j < id i from hij)
  rw [← map_inv]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

/- English proof (translation)
Assemble the required witnesses or components as `⟨{ carrier := iwahori (m := m) F mul_mem' := iwahori_mul one_mem' := ⟨one_mem _, fun i j hij => by rw [Units.val_one, Matrix.one_apply_ne (ne_of_gt hij)]; simp⟩ inv_mem' := iwahori_inv }, rfl⟩`.
-/
theorem exists_subgroup : ∃ U : Subgroup (GL (Fin m) F), (U : Set (GL (Fin m) F)) = iwahori (m := m) F :=
  ⟨{ carrier := iwahori (m := m) F
     mul_mem' := iwahori_mul
     one_mem' := ⟨one_mem _, fun i j hij => by
       rw [Units.val_one, Matrix.one_apply_ne (ne_of_gt hij)]; simp⟩
     inv_mem' := iwahori_inv }, rfl⟩

/- English proof (translation)
Introduce `_ ht` and use `⟨ht.1, fun i j hij => by rw [ht.2 i j (ne_of_gt hij)]; simp⟩`.
-/
theorem torusO_subset : torusO (n := m) F ⊆ iwahori (m := m) F := fun _ ht =>
  ⟨ht.1, fun i j hij => by rw [ht.2 i j (ne_of_gt hij)]; simp⟩

end Entries

section Top

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}

/- English proof (translation)
Set `H : AddSubgroup F` to `{ carrier := {x | valuation F x < 1} add_mem' := fun {a b} ha hb => (valuation F).map_add_lt ha hb zero_mem' := by simp neg_mem' := fun {x} hx => by simpa [Valuation.map_neg] using hx }`. Establish `ho : IsOpen (H : Set F)` using `H.isOpen_of_mem_nhds (g := 0) ((IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2 ⟨1, one_ne_zero, fun x hx => hx⟩)`. Conclude with `⟨H.isClosed_of_isOpen ho, ho⟩`.
-/
theorem isClopen_lt_one : IsClopen {x : F | valuation F x < 1} := by
  let H : AddSubgroup F :=
    { carrier := {x | valuation F x < 1}
      add_mem' := fun {a b} ha hb => (valuation F).map_add_lt ha hb
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by simpa [Valuation.map_neg] using hx }
  have ho : IsOpen (H : Set F) := H.isOpen_of_mem_nhds (g := 0)
    ((IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2 ⟨1, one_ne_zero, fun x hx => hx⟩)
  exact ⟨H.isClosed_of_isOpen ho, ho⟩

/- English proof (translation)
Set `H : AddSubgroup F` to `{ carrier := {x | valuation F x ≤ 1} add_mem' := fun {a b} (ha : valuation F a ≤ 1) (hb : valuation F b ≤ 1) => ((valuation F).map_add_le ha hb : valuation F (a + b) ≤ 1) zero_mem' := by simp neg_mem' := fun {x} hx => by simpa [Valuation.map_neg] using hx }`. Establish `ho : IsOpen (H : Set F)` using `H.isOpen_of_mem_nhds (g := 0) ((IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2 ⟨1, one_ne_zero, fun x (hx : valuation F x < 1) => (le_of_lt hx : valuation F x ≤ 1)⟩)`. Conclude with `⟨H.isClosed_of_isOpen ho, ho⟩`.
-/
theorem isClopen_le_one : IsClopen {x : F | valuation F x ≤ 1} := by
  let H : AddSubgroup F :=
    { carrier := {x | valuation F x ≤ 1}
      add_mem' := fun {a b} (ha : valuation F a ≤ 1) (hb : valuation F b ≤ 1) =>
        ((valuation F).map_add_le ha hb : valuation F (a + b) ≤ 1)
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by simpa [Valuation.map_neg] using hx }
  have ho : IsOpen (H : Set F) := H.isOpen_of_mem_nhds (g := 0)
    ((IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2
      ⟨1, one_ne_zero, fun x (hx : valuation F x < 1) => (le_of_lt hx : valuation F x ≤ 1)⟩)
  exact ⟨H.isClosed_of_isOpen ho, ho⟩

/- English proof (translation)
The claim follows from `(continuous_id.matrix_elem i j).comp Units.continuous_val`.
-/
theorem continuous_entry (i j : Fin m) :
    Continuous fun g : GL (Fin m) F => (g : Matrix (Fin m) (Fin m) F) i j :=
  (continuous_id.matrix_elem i j).comp Units.continuous_val

/- English proof (translation)
The claim follows from `(continuous_entry i j).comp continuous_inv`.
-/
theorem continuous_inv_entry (i j : Fin m) :
    Continuous fun g : GL (Fin m) F => ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j :=
  (continuous_entry i j).comp continuous_inv

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [iwahori, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, mem_unitGL_iff, and_assoc]`.
-/
theorem iwahori_eq : iwahori (m := m) F =
    (⋂ i, ⋂ j, (fun g : GL (Fin m) F => (g : Matrix (Fin m) (Fin m) F) i j) ⁻¹'
        {x | valuation F x ≤ 1}) ∩
    (⋂ i, ⋂ j, (fun g : GL (Fin m) F => ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j) ⁻¹'
        {x | valuation F x ≤ 1}) ∩
    (⋂ i, ⋂ j, ⋂ _ : j < i, (fun g : GL (Fin m) F => (g : Matrix (Fin m) (Fin m) F) i j) ⁻¹'
        {x | valuation F x < 1}) := by
  ext g
  simp only [iwahori, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq,
    mem_unitGL_iff, and_assoc]

/- English proof (translation)
Rewrite using `[iwahori_eq]`. Use `(IsClopen.inter ?_ ?_).inter ?_` and prove the remaining obligations. Apply the tactic sequence `exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => isClopen_le_one.preimage (continuous_entry i j)`. Apply the tactic sequence `exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => isClopen_le_one.preimage (continuous_inv_entry i j)`. Apply the tactic sequence `exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => isClopen_iInter_of_finite fun _ => isClopen_lt_one.preimage (continuous_entry i j)`.
-/
theorem isClopen_iwahori : IsClopen (iwahori (m := m) F) := by
  rw [iwahori_eq]
  refine (IsClopen.inter ?_ ?_).inter ?_
  · exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      isClopen_le_one.preimage (continuous_entry i j)
  · exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      isClopen_le_one.preimage (continuous_inv_entry i j)
  · exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      isClopen_iInter_of_finite fun _ => isClopen_lt_one.preimage (continuous_entry i j)

/- English proof (translation)
Establish `h : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => {x : F | valuation F x ≤ 1})` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall F 1`. Establish `e : {M : Matrix (Fin m) (Fin m) F | ∀ i j, valuation F (M i j) ≤ 1} = (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => {x : F | valuation F x ≤ 1})`. Use extensionality with `M`. Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem isCompact_integral : IsCompact {M : Matrix (Fin m) (Fin m) F | ∀ i j, valuation F (M i j) ≤ 1} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
      {x : F | valuation F x ≤ 1}) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      IsNonarchimedeanLocalField.isCompact_closedBall F 1
  have e : {M : Matrix (Fin m) (Fin m) F | ∀ i j, valuation F (M i j) ≤ 1} =
      (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
        {x : F | valuation F x ≤ 1}) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [e]
  exact h

/- English proof (translation)
Establish `hK` using `isCompact_integral (F := F) (m := m)`. Establish `hK'` using `hK.image MulOpposite.continuous_op`. Establish `hc` using `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin m) (Fin m) F)).isCompact_preimage (hK.prod hK')`. Use `hc.of_isClosed_subset isClopen_iwahori.isClosed fun g hg => ?_` and prove the remaining obligations. Establish `h` using `(mem_unitGL_iff g).1 hg.1`.

Conclude with `⟨h.1, ⟨_, h.2, rfl⟩⟩`.
-/
theorem isCompact_iwahori : IsCompact (iwahori (m := m) F) := by
  have hK := isCompact_integral (F := F) (m := m)
  have hK' := hK.image MulOpposite.continuous_op
  have hc := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin m) (Fin m) F)).isCompact_preimage (hK.prod hK')
  refine hc.of_isClosed_subset isClopen_iwahori.isClosed fun g hg => ?_
  have h := (mem_unitGL_iff g).1 hg.1
  exact ⟨h.1, ⟨_, h.2, rfl⟩⟩

end Top

section Ext

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [FiniteDimensional k E] in
/- English proof (translation)
Rewrite using `[← (valuation E).vle_iff_le, ← (valuation k).vle_iff_le, ValuativeExtension.vle_iff_vle]`.
-/
theorem val_algebraMap_le_iff (a b : k) :
    valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) ↔
      valuation k a ≤ valuation k b := by
  rw [← (valuation E).vle_iff_le, ← (valuation k).vle_iff_le, ValuativeExtension.vle_iff_vle]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [FiniteDimensional k E] in
/- English proof (translation)
Simplify using `using val_algebraMap_le_iff (E := E) a 1`.
-/
theorem val_algebraMap_le_one_iff (a : k) :
    valuation E (algebraMap k E a) ≤ 1 ↔ valuation k a ≤ 1 := by
  simpa using val_algebraMap_le_iff (E := E) a 1

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [FiniteDimensional k E] in
/- English proof (translation)
Use `val_algebraMap_le_iff (E := E) 1 a` as an intermediate fact. Simplify using `only [map_one] at this`. Rewrite using `[← not_le, ← not_le, this]`.
-/
theorem val_algebraMap_lt_one_iff (a : k) :
    valuation E (algebraMap k E a) < 1 ↔ valuation k a < 1 := by
  have := val_algebraMap_le_iff (E := E) 1 a
  simp only [map_one] at this
  rw [← not_le, ← not_le, this]

/- English proof (translation)
Establish `h` using `(GroundTheory.LocalField.isIntegral_iff k E x).2 hx`. Conclude with `(GroundTheory.LocalField.isIntegral_iff k E (τ x)).1 (h.map ((τ : E →ₐ[k] E).restrictScalars 𝒪[k]))`.
-/
theorem val_aut_le_one (τ : E ≃ₐ[k] E) {x : E} (hx : valuation E x ≤ 1) :
    valuation E (τ x) ≤ 1 := by
  have h := (GroundTheory.LocalField.isIntegral_iff k E x).2 hx
  exact (GroundTheory.LocalField.isIntegral_iff k E (τ x)).1
    (h.map ((τ : E →ₐ[k] E).restrictScalars 𝒪[k]))

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_lt]`. Establish `hb : b ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`.

Establish `hτb : τ b ≠ 0` using `by simpa using hb`. Establish `hτa : τ a ≠ 0`. Introduce `h0`. Rewrite `hc` using `[h0, map_zero]`. Conclude with `hτb ((valuation E).zero_iff.1 (le_zero_iff.1 hc))`.

Establish `ha : a ≠ 0` using `by simpa using hτa`. Establish `h1 : valuation E (τ b / τ a) ≤ 1`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ hc zero_le'`. Establish `h2` using `val_aut_le_one τ⁻¹ h1`.

Establish `h3 : τ⁻¹ (τ b / τ a) = b / a`. Rewrite using `[map_div₀]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[h3, map_div₀]`. Establish `h4 : valuation E a ≠ 0` using `(valuation E).ne_zero_iff.2 ha`.

Conclude with `absurd ((div_le_one₀ (zero_lt_iff.2 h4)).1 h2) (not_le.2 h)`.
-/
theorem val_aut_strictMono (τ : E ≃ₐ[k] E) {a b : E} (h : valuation E a < valuation E b) :
    valuation E (τ a) < valuation E (τ b) := by
  by_contra hc
  rw [not_lt] at hc
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h
  have hτb : τ b ≠ 0 := by simpa using hb
  have hτa : τ a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact hτb ((valuation E).zero_iff.1 (le_zero_iff.1 hc))
  have ha : a ≠ 0 := by simpa using hτa
  have h1 : valuation E (τ b / τ a) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ hc zero_le'
  have h2 := val_aut_le_one τ⁻¹ h1
  have h3 : τ⁻¹ (τ b / τ a) = b / a := by
    rw [map_div₀]
    simp
  rw [h3, map_div₀] at h2
  have h4 : valuation E a ≠ 0 := (valuation E).ne_zero_iff.2 ha
  exact absurd ((div_le_one₀ (zero_lt_iff.2 h4)).1 h2) (not_le.2 h)

/- English proof (translation)
Introduce `h`. Establish `hp : ∀ i : ℕ, (τ ^ (i + 1)) y = τ ((τ ^ i) y)` using `fun i => by`. Rewrite using `[pow_succ']`. Both sides reduce to the same expression. Establish `hstep : ∀ i : ℕ, valuation E ((τ ^ i) y) < valuation E ((τ ^ (i + 1)) y)`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simpa using h`. Consider the case `succ i ih`. Use `val_aut_strictMono τ ih` as an intermediate fact.

Rewrite using `[hp (i + 1)]`. Use `conv_lhs => rw [hp i]`. Conclude with `this`. Establish `hlt : ∀ i : ℕ, valuation E y < valuation E ((τ ^ (i + 1)) y)`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => simpa using h`. Consider the case `succ i ih => exact ih.trans (hstep (i + 1))`. Establish `hpos : 0 < orderOf τ` using `orderOf_pos τ`. Use `hlt (orderOf τ - 1)` as an intermediate fact.

Rewrite `this` using `[Nat.sub_add_cancel hpos, pow_orderOf_eq_one]`. Simplify using `at this`.
-/
theorem not_val_lt_val_aut [IsGalois k E] (τ : E ≃ₐ[k] E) (y : E) :
    ¬ valuation E y < valuation E (τ y) := by
  intro h
  have hp : ∀ i : ℕ, (τ ^ (i + 1)) y = τ ((τ ^ i) y) := fun i => by
    rw [pow_succ']
    rfl
  have hstep : ∀ i : ℕ, valuation E ((τ ^ i) y) < valuation E ((τ ^ (i + 1)) y) := by
    intro i
    induction i with
    | zero => simpa using h
    | succ i ih =>
      have := val_aut_strictMono τ ih
      rw [hp (i + 1)]
      conv_lhs => rw [hp i]
      exact this
  have hlt : ∀ i : ℕ, valuation E y < valuation E ((τ ^ (i + 1)) y) := by
    intro i
    induction i with
    | zero => simpa using h
    | succ i ih => exact ih.trans (hstep (i + 1))
  have hpos : 0 < orderOf τ := orderOf_pos τ
  have := hlt (orderOf τ - 1)
  rw [Nat.sub_add_cancel hpos, pow_orderOf_eq_one] at this
  simp at this

/- English proof (translation)
Use `le_antisymm (not_lt.1 (not_val_lt_val_aut τ x)) (not_lt.1 ?_)` and prove the remaining obligations. Use `not_val_lt_val_aut τ⁻¹ (τ x)` as an intermediate fact. Simplify using `using this`.
-/
theorem val_aut [IsGalois k E] (τ : E ≃ₐ[k] E) (x : E) : valuation E (τ x) = valuation E x := by
  refine le_antisymm (not_lt.1 (not_val_lt_val_aut τ x)) (not_lt.1 ?_)
  have := not_val_lt_val_aut τ⁻¹ (τ x)
  simpa using this

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [FiniteDimensional k E] in
/- English proof (translation)
Establish `h1 : ∀ i j, ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = algebraMap k E ((g : Matrix (Fin n) (Fin n) k) i j)` using `fun _ _ => rfl`. Establish `h2 : ∀ i j, (((incl g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = algebraMap k E (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j)`. Introduce `i j`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.

Simplify using `only [iwahori, Set.mem_setOf_eq, mem_unitGL_iff, h1, h2, val_algebraMap_le_one_iff, val_algebraMap_lt_one_iff]`.
-/
theorem incl_mem_iff {n : ℕ} (g : GL (Fin n) k) :
    incl g ∈ iwahori (m := n) E ↔ g ∈ iwahori (m := n) k := by
  have h1 : ∀ i j, ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      algebraMap k E ((g : Matrix (Fin n) (Fin n) k) i j) := fun _ _ => rfl
  have h2 : ∀ i j, (((incl g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      algebraMap k E (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) := by
    intro i j
    rw [← map_inv]
    rfl
  simp only [iwahori, Set.mem_setOf_eq, mem_unitGL_iff, h1, h2, val_algebraMap_le_one_iff,
    val_algebraMap_lt_one_iff]

/- English proof (translation)
Establish `h1 : ∀ i j, ((sigmaGL τ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = τ ((g : Matrix (Fin n) (Fin n) E) i j)` using `fun _ _ => rfl`. Establish `h2 : ∀ i j, (((sigmaGL τ g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = τ (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)`. Introduce `i j`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.

Simplify using `only [iwahori, Set.mem_setOf_eq, mem_unitGL_iff, h1, h2, val_aut]`.
-/
theorem sigma_mem_iff [IsGalois k E] {n : ℕ} (τ : E ≃ₐ[k] E) (g : GL (Fin n) E) :
    sigmaGL τ g ∈ iwahori (m := n) E ↔ g ∈ iwahori (m := n) E := by
  have h1 : ∀ i j, ((sigmaGL τ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      τ ((g : Matrix (Fin n) (Fin n) E) i j) := fun _ _ => rfl
  have h2 : ∀ i j, (((sigmaGL τ g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      τ (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    rw [← map_inv]
    rfl
  simp only [iwahori, Set.mem_setOf_eq, mem_unitGL_iff, h1, h2, val_aut]

end Ext

/- English proof (translation)
Use `⟨fun F _ _ _ _ n => ⟨exists_subgroup, isClopen_iwahori.isOpen, isCompact_iwahori, torusO_subset⟩, fun k E _ _ _ _ _ _ _ _ _ _ _ _ _ n => ⟨incl_mem_iff, fun τ g => sigma_mem_iff τ g⟩⟩` and prove the remaining obligations.
-/
theorem iwahori_compact_open_galois : PositivityTheory.Rg.Tf.Loc.I0 := by
  refine ⟨fun F _ _ _ _ n => ⟨exists_subgroup, isClopen_iwahori.isOpen, isCompact_iwahori,
    torusO_subset⟩, fun k E _ _ _ _ _ _ _ _ _ _ _ _ _ n =>
      ⟨incl_mem_iff, fun τ g => sigma_mem_iff τ g⟩⟩

end GlobalTheory.CompanionTheory.TfLoc.Iw
