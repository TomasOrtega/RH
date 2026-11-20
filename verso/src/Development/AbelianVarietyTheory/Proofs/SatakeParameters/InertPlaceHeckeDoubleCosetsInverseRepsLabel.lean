import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrdersStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitarStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertAtOfUniqueUnramifiedPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTensorInertAdicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleCStatement

noncomputable section

namespace GlobalTheory.InertDoubleCoset

open Formalism.UG
open scoped Matrix

section Abstract

variable {G Γ : Type} [Group G] [Group Γ] {φ : G →* Γ} {S : Subgroup G} {Kp : G → Prop} {U K₀ : Subgroup Γ}

/- English proof (translation)
Take `⟨k₁, hk₁, k₂, hk₂, e⟩` from `h`. Take `⟨a, ha, rfl⟩` from `hsurj k₁ hk₁.1`. Take `⟨b, hb, rfl⟩` from `hsurj k₂ hk₂.1`. Conclude with `⟨a, b, (hlev a ha).2 hk₁.2, ha, (hlev b hb).2 hk₂.2, hb, hinj _ hg' _ (mul_mem (mul_mem ha hg) hb) (by rw [e, map_mul, map_mul])⟩`.
-/
theorem lift_dc (hinj : ∀ g ∈ S, ∀ g' ∈ S, φ g = φ g' → g = g') (hsurj : ∀ u ∈ U, ∃ g ∈ S, φ g = u)
    (hlev : ∀ g ∈ S, Kp g ↔ φ g ∈ K₀) {g g' : G} (hg : g ∈ S) (hg' : g' ∈ S)
    (h : ∃ k₁ ∈ U ⊓ K₀, ∃ k₂ ∈ U ⊓ K₀, φ g' = k₁ * φ g * k₂) :
    ∃ a b, Kp a ∧ a ∈ S ∧ Kp b ∧ b ∈ S ∧ g' = a * g * b := by
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := h
  obtain ⟨a, ha, rfl⟩ := hsurj k₁ hk₁.1
  obtain ⟨b, hb, rfl⟩ := hsurj k₂ hk₂.1
  exact ⟨a, b, (hlev a ha).2 hk₁.2, ha, (hlev b hb).2 hk₂.2, hb,
    hinj _ hg' _ (mul_mem (mul_mem ha hg) hb) (by rw [e, map_mul, map_mul])⟩

/- English proof (translation)
Set `K : Subgroup G` to `S ⊓ K₀.comap φ`. Establish `hKm : ∀ k, k ∈ K ↔ Kp k ∧ k ∈ S` using `fun k => ⟨fun h => ⟨(hlev k h.1).2 h.2, h.1⟩, fun h => ⟨h.2, (hlev k h.2).1 h.1⟩⟩`. Simplify using `only [← hKm]`. Set `C : Set (G ⧸ K)` to `{c | ∃ a ∈ K, ∃ b ∈ K, c.out = a * g * b}`. Establish `hCS : ∀ c ∈ C, c.out ∈ S`.

Introduce and unpack `c ⟨a, ha, b, hb, e⟩`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem ha.1 hg) hb.1`. Establish `hC : C.Finite`. Use `Set.Finite.of_finite_image (f := fun c : G ⧸ K => (QuotientGroup.mk (φ c.out) : Γ ⧸ K₀)) ((P.finite_cosets_in_doset hK (φ g)).subset ?_) ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨c, ⟨a, ha, b, hb, e⟩, rfl⟩`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K₀ (φ c.out)`. Use `⟨⟨φ a, ha.2⟩, ⟨φ b, hb.2⟩ * k, ?_⟩` and prove the remaining obligations. Use `hk.trans ?_` and prove the remaining obligations. Simplify using `only [e, map_mul, Subgroup.coe_mul, mul_assoc]`.

Introduce `c hc c' hc' e`. Establish `h1 : (φ c.out)⁻¹ * φ c'.out ∈ K₀` using `QuotientGroup.eq.1 e`. Rewrite using `[← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]`. Use `⟨S.mul_mem (S.inv_mem (hCS c hc)) (hCS c' hc'), ?_⟩` and prove the remaining obligations. Use `show φ _ ∈ K₀`.

Rewrite using `[map_mul, map_inv]` and apply the resulting hypothesis. Use `⟨hC.toFinset.image Quotient.out, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hγ`. Conclude with `hCS c (hC.mem_toFinset.1 hc)`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hγ`.

Conclude with `hC.mem_toFinset.1 hc`. Introduce and unpack `x ⟨a, ha, b, hb, rfl⟩`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K (a * g * b)`. Use `⟨(QuotientGroup.mk (a * g * b) : G ⧸ K).out, ⟨Finset.mem_image.2 ⟨_, hC.mem_toFinset.2 ⟨a, ha, b * k, mul_mem hb k.2, by rw [hk, mul_assoc _ b]⟩, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `QuotientGroup.eq.1 (QuotientGroup.out_eq' _)`.

Introduce and unpack `γ ⟨hγ, h⟩`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hγ`. Rewrite using `[← QuotientGroup.eq.2 h, QuotientGroup.out_eq']`.
-/
theorem exists_reps (hlev : ∀ g ∈ S, Kp g ↔ φ g ∈ K₀) (hK : IsCommensurated K₀) {g : G} (hg : g ∈ S) :
    ∃ R : Finset G, (∀ γ ∈ R, γ ∈ S) ∧
      (∀ γ ∈ R, ∃ k₁, (Kp k₁ ∧ k₁ ∈ S) ∧ ∃ k₂, (Kp k₂ ∧ k₂ ∈ S) ∧ γ = k₁ * g * k₂) ∧
      ∀ x, (∃ k₁, (Kp k₁ ∧ k₁ ∈ S) ∧ ∃ k₂, (Kp k₂ ∧ k₂ ∈ S) ∧ x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R ∧ Kp (γ⁻¹ * x) ∧ γ⁻¹ * x ∈ S := by
  classical
  let K : Subgroup G := S ⊓ K₀.comap φ
  have hKm : ∀ k, k ∈ K ↔ Kp k ∧ k ∈ S := fun k =>
    ⟨fun h => ⟨(hlev k h.1).2 h.2, h.1⟩, fun h => ⟨h.2, (hlev k h.2).1 h.1⟩⟩
  simp only [← hKm]
  let C : Set (G ⧸ K) := {c | ∃ a ∈ K, ∃ b ∈ K, c.out = a * g * b}
  have hCS : ∀ c ∈ C, c.out ∈ S := by
    rintro c ⟨a, ha, b, hb, e⟩
    rw [e]; exact mul_mem (mul_mem ha.1 hg) hb.1
  have hC : C.Finite := by
    refine Set.Finite.of_finite_image (f := fun c : G ⧸ K => (QuotientGroup.mk (φ c.out) : Γ ⧸ K₀))
      ((P.finite_cosets_in_doset hK (φ g)).subset ?_) ?_
    · rintro _ ⟨c, ⟨a, ha, b, hb, e⟩, rfl⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₀ (φ c.out)
      refine ⟨⟨φ a, ha.2⟩, ⟨φ b, hb.2⟩ * k, ?_⟩
      refine hk.trans ?_
      simp only [e, map_mul, Subgroup.coe_mul, mul_assoc]
    · intro c hc c' hc' e
      have h1 : (φ c.out)⁻¹ * φ c'.out ∈ K₀ := QuotientGroup.eq.1 e
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      refine ⟨S.mul_mem (S.inv_mem (hCS c hc)) (hCS c' hc'), ?_⟩
      show φ _ ∈ K₀
      rwa [map_mul, map_inv]
  refine ⟨hC.toFinset.image Quotient.out, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    exact hCS c (hC.mem_toFinset.1 hc)
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    exact hC.mem_toFinset.1 hc
  · rintro x ⟨a, ha, b, hb, rfl⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (a * g * b)
    refine ⟨(QuotientGroup.mk (a * g * b) : G ⧸ K).out, ⟨Finset.mem_image.2 ⟨_, hC.mem_toFinset.2
      ⟨a, ha, b * k, mul_mem hb k.2, by rw [hk, mul_assoc _ b]⟩, rfl⟩, ?_⟩, ?_⟩
    · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    · rintro γ ⟨hγ, h⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hγ
      rw [← QuotientGroup.eq.2 h, QuotientGroup.out_eq']

end Abstract

section Rings

variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Use `⟨fun i j => (y.1 i j).2, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `((y⁻¹).1 i j).2`.

Introduce and unpack `⟨h1, h2⟩`. Establish `inj : Function.Injective (RingHom.mapMatrix (m` using `Fin n) O.subtype) := Matrix.map_injective Subtype.val_injective`. Use `⟨⟨Matrix.of fun i j => ⟨x.1 i j, h1 i j⟩, Matrix.of fun i j => ⟨(x⁻¹).1 i j, h2 i j⟩, inj ?_, inj ?_⟩, Units.ext rfl⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_one]`. Conclude with `x.mul_inv`.

Rewrite using `[map_mul, map_one]`. Conclude with `x.inv_mul`.
-/
theorem mem_range_iff (O : Subring A) (x : GL (Fin n) A) :
    x ∈ (bc (n := Fin n) O.subtype).range ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨fun i j => (y.1 i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((y⁻¹).1 i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) O.subtype) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨x.1 i j, h1 i j⟩, Matrix.of fun i j => ⟨(x⁻¹).1 i j, h2 i j⟩, inj ?_, inj ?_⟩,
      Units.ext rfl⟩
    · rw [map_mul, map_one]; exact x.mul_inv
    · rw [map_mul, map_one]; exact x.inv_mul

/- English proof (translation)
Rewrite using `[mem_range_iff, mem_range_iff, ← map_inv]`. Conclude with `and_congr (forall₂_congr fun i j => h _) (forall₂_congr fun i j => h _)`.
-/
theorem bc_mem_range_iff (ψ : A →+* B) {O : Subring A} {O' : Subring B} (h : ∀ z, z ∈ O ↔ ψ z ∈ O')
    (x : GL (Fin n) A) :
    x ∈ (bc (n := Fin n) O.subtype).range ↔ bc ψ x ∈ (bc (n := Fin n) O'.subtype).range := by
  rw [mem_range_iff, mem_range_iff, ← map_inv]
  exact and_congr (forall₂_congr fun i j => h _) (forall₂_congr fun i j => h _)

/- English proof (translation)
Establish `hg' : cT σ g.1 * J * g.1 = J` using `hg`. Use `show cT σ (h⁻¹ * g * h).1 * J' * (h⁻¹ * g * h).1 = J'`. Establish `e : h.1 * (h⁻¹ * g * h).1 = g.1 * h.1`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`.

Use `group`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hh, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT σ h.1 * (cT σ g.1 * J * g.1) * h.1 := by`.

Rewrite using `[e, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J' := by rw [hg', hh]`.
-/
theorem conj_mem_UJ (σ : A →+* A) {J J' : Matrix (Fin n) (Fin n) A} {h : GL (Fin n) A}
    (hh : cT σ h.1 * J * h.1 = J') {g : GL (Fin n) A} (hg : g ∈ UJ σ J) : h⁻¹ * g * h ∈ UJ σ J' := by
  have hg' : cT σ g.1 * J * g.1 = J := hg
  show cT σ (h⁻¹ * g * h).1 * J' * (h⁻¹ * g * h).1 = J'
  have e : h.1 * (h⁻¹ * g * h).1 = g.1 * h.1 := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  calc _ = cT σ (h.1 * (h⁻¹ * g * h).1) * J * (h.1 * (h⁻¹ * g * h).1) := by
        rw [← hh, cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ h.1 * (cT σ g.1 * J * g.1) * h.1 := by
        rw [e, cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg', hh]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hh, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem inv_frame (σ : A →+* A) {J J' : Matrix (Fin n) (Fin n) A} {h : GL (Fin n) A}
    (hh : cT σ h.1 * J * h.1 = J') : cT σ (h⁻¹).1 * J' * (h⁻¹).1 = J := by
  calc _ = cT σ (h.1 * (h⁻¹).1) * J * (h.1 * (h⁻¹).1) := by
        rw [← hh, cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Use `Final.BCMem A B (Fin n) σ σ' ψ (RingHom.ext h) 1 g hg` as an intermediate fact. Rewrite `this` using `[Matrix.map_one _ (map_zero ψ) (map_one ψ)]`. Then use the resulting hypothesis.
-/
theorem bc_mem_UJ_one {σ : A →+* A} {σ' : B →+* B} (ψ : A →+* B) (h : ∀ z, ψ (σ z) = σ' (ψ z))
    {g : GL (Fin n) A} (hg : g ∈ UJ σ 1) : bc ψ g ∈ UJ σ' (1 : Matrix (Fin n) (Fin n) B) := by
  have := Final.BCMem A B (Fin n) σ σ' ψ (RingHom.ext h) 1 g hg
  rwa [Matrix.map_one _ (map_zero ψ) (map_one ψ)] at this

end Rings

section Local

open IsDedekindDomain NumberField

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {σ : v.adicCompletion K →+* v.adicCompletion K} {n : ℕ}

/- English proof (translation)
Take `⟨a, -, k₁, hk₁, k₂, hk₂, e⟩` from `Final.CartanDecomp K v n ϖ (P.cartan_unif_lt_one K v ϖ hϖ).le hϖ g`. Establish `hT : ∀ k ∈ GLint (Fin n) (Ov K v), ∃ k' ∈ GLint (Fin n) (Ov K v), k'.1 = cT σ k.1` using `fun k hk => P.cartan_exists_glint _ (cT σ k.1) (cT σ (k⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one]) (fun i j => (hσ _).trans_le (P.cartan_entries_of_mem _ k hk j i)) (fun i j => (hσ _).trans_le (P.cartan_entries_of_mem _ _ (inv_mem hk) j i))`. Take `⟨l₁, hl₁, e₁⟩` from `hT k₁ hk₁`. Take `⟨l₂, hl₂, e₂⟩` from `hT k₂ hk₂`. Establish `hd : cT σ (diagPow K v ϖ a) = diagPow K v ϖ a`.

Unfold `cT diagPow`. Rewrite using `[Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]`. Simplify using `only [map_zpow₀, hϖσ]`. Establish `hg' : cT σ g.1 * 1 * g.1 = 1` using `hg`. Rewrite `hg'` using `[Matrix.mul_one]`.

Use `⟨l₂ * k₁⁻¹, mul_mem hl₂ (inv_mem hk₁), k₂⁻¹ * l₁, mul_mem (inv_mem hk₂) hl₁, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.inv_eq_of_mul_eq_one_left hg']`. Simplify using `only [Units.val_mul]`. Rewrite using `[e, cT_mul, cT_mul, hd, ← e₁, ← e₂]`. Simplify using `only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]`.
-/
theorem inv_mem_GL_dc (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {ϖ : v.adicCompletion K} (hϖσ : σ ϖ = ϖ)
    (hϖ : IsUnifV K v ϖ) {g : GL (Fin n) (v.adicCompletion K)}
    (hg : g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K))) :
    ∃ h ∈ GLint (Fin n) (Ov K v), ∃ k ∈ GLint (Fin n) (Ov K v), g⁻¹ = h * g * k := by
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Final.CartanDecomp K v n ϖ (P.cartan_unif_lt_one K v ϖ hϖ).le hϖ g
  have hT : ∀ k ∈ GLint (Fin n) (Ov K v), ∃ k' ∈ GLint (Fin n) (Ov K v), k'.1 = cT σ k.1 := fun k hk =>
    P.cartan_exists_glint _ (cT σ k.1) (cT σ (k⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one])
      (fun i j => (hσ _).trans_le (P.cartan_entries_of_mem _ k hk j i))
      (fun i j => (hσ _).trans_le (P.cartan_entries_of_mem _ _ (inv_mem hk) j i))
  obtain ⟨l₁, hl₁, e₁⟩ := hT k₁ hk₁
  obtain ⟨l₂, hl₂, e₂⟩ := hT k₂ hk₂
  have hd : cT σ (diagPow K v ϖ a) = diagPow K v ϖ a := by
    unfold cT diagPow
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    simp only [map_zpow₀, hϖσ]
  have hg' : cT σ g.1 * 1 * g.1 = 1 := hg
  rw [Matrix.mul_one] at hg'
  refine ⟨l₂ * k₁⁻¹, mul_mem hl₂ (inv_mem hk₁), k₂⁻¹ * l₁, mul_mem (inv_mem hk₂) hl₁, Units.ext ?_⟩
  rw [Units.inv_eq_of_mul_eq_one_left hg']
  simp only [Units.val_mul]
  rw [e, cT_mul, cT_mul, hd, ← e₁, ← e₂]
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]

/- English proof (translation)
Take `⟨k₁, hk₁, k₂, hk₂, e⟩` from `hg`. Take `⟨l₁, hl₁, l₂, hl₂, e'⟩` from `hg'`. Establish `hπv : Valued.v π ≠ 0` using `(Valuation.ne_zero_iff _).2 hπ`. Establish `hπ' : π' ≠ 0` using `(Valuation.ne_zero_iff _).1 (hv ▸ hπv)`. Establish `hint : ∀ u : v.adicCompletion K, Valued.v u = 1 → ∀ i j, Matrix.diagonal (fun i => u ^ d i) i j ∈ Ov K v` using `fun u hu i j => by`.

Rewrite using `[Matrix.diagonal_apply]`. Use `split_ifs`. Rewrite using `[P.cartan_mem_Ov, map_zpow₀, hu, one_zpow]`. Conclude with `zero_mem _`. Take `⟨u, hu, eu⟩` from `P.cartan_exists_glint (Ov K v) (Matrix.diagonal fun i => (π' / π) ^ d i) (Matrix.diagonal fun i => (π / π') ^ d i) (by`.

Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[← mul_zpow, div_mul_div_cancel₀ hπ, div_self hπ', one_zpow])`. Use the proof step `(hint _ (by rw [map_div₀, hv, div_self hπv])) (hint _ (by rw [map_div₀, hv, div_self hπv]))`.

Use `⟨l₁ * u * k₁⁻¹, mul_mem (mul_mem hl₁ hu) (inv_mem hk₁), k₂⁻¹ * l₂, mul_mem (inv_mem hk₂) hl₂, Units.ext ?_⟩` and prove the remaining obligations. Establish `ed : Matrix.diagonal (fun i => π' ^ d i) = u.1 * Matrix.diagonal (fun i => π ^ d i)`. Rewrite using `[eu, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[← mul_zpow, div_mul_cancel₀ _ hπ]`. Simplify using `only [Units.val_mul]`. Rewrite using `[e, e', ed]`. Simplify using `only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]`.
-/
theorem same_dc {π π' : v.adicCompletion K} (hπ : π ≠ 0) (hv : Valued.v π' = Valued.v π) (d : Fin n → ℤ)
    {g g' : GL (Fin n) (v.adicCompletion K)}
    (hg : ∃ k₁ ∈ GLint (Fin n) (Ov K v), ∃ k₂ ∈ GLint (Fin n) (Ov K v),
      g.1 = k₁.1 * Matrix.diagonal (fun i => π ^ d i) * k₂.1)
    (hg' : ∃ k₁ ∈ GLint (Fin n) (Ov K v), ∃ k₂ ∈ GLint (Fin n) (Ov K v),
      g'.1 = k₁.1 * Matrix.diagonal (fun i => π' ^ d i) * k₂.1) :
    ∃ h ∈ GLint (Fin n) (Ov K v), ∃ k ∈ GLint (Fin n) (Ov K v), g' = h * g * k := by
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hg
  obtain ⟨l₁, hl₁, l₂, hl₂, e'⟩ := hg'
  have hπv : Valued.v π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ
  have hπ' : π' ≠ 0 := (Valuation.ne_zero_iff _).1 (hv ▸ hπv)
  have hint : ∀ u : v.adicCompletion K, Valued.v u = 1 → ∀ i j,
      Matrix.diagonal (fun i => u ^ d i) i j ∈ Ov K v := fun u hu i j => by
    rw [Matrix.diagonal_apply]
    split_ifs
    · rw [P.cartan_mem_Ov, map_zpow₀, hu, one_zpow]
    · exact zero_mem _
  obtain ⟨u, hu, eu⟩ := P.cartan_exists_glint (Ov K v) (Matrix.diagonal fun i => (π' / π) ^ d i)
    (Matrix.diagonal fun i => (π / π') ^ d i)
    (by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← mul_zpow, div_mul_div_cancel₀ hπ, div_self hπ', one_zpow])
    (hint _ (by rw [map_div₀, hv, div_self hπv])) (hint _ (by rw [map_div₀, hv, div_self hπv]))
  refine ⟨l₁ * u * k₁⁻¹, mul_mem (mul_mem hl₁ hu) (inv_mem hk₁), k₂⁻¹ * l₂, mul_mem (inv_mem hk₂) hl₂, Units.ext ?_⟩
  have ed : Matrix.diagonal (fun i => π' ^ d i) = u.1 * Matrix.diagonal (fun i => π ^ d i) := by
    rw [eu, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← mul_zpow, div_mul_cancel₀ _ hπ]
  simp only [Units.val_mul]
  rw [e, e', ed]
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]

end Local

section CM

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

/- English proof (translation)
Use `GlobalTheory.T.isInertAt_of_unique_unramified_prime E v P (fun x hx => (hP x hx).trans (not_congr ?_)) hu` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.mem_integralFiniteAdelesTensor_iff_localOrders, ← locEmb_mem_locOrder_iff, ← mem_ordAt_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `h v` as an intermediate fact.

Rewrite `this` using `[map_mul, map_mul, he.2.1, one_mul, evF_finP_incl]`. Then use the resulting hypothesis. Introduce `h w`. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[he.2.1, one_mul, evF_finP_incl]`. Conclude with `h`. Rewrite using `[he.2.2 w hw, zero_mul]`. Conclude with `zero_mem _`.
-/
theorem inert_of_idem {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    {e : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (he : IsIdemOf E v e)
    (hP : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔
      finP (maximalRealSubfield E) E (e * inclR (AF (maximalRealSubfield E)) (x : E)⁻¹) ∉ intA (maximalRealSubfield E) E))
    (hu : ∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E,
      (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) :
    IsInertAt (maximalRealSubfield E) E v P := by
  refine GlobalTheory.T.isInertAt_of_unique_unramified_prime E v P (fun x hx => (hP x hx).trans (not_congr ?_)) hu
  rw [GlobalTheory.T.mem_integralFiniteAdelesTensor_iff_localOrders, ← locEmb_mem_locOrder_iff, ← mem_ordAt_iff]
  constructor
  · intro h
    have := h v
    rwa [map_mul, map_mul, he.2.1, one_mul, evF_finP_incl] at this
  · intro h w
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [he.2.1, one_mul, evF_finP_incl]
      exact h
    · rw [he.2.2 w hw, zero_mul]
      exact zero_mem _

/- English proof (translation)
Establish `hur` using `unramified hc`. Take `⟨σ, π, hσE, hσσ, hσv, hσx, hσπ, hπ⟩` from `GlobalTheory.T.exists_complexConj_isometry_inert_completion E v P hin`. Take `⟨ψ, hψE, hψσ, hψO⟩` from `GlobalTheory.T.exists_ringEquiv_tensor_inert_adicCompletion E v P hin σ hσE hσv`. Take `⟨h, hfr, hon⟩` from `exists_orthonormal hc V v`. Take `⟨s1, s2, s3⟩` from `GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary _ E hc V v e he`.

Set `S : Subgroup (HA (AF (maximalRealSubfield E)) hc.sig V.gram)` to `MonoidHom.ker (G := HA (AF (maximalRealSubfield E)) hc.sig V.gram) ((bc (infP (maximalRealSubfield E) E)).comp (HR (AF (maximalRealSubfield E)) hc.sig V.gram).subtype) ⊓ ⨅ (w) (_ : w ≠ v), (locMat hc V w).ker`. Establish `hS : ∀ k, Supp hc V e k ↔ k ∈ S` using `fun k => by`. Use `(s1 k).trans ⟨fun h => ⟨h.1, Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h.2 w hw⟩, fun h => ⟨h.1, fun w hw => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h.2 w) hw⟩⟩` and prove the remaining obligations. Set `ψ' : LocAlg v →+* P.adicCompletion E` to `ψ`. Set `φ : HA (AF (maximalRealSubfield E)) hc.sig V.gram →* GL (Fin V.rank) (P.adicCompletion E)` to `(bc ψ').comp ((MulAut.conj h⁻¹).toMonoidHom.comp (locMat hc V v))`.

Establish `hφ : ∀ k, φ k = bc ψ' (h⁻¹ * locMat hc V v k * h)` using `fun k => rfl`. Establish `hO : ∀ z, z ∈ ordAt E v ↔ ψ' z ∈ Ov E P` using `fun z => (mem_ordAt_iff v z).trans (hψO z)`. Establish `hback : ∀ x : GL (Fin V.rank) (LocAlg v), bc (ψ.symm : P.adicCompletion E →+* LocAlg v) (bc ψ' x) = x` using `fun x => Units.ext (Matrix.ext fun i j => ψ.symm_apply_apply _)`. Establish `hback' : ∀ x : GL (Fin V.rank) (P.adicCompletion E), bc ψ' (bc (ψ.symm : P.adicCompletion E →+* LocAlg v) x) = x` using `fun x => Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)`. Establish `hmem : ∀ k, φ k ∈ UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E))` using `fun k => bc_mem_UJ_one (σ := locConj v) ψ' hψσ (conj_mem_UJ _ hon (locMat_mem hc V v k))`.

Establish `hinj : ∀ k ∈ S, ∀ k' ∈ S, φ k = φ k' → k = k'` using `fun k hk k' hk' e => by`. Use `s2 k k' ((hS k).2 hk) ((hS k').2 hk') ?_` and prove the remaining obligations. Use `congrArg (bc (ψ.symm : P.adicCompletion E →+* LocAlg v)) e` as an intermediate fact. Rewrite `this` using `[hφ, hφ, hback, hback]`. Conclude with `mul_left_cancel (mul_right_cancel this)`.

Establish `hsurj : ∀ u ∈ UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)), ∃ k ∈ S, φ k = u` using `fun u hu => by`. Establish `h1` using `bc_mem_UJ_one (σ' := locConj v) (ψ.symm : P.adicCompletion E →+* LocAlg v) (fun z => ψ.injective (by`. Rewrite using `[hψσ]`. Conclude with `(ψ.apply_symm_apply _).trans (congrArg σ (ψ.apply_symm_apply _).symm))) hu`. Take `⟨k, hk, ek⟩` from `s3 _ (conj_mem_UJ _ (inv_frame _ hon) h1)`.

Use `⟨k, (hS k).1 hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, ek, ← hback' u]`. Use `congr 1`. Rewrite using `[hback']`. Use `group`.

Establish `hlev : ∀ k ∈ S, (IsFin hc V k ∧ Stab hc V k) ↔ φ k ∈ GLint (Fin V.rank) (Ov E P)` using `fun k hk => by`. Establish `h1` using `(s1 k).1 ((hS k).2 hk)`. Rewrite using `[and_iff_right h1.1, GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral _ E hc V v h hfr k h1.2]`. Conclude with `bc_mem_range_iff ψ' hO _`. Establish `hdiv : ∀ (ϖ : 𝓞 E) (d : Fin V.rank → ℤ) k, ϖ ∉ P.asIdeal ^ 2 → DivG hc V e (ϖ : E) d k → ∃ k₁ ∈ GLint (Fin V.rank) (Ov E P), ∃ k₂ ∈ GLint (Fin V.rank) (Ov E P), (φ k).1 = k₁.1 * Matrix.diagonal (fun i => algebraMap E (P.adicCompletion E) ϖ ^ d i) * k₂.1`.

Introduce `ϖ d k h2 hd`. Establish `h0 : (ϖ : E) ≠ 0` using `fun h0 => h2 (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)`. Take `⟨k₁, hk₁, k₂, hk₂, ek⟩` from `GlobalTheory.T.localMatrix_doubleCoset_of_elementaryDivisors _ E hc V v e h ϖ d k he hfr h0 hd`. Use `⟨bc ψ' k₁, (bc_mem_range_iff ψ' hO _).1 hk₁, bc ψ' k₂, (bc_mem_range_iff ψ' hO _).1 hk₂, ?_⟩` and prove the remaining obligations. Use `show (h⁻¹ * locMat hc V v k * h).1.map ψ' = k₁.1.map ψ' * _ * k₂.1.map ψ'`.

Rewrite using `[ek, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero ψ')]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Conclude with `(hψE _).trans (map_zpow₀ _ _ _)`. Establish `hval : ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → Valued.v (algebraMap E (P.adicCompletion E) ϖ) = WithZero.exp (-1 : ℤ)` using `fun ϖ h1 h2 => by`.

Rewrite using `[GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.UnramCompletion.intValuation_eq_of_notMem_sq P h1 h2]`. Conclude with `HeightOneSpectrum.valuation_of_algebraMap P ϖ`. Establish `hgS` using `(hS g).1 hg`. Simplify using `only [hS]`. Use `⟨fun k hk => hk.1, ?_, exists_reps hlev (Final.GLintComm E P V.rank) hgS, ?_⟩` and prove the remaining obligations.

Take `⟨a, ha, b, hb, e⟩` from `inv_mem_GL_dc hσv hσπ hπ (hmem g)`. Conclude with `lift_dc hinj hsurj hlev hgS (inv_mem hgS) (GlobalTheory.T.unitary_mem_integralUnitary_doubleCoset_of_GLn_doubleCoset E P σ _ hσσ hσv hσx _ (hmem g) _ (hmem g⁻¹) a ha b hb (by rw [map_inv, e]))`. Introduce `ϖ ϖ' d g' h1 h2 h1' h2' hg' hd hd'`. Establish `hv` using `hval ϖ h1 h2`. Take `⟨a, ha, b, hb, e⟩` from `same_dc (fun h0 => by rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm) ((hval ϖ' h1' h2').trans hv.symm) d (hdiv ϖ d g h2 hd) (hdiv ϖ' d g' h2' hd')`.

Conclude with `lift_dc hinj hsurj hlev hgS hg' (GlobalTheory.T.unitary_mem_integralUnitary_doubleCoset_of_GLn_doubleCoset E P σ _ hσσ hσv hσx _ (hmem g) _ (hmem g') a ha b hb e)`.
-/
theorem core (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    {e : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (he : IsIdemOf E v e)
    (hin : IsInertAt (maximalRealSubfield E) E v P) (g : HA (AF (maximalRealSubfield E)) hc.sig V.gram)
    (hg : Supp hc V e g) :
    (∀ k, Supp hc V e k → IsFin hc V k) ∧
    (∃ a b, (IsFin hc V a ∧ Stab hc V a) ∧ Supp hc V e a ∧ (IsFin hc V b ∧ Stab hc V b) ∧ Supp hc V e b ∧
      g⁻¹ = a * g * b) ∧
    (∃ R : Finset (HA (AF (maximalRealSubfield E)) hc.sig V.gram), (∀ γ ∈ R, Supp hc V e γ) ∧
      (∀ γ ∈ R, ∃ k₁, ((IsFin hc V k₁ ∧ Stab hc V k₁) ∧ Supp hc V e k₁) ∧
        ∃ k₂, ((IsFin hc V k₂ ∧ Stab hc V k₂) ∧ Supp hc V e k₂) ∧ γ = k₁ * g * k₂) ∧
      ∀ x, (∃ k₁, ((IsFin hc V k₁ ∧ Stab hc V k₁) ∧ Supp hc V e k₁) ∧
        ∃ k₂, ((IsFin hc V k₂ ∧ Stab hc V k₂) ∧ Supp hc V e k₂) ∧ x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R ∧ (IsFin hc V (γ⁻¹ * x) ∧ Stab hc V (γ⁻¹ * x)) ∧ Supp hc V e (γ⁻¹ * x)) ∧
    ∀ (ϖ ϖ' : 𝓞 E) (d : Fin V.rank → ℤ) g', ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal →
      ϖ' ∉ P.asIdeal ^ 2 → Supp hc V e g' → DivG hc V e (ϖ : E) d g → DivG hc V e (ϖ' : E) d g' →
      ∃ a b, (IsFin hc V a ∧ Stab hc V a) ∧ Supp hc V e a ∧ (IsFin hc V b ∧ Stab hc V b) ∧ Supp hc V e b ∧
        g' = a * g * b := by
  have hur := unramified hc
  obtain ⟨σ, π, hσE, hσσ, hσv, hσx, hσπ, hπ⟩ := GlobalTheory.T.exists_complexConj_isometry_inert_completion E v P hin
  obtain ⟨ψ, hψE, hψσ, hψO⟩ := GlobalTheory.T.exists_ringEquiv_tensor_inert_adicCompletion E v P hin σ hσE hσv
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary _ E hc V v e he
  let S : Subgroup (HA (AF (maximalRealSubfield E)) hc.sig V.gram) :=
    MonoidHom.ker (G := HA (AF (maximalRealSubfield E)) hc.sig V.gram)
      ((bc (infP (maximalRealSubfield E) E)).comp (HR (AF (maximalRealSubfield E)) hc.sig V.gram).subtype) ⊓
      ⨅ (w) (_ : w ≠ v), (locMat hc V w).ker
  have hS : ∀ k, Supp hc V e k ↔ k ∈ S := fun k => by
    refine (s1 k).trans ⟨fun h => ⟨h.1, Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h.2 w hw⟩,
      fun h => ⟨h.1, fun w hw => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h.2 w) hw⟩⟩
  let ψ' : LocAlg v →+* P.adicCompletion E := ψ
  let φ : HA (AF (maximalRealSubfield E)) hc.sig V.gram →* GL (Fin V.rank) (P.adicCompletion E) :=
    (bc ψ').comp ((MulAut.conj h⁻¹).toMonoidHom.comp (locMat hc V v))
  have hφ : ∀ k, φ k = bc ψ' (h⁻¹ * locMat hc V v k * h) := fun k => rfl
  have hO : ∀ z, z ∈ ordAt E v ↔ ψ' z ∈ Ov E P := fun z => (mem_ordAt_iff v z).trans (hψO z)
  have hback : ∀ x : GL (Fin V.rank) (LocAlg v), bc (ψ.symm : P.adicCompletion E →+* LocAlg v) (bc ψ' x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.symm_apply_apply _)
  have hback' : ∀ x : GL (Fin V.rank) (P.adicCompletion E),
      bc ψ' (bc (ψ.symm : P.adicCompletion E →+* LocAlg v) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have hmem : ∀ k, φ k ∈ UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)) := fun k =>
    bc_mem_UJ_one (σ := locConj v) ψ' hψσ (conj_mem_UJ _ hon (locMat_mem hc V v k))
  have hinj : ∀ k ∈ S, ∀ k' ∈ S, φ k = φ k' → k = k' := fun k hk k' hk' e => by
    refine s2 k k' ((hS k).2 hk) ((hS k').2 hk') ?_
    have := congrArg (bc (ψ.symm : P.adicCompletion E →+* LocAlg v)) e
    rw [hφ, hφ, hback, hback] at this
    exact mul_left_cancel (mul_right_cancel this)
  have hsurj : ∀ u ∈ UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)), ∃ k ∈ S, φ k = u :=
    fun u hu => by
    have h1 := bc_mem_UJ_one (σ' := locConj v) (ψ.symm : P.adicCompletion E →+* LocAlg v)
      (fun z => ψ.injective (by
        rw [hψσ]
        exact (ψ.apply_symm_apply _).trans (congrArg σ (ψ.apply_symm_apply _).symm))) hu
    obtain ⟨k, hk, ek⟩ := s3 _ (conj_mem_UJ _ (inv_frame _ hon) h1)
    refine ⟨k, (hS k).1 hk, ?_⟩
    rw [hφ, ek, ← hback' u]
    congr 1
    rw [hback']
    group
  have hlev : ∀ k ∈ S, (IsFin hc V k ∧ Stab hc V k) ↔ φ k ∈ GLint (Fin V.rank) (Ov E P) := fun k hk => by
    have h1 := (s1 k).1 ((hS k).2 hk)
    rw [and_iff_right h1.1, GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral _ E hc V v h hfr k h1.2]
    exact bc_mem_range_iff ψ' hO _
  have hdiv : ∀ (ϖ : 𝓞 E) (d : Fin V.rank → ℤ) k, ϖ ∉ P.asIdeal ^ 2 → DivG hc V e (ϖ : E) d k →
      ∃ k₁ ∈ GLint (Fin V.rank) (Ov E P), ∃ k₂ ∈ GLint (Fin V.rank) (Ov E P),
        (φ k).1 = k₁.1 * Matrix.diagonal (fun i => algebraMap E (P.adicCompletion E) ϖ ^ d i) * k₂.1 := by
    intro ϖ d k h2 hd
    have h0 : (ϖ : E) ≠ 0 := fun h0 => h2 (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
    obtain ⟨k₁, hk₁, k₂, hk₂, ek⟩ := GlobalTheory.T.localMatrix_doubleCoset_of_elementaryDivisors _ E hc V v e h ϖ d k he hfr h0 hd
    refine ⟨bc ψ' k₁, (bc_mem_range_iff ψ' hO _).1 hk₁, bc ψ' k₂, (bc_mem_range_iff ψ' hO _).1 hk₂, ?_⟩
    show (h⁻¹ * locMat hc V v k * h).1.map ψ' = k₁.1.map ψ' * _ * k₂.1.map ψ'
    rw [ek, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero ψ')]
    congr 3
    funext i
    exact (hψE _).trans (map_zpow₀ _ _ _)
  have hval : ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
      Valued.v (algebraMap E (P.adicCompletion E) ϖ) = WithZero.exp (-1 : ℤ) := fun ϖ h1 h2 => by
    rw [GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.UnramCompletion.intValuation_eq_of_notMem_sq P h1 h2]
    exact HeightOneSpectrum.valuation_of_algebraMap P ϖ
  have hgS := (hS g).1 hg
  simp only [hS]
  refine ⟨fun k hk => hk.1, ?_, exists_reps hlev (Final.GLintComm E P V.rank) hgS, ?_⟩
  · obtain ⟨a, ha, b, hb, e⟩ := inv_mem_GL_dc hσv hσπ hπ (hmem g)
    exact lift_dc hinj hsurj hlev hgS (inv_mem hgS)
      (GlobalTheory.T.unitary_mem_integralUnitary_doubleCoset_of_GLn_doubleCoset E P σ _ hσσ hσv hσx _ (hmem g) _ (hmem g⁻¹) a ha b hb (by rw [map_inv, e]))
  · intro ϖ ϖ' d g' h1 h2 h1' h2' hg' hd hd'
    have hv := hval ϖ h1 h2
    obtain ⟨a, ha, b, hb, e⟩ := same_dc (fun h0 => by rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm)
      ((hval ϖ' h1' h2').trans hv.symm) d (hdiv ϖ d g h2 hd) (hdiv ϖ' d g' h2' hd')
    exact lift_dc hinj hsurj hlev hgS hg'
      (GlobalTheory.T.unitary_mem_integralUnitary_doubleCoset_of_GLn_doubleCoset E P σ _ hσσ hσv hσx _ (hmem g) _ (hmem g') a ha b hb e)

end CM

section Host

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun v hv => absurd hv (Finset.notMem_empty v)⟩⟩`.
-/
theorem mem_KsphC_iff {D : D7} (V : HSp D) (k : GA D V) :
    k ∈ KsphC V ∅ ↔ GlobalTheory.PlaceComp.IsFin D.sp.cm V k ∧ GlobalTheory.PlaceComp.Stab D.sp.cm V k :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun v hv => absurd hv (Finset.notMem_empty v)⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `Subtype.ext (Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => ?_)))` and prove the remaining obligations. Conclude with `(h i j).symm.trans (zero_mul _)`. Introduce and unpack `rfl i j`.

Establish `: Formalism.L2.Theta.mt V 1 - 1 = 0` using `sub_self _`. Rewrite using `[this]`. Conclude with `mul_zero _`.
-/
theorem suppF_zero {D : D7} (V : HSp D) (g : GA D V) : SuppF V 0 g ↔ g = 1 := by
  constructor
  · intro h
    refine Subtype.ext (Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => ?_)))
    exact (h i j).symm.trans (zero_mul _)
  · rintro rfl i j
    have : Formalism.L2.Theta.mt V 1 - 1 = 0 := sub_self _
    rw [this]
    exact mul_zero _

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_mem _, fun y => by rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec], fun v hv => absurd hv (Finset.notMem_empty v)⟩`.
-/
theorem one_mem_KsphC {D : D7} (V : HSp D) : (1 : GA D V) ∈ KsphC V ∅ :=
  ⟨one_mem _, fun y => by rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec],
    fun v hv => absurd hv (Finset.notMem_empty v)⟩

/- English proof (translation)
Introduce `D V P e hP hu g hg`. Break down `hP with ⟨⟨⟨h1, h2, -⟩, -⟩, h3⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, a1, a2⟩, rfl⟩, hP⟩` into its components or cases. Establish `h4 : cA D e = 0` using `left_eq_add.1 h3`. Establish `h5 : e = 0`. Establish `h6 : ∀ z : Formalism.L2.Theta.AE D, cA D (cA D z) = z` using `fun z => by`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [(cA D).map_zero, (cA D).map_zero]`. Consider the case `add x y hx hy => rw [(cA D).map_add, (cA D).map_add, hx, hy]`. Consider the case `tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)`. Rewrite using `[← h6 e, h4, (cA D).map_zero]`.

Substitute `h5` using the available equality. Establish `k1` using `one_mem_KsphC V`. Establish `s1` using `(suppF_zero V 1).2 rfl`. Take `rfl` from `(suppF_zero V g).1 hg`. Use `⟨⟨1, 1, k1, s1, k1, s1, by simp⟩, ⟨{1}, fun γ hγ => by rwa [Finset.mem_singleton.1 hγ], fun γ hγ => ?_, ?_⟩, fun ϖ ϖ' d g' _ _ _ _ _ hg' _ _ => ⟨1, 1, k1, s1, k1, s1, by rw [(suppF_zero V g').1 hg']; simp⟩⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_singleton.1 hγ]`. Conclude with `⟨one_mem _, 1, ⟨k1, s1⟩, 1, ⟨k1, s1⟩, by simp⟩`. Introduce and unpack `x ⟨a, ha, b, hb, rfl⟩`. Rewrite using `[(suppF_zero V a).1 ha.2, (suppF_zero V b).1 hb.2]`. Conclude with `⟨1, ⟨Finset.mem_singleton_self _, by simpa using ⟨k1, s1⟩⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩`.

Establish `: IsCMField D.host.E` using `D.host.isCMField_hostE`. Establish `he` using `GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) a1 a2`. Take `⟨c0, c1, ⟨R, r1, r2, r3⟩, c3⟩` from `core (E := D.host.E) D.sp.cm V he (inert_of_idem (E := D.host.E) he hP hu) g hg`. Simplify using `only [IsCosetRep, Set.mem_setOf_eq, mem_KsphC_iff]`. Conclude with `⟨c1, ⟨R, r1, fun γ hγ => ⟨c0 γ (r1 γ hγ), r2 γ hγ⟩, r3⟩, fun ϖ ϖ' d g' h1 h2 h1' h2' _ hg' hd hd' => c3 ϖ ϖ' (fun i => d.getD i.1 0) g' h1 h2 h1' h2' hg' hd.2 hd'.2⟩`.
-/
theorem inert_double_cosets : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsPrimeIdem P e e → (∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → ∀ g, SuppF V e g → (∃ a b, a ∈ KsphC V ∅ ∧ SuppF V e a ∧ b ∈ KsphC V ∅ ∧ SuppF V e b ∧ g⁻¹ = a * g * b) ∧ (∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V e γ) ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V e k} g R) ∧ ∀ (ϖ ϖ' : 𝓞 D.host.E) d g', ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → SuppF V e g' → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ' : D.host.E) d g' → ∃ a b, a ∈ KsphC V ∅ ∧ SuppF V e a ∧ b ∈ KsphC V ∅ ∧ SuppF V e b ∧ g' = a * g * b := by
  intro D V P e hP hu g hg
  rcases hP with ⟨⟨⟨h1, h2, -⟩, -⟩, h3⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, a1, a2⟩, rfl⟩, hP⟩
  · have h4 : cA D e = 0 := left_eq_add.1 h3
    have h5 : e = 0 := by
      have h6 : ∀ z : Formalism.L2.Theta.AE D, cA D (cA D z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [(cA D).map_zero, (cA D).map_zero]
        | add x y hx hy => rw [(cA D).map_add, (cA D).map_add, hx, hy]
        | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)
      rw [← h6 e, h4, (cA D).map_zero]
    subst h5
    have k1 := one_mem_KsphC V
    have s1 := (suppF_zero V 1).2 rfl
    obtain rfl := (suppF_zero V g).1 hg
    refine ⟨⟨1, 1, k1, s1, k1, s1, by simp⟩, ⟨{1}, fun γ hγ => by rwa [Finset.mem_singleton.1 hγ],
      fun γ hγ => ?_, ?_⟩, fun ϖ ϖ' d g' _ _ _ _ _ hg' _ _ =>
        ⟨1, 1, k1, s1, k1, s1, by rw [(suppF_zero V g').1 hg']; simp⟩⟩
    · rw [Finset.mem_singleton.1 hγ]
      exact ⟨one_mem _, 1, ⟨k1, s1⟩, 1, ⟨k1, s1⟩, by simp⟩
    · rintro x ⟨a, ha, b, hb, rfl⟩
      rw [(suppF_zero V a).1 ha.2, (suppF_zero V b).1 hb.2]
      exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using ⟨k1, s1⟩⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
  · have : IsCMField D.host.E := D.host.isCMField_hostE
    have he := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) a1 a2
    obtain ⟨c0, c1, ⟨R, r1, r2, r3⟩, c3⟩ :=
      core (E := D.host.E) D.sp.cm V he (inert_of_idem (E := D.host.E) he hP hu) g hg
    simp only [IsCosetRep, Set.mem_setOf_eq, mem_KsphC_iff]
    exact ⟨c1, ⟨R, r1, fun γ hγ => ⟨c0 γ (r1 γ hγ), r2 γ hγ⟩, r3⟩,
      fun ϖ ϖ' d g' h1 h2 h1' h2' _ hg' hd hd' =>
        c3 ϖ ϖ' (fun i => d.getD i.1 0) g' h1 h2 h1' h2' hg' hd.2 hd'.2⟩

end Host

end GlobalTheory.InertDoubleCoset
