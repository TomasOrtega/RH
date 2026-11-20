import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.FrameCongOpen

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def congInt (N : ℕ) : Subgroup (GL (Fin n) (Formalism.L2.Herm.intAf F E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n)
    (Ideal.Quotient.mk (Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)}))).ker

/- English proof (translation)
Rewrite using `[congInt, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]`. Use `forall₂_congr fun a b => ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (z.1 a b) = (1 : Matrix (Fin n) (Fin n) _) a b ↔ _`. Simplify using `only [Matrix.one_apply]`.

Use `split_ifs`. Rewrite using `[map_one]`. Rewrite using `[map_zero]`.
-/
theorem mem_congInt_span {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, z.1 a b - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b ∈
      Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)} := by
  rw [congInt, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [← Ideal.Quotient.eq]
  change Ideal.Quotient.mk _ (z.1 a b) = (1 : Matrix (Fin n) (Fin n) _) a b ↔ _
  simp only [Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

/- English proof (translation)
Establish `hone : ∀ a b, (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) a b` using `fun a b => by`. Apply the tactic sequence `simp only [Matrix.one_apply]; split_ifs <;> rfl`. Rewrite using `[mem_congInt_span]`. Use `forall₂_congr fun a b => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_span_singleton']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Use `⟨c, c.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← hone, ← AddSubgroupClass.coe_sub, ← hc, Subring.coe_mul, Subring.coe_natCast, mul_comm]`. Introduce and unpack `⟨w, hw, e⟩`.

Use `⟨⟨w, hw⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub, hone, e, mul_comm]`.
-/
theorem mem_congInt {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  have hone : ∀ a b, (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b : Formalism.L2.Herm.intAf F E) :
      E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) a b := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> rfl
  rw [mem_congInt_span]
  refine forall₂_congr fun a b => ?_
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    rw [← hone, ← AddSubgroupClass.coe_sub, ← hc, Subring.coe_mul, Subring.coe_natCast, mul_comm]
  · rintro ⟨w, hw, e⟩
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub, hone, e, mul_comm]

/- English proof (translation)
Establish `hx : x = β * (β⁻¹ * x * β) * β⁻¹` using `by group`. Generalize the expression as in `β⁻¹ * x * β = m at h1 h2 h3 hx`. Establish `hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => A.map (Formalism.L2.Herm.intAf F E).subtype` using `Matrix.map_injective Subtype.val_injective`. Set `y : GL (Fin n) (Formalism.L2.Herm.intAf F E)` to `⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi (by`. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `m.mul_inv),`. Use `hi (by`. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `m.inv_mul)⟩`. Establish `hy : frGL β y = x`.

Establish `: intGL F E n y = m` using `Units.ext rfl`. Rewrite using `[hx, ← this]`. Both sides reduce to the same expression. Conclude with `⟨y, (mem_congInt y).2 fun i j => h3 i j, hy⟩`.
-/
theorem mem_cong (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ)
    (h1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h3 : ∀ i j, ∃ z ∈ Formalism.L2.Herm.intAf F E,
      (β⁻¹ * x * β).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (N : E ⊗[F] Formalism.L2.Herm.Af F) * z) :
    x ∈ (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  have hx : x = β * (β⁻¹ * x * β) * β⁻¹ := by group
  generalize β⁻¹ * x * β = m at h1 h2 h3 hx
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      A.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
  let y : GL (Fin n) (Formalism.L2.Herm.intAf F E) :=
    ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩,
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.mul_inv),
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.inv_mul)⟩
  have hy : frGL β y = x := by
    have : intGL F E n y = m := Units.ext rfl
    rw [hx, ← this]
    rfl
  exact ⟨y, (mem_congInt y).2 fun i j => h3 i j, hy⟩

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _`. Establish `ho` using `(GlobalTheory.Mass.intTens_open_compact F E).1`. Use `set s := GlobalTheory.Mass.swapTens F E (Af F)`.

Set `β' : GL (Fin n) (Af F ⊗[F] E)` to `Formalism.UG.bc (s.symm : _ →+* _) β`. Establish `hβ : Formalism.UG.bc (s : _ →+* _) β' = β` using `Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)`. Set `m : X → GL (Fin n) (Af F ⊗[F] E)` to `fun κ => β'⁻¹ * φ κ * β'`. Establish `hm : Continuous m` using `(continuous_const.mul hf).mul continuous_const`. Establish `hm1 : m x₀ = 1` using `by simp only [m, h₀, mul_one, inv_mul_cancel]`.

Establish `hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ)` using `fun κ => by`. Simplify using `only [m, map_mul, map_inv, hβ]`. Establish `hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈ GlobalTheory.Mass.intTens F E` using `fun i j => by`. Simplify using `only [Matrix.one_apply]`. Use `split_ifs`.

Use `exacts [one_mem _, zero_mem _]`. Establish `e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E`. Simplify using `only [Filter.eventually_all]`. Introduce `i j`. Conclude with `(ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)`.

Establish `e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E`. Simplify using `only [Filter.eventually_all]`. Introduce `i j`. Conclude with `(ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)`. Establish `e3 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, algebraMap F _ ((N : ℕ) : F)⁻¹ * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E`.

Simplify using `only [Filter.eventually_all]`. Introduce `i j`. Establish `hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((N : ℕ) : F)⁻¹ * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)` using `continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)`. Use `(ho.preimage hc).mem_nhds ?_` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]`.

Conclude with `(GlobalTheory.Mass.intTens F E).zero_mem`. Use `filter_upwards [e1, e2, e3] with κ h1 h2 h3`. Use `mem_cong β _ N ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hs]`. Conclude with `h1`.

Rewrite using `[hs, ← map_inv]`. Conclude with `h2`. Introduce `i j`. Use `⟨_, h3 i j, ?_⟩` and prove the remaining obligations. Establish `hN' : ((N : ℕ) : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`.

Establish `e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (N : ℕ) * (algebraMap F _ ((N : ℕ) : F)⁻¹ * ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j))`. Rewrite using `[← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul, mul_inv_cancel₀ hN', map_one, one_mul]`. Use `congrArg s e` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, map_sub]`. Rewrite using `[hs]`.

Use `Eq.trans ?_ this` and prove the remaining obligations. Use `congr 1`. Apply the tactic sequence `simp only [Matrix.one_apply]; split_ifs <;> simp`.
-/
theorem eventually_cong_mat (β : GL (Fin n) (E ⊗[F] Af F)) (N : ℕ) (hN : 0 < N) {X : Type} [TopologicalSpace X]
    {x₀ : X} {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) ∈
      (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈
      GlobalTheory.Mass.intTens F E := fun i j => by
    simp only [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)
  have e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ i j,
      algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    have hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage hc).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e1, e2, e3] with κ h1 h2 h3
  refine mem_cong β _ N ?_ ?_ ?_
  · rw [hs]; exact h1
  · rw [hs, ← map_inv]; exact h2
  · intro i j
    refine ⟨_, h3 i j, ?_⟩
    have hN' : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j =
        (N : ℕ) * (algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)) := by
      rw [← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul,
        mul_inv_cancel₀ hN', map_one, one_mul]
    have := congrArg s e
    rw [map_mul, map_natCast, map_sub] at this
    rw [hs]
    refine Eq.trans ?_ this
    congr 1
    simp only [Matrix.one_apply]; split_ifs <;> simp

def congFr (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  (congInt (F := F) (E := E) (n := n) N).map (frGL β)

/- English proof (translation)
Take `⟨z, hz, e⟩` from `Subgroup.mem_map.1 hx`. Conclude with `⟨z, e, (mem_congInt z).1 hz⟩`.
-/
theorem mem_congFr {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N : ℕ} (hx : x ∈ congFr β N) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf F E), frGL β z = x ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  obtain ⟨z, hz, e⟩ := Subgroup.mem_map.1 hx
  exact ⟨z, e, (mem_congInt z).1 hz⟩

end General

/- English proof (translation)
Introduce `D V β N hN`. Use `⟨(congFr β N).comap (Formalism.IndefR.Lev.finE V), ?_, fun κ hκ => ?_⟩` and prove the remaining obligations. Use `haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩ haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _ haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _ haveI : IsTopologicalGroup (GA D V) := inferInsta …`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Take `⟨π, hπ, -⟩` from `GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram`.

Establish `hf : Continuous (finHom V)` using `(continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ`. Conclude with `eventually_cong_mat β N hN hf (map_one _)`. Conclude with `mem_congFr (Subgroup.mem_comap.1 hκ)`.
-/
theorem exists_open_cong : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ κ ∈ U, ∃ z : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.frGL β z = Lev.finE V κ ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w := by
  intro D V β N hN
  refine ⟨(congFr β N).comap (Formalism.IndefR.Lev.finE V),
    ?_, fun κ hκ => ?_⟩
  · haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hf : Continuous (finHom V) :=
      (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    exact eventually_cong_mat β N hN hf (map_one _)
  · exact mem_congFr (Subgroup.mem_comap.1 hκ)

end GlobalTheory.FrameCongOpen

end
