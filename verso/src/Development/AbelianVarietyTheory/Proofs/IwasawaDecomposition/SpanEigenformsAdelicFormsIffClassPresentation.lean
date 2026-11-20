import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.LiftSpanEig

/- English proof (translation)
Introduce `G Γ W K G0 _ _ ι _ _ _ _ _ S σ ρ J χ _ _ Q ch act P Tt hB U ψ Φ`. Set `gA : Q → (G → W) →ₗ[ℂ] (G → W)` to `fun κ => { toFun := Bridge.g0Act ch κ map_add' := fun F F' => by`. Use function extensionality and compare the values at `h`. Simplify using `only [Bridge.g0Act, Pi.add_apply, smul_add]`. Use the proof step `map_smul' := fun a F => by`.

Use function extensionality and compare the values at `h`. Simplify using `only [Bridge.g0Act, Pi.smul_apply, RingHom.id_apply]`. Rewrite using `[smul_comm] }`. Establish `gA_apply : ∀ κ F h, gA κ F h = (((ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : G))` using `fun _ _ _ => rfl`. Establish `hsemi : ∀ (a : K) (f : S.Forms), P.extL (a • f) = σ a • P.extL f` using `fun a f => map_smulₛₗ P.extL a f`.

Establish `hact : ∀ (g : G0) (κ : Q), Tt.red κ = g → ∀ f : S.Forms, P.extL (act g f) = gA κ (P.extL f)` using `fun g κ hk f => Tt.act_eq g κ hk f`. Set `N : Submodule ℂ (G → W)` to `{ carrier := {Φ | Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G), Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h} add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun κ hu h => by`. Simplify using `only [Pi.add_apply, ha.2 κ hu h, hb.2 κ hu h, smul_add]⟩`. Use the proof step `zero_mem' := ⟨zero_mem _, fun κ hu h => by simp⟩`. Use the proof step `smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun κ hu h => by`.

Simplify using `only [Pi.smul_apply, ha.2 κ hu h]`. Rewrite using `[smul_comm c, smul_comm c]⟩ }`. Prove the components needed by the constructor for the conclusion. Introduce `hΦ`. Establish `: Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ≤ N`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Use `⟨hB.2 ▸ Submodule.subset_span ⟨f, rfl⟩, fun κ hu h => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun (hact (Tt.red κ) κ rfl f) h`. Establish `e2 : act (Tt.red κ) f = ((ψ ⟨_, hu⟩ : Kˣ) : K) • f` using `hf ⟨_, hu⟩`.

Rewrite `e` using `[e2, hsemi, gA_apply]`. Rewrite `e` using `[Pi.smul_apply]`. Rewrite using `[e, smul_smul, Units.mul_inv, one_smul]`. Conclude with `this hΦ`. Introduce and unpack `⟨hA, hc⟩ choose κ hκ using Tt.red_surj`.

Set `L : (G → W) →ₗ[ℂ] (G → W)` to `∑ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g)`. Establish `L_apply : ∀ F, L F = ∑ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g) F` using `fun F => by`. Simplify using `[L, LinearMap.sum_apply]`. Establish `hLext : ∀ f : S.Forms, L (P.extL f) = P.extL (GlobalTheory.TraceIncl.trU act U ψ f)` using `fun f => by`. Rewrite using `[L_apply, GlobalTheory.TraceIncl.trU_apply, map_sum]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[hsemi, hact g (κ g) (hκ g)]`. Set `E` to `P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}`. Establish `hspan : Submodule.span ℂ (Set.range P.extL) ≤ (Submodule.span ℂ E).comap L`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨f, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, hLext]`. Conclude with `Submodule.subset_span ⟨_, fun u => GlobalTheory.TraceIncl.trU_eigen act U ψ f u, rfl⟩`. Establish `hLΦ : L Φ = (Nat.card U : ℂ) • Φ`. Establish `term : ∀ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g) Φ = if g ∈ U then Φ else 0` using `fun g => by`.

Unfold `GlobalTheory.TraceIncl.invChar`. Use `split_ifs with hg`. Establish `hs : ψ ⟨Tt.red (κ g), (hκ g).symm ▸ hg⟩ = ψ ⟨g, hg⟩` using `congrArg ψ (Subtype.ext (hκ g))`. Use function extensionality and compare the values at `h`. Rewrite using `[Pi.smul_apply, gA_apply, hc (κ g) ((hκ g).symm ▸ hg) h, hs, smul_smul, smul_smul, smul_smul]`.

Use `one_smul ℂ (Φ h) using 2` and compare the differences between its conclusion and the goal. Rewrite using `[mul_assoc (σ _), Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one]`. Rewrite using `[map_zero, zero_smul]`. Rewrite using `[L_apply, Finset.sum_congr rfl fun g _ => term g, ← Finset.sum_filter, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Establish `hmem : L Φ ∈ Submodule.span ℂ E` using `hspan (hB.2.symm ▸ hA)`.

Rewrite `hmem` using `[hLΦ]`. Establish `hne : (Nat.card U : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Conclude with `(Submodule.smul_mem_iff _ hne).1 hmem`.
-/
theorem eigen_span_iff : ∀ {G Γ W K G0 : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) [Group G0] [Fintype G0] (Q : Subgroup G) (ch : Q →* ℂˣ) (act : Representation K G0 S.Forms) (P : Bridge.ClassPres ι S σ ρ J χ) (Tt : Bridge.ActTie ι P Q ch act), P.ExtBij → ∀ (U : Subgroup G0) (ψ : U →* Kˣ) (Φ : G → W), Φ ∈ Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ↔ (Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G), Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h) := by
  classical
  intro G Γ W K G0 _ _ ι _ _ _ _ _ S σ ρ J χ _ _ Q ch act P Tt hB U ψ Φ

  let gA : Q → (G → W) →ₗ[ℂ] (G → W) := fun κ =>
    { toFun := Bridge.g0Act ch κ
      map_add' := fun F F' => by
        funext h
        simp only [Bridge.g0Act, Pi.add_apply, smul_add]
      map_smul' := fun a F => by
        funext h
        simp only [Bridge.g0Act, Pi.smul_apply, RingHom.id_apply]
        rw [smul_comm] }
  have gA_apply : ∀ κ F h, gA κ F h = (((ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : G)) := fun _ _ _ => rfl
  have hsemi : ∀ (a : K) (f : S.Forms), P.extL (a • f) = σ a • P.extL f := fun a f => map_smulₛₗ P.extL a f
  have hact : ∀ (g : G0) (κ : Q), Tt.red κ = g → ∀ f : S.Forms, P.extL (act g f) = gA κ (P.extL f) :=
    fun g κ hk f => Tt.act_eq g κ hk f

  let N : Submodule ℂ (G → W) :=
    { carrier := {Φ | Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G),
        Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun κ hu h => by
        simp only [Pi.add_apply, ha.2 κ hu h, hb.2 κ hu h, smul_add]⟩
      zero_mem' := ⟨zero_mem _, fun κ hu h => by simp⟩
      smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun κ hu h => by
        simp only [Pi.smul_apply, ha.2 κ hu h]
        rw [smul_comm c, smul_comm c]⟩ }
  constructor
  · intro hΦ
    have : Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ≤ N := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      refine ⟨hB.2 ▸ Submodule.subset_span ⟨f, rfl⟩, fun κ hu h => ?_⟩
      have e := congrFun (hact (Tt.red κ) κ rfl f) h
      have e2 : act (Tt.red κ) f = ((ψ ⟨_, hu⟩ : Kˣ) : K) • f := hf ⟨_, hu⟩
      rw [e2, hsemi, gA_apply] at e
      rw [Pi.smul_apply] at e
      rw [e, smul_smul, Units.mul_inv, one_smul]
    exact this hΦ
  · rintro ⟨hA, hc⟩
    choose κ hκ using Tt.red_surj
    let L : (G → W) →ₗ[ℂ] (G → W) := ∑ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g)
    have L_apply : ∀ F, L F = ∑ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g) F := fun F => by
      simp [L, LinearMap.sum_apply]
    have hLext : ∀ f : S.Forms, L (P.extL f) = P.extL (GlobalTheory.TraceIncl.trU act U ψ f) := fun f => by
      rw [L_apply, GlobalTheory.TraceIncl.trU_apply, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hsemi, hact g (κ g) (hκ g)]
    let E := P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}
    have hspan : Submodule.span ℂ (Set.range P.extL) ≤ (Submodule.span ℂ E).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hLext]
      exact Submodule.subset_span ⟨_, fun u => GlobalTheory.TraceIncl.trU_eigen act U ψ f u, rfl⟩
    have hLΦ : L Φ = (Nat.card U : ℂ) • Φ := by
      have term : ∀ g : G0, σ (GlobalTheory.TraceIncl.invChar U ψ g) • gA (κ g) Φ = if g ∈ U then Φ else 0 := fun g => by
        unfold GlobalTheory.TraceIncl.invChar
        split_ifs with hg
        · have hs : ψ ⟨Tt.red (κ g), (hκ g).symm ▸ hg⟩ = ψ ⟨g, hg⟩ := congrArg ψ (Subtype.ext (hκ g))
          funext h
          rw [Pi.smul_apply, gA_apply, hc (κ g) ((hκ g).symm ▸ hg) h, hs, smul_smul, smul_smul, smul_smul]
          convert one_smul ℂ (Φ h) using 2
          rw [mul_assoc (σ _), Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one]
        · rw [map_zero, zero_smul]
      rw [L_apply, Finset.sum_congr rfl fun g _ => term g, ← Finset.sum_filter, Finset.sum_const,
        ← Nat.cast_smul_eq_nsmul ℂ, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hmem : L Φ ∈ Submodule.span ℂ E := hspan (hB.2.symm ▸ hA)
    rw [hLΦ] at hmem
    have hne : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact (Submodule.smul_mem_iff _ hne).1 hmem

end GlobalTheory.LiftSpanEig
