import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ m n δ γ hli hsub`. Establish `hAB : Submodule.span ℤ (Set.range γ) ≤ Submodule.span ℤ (Set.range δ)` using `Submodule.span_mono hsub`. Establish `key : ∀ z : L, z ∈ Submodule.span ℤ (Set.range δ) → ∀ a : ℤ, a ≠ 0 → a • z ∈ Submodule.span ℤ (Set.range γ) → z ∈ Submodule.span ℤ (Set.range γ)`. Introduce `z hz a ha haz`. Establish `himg : δ '' (δ ⁻¹' Set.range γ) = Set.range γ` using `Set.image_preimage_eq_of_subset hsub`.

Rewrite `haz`, the goal using `[← himg]`. Rewrite `haz`, the goal using `[Finsupp.mem_span_image_iff_linearCombination]`. Take `⟨l', hl'S, hl'⟩` from `haz`. Rewrite `hz` using `[Finsupp.mem_span_range_iff_exists_finsupp]`. Take `⟨c, hc⟩` from `hz`.

Establish `hlc : Finsupp.linearCombination ℤ δ c = z`. Rewrite using `[Finsupp.linearCombination_apply]`. Conclude with `hc`. Establish `heq : a • c = l'`. Apply `hli` to reduce the goal to its premises.

Rewrite using `[map_smul, hlc, hl']`. Use `⟨c, ?_, hlc⟩` and prove the remaining obligations. Rewrite `hl'S`, the goal using `[Finsupp.mem_supported']`. Introduce `i hi`. Use `hl'S i hi` as an intermediate fact.

Rewrite `this` using `[← heq, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `(mul_eq_zero.mp this).resolve_left ha`. Set `q : (L ⧸ Submodule.span ℤ (Set.range γ)) →ₗ[ℤ] (L ⧸ Submodule.span ℤ (Set.range δ))` to `Submodule.factor hAB`. Set `f : Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ)) →+ Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))` to `(q.restrict (p := Submodule.torsion ℤ _) (q := Submodule.torsion ℤ _) (fun x hx => by`. Rewrite `hx`, the goal using `[Submodule.mem_torsion_iff]`.

Take `⟨a, ha⟩` from `hx`. Conclude with `⟨a, by rw [Submonoid.smul_def] at ha ⊢; rw [← map_smul, ha, map_zero]⟩)).toAddMonoidHom`. Establish `hinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨x, hx⟩ hfx`.

Establish `hqx : q x = 0` using `congrArg Subtype.val hfx`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [ZeroMemClass.coe_zero]`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H z`.

Rewrite `hx` using `[Submodule.mem_torsion_iff]`. Take `⟨⟨a, ha0⟩, ha⟩` from `hx`. Establish `hz : z ∈ Submodule.span ℤ (Set.range δ)`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Simplify `hqx` using `[q]`.

Establish `ha' : a ≠ 0` using `nonZeroDivisors.ne_zero ha0`. Establish `haz : a • z ∈ Submodule.span ℤ (Set.range γ)`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]`. Simplify `ha` using `[Submonoid.smul_def]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `key z hz a ha' haz`. Conclude with `AddSubgroup.card_dvd_of_injective f hinj`.
-/
theorem natCard_torsion_quot_span_dvd_of_range_subset :
    ∀ (L : Type) [AddCommGroup L] {m n : ℕ} (δ : Fin m → L) (γ : Fin n → L), LinearIndependent ℤ δ →
    Set.range γ ⊆ Set.range δ →
    Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ))) ∣
      Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))) := by
  intro L _ m n δ γ hli hsub
  have hAB : Submodule.span ℤ (Set.range γ) ≤ Submodule.span ℤ (Set.range δ) :=
    Submodule.span_mono hsub
  have key : ∀ z : L, z ∈ Submodule.span ℤ (Set.range δ) → ∀ a : ℤ, a ≠ 0 →
      a • z ∈ Submodule.span ℤ (Set.range γ) → z ∈ Submodule.span ℤ (Set.range γ) := by
    intro z hz a ha haz
    have himg : δ '' (δ ⁻¹' Set.range γ) = Set.range γ := Set.image_preimage_eq_of_subset hsub
    rw [← himg] at haz ⊢
    rw [Finsupp.mem_span_image_iff_linearCombination] at haz ⊢
    obtain ⟨l', hl'S, hl'⟩ := haz
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
    obtain ⟨c, hc⟩ := hz
    have hlc : Finsupp.linearCombination ℤ δ c = z := by
      rw [Finsupp.linearCombination_apply]; exact hc
    have heq : a • c = l' := by
      apply hli
      rw [map_smul, hlc, hl']
    refine ⟨c, ?_, hlc⟩
    rw [Finsupp.mem_supported'] at hl'S ⊢
    intro i hi
    have := hl'S i hi
    rw [← heq, Finsupp.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  let q : (L ⧸ Submodule.span ℤ (Set.range γ)) →ₗ[ℤ] (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    Submodule.factor hAB
  let f : Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ)) →+
      Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    (q.restrict (p := Submodule.torsion ℤ _) (q := Submodule.torsion ℤ _) (fun x hx => by
      rw [Submodule.mem_torsion_iff] at hx ⊢
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [Submonoid.smul_def] at ha ⊢; rw [← map_smul, ha, map_zero]⟩)).toAddMonoidHom
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ hfx
    have hqx : q x = 0 := congrArg Subtype.val hfx
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.mem_torsion_iff] at hx
      obtain ⟨⟨a, ha0⟩, ha⟩ := hx
      have hz : z ∈ Submodule.span ℤ (Set.range δ) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        simpa [q] using hqx
      have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
      have haz : a • z ∈ Submodule.span ℤ (Set.range γ) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
        simpa [Submonoid.smul_def] using ha
      rw [Submodule.Quotient.mk_eq_zero]
      exact key z hz a ha' haz
  exact AddSubgroup.card_dvd_of_injective f hinj

end GlobalTheory
