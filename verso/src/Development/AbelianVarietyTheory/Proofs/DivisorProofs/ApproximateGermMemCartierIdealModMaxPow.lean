import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonUnitAtOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IzumiBoundModPrincipalIdealStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.FibreCorr

/- English proof (translation)
Take `⟨hO, h0⟩` from `hh`. Use `⟨mem_O_of_isHom hπ hO, ?_⟩` and prove the remaining obligations. Break down `h0 with h0 | hinv` into its components or cases. Conclude with `Or.inl h0`. Use `right`.

Introduce `hinv'`. Take `⟨V, g, hzV, rfl⟩` from `hO`. Establish `hV : (V : Set M₁.Z).Nonempty` using `⟨_, hzV⟩`. Establish `hnu : ¬ IsUnit (⟨valF M₁.pt V g, RatModel.valF_mem_O hzV g⟩ : M₁.O (π x'))`. Rewrite using `[RatModel.isUnit_O_iff]`.

Conclude with `fun H => hinv H.2`. Rewrite `hnu` using `[RatModel.isUnit_valF_iff hzV g]`. Establish `hx : x' ∈ π ⁻¹ᵁ V` using `hzV`. Establish `happ` using `hπ.valF_app hV g`. Simplify using `only [AlgHom.id_apply] at happ`.

Establish `hnu' : ¬ IsUnit (⟨valF M.pt (π ⁻¹ᵁ V) ((π.app V).hom g), RatModel.valF_mem_O hx _⟩ : M.O x')`. Rewrite using `[RatModel.isUnit_valF_iff hx]`. Introduce `hb`. Apply `hnu` to reduce the goal to its premises. Establish `: x' ∈ π ⁻¹ᵁ M₁.Z.basicOpen g`.

Rewrite using `[Scheme.preimage_basicOpen]`. Conclude with `hb`. Conclude with `this`. Apply `hnu'` to reduce the goal to its premises. Rewrite using `[RatModel.isUnit_O_iff]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show valF M.pt _ _ ≠ 0`. Rewrite using `[happ]`. Introduce `h0`. Establish `: valF M₁.pt V g = 0` using `h0`.

Rewrite `hinv` using `[this, inv_zero]`. Conclude with `hinv (zero_mem _)`. Simplify `hinv'` using `only [happ]`.
-/
theorem nonUnitAt_of_isHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z}
    (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {x' : M.Z} {h : Ω} (hh : NonUnitAt M₁ (π x') h) : NonUnitAt M x' h := by
  obtain ⟨hO, h0⟩ := hh
  refine ⟨mem_O_of_isHom hπ hO, ?_⟩
  rcases h0 with h0 | hinv
  · exact Or.inl h0
  · right
    intro hinv'
    obtain ⟨V, g, hzV, rfl⟩ := hO
    have hV : (V : Set M₁.Z).Nonempty := ⟨_, hzV⟩
    have hnu : ¬ IsUnit (⟨valF M₁.pt V g, RatModel.valF_mem_O hzV g⟩ : M₁.O (π x')) := by
      rw [RatModel.isUnit_O_iff]
      exact fun H => hinv H.2
    rw [RatModel.isUnit_valF_iff hzV g] at hnu
    have hx : x' ∈ π ⁻¹ᵁ V := hzV
    have happ := hπ.valF_app hV g
    simp only [AlgHom.id_apply] at happ
    have hnu' : ¬ IsUnit (⟨valF M.pt (π ⁻¹ᵁ V) ((π.app V).hom g), RatModel.valF_mem_O hx _⟩ : M.O x') := by
      rw [RatModel.isUnit_valF_iff hx]
      intro hb
      apply hnu
      have : x' ∈ π ⁻¹ᵁ M₁.Z.basicOpen g := by
        rw [Scheme.preimage_basicOpen]; exact hb
      exact this
    apply hnu'
    rw [RatModel.isUnit_O_iff]
    refine ⟨?_, ?_⟩
    · show valF M.pt _ _ ≠ 0
      rw [happ]
      intro h0
      have : valF M₁.pt V g = 0 := h0
      rw [this, inv_zero] at hinv
      exact hinv (zero_mem _)
    · simpa only [happ] using hinv'

end GlobalTheory.FibreCorr

/- English proof (translation)
Introduce `o Ω _ _ _ _ M₁ M π hπ hN U D hU z x' hx hc f' hf e`. Take `⟨i, hi, rfl⟩` from `hf`. Establish `hne : valF M.pt (D.U i) (D.f i) ≠ 0`. Introduce `h0`. Use `haveI : Nontrivial Γ(M.Z, D.U i) := RingHom.domain_nontrivial (M.Z.presheaf.germ (D.U i) x' hi).hom`.

Establish `hreg` using `D.regular i (D.U i) le_rfl`. Establish `h00 : D.f i = 0`. Apply `RatModel.valF_injective M ⟨x', hi⟩` to reduce the goal to its premises. Rewrite using `[h0]`. Unfold `valF`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `hreg` using `[h00, map_zero]`. Conclude with `zero_notMem_nonZeroDivisors hreg`. Take `⟨C, hC⟩` from `GlobalTheory.T.izumi_bound_mod_principal_ideal o Ω M hN U hU x' hc _ (RatModel.valF_mem_O hi (D.f i)) hne`. Use `⟨C e, fun n hn F hF => ?_⟩` and prove the remaining obligations.

Establish `hF'` using `approxIdeal_antitone U D z hn hF`. Establish `hFO : (F : Ω) ∈ M.O x'` using `mem_O_of_isHom hπ (hx ▸ F.2)`. Take `⟨a, b, hab, hb⟩` from `hC e ⟨F, hFO⟩ (by`. Introduce `p _ y hy`. Take `⟨hyx, hyU⟩` from `hy`.

Establish `hz : π (y (cPt p)) = z` using `by rw [hyx, hx]`. Break down `hF' p y hz hyU _ ⟨i, hyx ▸ hi, rfl⟩ with h1 | ⟨h, hh, hle⟩` into its components or cases. Conclude with `Or.inl h1`. Use `Or.inr ⟨h, nonUnitAt_of_isHom hπ (x' := x') (by rw [hx]; exact hh), hle⟩)` and prove the remaining obligations. Use `⟨a, b, hab, ?_⟩` and prove the remaining obligations.

Establish `hsp : Ideal.span {c : M.O x' | ¬ IsUnit c} = maximalIdeal (M.O x')` using `Ideal.span_eq (maximalIdeal (M.O x'))`. Rewrite `hb` using `[hsp]`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.FibreCorr.locbound : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → ∀ (z : M₁.Z) (x' : M.Z), π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∀ F ∈ GlobalTheory.FibreCorr.approxIdeal hπ U D z n, ∃ a b : M.O x', (F : Ω) = a * f' + b ∧ b ∈ maximalIdeal (M.O x') ^ e := by
  intro o Ω _ _ _ _ M₁ M π hπ hN U D hU z x' hx hc f' hf e
  obtain ⟨i, hi, rfl⟩ := hf
  have hne : valF M.pt (D.U i) (D.f i) ≠ 0 := by
    intro h0
    haveI : Nontrivial Γ(M.Z, D.U i) := RingHom.domain_nontrivial (M.Z.presheaf.germ (D.U i) x' hi).hom
    have hreg := D.regular i (D.U i) le_rfl
    have h00 : D.f i = 0 := by
      apply RatModel.valF_injective M ⟨x', hi⟩
      rw [h0]
      unfold valF
      split_ifs <;> simp
    rw [h00, map_zero] at hreg
    exact zero_notMem_nonZeroDivisors hreg
  obtain ⟨C, hC⟩ := GlobalTheory.T.izumi_bound_mod_principal_ideal o Ω M hN U hU x' hc _ (RatModel.valF_mem_O hi (D.f i)) hne
  refine ⟨C e, fun n hn F hF => ?_⟩
  have hF' := approxIdeal_antitone U D z hn hF
  have hFO : (F : Ω) ∈ M.O x' := mem_O_of_isHom hπ (hx ▸ F.2)
  obtain ⟨a, b, hab, hb⟩ := hC e ⟨F, hFO⟩ (by
    intro p _ y hy
    obtain ⟨hyx, hyU⟩ := hy
    have hz : π (y (cPt p)) = z := by rw [hyx, hx]
    rcases hF' p y hz hyU _ ⟨i, hyx ▸ hi, rfl⟩ with h1 | ⟨h, hh, hle⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h, nonUnitAt_of_isHom hπ (x' := x') (by rw [hx]; exact hh), hle⟩)
  refine ⟨a, b, hab, ?_⟩
  have hsp : Ideal.span {c : M.O x' | ¬ IsUnit c} = maximalIdeal (M.O x') := Ideal.span_eq (maximalIdeal (M.O x'))
  rwa [hsp] at hb
