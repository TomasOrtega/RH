import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ κ x L m n r V φ cc hV hli hsp hG P c₁ hc`. Take `⟨U, hPU, b, hbV, hfr⟩` from `(show L.IsVBOn Set.univ r V from hV) P (Set.mem_univ _)`. Establish `hbP : L.IsFrameAt b P` using `hfr P (Set.mem_univ _) hPU`. Take `⟨B, hBreg, hCreg, hBC⟩` from `GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x L m n r φ hG P c₁ hc b hbP`. Establish `hmem : ∀ a, ∃ t : Fin r → Ω, ∑ l, t l • cc l = b a`.

Introduce `a`. Establish `hba : b a ∈ Submodule.span Ω (Set.range cc)`. Rewrite using `[hsp, ← hbV]`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Conclude with `(Submodule.mem_span_range_iff_exists_fun Ω).1 hba`.

Use `choose t ht using hmem`. Use `⟨Matrix.of fun l a => t a l, Matrix.of (fun j a => φ j (b a) / x c₁ ^ m), B, ?_, ?_, hBC, ?_, hBreg⟩` and prove the remaining obligations. Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Establish `hli_b` using `hbP.1`.

Rewrite `hli_b` using `[Fintype.linearIndependent_iff]`. Establish `hcol : ∀ l, ∑ a, t a l * v a = 0` using `fun l => by`. Simplify `congrFun hv l` using `[Matrix.mulVec, dotProduct]`. Establish `hsum : ∑ a, v a • b a = 0`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]`. Use `_ = 0 := by simp [hcol]`. Conclude with `hv0 (funext fun a => hli_b v hsum a)`.

Use extensionality with `j a`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]`. Establish `h1 : ∑ l, φ j (cc l) * t a l = φ j (b a)`. Rewrite using `[← ht a, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`. Rewrite using `[h1]`. Distinguish the cases in `hx : x c₁ ^ m = 0`. It suffices to derive a contradiction. Establish `h2` using `congrFun (congrFun hBC a) a`.

Simplify using `[Matrix.mul_apply, hx, Matrix.one_apply] at h2`. Clear the denominators using the available nonvanishing facts. Introduce `j a`. Conclude with `hCreg j a`.
-/
theorem frames_at_point : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] {κ : Type} (x : κ → Ω) (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) (m n r : ℕ) (V : Submodule Ω E)
    (φ : Fin n → Module.Dual Ω E) (cc : Fin r → E) (hV : L.IsVB r V) (hli : LinearIndependent Ω cc)
    (hsp : Submodule.span Ω (Set.range cc) = V) (hG : IsTwistGen ξ x L m φ) (P : Cpt ξ) (c₁ : κ)
    (hc : InChart ξ x c₁ P),
    ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin n) (Fin r) Ω) (B : Matrix (Fin r) (Fin n) Ω),
      T.det ≠ 0 ∧ Matrix.of (fun j a => φ j (cc a)) * T = (x c₁ ^ m) • C ∧ B * C = 1 ∧
        (∀ j a, C j a ∈ regAt ξ P) ∧ ∀ a j, B a j ∈ regAt ξ P := by
  intro X Ω _ ξ E _ _ κ x L m n r V φ cc hV hli hsp hG P c₁ hc
  obtain ⟨U, hPU, b, hbV, hfr⟩ := (show L.IsVBOn Set.univ r V from hV) P (Set.mem_univ _)
  have hbP : L.IsFrameAt b P := hfr P (Set.mem_univ _) hPU
  obtain ⟨B, hBreg, hCreg, hBC⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x L m n r φ hG P c₁ hc b hbP
  have hmem : ∀ a, ∃ t : Fin r → Ω, ∑ l, t l • cc l = b a := by
    intro a
    have hba : b a ∈ Submodule.span Ω (Set.range cc) := by
      rw [hsp, ← hbV]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 hba
  choose t ht using hmem
  refine ⟨Matrix.of fun l a => t a l, Matrix.of (fun j a => φ j (b a) / x c₁ ^ m), B, ?_, ?_, hBC, ?_, hBreg⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hli_b := hbP.1
    rw [Fintype.linearIndependent_iff] at hli_b
    have hcol : ∀ l, ∑ a, t a l * v a = 0 := fun l => by
      simpa [Matrix.mulVec, dotProduct] using congrFun hv l
    have hsum : ∑ a, v a • b a = 0 := by
      calc ∑ a, v a • b a = ∑ a, v a • ∑ l, t a l • cc l := by simp only [ht]
        _ = ∑ l, (∑ a, t a l * v a) • cc l := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]
        _ = 0 := by simp [hcol]
    exact hv0 (funext fun a => hli_b v hsum a)
  · ext j a
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : ∑ l, φ j (cc l) * t a l = φ j (b a) := by
      rw [← ht a, map_sum]
      simp only [map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [h1]
    by_cases hx : x c₁ ^ m = 0
    · exfalso
      have h2 := congrFun (congrFun hBC a) a
      simp [Matrix.mul_apply, hx, Matrix.one_apply] at h2
    · field_simp
  · intro j a
    exact hCreg j a

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
