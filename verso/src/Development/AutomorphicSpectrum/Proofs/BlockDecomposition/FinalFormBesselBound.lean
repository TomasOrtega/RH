import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Take `⟨hh, hp, hi⟩` from `hU`. Use `⟨hh, fun u => ?_, fun u hu => ?_, fun g _ u u' => ?_, fun g hg u u' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : u = 0`. Simplify using `[h]`. Conclude with `(hp u h).le`.

Distinguish the cases in `h : u = 0`. Simplify using `[h]`. Use `hp u h` as an intermediate fact. Rewrite `this` using `[hu]`. Simplify using `at this`.

Rewrite using `[hi, Nat.sub_self, pow_zero, one_mul]`. Establish `h1 : g = 1`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `hg.2 i j (by omega)`.

Substitute `h1` using the available equality. Rewrite using `[Whittaker.psiN_one]`. Simplify using the standard rewrite rules.
-/
theorem inv_top {n : ℕ} (hn : 1 < n) {ρ : Representation ℂ (GL (Fin n) F) V} {ψ : AddChar F ℂ}
    {l : V →ₗ[ℂ] ℂ} {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) : Inv ρ ψ l (n - 1) B := by
  obtain ⟨hh, hp, hi⟩ := hU
  refine ⟨hh, fun u => ?_, fun u hu => ?_, fun g _ u u' => ?_, fun g hg u u' => ?_⟩
  · by_cases h : u = 0
    · simp [h]
    · exact (hp u h).le
  · by_cases h : u = 0
    · simp [h]
    · have := hp u h
      rw [hu] at this
      simp at this
  · rw [hi, Nat.sub_self, pow_zero, one_mul]
  · have h1 : g = 1 := by
      apply Units.ext
      ext i j
      exact hg.2 i j (by omega)
    subst h1
    rw [Whittaker.psiN_one]
    simp

/- English proof (translation)
Take `⟨B', hC⟩` from `h4a F μ ψ hψ n V ρ hρ l k B hk hB`. Take `⟨hh, hp, hz⟩` from `h4b F μ ψ hψ n V ρ hρ l k B B' hk hW hB hC`. Conclude with `⟨B', hC, hh, hp, hz, h4c F μ ψ hψ n V ρ hρ l k B B' hk hB hC, h4d F μ ψ hψ n V ρ hρ l k B B' hk hB hC⟩`.
-/
theorem inv_step [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ}
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {k : ℕ} (hk : k + 1 < n) {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : Inv ρ ψ l (k + 1) B) :
    ∃ B', Char μ ρ ψ k B B' ∧ Inv ρ ψ l k B' := by
  obtain ⟨B', hC⟩ := h4a F μ ψ hψ n V ρ hρ l k B hk hB
  obtain ⟨hh, hp, hz⟩ := h4b F μ ψ hψ n V ρ hρ l k B B' hk hW hB hC
  exact ⟨B', hC, hh, hp, hz, h4c F μ ψ hψ n V ρ hρ l k B B' hk hB hC,
    h4d F μ ψ hψ n V ρ hρ l k B B' hk hB hC⟩

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => exact ⟨B, inv_top hn hU⟩`. Consider the case `succ d ih`. Take `⟨B₁, h₁⟩` from `ih (by omega)`. Establish `e : n - 1 - d = n - 1 - (d + 1) + 1` using `by omega`.

Rewrite `h₁` using `[e]`. Take `⟨B₂, -, h₂⟩` from `inv_step h4a h4b h4c h4d μ hψ hρ hW (by omega) h₁`. Conclude with `⟨B₂, h₂⟩`.
-/
theorem inv_down [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ} (hn : 1 < n)
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) (d : ℕ) (hd : d ≤ n - 2) :
    ∃ B₁, Inv ρ ψ l (n - 1 - d) B₁ := by
  induction d with
  | zero => exact ⟨B, inv_top hn hU⟩
  | succ d ih =>
    obtain ⟨B₁, h₁⟩ := ih (by omega)
    have e : n - 1 - d = n - 1 - (d + 1) + 1 := by omega
    rw [e] at h₁
    obtain ⟨B₂, -, h₂⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (by omega) h₁
    exact ⟨B₂, h₂⟩

/- English proof (translation)
Introduce `h4a h4b h4c h4d h5 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l B hn hW hU`. Take `⟨B₁, h₁⟩` from `inv_down h4a h4b h4c h4d μ hψ hn hρ hW hU (n - 2) le_rfl`. Establish `e : n - 1 - (n - 2) = 0 + 1` using `by omega`. Rewrite `h₁` using `[e]`. Take `⟨B', hC, h'⟩` from `inv_step h4a h4b h4c h4d μ hψ hρ hW (k := 0) (by omega) h₁`.

Conclude with `⟨B', h', h5 F μ ψ hψ n V ρ hρ l B₁ B' hn h₁ hC⟩`.
-/
theorem final_form_bessel_bound : StableAverageExists → FormHermitianPositive → FormQuasiInvariantMirabolic → FormEquivariantColumn → L5 → L6 := by
  intro h4a h4b h4c h4d h5 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l B hn hW hU
  obtain ⟨B₁, h₁⟩ := inv_down h4a h4b h4c h4d μ hψ hn hρ hW hU (n - 2) le_rfl
  have e : n - 1 - (n - 2) = 0 + 1 := by omega
  rw [e] at h₁
  obtain ⟨B', hC, h'⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (k := 0) (by omega) h₁
  exact ⟨B', h', h5 F μ ψ hψ n V ρ hρ l B₁ B' hn h₁ hC⟩

end GlobalTheory.CompanionTheory.SatakeBound

end
