import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeSupOfCoprime
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FourierTranslatesVacuumRootsLevelPointsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverFourierCoeffEqFiniteFourierSumStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GPhi

/- English proof (translation)
Establish `h1 : (AddSubgroup.toIntSubmodule C).FG` using `(Submodule.fg_iff_addSubgroup_fg _).2 hC`. Establish `h2 : (AddSubgroup.toIntSubmodule A).FG` using `h1.of_le hA`. Establish `h3 : A.FG` using `(Submodule.fg_iff_addSubgroup_fg _).1 h2`. Establish `: AddGroup.FG A` using `(AddGroup.fg_iff_addSubgroup_fg A).2 h3`. Use `AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Use `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Conclude with `h y y.2`.
-/
theorem finite_quot {G : Type} [AddCommGroup G] {A B C : AddSubgroup G} (hC : C.FG) (hA : A ≤ C) {m : ℕ}
    (hm : 0 < m) (h : ∀ y ∈ A, m • y ∈ B) : Finite (A ⧸ B.addSubgroupOf A) := by
  have h1 : (AddSubgroup.toIntSubmodule C).FG := (Submodule.fg_iff_addSubgroup_fg _).2 hC
  have h2 : (AddSubgroup.toIntSubmodule A).FG := h1.of_le hA
  have h3 : A.FG := (Submodule.fg_iff_addSubgroup_fg _).1 h2
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 h3
  refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact h y y.2

/- English proof (translation)
Use `Fintype.ofFinite Q` as an intermediate fact. Use `Fintype.ofFinite C` as an intermediate fact. Simplify using `only [finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.mul_sum, Finset.sum_smul, mul_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem finsum_exchange {Q C V : Type} [Finite Q] [Finite C] [AddCommGroup V] [Module ℂ V] (t : ℂ) (a : C → ℂ)
    (e : C → Q → ℂ) (f : Q → V) :
    ∑ᶠ q, (t * ∑ᶠ c, a c * e c q) • f q = t • ∑ᶠ c, a c • ∑ᶠ q, e c q • f q := by
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite C
  simp only [finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.mul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hM : l.Mb ≠ ⊥`. Introduce `h`. Establish `h₁` using `l.prod`. Rewrite `h₁` using `[h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot]`. Establish `h₂ : l.M = 0` using `by exact_mod_cast h₁`.

Use `l.three_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `l.Mb.finiteQuotientOfFreeOfNeBot hM` as an intermediate fact. Use `Dw.fin` as an intermediate fact. Conclude with `Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top`.
-/
theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

/- English proof (translation)
Establish `h : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l` using `l.prod.symm.le.trans Ideal.mul_le_right`. Conclude with `h (Ideal.mem_span_singleton_self _)`.
-/
theorem natCast_mem_Mfr {H : Host E} (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ Mfr l := by
  have h : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l := l.prod.symm.le.trans Ideal.mul_le_right
  exact h (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c n d _ _ hF hlev ph ψ x₀ hpin r g X bas idx D hn hs hev hr tie v₀ hv₀ x0`. Establish `hM0 : 0 < d.l₂.M` using `by have := d.l₂.three_le; omega`. Establish `hM : (d.l₂.M : 𝓞 E) ∈ D.𝔪` using `tie.m ▸ natCast_mem_Mfr d.l₂`. Use `finite_levQ Dw d.l₂` as an intermediate fact. Take `⟨ρ, s, hρ, hsv⟩` from `ShVac.shift_vac E r X g bas idx n hs hev D _ hM0 hM v₀ hv₀`.

Establish `hcard : 0 < Nat.card (Fin n → LevQ Dw d.l₂)` using `Nat.card_pos`. Use `⟨Nat.card (Fin n → LevQ Dw d.l₂) * ρ, s, mul_pos (by exact_mod_cast hcard) hρ, ?_⟩` and prove the remaining obligations. Introduce `L hL mk mk₂ δ v h1 h2 h12 hd hx hv`. Rewrite `hv`, the goal using `[← tie.w]`. Take `⟨t₁, ht₁, H₁⟩` from `GlobalTheory.T.coverFourierCoeff_eq_finite_fourier_sum E H Dw l Xo c n d hF hlev ph ψ x₀ hpin r X D hn hr tie L hL mk mk₂ δ x0 h1 h2 h12 hd hx`.

Take `⟨t₂, ht₂, H₂⟩` from `hsv L hL v hv`. Use `⟨t₁ * (Nat.card (Fin n → LevQ Dw d.l₂) * t₂), by rw [norm_mul, norm_mul, ht₁, ht₂, Complex.norm_natCast, _root_.one_mul], fun Λ hΛ => ⟨(H₂ Λ hΛ).1, fun N hN Y hY => ?_⟩⟩` and prove the remaining obligations. Take `⟨⟨u, hu⟩, -, hp, -⟩` from `TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr L hL.1 _ Λ hΛ`. Establish `hfg` using `(GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hev D.w D.w_int D.w_tr L hL.1 _ Λ hΛ).1`. Establish `hfin : Finite (tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸ (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _)`.

Use `finite_quot hfg ?_ hM0 (ShVac.nsmul_tens_right fun x hx => ?_)` and prove the remaining obligations. Introduce `y hy`. Simplify `Submodule.smul_le_right hx) y hy` using `using ShVac.nsmul_tens_right (Λ := Λ) (k := 1) (L' := L) (fun x hx => by simpa`. Rewrite using `[mul_comm _ D.𝔪, Submodule.mul_smul]`. Conclude with `Submodule.smul_mem_smul hM hx`.

Establish `hP` using `GlobalTheory.T.fourier_translates_vacuum_roots_levelPoints E H Dw d.l₂ r g X bas idx n hs hev D.w D.w_int D.w_tr L mk₂ hL.1 h2 Λ hΛ N hN Y hY (projA X bas D.w (tens Λ L) v) (by rw [hp v hv.1 u hu]; exact TensVac.sb_smul _ hu.1) (fun y hy => by rw [hp v hv.1 u hu, TensVac.heisG_sm …`. Rewrite `hP` using `[← tie.m]`. Establish `e` using `(H₂ Λ hΛ).2`. Rewrite `e` using `[Level.sh]`. Unfold `gphi phiF`.

Simplify using `only [H₁ Λ hΛ N hN Y hY]`. Rewrite using `[finsum_exchange]`. Simplify using `only [fun cl : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) => hP cl cl.2, e, TensVac.heisG_smul]`. Use `Fintype.ofFinite (tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸ (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _)` as an intermediate fact. Simplify using `only [finsum_eq_sum_of_fintype, Finset.smul_sum, smul_smul, Level.sh]`.

Use `Finset.sum_congr rfl fun cl _ => ?_` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gphi_eq_smul_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n), IsSympl X bas → Even n → r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ (ρ : ℝ) (s : Lt E n → ℝ), 0 < ρ ∧ ∀ L ∈ D.lats, ∀ (mk mk₂ δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (v : TF n g), IsMark l L mk → IsMark d.l₂ L mk₂ → MarkOver l d.l₂ L mk mk₂ → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → ∃ t : ℂ, ‖t‖ = ρ ∧ ∀ Λ ∈ Vset E n d.l₂.M, 0 < s Λ ∧ ∀ N : ℕ, NOK Λ N d.l₂.M → ∀ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ L mk₂ N Y → gphi X bas (H.w0 : E) Λ L v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y = (t * (s Λ : ℂ)) • phiF bas D (Mfr l) hn v₀ L Λ := by
  intro E _ _ _ H Dw l Xo c n d _ _ hF hlev ph ψ x₀ hpin r g X bas idx D hn hs hev hr tie v₀ hv₀ x0
  have hM0 : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM : (d.l₂.M : 𝓞 E) ∈ D.𝔪 := tie.m ▸ natCast_mem_Mfr d.l₂
  have := finite_levQ Dw d.l₂
  obtain ⟨ρ, s, hρ, hsv⟩ := ShVac.shift_vac E r X g bas idx n hs hev D _ hM0 hM v₀ hv₀
  have hcard : 0 < Nat.card (Fin n → LevQ Dw d.l₂) := Nat.card_pos
  refine ⟨Nat.card (Fin n → LevQ Dw d.l₂) * ρ, s, mul_pos (by exact_mod_cast hcard) hρ, ?_⟩
  intro L hL mk mk₂ δ v h1 h2 h12 hd hx hv
  rw [← tie.w] at hv ⊢
  obtain ⟨t₁, ht₁, H₁⟩ := GlobalTheory.T.coverFourierCoeff_eq_finite_fourier_sum E H Dw l Xo c n d hF hlev ph ψ x₀ hpin r X D hn hr tie L hL mk mk₂ δ x0
    h1 h2 h12 hd hx
  obtain ⟨t₂, ht₂, H₂⟩ := hsv L hL v hv
  refine ⟨t₁ * (Nat.card (Fin n → LevQ Dw d.l₂) * t₂), by rw [norm_mul, norm_mul, ht₁, ht₂, Complex.norm_natCast, _root_.one_mul],
    fun Λ hΛ => ⟨(H₂ Λ hΛ).1, fun N hN Y hY => ?_⟩⟩
  obtain ⟨⟨u, hu⟩, -, hp, -⟩ := TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr L hL.1 _ Λ hΛ
  have hfg := (GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hev D.w D.w_int D.w_tr L hL.1 _ Λ hΛ).1
  have hfin : Finite (tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _) := by
    refine finite_quot hfg ?_ hM0 (ShVac.nsmul_tens_right fun x hx => ?_)
    · intro y hy
      simpa using ShVac.nsmul_tens_right (Λ := Λ) (k := 1) (L' := L)
        (fun x hx => by simpa using Submodule.smul_le_right hx) y hy
    · rw [mul_comm _ D.𝔪, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hM hx
  have hP := GlobalTheory.T.fourier_translates_vacuum_roots_levelPoints E H Dw d.l₂ r g X bas idx n hs hev D.w D.w_int D.w_tr L mk₂ hL.1 h2 Λ hΛ N hN Y hY
    (projA X bas D.w (tens Λ L) v) (by rw [hp v hv.1 u hu]; exact TensVac.sb_smul _ hu.1)
    (fun y hy => by rw [hp v hv.1 u hu, TensVac.heisG_smul, smul_comm, hu.2.2 y hy])
  rw [← tie.m] at hP
  have e := (H₂ Λ hΛ).2
  rw [Level.sh] at e
  unfold gphi phiF
  simp only [H₁ Λ hΛ N hN Y hY]
  rw [finsum_exchange]
  simp only [fun cl : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) => hP cl cl.2, e, TensVac.heisG_smul]
  have := Fintype.ofFinite (tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _)
  simp only [finsum_eq_sum_of_fintype, Finset.smul_sum, smul_smul, Level.sh]
  refine Finset.sum_congr rfl fun cl _ => ?_
  congr 1
  ring

end GlobalTheory.Dict.GPhi
