import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CMFieldDegreeEqTwiceCardStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenusEqCardMulSignatureStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeRationalEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlternatingFormHermitianDescentStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExistsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlternatingFormLatticeCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealBasisFromLatticeBasisStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingInverseRootImaginaryStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx

/- English proof (translation)
Introduce `τ`. Establish `: ballMat q 0 τ = 0` using `by ext a b; simp [ballMat]`. Rewrite using `[this]`. Simplify using `using Matrix.PosDef.one`.
-/
theorem zero_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by ext a b; simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

/- English proof (translation)
Establish `nd` using `traceForm_nondegenerate ℚ E`. Apply `nd.1` to reduce the goal to its premises. Introduce `a`. Establish `halg : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨n, hn, hint⟩` from `halg.exists_integral_multiple`.

Establish `h1 : Algebra.trace ℚ E ((n • a) * w) = 0` using `hw ⟨n • a, hint⟩`. Establish `hnq : ((n : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast hn`. Establish `h2 : (n • a) * w = ((n : ℚ)) • (w * a)`. Rewrite using `[← Int.cast_smul_eq_zsmul ℚ n a, smul_mul_assoc, mul_comm a w]`. Rewrite `h1` using `[h2, map_smul, smul_eq_mul]`.

Rewrite using `[Algebra.traceForm_apply]`. Conclude with `(mul_eq_zero.1 h1).resolve_left hnq`.
-/
theorem trace_zero_of_int {E : Type} [Field E] [NumberField E] (w : E)
    (hw : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * w) = 0) : w = 0 := by
  have nd := traceForm_nondegenerate ℚ E
  apply nd.1
  intro a
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ E ((n • a) * w) = 0 := hw ⟨n • a, hint⟩
  have hnq : ((n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have h2 : (n • a) * w = ((n : ℚ)) • (w * a) := by
    rw [← Int.cast_smul_eq_zsmul ℚ n a, smul_mul_assoc, mul_comm a w]
  rw [h2, map_smul, smul_eq_mul] at h1
  rw [Algebra.traceForm_apply]
  exact (mul_eq_zero.1 h1).resolve_left hnq

/- English proof (translation)
Introduce `E _ _ _ Ψ _ j j' n g Λ _ _ H F`. Establish `h0 : (0 : Fin n → ℂ) ∈ ballDom F.q` using `zero_mem_ballDom F.q`. Take `⟨R, hR⟩ : ∃ R, R = F.R 0` from `⟨_, rfl⟩`. Use `haveI := R.free`. Use `haveI := R.fin`.

Establish `hform : R.form = F.form` using `by rw [hR]; exact F.form_eq 0`. Establish `hrk` using `GlobalTheory.T.CM_field_degree_eq_twice_card E Ψ F.σ F.cm`. Establish `hg` using `GlobalTheory.T.genus_eq_card_mul_signature E Ψ g j j' R.B F.σ F.cm (by rw [hR]; exact F.sig 0 h0)`. Take `⟨N, hN, e, einj, esmul, hspan⟩` from `GlobalTheory.T.lattice_rational_embedding E Λ`. Establish `hpos : 0 < Module.finrank ℚ E` using `Module.finrank_pos`.

Establish `hNj : N = j + j'`. Rewrite `hN` using `[R.rank, hrk, hg]`. Establish `hc : 0 < Fintype.card Ψ` using `by omega`. Establish `: Fintype.card Ψ * N = Fintype.card Ψ * (j + j')` using `by nlinarith`. Conclude with `Nat.eq_of_mul_eq_mul_left hc this`.

Substitute `hNj` using the available equality. Establish `hunim : Function.Bijective F.form` using `hform ▸ R.unimod`. Establish `halt : ∀ x, F.form x x = 0` using `fun x => by rw [← hform]; exact R.alt x`. Establish `hadj : ∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, F.form (a • x) y = F.form x (a' • y)`. Rewrite using `[← hform]`.

Conclude with `R.adj`. Take `⟨B, hBe, hBadj, hBskew, hBnd⟩` from `GlobalTheory.T.alternating_form_hermitian_descent E Λ (j + j') e einj esmul hspan F.form halt hunim hadj`. Take `⟨h, m, hm, hmaster, hint⟩` from `GlobalTheory.T.skew_hermitian_form_exists E H Λ (j + j') e B hBadj hBskew hBnd`. Establish `hdual` using `GlobalTheory.T.alternating_form_lattice_compatible E H Λ (j + j') e einj F.form hunim B hBe hBskew hBnd hspan h m hm hmaster`. Establish `hrt : (H.rt : E) ≠ 0`.

Introduce `h0`. Establish `h1 : ((H.rt ^ 2 : 𝓞 E) : E) = ((-(H.d : 𝓞 E) : 𝓞 E) : E)` using `by rw [H.rt_sq]`. Establish `hd : H.d ≠ 0` using `H.d_prime.ne_zero`. Simplify using `[h0] at h1`. Conclude with `hd h1`.

Establish `hxi : ((m : E) * (H.rt : E))⁻¹ ≠ 0` using `inv_ne_zero (mul_ne_zero (by exact_mod_cast hm) hrt)`. Use `choose eps heps hxieq using fun τ => GlobalTheory.T.embedding_inverse_root_imaginary E H (F.σ τ) m hm`. Establish `hmat : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x))`. Introduce `x y`. Use `hmaster 1 (e x) (e y)` as an intermediate fact.

Rewrite `this` using `[one_mul, one_smul]`. Rewrite using `[this, hBe]`. Set `lam : Module.Basis (Fin (2 * g)) ℤ Λ` to `(Module.finBasisOfFinrankEq ℤ Λ R.rank)`. Take `⟨bas, hbas⟩` from `GlobalTheory.T.real_basis_from_lattice_basis E Ψ g (j + j') F.σ F.cm hg Λ e hspan lam`. Establish `hlat : IsLattice E e.range`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `a _ ⟨x, rfl⟩`. Conclude with `⟨a • x, esmul a x⟩`. Establish `: AddGroup.FG Λ` using `Module.Finite.iff_addGroup_fg.1 inferInstance`. Conclude with `(AddGroup.fg_iff_addSubgroup_fg _).1 (AddGroup.fg_range e)`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Take `⟨k, x, hk, hx⟩` from `hspan v`. Establish `hk' : (k : E) ≠ 0` using `by exact_mod_cast hk`. Establish `: v = (k : E)⁻¹ • e x`.

Rewrite using `[hx, Nat.cast_smul_eq_nsmul E k v |>.symm, smul_smul, inv_mul_cancel₀ hk', one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)`. Establish `hintegral : IsIntegralOn h e.range`. Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`.

Conclude with `hint x y`. Establish `hDI : IsDIntegral h (e.range.relIndex (dualLattice h e.range)) e.range` using `⟨hlat, hintegral, hdual, le_rfl⟩`. Establish `horth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0`. Introduce `x y`. Establish `hsw : h.toSesq (e x) (e y) = 0 ↔ h.toSesq (e y) (e x) = 0`.

Prove the components needed by the constructor for the conclusion. Introduce `h1`. Establish `h2` using `h.isSymm.eq (e x) (e y)`. Rewrite `h2` using `[h1]`. Simplify using `using h2.symm`.

Introduce `h1`. Establish `h2` using `h.isSymm.eq (e y) (e x)`. Rewrite `h2` using `[h1]`. Simplify using `using h2.symm`. Establish `hfa : ∀ a : 𝓞 E, ((F.form (a • x) y : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x)))`.

Introduce `a`. Rewrite using `[hmaster (a : E) (e x) (e y), ← hBe, esmul]`. Rewrite using `[hsw]`. Prove the components needed by the constructor for the conclusion. Introduce `h1 a`.

Use `hfa a` as an intermediate fact. Rewrite `this` using `[h1, mul_zero, mul_zero, map_zero]`. Conclude with `this` after adjusting the coercions. Introduce `h1`. Establish `: ((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x) = 0`.

Apply `trace_zero_of_int` to reduce the goal to its premises. Introduce `a`. Rewrite using `[← hfa a, h1 a]`. Simplify using the standard rewrite rules. Conclude with `(mul_eq_zero.1 this).resolve_left hxi`.

Establish `hcpos : 0 < 1 / ((m : ℝ) * Real.sqrt H.d)`. Establish `h1 : (0 : ℝ) < m` using `by exact_mod_cast Nat.pos_of_ne_zero hm`. Establish `h2 : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Check the signs of the components of the expression. Conclude with `⟨{ h := h, e := e, e_inj := einj, e_smul := esmul, Dn := _, integral := hDI, orth := horth, xi := ((m : E) * (H.rt : E))⁻¹, c := 1 / ((m : ℝ) * Real.sqrt H.d), c_pos := hcpos, eps := eps, eps_sq := heps, xi_eq := hxieq, form_eq := hmat, lam := lam, bas := bas, bas_eq := hbas }⟩`.
-/
theorem exists_latEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (_H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (LatEmb F) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ H F
  have h0 : (0 : Fin n → ℂ) ∈ ballDom F.q := zero_mem_ballDom F.q
  obtain ⟨R, hR⟩ : ∃ R, R = F.R 0 := ⟨_, rfl⟩
  haveI := R.free
  haveI := R.fin
  have hform : R.form = F.form := by rw [hR]; exact F.form_eq 0
  have hrk := GlobalTheory.T.CM_field_degree_eq_twice_card E Ψ F.σ F.cm
  have hg := GlobalTheory.T.genus_eq_card_mul_signature E Ψ g j j' R.B F.σ F.cm (by rw [hR]; exact F.sig 0 h0)
  obtain ⟨N, hN, e, einj, esmul, hspan⟩ := GlobalTheory.T.lattice_rational_embedding E Λ
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hNj : N = j + j' := by
    rw [R.rank, hrk, hg] at hN
    have hc : 0 < Fintype.card Ψ := by omega
    have : Fintype.card Ψ * N = Fintype.card Ψ * (j + j') := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left hc this
  subst hNj
  have hunim : Function.Bijective F.form := hform ▸ R.unimod
  have halt : ∀ x, F.form x x = 0 := fun x => by rw [← hform]; exact R.alt x
  have hadj : ∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, F.form (a • x) y = F.form x (a' • y) := by
    rw [← hform]; exact R.adj
  obtain ⟨B, hBe, hBadj, hBskew, hBnd⟩ := GlobalTheory.T.alternating_form_hermitian_descent E Λ (j + j') e einj esmul hspan F.form halt hunim hadj
  obtain ⟨h, m, hm, hmaster, hint⟩ := GlobalTheory.T.skew_hermitian_form_exists E H Λ (j + j') e B hBadj hBskew hBnd
  have hdual := GlobalTheory.T.alternating_form_lattice_compatible E H Λ (j + j') e einj F.form hunim B hBe hBskew hBnd hspan h m hm hmaster
  have hrt : (H.rt : E) ≠ 0 := by
    intro h0
    have h1 : ((H.rt ^ 2 : 𝓞 E) : E) = ((-(H.d : 𝓞 E) : 𝓞 E) : E) := by rw [H.rt_sq]
    have hd : H.d ≠ 0 := H.d_prime.ne_zero
    simp [h0] at h1
    exact hd h1
  have hxi : ((m : E) * (H.rt : E))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by exact_mod_cast hm) hrt)
  choose eps heps hxieq using fun τ => GlobalTheory.T.embedding_inverse_root_imaginary E H (F.σ τ) m hm
  have hmat : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x)) := by
    intro x y
    have := hmaster 1 (e x) (e y)
    rw [one_mul, one_smul] at this
    rw [this, hBe]
  let lam : Module.Basis (Fin (2 * g)) ℤ Λ := (Module.finBasisOfFinrankEq ℤ Λ R.rank)
  obtain ⟨bas, hbas⟩ := GlobalTheory.T.real_basis_from_lattice_basis E Ψ g (j + j') F.σ F.cm hg Λ e hspan lam
  have hlat : IsLattice E e.range := by
    refine ⟨?_, ?_, ?_⟩
    · rintro a _ ⟨x, rfl⟩
      exact ⟨a • x, esmul a x⟩
    · have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
      exact (AddGroup.fg_iff_addSubgroup_fg _).1 (AddGroup.fg_range e)
    · rw [eq_top_iff]
      intro v _
      obtain ⟨k, x, hk, hx⟩ := hspan v
      have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
      have : v = (k : E)⁻¹ • e x := by
        rw [hx, Nat.cast_smul_eq_nsmul E k v |>.symm, smul_smul, inv_mul_cancel₀ hk', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hintegral : IsIntegralOn h e.range := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hint x y
  have hDI : IsDIntegral h (e.range.relIndex (dualLattice h e.range)) e.range := ⟨hlat, hintegral, hdual, le_rfl⟩
  have horth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0 := by
    intro x y
    have hsw : h.toSesq (e x) (e y) = 0 ↔ h.toSesq (e y) (e x) = 0 := by
      constructor
      · intro h1
        have h2 := h.isSymm.eq (e x) (e y)
        rw [h1] at h2
        simpa using h2.symm
      · intro h1
        have h2 := h.isSymm.eq (e y) (e x)
        rw [h1] at h2
        simpa using h2.symm
    have hfa : ∀ a : 𝓞 E, ((F.form (a • x) y : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * (((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x))) := by
      intro a
      rw [hmaster (a : E) (e x) (e y), ← hBe, esmul]
    rw [hsw]
    constructor
    · intro h1 a
      have := hfa a
      rw [h1, mul_zero, mul_zero, map_zero] at this
      exact_mod_cast this
    · intro h1
      have : ((m : E) * (H.rt : E))⁻¹ * h.toSesq (e y) (e x) = 0 := by
        apply trace_zero_of_int
        intro a
        rw [← hfa a, h1 a]
        simp
      exact (mul_eq_zero.1 this).resolve_left hxi
  have hcpos : 0 < 1 / ((m : ℝ) * Real.sqrt H.d) := by
    have h1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have h2 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    positivity
  exact ⟨{ h := h, e := e, e_inj := einj, e_smul := esmul, Dn := _, integral := hDI, orth := horth,
           xi := ((m : E) * (H.rt : E))⁻¹, c := 1 / ((m : ℝ) * Real.sqrt H.d), c_pos := hcpos, eps := eps, eps_sq := heps,
           xi_eq := hxieq, form_eq := hmat, lam := lam, bas := bas, bas_eq := hbas }⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx
