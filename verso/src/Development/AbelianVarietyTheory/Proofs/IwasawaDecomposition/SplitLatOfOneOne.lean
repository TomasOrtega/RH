import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat GlobalTheory.HermModel GlobalTheory.SplitGenus
open scoped nonZeroDivisors

namespace GlobalTheory.AnyLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E}

/- English proof (translation)
Take `⟨D₁, p1, q1⟩` from `h1`. Set `D₂` to `DatumSum.sumDatum D₁ (CM.ConjDatum.conj D₁)`. Establish `p2 : D₂.p = D₀.p`. Express the relevant statement in the definitionally equal form `D₁.p + D₁.q = _`. Use linear arithmetic over natural numbers and integers.

Establish `q2 : D₂.q = D₀.q`. Express the relevant statement in the definitionally equal form `D₁.q + D₁.p = _`. Use linear arithmetic over natural numbers and integers. Take `⟨φ, inj, -, -, -, hEF⟩` from `GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt E H D₀ D₂ _ (H.rt : E) G φ₀ p2 q2 (GlobalTheory.OneSpace.cc_rt H) hM`. Establish `: Nontrivial D₁.La` using `Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D₁.rank]; omega)`.

Take `⟨x, hx⟩` from `exists_ne (0 : D₁.La)`. Set `v : D₂.La` to `(x, x)`. Use `⟨φ v, fun h => hx (congrArg Prod.fst (inj (h.trans (map_zero φ).symm))), ?_⟩` and prove the remaining obligations. Rewrite using `[← herm_zero_left G (φ v)]`. Use `herm_eq_of_trace G (GlobalTheory.OneSpace.rt_ne H) fun s => ?_` and prove the remaining obligations.

Establish `e : D₂.EF (s • v) v = D₁.EF (s • x) x + D₁.EF (H.bar s • x) x` using `DatumSum.sumForm_apply D₁.EF (CM.ConjDatum.conj D₁).EF (s • v) v`. Establish `e2 : D₁.EF (s • x) x + D₁.EF (H.bar s • x) x = 0`. Establish `h` using `D₁.alt (x + H.bar s • x)`. Simplify using `only [map_add, LinearMap.add_apply, D₁.alt] at h`. Rewrite using `[D₁.adj]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← map_smul, ← hEF, e, e2, smul_zero, herm_zero_left]`. Simplify using the standard rewrite rules.
-/
theorem exists_isotropic (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) (D₀ : Datum H) (hp : D₀.p = 1) (hq : D₀.q = 1)
    (G : Matrix (Fin r) (Fin r) E) (φ₀ : D₀.La →ₗ[𝓞 E] (Fin r → E))
    (hM : Function.Injective φ₀ ∧ Submodule.span E (Set.range φ₀) = ⊤ ∧ (∀ a b, FD.cc (G a b) = G b a) ∧ G.det ≠ 0 ∧
      ∀ x y, ((D₀.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E ((H.rt : E) * FD.herm G (φ₀ x) (φ₀ y))) :
    ∃ z : Fin r → E, z ≠ 0 ∧ FD.herm G z z = 0 := by
  obtain ⟨D₁, p1, q1⟩ := h1
  let D₂ := DatumSum.sumDatum D₁ (CM.ConjDatum.conj D₁)
  have p2 : D₂.p = D₀.p := by
    change D₁.p + D₁.q = _
    omega
  have q2 : D₂.q = D₀.q := by
    change D₁.q + D₁.p = _
    omega
  obtain ⟨φ, inj, -, -, -, hEF⟩ := GlobalTheory.model_in_same_space
    (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt E H D₀ D₂ _ (H.rt : E) G φ₀ p2 q2 (GlobalTheory.OneSpace.cc_rt H) hM
  have : Nontrivial D₁.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D₁.rank]; omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : D₁.La)
  let v : D₂.La := (x, x)
  refine ⟨φ v, fun h => hx (congrArg Prod.fst (inj (h.trans (map_zero φ).symm))), ?_⟩
  rw [← herm_zero_left G (φ v)]
  refine herm_eq_of_trace G (GlobalTheory.OneSpace.rt_ne H) fun s => ?_
  have e : D₂.EF (s • v) v = D₁.EF (s • x) x + D₁.EF (H.bar s • x) x :=
    DatumSum.sumForm_apply D₁.EF (CM.ConjDatum.conj D₁).EF (s • v) v
  have e2 : D₁.EF (s • x) x + D₁.EF (H.bar s • x) x = 0 := by
    have h := D₁.alt (x + H.bar s • x)
    simp only [map_add, LinearMap.add_apply, D₁.alt] at h
    rw [D₁.adj]
    linarith
  rw [← map_smul, ← hEF, e, e2, smul_zero, herm_zero_left]
  simp

/- English proof (translation)
Introduce `E _ _ _ H D h1 hp hq`. Take `⟨D₀, ep, eq, Lp, Lm, htop, ho, rp, rm, sp, sm⟩` from `GlobalTheory.T.exists_splitLattice_datum_every_signature E H D.p D.q h1`. Use `D.fin` as an intermediate fact. Use `D₀.fin` as an intermediate fact. Establish `hξ` using `GlobalTheory.OneSpace.cc_rt H`.

Establish `hξ0` using `GlobalTheory.OneSpace.rt_ne H`. Take `⟨G, φ₀, hM₀⟩` from `GlobalTheory.exists_herm_coord_of_datum E H D₀ (H.rt : E) hξ hξ0 (D.p + D.q) (by rw [ep, eq])`. Take `⟨φ, hM⟩` from `GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt E H D₀ D _ (H.rt : E) G φ₀ ep.symm eq.symm hξ hM₀`. Establish `hz` using `exists_isotropic h1 D₀ (ep.trans hp) (eq.trans hq) G φ₀ hM₀`. Take `⟨-, hfg, -, hdual⟩` from `rank_integral_selfDual E H D _ _ G φ hξ hM`.

Take `⟨inj₀, span₀, hG, hdet, hEF₀⟩` from `hM₀`. Take `⟨inj, span, -, -, hEF⟩` from `hM`. Establish `hc : IsCompl Lp Lm`. Use `⟨Submodule.disjoint_def.2 fun a ha hb => ?_, codisjoint_iff.2 htop⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Conclude with `lt_asymm (sp a ha h0) (sm a hb h0)`. Take `⟨π, π1, π2, π3, π4, π5⟩` from `exists_projector D₀ G φ₀ inj₀ span₀ hG hEF₀ Lp Lm hc ho`. Establish `hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G`. Use `⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩` and prove the remaining obligations. Establish `h2 : (H.rt : E) = -(H.rt : E)` using `h.symm.trans hξ`.

Take the linear combination `(1 / 2 : E) * h2`. Establish `: Nontrivial Lp` using `Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by omega)`. Take `⟨⟨a, ha⟩, ha0⟩` from `exists_ne (0 : Lp)`. Establish `hxx : FD.herm G (φ₀ a) (φ₀ a) ≠ 0`. Introduce `h`.

Establish `h5` using `sp a ha fun h => ha0 (Subtype.ext h)`. Establish `h6` using `hEF₀ (H.rt • a) a`. Rewrite `h6` using `[map_smul φ₀, show H.rt • φ₀ a = (H.rt : E) • φ₀ a from rfl, herm_smul_left, h, mul_zero, mul_zero, map_zero]`. Establish `h7 : D₀.EF (H.rt • a) a = 0` using `by exact_mod_cast h6`. Rewrite `h5` using `[h7]`.

Simplify using `at h5`. Take `⟨b₁, hb₁, m₁⟩` from `GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ span₀`. Take `⟨b₂, hb₂, m₂⟩` from `GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ₀ φ span`. Take `⟨k, f, hk, hf⟩` from `GlobalTheory.T.exists_coprime_scaled_isometry_same_signature E H D D₀ ep eq (2 * b₁ * b₂) (by positivity)`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hk` using `[Nat.coprime_zero_left]`. Rewrite `hk` using `[mul_assoc]`. Use linear arithmetic over natural numbers and integers. Establish `hkE : (k : E) ≠ 0` using `by exact_mod_cast hk0`.

Establish `hkQ : (k : ℚ) ^ 2 ≠ 0` using `by positivity`. Take `⟨A, hA⟩` from `exists_matrix φ (φ₀ ∘ₗ f) inj span`. Establish `hA' : ∀ x, (k : E) • (((k : E)⁻¹ • A) *ᵥ φ x) = φ₀ (f x)` using `fun x => by`. Rewrite using `[smul_mulVec, smul_smul, mul_inv_cancel₀ hkE, one_smul]`. Conclude with `hA x`.

Generalize the expression as in `(k : E)⁻¹ • A = γ₀ at hA'`. Establish `hU₀ : ∀ x y, FD.herm G (γ₀ *ᵥ x) (γ₀ *ᵥ y) = FD.herm G x y` using `fun x y => by`. Use `herm_ext G γ₀ γ₀ 1 1 span (by` as an intermediate fact. Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`. Rewrite using `[one_mulVec, one_mulVec]`.

Use `herm_eq_of_trace G hξ0 fun s => ?_` and prove the remaining obligations. Rewrite using `[show s • γ₀ *ᵥ φ x = (s : E) • γ₀ *ᵥ φ x from rfl, ← mulVec_smul, show (s : E) • φ x = s • φ x from rfl, ← map_smul]`. Apply `mul_left_cancel₀ hkQ` to reduce the goal to its premises. Rewrite using `[← trace_nsmul, hA', hA', ← hEF₀, ← hEF, hf]`. Use `push_cast`.

Use the proof step `rfl) x y`. Rewrite `this` using `[one_mulVec, one_mulVec]`. Then use the resulting hypothesis. Establish `hd₀` using `isUnit_det hdet hU₀`. Take `⟨γ, hU, hγ⟩` from `GlobalTheory.T.exists_unitary_conj_split_lattice_of_local (maximalRealSubfield E) E (IsCMField.complexConj E) _ G (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hh hz (LinearMap.range φ) (LinearMap.range φ₀) hfg span π γ₀ (φ₀ a) (2 * b₁ * b₂) k π1 π2 ((π4 a).2 ha) hxx (by rint …`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[mul_right_comm, mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₁]`. Conclude with `nsmul_mem (m₁ x) _)`. Use the proof step `(by`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₂]`.

Conclude with `nsmul_mem (m₂ x) _)`. Use `hU₀ hk`. Use the proof step `(by`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[← Nat.cast_smul_eq_nsmul E, hA']`.

Conclude with `⟨_, rfl⟩)`. Use the proof step `(by`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `(hdual _).1 fun x => ⟨D₀.EF y (f x), ?_⟩` and prove the remaining obligations. Rewrite using `[hEF₀, ← hA', ← Nat.cast_smul_eq_nsmul E, herm_smul_left, herm_smul_right, ← hU₀ (γ₀⁻¹ *ᵥ φ₀ y), mulVec_mulVec, mul_nonsing_inv _ hd₀, one_mulVec, show FD.cc (k : E) = k by simp [FD.cc], mul_comm (k : E)])`.

Establish `hU' : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y` using `hU`. Establish `hd` using `isUnit_det hdet hU'`. Take `⟨N, g, hN, hg⟩` from `exists_scaled_map ((Matrix.toLin' γ).restrictScalars (𝓞 E) ∘ₗ φ) φ₀ inj₀ span₀`. Establish `hg' : ∀ x, φ₀ (g x) = (N : E) • γ *ᵥ φ x` using `hg`. Establish `hE : ∀ x y, D₀.EF (g x) (g y) = (N : ℤ) ^ 2 * D.EF x y` using `fun x y => by`.

Use `hEF₀ (g x) (g y)` as an intermediate fact. Rewrite `this` using `[hg', hg', trace_nsmul, hU', ← hEF]`. Conclude with `this` after adjusting the coercions. Use `split_of_scaled D D₀ ep eq Lp Lm ho rp rm sp sm N hN g ?_ hE fun x => ?_` and prove the remaining obligations. Use `(injective_iff_map_eq_zero g).2 fun x hx => D.unimod.1 ?_` and prove the remaining obligations.

Use extensionality with `y`. Use `hE x y` as an intermediate fact. Rewrite `this` using `[hx, map_zero, LinearMap.zero_apply]`. Rewrite using `[map_zero, LinearMap.zero_apply]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left (by positivity)`.

Take `⟨c, hc⟩` from `hγ _ ⟨x, rfl⟩`. Establish `e : γ *ᵥ φ c = π *ᵥ (γ *ᵥ φ x)`. Rewrite using `[hc, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]`. Establish `e2 : π *ᵥ (γ *ᵥ φ c) = γ *ᵥ φ c` using `by rw [e, mulVec_mulVec, π1]`. Use `⟨c, (π4 _).1 ?_, π5 _ ?_⟩` and prove the remaining obligations.

Rewrite using `[hg', mulVec_smul, e2]`. Rewrite using `[hg', mulVec_smul, map_sub, mulVec_sub, mulVec_sub, e2, e, sub_self, smul_zero]`.
-/
theorem splitLat_of_one_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → D.p = 1 → D.q = 1 → SplitLat D := by
  intro E _ _ _ H D h1 hp hq
  obtain ⟨D₀, ep, eq, Lp, Lm, htop, ho, rp, rm, sp, sm⟩ := GlobalTheory.T.exists_splitLattice_datum_every_signature E H D.p D.q h1
  have := D.fin
  have := D₀.fin
  have hξ := GlobalTheory.OneSpace.cc_rt H
  have hξ0 := GlobalTheory.OneSpace.rt_ne H
  obtain ⟨G, φ₀, hM₀⟩ := GlobalTheory.exists_herm_coord_of_datum E H D₀ (H.rt : E) hξ hξ0 (D.p + D.q) (by rw [ep, eq])
  obtain ⟨φ, hM⟩ := GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt E H D₀ D _ (H.rt : E) G φ₀ ep.symm eq.symm hξ hM₀
  have hz := exists_isotropic h1 D₀ (ep.trans hp) (eq.trans hq) G φ₀ hM₀
  obtain ⟨-, hfg, -, hdual⟩ := rank_integral_selfDual E H D _ _ G φ hξ hM
  obtain ⟨inj₀, span₀, hG, hdet, hEF₀⟩ := hM₀
  obtain ⟨inj, span, -, -, hEF⟩ := hM
  have hc : IsCompl Lp Lm := by
    refine ⟨Submodule.disjoint_def.2 fun a ha hb => ?_, codisjoint_iff.2 htop⟩
    by_contra h0
    exact lt_asymm (sp a ha h0) (sm a hb h0)
  obtain ⟨π, π1, π2, π3, π4, π5⟩ := exists_projector D₀ G φ₀ inj₀ span₀ hG hEF₀ Lp Lm hc ho
  have hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G := by
    refine ⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩
    have h2 : (H.rt : E) = -(H.rt : E) := h.symm.trans hξ
    linear_combination (1 / 2 : E) * h2
  have : Nontrivial Lp := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by omega)
  obtain ⟨⟨a, ha⟩, ha0⟩ := exists_ne (0 : Lp)
  have hxx : FD.herm G (φ₀ a) (φ₀ a) ≠ 0 := by
    intro h
    have h5 := sp a ha fun h => ha0 (Subtype.ext h)
    have h6 := hEF₀ (H.rt • a) a
    rw [map_smul φ₀, show H.rt • φ₀ a = (H.rt : E) • φ₀ a from rfl, herm_smul_left, h, mul_zero, mul_zero,
      map_zero] at h6
    have h7 : D₀.EF (H.rt • a) a = 0 := by exact_mod_cast h6
    rw [h7] at h5
    simp at h5
  obtain ⟨b₁, hb₁, m₁⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ span₀
  obtain ⟨b₂, hb₂, m₂⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ₀ φ span
  obtain ⟨k, f, hk, hf⟩ := GlobalTheory.T.exists_coprime_scaled_isometry_same_signature E H D D₀ ep eq (2 * b₁ * b₂) (by positivity)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    rw [mul_assoc] at hk
    omega
  have hkE : (k : E) ≠ 0 := by exact_mod_cast hk0
  have hkQ : (k : ℚ) ^ 2 ≠ 0 := by positivity
  obtain ⟨A, hA⟩ := exists_matrix φ (φ₀ ∘ₗ f) inj span
  have hA' : ∀ x, (k : E) • (((k : E)⁻¹ • A) *ᵥ φ x) = φ₀ (f x) := fun x => by
    rw [smul_mulVec, smul_smul, mul_inv_cancel₀ hkE, one_smul]
    exact hA x
  generalize (k : E)⁻¹ • A = γ₀ at hA'
  have hU₀ : ∀ x y, FD.herm G (γ₀ *ᵥ x) (γ₀ *ᵥ y) = FD.herm G x y := fun x y => by
    have := herm_ext G γ₀ γ₀ 1 1 span (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [one_mulVec, one_mulVec]
      refine herm_eq_of_trace G hξ0 fun s => ?_
      rw [show s • γ₀ *ᵥ φ x = (s : E) • γ₀ *ᵥ φ x from rfl, ← mulVec_smul,
        show (s : E) • φ x = s • φ x from rfl, ← map_smul]
      apply mul_left_cancel₀ hkQ
      rw [← trace_nsmul, hA', hA', ← hEF₀, ← hEF, hf]
      push_cast
      rfl) x y
    rwa [one_mulVec, one_mulVec] at this
  have hd₀ := isUnit_det hdet hU₀
  obtain ⟨γ, hU, hγ⟩ := GlobalTheory.T.exists_unitary_conj_split_lattice_of_local (maximalRealSubfield E) E (IsCMField.complexConj E) _ G
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hh hz (LinearMap.range φ) (LinearMap.range φ₀) hfg span
    π γ₀ (φ₀ a) (2 * b₁ * b₂) k π1 π2 ((π4 a).2 ha) hxx (by rintro _ ⟨y, rfl⟩; exact π3 y) (by positivity)
    (by
      rintro _ ⟨x, rfl⟩
      rw [mul_right_comm, mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₁]
      exact nsmul_mem (m₁ x) _)
    (by
      rintro _ ⟨x, rfl⟩
      rw [mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₂]
      exact nsmul_mem (m₂ x) _)
    hU₀ hk
    (by
      rintro _ ⟨x, rfl⟩
      rw [← Nat.cast_smul_eq_nsmul E, hA']
      exact ⟨_, rfl⟩)
    (by
      rintro _ ⟨y, rfl⟩
      refine (hdual _).1 fun x => ⟨D₀.EF y (f x), ?_⟩
      rw [hEF₀, ← hA', ← Nat.cast_smul_eq_nsmul E, herm_smul_left, herm_smul_right, ← hU₀ (γ₀⁻¹ *ᵥ φ₀ y),
        mulVec_mulVec, mul_nonsing_inv _ hd₀, one_mulVec, show FD.cc (k : E) = k by simp [FD.cc], mul_comm (k : E)])
  have hU' : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y := hU
  have hd := isUnit_det hdet hU'
  obtain ⟨N, g, hN, hg⟩ := exists_scaled_map ((Matrix.toLin' γ).restrictScalars (𝓞 E) ∘ₗ φ) φ₀ inj₀ span₀
  have hg' : ∀ x, φ₀ (g x) = (N : E) • γ *ᵥ φ x := hg
  have hE : ∀ x y, D₀.EF (g x) (g y) = (N : ℤ) ^ 2 * D.EF x y := fun x y => by
    have := hEF₀ (g x) (g y)
    rw [hg', hg', trace_nsmul, hU', ← hEF] at this
    exact_mod_cast this
  refine split_of_scaled D D₀ ep eq Lp Lm ho rp rm sp sm N hN g ?_ hE fun x => ?_
  · refine (injective_iff_map_eq_zero g).2 fun x hx => D.unimod.1 ?_
    ext y
    have := hE x y
    rw [hx, map_zero, LinearMap.zero_apply] at this
    rw [map_zero, LinearMap.zero_apply]
    exact (mul_eq_zero.1 this.symm).resolve_left (by positivity)
  · obtain ⟨c, hc⟩ := hγ _ ⟨x, rfl⟩
    have e : γ *ᵥ φ c = π *ᵥ (γ *ᵥ φ x) := by
      rw [hc, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd,
        Matrix.one_mul]
    have e2 : π *ᵥ (γ *ᵥ φ c) = γ *ᵥ φ c := by rw [e, mulVec_mulVec, π1]
    refine ⟨c, (π4 _).1 ?_, π5 _ ?_⟩
    · rw [hg', mulVec_smul, e2]
    · rw [hg', mulVec_smul, map_sub, mulVec_sub, mulVec_sub, e2, e, sub_self, smul_zero]

end GlobalTheory.AnyLevel
