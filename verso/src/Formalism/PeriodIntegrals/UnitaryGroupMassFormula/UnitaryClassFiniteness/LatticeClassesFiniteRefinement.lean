import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.HermSingleLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.IsIntegralOfIntOE
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HermLatFin

noncomputable section

open Matrix NumberField
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.HermLatFin

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h` using `isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ))`. Simplify using `using h`.
-/
theorem int_nat (m : ℕ) : IsIntegral ℤ (m : E) := by
  have h := isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ))
  simpa using h

/- English proof (translation)
The claim follows from `ha.map σ.toIntAlgHom`.
-/
theorem int_sigma (σ : E →+* E) {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (σ a) := ha.map σ.toIntAlgHom

/- English proof (translation)
Establish `hex : ∀ a : E, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a)`. Introduce `a`. Establish `halg : IsAlgebraic ℤ a` using `by first`. Consider the case `exact (IsFractionRing.isAlgebraic_iff ℤ ℚ).mpr (Algebra.IsAlgebraic.isAlgebraic a)`. Consider the case `exact (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)`.

Consider the case `exact (IsFractionRing.isAlgebraic_iff (R := ℤ) (K := ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic a)`. Consider the case `exact Algebra.IsAlgebraic.isAlgebraic a`. Take `⟨y, hy0, hy⟩ : ∃ y ≠ (0 : ℤ), IsIntegral ℤ (y • a)` from `by first`. Consider the case `exact halg.exists_integral_multiple`. Consider the case `exact exists_integral_multiple halg`.

Use `⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩` and prove the remaining obligations. Establish `hcast : ((y.natAbs : ℕ) : E) = (((y.natAbs : ℕ) : ℤ) : E)` using `(Int.cast_natCast _).symm`. Break down `(show ((y.natAbs : ℕ) : ℤ) = y ∨ ((y.natAbs : ℕ) : ℤ) = -y by omega) with h | h` into its components or cases. Rewrite using `[hcast, h, ← zsmul_eq_mul]`. Conclude with `hy`.

Rewrite using `[hcast, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]`. Conclude with `hy.neg`. Use `choose d hd0 hd using fun p : Fin M × Fin M => hex (A p.1 p.2)`. Use `⟨∏ p, d p, Finset.prod_pos fun p _ => hd0 p, fun i j => ?_⟩` and prove the remaining obligations. Establish `hsplit : (∏ p, d p : ℕ) = (∏ p ∈ Finset.univ.erase (i, j), d p) * d (i, j)` using `(Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm`.

Rewrite using `[hsplit, Nat.cast_mul, mul_assoc]`. Conclude with `(int_nat _).mul (hd (i, j))`.
-/
theorem mat_den {M : ℕ} (A : Matrix (Fin M) (Fin M) E) : ∃ d : ℕ, 0 < d ∧ ∀ i j, IsIntegral ℤ ((d : E) * A i j) := by
  have hex : ∀ a : E, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
    intro a
    have halg : IsAlgebraic ℤ a := by
      first
      | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact (IsFractionRing.isAlgebraic_iff (R := ℤ) (K := ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact Algebra.IsAlgebraic.isAlgebraic a
    obtain ⟨y, hy0, hy⟩ : ∃ y ≠ (0 : ℤ), IsIntegral ℤ (y • a) := by
      first
      | exact halg.exists_integral_multiple
      | exact exists_integral_multiple halg
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
    have hcast : ((y.natAbs : ℕ) : E) = (((y.natAbs : ℕ) : ℤ) : E) := (Int.cast_natCast _).symm
    rcases (show ((y.natAbs : ℕ) : ℤ) = y ∨ ((y.natAbs : ℕ) : ℤ) = -y by omega) with h | h
    · rw [hcast, h, ← zsmul_eq_mul]
      exact hy
    · rw [hcast, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hy.neg
  choose d hd0 hd using fun p : Fin M × Fin M => hex (A p.1 p.2)
  refine ⟨∏ p, d p, Finset.prod_pos fun p _ => hd0 p, fun i j => ?_⟩
  have hsplit : (∏ p, d p : ℕ) = (∏ p ∈ Finset.univ.erase (i, j), d p) * d (i, j) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
  rw [hsplit, Nat.cast_mul, mul_assoc]
  exact (int_nat _).mul (hd (i, j))

/- English proof (translation)
Introduce `E _ _ σ M J D T c0 hσ hpos hD hT hc0`. Use `set J' : Matrix (Fin M) (Fin M) E := (D : E) • J with hJ'`. Establish `hpos' : ∀ τ : E →+* ℂ, (J'.map τ).PosDef`. Introduce `τ`. Establish `: J'.map τ = (D : ℂ) • J.map τ`.

Use extensionality with `i j`. Simplify using `[hJ', map_natCast]`. Rewrite using `[this]`. Conclude with `(hpos τ).smul (by exact_mod_cast hD)`. Take `⟨SE, hSEf, hSE⟩` from `hermitian_lattice_finite E M σ J' T hσ hpos' hT`.

Set `Sub : Submodule (𝓞 E) (Fin M → E) → Set (Set (Fin M → E))` to `fun N₀ => {s | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧ (∀ x ∈ N₀, (c0 : E) • x ∈ s) ∧ s ⊆ N₀}`. Use `⟨⋃ N₀ ∈ {N₀ | N₀ ∈ SE ∧ N₀.FG}, Sub N₀, Set.Finite.biUnion (hSEf.subset fun N₀ h => h.1) fun N₀ h => sub_finite N₀ h.2 c0 hc0, ?_⟩` and prove the remaining obligations. Introduce `Λ h1 h2 h3 h4`. Establish `hDE : (D : E) ≠ 0` using `by exact_mod_cast hD.ne'`. Establish `hJdet : J.det ≠ 0`.

Introduce `h0`. Take `⟨τ⟩` from `(inferInstance : Nonempty (E →+* ℂ))`. Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).1 (hpos τ).isUnit`. Establish `e : (J.map τ).det = τ J.det` using `(RingHom.map_det τ J).symm`. Rewrite `hu` using `[e, h0, map_zero]`.

Conclude with `not_isUnit_zero hu`. Take `⟨d, hd, hdJ⟩` from `mat_den J⁻¹`. Use `set N : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Λ : Set (Fin M → E)) with hNdef`. Establish `smul_coe : ∀ (a : 𝓞 E) (y : Fin M → E), a • y = (a : E) • y` using `fun a y => rfl`. Establish `hI1 : ∀ x ∈ Λ, ∀ y ∈ N, IsIntegral ℤ ((D : E) * herm σ J x y)`.

Introduce `x hx y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact h3 x hx y hy`. Consider the case `zero => rw [herm_zero_right, mul_zero]`. Conclude with `isIntegral_zero`.

Consider the case `add y z _ _ h1 h2 => rw [herm_add_right, mul_add]`. Conclude with `h1.add h2`. Consider the case `smul a y _ h1`. Rewrite using `[smul_coe, herm_smul_right, mul_left_comm]`. Conclude with `a.isIntegral_coe.mul h1`.

Establish `hI : ∀ x ∈ N, ∀ y ∈ N, IsIntegral ℤ (herm σ J' x y)`. Introduce `x hx y hy`. Rewrite using `[hJ', herm_scale]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hI1 x hx y hy`.

Consider the case `zero => rw [herm_zero_left, mul_zero]`. Conclude with `isIntegral_zero`. Consider the case `add x z _ _ h1 h2 => rw [herm_add_left, mul_add]`. Conclude with `h1.add h2`. Consider the case `smul a x _ h1`.

Rewrite using `[smul_coe, herm_smul_left, mul_left_comm]`. Conclude with `(int_sigma σ a.isIntegral_coe).mul h1`. Establish `hDual : ∀ y : Fin M → E, (∀ x ∈ N, IsIntegral ℤ (herm σ J' x y)) → (T : E) • y ∈ N`. Introduce `y hy`. Use `Submodule.subset_span (h4 y fun x hx => ?_)` and prove the remaining obligations.

Use `hy x (Submodule.subset_span hx)` as an intermediate fact. Rewrite `this` using `[hJ', herm_scale]`. Then use the resulting hypothesis. Take `⟨k, hk, hkΛ⟩` from `h2`. Establish `hsing : ∀ i, (Pi.single i (k : E) : Fin M → E) ∈ Λ`. Introduce `i`.

Use `hkΛ i 1 isIntegral_one` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Establish `hNfg : N.FG`. Use `fg_of_den N (d * D * k) (Nat.mul_pos (Nat.mul_pos hd hD) hk) fun y hy j => ?_` and prove the remaining obligations. Establish `hJy : ∀ i, IsIntegral ℤ ((D : E) * (k : E) * (J.mulVec y) i)`.

Introduce `i`. Use `hI1 _ (hsing i) y hy` as an intermediate fact. Rewrite `this` using `[herm_single_left, ← mul_assoc]`. Then use the resulting hypothesis. Take `⟨w, hw⟩ : ∃ w, w = J.mulVec y` from `⟨_, rfl⟩`. Establish `hy' : y = J⁻¹.mulVec w`.

Rewrite using `[hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hJdet), Matrix.one_mulVec]`. Rewrite `hJy` using `[← hw]`. Establish `: ((d * D * k : ℕ) : E) * y j = ∑ i, ((d : E) * J⁻¹ j i) * ((D : E) * (k : E) * w i)` using `by conv_lhs => rw [hy']`. Rewrite using `[Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `IsIntegral.sum _ fun i _ => (hdJ j i).mul (hJy i)`. Establish `hNspan : Submodule.span E (N : Set (Fin M → E)) = ⊤`.

Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Establish `hkE : (k : E) ≠ 0` using `by exact_mod_cast hk.ne'`. Establish `hv : v = ∑ j, (v j / (k : E)) • (Pi.single j (k : E) : Fin M → E)` using `by conv_lhs => rw [← Finset.univ_sum_single v]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Pi.single_smul]`.

Use `congr 1`. Rewrite using `[smul_eq_mul, div_mul_cancel₀ _ hkE]`. Rewrite using `[hv]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span (hsing j)))`. Establish `hAdm : admitted σ J' T N` using `⟨⟨hNfg, hNspan⟩, hI, hDual⟩`.

Take `⟨N₀, hN₀, g, hg, hgN⟩` from `hSE N hAdm`. Establish `hJ'det : J'.det ≠ 0`. Rewrite using `[hJ', Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hDE) hJdet`. Establish `hgdet : g.det ≠ 0`.

Introduce `h0`. Use `congrArg Matrix.det hg` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Conclude with `hJ'det this.symm`. Establish `hgU : PI.UJClassFin.cT σ g * J * g = J`.

Establish `e1 : (g.map σ)ᵀ * J' * g = (D : E) • (PI.UJClassFin.cT σ g * J * g)`. Rewrite using `[hJ', Matrix.mul_smul, Matrix.smul_mul]`. Both sides reduce to the same expression. Use `hg` as an intermediate fact. Unfold `IsUJ at this`.

Rewrite `this` using `[e1]`. Conclude with `smul_right_injective _ hDE this`. Set `G : GL (Fin M) E` to `Matrix.nonsingInvUnit g (Ne.isUnit hgdet)`. Establish `hGg : ((G : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = g` using `rfl`. Establish `hGU : G ∈ PI.UJClassFin.UJ σ J` using `by show PI.UJClassFin.cT σ (G : Matrix (Fin M) (Fin M) E) * J * (G : Matrix (Fin M) (Fin M) E) = J`.

Rewrite using `[hGg]`. Conclude with `hgU`. Establish `hgi : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul _ (Ne.isUnit hgdet)`. Establish `hig : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (Ne.isUnit hgdet)`. Establish `hN₀eq : (N₀ : Set (Fin M → E)) = (fun x => g⁻¹.mulVec x) '' (N : Set (Fin M → E))`.

Rewrite using `[← hgN, Set.image_image]`. Simplify using `only [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec, Set.image_id']`. Establish `hN₀fg : N₀.FG`. Establish `: N₀ = N.map ((Matrix.mulVecLin g⁻¹).restrictScalars (𝓞 E))`. Apply `SetLike.coe_injective` to reduce the goal to its premises.

Rewrite using `[hN₀eq, Submodule.map_coe]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hNfg.map _`. Establish `hc0N : ∀ y ∈ N, (c0 : E) • y ∈ Λ`.

Set `Nc : Submodule (𝓞 E) (Fin M → E)` to `{ carrier := {y | ∀ a : 𝓞 E, (c0 : E) • ((a : E) • y) ∈ Λ} add_mem' := fun {y z} hy hz a => by rw [smul_add, smul_add]; exact Λ.add_mem (hy a) (hz a) zero_mem' := fun a => by rw [smul_zero, smul_zero]; exact Λ.zero_mem smul_mem' := fun b y hy a => by show (c0 : E) • ((a : E) • (b …`. Establish `e : (a : E) • (b • y) = ((a * b : 𝓞 E) : E) • y`. Rewrite using `[smul_coe b y, smul_smul]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `hy (a * b) }`. Establish `hle : N ≤ Nc`. Rewrite using `[hNdef, Submodule.span_le]`. Introduce `x hx a`. Rewrite using `[smul_smul]`.

Conclude with `h1 x hx _ a.isIntegral_coe`. Introduce `y hy`. Use `hle hy 1` as an intermediate fact. Rewrite `this` using `[show ((1 : 𝓞 E) : E) = 1 from rfl, one_smul]`. Then use the resulting hypothesis. Set `s : Set (Fin M → E)` to `(fun x => g⁻¹.mulVec x) '' (Λ : Set (Fin M → E))`.

Establish `hs : s ∈ Sub N₀`. Use `⟨⟨Λ.map (Matrix.mulVecLin g⁻¹).toAddMonoidHom, by rw [AddSubgroup.coe_map]; rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hgx : g.mulVec x ∈ N` using `by rw [← SetLike.mem_coe, ← hgN]; exact ⟨x, hx, rfl⟩`. Use `⟨(c0 : E) • g.mulVec x, hc0N _ hgx, ?_⟩` and prove the remaining obligations.

Use `show g⁻¹.mulVec ((c0 : E) • g.mulVec x) = (c0 : E) • x`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]`. Introduce and unpack `_ ⟨x, hx, rfl⟩ show g⁻¹.mulVec x ∈ (N₀ : Set (Fin M → E))`. Rewrite using `[hN₀eq]`. Conclude with `Set.mem_image_of_mem _ (Submodule.subset_span hx)`.

Use `⟨s, Set.mem_biUnion ⟨hN₀, hN₀fg⟩ hs, ⟨G, hGU⟩, ?_⟩` and prove the remaining obligations. Use `show (Λ : Set (Fin M → E)) = (fun x => g.mulVec x) '' s`. Rewrite using `[Set.image_image]`. Simplify using `only [Matrix.mulVec_mulVec, hig, Matrix.one_mulVec, Set.image_id']`.
-/
theorem lattice_classes_finite_refinement : LatFin := by
  intro E _ _ σ M J D T c0 hσ hpos hD hT hc0
  classical
  set J' : Matrix (Fin M) (Fin M) E := (D : E) • J with hJ'
  have hpos' : ∀ τ : E →+* ℂ, (J'.map τ).PosDef := by
    intro τ
    have : J'.map τ = (D : ℂ) • J.map τ := by
      ext i j
      simp [hJ', map_natCast]
    rw [this]
    exact (hpos τ).smul (by exact_mod_cast hD)
  obtain ⟨SE, hSEf, hSE⟩ := hermitian_lattice_finite E M σ J' T hσ hpos' hT
  let Sub : Submodule (𝓞 E) (Fin M → E) → Set (Set (Fin M → E)) := fun N₀ =>
    {s | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧ (∀ x ∈ N₀, (c0 : E) • x ∈ s) ∧ s ⊆ N₀}
  refine ⟨⋃ N₀ ∈ {N₀ | N₀ ∈ SE ∧ N₀.FG}, Sub N₀,
    Set.Finite.biUnion (hSEf.subset fun N₀ h => h.1) fun N₀ h => sub_finite N₀ h.2 c0 hc0, ?_⟩
  intro Λ h1 h2 h3 h4
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'

  have hJdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (hpos τ).isUnit
    have e : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [e, h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨d, hd, hdJ⟩ := mat_den J⁻¹
  set N : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Λ : Set (Fin M → E)) with hNdef
  have smul_coe : ∀ (a : 𝓞 E) (y : Fin M → E), a • y = (a : E) • y := fun a y => rfl

  have hI1 : ∀ x ∈ Λ, ∀ y ∈ N, IsIntegral ℤ ((D : E) * herm σ J x y) := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h3 x hx y hy
    | zero => rw [herm_zero_right, mul_zero]; exact isIntegral_zero
    | add y z _ _ h1 h2 => rw [herm_add_right, mul_add]; exact h1.add h2
    | smul a y _ h1 =>
      rw [smul_coe, herm_smul_right, mul_left_comm]
      exact a.isIntegral_coe.mul h1
  have hI : ∀ x ∈ N, ∀ y ∈ N, IsIntegral ℤ (herm σ J' x y) := by
    intro x hx y hy
    rw [hJ', herm_scale]
    induction hx using Submodule.span_induction with
    | mem x hx => exact hI1 x hx y hy
    | zero => rw [herm_zero_left, mul_zero]; exact isIntegral_zero
    | add x z _ _ h1 h2 => rw [herm_add_left, mul_add]; exact h1.add h2
    | smul a x _ h1 =>
      rw [smul_coe, herm_smul_left, mul_left_comm]
      exact (int_sigma σ a.isIntegral_coe).mul h1

  have hDual : ∀ y : Fin M → E, (∀ x ∈ N, IsIntegral ℤ (herm σ J' x y)) → (T : E) • y ∈ N := by
    intro y hy
    refine Submodule.subset_span (h4 y fun x hx => ?_)
    have := hy x (Submodule.subset_span hx)
    rwa [hJ', herm_scale] at this

  obtain ⟨k, hk, hkΛ⟩ := h2
  have hsing : ∀ i, (Pi.single i (k : E) : Fin M → E) ∈ Λ := by
    intro i
    have := hkΛ i 1 isIntegral_one
    rwa [mul_one] at this
  have hNfg : N.FG := by
    refine fg_of_den N (d * D * k) (Nat.mul_pos (Nat.mul_pos hd hD) hk) fun y hy j => ?_
    have hJy : ∀ i, IsIntegral ℤ ((D : E) * (k : E) * (J.mulVec y) i) := by
      intro i
      have := hI1 _ (hsing i) y hy
      rwa [herm_single_left, ← mul_assoc] at this
    obtain ⟨w, hw⟩ : ∃ w, w = J.mulVec y := ⟨_, rfl⟩
    have hy' : y = J⁻¹.mulVec w := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hJdet), Matrix.one_mulVec]
    rw [← hw] at hJy
    have : ((d * D * k : ℕ) : E) * y j = ∑ i, ((d : E) * J⁻¹ j i) * ((D : E) * (k : E) * w i) := by
      conv_lhs => rw [hy']
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [this]
    exact IsIntegral.sum _ fun i _ => (hdJ j i).mul (hJy i)
  have hNspan : Submodule.span E (N : Set (Fin M → E)) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hkE : (k : E) ≠ 0 := by exact_mod_cast hk.ne'
    have hv : v = ∑ j, (v j / (k : E)) • (Pi.single j (k : E) : Fin M → E) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Pi.single_smul]
      congr 1
      rw [smul_eq_mul, div_mul_cancel₀ _ hkE]
    rw [hv]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Submodule.subset_span (hsing j)))
  have hAdm : admitted σ J' T N := ⟨⟨hNfg, hNspan⟩, hI, hDual⟩
  obtain ⟨N₀, hN₀, g, hg, hgN⟩ := hSE N hAdm

  have hJ'det : J'.det ≠ 0 := by
    rw [hJ', Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hDE) hJdet
  have hgdet : g.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact hJ'det this.symm
  have hgU : PI.UJClassFin.cT σ g * J * g = J := by
    have e1 : (g.map σ)ᵀ * J' * g = (D : E) • (PI.UJClassFin.cT σ g * J * g) := by
      rw [hJ', Matrix.mul_smul, Matrix.smul_mul]
      rfl
    have := hg
    unfold IsUJ at this
    rw [e1] at this
    exact smul_right_injective _ hDE this
  let G : GL (Fin M) E := Matrix.nonsingInvUnit g (Ne.isUnit hgdet)
  have hGg : ((G : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = g := rfl
  have hGU : G ∈ PI.UJClassFin.UJ σ J := by
    show PI.UJClassFin.cT σ (G : Matrix (Fin M) (Fin M) E) * J * (G : Matrix (Fin M) (Fin M) E) = J
    rw [hGg]; exact hgU
  have hgi : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hgdet)
  have hig : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hgdet)

  have hN₀eq : (N₀ : Set (Fin M → E)) = (fun x => g⁻¹.mulVec x) '' (N : Set (Fin M → E)) := by
    rw [← hgN, Set.image_image]
    simp only [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec, Set.image_id']
  have hN₀fg : N₀.FG := by
    have : N₀ = N.map ((Matrix.mulVecLin g⁻¹).restrictScalars (𝓞 E)) := by
      apply SetLike.coe_injective
      rw [hN₀eq, Submodule.map_coe]
      rfl
    rw [this]
    exact hNfg.map _

  have hc0N : ∀ y ∈ N, (c0 : E) • y ∈ Λ := by
    let Nc : Submodule (𝓞 E) (Fin M → E) :=
      { carrier := {y | ∀ a : 𝓞 E, (c0 : E) • ((a : E) • y) ∈ Λ}
        add_mem' := fun {y z} hy hz a => by rw [smul_add, smul_add]; exact Λ.add_mem (hy a) (hz a)
        zero_mem' := fun a => by rw [smul_zero, smul_zero]; exact Λ.zero_mem
        smul_mem' := fun b y hy a => by
          show (c0 : E) • ((a : E) • (b • y)) ∈ Λ
          have e : (a : E) • (b • y) = ((a * b : 𝓞 E) : E) • y := by
            rw [smul_coe b y, smul_smul]
            rfl
          rw [e]
          exact hy (a * b) }
    have hle : N ≤ Nc := by
      rw [hNdef, Submodule.span_le]
      intro x hx a
      rw [smul_smul]
      exact h1 x hx _ a.isIntegral_coe
    intro y hy
    have := hle hy 1
    rwa [show ((1 : 𝓞 E) : E) = 1 from rfl, one_smul] at this
  let s : Set (Fin M → E) := (fun x => g⁻¹.mulVec x) '' (Λ : Set (Fin M → E))
  have hs : s ∈ Sub N₀ := by
    refine ⟨⟨Λ.map (Matrix.mulVecLin g⁻¹).toAddMonoidHom, by rw [AddSubgroup.coe_map]; rfl⟩, ?_, ?_⟩
    · intro x hx
      have hgx : g.mulVec x ∈ N := by rw [← SetLike.mem_coe, ← hgN]; exact ⟨x, hx, rfl⟩
      refine ⟨(c0 : E) • g.mulVec x, hc0N _ hgx, ?_⟩
      show g⁻¹.mulVec ((c0 : E) • g.mulVec x) = (c0 : E) • x
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
    · rintro _ ⟨x, hx, rfl⟩
      show g⁻¹.mulVec x ∈ (N₀ : Set (Fin M → E))
      rw [hN₀eq]
      exact Set.mem_image_of_mem _ (Submodule.subset_span hx)
  refine ⟨s, Set.mem_biUnion ⟨hN₀, hN₀fg⟩ hs, ⟨G, hGU⟩, ?_⟩
  show (Λ : Set (Fin M → E)) = (fun x => g.mulVec x) '' s
  rw [Set.image_image]
  simp only [Matrix.mulVec_mulVec, hig, Matrix.one_mulVec, Set.image_id']

end PI.UnitaryGroupMassFormula.UJClassFin
