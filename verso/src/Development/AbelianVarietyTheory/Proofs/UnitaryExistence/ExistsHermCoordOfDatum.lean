import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix
open scoped nonZeroDivisors TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DatumCoord

variable {E : Type} [Field E] [NumberField E]

open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
/- English proof (translation)
Assume the negation of the conclusion as `hcd`. Establish `hne : c - d ≠ 0` using `sub_ne_zero.2 hcd`. Establish `halg : IsAlgebraic ℤ (c - d)⁻¹` using `IsFractionRing.isAlgebraic_iff ℤ ℚ _ |>.mpr (.of_finite ℚ _)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Establish `key` using `h ⟨y • (c - d)⁻¹, hint⟩`.

Rewrite `key` using `[← sub_eq_zero, ← map_sub, ← mul_sub]`. Express the relevant statement in the definitionally equal form `Algebra.trace ℚ E (y • (c - d)⁻¹ * (c - d)) = 0 at key`. Rewrite `key` using `[zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one, show (y : E) = algebraMap ℚ E y by simp, Algebra.trace_algebraMap]`. Simplify using `[hy, Module.finrank_pos.ne'] at key`.
-/
theorem _root_.GlobalTheory.DatumCoord.eq_of_trace_int {c d : E}
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * c) = Algebra.trace ℚ E ((a : E) * d)) :
    c = d := by
  by_contra hcd
  have hne : c - d ≠ 0 := sub_ne_zero.2 hcd
  have halg : IsAlgebraic ℤ (c - d)⁻¹ :=
    IsFractionRing.isAlgebraic_iff ℤ ℚ _ |>.mpr (.of_finite ℚ _)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have key := h ⟨y • (c - d)⁻¹, hint⟩
  rw [← sub_eq_zero, ← map_sub, ← mul_sub] at key
  change Algebra.trace ℚ E (y • (c - d)⁻¹ * (c - d)) = 0 at key
  rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one,
    show (y : E) = algebraMap ℚ E y by simp, Algebra.trace_algebraMap] at key
  simp [hy, Module.finrank_pos.ne'] at key

/- English proof (translation)
Establish `hb` using `TensorProduct.isBaseChange (𝓞 E) M E`. Establish `hl` using `(isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E _).2 hb`. Establish `h1 : Module.finrank E (E ⊗[𝓞 E] M) = r`. Rewrite using `[IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl, IsLocalizedModule.finrank_eq (𝓞 E)⁰ (TensorProduct.mk (𝓞 E) E M 1) le_rfl, hr]`. Set `e` to `(Module.finBasisOfFinrankEq E (E ⊗[𝓞 E] M) h1).equivFun`.

Conclude with `⟨e.toLinearMap.restrictScalars (𝓞 E) ∘ₗ TensorProduct.mk (𝓞 E) E M 1, IsBaseChange.of_equiv e fun _ => rfl⟩`.
-/
theorem exists_coord (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    (r : ℕ) (hr : Module.finrank (𝓞 E) M = r) :
    ∃ φ : M →ₗ[𝓞 E] (Fin r → E), IsBaseChange E φ := by
  have hb := TensorProduct.isBaseChange (𝓞 E) M E
  have hl := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E _).2 hb
  have h1 : Module.finrank E (E ⊗[𝓞 E] M) = r := by
    rw [IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl,
      IsLocalizedModule.finrank_eq (𝓞 E)⁰ (TensorProduct.mk (𝓞 E) E M 1) le_rfl, hr]
  let e := (Module.finBasisOfFinrankEq E (E ⊗[𝓞 E] M) h1).equivFun
  exact ⟨e.toLinearMap.restrictScalars (𝓞 E) ∘ₗ TensorProduct.mk (𝓞 E) E M 1,
    IsBaseChange.of_equiv e fun _ => rfl⟩

variable [IsCMField E]

end GlobalTheory.DatumCoord

namespace GlobalTheory

open DatumCoord

open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
/- English proof (translation)
Set `g : E →ₗ[ℚ] ℚ` to `(integralBasis E).constr ℚ (fun i => (f (RingOfIntegers.basis E i) : ℚ))`. Establish `hnd` using `traceForm_nondegenerate ℚ E`. Take `⟨z, hz⟩` from `((Algebra.traceForm ℚ E).toDual hnd).surjective g`. Use `⟨z, fun a => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ b : E, Algebra.trace ℚ E (b * z) = g b` using `fun b => by`.

Rewrite using `[← hz]`. Simplify using `[LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, mul_comm]`. Set `u : 𝓞 E →ₗ[ℤ] ℚ` to `(g.restrictScalars ℤ).comp ((algebraMap (𝓞 E) E : 𝓞 E →+* E).toIntAlgHom.toLinearMap)`. Set `v : 𝓞 E →ₗ[ℤ] ℚ` to `(Int.castRingHom ℚ).toIntAlgHom.toLinearMap.comp f.toIntLinearMap`. Establish `huv : u = v` using `(RingOfIntegers.basis E).ext fun i => by`.

Simplify using `[u, v, g, ← integralBasis_apply]`. Rewrite using `[h1]`. Conclude with `congrArg (fun w : 𝓞 E →ₗ[ℤ] ℚ => w a) huv`.
-/
private lemma exists_trace_mul_eq_of_addMonoidHom (f : 𝓞 E →+ ℤ) :
    ∃ z : E, ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * z) = (f a : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => (f (RingOfIntegers.basis E i) : ℚ))
  have hnd := traceForm_nondegenerate ℚ E
  obtain ⟨z, hz⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective g
  refine ⟨z, fun a => ?_⟩
  have h1 : ∀ b : E, Algebra.trace ℚ E (b * z) = g b := fun b => by
    rw [← hz]; simp [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, mul_comm]
  let u : 𝓞 E →ₗ[ℤ] ℚ :=
    (g.restrictScalars ℤ).comp ((algebraMap (𝓞 E) E : 𝓞 E →+* E).toIntAlgHom.toLinearMap)
  let v : 𝓞 E →ₗ[ℤ] ℚ := (Int.castRingHom ℚ).toIntAlgHom.toLinearMap.comp f.toIntLinearMap
  have huv : u = v := (RingOfIntegers.basis E).ext fun i => by
    simp [u, v, g, ← integralBasis_apply]
  rw [h1]
  exact congrArg (fun w : 𝓞 E →ₗ[ℤ] ℚ => w a) huv

open NumberField Matrix in
open scoped nonZeroDivisors TensorProduct in

/- English proof (translation)
Introduce `E _ _ _ H D ξ hξ hξ0 r hr`. Establish `hz : ∀ x y : D.La, ∃ z : E, ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * z) = (D.EF (a • x) y : ℚ)` using `fun x y => exists_trace_mul_eq_of_addMonoidHom (AddMonoidHom.mk' (fun a => D.EF (a • x) y) fun a b => by simp [add_smul])`. Use `choose h0 hh0 using hz`. Establish `huniq` using `fun c d h => _root_.GlobalTheory.DatumCoord.eq_of_trace_int (E := E) (c := c) (d := d) h`. Establish `hsmul : ∀ (b : 𝓞 E) x y, h0 (b • x) y = b * h0 x y` using `fun b x y => huniq _ _ fun a => by`.

Rewrite using `[hh0, ← mul_assoc, ← map_mul, hh0, smul_smul]`. Establish `hadd : ∀ x x' y, h0 (x + x') y = h0 x y + h0 x' y` using `fun x x' y => huniq _ _ fun a => by`. Rewrite using `[hh0, mul_add, map_add, hh0, hh0]`. Simplify using `[smul_add]`. Establish `hadd' : ∀ x y y', h0 x (y + y') = h0 x y + h0 x y'` using `fun x y y' => huniq _ _ fun a => by`.

Rewrite using `[mul_add, map_add, hh0, hh0, hh0, map_add, Int.cast_add]`. Set `σ : E ≃ₐ[ℚ] E` to `(IsCMField.complexConj E).restrictScalars ℚ`. Establish `hσ : ∀ e, σ e = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc e` using `fun e => rfl`. Establish `hσσ : ∀ e, σ (σ e) = e` using `fun e => by simp [σ]`. Establish `hbar : ∀ b, ((H.bar b : 𝓞 E) : E) = σ b` using `fun b => H.bar_eq b`.

Establish `hbb : ∀ b, H.bar (H.bar b) = b` using `fun b => RingOfIntegers.ext (by rw [hbar, hbar, hσσ])`. Establish `htr : ∀ e, Algebra.trace ℚ E (σ e) = Algebra.trace ℚ E e` using `fun e => Algebra.trace_eq_of_algEquiv σ e`. Establish `hanti : ∀ u v, D.EF u v = - D.EF v u` using `fun u v => by`. Establish `h` using `D.alt (u + v)`. Simplify using `only [map_add, LinearMap.add_apply, D.alt u, D.alt v] at h`.

Use linear arithmetic over natural numbers and integers. Establish `hsmul' : ∀ (b : 𝓞 E) x y, h0 x (b • y) = σ b * h0 x y` using `fun b x y => huniq _ _ fun a => by`. Rewrite using `[hh0, ← hbb b, ← D.adj, smul_smul, ← hh0, hbb]`. Use `congr 1`. Move the coercions through the operations in `[hbar]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hherm : ∀ x y, h0 y x = - σ (h0 x y)` using `fun x y => huniq _ _ fun a => by`. Rewrite using `[hh0, hanti, ← hbb a, ← D.adj, Int.cast_neg, ← hh0, hbb, hbar, ← htr (σ a * h0 x y), map_mul, hσσ, mul_neg, map_neg]`. Use `haveI := D.fin`. Establish `hrk : Module.finrank (𝓞 E) D.La = r` using `hr ▸ D.rank`.

Take `⟨l, hl⟩` from `exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := D.La) hrk.ge`. Establish `hmax : ∀ x : D.La, ∃ t : 𝓞 E, t ≠ 0 ∧ ∃ c : Fin r → 𝓞 E, ∑ i, c i • l i = t • x`. Introduce `x`. Establish `hnot : ¬ LinearIndependent (𝓞 E) (Fin.snoc l x : Fin (r + 1) → D.La)` using `fun h => by`. Use `h.fintype_card_le_finrank` as an intermediate fact.

Simplify using `[hrk] at this`. Take `⟨g, hg, i, hi⟩` from `Fintype.not_linearIndependent_iff.1 hnot`. Rewrite `hg` using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last] at hg`. Use `⟨g (Fin.last r), fun hg0 => hi ?_, fun j => -g j.castSucc, ?_⟩` and prove the remaining obligations.

Rewrite `hg` using `[hg0, zero_smul, add_zero]`. Use `Fintype.linearIndependent_iff.1 hl _ hg` as an intermediate fact. Break down `Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl` into its components or cases. Conclude with `this j`. Conclude with `hg0`.

Simplify using `only [neg_smul, Finset.sum_neg_distrib]`. Conclude with `neg_eq_of_add_eq_zero_right hg`. Establish `hz0 : ∀ y, h0 0 y = 0` using `fun y => by simpa using hadd 0 0 y`. Establish `hz0' : ∀ x, h0 x 0 = 0` using `fun x => by simpa using hadd' x 0 0`. Establish `hsumL : ∀ (c : Fin r → 𝓞 E) y, h0 (∑ i, c i • l i) y = ∑ i, (c i : E) * h0 (l i) y`.

Introduce `c y`. Proceed by induction on `(Finset.univ : Finset (Fin r)) using Finset.induction_on with`. Consider the case `empty => simp [hz0]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]`. Establish `hsumR : ∀ (d : Fin r → 𝓞 E) x, h0 x (∑ j, d j • l j) = ∑ j, σ (d j) * h0 x (l j)`.

Introduce `d x`. Proceed by induction on `(Finset.univ : Finset (Fin r)) using Finset.induction_on with`. Consider the case `empty => simp [hz0']`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd', hsmul', ih]`. Establish `hσ0 : ∀ s : 𝓞 E, s ≠ 0 → σ s ≠ 0` using `fun s hs => by simpa using hs`.

Establish `hnd : ∀ x, (∀ y, h0 x y = 0) → x = 0` using `fun x hx => D.unimod.1 (LinearMap.ext fun y => by`. Use `hh0 x y 1` as an intermediate fact. Rewrite `this` using `[hx, mul_zero, map_zero, one_smul]`. Simplify using `only [map_zero, LinearMap.zero_apply]`. Conclude with `this.symm)` after adjusting the coercions.

Set `ψ : D.La →ₗ[𝓞 E] (Fin r → E)` to `{ toFun := fun x j => h0 x (l j) map_add' := fun x y => funext fun j => hadd _ _ _ map_smul' := fun b x => funext fun j => by simp [hsmul, Algebra.smul_def] }`. Establish `hψ : ∀ x j, ψ x j = h0 x (l j)` using `fun x j => rfl`. Establish `hinj : Function.Injective ψ` using `(injective_iff_map_eq_zero ψ).2 fun x hx => hnd x fun y => by`. Take `⟨s, hs, d, hd⟩` from `hmax y`. Establish `h1 : σ s * h0 x y = 0`.

Rewrite using `[← hsmul', ← hd, hsumR]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [← hψ, hx]; simp`. Conclude with `(mul_eq_zero.1 h1).resolve_left (hσ0 s hs)`. Set `gram : Matrix (Fin r) (Fin r) E` to `Matrix.of fun i j => h0 (l i) (l j)`. Establish `hgramσ : ∀ i j, σ (gram i j) = - gram j i` using `fun i j => by`.

Simplify using `[gram, hherm (l i) (l j), hσσ]`. Establish `hdet : gram.det ≠ 0`. Introduce `h`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h`. Take `⟨⟨m, hm⟩, hmv⟩` from `IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ v`.

Use `choose c hc using fun i => hmv i (Finset.mem_univ i)`. Establish `hx : ∑ i, c i • l i = 0` using `hinj <| funext fun j => by`. Rewrite using `[map_zero, Pi.zero_apply, hψ, hsumL]`. Use `congrFun hv j` as an intermediate fact. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply, gram, Matrix.of_apply] at this`.

Simplify using `only [hc, Submonoid.smul_def, Algebra.smul_def, mul_assoc, ← Finset.mul_sum, this, mul_zero]`. Establish `hc0` using `Fintype.linearIndependent_iff.1 hl c hx`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `hc i` as an intermediate fact.

Rewrite `this` using `[hc0 i, map_zero, Algebra.smul_def]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left (by simpa using nonZeroDivisors.ne_zero hm)`. Use `⟨-ξ⁻¹ • gram⁻¹, ψ, hinj, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `w _`.

Establish `hw : w = ∑ i, (w ᵥ* gram⁻¹) i • ψ (l i)`. Establish `hsum : ∑ i, (w ᵥ* gram⁻¹) i • ψ (l i) = (w ᵥ* gram⁻¹) ᵥ* gram`. Use function extensionality and compare the values at `j`. Simplify using `[Matrix.vecMul, dotProduct, Finset.sum_apply, hψ, gram]`. Rewrite using `[hsum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.vecMul_one]`.

Rewrite using `[hw]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l i, rfl⟩)`. Establish `hu : IsUnit gram.det` using `isUnit_iff_ne_zero.2 hdet`. Establish `h1 : gram.map σ = -gramᵀ`. Use extensionality with `i j`.

Simplify using `[hgramσ]`. Establish `e1 : (gram⁻¹).map σ * gram.map σ = 1`. Establish `h3 : (gram⁻¹ * gram).map (σ : E →+* E) = (gram⁻¹).map σ * gram.map σ` using `Matrix.map_mul`. Rewrite using `[← h3, Matrix.nonsing_inv_mul _ hu]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `e2 : -(gram⁻¹)ᵀ * gram.map σ = 1`. Rewrite using `[h1, neg_mul_neg, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]`. Establish `hinvσ : (gram⁻¹).map σ = -(gram⁻¹)ᵀ` using `(Matrix.inv_eq_left_inv e1).symm.trans (Matrix.inv_eq_left_inv e2)`. Introduce `a b`. Establish `h2` using `congrFun (congrFun hinvσ a) b`.

Establish `hξσ : σ ξ = -ξ` using `hξ`. Simplify using `only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply] at h2`. Rewrite using `[← hσ]`. Simplify using `[Matrix.smul_apply, map_inv₀, hξσ, h2]`. Rewrite using `[Matrix.det_smul]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hξ0))) (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hdet)).ne_zero`. Establish `hu : IsUnit gram.det` using `isUnit_iff_ne_zero.2 hdet`. Introduce `x y`. Take `⟨t, ht, c, hc⟩` from `hmax x`. Take `⟨s, hs, d, hd⟩` from `hmax y`.

Establish `ht' : (t : E) ≠ 0` using `by simpa using ht`. Set `cv : Fin r → E` to `fun i => c i`. Set `dv : Fin r → E` to `fun j => σ (d j)`. Establish `hA : (fun j => (t : E) * ψ x j) = cv ᵥ* gram` using `funext fun j => by`. Rewrite using `[hψ, ← hsmul, ← hc, hsumL]`.

Simplify using `[Matrix.vecMul, dotProduct, cv, gram]`. Establish `hB : (fun b => -(σ (s : E) * σ (ψ y b))) = gram *ᵥ dv` using `funext fun b => by`. Rewrite using `[hψ, hherm (l b) y, map_neg, hσσ, mul_neg, neg_neg, ← hsmul', ← hd, hsumR]`. Simplify using `[Matrix.mulVec, dotProduct, dv, gram, mul_comm]`. Establish `hC : (t : E) * σ s * h0 x y = cv ⬝ᵥ (gram *ᵥ dv)`.

Rewrite using `[mul_assoc, ← hsmul', ← hsmul, ← hc, ← hd, hsumL]`. Simplify using `only [hsumR, Matrix.mulVec, dotProduct, Finset.mul_sum, cv, dv, gram, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `key : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (-ξ⁻¹ • gram⁻¹) (ψ x) (ψ y) = h0 x y`. Apply `mul_left_cancel₀ (mul_ne_zero ht' (hσ0 s hs))` to reduce the goal to its premises.

Rewrite using `[hC, ← vecMul_one cv, ← Matrix.mul_nonsing_inv _ hu, ← vecMul_vecMul, ← dotProduct_mulVec, ← hA, ← hB]`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.herm`. Simplify using `only [← hσ, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Establish `h1` using `hh0 x y 1`. Rewrite `h1` using `[one_smul]`. Rewrite using `[key, ← h1]`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.exists_herm_coord_of_datum :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (ξ : E),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → ξ ≠ 0 → ∀ r : ℕ, r = D.p + D.q →
      ∃ (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)),
        (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
          (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
          ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) := by
  intro E _ _ _ H D ξ hξ hξ0 r hr
  have hz : ∀ x y : D.La, ∃ z : E, ∀ a : 𝓞 E,
      Algebra.trace ℚ E ((a : E) * z) = (D.EF (a • x) y : ℚ) := fun x y =>
    exists_trace_mul_eq_of_addMonoidHom (AddMonoidHom.mk' (fun a => D.EF (a • x) y) fun a b => by simp [add_smul])
  choose h0 hh0 using hz
  have huniq := fun c d h => _root_.GlobalTheory.DatumCoord.eq_of_trace_int (E := E) (c := c) (d := d) h
  have hsmul : ∀ (b : 𝓞 E) x y, h0 (b • x) y = b * h0 x y := fun b x y => huniq _ _ fun a => by
    rw [hh0, ← mul_assoc, ← map_mul, hh0, smul_smul]
  have hadd : ∀ x x' y, h0 (x + x') y = h0 x y + h0 x' y := fun x x' y => huniq _ _ fun a => by
    rw [hh0, mul_add, map_add, hh0, hh0]; simp [smul_add]
  have hadd' : ∀ x y y', h0 x (y + y') = h0 x y + h0 x y' := fun x y y' => huniq _ _ fun a => by
    rw [mul_add, map_add, hh0, hh0, hh0, map_add, Int.cast_add]
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσ : ∀ e, σ e = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc e := fun e => rfl
  have hσσ : ∀ e, σ (σ e) = e := fun e => by simp [σ]
  have hbar : ∀ b, ((H.bar b : 𝓞 E) : E) = σ b := fun b => H.bar_eq b
  have hbb : ∀ b, H.bar (H.bar b) = b := fun b => RingOfIntegers.ext (by rw [hbar, hbar, hσσ])
  have htr : ∀ e, Algebra.trace ℚ E (σ e) = Algebra.trace ℚ E e := fun e =>
    Algebra.trace_eq_of_algEquiv σ e
  have hanti : ∀ u v, D.EF u v = - D.EF v u := fun u v => by
    have h := D.alt (u + v)
    simp only [map_add, LinearMap.add_apply, D.alt u, D.alt v] at h
    omega
  have hsmul' : ∀ (b : 𝓞 E) x y, h0 x (b • y) = σ b * h0 x y := fun b x y => huniq _ _ fun a => by
    rw [hh0, ← hbb b, ← D.adj, smul_smul, ← hh0, hbb]
    congr 1
    push_cast [hbar]
    ring
  have hherm : ∀ x y, h0 y x = - σ (h0 x y) := fun x y => huniq _ _ fun a => by
    rw [hh0, hanti, ← hbb a, ← D.adj, Int.cast_neg, ← hh0, hbb, hbar, ← htr (σ a * h0 x y),
      map_mul, hσσ, mul_neg, map_neg]
  haveI := D.fin
  have hrk : Module.finrank (𝓞 E) D.La = r := hr ▸ D.rank
  obtain ⟨l, hl⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := D.La) hrk.ge
  have hmax : ∀ x : D.La, ∃ t : 𝓞 E, t ≠ 0 ∧ ∃ c : Fin r → 𝓞 E, ∑ i, c i • l i = t • x := by
    intro x
    have hnot : ¬ LinearIndependent (𝓞 E) (Fin.snoc l x : Fin (r + 1) → D.La) := fun h => by
      have := h.fintype_card_le_finrank
      simp [hrk] at this
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
    rw [Fin.sum_univ_castSucc] at hg
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
    refine ⟨g (Fin.last r), fun hg0 => hi ?_, fun j => -g j.castSucc, ?_⟩
    · rw [hg0, zero_smul, add_zero] at hg
      have := Fintype.linearIndependent_iff.1 hl _ hg
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact this j
      · exact hg0
    · simp only [neg_smul, Finset.sum_neg_distrib]
      exact neg_eq_of_add_eq_zero_right hg
  have hz0 : ∀ y, h0 0 y = 0 := fun y => by simpa using hadd 0 0 y
  have hz0' : ∀ x, h0 x 0 = 0 := fun x => by simpa using hadd' x 0 0
  have hsumL : ∀ (c : Fin r → 𝓞 E) y, h0 (∑ i, c i • l i) y = ∑ i, (c i : E) * h0 (l i) y := by
    intro c y
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [hz0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih]
  have hsumR : ∀ (d : Fin r → 𝓞 E) x, h0 x (∑ j, d j • l j) = ∑ j, σ (d j) * h0 x (l j) := by
    intro d x
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp [hz0']
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd', hsmul', ih]
  have hσ0 : ∀ s : 𝓞 E, s ≠ 0 → σ s ≠ 0 := fun s hs => by simpa using hs
  have hnd : ∀ x, (∀ y, h0 x y = 0) → x = 0 := fun x hx => D.unimod.1 (LinearMap.ext fun y => by
    have := hh0 x y 1
    rw [hx, mul_zero, map_zero, one_smul] at this
    simp only [map_zero, LinearMap.zero_apply]
    exact_mod_cast this.symm)
  let ψ : D.La →ₗ[𝓞 E] (Fin r → E) :=
    { toFun := fun x j => h0 x (l j)
      map_add' := fun x y => funext fun j => hadd _ _ _
      map_smul' := fun b x => funext fun j => by simp [hsmul, Algebra.smul_def] }
  have hψ : ∀ x j, ψ x j = h0 x (l j) := fun x j => rfl
  have hinj : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun x hx => hnd x fun y => by
    obtain ⟨s, hs, d, hd⟩ := hmax y
    have h1 : σ s * h0 x y = 0 := by
      rw [← hsmul', ← hd, hsumR]
      exact Finset.sum_eq_zero fun j _ => by rw [← hψ, hx]; simp
    exact (mul_eq_zero.1 h1).resolve_left (hσ0 s hs)
  let gram : Matrix (Fin r) (Fin r) E := Matrix.of fun i j => h0 (l i) (l j)
  have hgramσ : ∀ i j, σ (gram i j) = - gram j i := fun i j => by
    simp [gram, hherm (l i) (l j), hσσ]
  have hdet : gram.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨⟨m, hm⟩, hmv⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ v
    choose c hc using fun i => hmv i (Finset.mem_univ i)
    have hx : ∑ i, c i • l i = 0 := hinj <| funext fun j => by
      rw [map_zero, Pi.zero_apply, hψ, hsumL]
      have := congrFun hv j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, gram, Matrix.of_apply] at this
      simp only [hc, Submonoid.smul_def, Algebra.smul_def, mul_assoc, ← Finset.mul_sum, this,
        mul_zero]
    have hc0 := Fintype.linearIndependent_iff.1 hl c hx
    apply hv0
    funext i
    have := hc i
    rw [hc0 i, map_zero, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (by simpa using nonZeroDivisors.ne_zero hm)
  refine ⟨-ξ⁻¹ • gram⁻¹, ψ, hinj, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro w _
    have hw : w = ∑ i, (w ᵥ* gram⁻¹) i • ψ (l i) := by
      have hsum : ∑ i, (w ᵥ* gram⁻¹) i • ψ (l i) = (w ᵥ* gram⁻¹) ᵥ* gram := by
        funext j
        simp [Matrix.vecMul, dotProduct, Finset.sum_apply, hψ, gram]
      rw [hsum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
        Matrix.vecMul_one]
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l i, rfl⟩)
  · have hu : IsUnit gram.det := isUnit_iff_ne_zero.2 hdet
    have h1 : gram.map σ = -gramᵀ := by
      ext i j
      simp [hgramσ]
    have e1 : (gram⁻¹).map σ * gram.map σ = 1 := by
      have h3 : (gram⁻¹ * gram).map (σ : E →+* E) = (gram⁻¹).map σ * gram.map σ := Matrix.map_mul
      rw [← h3, Matrix.nonsing_inv_mul _ hu]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : -(gram⁻¹)ᵀ * gram.map σ = 1 := by
      rw [h1, neg_mul_neg, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    have hinvσ : (gram⁻¹).map σ = -(gram⁻¹)ᵀ :=
      (Matrix.inv_eq_left_inv e1).symm.trans (Matrix.inv_eq_left_inv e2)
    intro a b
    have h2 := congrFun (congrFun hinvσ a) b
    have hξσ : σ ξ = -ξ := hξ
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply] at h2
    rw [← hσ]
    simp [Matrix.smul_apply, map_inv₀, hξσ, h2]
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hξ0)))
      (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hdet)).ne_zero
  · have hu : IsUnit gram.det := isUnit_iff_ne_zero.2 hdet
    intro x y
    obtain ⟨t, ht, c, hc⟩ := hmax x
    obtain ⟨s, hs, d, hd⟩ := hmax y
    have ht' : (t : E) ≠ 0 := by simpa using ht
    let cv : Fin r → E := fun i => c i
    let dv : Fin r → E := fun j => σ (d j)
    have hA : (fun j => (t : E) * ψ x j) = cv ᵥ* gram := funext fun j => by
      rw [hψ, ← hsmul, ← hc, hsumL]
      simp [Matrix.vecMul, dotProduct, cv, gram]
    have hB : (fun b => -(σ (s : E) * σ (ψ y b))) = gram *ᵥ dv := funext fun b => by
      rw [hψ, hherm (l b) y, map_neg, hσσ, mul_neg, neg_neg, ← hsmul', ← hd, hsumR]
      simp [Matrix.mulVec, dotProduct, dv, gram, mul_comm]
    have hC : (t : E) * σ s * h0 x y = cv ⬝ᵥ (gram *ᵥ dv) := by
      rw [mul_assoc, ← hsmul', ← hsmul, ← hc, ← hd, hsumL]
      simp only [hsumR, Matrix.mulVec, dotProduct, Finset.mul_sum, cv, dv, gram, Matrix.of_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have key : ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (-ξ⁻¹ • gram⁻¹) (ψ x) (ψ y) = h0 x y := by
      apply mul_left_cancel₀ (mul_ne_zero ht' (hσ0 s hs))
      rw [hC, ← vecMul_one cv, ← Matrix.mul_nonsing_inv _ hu, ← vecMul_vecMul, ← dotProduct_mulVec,
        ← hA, ← hB]
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
      simp only [← hσ, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    have h1 := hh0 x y 1
    rw [one_smul] at h1
    rw [key, ← h1]
    simp

end GlobalTheory
