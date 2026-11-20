import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
namespace GlobalTheory.EigLine

/- English proof (translation)
Introduce `E _ _ O hO L hL W _ _ P hspan hdim T hT τ`. Establish `hext : ∀ f g : Module.End ℂ W, (∀ x : L, f (P x) = g (P x)) → f = g` using `fun f g h => LinearMap.ext_on_range hspan h`. Set `mulL : O → L → L` to `fun a x => ⟨(a : E) * x, hL a a.2 x x.2⟩`. Establish `hT' : ∀ (a : O) (x : L), T a (P x) = P (mulL a x)` using `fun a x => hT a x _ rfl`. Set `TR : O →+* Module.End ℂ W` to `{ toFun := T map_one' := hext _ _ fun x => by`.

Rewrite using `[hT', Module.End.one_apply]`. Use `congr 1`. Use `ext`. Simplify using `[mulL]`. Use the proof step `map_mul' := fun a b => hext _ _ fun x => by`.

Rewrite using `[Module.End.mul_apply, hT', hT', hT']`. Use `congr 1`. Use `ext`. Simplify using `[mulL]`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `map_zero' := hext _ _ fun x => by`. Rewrite using `[hT', LinearMap.zero_apply]`. Use `P.map_zero` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using `[mulL]`.

Use the proof step `map_add' := fun a b => hext _ _ fun x => by`. Rewrite using `[LinearMap.add_apply, hT', hT', hT', ← map_add]`. Use `congr 1`. Use `ext`. Simplify using `[mulL, add_mul] }`.

Take `⟨α, hα⟩` from `Field.exists_primitive_element ℚ E`. Take `⟨n, hn0, hnO⟩` from `hO α`. Establish `hnE : (n : E) ≠ 0` using `by exact_mod_cast hn0`. Use `set θ : E := (n : E) * α with hθdef`. Set `θO : O` to `⟨θ, hnO⟩`.

Establish `hint : IsIntegral ℚ θ` using `Algebra.IsIntegral.isIntegral θ`. Establish `hθtop : IntermediateField.adjoin ℚ {θ} = ⊤`. Rewrite using `[eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]`. Establish `: α = θ / (n : E)` using `by rw [hθdef]; field_simp`. Rewrite using `[this]`.

Conclude with `div_mem (IntermediateField.mem_adjoin_simple_self ℚ θ) (natCast_mem _ n)`. Establish `hadj : Algebra.adjoin ℚ {θ} = ⊤`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθtop, IntermediateField.top_toSubalgebra]`. Set `pb` to `PowerBasis.ofAdjoinEqTop hint hadj`. Establish `hpbdim : pb.dim = Module.finrank ℚ E` using `pb.finrank.symm`.

Establish `hpbgen : pb.gen = θ` using `rfl`. Set `Zd : Submodule ℤ O` to `Submodule.span ℤ (Set.range fun k : Fin pb.dim => θO ^ (k : ℕ))`. Establish `hA : ∀ y : E, ∃ N : ℕ, N ≠ 0 ∧ ∃ z ∈ Zd, (z : E) = N * y`. Introduce `y`. Establish `hy : y ∈ Submodule.span ℚ (Set.range fun k : Fin pb.dim => θ ^ (k : ℕ))`.

Establish `h` using `pb.basis.span_eq`. Rewrite `h` using `[pb.coe_basis, hpbgen]`. Rewrite using `[h]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Conclude with `⟨1, one_ne_zero, θO ^ (k : ℕ), Submodule.subset_span ⟨k, rfl⟩, by simp [θO]⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, 0, Zd.zero_mem, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨N1, h1, z1, hz1, e1⟩` from `hx`. Take `⟨N2, h2, z2, hz2, e2⟩` from `hy`. Use `⟨N1 * N2, mul_ne_zero h1 h2, (N2 : ℤ) • z1 + (N1 : ℤ) • z2, Zd.add_mem (Zd.smul_mem _ hz1) (Zd.smul_mem _ hz2), ?_⟩` and prove the remaining obligations. Simplify using `only [Subring.coe_add, AddSubgroupClass.coe_zsmul, zsmul_eq_mul]`. Use `push_cast`.

Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul q x _ hx`. Take `⟨N, h, z, hz, e⟩` from `hx`. Use `⟨q.den * N, mul_ne_zero q.den_nz h, q.num • z, Zd.smul_mem _ hz, ?_⟩` and prove the remaining obligations.

Establish `hq : ((q.num : ℚ) : E) = (q.den : E) * (q : E)`. Rewrite using `[← Rat.den_mul_eq_num q]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [AddSubgroupClass.coe_zsmul, zsmul_eq_mul, Rat.smul_def]`.

Use `push_cast`. Rewrite using `[e]`. Establish `hq' : (q.num : E) = (q.den : E) * (q : E)` using `by exact_mod_cast hq`. Rewrite using `[hq']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdpos : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Choose the witnesses or unpack the hypotheses as in `⟨e0, he0⟩ : ∃ e0 : L, (e0 : E) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hbot : Submodule.span ℂ (Set.range P) = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `: x = 0` using `Subtype.ext (hcon x)`. Rewrite using `[this, map_zero]`.

Rewrite `hbot` using `[hspan]`. Establish `h0 : Module.finrank ℂ W = 0`. Rewrite using `[← finrank_top ℂ W, hbot, finrank_bot]`. Use linear arithmetic over natural numbers and integers. Use `set w0 : W := P e0 with hw0`.

Use `set A : Module.End ℂ W := T θO with hAdef`. Set `v : Fin pb.dim → W` to `fun k => (A ^ (k : ℕ)) w0`. Establish `hψ : ∀ z : O, TR z w0 = P (mulL z e0)` using `fun z => hT' z e0`. Establish `hZ : ∀ z ∈ Zd, TR z w0 ∈ Submodule.span ℂ (Set.range v)`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Rewrite using `[map_pow]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`.

Consider the case `zero => rw [map_zero, LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul m x _ hx`.

Rewrite using `[map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `hSd : Submodule.span ℂ (Set.range v) = ⊤`. Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Take `⟨N, hN, z, hz, hzE⟩` from `hA ((x : E) / e0)`. Establish `hmul : mulL z e0 = N • x`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (z : E) * e0 = _`. Rewrite using `[AddSubgroup.coe_nsmul, nsmul_eq_mul, hzE, _root_.mul_assoc, div_mul_cancel₀ _ he0]`.

Establish `h1 : (N : ℂ) • P x ∈ Submodule.span ℂ (Set.range v)`. Rewrite using `[Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hmul, ← hψ]`. Conclude with `hZ z hz`. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN`. Establish `h2` using `Submodule.smul_mem _ (N : ℂ)⁻¹ h1`.

Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hNc, one_smul]`. Then use the resulting hypothesis. Establish `hcard : Fintype.card (Fin pb.dim) = Module.finrank ℂ W`. Rewrite using `[Fintype.card_fin, hdim, hpbdim]`. Establish `hli : LinearIndependent ℂ v` using `linearIndependent_of_top_le_span_of_card_eq_finrank hSd.ge hcard`. Use `set f := minpoly ℚ θ with hf`.

Use `set fC : Polynomial ℂ := f.map (algebraMap ℚ ℂ) with hfC`. Establish `hfA : Polynomial.aeval A fC = 0`. Take `⟨b, hb⟩` from `IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) f`. Use `set g := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f with hg`. Establish `hb0 : ((b : ℤ) : ℂ) ≠ 0` using `by exact_mod_cast nonZeroDivisors.ne_zero b.2`.

Establish `hgθ : Polynomial.aeval θO g = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : ((Polynomial.aeval θO g : O) : E) = Polynomial.aeval θ g` using `(Polynomial.aeval_algHom_apply (O.subtype : O →+* E).toIntAlgHom θO g).symm`. Rewrite using `[h1, ← Polynomial.aeval_map_algebraMap ℚ, hb, map_zsmul, minpoly.aeval, smul_zero]`. Both sides reduce to the same expression.

Establish `h2 : Polynomial.aeval A g = 0`. Use `Polynomial.aeval_algHom_apply TR.toIntAlgHom θO g` as an intermediate fact. Rewrite `this` using `[hgθ, map_zero]`. Conclude with `this`. Establish `h3 : g.map (algebraMap ℤ ℂ) = (b : ℤ) • fC`.

Rewrite using `[IsScalarTower.algebraMap_eq ℤ ℚ ℂ, ← Polynomial.map_map, hb, zsmul_eq_mul, zsmul_eq_mul, Polynomial.map_mul, Polynomial.map_intCast]`. Establish `h4 : Polynomial.aeval A (g.map (algebraMap ℤ ℂ)) = 0`. Rewrite using `[Polynomial.aeval_map_algebraMap]`. Conclude with `h2`. Rewrite `h4` using `[h3, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]`.

Conclude with `(smul_eq_zero.mp h4).resolve_left hb0`. Use `set r : ℂ := τ θ with hr`. Establish `hroot : fC.IsRoot r`. Rewrite using `[Polynomial.IsRoot, hfC, Polynomial.eval_map_algebraMap, show r = τ.toRatAlgHom θ from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hsep : fC.Separable` using `Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ θ)`.

Use `set f₁ := fC /ₘ (Polynomial.X - Polynomial.C r) with hf₁`. Establish `hfac : (Polynomial.X - Polynomial.C r) * f₁ = fC` using `Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot`. Establish `hf1r : f₁.eval r ≠ 0`. Establish `h` using `hsep.aeval_derivative_ne_zero (x := r) (by rw [Polynomial.coe_aeval_eq_eval]; exact hroot)`. Rewrite `h` using `[Polynomial.coe_aeval_eq_eval, ← hfac, Polynomial.derivative_mul]`.

Simplify using `using h`. Establish `hfC0 : fC ≠ 0` using `(Polynomial.Monic.map _ (minpoly.monic hint)).ne_zero`. Establish `hf1ne : f₁ ≠ 0`. Introduce and unpack `h0`. Rewrite `hfac` using `[h0, mul_zero]`.

Conclude with `hfC0 hfac.symm`. Establish `hdegC : fC.natDegree = pb.dim`. Rewrite using `[hfC, Polynomial.natDegree_map, hf, ← hpbgen, PowerBasis.natDegree_minpoly]`. Establish `hdeg1 : f₁.natDegree + 1 = pb.dim`. Rewrite using `[← hdegC, ← hfac, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hf1ne, Polynomial.natDegree_X_sub_C, add_comm]`.

Use `set S : Module.End ℂ W := Polynomial.aeval A f₁ with hSdef`. Establish `hS : ∀ w, A (S w) = r • S w`. Introduce `w`. Establish `h : (Polynomial.aeval A fC) w = 0` using `by rw [hfA]; rfl`. Rewrite `h` using `[← hfac, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply]`.

Conclude with `h`. Establish `hpow : ∀ (u : W) (c : ℂ), A u = c • u → ∀ k : ℕ, (A ^ k) u = c ^ k • u`. Introduce `u c hu k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hu, smul_smul, pow_succ]`. Establish `hne : S w0 ≠ 0`. Introduce `h0`. Establish `hlt : f₁.natDegree < pb.dim` using `by omega`. Establish `hsum : ∑ k : Fin pb.dim, f₁.coeff k • v k = 0`.

Rewrite using `[← h0, hSdef, Polynomial.aeval_eq_sum_range' hlt, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply]`. Conclude with `Fin.sum_univ_eq_sum_range (fun i => f₁.coeff i • (A ^ i) w0) pb.dim`. Establish `h` using `(Fintype.linearIndependent_iff.mp hli) _ hsum ⟨f₁.natDegree, hlt⟩`. Conclude with `hf1ne (Polynomial.leadingCoeff_eq_zero.mp h)`.

Establish `hcomm : Commute S A`. Use `(Commute.all f₁ Polynomial.X).map (Polynomial.aeval A)` as an intermediate fact. Rewrite `this` using `[Polynomial.aeval_X]`. Then use the resulting hypothesis. Establish `hSall : ∀ w, S w ∈ Submodule.span ℂ {S w0}`. Establish `hle : Submodule.span ℂ (Set.range v) ≤ (Submodule.span ℂ {S w0}).comap S`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Use `show S ((A ^ (k : ℕ)) w0) ∈ _`. Rewrite using `[← Module.End.mul_apply, (hcomm.pow_right _).eq, Module.End.mul_apply, hpow _ r (hS w0)]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Introduce `w`. Conclude with `hle (hSd ▸ Submodule.mem_top)`. Establish `hle : Module.End.eigenspace A r ≤ Submodule.span ℂ {S w0}`. Introduce `u hu`.

Rewrite `hu` using `[Module.End.mem_eigenspace_iff]`. Establish `hSu : S u = f₁.eval r • u`. Distinguish the cases in `hu0 : u = 0`. Simplify using `[hu0]`. Conclude with `Module.End.aeval_apply_of_hasEigenvector (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hu, hu0⟩)`.

Establish `h2` using `Submodule.smul_mem _ (f₁.eval r)⁻¹ (hSall u)`. Rewrite `h2` using `[hSu, smul_smul, inv_mul_cancel₀ hf1r, one_smul]`. Then use the resulting hypothesis. Establish `heq : Module.End.eigenspace A r = Submodule.span ℂ {S w0}` using `le_antisymm hle ((Submodule.span_singleton_le_iff_mem _ _).mpr (Module.End.mem_eigenspace_iff.mpr (hS w0)))`. Establish `hcommon : (⨅ a : O, Module.End.eigenspace (T a) (τ a)) = Module.End.eigenspace A r`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `iInf_le (fun a : O => Module.End.eigenspace (T a) (τ a)) θO`. Introduce `u hu`. Rewrite `hu` using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[Submodule.mem_iInf]`. Introduce `a`.

Rewrite using `[Module.End.mem_eigenspace_iff]`. Establish `hZu : ∀ z ∈ Zd, TR z u = τ z • u`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨k, rfl⟩` from `hx`. Rewrite using `[map_pow]`. Use `show (A ^ (k : ℕ)) u = _`. Rewrite using `[hpow u r hu]`. Simplify using `[θO, r]`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, LinearMap.add_apply, hx, hy, Subring.coe_add, map_add, add_smul]`. Consider the case `smul m x _ hx`. Rewrite using `[map_zsmul, LinearMap.smul_apply, hx, AddSubgroupClass.coe_zsmul, map_zsmul, smul_assoc]`.

Take `⟨N, hN, z, hz, hzE⟩` from `hA a`. Establish `hza : z = N • a` using `Subtype.ext (by rw [hzE, AddSubmonoidClass.coe_nsmul, nsmul_eq_mul])`. Establish `h1` using `hZu z hz`. Rewrite `h1` using `[hza, map_nsmul, LinearMap.smul_apply, AddSubmonoidClass.coe_nsmul, map_nsmul, smul_assoc, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ N (τ a • u)]`. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN`.

Conclude with `smul_right_injective W hNc h1`. Rewrite using `[hcommon, heq, finrank_span_singleton hne]`.
-/
theorem finrank_common_eigenspace_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] (O : Subring E), (∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ O) →
    ∀ (L : AddSubgroup E), (∀ a ∈ O, ∀ x ∈ L, a * x ∈ L) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (P : L →+ W), Submodule.span ℂ (Set.range P) = ⊤ →
      Module.finrank ℂ W = Module.finrank ℚ E →
    ∀ (T : O → Module.End ℂ W), (∀ (a : O) (x y : L), (y : E) = a * x → T a (P x) = P y) →
    ∀ τ : E →+* ℂ, Module.finrank ℂ (⨅ a : O, Module.End.eigenspace (T a) (τ a) : Submodule ℂ W) = 1 := by
  intro E _ _ O hO L hL W _ _ P hspan hdim T hT τ
  have hext : ∀ f g : Module.End ℂ W, (∀ x : L, f (P x) = g (P x)) → f = g := fun f g h =>
    LinearMap.ext_on_range hspan h
  let mulL : O → L → L := fun a x => ⟨(a : E) * x, hL a a.2 x x.2⟩
  have hT' : ∀ (a : O) (x : L), T a (P x) = P (mulL a x) := fun a x => hT a x _ rfl
  let TR : O →+* Module.End ℂ W :=
    { toFun := T
      map_one' := hext _ _ fun x => by
        rw [hT', Module.End.one_apply]; congr 1; ext; simp [mulL]
      map_mul' := fun a b => hext _ _ fun x => by
        rw [Module.End.mul_apply, hT', hT', hT']; congr 1; ext; simp [mulL]; ring
      map_zero' := hext _ _ fun x => by
        rw [hT', LinearMap.zero_apply]; convert P.map_zero; ext; simp [mulL]
      map_add' := fun a b => hext _ _ fun x => by
        rw [LinearMap.add_apply, hT', hT', hT', ← map_add]; congr 1; ext; simp [mulL, add_mul] }

  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨n, hn0, hnO⟩ := hO α
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn0
  set θ : E := (n : E) * α with hθdef
  let θO : O := ⟨θ, hnO⟩
  have hint : IsIntegral ℚ θ := Algebra.IsIntegral.isIntegral θ
  have hθtop : IntermediateField.adjoin ℚ {θ} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have : α = θ / (n : E) := by rw [hθdef]; field_simp
    rw [this]
    exact div_mem (IntermediateField.mem_adjoin_simple_self ℚ θ) (natCast_mem _ n)
  have hadj : Algebra.adjoin ℚ {θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθtop,
      IntermediateField.top_toSubalgebra]
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hpbdim : pb.dim = Module.finrank ℚ E := pb.finrank.symm
  have hpbgen : pb.gen = θ := rfl

  let Zd : Submodule ℤ O := Submodule.span ℤ (Set.range fun k : Fin pb.dim => θO ^ (k : ℕ))
  have hA : ∀ y : E, ∃ N : ℕ, N ≠ 0 ∧ ∃ z ∈ Zd, (z : E) = N * y := by
    intro y
    have hy : y ∈ Submodule.span ℚ (Set.range fun k : Fin pb.dim => θ ^ (k : ℕ)) := by
      have h := pb.basis.span_eq
      rw [pb.coe_basis, hpbgen] at h
      rw [h]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨1, one_ne_zero, θO ^ (k : ℕ), Submodule.subset_span ⟨k, rfl⟩, by simp [θO]⟩
    | zero => exact ⟨1, one_ne_zero, 0, Zd.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1, z1, hz1, e1⟩ := hx
      obtain ⟨N2, h2, z2, hz2, e2⟩ := hy
      refine ⟨N1 * N2, mul_ne_zero h1 h2, (N2 : ℤ) • z1 + (N1 : ℤ) • z2,
        Zd.add_mem (Zd.smul_mem _ hz1) (Zd.smul_mem _ hz2), ?_⟩
      simp only [Subring.coe_add, AddSubgroupClass.coe_zsmul, zsmul_eq_mul]
      push_cast
      rw [e1, e2]; ring
    | smul q x _ hx =>
      obtain ⟨N, h, z, hz, e⟩ := hx
      refine ⟨q.den * N, mul_ne_zero q.den_nz h, q.num • z, Zd.smul_mem _ hz, ?_⟩
      have hq : ((q.num : ℚ) : E) = (q.den : E) * (q : E) := by
        rw [← Rat.den_mul_eq_num q]; push_cast; ring
      simp only [AddSubgroupClass.coe_zsmul, zsmul_eq_mul, Rat.smul_def]
      push_cast
      rw [e]
      have hq' : (q.num : E) = (q.den : E) * (q : E) := by exact_mod_cast hq
      rw [hq']; push_cast; ring

  have hdpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  obtain ⟨e0, he0⟩ : ∃ e0 : L, (e0 : E) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : Submodule.span ℂ (Set.range P) = ⊥ := by
      rw [Submodule.span_eq_bot]; rintro _ ⟨x, rfl⟩
      have : x = 0 := Subtype.ext (hcon x)
      rw [this, map_zero]
    rw [hspan] at hbot
    have h0 : Module.finrank ℂ W = 0 := by
      rw [← finrank_top ℂ W, hbot, finrank_bot]
    omega
  set w0 : W := P e0 with hw0
  set A : Module.End ℂ W := T θO with hAdef
  let v : Fin pb.dim → W := fun k => (A ^ (k : ℕ)) w0
  have hψ : ∀ z : O, TR z w0 = P (mulL z e0) := fun z => hT' z e0
  have hZ : ∀ z ∈ Zd, TR z w0 ∈ Submodule.span ℂ (Set.range v) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [map_pow]; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
    | smul m x _ hx =>
      rw [map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ]
      exact Submodule.smul_mem _ _ hx
  have hSd : Submodule.span ℂ (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨N, hN, z, hz, hzE⟩ := hA ((x : E) / e0)
    have hmul : mulL z e0 = N • x := by
      apply Subtype.ext
      show (z : E) * e0 = _
      rw [AddSubgroup.coe_nsmul, nsmul_eq_mul, hzE, _root_.mul_assoc, div_mul_cancel₀ _ he0]
    have h1 : (N : ℂ) • P x ∈ Submodule.span ℂ (Set.range v) := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hmul, ← hψ]; exact hZ z hz
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    have h2 := Submodule.smul_mem _ (N : ℂ)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hNc, one_smul] at h2
  have hcard : Fintype.card (Fin pb.dim) = Module.finrank ℂ W := by
    rw [Fintype.card_fin, hdim, hpbdim]
  have hli : LinearIndependent ℂ v := linearIndependent_of_top_le_span_of_card_eq_finrank hSd.ge hcard

  set f := minpoly ℚ θ with hf
  set fC : Polynomial ℂ := f.map (algebraMap ℚ ℂ) with hfC
  have hfA : Polynomial.aeval A fC = 0 := by
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) f
    set g := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f with hg
    have hb0 : ((b : ℤ) : ℂ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero b.2
    have hgθ : Polynomial.aeval θO g = 0 := by
      apply Subtype.ext
      have h1 : ((Polynomial.aeval θO g : O) : E) = Polynomial.aeval θ g :=
        (Polynomial.aeval_algHom_apply (O.subtype : O →+* E).toIntAlgHom θO g).symm
      rw [h1, ← Polynomial.aeval_map_algebraMap ℚ, hb, map_zsmul, minpoly.aeval, smul_zero]
      rfl
    have h2 : Polynomial.aeval A g = 0 := by
      have := Polynomial.aeval_algHom_apply TR.toIntAlgHom θO g
      rw [hgθ, map_zero] at this
      exact this
    have h3 : g.map (algebraMap ℤ ℂ) = (b : ℤ) • fC := by
      rw [IsScalarTower.algebraMap_eq ℤ ℚ ℂ, ← Polynomial.map_map, hb, zsmul_eq_mul, zsmul_eq_mul,
        Polynomial.map_mul, Polynomial.map_intCast]
    have h4 : Polynomial.aeval A (g.map (algebraMap ℤ ℂ)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]; exact h2
    rw [h3, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ] at h4
    exact (smul_eq_zero.mp h4).resolve_left hb0

  set r : ℂ := τ θ with hr
  have hroot : fC.IsRoot r := by
    rw [Polynomial.IsRoot, hfC, Polynomial.eval_map_algebraMap, show r = τ.toRatAlgHom θ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hsep : fC.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ θ)
  set f₁ := fC /ₘ (Polynomial.X - Polynomial.C r) with hf₁
  have hfac : (Polynomial.X - Polynomial.C r) * f₁ = fC :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hf1r : f₁.eval r ≠ 0 := by
    have h := hsep.aeval_derivative_ne_zero (x := r) (by rw [Polynomial.coe_aeval_eq_eval]; exact hroot)
    rw [Polynomial.coe_aeval_eq_eval, ← hfac, Polynomial.derivative_mul] at h
    simpa using h
  have hfC0 : fC ≠ 0 := (Polynomial.Monic.map _ (minpoly.monic hint)).ne_zero
  have hf1ne : f₁ ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hfac; exact hfC0 hfac.symm
  have hdegC : fC.natDegree = pb.dim := by
    rw [hfC, Polynomial.natDegree_map, hf, ← hpbgen, PowerBasis.natDegree_minpoly]
  have hdeg1 : f₁.natDegree + 1 = pb.dim := by
    rw [← hdegC, ← hfac, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hf1ne,
      Polynomial.natDegree_X_sub_C, add_comm]
  set S : Module.End ℂ W := Polynomial.aeval A f₁ with hSdef
  have hS : ∀ w, A (S w) = r • S w := by
    intro w
    have h : (Polynomial.aeval A fC) w = 0 := by rw [hfA]; rfl
    rw [← hfac, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h
    exact h
  have hpow : ∀ (u : W) (c : ℂ), A u = c • u → ∀ k : ℕ, (A ^ k) u = c ^ k • u := by
    intro u c hu k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hu, smul_smul, pow_succ]
  have hne : S w0 ≠ 0 := by
    intro h0
    have hlt : f₁.natDegree < pb.dim := by omega
    have hsum : ∑ k : Fin pb.dim, f₁.coeff k • v k = 0 := by
      rw [← h0, hSdef, Polynomial.aeval_eq_sum_range' hlt, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
      exact Fin.sum_univ_eq_sum_range (fun i => f₁.coeff i • (A ^ i) w0) pb.dim
    have h := (Fintype.linearIndependent_iff.mp hli) _ hsum ⟨f₁.natDegree, hlt⟩
    exact hf1ne (Polynomial.leadingCoeff_eq_zero.mp h)
  have hcomm : Commute S A := by
    have := (Commute.all f₁ Polynomial.X).map (Polynomial.aeval A)
    rwa [Polynomial.aeval_X] at this
  have hSall : ∀ w, S w ∈ Submodule.span ℂ {S w0} := by
    have hle : Submodule.span ℂ (Set.range v) ≤ (Submodule.span ℂ {S w0}).comap S := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show S ((A ^ (k : ℕ)) w0) ∈ _
      rw [← Module.End.mul_apply, (hcomm.pow_right _).eq, Module.End.mul_apply, hpow _ r (hS w0)]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    intro w
    exact hle (hSd ▸ Submodule.mem_top)
  have hle : Module.End.eigenspace A r ≤ Submodule.span ℂ {S w0} := by
    intro u hu
    rw [Module.End.mem_eigenspace_iff] at hu
    have hSu : S u = f₁.eval r • u := by
      by_cases hu0 : u = 0
      · simp [hu0]
      · exact Module.End.aeval_apply_of_hasEigenvector
          (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hu, hu0⟩)
    have h2 := Submodule.smul_mem _ (f₁.eval r)⁻¹ (hSall u)
    rwa [hSu, smul_smul, inv_mul_cancel₀ hf1r, one_smul] at h2
  have heq : Module.End.eigenspace A r = Submodule.span ℂ {S w0} :=
    le_antisymm hle ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (Module.End.mem_eigenspace_iff.mpr (hS w0)))

  have hcommon : (⨅ a : O, Module.End.eigenspace (T a) (τ a)) = Module.End.eigenspace A r := by
    apply le_antisymm
    · exact iInf_le (fun a : O => Module.End.eigenspace (T a) (τ a)) θO
    · intro u hu
      rw [Module.End.mem_eigenspace_iff] at hu
      rw [Submodule.mem_iInf]; intro a
      rw [Module.End.mem_eigenspace_iff]
      have hZu : ∀ z ∈ Zd, TR z u = τ z • u := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          rw [map_pow]
          show (A ^ (k : ℕ)) u = _
          rw [hpow u r hu]
          simp [θO, r]
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply, hx, hy, Subring.coe_add, map_add, add_smul]
        | smul m x _ hx =>
          rw [map_zsmul, LinearMap.smul_apply, hx, AddSubgroupClass.coe_zsmul, map_zsmul, smul_assoc]
      obtain ⟨N, hN, z, hz, hzE⟩ := hA a
      have hza : z = N • a := Subtype.ext (by rw [hzE, AddSubmonoidClass.coe_nsmul, nsmul_eq_mul])
      have h1 := hZu z hz
      rw [hza, map_nsmul, LinearMap.smul_apply, AddSubmonoidClass.coe_nsmul, map_nsmul, smul_assoc,
        ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ N (τ a • u)] at h1
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
      exact smul_right_injective W hNc h1
  rw [hcommon, heq, finrank_span_singleton hne]

end GlobalTheory.EigLine
