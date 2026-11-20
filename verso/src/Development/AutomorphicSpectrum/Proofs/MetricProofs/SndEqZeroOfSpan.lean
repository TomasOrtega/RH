import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgHomAdjoinInv
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan

open TrivSqZeroExt

def dualPt {σ : Type} (t v : σ → ℂ) : σ → TrivSqZeroExt ℂ ℂ := fun q => inl (t q) + inr (v q)

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on with`. Consider the case `C a => simp [algebraMap_eq_inl]`. Consider the case `add p q hp hq`. Use `⟨by simp [hp.1, hq.1], ?_⟩` and prove the remaining obligations. Simplify using `[hp.2, hq.2, mul_add, Finset.sum_add_distrib]`.

Consider the case `mul_X p q hp`. Use `⟨by simp [hp.1, dualPt], ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, aeval_X, snd_mul, hp.1, hp.2, dualPt, fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr, Derivation.leibniz, pderiv_X, eval_mul, eval_X, smul_eq_mul, op_smul_eq_mul, add_zero, zero_add, map_add]`. Simplify using `[Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]`.
-/
theorem aeval_dualPt {σ : Type} [Fintype σ] (t v : σ → ℂ) (G : MvPolynomial σ ℂ) :
    fst (aeval (dualPt t v) G) = eval t G ∧
      snd (aeval (dualPt t v) G) = ∑ q, v q * eval t (pderiv q G) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq_inl]
  | add p q hp hq =>
    refine ⟨by simp [hp.1, hq.1], ?_⟩
    simp [hp.2, hq.2, mul_add, Finset.sum_add_distrib]
  | mul_X p q hp =>
    refine ⟨by simp [hp.1, dualPt], ?_⟩
    simp only [map_mul, aeval_X, snd_mul, hp.1, hp.2, dualPt, fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
      Derivation.leibniz, pderiv_X, eval_mul, eval_X, smul_eq_mul, op_smul_eq_mul, add_zero, zero_add, map_add]
    simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

/- English proof (translation)
Set `f : S →+* ℂ` to `(TrivSqZeroExt.fstHom ℚ ℂ ℂ).toRingHom.comp φ.toRingHom`. Use `letI : Module S ℂ := Module.compHom ℂ f`. Use `haveI : IsScalarTower ℚ S ℂ := ⟨fun q a m => by show f (q • a) * m = q • (f a * m)`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def, mul_assoc]`. Use `congr 1`.

Conclude with `(eq_ratCast (f.comp (algebraMap ℚ S)) q).trans (eq_ratCast (algebraMap ℚ ℂ) q).symm⟩`. Set `d : Derivation ℚ S ℂ` to `{ toFun := fun a => snd (φ a) map_add' := fun a b => by simp map_smul' := fun q a => by simp map_one_eq_zero' := by simp leibniz' := fun a b => by show snd (φ (a * b)) = (φ a).fst * snd (φ b) + (φ b).fst * snd (φ a)`. Rewrite using `[map_mul, snd_mul, smul_eq_mul, op_smul_eq_mul]`. Use `ring }`. Establish `key : d.liftKaehlerDifferential = 0`.

Use `LinearMap.ext_on_range hspan fun i => ?_` and prove the remaining obligations. Rewrite using `[Derivation.liftKaehlerDifferential_comp_D]`. Conclude with `h i`. Establish `h2` using `congrArg (fun L => L (KaehlerDifferential.D ℚ S s)) key`. Simplify `h2` using `[Derivation.liftKaehlerDifferential_comp_D, d]`.
-/
theorem snd_eq_zero_of_span {S : Type} [CommRing S] [Algebra ℚ S]
    (φ : S →ₐ[ℚ] TrivSqZeroExt ℂ ℂ) {e : ℕ} (z : Fin e → S)
    (hspan : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤)
    (h : ∀ i, snd (φ (z i)) = 0) (s : S) : snd (φ s) = 0 := by
  let f : S →+* ℂ := (TrivSqZeroExt.fstHom ℚ ℂ ℂ).toRingHom.comp φ.toRingHom
  letI : Module S ℂ := Module.compHom ℂ f
  haveI : IsScalarTower ℚ S ℂ := ⟨fun q a m => by
    show f (q • a) * m = q • (f a * m)
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, mul_assoc]
    congr 1
    exact (eq_ratCast (f.comp (algebraMap ℚ S)) q).trans (eq_ratCast (algebraMap ℚ ℂ) q).symm⟩
  let d : Derivation ℚ S ℂ :=
    { toFun := fun a => snd (φ a)
      map_add' := fun a b => by simp
      map_smul' := fun q a => by simp
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        show snd (φ (a * b)) = (φ a).fst * snd (φ b) + (φ b).fst * snd (φ a)
        rw [map_mul, snd_mul, smul_eq_mul, op_smul_eq_mul]
        ring }
  have key : d.liftKaehlerDifferential = 0 := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    rw [Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  have h2 := congrArg (fun L => L (KaehlerDifferential.D ℚ S s)) key
  simpa [Derivation.liftKaehlerDifferential_comp_D, d] using h2

/- English proof (translation)
Introduce `Ω _ _ σ _ τ F S e z Z N t v c hF0 hS hspan hz hker0 hFt hker1 hZc hZd`. Establish `hψ : ∀ G : MvPolynomial σ ℚ, (aeval (dualPt t v) G : TrivSqZeroExt ℂ ℂ) = aeval (dualPt t v) (map (algebraMap ℚ ℂ) G)` using `fun G => (aeval_map_algebraMap ℂ (dualPt t v) G).symm`. Establish `hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → (aeval (dualPt t v) G : TrivSqZeroExt ℂ ℂ) = 0`. Introduce `G hG`. Establish `h1` using `aeval_dualPt t v (map (algebraMap ℚ ℂ) G)`.

Rewrite using `[hψ]`. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[h1.1, hker0 G hG]`. Simplify using the standard rewrite rules. Rewrite using `[h1.2, hker1 G hG]`.

Simplify using the standard rewrite rules. Establish `memInv : (aeval τ F)⁻¹ ∈ S` using `hS ▸ Algebra.subset_adjoin (Set.mem_insert _ _)`. Establish `memτ : ∀ q, τ q ∈ S` using `fun q => hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)`. Establish `hRS : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range ≤ S`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval ℚ τ, hS]`.

Conclude with `Algebra.adjoin_mono (Set.subset_insert _ _)`. Establish `hsurjS : ∀ s ∈ S, ∃ r ∈ (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range, ∃ n : ℕ, s = r * (aeval τ F)⁻¹ ^ n`. Rewrite using `[hS]`. Introduce `s hs`. Proceed by induction on `hs using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Break down `hy with rfl | ⟨q, rfl⟩` into its components or cases. Conclude with `⟨1, Subalgebra.one_mem _, 1, by ring⟩`. Conclude with `⟨τ q, ⟨X q, aeval_X τ q⟩, 0, by ring⟩`. Consider the case `algebraMap r => exact ⟨algebraMap ℚ Ω r, Subalgebra.algebraMap_mem _ r, 0, by ring⟩`.

Consider the case `add y y' _ _ hy hy'`. Take `⟨r, hr, n, rfl⟩` from `hy`. Take `⟨r', hr', n', rfl⟩` from `hy'`. Use `⟨r * aeval τ F ^ n' + r' * aeval τ F ^ n, Subalgebra.add_mem _ (Subalgebra.mul_mem _ hr (Subalgebra.pow_mem _ (AlgHom.mem_range_self _ F) _)) (Subalgebra.mul_mem _ hr' (Subalgebra.pow_mem _ (AlgHom.mem_range_self _ F) _)), n + n', ?_⟩` and prove the remaining obligations. Rewrite using `[inv_pow, inv_pow, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul y y' _ _ hy hy'`. Take `⟨r, hr, n, rfl⟩` from `hy`. Take `⟨r', hr', n', rfl⟩` from `hy'`.

Conclude with `⟨r * r', Subalgebra.mul_mem _ hr hr', n + n', by rw [pow_add]; ring⟩`. Use `letI : Algebra (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range S := (Subalgebra.inclusion hRS).toRingHom.toAlgebra`. Set `xR : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range` to `⟨aeval τ F, AlgHom.mem_range_self _ F⟩`. Establish `hxS : IsUnit (algebraMap _ S xR)` using `isUnit_iff_exists_inv.2 ⟨⟨(aeval τ F)⁻¹, memInv⟩, Subtype.ext (by show aeval τ F * (aeval τ F)⁻¹ = 1`. Conclude with `mul_inv_cancel₀ hF0)⟩`.

Use `haveI : IsLocalization.Away xR S := by`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, n, rfl⟩`. Rewrite using `[map_pow]`. Conclude with `hxS.pow n`.

Introduce `s`. Take `⟨r, hr, n, hs⟩` from `hsurjS s s.2`. Use `⟨(⟨r, hr⟩, ⟨xR ^ n, n, rfl⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (s : Ω) * ((xR ^ n : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) : Ω) = r`. Rewrite using `[SubmonoidClass.coe_pow, hs]`.

Use `show r * (aeval τ F)⁻¹ ^ n * aeval τ F ^ n = r`. Rewrite using `[mul_assoc, ← mul_pow, inv_mul_cancel₀ hF0, one_pow, mul_one]`. Introduce `a b h`. Establish `h' : ((algebraMap _ S a : S) : Ω) = ((algebraMap _ S b : S) : Ω)` using `congrArg (fun s : S => (s : Ω)) h`. Conclude with `⟨1, congrArg _ (Subtype.ext h')⟩`.

Establish `hsurjR : Function.Surjective ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict : MvPolynomial σ ℚ →+* (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range)`. Introduce and unpack `⟨y, G, rfl⟩`. Conclude with `⟨G, rfl⟩`. Set `ψR : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range →+* TrivSqZeroExt ℂ ℂ` to `RingHom.liftOfSurjective _ hsurjR ⟨(aeval (dualPt t v) : MvPolynomial σ ℚ →ₐ[ℚ] TrivSqZeroExt ℂ ℂ).toRingHom, fun G hG => by`. Rewrite `hG`, the goal using `[RingHom.mem_ker]`.

Conclude with `hker G (congrArg Subtype.val hG)⟩`. Establish `hψR : ∀ G : MvPolynomial σ ℚ, ψR ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict G) = aeval (dualPt t v) G` using `fun G => RingHom.liftOfSurjective_comp_apply _ hsurjR _ G`. Establish `hxR : xR = (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict F` using `rfl`. Establish `hFt' : IsUnit (aeval (dualPt t v) F : TrivSqZeroExt ℂ ℂ)`. Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ, (aeval_dualPt t v _).1]`.

Conclude with `isUnit_iff_ne_zero.2 hFt`. Establish `hu : IsUnit (ψR xR)` using `by rw [hxR, hψR]; exact hFt'`. Set `φS : S →+* TrivSqZeroExt ℂ ℂ` to `IsLocalization.Away.lift xR hu`. Establish `hφS : ∀ G : MvPolynomial σ ℚ, φS (algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict G)) = aeval (dualPt t v) G` using `fun G => by`. Rewrite using `[IsLocalization.Away.lift_eq, hψR]`.

Establish `hZ : ∀ i, (aeval (dualPt t v) (Z i) : TrivSqZeroExt ℂ ℂ) = inl (c i) * aeval (dualPt t v) F ^ N i`. Introduce `i`. Establish `h0 : (aeval (dualPt t v) (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i) : TrivSqZeroExt ℂ ℂ) = 0`. Establish `h1` using `aeval_dualPt t v (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i)`. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[h1.1]`. Simplify using `[hZc i]`. Rewrite using `[h1.2, hZd i]`. Simplify using the standard rewrite rules. Rewrite `h0` using `[map_sub, map_mul, map_pow, aeval_C, algebraMap_eq_inl, ← hψ, ← hψ, sub_eq_zero]`.

Conclude with `h0`. Establish `hφz : ∀ i, snd (φS.toRatAlgHom (z i)) = 0`. Introduce `i`. Establish `e1 : z i * algebraMap _ S (xR ^ N i) = algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict (Z i))` using `Subtype.ext (by show (z i : Ω) * ((xR ^ N i : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) : Ω) = aeval τ (Z i)`. Rewrite using `[SubmonoidClass.coe_pow]`.

Conclude with `hz i)`. Establish `e2` using `congrArg φS e1`. Establish `hφx : φS (algebraMap _ S xR) = aeval (dualPt t v) F` using `by rw [hxR]; exact hφS F`. Rewrite `e2` using `[map_mul, map_pow, map_pow, hφx, hφS, hZ]`. Establish `e3 : φS (z i) = inl (c i)` using `(hFt'.pow (N i)).mul_left_inj.1 e2`.

Use `show snd (φS (z i)) = 0`. Rewrite using `[e3, snd_inl]`. Use function extensionality and compare the values at `q`. Establish `h` using `snd_eq_zero_of_span φS.toRatAlgHom z hspan hφz ⟨τ q, memτ q⟩`. Establish `hq : (⟨τ q, memτ q⟩ : S) = algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict (X q))` using `Subtype.ext (aeval_X τ q).symm`.

Express the relevant statement in the definitionally equal form `snd (φS ⟨τ q, memτ q⟩) = 0 at h`. Rewrite `h` using `[hq, hφS, aeval_X]`. Simplify `h` using `[dualPt]`.
-/
theorem tangent_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) [Fintype σ] (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (e : ℕ) (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ) (t v : σ → ℂ) (c : Fin e → ℂ), aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) → Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ → (∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i)) → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → eval t (map (algebraMap ℚ ℂ) F) ≠ 0 → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → ∑ q, v q * eval t (pderiv q (map (algebraMap ℚ ℂ) G)) = 0) → (∀ i, eval t (map (algebraMap ℚ ℂ) (Z i)) = c i * eval t (map (algebraMap ℚ ℂ) F) ^ N i) → (∀ i, ∑ q, v q * eval t (pderiv q (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i)) = 0) → v = 0 := by
  intro Ω _ _ σ _ τ F S e z Z N t v c hF0 hS hspan hz hker0 hFt hker1 hZc hZd
  have hψ : ∀ G : MvPolynomial σ ℚ, (aeval (dualPt t v) G : TrivSqZeroExt ℂ ℂ) =
      aeval (dualPt t v) (map (algebraMap ℚ ℂ) G) := fun G =>
    (aeval_map_algebraMap ℂ (dualPt t v) G).symm
  have hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → (aeval (dualPt t v) G : TrivSqZeroExt ℂ ℂ) = 0 := by
    intro G hG
    have h1 := aeval_dualPt t v (map (algebraMap ℚ ℂ) G)
    rw [hψ]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [h1.1, hker0 G hG]; simp
    · rw [h1.2, hker1 G hG]; simp
  have memInv : (aeval τ F)⁻¹ ∈ S := hS ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  have memτ : ∀ q, τ q ∈ S := fun q => hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  have hRS : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range ≤ S := by
    rw [← Algebra.adjoin_range_eq_range_aeval ℚ τ, hS]
    exact Algebra.adjoin_mono (Set.subset_insert _ _)
  have hsurjS : ∀ s ∈ S, ∃ r ∈ (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range, ∃ n : ℕ, s = r * (aeval τ F)⁻¹ ^ n := by
    rw [hS]
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with rfl | ⟨q, rfl⟩
      · exact ⟨1, Subalgebra.one_mem _, 1, by ring⟩
      · exact ⟨τ q, ⟨X q, aeval_X τ q⟩, 0, by ring⟩
    | algebraMap r => exact ⟨algebraMap ℚ Ω r, Subalgebra.algebraMap_mem _ r, 0, by ring⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨r, hr, n, rfl⟩ := hy
      obtain ⟨r', hr', n', rfl⟩ := hy'
      refine ⟨r * aeval τ F ^ n' + r' * aeval τ F ^ n, Subalgebra.add_mem _ (Subalgebra.mul_mem _ hr
        (Subalgebra.pow_mem _ (AlgHom.mem_range_self _ F) _)) (Subalgebra.mul_mem _ hr'
        (Subalgebra.pow_mem _ (AlgHom.mem_range_self _ F) _)), n + n', ?_⟩
      rw [inv_pow, inv_pow, inv_pow]
      field_simp
      ring
    | mul y y' _ _ hy hy' =>
      obtain ⟨r, hr, n, rfl⟩ := hy
      obtain ⟨r', hr', n', rfl⟩ := hy'
      exact ⟨r * r', Subalgebra.mul_mem _ hr hr', n + n', by rw [pow_add]; ring⟩
  letI : Algebra (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range S := (Subalgebra.inclusion hRS).toRingHom.toAlgebra
  let xR : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range := ⟨aeval τ F, AlgHom.mem_range_self _ F⟩
  have hxS : IsUnit (algebraMap _ S xR) :=
    isUnit_iff_exists_inv.2 ⟨⟨(aeval τ F)⁻¹, memInv⟩, Subtype.ext (by
      show aeval τ F * (aeval τ F)⁻¹ = 1
      exact mul_inv_cancel₀ hF0)⟩
  haveI : IsLocalization.Away xR S := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      rw [map_pow]
      exact hxS.pow n
    · intro s
      obtain ⟨r, hr, n, hs⟩ := hsurjS s s.2
      refine ⟨(⟨r, hr⟩, ⟨xR ^ n, n, rfl⟩), Subtype.ext ?_⟩
      show (s : Ω) * ((xR ^ n : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) : Ω) = r
      rw [SubmonoidClass.coe_pow, hs]
      show r * (aeval τ F)⁻¹ ^ n * aeval τ F ^ n = r
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hF0, one_pow, mul_one]
    · intro a b h
      have h' : ((algebraMap _ S a : S) : Ω) = ((algebraMap _ S b : S) : Ω) := congrArg (fun s : S => (s : Ω)) h
      exact ⟨1, congrArg _ (Subtype.ext h')⟩
  have hsurjR : Function.Surjective ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict :
      MvPolynomial σ ℚ →+* (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) := by
    rintro ⟨y, G, rfl⟩
    exact ⟨G, rfl⟩
  let ψR : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range →+* TrivSqZeroExt ℂ ℂ :=
    RingHom.liftOfSurjective _ hsurjR ⟨(aeval (dualPt t v) : MvPolynomial σ ℚ →ₐ[ℚ] TrivSqZeroExt ℂ ℂ).toRingHom,
      fun G hG => by
        rw [RingHom.mem_ker] at hG ⊢
        exact hker G (congrArg Subtype.val hG)⟩
  have hψR : ∀ G : MvPolynomial σ ℚ, ψR ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict G) =
      aeval (dualPt t v) G := fun G => RingHom.liftOfSurjective_comp_apply _ hsurjR _ G
  have hxR : xR = (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict F := rfl
  have hFt' : IsUnit (aeval (dualPt t v) F : TrivSqZeroExt ℂ ℂ) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ, (aeval_dualPt t v _).1]
    exact isUnit_iff_ne_zero.2 hFt
  have hu : IsUnit (ψR xR) := by rw [hxR, hψR]; exact hFt'
  let φS : S →+* TrivSqZeroExt ℂ ℂ := IsLocalization.Away.lift xR hu
  have hφS : ∀ G : MvPolynomial σ ℚ, φS (algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict G)) =
      aeval (dualPt t v) G := fun G => by
    rw [IsLocalization.Away.lift_eq, hψR]
  have hZ : ∀ i, (aeval (dualPt t v) (Z i) : TrivSqZeroExt ℂ ℂ) =
      inl (c i) * aeval (dualPt t v) F ^ N i := by
    intro i
    have h0 : (aeval (dualPt t v) (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i) :
        TrivSqZeroExt ℂ ℂ) = 0 := by
      have h1 := aeval_dualPt t v (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i)
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [h1.1]; simp [hZc i]
      · rw [h1.2, hZd i]; simp
    rw [map_sub, map_mul, map_pow, aeval_C, algebraMap_eq_inl, ← hψ, ← hψ, sub_eq_zero] at h0
    exact h0
  have hφz : ∀ i, snd (φS.toRatAlgHom (z i)) = 0 := by
    intro i
    have e1 : z i * algebraMap _ S (xR ^ N i) =
        algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict (Z i)) := Subtype.ext (by
      show (z i : Ω) * ((xR ^ N i : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) : Ω) = aeval τ (Z i)
      rw [SubmonoidClass.coe_pow]
      exact hz i)
    have e2 := congrArg φS e1
    have hφx : φS (algebraMap _ S xR) = aeval (dualPt t v) F := by rw [hxR]; exact hφS F
    rw [map_mul, map_pow, map_pow, hφx, hφS, hZ] at e2
    have e3 : φS (z i) = inl (c i) := (hFt'.pow (N i)).mul_left_inj.1 e2
    show snd (φS (z i)) = 0
    rw [e3, snd_inl]
  funext q
  have h := snd_eq_zero_of_span φS.toRatAlgHom z hspan hφz ⟨τ q, memτ q⟩
  have hq : (⟨τ q, memτ q⟩ : S) = algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict (X q)) :=
    Subtype.ext (aeval_X τ q).symm
  change snd (φS ⟨τ q, memτ q⟩) = 0 at h
  rw [hq, hφS, aeval_X] at h
  simpa [dualPt] using h

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
