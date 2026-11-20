import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace PairConeAlg

/- English proof (translation)
Repeatedly rewrite using `[Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h : ψ (e i) = ∑ q, u.repr (e i) q * ψ (u q)` using `by conv_lhs => rw [← u.sum_repr (e i)]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, smul_eq_mul]`. Rewrite using `[h, map_sum, Finset.mul_sum]`. Simplify using `only [map_mul, mul_assoc]`.
-/
theorem eval_generic {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N : ℕ} (e u : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (ψ : Module.Dual Ω E) :
    ∑ i, t i * algebraMap Ω Φ (ψ (e i)) =
      ∑ q, (∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * algebraMap Ω Φ (ψ (u q)) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ψ (e i) = ∑ q, u.repr (e i) q * ψ (u q) := by
    conv_lhs => rw [← u.sum_repr (e i)]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [h, map_sum, Finset.mul_sum]
  simp only [map_mul, mul_assoc]

/- English proof (translation)
Rewrite using `[eval_generic e u t ψ, Finset.mul_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← map_mul]`. Use `congr 2`. Simplify using `only [map_div₀]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem expand {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N : ℕ} {σ : Type*} (e u : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (ψ : Module.Dual Ω E) (Y Z : Ω) (o : σ) :
    ∑ q, C (algebraMap Ω Φ (ψ (u q) / Z)) *
        (C (algebraMap Ω Φ Y * ∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * (X o : MvPolynomial σ Φ)) =
      C (algebraMap Ω Φ (Y / Z) * ∑ i, t i * algebraMap Ω Φ (ψ (e i))) * X o := by
  rw [eval_generic e u t ψ, Finset.mul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_assoc, ← map_mul]
  congr 2
  simp only [map_div₀]
  ring

/- English proof (translation)
Set `AC` to `Subalgebra.algebraicClosure R L`. Set `GA : Matrix n n AC` to `fun i j => ⟨G i j, hG i j⟩`. Set `f : AC →+* L` to `AC.val.toRingHom`. Establish `hmap : f.mapMatrix GA = G` using `by ext i j; rfl`. Establish `hadj : ∀ i j, G.adjugate i j ∈ AC`.

Introduce `i j`. Rewrite using `[← hmap, ← RingHom.map_adjugate]`. Conclude with `(GA.adjugate i j).2`. Establish `hdetA : G.det ∈ AC`. Rewrite using `[← hmap, ← RingHom.map_det]`.

Conclude with `(GA.det).2`. Establish `key : G.det * w q = (G.adjugate.mulVec (G.mulVec w)) q`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Both sides reduce to the same expression. Use `IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hdet) hdetA ?_` and prove the remaining obligations.

Rewrite using `[key]`. Conclude with `Subalgebra.sum_mem AC fun j _ => AC.mul_mem (hadj q j) (hGw j)`.
-/
theorem isAlgebraic_of_mulVec {R L : Type*} [CommRing R] [IsDomain R] [CommRing L] [IsDomain L]
    [Algebra R L] {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n L) (w : n → L)
    (hG : ∀ i j, IsAlgebraic R (G i j)) (hGw : ∀ i, IsAlgebraic R ((G.mulVec w) i)) (hdet : G.det ≠ 0)
    (q : n) : IsAlgebraic R (w q) := by
  let AC := Subalgebra.algebraicClosure R L
  let GA : Matrix n n AC := fun i j => ⟨G i j, hG i j⟩
  let f : AC →+* L := AC.val.toRingHom
  have hmap : f.mapMatrix GA = G := by ext i j; rfl
  have hadj : ∀ i j, G.adjugate i j ∈ AC := by
    intro i j
    rw [← hmap, ← RingHom.map_adjugate]
    exact (GA.adjugate i j).2
  have hdetA : G.det ∈ AC := by
    rw [← hmap, ← RingHom.map_det]
    exact (GA.det).2
  have key : G.det * w q = (G.adjugate.mulVec (G.mulVec w)) q := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hdet) hdetA ?_
  rw [key]
  exact Subalgebra.sum_mem AC fun j _ => AC.mul_mem (hadj q j) (hGw j)

end PairConeAlg

open PairConeAlg GenericProjClosureDim in

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht`. Establish `hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0` using `fun k => by`. Take `⟨j, hj⟩` from `hV.multiProj.relevant k`. Use `⟨j, fun h0 => hj ?_⟩` and prove the remaining obligations. Rewrite using `[pointIdeal, RingHom.mem_ker]`.

Simplify using `[pointConeMap, h0]`. Use `choose c hc using hne`. Establish `hyc : segreVec y c ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`. Establish `hli` using `ht.linearIndependent`. Use `Module.Finite.of_basis e` as an intermediate fact.

Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : Fin N → Fin M, LinearIndependent Ω (φ ∘ l) := by`. Take `⟨κ, a, ha, hsp, hind⟩` from `exists_linearIndependent' Ω φ`. Establish `: Finite κ` using `Finite.of_injective a ha`. Use `haveI := Fintype.ofFinite κ`. Establish `hcard : Fintype.card κ = N`.

Rewrite using `[← finrank_span_eq_card hind, hsp, TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc, finrank_top, Subspace.dual_finrank_eq, Module.finrank_eq_card_basis e, Fintype.card_fin]`. Set `σ` to `Fintype.equivFinOfCardEq hcard`. Conclude with `⟨a ∘ σ.symm, hind.comp σ.symm σ.symm.injective⟩`. Take `⟨m', hm'⟩` from `exists_ne_zero_of_span hN e hli φ' (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)`. Establish `hϖ0 : algebraMap O Ω ϖ ≠ 0`.

Introduce `h0`. Establish `hmem : ϖ ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)`. Rewrite using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0, map_zero]`. Rewrite `hmem` using `[hV.noTorsion]`. Conclude with `hϖ.ne_zero (Ideal.mem_bot.1 hmem)`.

Take `⟨k', f, cc, hf, hcc, hsum, hb⟩` from `B.frame c hyc`. Use `choose b hbli hbsp hiff using hb`. Take `⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0` from `by by_contra! h`. Simplify using `[h] at hsum`. Establish `hsec : ∀ q, ∃ n : ℕ, f l0 ^ n • b l0 q ∈ B.lat c` using `fun q => (hiff l0 (b l0 q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by`.

Distinguish the cases in `h : q' = q`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]⟩, by simp [Pi.single_apply]⟩`. Use `choose n hn using hsec`.

Set `u` to `(Module.Basis.mk (hbli l0) (hbsp l0).ge).isUnitSMul (fun q => (pow_ne_zero (n q) hl0).isUnit)`. Establish `hu : ∀ q, u q ∈ B.lat c` using `fun q => by`. Rewrite using `[Module.Basis.isUnitSMul_apply, Module.Basis.mk_apply]`. Conclude with `hn q`. Use `set Y : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀ k with hYdef`.

Use `set Y' : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀' k with hY'def`. Establish `hY : Y ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)`. Establish `hY' : Y' ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)`. Set `Gm : Matrix (Fin N) (Fin N) Ω` to `fun i q => φ (l i) (u q) / Y`. Establish `hdet : Gm.det ≠ 0`.

Introduce `h0`. Take `⟨r, hr0, hr⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h0`. Apply `hr0` to reduce the goal to its premises. Establish `hzero : ∑ i, r i • φ (l i) = 0`. Use `u.ext fun q => ?_` and prove the remaining obligations.

Establish `hq` using `congrFun hr q`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply, Gm] at hq`. Rewrite using `[LinearMap.zero_apply, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by field_simp`. Use `_ = 0 := by rw [hq, mul_zero]`. Conclude with `funext (Fintype.linearIndependent_iff.1 hl r hzero)`. Establish `key : ∀ A1 : Subalgebra O (MvPolynomial (Option (Option K)) Φ), (∀ q : Σ k, ι k, C (algebraMap Ω Φ (y q)) * X (some (some q.1)) ∈ A1) → (∀ i, C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none) ∈ A1) → C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none ∈ A1 → ∀ p : Σ o, b …`.

Introduce `A1 h1 h2 h3`. Set `AC` to `Subalgebra.algebraicClosure A1 (MvPolynomial (Option (Option K)) Φ)`. Establish `hA : ∀ x ∈ A1, x ∈ AC` using `fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : A1)`. Set `ψ : Ω →+* MvPolynomial (Option (Option K)) Φ` to `(C : Φ →+* _).comp (algebraMap Ω Φ)`. Establish `hψ : ∀ a, ψ a = C (algebraMap Ω Φ a)` using `fun _ => rfl`.

Set `G : Subalgebra O Ω` to `{ carrier := {a | ψ a ∈ AC} mul_mem' := fun {a b} ha hb => by show ψ (a * b) ∈ AC`. Rewrite using `[map_mul]`. Conclude with `AC.mul_mem ha hb`. Use the proof step `add_mem' := fun {a b} ha hb => by show ψ (a + b) ∈ AC`. Rewrite using `[map_add]`.

Conclude with `AC.add_mem ha hb`. Use the proof step `algebraMap_mem' := fun r => by show ψ (algebraMap O Ω r) ∈ AC`. Establish `: ψ (algebraMap O Ω r) = algebraMap O (MvPolynomial (Option (Option K)) Φ) r`. Rewrite using `[hψ, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]`. Rewrite using `[this]`.

Conclude with `hA _ (A1.algebraMap_mem r) }`. Establish `hratio : ∀ k j, ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ AC`. Introduce `k j`. Establish `h0 : C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ)` using `mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (by rw [← hψ]; exact (map_ne_zero ψ).2 (hc k)) (X_ne_zero _))`. Use `IsAlgebraic.of_mul h0 (hA _ (h1 ⟨k, c k⟩)) ?_` and prove the remaining obligations.

Establish `: C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) * ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) = C (algebraMap Ω Φ (y ⟨k, j⟩)) * X (some (some k))`. Rewrite using `[hψ, mul_right_comm, ← map_mul, ← map_mul, mul_div_cancel₀ _ (hc k)]`. Rewrite using `[this]`. Conclude with `hA _ (h1 ⟨k, j⟩)`. Establish `hchart : chartRing O (segreVec y) c ≤ G`.

Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `show ψ (segreVec y j / segreVec y c) ∈ AC`. Rewrite using `[segreVec, segreVec, ← Finset.prod_div_distrib, map_prod]`. Conclude with `Subalgebra.prod_mem AC fun k _ => hratio k (j k)`.

Establish `hϖG : ψ (algebraMap O Ω ϖ) ∈ AC` using `G.algebraMap_mem ϖ`. Establish `hg : ∀ l q, ψ (φ l (u q) / Y) ∈ AC`. Introduce `l q`. Take `⟨a, ha, hrep⟩` from `hφ.sections c hyc l (u q) (hu q)`. Establish `: φ l (u q) / Y = a` using `by rw [hrep, mul_div_cancel_right₀ _ hY]`.

Rewrite using `[this]`. Conclude with `hchart ha`. Establish `hg' : ∀ l q, ψ (φ' l (u q) / Y') ∈ AC`. Introduce `l q`. Take `⟨m, hm⟩` from `(hB c hyc).1 (u q) (hu q)`.

Take `⟨a, ha, hrep⟩` from `hφ'.sections c hyc l _ hm`. Rewrite `hrep` using `[map_smul, smul_eq_mul]`. Establish `h0 : ψ (algebraMap O Ω ϖ ^ m) ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ)` using `mem_nonZeroDivisors_of_ne_zero ((map_ne_zero ψ).2 (pow_ne_zero _ hϖ0))`. Establish `hpow : ψ (algebraMap O Ω ϖ ^ m) ∈ AC`. Rewrite using `[map_pow]`.

Conclude with `AC.pow_mem hϖG m`. Use `IsAlgebraic.of_mul h0 hpow ?_` and prove the remaining obligations. Rewrite using `[← map_mul, mul_div_assoc', hrep, mul_div_cancel_right₀ _ hY']`. Conclude with `hchart ha`. Set `w : Fin N → MvPolynomial (Option (Option K)) Φ` to `fun q => C (algebraMap Ω Φ Y * ∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * X (some none)`.

Establish `hx : ∀ lφ, C (pairProjCoord y e φ φ' t ⟨some none, lφ⟩) * X (some none) = ∑ q, ψ (φ lφ (u q) / Y) * w q`. Introduce `lφ`. Use `expand e u t (φ lφ) Y Y (some none : Option (Option K))` as an intermediate fact. Rewrite `this` using `[div_self hY, map_one, one_mul]`. Conclude with `this.symm`.

Establish `hw : ∀ q, w q ∈ AC`. Introduce `q`. Use `isAlgebraic_of_mulVec (Gm.map ψ) w (fun i j => hg _ _) (fun i => ?_) ?_ q` and prove the remaining obligations. Establish `: ((Gm.map ψ).mulVec w) i = ∑ q, ψ (φ (l i) (u q) / Y) * w q` using `rfl`. Rewrite using `[this, ← hx (l i)]`.

Conclude with `hA _ (h2 i)`. Use `show (ψ.mapMatrix Gm).det ≠ 0`. Rewrite using `[← RingHom.map_det]`. Conclude with `(map_ne_zero ψ).2 hdet`. Introduce and unpack `⟨(_ | _ | k), j⟩`.

Set `P : Fin M' → MvPolynomial (Option (Option K)) Φ` to `fun l' => ∑ q, ψ (φ' l' (u q) / Y') * w q`. Establish `hP : ∀ l', P l' = C (algebraMap Ω Φ (Y / Y') * pairProjCoord y e φ φ' t ⟨none, l'⟩) * X (some none)` using `fun l' => expand e u t (φ' l') Y Y' (some none : Option (Option K))`. Establish `hPA : ∀ l', P l' ∈ AC` using `fun l' => Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg' l' q) (hw q)`. Establish `hP0 : P m' ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ)`. Rewrite using `[hP]`.

Use `mem_nonZeroDivisors_of_ne_zero (mul_ne_zero ?_ (X_ne_zero _))` and prove the remaining obligations. Rewrite using `[Ne, C_eq_zero]`. Conclude with `mul_ne_zero ((map_ne_zero _).2 (div_ne_zero hY hY')) hm'`. Use `IsAlgebraic.of_mul hP0 (hPA m') ?_` and prove the remaining obligations. Establish `: P m' * (C (pairProjCoord y e φ φ' t ⟨none, j⟩) * X none) = P j * (C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none)`.

Rewrite using `[hP m', hP j]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `AC.mul_mem (hPA j) (hA _ h3)`.

Use `show C (pairProjCoord y e φ φ' t ⟨some none, j⟩) * X (some none) ∈ AC`. Rewrite using `[hx]`. Conclude with `Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg j q) (hw q)`. Conclude with `hA _ (h1 ⟨k, j⟩)`. Conclude with `⟨l, m', hl, hm', key _ (fun q => Algebra.subset_adjoin (Or.inl ⟨q, rfl⟩)) (fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨Sum.inr (), rfl⟩))⟩`.
-/
theorem PairConeAlg.proof : PairConeAlg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
  classical

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent
  have := Module.Finite.of_basis e

  obtain ⟨l, hl⟩ : ∃ l : Fin N → Fin M, LinearIndependent Ω (φ ∘ l) := by
    obtain ⟨κ, a, ha, hsp, hind⟩ := exists_linearIndependent' Ω φ
    have : Finite κ := Finite.of_injective a ha
    haveI := Fintype.ofFinite κ
    have hcard : Fintype.card κ = N := by
      rw [← finrank_span_eq_card hind, hsp, TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc,
        finrank_top, Subspace.dual_finrank_eq, Module.finrank_eq_card_basis e, Fintype.card_fin]
    let σ := Fintype.equivFinOfCardEq hcard
    exact ⟨a ∘ σ.symm, hind.comp σ.symm σ.symm.injective⟩
  obtain ⟨m', hm'⟩ := exists_ne_zero_of_span hN e hli φ'
    (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)

  have hϖ0 : algebraMap O Ω ϖ ≠ 0 := by
    intro h0
    have hmem : ϖ ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0,
        map_zero]
    rw [hV.noTorsion] at hmem
    exact hϖ.ne_zero (Ideal.mem_bot.1 hmem)

  obtain ⟨k', f, cc, hf, hcc, hsum, hb⟩ := B.frame c hyc
  choose b hbli hbsp hiff using hb
  obtain ⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  have hsec : ∀ q, ∃ n : ℕ, f l0 ^ n • b l0 q ∈ B.lat c := fun q =>
    (hiff l0 (b l0 q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      by_cases h : q' = q
      · subst h; simp
      · simp [h]⟩, by simp [Pi.single_apply]⟩
  choose n hn using hsec
  let u := (Module.Basis.mk (hbli l0) (hbsp l0).ge).isUnitSMul (fun q => (pow_ne_zero (n q) hl0).isUnit)
  have hu : ∀ q, u q ∈ B.lat c := fun q => by
    rw [Module.Basis.isUnitSMul_apply, Module.Basis.mk_apply]
    exact hn q
  set Y : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀ k with hYdef
  set Y' : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀' k with hY'def
  have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
  have hY' : Y' ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)

  let Gm : Matrix (Fin N) (Fin N) Ω := fun i q => φ (l i) (u q) / Y
  have hdet : Gm.det ≠ 0 := by
    intro h0
    obtain ⟨r, hr0, hr⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hr0
    have hzero : ∑ i, r i • φ (l i) = 0 := by
      refine u.ext fun q => ?_
      have hq := congrFun hr q
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, Gm] at hq
      rw [LinearMap.zero_apply, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      calc ∑ i, r i * φ (l i) (u q) = Y * ∑ i, r i * (φ (l i) (u q) / Y) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by field_simp
        _ = 0 := by rw [hq, mul_zero]
    exact funext (Fintype.linearIndependent_iff.1 hl r hzero)

  have key : ∀ A1 : Subalgebra O (MvPolynomial (Option (Option K)) Φ),
      (∀ q : Σ k, ι k, C (algebraMap Ω Φ (y q)) * X (some (some q.1)) ∈ A1) →
      (∀ i, C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none) ∈ A1) →
      C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none ∈ A1 →
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic A1 (C (pairProjCoord y e φ φ' t p) * X p.1) := by
    intro A1 h1 h2 h3
    let AC := Subalgebra.algebraicClosure A1 (MvPolynomial (Option (Option K)) Φ)
    have hA : ∀ x ∈ A1, x ∈ AC := fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : A1)
    let ψ : Ω →+* MvPolynomial (Option (Option K)) Φ := (C : Φ →+* _).comp (algebraMap Ω Φ)
    have hψ : ∀ a, ψ a = C (algebraMap Ω Φ a) := fun _ => rfl

    let G : Subalgebra O Ω :=
      { carrier := {a | ψ a ∈ AC}
        mul_mem' := fun {a b} ha hb => by
          show ψ (a * b) ∈ AC
          rw [map_mul]
          exact AC.mul_mem ha hb
        add_mem' := fun {a b} ha hb => by
          show ψ (a + b) ∈ AC
          rw [map_add]
          exact AC.add_mem ha hb
        algebraMap_mem' := fun r => by
          show ψ (algebraMap O Ω r) ∈ AC
          have : ψ (algebraMap O Ω r) = algebraMap O (MvPolynomial (Option (Option K)) Φ) r := by
            rw [hψ, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]
          rw [this]
          exact hA _ (A1.algebraMap_mem r) }
    have hratio : ∀ k j, ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ AC := by
      intro k j
      have h0 : C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) ∈
          nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) :=
        mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (by rw [← hψ]; exact (map_ne_zero ψ).2 (hc k)) (X_ne_zero _))
      refine IsAlgebraic.of_mul h0 (hA _ (h1 ⟨k, c k⟩)) ?_
      have : C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) * ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) =
          C (algebraMap Ω Φ (y ⟨k, j⟩)) * X (some (some k)) := by
        rw [hψ, mul_right_comm, ← map_mul, ← map_mul, mul_div_cancel₀ _ (hc k)]
      rw [this]
      exact hA _ (h1 ⟨k, j⟩)
    have hchart : chartRing O (segreVec y) c ≤ G := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      show ψ (segreVec y j / segreVec y c) ∈ AC
      rw [segreVec, segreVec, ← Finset.prod_div_distrib, map_prod]
      exact Subalgebra.prod_mem AC fun k _ => hratio k (j k)
    have hϖG : ψ (algebraMap O Ω ϖ) ∈ AC := G.algebraMap_mem ϖ

    have hg : ∀ l q, ψ (φ l (u q) / Y) ∈ AC := by
      intro l q
      obtain ⟨a, ha, hrep⟩ := hφ.sections c hyc l (u q) (hu q)
      have : φ l (u q) / Y = a := by rw [hrep, mul_div_cancel_right₀ _ hY]
      rw [this]
      exact hchart ha
    have hg' : ∀ l q, ψ (φ' l (u q) / Y') ∈ AC := by
      intro l q
      obtain ⟨m, hm⟩ := (hB c hyc).1 (u q) (hu q)
      obtain ⟨a, ha, hrep⟩ := hφ'.sections c hyc l _ hm
      rw [map_smul, smul_eq_mul] at hrep
      have h0 : ψ (algebraMap O Ω ϖ ^ m) ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) :=
        mem_nonZeroDivisors_of_ne_zero ((map_ne_zero ψ).2 (pow_ne_zero _ hϖ0))
      have hpow : ψ (algebraMap O Ω ϖ ^ m) ∈ AC := by
        rw [map_pow]
        exact AC.pow_mem hϖG m
      refine IsAlgebraic.of_mul h0 hpow ?_
      rw [← map_mul, mul_div_assoc', hrep, mul_div_cancel_right₀ _ hY']
      exact hchart ha

    let w : Fin N → MvPolynomial (Option (Option K)) Φ := fun q =>
      C (algebraMap Ω Φ Y * ∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * X (some none)
    have hx : ∀ lφ, C (pairProjCoord y e φ φ' t ⟨some none, lφ⟩) * X (some none) =
        ∑ q, ψ (φ lφ (u q) / Y) * w q := by
      intro lφ
      have := expand e u t (φ lφ) Y Y (some none : Option (Option K))
      rw [div_self hY, map_one, one_mul] at this
      exact this.symm
    have hw : ∀ q, w q ∈ AC := by
      intro q
      refine isAlgebraic_of_mulVec (Gm.map ψ) w (fun i j => hg _ _) (fun i => ?_) ?_ q
      · have : ((Gm.map ψ).mulVec w) i = ∑ q, ψ (φ (l i) (u q) / Y) * w q := rfl
        rw [this, ← hx (l i)]
        exact hA _ (h2 i)
      · show (ψ.mapMatrix Gm).det ≠ 0
        rw [← RingHom.map_det]
        exact (map_ne_zero ψ).2 hdet
    rintro ⟨(_ | _ | k), j⟩
    ·
      let P : Fin M' → MvPolynomial (Option (Option K)) Φ := fun l' => ∑ q, ψ (φ' l' (u q) / Y') * w q
      have hP : ∀ l', P l' = C (algebraMap Ω Φ (Y / Y') * pairProjCoord y e φ φ' t ⟨none, l'⟩) * X (some none) :=
        fun l' => expand e u t (φ' l') Y Y' (some none : Option (Option K))
      have hPA : ∀ l', P l' ∈ AC := fun l' => Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg' l' q) (hw q)
      have hP0 : P m' ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) := by
        rw [hP]
        refine mem_nonZeroDivisors_of_ne_zero (mul_ne_zero ?_ (X_ne_zero _))
        rw [Ne, C_eq_zero]
        exact mul_ne_zero ((map_ne_zero _).2 (div_ne_zero hY hY')) hm'
      refine IsAlgebraic.of_mul hP0 (hPA m') ?_
      have : P m' * (C (pairProjCoord y e φ φ' t ⟨none, j⟩) * X none) =
          P j * (C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none) := by
        rw [hP m', hP j]
        simp only [map_mul]
        ring
      rw [this]
      exact AC.mul_mem (hPA j) (hA _ h3)
    ·
      show C (pairProjCoord y e φ φ' t ⟨some none, j⟩) * X (some none) ∈ AC
      rw [hx]
      exact Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg j q) (hw q)
    ·
      exact hA _ (h1 ⟨k, j⟩)
  exact ⟨l, m', hl, hm', key _ (fun q => Algebra.subset_adjoin (Or.inl ⟨q, rfl⟩))
    (fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩))
    (Algebra.subset_adjoin (Or.inr ⟨Sum.inr (), rfl⟩))⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
