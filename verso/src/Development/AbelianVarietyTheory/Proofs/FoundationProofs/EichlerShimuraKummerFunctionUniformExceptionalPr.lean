import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPowerUnitsTowerClosureProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceModularFunctionTowerLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPowOfGaussValuationCongrOneAlmostAllPrimesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemGammaOfMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDomGauss
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.Ues

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Establish `hmm : 0 < (m * m').det` using `by rw [Matrix.det_mul]; exact mul_pos h h'`. Unfold `toGQ`. Rewrite using `[dif_pos hmm, dif_pos h, dif_pos h']`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `Matrix.map_mul (f := Int.castRingHom ℚ)`.
-/
theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dif_pos hmm, dif_pos h, dif_pos h']
  apply Subtype.ext
  apply Units.ext
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

/- English proof (translation)
Introduce `γ hγ` and use `by rw [map_mul, hf γ hγ, hg γ hγ]`.
-/
theorem lev_mul {X : Tower Ω ε} {M : ℕ} {f g : X.K} (hf : Lev X M f) (hg : Lev X M g) : Lev X M (f * g) :=
  fun γ hγ => by rw [map_mul, hf γ hγ, hg γ hγ]

/- English proof (translation)
Introduce `γ hγ` and use `by rw [map_div₀, hf γ hγ, hg γ hγ]`.
-/
theorem lev_div {X : Tower Ω ε} {M : ℕ} {f g : X.K} (hf : Lev X M f) (hg : Lev X M g) : Lev X M (f / g) :=
  fun γ hγ => by rw [map_div₀, hf γ hγ, hg γ hγ]

/- English proof (translation)
Introduce `γ hγ` and use `by rw [map_pow, hf γ hγ]`.
-/
theorem lev_pow {X : Tower Ω ε} {M : ℕ} {f : X.K} (hf : Lev X M f) (k : ℕ) : Lev X M (f ^ k) :=
  fun γ hγ => by rw [map_pow, hf γ hγ]

/- English proof (translation)
Introduce `_ _` and use `AlgEquiv.commutes _ c`.
-/
theorem lev_const (X : Tower Ω ε) (M : ℕ) (c : Ω) : Lev X M (algebraMap Ω X.K c) :=
  fun _ _ => AlgEquiv.commutes _ c

/- English proof (translation)
Introduce `δ hδ`. Establish `e : γ * δ = (γ * δ * γ⁻¹) * γ` using `by group`. Rewrite using `[← X.sl_mul, ← map_mul, e, map_mul, X.sl_mul, hf _ ((CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ)]`.
-/
theorem lev_sl {X : Tower Ω ε} {M : ℕ} {f : X.K} (hf : Lev X M f) (γ : SL(2, ℤ)) : Lev X M (X.sl (ofSL γ) f) := by
  intro δ hδ
  have e : γ * δ = (γ * δ * γ⁻¹) * γ := by group
  rw [← X.sl_mul, ← map_mul, e, map_mul, X.sl_mul,
    hf _ ((CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ)]

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω M`. Introduce `δ hδ`.

Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one (ξ := s ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])`. Take `⟨h00, h01, h10, h11⟩` from `CongruenceSubgroup.Gamma_mem.1 hδ`. Use `X.recip M f hM hf ζ hζ s (i : ℤ) (by rw [← hi, zpow_natCast]) 1 δ (by simp [en, h00, h01, h10, h11])` as an intermediate fact. Rewrite `this` using `[map_one, X.sl_one]`. Conclude with `this.symm`.
-/
theorem lev_gal [IsAlgClosure ℚ Ω] {X : Tower Ω ε} {M : ℕ} (hM : 0 < M) {f : X.K} (hf : Lev X M f)
    (s : Ω ≃ₐ[ℚ] Ω) : Lev X M (X.gal s f) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  intro δ hδ
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := s ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  have := X.recip M f hM hf ζ hζ s (i : ℤ) (by rw [← hi, zpow_natCast]) 1 δ
    (by simp [en, h00, h01, h10, h11])
  rw [map_one, X.sl_one] at this
  exact this.symm

/- English proof (translation)
Establish `h1 : W.valuation x = 1`. Establish `e : x = 1 + (x - 1)` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]`. Establish `e : x * y - 1 = x * (y - 1) + (x - 1)` using `by ring`. Rewrite using `[e]`.

Conclude with `Valuation.map_add_lt _ (by rwa [map_mul, h1, one_mul]) hx`.
-/
theorem val_mul_sub_one {K : Type} [Field K] (W : ValuationSubring K) {x y : K} (hx : W.valuation (x - 1) < 1)
    (hy : W.valuation (y - 1) < 1) : W.valuation (x * y - 1) < 1 := by
  have h1 : W.valuation x = 1 := by
    have e : x = 1 + (x - 1) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  exact Valuation.map_add_lt _ (by rwa [map_mul, h1, one_mul]) hx

/- English proof (translation)
Introduce `W hW`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_one, one_pow, div_one, Units.val_mk0, KmapA.val_eq_one_iff _ hc]`. Conclude with `⟨hW.1 c, by rw [← map_inv₀]; exact hW.1 _⟩`.
-/
theorem const_mem_un (X : Tower Ω ε) (m : ℕ) {c : Ω} (hc : algebraMap Ω X.K c ≠ 0) :
    Units.mk0 (algebraMap Ω X.K c) hc ∈ X.Un m := by
  intro W hW
  refine ⟨1, ?_⟩
  rw [Units.val_one, one_pow, div_one, Units.val_mk0, KmapA.val_eq_one_iff _ hc]
  exact ⟨hW.1 c, by rw [← map_inv₀]; exact hW.1 _⟩

end GlobalTheory.KZ.ES.Ues

open GlobalTheory.KZ.ES.Ues in

/- English proof (translation)
Introduce `Ω _ _ _ ε X hhol l M₀ hl hM₀ hlM`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Take `⟨S₁, hS₁⟩` from `GlobalTheory.T.kronecker_congruence_modularFunctionTower_level ε X hhol l M₀ hl hM₀`. Take `⟨S₂, hS₂⟩` from `GlobalTheory.T.isPow_of_gauss_valuation_congr_one_almost_all_primes ε X hhol l M₀ hl hM₀ hlM`. Use `⟨S₁ ∪ S₂ ∪ M₀.primeFactors, ?_⟩` and prove the remaining obligations.

Introduce `q hq hqS V s hFrob n k f hf hlev γ hγ`. Simplify using `only [Finset.mem_union, not_or] at hqS`. Take `⟨⟨hq1, hq2⟩, hq3⟩` from `hqS`. Establish `hqM₀ : Nat.Coprime q M₀` using `(Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hq3 (Nat.mem_primeFactors.2 ⟨hq, h, hM₀.ne'⟩)`. Establish `hqM : Nat.Coprime q (M₀ * l ^ k)` using `Nat.Coprime.mul_right hqM₀ (Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_right hlM hqM₀))`.

Establish `hM : 0 < M₀ * l ^ k` using `Nat.mul_pos hM₀ (pow_pos hl.pos k)`. Take `⟨W, hDom, hGauss⟩` from `GlobalTheory.KZ.ES.exists_dom_gauss ε X V`. Establish `hY` using `Tower.overY_comap_sl_gal ε X ε.injective hhol`. Take `⟨hU1, hUmul, hUinv, -, -, hUpow, -⟩` from `UnClosure.un_closure ε X ε.injective hhol (l ^ n)`. Establish `hsl : ∀ (g : GQ) (u : X.Kˣ), u ∈ X.Un (l ^ n) → ∃ v ∈ X.Un (l ^ n), (v : X.K) = X.sl g u` using `fun g u hu => ⟨_, KmapA.un_map X (X.sl g).toRingEquiv (fun W hW => (hY W hW).1 g) _ u hu, rfl⟩`.

Establish `hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), u ∈ X.Un (l ^ n) → ∃ v ∈ X.Un (l ^ n), (v : X.K) = X.gal t u` using `fun t u hu => ⟨_, KmapA.un_map X (X.gal t) (fun W hW => (hY W hW).2 t) _ u hu, rfl⟩`. Take `⟨f', hf', ef'⟩` from `hsl (ofSL γ) f hf`. Establish `hlev' : Lev X (M₀ * l ^ k) (f' : X.K)` using `ef' ▸ lev_sl hlev γ`. Take `⟨c₁, hc₁⟩` from `(hS₁ q hq hq1 V s hFrob W hDom k f f.ne_zero hlev).1`. Take `⟨c₂, hc₂⟩` from `(hS₁ q hq hq1 V s hFrob W hDom k f' f'.ne_zero hlev').2`.

Establish `hc₁0 : c₁ ≠ 0` using `by rintro rfl; simp at hc₁`. Establish `hc₂0 : c₂ ≠ 0` using `by rintro rfl; simp at hc₂`. Establish `hc : algebraMap Ω X.K (c₁ * c₂) ≠ 0` using `(_root_.map_ne_zero _).2 (mul_ne_zero hc₁0 hc₂0)`. Establish `hsplit : X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (f' : X.K)`. Rewrite using `[toGQ_mul _ _ (by rw [γ.det_coe]; exact one_pos) (by simp [Matrix.det_fin_two, hq.pos]), Betti.toGQ_sl, X.sl_mul, ef']`.

Establish `hnlev` using `GlobalTheory.KZ.ES.lev_heckeProd ε X _ q f γ hM hq hqM hlev hγ`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN, eN⟩ : ∃ v ∈ X.Un (l ^ n), (v : X.K) = Nq X (M₀ * l ^ k) q f := by`. Unfold `Nq`. Use `Finset.prod_induction _ (fun x => ∃ v ∈ X.Un (l ^ n), (v : X.K) = x) ?_ ⟨1, hU1, rfl⟩ (fun j _ => hsl _ f hf)` and prove the remaining obligations. Introduce and unpack `_ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩`.

Conclude with `⟨a * b, hUmul a b ha hb, rfl⟩`. Take `⟨T, hT, eT⟩` from `hsl (toGQ !![(q : ℤ), 0; 0, 1]) f' hf'`. Take `⟨A, hA, eA⟩` from `hgal s f hf`. Take `⟨B, hB, eB⟩` from `hgal s.symm f' hf'`. Establish `hAl : Lev X (M₀ * l ^ k) (A : X.K)` using `eA ▸ lev_gal hM hlev s`.

Establish `hBl : Lev X (M₀ * l ^ k) (B : X.K)` using `eB ▸ lev_gal hM hlev' s.symm`. Rewrite `hnlev` using `[hsplit, ← eN, ← eT]`. Rewrite using `[hsplit, ← eN, ← eT, ← ef', ← eA, ← eB]`. Rewrite `hc₁` using `[← eN, ← eA]`. Rewrite `hc₂` using `[← eT, ← eB]`.

Establish `eU : ((Units.mk0 _ hc * (N * T) * (A * B ^ q)⁻¹ : X.Kˣ) : X.K) = algebraMap Ω X.K (c₁ * c₂) * (N * T) / (A * B ^ q)`. Simplify using `[div_eq_mul_inv]`. Take `⟨g, hg⟩` from `hS₂ q hq hq2 V hFrob.1 W hGauss n k (Units.mk0 _ hc * (N * T) * (A * B ^ q)⁻¹) (hUmul _ _ (hUmul _ _ (const_mem_un X _ hc) (hUmul _ _ hN hT)) (hUinv _ (hUmul _ _ hA (hUpow q _ hB)))) (by rw [eU]; exact lev_div (lev_mul (lev_const X _ _) hnlev) (lev_mul hAl (lev_pow hBl q))) (by`. Rewrite using `[eU]`. Use `val_mul_sub_one W hc₁ hc₂ using 3` and compare the differences between its conclusion and the goal.

Rewrite using `[map_mul]`. Use the proof step `ring)`. Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq (c₁ * c₂)⁻¹ (pow_pos hl.pos n)`. Establish `hb0 : algebraMap Ω X.K b ≠ 0`. Use `(_root_.map_ne_zero _).2 ?_` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `hb` using `[zero_pow (pow_pos hl.pos n).ne']`. Conclude with `inv_ne_zero (mul_ne_zero hc₁0 hc₂0) hb.symm`. Use `⟨Units.mk0 _ hb0 * g, ?_⟩` and prove the remaining obligations. Establish `hg'` using `congrArg (fun u : X.Kˣ => (u : X.K)) hg`.

Simplify using `only [eU, Units.val_pow_eq_pow_val] at hg'`. Rewrite using `[Units.val_mul, Units.val_mk0, mul_pow, ← map_pow, hb, ← hg', map_inv₀]`. Establish `hA0` using `A.ne_zero`. Establish `hB0` using `B.ne_zero`. Clear the denominators using the available nonvanishing facts.
-/
theorem GlobalTheory.KZ.ES.eichlerShimura_unit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ (n k : ℕ) (f : X.Kˣ), f ∈ X.Un (l ^ n) → Lev X (M₀ * l ^ k) f → ∀ γ : SL(2, ℤ), DiagMod (M₀ * l ^ k) q γ → ∃ g : X.Kˣ, Nq X (M₀ * l ^ k) q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL γ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n) := by
  intro Ω _ _ _ ε X hhol l M₀ hl hM₀ hlM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.kronecker_congruence_modularFunctionTower_level ε X hhol l M₀ hl hM₀
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.isPow_of_gauss_valuation_congr_one_almost_all_primes ε X hhol l M₀ hl hM₀ hlM
  refine ⟨S₁ ∪ S₂ ∪ M₀.primeFactors, ?_⟩
  intro q hq hqS V s hFrob n k f hf hlev γ hγ
  simp only [Finset.mem_union, not_or] at hqS
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hqS
  have hqM₀ : Nat.Coprime q M₀ :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hq3 (Nat.mem_primeFactors.2 ⟨hq, h, hM₀.ne'⟩)
  have hqM : Nat.Coprime q (M₀ * l ^ k) :=
    Nat.Coprime.mul_right hqM₀ (Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_right hlM hqM₀))
  have hM : 0 < M₀ * l ^ k := Nat.mul_pos hM₀ (pow_pos hl.pos k)
  obtain ⟨W, hDom, hGauss⟩ := GlobalTheory.KZ.ES.exists_dom_gauss ε X V
  have hY := Tower.overY_comap_sl_gal ε X ε.injective hhol
  obtain ⟨hU1, hUmul, hUinv, -, -, hUpow, -⟩ := UnClosure.un_closure ε X ε.injective hhol (l ^ n)
  have hsl : ∀ (g : GQ) (u : X.Kˣ), u ∈ X.Un (l ^ n) → ∃ v ∈ X.Un (l ^ n), (v : X.K) = X.sl g u := fun g u hu =>
    ⟨_, KmapA.un_map X (X.sl g).toRingEquiv (fun W hW => (hY W hW).1 g) _ u hu, rfl⟩
  have hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), u ∈ X.Un (l ^ n) → ∃ v ∈ X.Un (l ^ n), (v : X.K) = X.gal t u :=
    fun t u hu => ⟨_, KmapA.un_map X (X.gal t) (fun W hW => (hY W hW).2 t) _ u hu, rfl⟩
  obtain ⟨f', hf', ef'⟩ := hsl (ofSL γ) f hf
  have hlev' : Lev X (M₀ * l ^ k) (f' : X.K) := ef' ▸ lev_sl hlev γ
  obtain ⟨c₁, hc₁⟩ := (hS₁ q hq hq1 V s hFrob W hDom k f f.ne_zero hlev).1
  obtain ⟨c₂, hc₂⟩ := (hS₁ q hq hq1 V s hFrob W hDom k f' f'.ne_zero hlev').2
  have hc₁0 : c₁ ≠ 0 := by rintro rfl; simp at hc₁
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; simp at hc₂
  have hc : algebraMap Ω X.K (c₁ * c₂) ≠ 0 := (_root_.map_ne_zero _).2 (mul_ne_zero hc₁0 hc₂0)
  have hsplit : X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) =
      X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (f' : X.K) := by
    rw [toGQ_mul _ _ (by rw [γ.det_coe]; exact one_pos) (by simp [Matrix.det_fin_two, hq.pos]), Betti.toGQ_sl,
      X.sl_mul, ef']
  have hnlev := GlobalTheory.KZ.ES.lev_heckeProd ε X _ q f γ hM hq hqM hlev hγ
  obtain ⟨N, hN, eN⟩ : ∃ v ∈ X.Un (l ^ n), (v : X.K) = Nq X (M₀ * l ^ k) q f := by
    unfold Nq
    refine Finset.prod_induction _ (fun x => ∃ v ∈ X.Un (l ^ n), (v : X.K) = x) ?_ ⟨1, hU1, rfl⟩
      (fun j _ => hsl _ f hf)
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, hUmul a b ha hb, rfl⟩
  obtain ⟨T, hT, eT⟩ := hsl (toGQ !![(q : ℤ), 0; 0, 1]) f' hf'
  obtain ⟨A, hA, eA⟩ := hgal s f hf
  obtain ⟨B, hB, eB⟩ := hgal s.symm f' hf'
  have hAl : Lev X (M₀ * l ^ k) (A : X.K) := eA ▸ lev_gal hM hlev s
  have hBl : Lev X (M₀ * l ^ k) (B : X.K) := eB ▸ lev_gal hM hlev' s.symm
  rw [hsplit, ← eN, ← eT] at hnlev
  rw [hsplit, ← eN, ← eT, ← ef', ← eA, ← eB]
  rw [← eN, ← eA] at hc₁
  rw [← eT, ← eB] at hc₂
  have eU : ((Units.mk0 _ hc * (N * T) * (A * B ^ q)⁻¹ : X.Kˣ) : X.K) =
      algebraMap Ω X.K (c₁ * c₂) * (N * T) / (A * B ^ q) := by
    simp [div_eq_mul_inv]
  obtain ⟨g, hg⟩ := hS₂ q hq hq2 V hFrob.1 W hGauss n k (Units.mk0 _ hc * (N * T) * (A * B ^ q)⁻¹)
    (hUmul _ _ (hUmul _ _ (const_mem_un X _ hc) (hUmul _ _ hN hT)) (hUinv _ (hUmul _ _ hA (hUpow q _ hB))))
    (by rw [eU]; exact lev_div (lev_mul (lev_const X _ _) hnlev) (lev_mul hAl (lev_pow hBl q)))
    (by
      rw [eU]
      convert val_mul_sub_one W hc₁ hc₂ using 3
      rw [map_mul]; ring)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (c₁ * c₂)⁻¹ (pow_pos hl.pos n)
  have hb0 : algebraMap Ω X.K b ≠ 0 := by
    refine (_root_.map_ne_zero _).2 ?_
    rintro rfl
    rw [zero_pow (pow_pos hl.pos n).ne'] at hb
    exact inv_ne_zero (mul_ne_zero hc₁0 hc₂0) hb.symm
  refine ⟨Units.mk0 _ hb0 * g, ?_⟩
  have hg' := congrArg (fun u : X.Kˣ => (u : X.K)) hg
  simp only [eU, Units.val_pow_eq_pow_val] at hg'
  rw [Units.val_mul, Units.val_mk0, mul_pow, ← map_pow, hb, ← hg', map_inv₀]
  have hA0 := A.ne_zero
  have hB0 := B.ne_zero
  field_simp
