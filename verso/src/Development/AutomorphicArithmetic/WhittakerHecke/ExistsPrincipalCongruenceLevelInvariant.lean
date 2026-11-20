import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Establish `hc : ContinuousAt (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) 0`. Use `Continuous.continuousAt ?_` and prove the remaining obligations. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Conclude with `((continuous_apply j).comp (continuous_apply i)).add continuous_const`. Establish `h0 : (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) ⁻¹' t ∈ 𝓝 (0 : Fin 2 → Fin 2 → R)` using `hc.preimage_mem_nhds (by`.

Establish `: (Matrix.of fun i j => (0 : Fin 2 → Fin 2 → R) i j + c i j : Matrix (Fin 2) (Fin 2) R) = c`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `ht)`.

Rewrite `h0` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t1, ht1, hI⟩` from `h0`. Establish `ht2 : ∀ i, ∃ W ∈ 𝓝 (0 : R), ∀ m : Fin 2 → R, (∀ j, m j ∈ W) → m ∈ t1 i` using `fun i => by`. Establish `h` using `ht1 i`. Rewrite `h` using `[Pi.zero_apply, nhds_pi, Filter.mem_pi]`.

Take `⟨J, -, s, hs, hJ⟩` from `h`. Conclude with `⟨⋂ j, s j, Filter.iInter_mem.2 hs, fun m hm => hJ fun j _ => Set.mem_iInter.1 (hm j) j⟩`. Use `choose W hW hWt using ht2`. Use `⟨⋂ i, W i, Filter.iInter_mem.2 hW, fun m hm => ?_⟩` and prove the remaining obligations. Establish `: (fun i j => m i j - c i j) ∈ (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) ⁻¹' t` using `hI fun i _ => hWt i _ fun j => Set.mem_iInter.1 (hm i j) i`.

Establish `e : (Matrix.of fun i j => (m i j - c i j) + c i j : Matrix (Fin 2) (Fin 2) R) = m`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(Matrix.of fun i j => (m i j - c i j) + c i j : Matrix (Fin 2) (Fin 2) R) ∈ t at this`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
private theorem mat_nhds {R : Type} [TopologicalSpace R] [AddGroup R] [IsTopologicalAddGroup R]
    (t : Set (Matrix (Fin 2) (Fin 2) R)) (c : Matrix (Fin 2) (Fin 2) R) (ht : t ∈ 𝓝 c) :
    ∃ W ∈ 𝓝 (0 : R), ∀ m : Matrix (Fin 2) (Fin 2) R, (∀ i j, m i j - c i j ∈ W) → m ∈ t := by
  have hc : ContinuousAt (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) 0 := by
    refine Continuous.continuousAt ?_
    refine continuous_matrix fun i j => ?_
    exact ((continuous_apply j).comp (continuous_apply i)).add continuous_const
  have h0 : (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) ⁻¹' t ∈ 𝓝 (0 : Fin 2 → Fin 2 → R) :=
    hc.preimage_mem_nhds (by
      have : (Matrix.of fun i j => (0 : Fin 2 → Fin 2 → R) i j + c i j : Matrix (Fin 2) (Fin 2) R) = c := by
        ext i j; simp
      rw [this]; exact ht)
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, -, t1, ht1, hI⟩ := h0
  have ht2 : ∀ i, ∃ W ∈ 𝓝 (0 : R), ∀ m : Fin 2 → R, (∀ j, m j ∈ W) → m ∈ t1 i := fun i => by
    have h := ht1 i
    rw [Pi.zero_apply, nhds_pi, Filter.mem_pi] at h
    obtain ⟨J, -, s, hs, hJ⟩ := h
    exact ⟨⋂ j, s j, Filter.iInter_mem.2 hs, fun m hm => hJ fun j _ => Set.mem_iInter.1 (hm j) j⟩
  choose W hW hWt using ht2
  refine ⟨⋂ i, W i, Filter.iInter_mem.2 hW, fun m hm => ?_⟩
  have : (fun i j => m i j - c i j) ∈ (fun e : Fin 2 → Fin 2 → R => (Matrix.of fun i j => e i j + c i j : Matrix (Fin 2) (Fin 2) R)) ⁻¹' t :=
    hI fun i _ => hWt i _ fun j => Set.mem_iInter.1 (hm i j) i
  have e : (Matrix.of fun i j => (m i j - c i j) + c i j : Matrix (Fin 2) (Fin 2) R) = m := by
    ext i j; simp
  change (Matrix.of fun i j => (m i j - c i j) + c i j : Matrix (Fin 2) (Fin 2) R) ∈ t at this
  rwa [e] at this

/- English proof (translation)
Rewrite `hV` using `[Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap]`. Take `⟨t, ht, hts⟩` from `hV`. Rewrite `ht` using `[map_one]`. Establish `ht' : t ∈ 𝓝 ((1 : Matrix (Fin 2) (Fin 2) R), MulOpposite.op (1 : Matrix (Fin 2) (Fin 2) R))` using `ht`. Take `⟨u, hu, w, hw, huw⟩` from `mem_nhds_prod_iff.1 ht'`.

Establish `hw' : MulOpposite.op ⁻¹' w ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) R)` using `MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hw`. Take `⟨W1, hW1, h1⟩` from `mat_nhds u 1 hu`. Take `⟨W2, hW2, h2⟩` from `mat_nhds _ 1 hw'`. Use `⟨W1 ∩ W2, Filter.inter_mem hW1 hW2, fun k hk hk' => hts ?_⟩` and prove the remaining obligations. Conclude with `huw (Set.mk_mem_prod (h1 _ fun i j => (hk i j).1) (h2 _ fun i j => (hk' i j).2))`.
-/
private theorem gl_nhds {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (V : Set (GL (Fin 2) R)) (hV : V ∈ 𝓝 (1 : GL (Fin 2) R)) :
    ∃ W ∈ 𝓝 (0 : R), ∀ k : GL (Fin 2) R, (∀ i j, k.val i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ W) →
      (∀ i j, (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ W) → k ∈ V := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨t, ht, hts⟩ := hV
  rw [map_one] at ht
  have ht' : t ∈ 𝓝 ((1 : Matrix (Fin 2) (Fin 2) R), MulOpposite.op (1 : Matrix (Fin 2) (Fin 2) R)) := ht
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1 ht'
  have hw' : MulOpposite.op ⁻¹' w ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) R) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hw
  obtain ⟨W1, hW1, h1⟩ := mat_nhds u 1 hu
  obtain ⟨W2, hW2, h2⟩ := mat_nhds _ 1 hw'
  refine ⟨W1 ∩ W2, Filter.inter_mem hW1 hW2, fun k hk hk' => hts ?_⟩
  exact huw (Set.mk_mem_prod (h1 _ fun i j => (hk i j).1) (h2 _ fun i j => (hk' i j).2))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(infEq E).symm x.1 = 0`. Rewrite using `[hx, map_zero]`.
-/
private theorem pInf_zero {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : A E) (hx : x.1 = 0) : pInf E x = 0 := by
  change (infEq E).symm x.1 = 0
  rw [hx, map_zero]

/- English proof (translation)
Introduce `E _ _ _ P f hf h`. Establish `hopen : IsOpen {k | GlobalTheory.CuspRep.finRep E 2 k f = f}` using `(P.cusp f hf).1.level`. Take `⟨l, hl⟩ : ∃ l, l = GeneralLinearGroup.map (pFin E) h` from `⟨_, rfl⟩`. Take `⟨y, hy⟩ : ∃ y, y = GeneralLinearGroup.map (pInf E) h` from `⟨_, rfl⟩`. Establish `hh : h = infGL E 2 y * finGL E 2 l` using `by rw [hy, hl]; exact (infGL_mul_finGL h).symm`.

Establish `hc : Continuous fun k : GL (Fin 2) (Af E) => l⁻¹ * k * l` using `(continuous_const.mul continuous_id).mul continuous_const`. Establish `hV : (fun k : GL (Fin 2) (Af E) => l⁻¹ * k * l) ⁻¹' {k | GlobalTheory.CuspRep.finRep E 2 k f = f} ∈ 𝓝 (1 : GL (Fin 2) (Af E))` using `hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simp))`. Take `⟨W, hW, hWk⟩` from `gl_nhds _ hV`. Take `⟨d, hd0, hd⟩` from `exists_forall_mul_mem_of_mem_nhds hW`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))`.

Establish `hM : 0 < Ideal.absNorm (Ideal.span {d})`. Use `Nat.pos_of_ne_zero fun h0 => hd0 ?_` and prove the remaining obligations. Rewrite `h0` using `[Ideal.absNorm_eq_zero_iff]`. Simplify using `using h0`. Use `⟨Ideal.absNorm (Ideal.span {d}), hM, fun κ hκ g => ?_⟩` and prove the remaining obligations.

Establish `hent : ∀ x : A E, ∀ c ∈ Oh E, x = (Ideal.absNorm (Ideal.span {d}) : A E) * c → pFin E x ∈ W`. Introduce and unpack `x c ⟨-, hc2⟩ rfl`. Establish `hint : algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * c.2 ∈ integralFiniteAdeles (𝓞 E) E`. Rewrite using `[mem_integralFiniteAdeles]`. Introduce `v`.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Express the relevant statement in the definitionally equal form `Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) v * c.2 v) ≤ 1`. Rewrite using `[Valuation.map_mul]`. Use `mul_le_one' ?_ (hc2 v)` and prove the remaining obligations. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (coe_algebraMap_mem_adicCompletionIntegers v e)`.

Use `hd _ hint` as an intermediate fact. Establish `e1 : pFin E ((Ideal.absNorm (Ideal.span {d}) : A E) * c) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E d) * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * c.2)`. Establish `e2 : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : FiniteAdeleRing (𝓞 E) E) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E d)`. Rewrite using `[← map_mul, ← map_mul, he, map_natCast, map_natCast]`. Rewrite using `[map_mul, map_natCast, e2, mul_assoc, ← mul_assoc (algebraMap E _ _) (algebraMap E _ _), mul_comm (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e)), mul_assoc]`.

Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `this`. Take `⟨k, hk⟩ : ∃ k, k = GeneralLinearGroup.map (pFin E) κ` from `⟨_, rfl⟩`. Establish `hκk : κ = finGL E 2 k`.

Establish `h1 : GeneralLinearGroup.map (pInf E) κ = 1`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Take `⟨⟨c, hc, hcx⟩, -⟩` from `hκ i j`. Establish `h0 : pInf E (κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) = 0`. Rewrite using `[hcx]`.

Conclude with `pInf_zero _ (by`. Express the relevant statement in the definitionally equal form `((Ideal.absNorm (Ideal.span {d}) : A E)).1 * c.1 = 0`. Rewrite using `[hc.1, mul_zero])`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Express the relevant statement in the definitionally equal form `pInf E (κ.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j`.

Rewrite using `[h0]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Use `infGL_mul_finGL κ` as an intermediate fact. Rewrite `this` using `[h1, map_one, one_mul, ← hk]`. Conclude with `this.symm`.

Establish `hkV : l⁻¹ * k * l ∈ {k | GlobalTheory.CuspRep.finRep E 2 k f = f}`. Use `hWk k (fun i j => ?_) (fun i j => ?_)` and prove the remaining obligations. Take `⟨⟨c, hc, hcx⟩, -⟩` from `hκ i j`. Use `hent _ c hc hcx` as an intermediate fact. Establish `e : k.val i j - (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E (κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j)`.

Rewrite using `[map_sub, hk]`. Use `congr 1`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Rewrite using `[e]`. Conclude with `this`.

Take `⟨-, ⟨c, hc, hcx⟩⟩` from `hκ i j`. Use `hent _ c hc hcx` as an intermediate fact. Establish `e : (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((κ⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j)`. Rewrite using `[map_sub, hk, ← map_inv]`. Use `congr 1`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Rewrite using `[e]`. Conclude with `this`. Establish `hfix : f.1 (g * h * finGL E 2 (l⁻¹ * k * l)) = f.1 (g * h)` using `congrFun (congrArg Subtype.val hkV) (g * h)`. Rewrite using `[← hfix, hκk, hh]`.

Use `congr 1`. Simplify using `only [map_mul, map_inv, mul_assoc]`. Rewrite using `[← mul_assoc (finGL E 2 k), ← infGL_comm]`. Simplify using `[mul_assoc]`.
-/
theorem UpperTheory.exists_principalCongruence_level_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (f : Sm E 2), f ∈ P.V → ∀ h : GL (Fin 2) (A E), ∃ M : ℕ, 0 < M ∧ ∀ κ : GL (Fin 2) (A E), CongE M κ → ∀ g, f.1 (g * κ * h) = f.1 (g * h) := by
  intro E _ _ _ P f hf h
  have hopen : IsOpen {k | GlobalTheory.CuspRep.finRep E 2 k f = f} := (P.cusp f hf).1.level
  obtain ⟨l, hl⟩ : ∃ l, l = GeneralLinearGroup.map (pFin E) h := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = GeneralLinearGroup.map (pInf E) h := ⟨_, rfl⟩
  have hh : h = infGL E 2 y * finGL E 2 l := by rw [hy, hl]; exact (infGL_mul_finGL h).symm
  have hc : Continuous fun k : GL (Fin 2) (Af E) => l⁻¹ * k * l :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hV : (fun k : GL (Fin 2) (Af E) => l⁻¹ * k * l) ⁻¹' {k | GlobalTheory.CuspRep.finRep E 2 k f = f} ∈ 𝓝 (1 : GL (Fin 2) (Af E)) :=
    hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simp))
  obtain ⟨W, hW, hWk⟩ := gl_nhds _ hV
  obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have hM : 0 < Ideal.absNorm (Ideal.span {d}) := by
    refine Nat.pos_of_ne_zero fun h0 => hd0 ?_
    rw [Ideal.absNorm_eq_zero_iff] at h0
    simpa using h0
  refine ⟨Ideal.absNorm (Ideal.span {d}), hM, fun κ hκ g => ?_⟩
  have hent : ∀ x : A E, ∀ c ∈ Oh E, x = (Ideal.absNorm (Ideal.span {d}) : A E) * c → pFin E x ∈ W := by
    rintro x c ⟨-, hc2⟩ rfl
    have hint : algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * c.2 ∈ integralFiniteAdeles (𝓞 E) E := by
      rw [mem_integralFiniteAdeles]
      intro v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) v * c.2 v) ≤ 1
      rw [Valuation.map_mul]
      refine mul_le_one' ?_ (hc2 v)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (coe_algebraMap_mem_adicCompletionIntegers v e)
    have := hd _ hint
    have e1 : pFin E ((Ideal.absNorm (Ideal.span {d}) : A E) * c) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E d) * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * c.2) := by
      have e2 : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : FiniteAdeleRing (𝓞 E) E) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E d) := by
        rw [← map_mul, ← map_mul, he, map_natCast, map_natCast]
      rw [map_mul, map_natCast, e2, mul_assoc, ← mul_assoc (algebraMap E _ _) (algebraMap E _ _), mul_comm (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E e)), mul_assoc]
      rfl
    rw [e1]
    exact this
  obtain ⟨k, hk⟩ : ∃ k, k = GeneralLinearGroup.map (pFin E) κ := ⟨_, rfl⟩
  have hκk : κ = finGL E 2 k := by
    have h1 : GeneralLinearGroup.map (pInf E) κ = 1 := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      obtain ⟨⟨c, hc, hcx⟩, -⟩ := hκ i j
      have h0 : pInf E (κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) = 0 := by
        rw [hcx]
        exact pInf_zero _ (by
          change ((Ideal.absNorm (Ideal.span {d}) : A E)).1 * c.1 = 0
          rw [hc.1, mul_zero])
      rw [map_sub, sub_eq_zero] at h0
      change pInf E (κ.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
      rw [h0]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have := infGL_mul_finGL κ
    rw [h1, map_one, one_mul, ← hk] at this
    exact this.symm
  have hkV : l⁻¹ * k * l ∈ {k | GlobalTheory.CuspRep.finRep E 2 k f = f} := by
    refine hWk k (fun i j => ?_) (fun i j => ?_)
    · obtain ⟨⟨c, hc, hcx⟩, -⟩ := hκ i j
      have := hent _ c hc hcx
      have e : k.val i j - (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E (κ.val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
        rw [map_sub, hk]
        congr 1
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [e]; exact this
    · obtain ⟨-, ⟨c, hc, hcx⟩⟩ := hκ i j
      have := hent _ c hc hcx
      have e : (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((κ⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
        rw [map_sub, hk, ← map_inv]
        congr 1
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [e]; exact this
  have hfix : f.1 (g * h * finGL E 2 (l⁻¹ * k * l)) = f.1 (g * h) := congrFun (congrArg Subtype.val hkV) (g * h)
  rw [← hfix, hκk, hh]
  congr 1
  simp only [map_mul, map_inv, mul_assoc]
  rw [← mul_assoc (finGL E 2 k), ← infGL_comm]
  simp [mul_assoc]
