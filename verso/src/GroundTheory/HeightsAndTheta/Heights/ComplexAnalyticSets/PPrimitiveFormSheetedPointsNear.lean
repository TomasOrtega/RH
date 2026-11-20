import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedPointsNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormMinimalFactorPoints
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticSimpleRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Use `set p : Polynomial ℂ := Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) with hp`. Establish `hlt : (∑ j : Fin n, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).degree < (Polynomial.X ^ n : Polynomial ℂ).degree`. Rewrite using `[Polynomial.degree_X_pow]`. Use `lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_` and prove the remaining obligations. Use `(Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun j _ => ?_` and prove the remaining obligations.

Conclude with `lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.2 j.isLt)`. Establish `hdeg : p.degree = n`. Rewrite using `[hp, Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]`. Take `⟨τ, hτ⟩` from `Complex.exists_root (f := p) (by rw [hdeg]; exact_mod_cast Nat.pos_of_ne_zero hn)`. Conclude with `⟨τ, by simpa [p, Polynomial.eval_finsetSum] using hτ⟩`.
-/
theorem PrimitiveFormSheetedPointsNear.exists_root (n : ℕ) (hn : n ≠ 0) (c : Fin n → ℂ) :
    ∃ τ : ℂ, τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0 := by
  set p : Polynomial ℂ := Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) with hp
  have hlt : (∑ j : Fin n, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).degree < (Polynomial.X ^ n : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun j _ => ?_
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.2 j.isLt)
  have hdeg : p.degree = n := by
    rw [hp, Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  obtain ⟨τ, hτ⟩ := Complex.exists_root (f := p) (by rw [hdeg]; exact_mod_cast Nat.pos_of_ne_zero hn)
  exact ⟨τ, by simpa [p, Polynomial.eval_finsetSum] using hτ⟩

/- English proof (translation)
Establish `h0 : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).eval τ = 0`. Simplify `hτ` using `[Polynomial.eval_finsetSum]`. Conclude with `hs.eval₂_derivative_ne_zero (RingHom.id ℂ) h0`.
-/
theorem PrimitiveFormSheetedPointsNear.derivative_ne_zero (n : ℕ) (c : Fin n → ℂ) (τ : ℂ)
    (hs : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hτ : τ ^ n + ∑ j, c j * τ ^ (j : ℕ) = 0) :
    (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 := by
  have h0 : (Polynomial.X ^ n + ∑ j, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).eval τ = 0 := by
    simpa [Polynomial.eval_finsetSum] using hτ
  exact hs.eval₂_derivative_ne_zero (RingHom.id ℂ) h0

/- English proof (translation)
Introduce `σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel U hU`. Take `⟨n, b, hb, hm, hsepm, hpts⟩` from `hmin σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel`. Establish `hgood : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧ (z ∈ X → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ))` using `by filter_upwards [hU, hP, eventually_all.2 hrel] with z h1 h2 h3 using ⟨h1, h2, fun hz i => h3 i hz⟩`. Take `⟨U₁, hU₁sub, hU₁o, hwU₁⟩` from `mem_nhds_iff.1 hgood`. Establish `hn : n ≠ 0`.

Introduce and unpack `rfl`. Simplify using `using hm.self_of_nhds hirr.1`. Establish `hE : ∀ᶠ y in 𝓝 (A w), (δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 → (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U₁ ∧ A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧ ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ) ∧ (δ y ≠ 0 → (Polynomial.X ^ n + ∑ …` using `by filter_upwards [hpts U₁ (hU₁o.mem_nhds hwU₁), hsepm, hsepP, eventually_all.2 fun j => (ha j).eventually_analyticAt, eventually_all.2 fun j => (hb j).eventually_analyticAt, hδ.eventually_analyticAt, eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyti …`. Take `⟨y, hyE, hyδ⟩` from `(hE.eventually_nhds.and_frequently (not_eventually.1 hδ0)).exists`. Take `⟨E, hEsub, hEo, hyE⟩` from `mem_nhds_iff.1 hyE`.

Take `⟨hptsy, hsepmy, hsepPy, hay, hby, -, -⟩` from `hEsub hyE`. Take `⟨τ, hτ⟩` from `PrimitiveFormSheetedPointsNear.exists_root n hn (fun j => b j y)`. Take `⟨⟨hzX, hzU₁⟩, hAz, hℓz⟩` from `hptsy hyδ τ hτ`. Use `set z : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hz`. Establish `hPτ : τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0`.

Simplify `(hU₁sub hzU₁).2.1 hzX` using `[hAz, hℓz]`. Take `⟨OP, BP, ψP, hOPo, hyOP, hBPo, hτBP, -, -, hψP⟩` from `hbr d N a y τ hay hPτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero N (fun j => a j y) τ (hsepPy hyδ) hPτ)`. Take `⟨Om, Bm, ψm, hOmo, hyOm, -, -, hψman, hψmy, hψm⟩` from `hbr d n b y τ hby hτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero n (fun j => b j y) τ (hsepmy hyδ) hτ)`. Establish `hδc : ContinuousOn δ E` using `fun t ht => (hEsub ht).2.2.2.2.2.1.continuousAt.continuousWithinAt`. Use `set O : Set (Fin d → ℂ) := (Om ∩ ψm ⁻¹' BP) ∩ OP ∩ (E ∩ δ ⁻¹' {0}ᶜ) with hO`.

Establish `hOo : IsOpen O` using `((hψman.continuousOn.isOpen_inter_preimage hOmo hBPo).inter hOPo).inter (hδc.isOpen_inter_preimage hEo isOpen_compl_singleton)`. Use `set g : (Fin d → ℂ) → σ → ℂ := fun t i => (∑ j, q i j t * ψm t ^ (j : ℕ)) / δ t with hg`. Establish `key : ∀ t ∈ O, g t ∈ X ∩ U₁ ∧ A (g t) = t ∧ ℓ (g t) = ψm t` using `fun t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩ => (hEsub htE).1 htδ (ψm t) (((hψm t htm).2 (ψm t) (hψm t htm).1).2 rfl)`. Establish `hPψ : ∀ t ∈ O, ψm t = ψP t` using `fun t ht => by`. Take `⟨⟨hgX, hgU⟩, hgA, hgℓ⟩` from `key t ht`.

Establish `h` using `(hU₁sub hgU).2.1 hgX`. Rewrite `h` using `[hgA, hgℓ]`. Conclude with `((hψP t ht.1.2).2 (ψm t) ht.1.1.2).1 h`. Use `set V : Set (σ → ℂ) := U₁ ∩ A ⁻¹' O ∩ ℓ ⁻¹' BP with hV`. Use `⟨z, ⟨hzX, (hU₁sub hzU₁).1⟩, by rw [hAz]; exact hyδ, O, V, g, hOo, (hU₁o.inter (hOo.preimage A.continuous)).inter (hBPo.preimage ℓ.continuous), ⟨⟨hzU₁, by rw [Set.mem_preimage, hAz]; exact ⟨⟨⟨hyOm, by rw [Set.mem_preimage, hψmy]; exact hτBP⟩, hyOP⟩, hyE, hyδ⟩⟩, by rw [Set.mem_prei …` and prove the remaining obligations.

Introduce and unpack `t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩`. Take `⟨-, -, -, -, -, -, hqt⟩` from `hEsub htE`. Establish `hδt : AnalyticAt ℂ δ t` using `(hEsub htE).2.2.2.2.2.1`. Use `AnalyticAt.pi fun i => AnalyticAt.fun_div ?_ hδt htδ` and prove the remaining obligations. Conclude with `Finset.analyticAt_fun_sum _ fun j _ => (hqt i j).mul ((hψman t htm).pow _)`.

Use extensionality with `z'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz'X, ⟨hz'U, hz'O⟩, hz'B⟩`. Use `⟨A z', hz'O, ?_⟩` and prove the remaining obligations. Establish `hs : ℓ z' = ψm (A z')`.

Rewrite using `[hPψ _ hz'O]`. Conclude with `((hψP _ hz'O.1.2).2 _ hz'B).1 ((hU₁sub hz'U).2.1 hz'X)`. Establish `hδt : δ (A z') ≠ 0` using `hz'O.2.2`. Use function extensionality and compare the values at `i`. Rewrite using `[hg, div_eq_iff hδt, ← hs, ← (hU₁sub hz'U).2.2 hz'X i, mul_comm]`.

Introduce and unpack `⟨t, ht, rfl⟩`. Take `⟨⟨hgX, hgU⟩, hgA, hgℓ⟩` from `key t ht`. Conclude with `⟨hgX, ⟨hgU, by rw [Set.mem_preimage, hgA]; exact ht⟩, by rw [Set.mem_preimage, hgℓ]; exact ht.1.1.2⟩`.
-/
theorem PrimitiveFormSheetedPointsNear.proof (hmin : PrimitiveFormMinimalFactorPoints.Statement)
    (hbr : AnalyticSimpleRootBranch.Statement) : PrimitiveFormSheetedPointsNear.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel U hU
  obtain ⟨n, b, hb, hm, hsepm, hpts⟩ :=
    hmin σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsepP hrel
  have hgood : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
      (z ∈ X → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) := by
    filter_upwards [hU, hP, eventually_all.2 hrel] with z h1 h2 h3 using ⟨h1, h2, fun hz i => h3 i hz⟩
  obtain ⟨U₁, hU₁sub, hU₁o, hwU₁⟩ := mem_nhds_iff.1 hgood
  have hn : n ≠ 0 := by
    rintro rfl
    simpa using hm.self_of_nhds hirr.1
  have hE : ∀ᶠ y in 𝓝 (A w), (δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 →
        (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U₁ ∧
          A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧
          ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ) ∧
      (δ y ≠ 0 → (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      (δ y ≠ 0 → (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      (∀ j, AnalyticAt ℂ (a j) y) ∧ (∀ j, AnalyticAt ℂ (b j) y) ∧ AnalyticAt ℂ δ y ∧
      (∀ i j, AnalyticAt ℂ (q i j) y) := by
    filter_upwards [hpts U₁ (hU₁o.mem_nhds hwU₁), hsepm, hsepP,
      eventually_all.2 fun j => (ha j).eventually_analyticAt, eventually_all.2 fun j => (hb j).eventually_analyticAt,
      hδ.eventually_analyticAt, eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt]
      with y h1 h2 h3 h4 h5 h6 h7 using ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨y, hyE, hyδ⟩ := (hE.eventually_nhds.and_frequently (not_eventually.1 hδ0)).exists
  obtain ⟨E, hEsub, hEo, hyE⟩ := mem_nhds_iff.1 hyE
  obtain ⟨hptsy, hsepmy, hsepPy, hay, hby, -, -⟩ := hEsub hyE
  obtain ⟨τ, hτ⟩ := PrimitiveFormSheetedPointsNear.exists_root n hn (fun j => b j y)
  obtain ⟨⟨hzX, hzU₁⟩, hAz, hℓz⟩ := hptsy hyδ τ hτ
  set z : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hz
  have hPτ : τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 := by
    simpa [hAz, hℓz] using (hU₁sub hzU₁).2.1 hzX
  obtain ⟨OP, BP, ψP, hOPo, hyOP, hBPo, hτBP, -, -, hψP⟩ :=
    hbr d N a y τ hay hPτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero N (fun j => a j y) τ (hsepPy hyδ) hPτ)
  obtain ⟨Om, Bm, ψm, hOmo, hyOm, -, -, hψman, hψmy, hψm⟩ :=
    hbr d n b y τ hby hτ (PrimitiveFormSheetedPointsNear.derivative_ne_zero n (fun j => b j y) τ (hsepmy hyδ) hτ)
  have hδc : ContinuousOn δ E := fun t ht => (hEsub ht).2.2.2.2.2.1.continuousAt.continuousWithinAt
  set O : Set (Fin d → ℂ) := (Om ∩ ψm ⁻¹' BP) ∩ OP ∩ (E ∩ δ ⁻¹' {0}ᶜ) with hO
  have hOo : IsOpen O := ((hψman.continuousOn.isOpen_inter_preimage hOmo hBPo).inter hOPo).inter
    (hδc.isOpen_inter_preimage hEo isOpen_compl_singleton)
  set g : (Fin d → ℂ) → σ → ℂ := fun t i => (∑ j, q i j t * ψm t ^ (j : ℕ)) / δ t with hg
  have key : ∀ t ∈ O, g t ∈ X ∩ U₁ ∧ A (g t) = t ∧ ℓ (g t) = ψm t := fun t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩ =>
    (hEsub htE).1 htδ (ψm t) (((hψm t htm).2 (ψm t) (hψm t htm).1).2 rfl)
  have hPψ : ∀ t ∈ O, ψm t = ψP t := fun t ht => by
    obtain ⟨⟨hgX, hgU⟩, hgA, hgℓ⟩ := key t ht
    have h := (hU₁sub hgU).2.1 hgX
    rw [hgA, hgℓ] at h
    exact ((hψP t ht.1.2).2 (ψm t) ht.1.1.2).1 h
  set V : Set (σ → ℂ) := U₁ ∩ A ⁻¹' O ∩ ℓ ⁻¹' BP with hV
  refine ⟨z, ⟨hzX, (hU₁sub hzU₁).1⟩, by rw [hAz]; exact hyδ, O, V, g, hOo,
    (hU₁o.inter (hOo.preimage A.continuous)).inter (hBPo.preimage ℓ.continuous),
    ⟨⟨hzU₁, by rw [Set.mem_preimage, hAz]; exact ⟨⟨⟨hyOm, by rw [Set.mem_preimage, hψmy]; exact hτBP⟩, hyOP⟩, hyE, hyδ⟩⟩,
      by rw [Set.mem_preimage, hℓz]; exact hτBP⟩, ?_, fun t ht => (key t ht).2.1, ?_⟩
  · rintro t ⟨⟨⟨htm, _⟩, _⟩, htE, htδ⟩
    obtain ⟨-, -, -, -, -, -, hqt⟩ := hEsub htE
    have hδt : AnalyticAt ℂ δ t := (hEsub htE).2.2.2.2.2.1
    refine AnalyticAt.pi fun i => AnalyticAt.fun_div ?_ hδt htδ
    exact Finset.analyticAt_fun_sum _ fun j _ => (hqt i j).mul ((hψman t htm).pow _)
  · ext z'
    constructor
    · rintro ⟨hz'X, ⟨hz'U, hz'O⟩, hz'B⟩
      refine ⟨A z', hz'O, ?_⟩
      have hs : ℓ z' = ψm (A z') := by
        rw [hPψ _ hz'O]; exact ((hψP _ hz'O.1.2).2 _ hz'B).1 ((hU₁sub hz'U).2.1 hz'X)
      have hδt : δ (A z') ≠ 0 := hz'O.2.2
      funext i
      rw [hg, div_eq_iff hδt, ← hs, ← (hU₁sub hz'U).2.2 hz'X i, mul_comm]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨⟨hgX, hgU⟩, hgA, hgℓ⟩ := key t ht
      exact ⟨hgX, ⟨hgU, by rw [Set.mem_preimage, hgA]; exact ht⟩, by rw [Set.mem_preimage, hgℓ]; exact ht.1.1.2⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
