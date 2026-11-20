import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.IsOrthogonalProjectionTwoLines

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq PositivityTheory.Rg.Tf.Adel ContinuousLinearMap
open scoped InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/- English proof (translation)
Take `⟨V, -, -, hV⟩` from `exists_polar (A ∘L B)`. Set `b` to `stdHilbertBasis ℂ K`. Establish `h1 : IsHilbertSchmidt (adjoint A ∘L V)` using `hA.adjoint.comp_right V`. Use `(traceNorm_le_of_adjoint_comp b hV).trans_lt ?_` and prove the remaining obligations. Establish `h2 : ∑' i, ‖⟪V (b i), (A ∘L B) (b i)⟫_ℂ‖ₑ ≤ ∑' i, (‖(adjoint A ∘L V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2)`.

Use `ENNReal.tsum_le_tsum fun i => ?_` and prove the remaining obligations. Rewrite using `[comp_apply, ← adjoint_inner_left, comp_apply]`. Conclude with `(enorm_inner_le _ _).trans (ennreal_mul_le_sq_add_sq _ _)`. Use `h2.trans_lt ?_` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_add, ← hsNormSq_eq_tsum b, ← hsNormSq_eq_tsum b]`.

Conclude with `ENNReal.add_lt_top.2 ⟨h1, hB⟩`.
-/
private theorem tc_two {A : H →L[ℂ] K} {B : K →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsTraceClass (A ∘L B) := by
  obtain ⟨V, -, -, hV⟩ := exists_polar (A ∘L B)
  let b := stdHilbertBasis ℂ K
  have h1 : IsHilbertSchmidt (adjoint A ∘L V) := hA.adjoint.comp_right V
  refine (traceNorm_le_of_adjoint_comp b hV).trans_lt ?_
  have h2 : ∑' i, ‖⟪V (b i), (A ∘L B) (b i)⟫_ℂ‖ₑ ≤ ∑' i, (‖(adjoint A ∘L V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [comp_apply, ← adjoint_inner_left, comp_apply]
    exact (enorm_inner_le _ _).trans (ennreal_mul_le_sq_add_sq _ _)
  refine h2.trans_lt ?_
  rw [ENNReal.tsum_add, ← hsNormSq_eq_tsum b, ← hsNormSq_eq_tsum b]
  exact ENNReal.add_lt_top.2 ⟨h1, hB⟩

/- English proof (translation)
Take `⟨S, R, hS, hR, rfl⟩` from `hT.exists_comp`. Establish `hA : IsHilbertSchmidt (π ∘L S)` using `hS.comp_left π`. Establish `hB : IsHilbertSchmidt (R ∘L ι)` using `hR.comp_right ι`. Establish `e : π ∘L (S ∘L R) ∘L ι = (π ∘L S) ∘L (R ∘L ι)` using `by ext1 x; rfl`. Rewrite using `[e]`.

Use `⟨tc_two hA hB, ?_⟩` and prove the remaining obligations. Establish `h1 : trace ((π ∘L S) ∘L (R ∘L ι)) = trace ((R ∘L ι) ∘L (π ∘L S))` using `(hasSum_inner_comp_comm (stdHilbertBasis ℂ K) (stdHilbertBasis ℂ H) hA hB).tsum_eq`. Establish `h2 : trace (R ∘L ((ι ∘L π) ∘L S)) = trace (((ι ∘L π) ∘L S) ∘L R)` using `trace_comp_comm_of_isHilbertSchmidt hR (hS.comp_left _)`. Establish `h4 : (R ∘L ι) ∘L (π ∘L S) = R ∘L ((ι ∘L π) ∘L S)` using `by ext1 x; rfl`. Rewrite using `[h1, h4, h2, comp_assoc, hP]`.
-/
private theorem tr_compress (ι : K →L[ℂ] H) (π : H →L[ℂ] K) {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (hP : (ι ∘L π) ∘L T = T) : IsTraceClass (π ∘L T ∘L ι) ∧ trace (π ∘L T ∘L ι) = trace T := by
  obtain ⟨S, R, hS, hR, rfl⟩ := hT.exists_comp
  have hA : IsHilbertSchmidt (π ∘L S) := hS.comp_left π
  have hB : IsHilbertSchmidt (R ∘L ι) := hR.comp_right ι
  have e : π ∘L (S ∘L R) ∘L ι = (π ∘L S) ∘L (R ∘L ι) := by ext1 x; rfl
  rw [e]
  refine ⟨tc_two hA hB, ?_⟩
  have h1 : trace ((π ∘L S) ∘L (R ∘L ι)) = trace ((R ∘L ι) ∘L (π ∘L S)) :=
     (hasSum_inner_comp_comm (stdHilbertBasis ℂ K) (stdHilbertBasis ℂ H) hA hB).tsum_eq
  have h2 : trace (R ∘L ((ι ∘L π) ∘L S)) = trace (((ι ∘L π) ∘L S) ∘L R) :=
    trace_comp_comm_of_isHilbertSchmidt hR (hS.comp_left _)
  have h4 : (R ∘L ι) ∘L (π ∘L S) = R ∘L ((ι ∘L π) ∘L S) := by ext1 x; rfl
  rw [h1, h4, h2, comp_assoc, hP]

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/- English proof (translation)
The claim follows from `isSelfAdjoint_iff_isSymmetric.2 h`.
-/
private theorem sa_of {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E}
    (h : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) : IsSelfAdjoint A :=
  isSelfAdjoint_iff_isSymmetric.2 h

/- English proof (translation)
The claim follows from `isSelfAdjoint_iff_isSymmetric.1 h x y`.
-/
private theorem sa_to {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E}
    (h : IsSelfAdjoint A) (x y : E) : ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ :=
  isSelfAdjoint_iff_isSymmetric.1 h x y

/- English proof (translation)
Establish `hadj' : ∀ x h, ⟪h, ι x⟫_ℂ = ⟪π h, x⟫_ℂ` using `fun x h => by`. Rewrite using `[← inner_conj_symm, hadj, inner_conj_symm]`. Establish `hii : ∀ x y, ⟪ι x, ι y⟫_ℂ = ⟪x, y⟫_ℂ` using `fun x y => by rw [hadj, hπι]`. Establish `hπJ : ∀ u, π (J u) = J₀ u` using `fun u => by rw [← hJ, hπι]`. Establish `hπJ' : ∀ u, π (J' u) = J₀' u` using `fun u => by rw [← hJ', hπι]`.

Establish `hin : ∀ u v, ⟪J₀ u, J₀' v⟫_ℂ = ⟪J u, J' v⟫_ℂ` using `fun u v => by rw [← hii, hJ, hJ']`. Set `D : Datum K V W` to `{ J := J₀ J' := J₀' T₀ := 0 B := π ∘L B ∘L ι β := β β' := β' span := fun h h1 h2 => by`. Rewrite using `[← hπι h]`. Use `hspan _ (fun u => ?_) fun u => ?_` and prove the remaining obligations. Rewrite using `[← hJ, hii, h1]`.

Rewrite using `[← hJ', hii, h2]`. Use `shift := fun t u u' v v' h1 h2 => by rw [hin, hin]; exact shift t u u' v v' h1 h2`. Use `causal := fun s u v h1 h2 => by rw [hin]; exact causal s u v h1 h2`. Use `β_ker := hβ`. Use the proof step `β'_ker := hβ'`.

Use `β_unit := hu`. Use the proof step `β'_unit := hu'`. Use `B_sa := sa_of fun x y => by`. Simplify using `only [comp_apply]`. Rewrite using `[← hadj', ← hadj, sa_to hB]`.

Use `B_J := fun u v h => by simp only [comp_apply]; rw [hJ, hBJ u v h, hπJ]`. Use the proof step `B_J' := fun u v h => by simp only [comp_apply]; rw [hJ', hBJ' u v h, hπJ']`. Use `compact := fun T Λ hT hΛ => by`. Take `⟨s1, s2, s3⟩` from `hΛ`. Establish `s2' : ∀ x, Λ (Λ x) = Λ x` using `fun x => congrArg (fun A : K →L[ℂ] K => A x) s2`.

Establish `ht : IsTrunc J J' T (ι ∘L Λ ∘L π + (1 - ι ∘L π))`. Use `⟨sa_of fun x y => ?_, ?_, fun h => ?_⟩` and prove the remaining obligations. Simplify using `only [add_apply, sub_apply, comp_apply, one_apply_eq_self, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, hadj, hadj', sa_to s1]`. Use extensionality with `x`. Simplify using `[hπι, s2']`.

Simplify using `only [add_apply, sub_apply, comp_apply, one_apply_eq_self]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `h1 : Λ (π h) = 0` using `by simpa [hπι] using congrArg π h0`. Establish `h2 : h = ι (π h)` using `by simpa [h1, sub_eq_zero] using h0`.

Take `⟨u, v, a1, a2, a3⟩` from `(s3 _).1 h1`. Conclude with `⟨u, v, a1, a2, by rw [h2, a3, map_add, hJ, hJ']⟩`. Introduce and unpack `⟨u, v, a1, a2, rfl⟩`. Establish `h1` using `(s3 _).2 ⟨u, v, a1, a2, rfl⟩`. Rewrite using `[map_add π, hπJ, hπJ', h1, map_add ι, hJ, hJ']`.

Simplify using the standard rewrite rules. Establish `hk` using `((hc T _ hT ht).comp_clm (ι ∘L Λ)).clm_comp π`. Establish `e : ⇑(Λ ∘L (π ∘L B ∘L ι) ∘L Λ) = ⇑π ∘ ⇑((ι ∘L Λ ∘L π + (1 - ι ∘L π)) ∘L B ∘L ι ∘L π) ∘ ⇑(ι ∘L Λ)`. Use function extensionality and compare the values at `x`. Simplify using `[hπι]`.

Rewrite using `[e]`. Conclude with `hk }`. Take `⟨N, hN1, hN2⟩` from `hM K V W D`. Use `⟨N, fun Y b b' k k' c c' => hN1 (π ∘L Y ∘L ι) b b' k k' (fun u v h => ?_) fun u v h => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π (Y (ι (J₀ u))) = J₀ v`.

Rewrite using `[hJ, c u v h, hπJ]`. Express the relevant statement in the definitionally equal form `π (Y (ι (J₀' u))) = J₀' v`. Rewrite using `[hJ', c' u v h, hπJ']`. Introduce `X Λ κ T C hκ hX hXP hT hΛ htc hb`. Take `⟨s1, s2, s3⟩` from `hΛ`.

Establish `s2' : ∀ x, Λ (Λ x) = Λ x` using `fun x => congrArg (fun A : H →L[ℂ] H => A x) s2`. Establish `hXP' : ∀ x, X (ι (π x)) = ι (π (X x))` using `fun x => congrArg (fun A : H →L[ℂ] H => A x) hXP`. Establish `e1 : ∀ x, ι (π (x - Λ x)) = x - Λ x` using `fun x => by`. Take `⟨u, v, -, -, a⟩` from `(s3 (x - Λ x)).1 (by simp [s2'])`. Rewrite using `[a, map_add, map_add, hπJ, hπJ', hJ, hJ']`.

Establish `e2 : ∀ x, Λ (ι (π x)) = ι (π (Λ x))` using `fun x => by`. Establish `a : ι (π x) - Λ (ι (π x)) = x - Λ x`. Use `ext_inner_left ℂ fun y => ?_` and prove the remaining obligations. Establish `b : ∀ z, ⟪y, z - Λ z⟫_ℂ = ⟪y - Λ y, z⟫_ℂ` using `fun z => by rw [inner_sub_left, inner_sub_right, sa_to s1]`. Rewrite using `[b, b, hadj', ← hadj', ← e1 y, hadj, hadj, hπι]`.

Establish `a'` using `e1 x`. Rewrite `a'` using `[map_sub, map_sub, ← a]`. Conclude with `(sub_right_injective a').symm`. Establish `e3 : ∀ x, ι (π (Λ (ι x))) = Λ (ι x)` using `fun x => by rw [← e2, hπι]`. Establish `ht : IsTrunc J₀ J₀' T (π ∘L Λ ∘L ι)`.

Use `⟨sa_of fun x y => ?_, ?_, fun h => ?_⟩` and prove the remaining obligations. Simplify using `only [comp_apply]`. Rewrite using `[← hadj', ← hadj, sa_to s1]`. Use `ext1 x`. Simplify using `only [comp_apply, e3, s2']`.

Simplify using `only [comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `h1 : Λ (ι h) = 0` using `by rw [← e3, h0, map_zero]`. Take `⟨u, v, a1, a2, a3⟩` from `(s3 _).1 h1`.

Conclude with `⟨u, v, a1, a2, by rw [← hπι h, a3, map_add, hπJ, hπJ']⟩`. Introduce and unpack `⟨u, v, a1, a2, rfl⟩`. Rewrite using `[map_add ι, hJ, hJ', (s3 _).2 ⟨u, v, a1, a2, rfl⟩, map_zero]`. Take `⟨t1, t2⟩` from `tr_compress ι π htc (by ext1 x`. Simplify using `only [comp_apply]`.

Rewrite using `[← e2, ← hXP', hπι])`. Establish `e4 : (π ∘L Λ ∘L ι) ∘L (π ∘L X ∘L ι) ∘L (π ∘L Λ ∘L ι) = π ∘L (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) ∘L ι` using `by ext1 x`. Simplify using `only [comp_apply]`. Rewrite using `[← hXP', hπι]`. Use `hN2 (π ∘L X ∘L ι) (π ∘L Λ ∘L ι) κ T C hκ (fun u v h => by` as an intermediate fact.

Express the relevant statement in the definitionally equal form `π (X (ι (J₀ u))) = J₀' v`. Rewrite using `[hJ, hX u v h, hπJ']) hT ht (e4 ▸ t1) hb`. Rewrite `this` using `[e4, t2]`. Simplify `this` using `[D]`.
-/
private theorem core (hM : Main) (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (ι : K →L[ℂ] H) (π : H →L[ℂ] K)
    (J₀ : L V →ₗᵢ[ℂ] K) (J₀' : L W →ₗᵢ[ℂ] K) (hJ : ∀ u, ι (J₀ u) = J u) (hJ' : ∀ u, ι (J₀' u) = J' u)
    (hπι : ∀ x, π (ι x) = x) (hadj : ∀ x h, ⟪ι x, h⟫_ℂ = ⟪x, π h⟫_ℂ)
    (hspan : ∀ h, (∀ u, ⟪J u, h⟫_ℂ = 0) → (∀ v, ⟪J' v, h⟫_ℂ = 0) → π h = 0)
    (shift : ∀ (t : ℝ) (u u' : L V) (v v' : L W), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
      ⟪J u', J' v⟫_ℂ = ⟪J u, J' v'⟫_ℂ)
    (causal : ∀ (s : ℝ) (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * 0 - s → v x = 0) →
      ⟪J u, J' v⟫_ℂ = 0)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W) (hβ : Ker β) (hβ' : Ker β') (hu : IsUnit (symb β 0))
    (hu' : IsUnit (symb β' 0)) (hB : IsSelfAdjoint B) (hBJ : Conv J J B β) (hBJ' : Conv J' J' B β')
    (hc : ∀ (T : ℝ) (Λ : H →L[ℂ] H), 0 ≤ T → IsTrunc J J' T Λ → IsCompactOperator (Λ ∘L B ∘L (ι ∘L π))) :
    ∃ N : W ≃ₗᵢ[ℂ] V,
      (∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → Conv J J Y β → Conv J' J' Y β' →
        ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
      ∀ (X Λ : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) (T C : ℝ), Ker κ → Conv J J' X κ → X ∘L (ι ∘L π) = (ι ∘L π) ∘L X → 0 ≤ T →
        IsTrunc J J' T Λ → IsTraceClass (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) →
        (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ C / (1 + |z.im|)) →
        ‖trace (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) -
            (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
          Module.finrank ℂ V * C * Real.exp (-2 * T) := by
  have hadj' : ∀ x h, ⟪h, ι x⟫_ℂ = ⟪π h, x⟫_ℂ := fun x h => by
    rw [← inner_conj_symm, hadj, inner_conj_symm]
  have hii : ∀ x y, ⟪ι x, ι y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by rw [hadj, hπι]
  have hπJ : ∀ u, π (J u) = J₀ u := fun u => by rw [← hJ, hπι]
  have hπJ' : ∀ u, π (J' u) = J₀' u := fun u => by rw [← hJ', hπι]
  have hin : ∀ u v, ⟪J₀ u, J₀' v⟫_ℂ = ⟪J u, J' v⟫_ℂ := fun u v => by rw [← hii, hJ, hJ']
  let D : Datum K V W :=
    { J := J₀
      J' := J₀'
      T₀ := 0
      B := π ∘L B ∘L ι
      β := β
      β' := β'
      span := fun h h1 h2 => by
        rw [← hπι h]
        refine hspan _ (fun u => ?_) fun u => ?_
        · rw [← hJ, hii, h1]
        · rw [← hJ', hii, h2]
      shift := fun t u u' v v' h1 h2 => by rw [hin, hin]; exact shift t u u' v v' h1 h2
      causal := fun s u v h1 h2 => by rw [hin]; exact causal s u v h1 h2
      β_ker := hβ
      β'_ker := hβ'
      β_unit := hu
      β'_unit := hu'
      B_sa := sa_of fun x y => by
        simp only [comp_apply]
        rw [← hadj', ← hadj, sa_to hB]
      B_J := fun u v h => by simp only [comp_apply]; rw [hJ, hBJ u v h, hπJ]
      B_J' := fun u v h => by simp only [comp_apply]; rw [hJ', hBJ' u v h, hπJ']
      compact := fun T Λ hT hΛ => by
        obtain ⟨s1, s2, s3⟩ := hΛ
        have s2' : ∀ x, Λ (Λ x) = Λ x := fun x => congrArg (fun A : K →L[ℂ] K => A x) s2
        have ht : IsTrunc J J' T (ι ∘L Λ ∘L π + (1 - ι ∘L π)) := by
          refine ⟨sa_of fun x y => ?_, ?_, fun h => ?_⟩
          · simp only [add_apply, sub_apply, comp_apply, one_apply_eq_self, inner_add_left, inner_add_right, inner_sub_left,
              inner_sub_right, hadj, hadj', sa_to s1]
          · ext x
            simp [hπι, s2']
          · simp only [add_apply, sub_apply, comp_apply, one_apply_eq_self]
            constructor
            · intro h0
              have h1 : Λ (π h) = 0 := by simpa [hπι] using congrArg π h0
              have h2 : h = ι (π h) := by simpa [h1, sub_eq_zero] using h0
              obtain ⟨u, v, a1, a2, a3⟩ := (s3 _).1 h1
              exact ⟨u, v, a1, a2, by rw [h2, a3, map_add, hJ, hJ']⟩
            · rintro ⟨u, v, a1, a2, rfl⟩
              have h1 := (s3 _).2 ⟨u, v, a1, a2, rfl⟩
              rw [map_add π, hπJ, hπJ', h1, map_add ι, hJ, hJ']
              simp
        have hk := ((hc T _ hT ht).comp_clm (ι ∘L Λ)).clm_comp π
        have e : ⇑(Λ ∘L (π ∘L B ∘L ι) ∘L Λ) =
            ⇑π ∘ ⇑((ι ∘L Λ ∘L π + (1 - ι ∘L π)) ∘L B ∘L ι ∘L π) ∘ ⇑(ι ∘L Λ) := by
          funext x
          simp [hπι]
        rw [e]
        exact hk }
  obtain ⟨N, hN1, hN2⟩ := hM K V W D
  refine ⟨N, fun Y b b' k k' c c' => hN1 (π ∘L Y ∘L ι) b b' k k' (fun u v h => ?_) fun u v h => ?_, ?_⟩
  · change π (Y (ι (J₀ u))) = J₀ v
    rw [hJ, c u v h, hπJ]
  · change π (Y (ι (J₀' u))) = J₀' v
    rw [hJ', c' u v h, hπJ']
  intro X Λ κ T C hκ hX hXP hT hΛ htc hb
  obtain ⟨s1, s2, s3⟩ := hΛ
  have s2' : ∀ x, Λ (Λ x) = Λ x := fun x => congrArg (fun A : H →L[ℂ] H => A x) s2
  have hXP' : ∀ x, X (ι (π x)) = ι (π (X x)) := fun x => congrArg (fun A : H →L[ℂ] H => A x) hXP
  have e1 : ∀ x, ι (π (x - Λ x)) = x - Λ x := fun x => by
    obtain ⟨u, v, -, -, a⟩ := (s3 (x - Λ x)).1 (by simp [s2'])
    rw [a, map_add, map_add, hπJ, hπJ', hJ, hJ']
  have e2 : ∀ x, Λ (ι (π x)) = ι (π (Λ x)) := fun x => by
    have a : ι (π x) - Λ (ι (π x)) = x - Λ x := by
      refine ext_inner_left ℂ fun y => ?_
      have b : ∀ z, ⟪y, z - Λ z⟫_ℂ = ⟪y - Λ y, z⟫_ℂ := fun z => by rw [inner_sub_left, inner_sub_right, sa_to s1]
      rw [b, b, hadj', ← hadj', ← e1 y, hadj, hadj, hπι]
    have a' := e1 x
    rw [map_sub, map_sub, ← a] at a'
    exact (sub_right_injective a').symm
  have e3 : ∀ x, ι (π (Λ (ι x))) = Λ (ι x) := fun x => by rw [← e2, hπι]
  have ht : IsTrunc J₀ J₀' T (π ∘L Λ ∘L ι) := by
    refine ⟨sa_of fun x y => ?_, ?_, fun h => ?_⟩
    · simp only [comp_apply]
      rw [← hadj', ← hadj, sa_to s1]
    · ext1 x
      simp only [comp_apply, e3, s2']
    · simp only [comp_apply]
      constructor
      · intro h0
        have h1 : Λ (ι h) = 0 := by rw [← e3, h0, map_zero]
        obtain ⟨u, v, a1, a2, a3⟩ := (s3 _).1 h1
        exact ⟨u, v, a1, a2, by rw [← hπι h, a3, map_add, hπJ, hπJ']⟩
      · rintro ⟨u, v, a1, a2, rfl⟩
        rw [map_add ι, hJ, hJ', (s3 _).2 ⟨u, v, a1, a2, rfl⟩, map_zero]
  obtain ⟨t1, t2⟩ := tr_compress ι π htc (by
    ext1 x
    simp only [comp_apply]
    rw [← e2, ← hXP', hπι])
  have e4 : (π ∘L Λ ∘L ι) ∘L (π ∘L X ∘L ι) ∘L (π ∘L Λ ∘L ι) = π ∘L (Λ ∘L X ∘L (ι ∘L π) ∘L Λ) ∘L ι := by
    ext1 x
    simp only [comp_apply]
    rw [← hXP', hπι]
  have := hN2 (π ∘L X ∘L ι) (π ∘L Λ ∘L ι) κ T C hκ (fun u v h => by
    change π (X (ι (J₀ u))) = J₀' v
    rw [hJ, hX u v h, hπJ']) hT ht (e4 ▸ t1) hb
  rw [e4, t2] at this
  simpa [D] using this

/- English proof (translation)
Take `⟨p1, p2, p3⟩` from `hP`. Establish `p2' : ∀ x, P (P x) = P x` using `fun x => congrArg (fun A : H →L[ℂ] H => A x) p2`. Set `S : Submodule ℂ H` to `(1 - P : H →L[ℂ] H).ker`. Establish `hS : ∀ x, x ∈ S ↔ P x = x` using `fun x => by`. Simplify using `only [S, LinearMap.mem_ker, coe_coe, sub_apply, one_apply_eq_self, sub_eq_zero]`.

Conclude with `eq_comm`. Use `haveI : CompleteSpace S := (1 - P : H →L[ℂ] H).isClosed_ker.completeSpace_coe`. Establish `fix : ∀ x, (∀ h, P h = 0 → ⟪x, h⟫_ℂ = 0) → x ∈ S` using `fun x hx => by`. Use `(hS x).2 (ext_inner_right ℂ fun y => ?_)` and prove the remaining obligations. Use `hx (y - P y) (by simp [p2'])` as an intermediate fact.

Rewrite `this` using `[inner_sub_right, sub_eq_zero]`. Rewrite using `[sa_to p1, this]`. Establish `m1 : ∀ u, J u ∈ S` using `fun u => fix _ fun h hh => ((p3 h).1 hh).1 u`. Establish `m2 : ∀ u, J' u ∈ S` using `fun u => fix _ fun h hh => ((p3 h).1 hh).2 u`. Set `π : H →L[ℂ] S` to `P.codRestrict S fun x => (hS _).2 (p2' x)`.

Establish `e : S.subtypeL ∘L π = P` using `by ext1 x; rfl`. Use `core hM J J' S.subtypeL π ⟨J.toLinearMap.codRestrict S m1, fun u => J.norm_map u⟩ ⟨J'.toLinearMap.codRestrict S m2, fun u => J'.norm_map u⟩ (fun _ => rfl) (fun _ => rfl) (fun x => Subtype.ext ((hS _).1 x.2)) (fun x h => by` as an intermediate fact. Express the relevant statement in the definitionally equal form `⟪(x : H), h⟫_ℂ = ⟪(x : H), P h⟫_ℂ`. Rewrite using `[← sa_to p1, (hS _).1 x.2])`. Use the proof step `(fun h h1 h2 => Subtype.ext ((p3 h).2 ⟨h1, h2⟩)) shift causal B β β' hβ hβ' hu hu' hB hBJ hBJ' (by rw [e]; exact hc)`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem scat_on_span (hM : Main) (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (shift : ∀ (t : ℝ) (u u' : L V) (v v' : L W), (∀ᵐ x : ℝ, u' x = u (x + t)) → (∀ᵐ x : ℝ, v' x = v (x + t)) →
      ⟪J u', J' v⟫_ℂ = ⟪J u, J' v'⟫_ℂ)
    (causal : ∀ (s : ℝ) (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → (∀ᵐ x : ℝ, x ≤ 2 * 0 - s → v x = 0) →
      ⟪J u, J' v⟫_ℂ = 0)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W) (hβ : Ker β) (hβ' : Ker β') (hu : IsUnit (symb β 0))
    (hu' : IsUnit (symb β' 0)) (hB : IsSelfAdjoint B) (hBJ : Conv J J B β) (hBJ' : Conv J' J' B β')
    (hc : ∀ (T : ℝ) (Λ : H →L[ℂ] H), 0 ≤ T → IsTrunc J J' T Λ → IsCompactOperator (Λ ∘L B ∘L P)) :
    ∃ N : W ≃ₗᵢ[ℂ] V,
      (∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → Conv J J Y β → Conv J' J' Y β' →
        ∀ w, N (symb β' 0 w) = symb β 0 (N w)) ∧
      ∀ (X Λ : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W) (T C : ℝ), Ker κ → Conv J J' X κ → X ∘L P = P ∘L X → 0 ≤ T →
        IsTrunc J J' T Λ → IsTraceClass (Λ ∘L X ∘L P ∘L Λ) →
        (∀ z : ℂ, |z.re| ≤ 1 → ‖symb κ z‖ ≤ C / (1 + |z.im|)) →
        ‖trace (Λ ∘L X ∘L P ∘L Λ) -
            (1 / 2 : ℂ) * LinearMap.trace ℂ V ((N.toLinearEquiv : W →ₗ[ℂ] V) ∘ₗ (symb κ 0 : V →ₗ[ℂ] W))‖ ≤
          Module.finrank ℂ V * C * Real.exp (-2 * T) := by
  obtain ⟨p1, p2, p3⟩ := hP
  have p2' : ∀ x, P (P x) = P x := fun x => congrArg (fun A : H →L[ℂ] H => A x) p2
  let S : Submodule ℂ H := (1 - P : H →L[ℂ] H).ker
  have hS : ∀ x, x ∈ S ↔ P x = x := fun x => by
    simp only [S, LinearMap.mem_ker, coe_coe, sub_apply, one_apply_eq_self, sub_eq_zero]
    exact eq_comm
  haveI : CompleteSpace S := (1 - P : H →L[ℂ] H).isClosed_ker.completeSpace_coe
  have fix : ∀ x, (∀ h, P h = 0 → ⟪x, h⟫_ℂ = 0) → x ∈ S := fun x hx => by
    refine (hS x).2 (ext_inner_right ℂ fun y => ?_)
    have := hx (y - P y) (by simp [p2'])
    rw [inner_sub_right, sub_eq_zero] at this
    rw [sa_to p1, this]
  have m1 : ∀ u, J u ∈ S := fun u => fix _ fun h hh => ((p3 h).1 hh).1 u
  have m2 : ∀ u, J' u ∈ S := fun u => fix _ fun h hh => ((p3 h).1 hh).2 u
  let π : H →L[ℂ] S := P.codRestrict S fun x => (hS _).2 (p2' x)
  have e : S.subtypeL ∘L π = P := by ext1 x; rfl
  have := core hM J J' S.subtypeL π ⟨J.toLinearMap.codRestrict S m1, fun u => J.norm_map u⟩
    ⟨J'.toLinearMap.codRestrict S m2, fun u => J'.norm_map u⟩ (fun _ => rfl) (fun _ => rfl)
    (fun x => Subtype.ext ((hS _).1 x.2))
    (fun x h => by
      change ⟪(x : H), h⟫_ℂ = ⟪(x : H), P h⟫_ℂ
      rw [← sa_to p1, (hS _).1 x.2])
    (fun h h1 h2 => Subtype.ext ((p3 h).2 ⟨h1, h2⟩)) shift causal B β β' hβ hβ' hu hu' hB hBJ hBJ' (by rw [e]; exact hc)
  rwa [e] at this

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
