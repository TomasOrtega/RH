import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global.SemiLocal GroundTheory.Automorphic ValuativeRel

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff]`. Conclude with `(ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one`.
-/
private theorem mem_integers_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : x ∈ 𝒪[v.adicCompletion K] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one

/- English proof (translation)
Rewrite using `[mem_integers_iff, mem_integers_iff, valued_completionMap]`. Conclude with `pow_le_one_iff (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 F)).ne'`.
-/
private theorem completionMap_mem_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v) (x : v.adicCompletion F) :
    completionMap v w.1 x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F] := by
  rw [mem_integers_iff, mem_integers_iff, valued_completionMap]
  exact pow_le_one_iff (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 F)).ne'

/- English proof (translation)
Introduce `F E _ _ _ _ _ n v t`. Establish `key : ∀ w : PlacesOver E v, mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) t) ∈ GLnLocal.integralGL (w.1.adicCompletion E) n ↔ t ∈ KF F n v`. Introduce `w`. Establish `hc : ∀ s : GL (Fin n) (v.adicCompletion F), mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) s) = mapGL n (completionMap v w.1) s` using `fun s => Units.ext (Matrix.ext fun i j => rfl)`. Rewrite using `[hc, GLnLocal.mem_integralGL_iff, GLnLocal.mem_integralGL_iff, ← map_inv]`.

Conclude with `and_congr (forall₂_congr fun i j => completionMap_mem_iff v w _) (forall₂_congr fun i j => completionMap_mem_iff v w _)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hQv⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`.

Set `w : PlacesOver E v` to `⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, hQv⟩`. Conclude with `(key w).1 (h w)`. Introduce `h w`. Conclude with `(key w).2 h`.
-/
theorem UpperTheory.adicCompletion_integers_baseChange_iff :
    UnitIff := by
  intro F E _ _ _ _ _ n v t
  have key : ∀ w : PlacesOver E v,
      mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) t) ∈
        GLnLocal.integralGL (w.1.adicCompletion E) n ↔ t ∈ KF F n v := by
    intro w
    have hc : ∀ s : GL (Fin n) (v.adicCompletion F),
        mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) s) =
          mapGL n (completionMap v w.1) s := fun s => Units.ext (Matrix.ext fun i j => rfl)
    rw [hc, GLnLocal.mem_integralGL_iff, GLnLocal.mem_integralGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => completionMap_mem_iff v w _)
      (forall₂_congr fun i j => completionMap_mem_iff v w _)
  constructor
  · intro h
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    let w : PlacesOver E v := ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, hQv⟩
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 h
