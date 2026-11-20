import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Take `⟨c, hc⟩` from `IsCO.res_surj (O := Λ) b`. Establish `hsurj : Function.Surjective f`. Introduce `y`. Take `⟨d, rfl⟩` from `IsLocalRing.residue_surjective y`. Conclude with `⟨algebraMap Λ B d, by rw [AlgHom.commutes]; rfl⟩`.

Establish `hmax : (RingHom.ker (f : B →+* ResidueField Λ)).IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ hsurj`. Establish `hk : RingHom.ker (f : B →+* ResidueField Λ) = maximalIdeal B` using `IsLocalRing.eq_maximalIdeal hmax`. Establish `h1 : f (b - algebraMap Λ B c) = 0`. Establish `hm : b - algebraMap Λ B c ∈ RingHom.ker (f : B →+* ResidueField Λ)` using `hk ▸ hc`. Simplify using `using hm`.

Establish `h2 : res Λ B (b - algebraMap Λ B c) = 0` using `(res_eq_zero_iff Λ B _).2 hc`. Rewrite `h1`, `h2` using `[map_sub, sub_eq_zero]`. Rewrite using `[h1, h2, AlgHom.commutes, AlgHom.commutes]`.
-/
private theorem algHom_res_unique {Λ B : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [Algebra Λ B] [IsCO Λ B]
    (f : B →ₐ[Λ] ResidueField Λ) (b : B) : f b = res Λ B b := by
  obtain ⟨c, hc⟩ := IsCO.res_surj (O := Λ) b
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Λ B d, by rw [AlgHom.commutes]; rfl⟩
  have hmax : (RingHom.ker (f : B →+* ResidueField Λ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  have hk : RingHom.ker (f : B →+* ResidueField Λ) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have h1 : f (b - algebraMap Λ B c) = 0 := by
    have hm : b - algebraMap Λ B c ∈ RingHom.ker (f : B →+* ResidueField Λ) := hk ▸ hc
    simpa using hm
  have h2 : res Λ B (b - algebraMap Λ B c) = 0 := (res_eq_zero_iff Λ B _).2 hc
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

/- English proof (translation)
Establish `hB : ∀ b : X.B, x (algebraMap X.B X.A b) = y (algebraMap X.B X.A b)`. Introduce `b`. Establish `h1` using `algHom_res_unique (x.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b`. Establish `h2` using `algHom_res_unique (y.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b`. Simplify using `only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2`.

Rewrite using `[h1, h2]`. Establish `hz : z ∈ (⊤ : Subalgebra X.B X.A)` using `trivial`. Rewrite `hz` using `[← X.gen]`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem w hw`.

Break down `hw with ⟨⟨g, i, j⟩, rfl⟩ | ⟨⟨v, i, j⟩, rfl⟩` into its components or cases. Conclude with `congrArg (fun Q => Q.r g i j) h`. Conclude with `congrArg (fun Q => Q.n v i j) h`. Consider the case `algebraMap b => exact hB b`. Consider the case `add u w _ _ hu hw => rw [map_add, map_add, hu, hw]`.

Consider the case `mul u w _ _ hu hw => rw [map_mul, map_mul, hu, hw]`.
-/
private theorem point_ext {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) (x y : X.A →ₐ[Λ] ResidueField Λ)
    (h : X.P.map (x : X.A →+* ResidueField Λ) = X.P.map (y : X.A →+* ResidueField Λ)) (z : X.A) : x z = y z := by
  have hB : ∀ b : X.B, x (algebraMap X.B X.A b) = y (algebraMap X.B X.A b) := by
    intro b
    have h1 := algHom_res_unique (x.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b
    have h2 := algHom_res_unique (y.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2
    rw [h1, h2]
  have hz : z ∈ (⊤ : Subalgebra X.B X.A) := trivial
  rw [← X.gen] at hz
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rcases hw with ⟨⟨g, i, j⟩, rfl⟩ | ⟨⟨v, i, j⟩, rfl⟩
    · exact congrArg (fun Q => Q.r g i j) h
    · exact congrArg (fun Q => Q.n v i j) h
  | algebraMap b => exact hB b
  | add u w _ _ hu hw => rw [map_add, map_add, hu, hw]
  | mul u w _ _ hu hw => rw [map_mul, map_mul, hu, hw]

/- English proof (translation)
Introduce `z hz`. Establish `hy : X.P.map ((((Polynomial.aeval t).restrictScalars Λ).comp f : X.A →ₐ[Λ] ResidueField Λ) : X.A →+* ResidueField Λ) = X.P.map (x : X.A →+* ResidueField Λ)`. Rewrite using `[← h]`. Both sides reduce to the same expression. Establish `hxz` using `point_ext X _ x hy z`.

Rewrite `hz`, the goal using `[RingHom.mem_ker]`. Rewrite using `[← hxz]`. Simplify using `[hz]`.
-/
private theorem ker_le_of_eval {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type}
    [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) (x : X.A →ₐ[Λ] ResidueField Λ)
    (f : X.A →ₐ[Λ] (ResidueField Λ)[X]) (t : ResidueField Λ)
    (h : (X.P.map (f : X.A →+* (ResidueField Λ)[X])).map (evalRingHom t) = X.P.map (x : X.A →+* ResidueField Λ)) :
    RingHom.ker f ≤ RingHom.ker x := by
  intro z hz
  have hy : X.P.map ((((Polynomial.aeval t).restrictScalars Λ).comp f : X.A →ₐ[Λ] ResidueField Λ) :
      X.A →+* ResidueField Λ) = X.P.map (x : X.A →+* ResidueField Λ) := by
    rw [← h]; rfl
  have hxz := point_ext X _ x hy z
  rw [RingHom.mem_ker] at hz ⊢
  rw [← hxz]
  simp [hz]

/- English proof (translation)
Introduce `O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a _ X J x x' hL`. Take `⟨Q, hQ, h0, h1⟩` from `hL`. Take `⟨f, hf, -⟩` from `X.line Q hQ`. Establish `k0 : RingHom.ker f ≤ RingHom.ker x` using `ker_le_of_eval X x f 0 (by rw [hf, h0])`. Establish `k1 : RingHom.ker f ≤ RingHom.ker x'` using `ker_le_of_eval X x' f 1 (by rw [hf, h1])`.

Use `haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f`. Take `⟨q, hq, hqf⟩` from `Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker f) bot_le`. Conclude with `⟨fun hA => ⟨q, hq, hqf.trans k1, hA q hq (hqf.trans k0)⟩, fun hA => ⟨q, hq, hqf.trans k0, hA q hq (hqf.trans k1)⟩⟩`.
-/
theorem UpperTheory.V.Ws.conn :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ (X : Space Φ a) (J : Ideal X.B) (x x' : X.A →ₐ[Λ] ResidueField Λ),
      Φ.Linked ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) (X.P.map (x' : X.A →+* ResidueField Λ)) →
      (X.AllIn J (RingHom.ker x) → X.SomeIn J (RingHom.ker x')) ∧ (X.AllIn J (RingHom.ker x') → X.SomeIn J (RingHom.ker x)) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a _ X J x x' hL
  obtain ⟨Q, hQ, h0, h1⟩ := hL
  obtain ⟨f, hf, -⟩ := X.line Q hQ
  have k0 : RingHom.ker f ≤ RingHom.ker x := ker_le_of_eval X x f 0 (by rw [hf, h0])
  have k1 : RingHom.ker f ≤ RingHom.ker x' := ker_le_of_eval X x' f 1 (by rw [hf, h1])
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨q, hq, hqf⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker f) bot_le
  exact ⟨fun hA => ⟨q, hq, hqf.trans k1, hA q hq (hqf.trans k0)⟩,
    fun hA => ⟨q, hq, hqf.trans k0, hA q hq (hqf.trans k1)⟩⟩
