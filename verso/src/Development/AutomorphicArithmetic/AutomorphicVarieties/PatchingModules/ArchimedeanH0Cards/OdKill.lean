import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

/- English proof (translation)
Take `⟨q, hq⟩` from `CharP.exists K`. Use `haveI := hq`. Establish `hx : (q : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite K q)`. Establish `h1` using `congrArg (algebraMap ℤ_[l] K) (PadicInt.unitCoeff_spec hx)`. Rewrite `h1` using `[map_natCast, CharP.cast_eq_zero, map_mul, map_pow, map_natCast]`.

Establish `hu : algebraMap ℤ_[l] K (PadicInt.unitCoeff hx : ℤ_[l]) ≠ 0` using `((PadicInt.unitCoeff hx).isUnit.map (algebraMap ℤ_[l] K)).ne_zero`. Conclude with `pow_eq_zero_iff'.mp ((mul_eq_zero.mp h1.symm).resolve_left hu) |>.1`.
-/
private theorem UpperTheory.V.Pa.B2.odKill_char (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] :
    (l : K) = 0 := by
  obtain ⟨q, hq⟩ := CharP.exists K
  haveI := hq
  have hx : (q : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite K q)
  have h1 := congrArg (algebraMap ℤ_[l] K) (PadicInt.unitCoeff_spec hx)
  rw [map_natCast, CharP.cast_eq_zero, map_mul, map_pow, map_natCast] at h1
  have hu : algebraMap ℤ_[l] K (PadicInt.unitCoeff hx : ℤ_[l]) ≠ 0 :=
    ((PadicInt.unitCoeff hx).isUnit.map (algebraMap ℤ_[l] K)).ne_zero
  exact pow_eq_zero_iff'.mp ((mul_eq_zero.mp h1.symm).resolve_left hu) |>.1

/- English proof (translation)
Introduce `l _ L G G0 h n x X _ _ D hD`. Establish `hlA : (l : x.A) = 0` using `by show (l : PowerSeries x.K) = 0`. Rewrite using `[← map_natCast (algebraMap x.K (PowerSeries x.K)) l, odKill_char l x.K, map_zero]`. Use `⟨fun m => ?_, fun w m => ?_, fun u g hg m => ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]`.

Rewrite using `[← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]`. Take `⟨m', rfl⟩` from `D.surj (inU G u) m`. Use `(D.equiv (inU G u) g m').symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Set `g' : G.G₀` to `G.φu u g`.

Establish `hp : h.p₀ g' = G0.φu u g` using `Subtype.ext (by exact h.φu u g)`. Establish `hmem : h.p₀ g' ∈ G0.frame.Iu u`. Rewrite using `[hp]`. Conclude with `Subgroup.mem_map_of_mem _ hg`. Establish `h1 : x.ρ (h.p₀ g') = 1` using `x.ine u _ hmem`.

Establish `h2 : x.ρ (h.p₀ g'⁻¹) = 1` using `by rw [map_inv h.p₀, map_inv x.ρ, h1, inv_one]`. Apply `hD.e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((hD.e (D.M.ρ (g' : G.Γ) m')) : Matrix (Fin n) (Fin n) X) = hD.e m'`. Rewrite using `[hD.act g' m']`.

Use `show ((x.ρ (h.p₀ g') : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) * _ * ((x.ρ (h.p₀ g'⁻¹) : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) = _`. Rewrite using `[h1, h2, Units.val_one]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Pa.B2.odKill :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (D : Dat x.A (plOf G)), IsOd h x X D → (∀ m : D.M.X, l • m = 0) ∧ (∀ w, ∀ m : (D.Q w).X, l • m = 0) ∧ ∀ u, ∀ g ∈ L.Ju u, ∀ m : (D.Q (inU G u)).X, (D.Q (inU G u)).ρ g m = m := by
  intro l _ L G G0 h n x X _ _ D hD
  have hlA : (l : x.A) = 0 := by
    show (l : PowerSeries x.K) = 0
    rw [← map_natCast (algebraMap x.K (PowerSeries x.K)) l, odKill_char l x.K, map_zero]
  refine ⟨fun m => ?_, fun w m => ?_, fun u g hg m => ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]
  · rw [← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]
  · obtain ⟨m', rfl⟩ := D.surj (inU G u) m
    refine (D.equiv (inU G u) g m').symm.trans ?_
    congr 1
    let g' : G.G₀ := G.φu u g
    have hp : h.p₀ g' = G0.φu u g := Subtype.ext (by exact h.φu u g)
    have hmem : h.p₀ g' ∈ G0.frame.Iu u := by
      rw [hp]
      exact Subgroup.mem_map_of_mem _ hg
    have h1 : x.ρ (h.p₀ g') = 1 := x.ine u _ hmem
    have h2 : x.ρ (h.p₀ g'⁻¹) = 1 := by rw [map_inv h.p₀, map_inv x.ρ, h1, inv_one]
    apply hD.e.injective
    apply Subtype.ext
    show ((hD.e (D.M.ρ (g' : G.Γ) m')) : Matrix (Fin n) (Fin n) X) = hD.e m'
    rw [hD.act g' m']
    show ((x.ρ (h.p₀ g') : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) * _ *
      ((x.ρ (h.p₀ g'⁻¹) : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) = _
    rw [h1, h2, Units.val_one]
    simp
