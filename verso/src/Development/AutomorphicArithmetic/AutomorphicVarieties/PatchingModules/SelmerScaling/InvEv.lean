import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l hl L G G0 h n x hl2 Y _ hT hd`. Establish `hmul : ∀ g g', x.ρX x.Fr (g * g') = x.ρX x.Fr g * x.ρX x.Fr g'`. Introduce `g g'`. Simplify using `only [NP.ρX, mat, map_mul, Units.val_mul]`. Conclude with `Matrix.map_mul`.

Establish `hone : x.ρX x.Fr 1 = 1`. Simplify using `only [NP.ρX, mat, map_one, Units.val_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hsurj : Function.Surjective h.p₀`. Introduce `g`.

Take `⟨γ, hγ⟩` from `h.surj g.1`. Establish `hm : γ ∈ G.η.ker`. Rewrite using `[MonoidHom.mem_ker, ← h.η γ, hγ]`. Conclude with `g.2`. Conclude with `⟨⟨γ, hm⟩, Subtype.ext hγ⟩`.

Establish `hc : ∀ g, x.ρX x.Fr g * Y = Y * x.ρX x.Fr g`. Introduce `g`. Take `⟨γ, rfl⟩` from `hsurj g`. Establish `e` using `hd γ`. Simplify using `only [dY, sub_eq_zero] at e`.

Establish `e2 : x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ) = 1`. Rewrite using `[← hmul, ← map_mul, inv_mul_cancel, map_one, hone]`. Combine the equalities or inequalities in the displayed calculation. Establish `hs : ∀ Z ∈ Submodule.span x.A (mat x.ρ '' (G0.frame.G' : Set G0.frame.G₀)), Z.map (algebraMap x.A x.Fr) * Y = Y * Z.map (algebraMap x.A x.Fr)`. Introduce `Z hZ`.

Proceed by induction on `hZ using Submodule.span_induction with`. Consider the case `mem Z hZ`. Take `⟨g, _, rfl⟩` from `hZ`. Conclude with `hc g`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb`. Rewrite using `[Matrix.map_add _ (map_add _), add_mul, mul_add, ha, hb]`. Consider the case `smul c a _ ha`. Establish `: (c • a).map (algebraMap x.A x.Fr) = algebraMap x.A x.Fr c • a.map (algebraMap x.A x.Fr)`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.smul_mul, Matrix.mul_smul, ha]`. Establish `h2 : (2 : x.Fr) ≠ 0`. Establish `hu : IsUnit (2 : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`.

Establish `: ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1`. Rewrite using `[PadicInt.norm_int_lt_one_iff_dvd]`. Introduce `hdv`. Establish `: l ∣ 2` using `by exact_mod_cast hdv`. Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 this)`.

Establish `h3 : ‖((2 : ℤ) : ℤ_[l])‖ = 1` using `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 this)`. Simplify using `using h3`. Use `(hu.map (((algebraMap x.A x.Fr).comp (algebraMap x.K x.A)).comp (algebraMap ℤ_[l] x.K))).ne_zero` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Use extensionality with `i j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `e` using `congrFun (congrFun hT i) i`. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply] at e`. Establish `: (2 : x.Fr) * Y i i = 0` using `by linear_combination e`.

Simplify using `using (mul_eq_zero.1 this).resolve_left h2`. Establish `hE : (Matrix.single i i (1 : x.A)) ∈ Ev x.A x.A n x.a`. Introduce `p q`. Use `⟨fun _ => trivial, fun hne => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_bot]`.

Apply `Matrix.single_apply_of_ne` to reduce the goal to its premises. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hne Iff.rfl`. Take `⟨s, hsp⟩` from `x.span _ hE`. Establish `e` using `hs _ hsp`.

Establish `hm : ((PowerSeries.X : PowerSeries x.K) ^ s • Matrix.single i i (1 : x.A)).map (algebraMap x.A x.Fr) = Matrix.single i i (algebraMap x.A x.Fr (x.t ^ s))`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one, Matrix.map_single]`. Rewrite `e` using `[hm]`. Establish `e'` using `congrFun (congrFun e i) j`. Rewrite `e'` using `[Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hij)]`.

Establish `ht : algebraMap x.A x.Fr (x.t ^ s) ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `pow_ne_zero _ PowerSeries.X_ne_zero`. Simplify using `using (mul_eq_zero.1 e').resolve_left ht`.
-/
theorem UpperTheory.V.Pa.invEv :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), l ≠ 2 → ∀ Y : Matrix (Fin n) (Fin n) x.Fr, Y ∈ Ev x.A x.Fr n x.a → Yᵀ = -Y → (∀ g : G.G₀, dY G.frame (fun g => x.ρX x.Fr (h.p₀ g)) Y g = 0) → Y = 0 := by
  intro l hl L G G0 h n x hl2 Y _ hT hd
  have hmul : ∀ g g', x.ρX x.Fr (g * g') = x.ρX x.Fr g * x.ρX x.Fr g' := by
    intro g g'
    simp only [NP.ρX, mat, map_mul, Units.val_mul]
    exact Matrix.map_mul
  have hone : x.ρX x.Fr 1 = 1 := by
    simp only [NP.ρX, mat, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hsurj : Function.Surjective h.p₀ := by
    intro g
    obtain ⟨γ, hγ⟩ := h.surj g.1
    have hm : γ ∈ G.η.ker := by
      rw [MonoidHom.mem_ker, ← h.η γ, hγ]
      exact g.2
    exact ⟨⟨γ, hm⟩, Subtype.ext hγ⟩
  have hc : ∀ g, x.ρX x.Fr g * Y = Y * x.ρX x.Fr g := by
    intro g
    obtain ⟨γ, rfl⟩ := hsurj g
    have e := hd γ
    simp only [dY, sub_eq_zero] at e
    have e2 : x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ) = 1 := by
      rw [← hmul, ← map_mul, inv_mul_cancel, map_one, hone]
    calc x.ρX x.Fr (h.p₀ γ) * Y
        = x.ρX x.Fr (h.p₀ γ) * Y * (x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ)) := by rw [e2, mul_one]
      _ = Y * x.ρX x.Fr (h.p₀ γ) := by rw [← mul_assoc, e]
  have hs : ∀ Z ∈ Submodule.span x.A (mat x.ρ '' (G0.frame.G' : Set G0.frame.G₀)),
      Z.map (algebraMap x.A x.Fr) * Y = Y * Z.map (algebraMap x.A x.Fr) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, _, rfl⟩ := hZ
      exact hc g
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Matrix.map_add _ (map_add _), add_mul, mul_add, ha, hb]
    | smul c a _ ha =>
      have : (c • a).map (algebraMap x.A x.Fr) = algebraMap x.A x.Fr c • a.map (algebraMap x.A x.Fr) := by
        ext i j; simp
      rw [this, Matrix.smul_mul, Matrix.mul_smul, ha]
  have h2 : (2 : x.Fr) ≠ 0 := by
    have hu : IsUnit (2 : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      have : ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro hdv
        have : l ∣ 2 := by exact_mod_cast hdv
        exact hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 this)
      have h3 : ‖((2 : ℤ) : ℤ_[l])‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 this)
      simpa using h3
    have := (hu.map (((algebraMap x.A x.Fr).comp (algebraMap x.K x.A)).comp (algebraMap ℤ_[l] x.K))).ne_zero
    rwa [map_ofNat] at this
  ext i j
  by_cases hij : i = j
  · subst hij
    have e := congrFun (congrFun hT i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at e
    have : (2 : x.Fr) * Y i i = 0 := by linear_combination e
    simpa using (mul_eq_zero.1 this).resolve_left h2
  · have hE : (Matrix.single i i (1 : x.A)) ∈ Ev x.A x.A n x.a := by
      intro p q
      refine ⟨fun _ => trivial, fun hne => ?_⟩
      rw [Submodule.mem_bot]
      apply Matrix.single_apply_of_ne
      rintro ⟨rfl, rfl⟩
      exact hne Iff.rfl
    obtain ⟨s, hsp⟩ := x.span _ hE
    have e := hs _ hsp
    have hm : ((PowerSeries.X : PowerSeries x.K) ^ s • Matrix.single i i (1 : x.A)).map (algebraMap x.A x.Fr)
        = Matrix.single i i (algebraMap x.A x.Fr (x.t ^ s)) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.map_single]
    rw [hm] at e
    have e' := congrFun (congrFun e i) j
    rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hij)] at e'
    have ht : algebraMap x.A x.Fr (x.t ^ s) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact pow_ne_zero _ PowerSeries.X_ne_zero
    simpa using (mul_eq_zero.1 e').resolve_left ht
