import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc Matrix

/- English proof (translation)
Establish `h1 : u ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d⁻¹`. Rewrite using `[map_inv]`. Conclude with `eq_inv_of_mul_eq_one_left h`. Establish `h2 : u⁻¹ ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d`. Rewrite using `[inv_pow, h1, map_inv, inv_inv]`.

Establish `i1 : IsIntegral O (u : L)`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, h1]`. Conclude with `((d⁻¹ : (integralClosure O L)ˣ) : integralClosure O L).2`. Establish `i2 : IsIntegral O ((u⁻¹ : Lˣ) : L)`.

Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, h2]`. Conclude with `(d : integralClosure O L).2`. Conclude with `⟨⟨⟨u, i1⟩, ⟨(u⁻¹ : Lˣ), i2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, Units.ext rfl⟩`.
-/
private theorem scal_mem {O L : Type} [CommRing O] [CommRing L] [Algebra O L] (u : Lˣ)
    (d : (integralClosure O L)ˣ)
    (h : u ^ 2 * Units.map ((integralClosure O L).val : integralClosure O L →* L) d = 1) :
    ∃ w : (integralClosure O L)ˣ, Units.map ((integralClosure O L).val : integralClosure O L →* L) w = u := by
  have h1 : u ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have h2 : u⁻¹ ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d := by
    rw [inv_pow, h1, map_inv, inv_inv]
  have i1 : IsIntegral O (u : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h1]
    exact ((d⁻¹ : (integralClosure O L)ˣ) : integralClosure O L).2
  have i2 : IsIntegral O ((u⁻¹ : Lˣ) : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h2]
    exact (d : integralClosure O L).2
  exact ⟨⟨⟨u, i1⟩, ⟨(u⁻¹ : Lˣ), i2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, Units.ext rfl⟩

/- English proof (translation)
Introduce `O K _ _ _ Δ g hg hs`. Establish `hn : (ZD Δ).Normal`. Use `⟨fun n hn x => ?_⟩` and prove the remaining obligations. Establish `: x * n * x⁻¹ = n`. Take `⟨z, hz⟩` from `Subgroup.mem_subgroupOf.1 hn`.

Rewrite using `[mul_inv_eq_iff_eq_mul]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, ← hz]`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm).eq`.

Rewrite using `[this]` and apply the resulting hypothesis. Take `⟨s, hsz, k, hk, rfl⟩` from `Subgroup.mem_sup_of_normal_left.1 hg`. Use `mul_mem ?_ hk` and prove the remaining obligations. Take `⟨z, hz⟩` from `Subgroup.mem_subgroupOf.1 hsz`. Take `⟨k₀, hk₀⟩` from `Subgroup.mem_subgroupOf.1 hk`.

Establish `hd : GeneralLinearGroup.det ((s : GL (Fin 2) (Lsq K Δ)) * (k : GL (Fin 2) (Lsq K Δ))) = 1` using `hs`. Rewrite `hd` using `[map_mul, ← hz, ← hk₀]`. Take `⟨w, hw⟩` from `scal_mem (O := O) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z) (GeneralLinearGroup.det k₀) (by`. Rewrite using `[← hd]`. Use `congr 1`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `[pow_two])`. Use `Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.scalar (Fin 2) w, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, MonoidHom.comp_apply, ← hw]`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j : 1`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply]`.
-/
theorem UpperTheory.orbitalFiber_det_eq_one :
    UpperTheory.V.Z.Sym.Glob.Fib.DetOne := by
  intro O K _ _ _ Δ g hg hs
  have hn : (ZD Δ).Normal := by
    refine ⟨fun n hn x => ?_⟩
    have : x * n * x⁻¹ = n := by
      obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hn
      rw [mul_inv_eq_iff_eq_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hz]
      apply Units.ext
      exact ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm).eq
    rwa [this]
  obtain ⟨s, hsz, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  refine mul_mem ?_ hk
  obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hsz
  obtain ⟨k₀, hk₀⟩ := Subgroup.mem_subgroupOf.1 hk
  have hd : GeneralLinearGroup.det ((s : GL (Fin 2) (Lsq K Δ)) * (k : GL (Fin 2) (Lsq K Δ))) = 1 := hs
  rw [map_mul, ← hz, ← hk₀] at hd
  obtain ⟨w, hw⟩ := scal_mem (O := O) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z)
    (GeneralLinearGroup.det k₀) (by
      rw [← hd]
      congr 1
      · apply Units.ext
        simp [pow_two])
  refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.scalar (Fin 2) w, ?_⟩
  rw [← hz, MonoidHom.comp_apply, ← hw]
  apply Units.ext
  ext i j : 1
  by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply]
