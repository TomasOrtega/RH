import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Rewrite using `[MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]`.
-/
private theorem ms_single {B X Y : Type} [CommRing B] [Group X] [Group Y] (f : X →* Y) (a : X) (c : B) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.single a c) = MonoidAlgebra.single (f a) c := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

/- English proof (translation)
Unfold `GFrame.star GFrame.starOp`. Rewrite using `[MonoidAlgebra.lift_single, MulOpposite.unop_smul]`. Simplify using `only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, MonoidAlgebra.smul_single, smul_eq_mul]`.
-/
private theorem ms_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a : F.G₀) (c : B) :
    F.star O B n (MonoidAlgebra.single a c) =
      MonoidAlgebra.single (F.conj a)⁻¹ (c * ((F.eps O B a ^ (1 - (n : ℤ)) : Bˣ) : B)) := by
  unfold GFrame.star GFrame.starOp
  rw [MonoidAlgebra.lift_single, MulOpposite.unop_smul]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, MonoidAlgebra.smul_single, smul_eq_mul]

/- English proof (translation)
Unfold `GFrame.star`. Rewrite using `[map_add, MulOpposite.unop_add]`.
-/
private theorem ms_add {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a b : MonoidAlgebra B F.G₀) :
    F.star O B n (a + b) = F.star O B n a + F.star O B n b := by
  unfold GFrame.star
  rw [map_add, MulOpposite.unop_add]

/- English proof (translation)
Unfold `GFrame.star`. Rewrite using `[map_zero, MulOpposite.unop_zero]`.
-/
private theorem ms_zero {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) : F.star O B n 0 = 0 := by
  unfold GFrame.star
  rw [map_zero, MulOpposite.unop_zero]

/- English proof (translation)
Introduce `l _ L G G' g n O _ _ B _ _`. Use `⟨fun y => ?_, fun v ψ a => ?_, fun ph U => ?_, fun ph ta U i y => ?_⟩` and prove the remaining obligations. Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => rw [ms_zero, map_zero, ms_zero]`. Consider the case `add a b ha hb => rw [ms_add, map_add, map_add, ms_add, ha, hb]`.

Consider the case `single a c`. Rewrite using `[ms_star, ms_single, ms_single, ms_star, map_inv, g.p₀_conj, g.eps_p₀]`. Unfold `GFrame.oEl`. Rewrite using `[map_list_prod, List.map_ofFn]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, map_sub, ms_single, map_one]`. Rewrite using `[show g.p₀ (G.φ v (a i)) = G'.φ v (a i) from g.p₀_φ v (a i)]`. Unfold `q1El`. Rewrite using `[map_list_prod, List.map_ofFn]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, map_sub, ms_single, map_one]`. Unfold `q2El`. Rewrite using `[map_mul, map_list_prod, List.map_ofFn]`.

Use `congr 1`. Use `congr 2`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply]`. Use `split_ifs`.

Conclude with `map_one _`. Simplify using `only [map_sub, ms_single, map_one]`. Simplify using `only [map_sub, ms_single, map_one]`.
-/
theorem UpperTheory.V.Pa.map_star :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B : Type) [CommRing B] [Algebra O B], (∀ y, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.star O B n y) = G'.frame.star O B n (MonoidAlgebra.mapDomainRingHom B g.p₀ y)) ∧ (∀ v (ψ : Fin n → L.Gv v →* Bˣ) a, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.oEl v ψ a) = G'.frame.oEl v ψ a) ∧ (∀ (ph : G.G₀) (U : Fin n → B), MonoidAlgebra.mapDomainRingHom B g.p₀ (q1El ph U) = q1El (g.p₀ ph) U) ∧ ∀ (ph ta : G.G₀) (U : Fin n → B) i y, MonoidAlgebra.mapDomainRingHom B g.p₀ (q2El ph ta U i y) = q2El (g.p₀ ph) (g.p₀ ta) U i y := by
  intro l _ L G G' g n O _ _ B _ _
  refine ⟨fun y => ?_, fun v ψ a => ?_, fun ph U => ?_, fun ph ta U i y => ?_⟩
  · induction y using MonoidAlgebra.induction_linear with
    | zero => rw [ms_zero, map_zero, ms_zero]
    | add a b ha hb => rw [ms_add, map_add, map_add, ms_add, ha, hb]
    | single a c =>
      rw [ms_star, ms_single, ms_single, ms_star, map_inv, g.p₀_conj, g.eps_p₀]
  · unfold GFrame.oEl
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one]
    rw [show g.p₀ (G.φ v (a i)) = G'.φ v (a i) from g.p₀_φ v (a i)]
  · unfold q1El
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one]
  · unfold q2El
    rw [map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2
      funext k
      simp only [Function.comp_apply]
      split_ifs
      · exact map_one _
      · simp only [map_sub, ms_single, map_one]
    · simp only [map_sub, ms_single, map_one]
