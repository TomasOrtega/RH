import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RootOfCharpoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TanCocIsBK
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BlochKatoNonpositiveWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.LiftingTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtShape
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

/- English proof (translation)
Break down `eq_or_ne b 0 with rfl | h0` into its components or cases. Simplify using the standard rewrite rules. Establish `h` using `UpperTheory.V.Base.normO l c.O b h0`. Establish `hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0`. Rewrite using `[Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff, IsDiscreteValuationRing.addVal_eq_top_iff]`.

Conclude with `fun h => h.elim hb h0`. Establish `hl : ((l : ℝ)⁻¹) < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`. Establish `h1` using `pow_lt_one₀ (by positivity) hl hv`. Rewrite `h1` using `[← h]`. Assume the negation of the conclusion as `hn`.

Conclude with `absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))`.
-/
private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  rcases eq_or_ne b 0 with rfl | h0
  · simp
  have h := UpperTheory.V.Base.normO l c.O b h0
  have hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
      IsDiscreteValuationRing.addVal_eq_top_iff]
    exact fun h => h.elim hb h0
  have hl : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have h1 := pow_lt_one₀ (by positivity) hl hv
  rw [← h] at h1
  by_contra hn
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))

/- English proof (translation)
Introduce `y hy`. Use `norm_lt_one_of_nonunit c (x y) fun hu => ?_` and prove the remaining obligations. Establish `h2 : IsUnit (y - algebraMap c.O R (x y))`. Assume the negation of the conclusion as `hn`. Establish `h3 : y - algebraMap c.O R (x y) ∈ maximalIdeal R` using `hn`.

Establish `h4 : algebraMap c.O R (x y) ∈ maximalIdeal R` using `by simpa using Ideal.sub_mem _ hy h3`. Conclude with `h4 (hu.map _)`. Establish `h5` using `h2.map x`. Rewrite `h5` using `[map_sub, AlgHom.commutes]`. Simplify using `at h5`.
-/
private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  refine norm_lt_one_of_nonunit c (x y) fun hu => ?_
  have h2 : IsUnit (y - algebraMap c.O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap c.O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap c.O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

/- English proof (translation)
Use `MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl` and prove the remaining obligations. Use `show (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R).map f = tor S (Units.map f.toMonoidHom (Ψ g))`. Rewrite using `[tor_val, tor_val, Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `congrArg Units.val (map_zpow (Units.map f.toMonoidHom) (Ψ g) (wt1 i))`.
-/
private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R).map f = tor S (Units.map f.toMonoidHom (Ψ g))
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) (Ψ g) (wt1 i))

/- English proof (translation)
Take `⟨m, rfl⟩` from `h`. Use `⟨-m, funext fun g => ?_⟩` and prove the remaining obligations. Use `show adRep r g m - m = -m - adRep r g (-m)`. Rewrite using `[map_neg]`. Normalize the expressions using the abelian group laws.
-/
private theorem coboundary_of_mem_B1 {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG 3 κ)
    (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) : ∃ X, γ = cob r X := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨-m, funext fun g => ?_⟩
  show adRep r g m - m = -m - adRep r g (-m)
  rw [map_neg]
  abel

/- English proof (translation)
Introduce `g` and use `⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩`.
-/
private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ]
    [Algebra O κ] (f : R →ₐ[O] κ) (r : Γ →* GG 3 R) : IsPush (f.comp (entAlg O r).val) r (push f r) :=
  fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩

/- English proof (translation)
Introduce `hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx`. Establish `h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ`. Establish `e1 : push (toBar x₀) S.r.hom = (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom)` using `rfl`. Rewrite using `[e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx, map_reducible_three_dim]`. Both sides reduce to the same expression.

Use `⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `pt_fixed hI.toCohInp D hM (isPt_push D hM S f hf) hU hL`. Establish `h1` using `tanCoc_isBK hI.toCohInp D hM S F (hF ▸ isLocPt_toBar x₀)`. Rewrite `h1` using `[hF, h0]`.

Rewrite using `[h0]`. Conclude with `coboundary_of_mem_B1 _ _ (bloch_kato_nonpositive_weight hI.toCohInp D j hj _ h1.1 hw h1.2)`. Establish `h1` using `tanCoc_isBK hI.toCohInp D hM S F (hF ▸ hf.1)`. Rewrite `h1` using `[hF]`. Establish `hp` using `isPt_push D hM S f hf.1`.

Establish `hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom))`. Break down `(twoPt_shape S D.gd.l_odd hM f hf).1 with h | h` into its components or cases. Conclude with `bloch_kato_type_one hI.toCohInp hI.adK D hM hp ι h (hB U S _ _ hp.mult (isPush_push f _) h)`. Conclude with `hI.rigII D hM hp ι h (hW U S _ _ (isPush_push f _) h (typeII_facts hI.toCohInp D hM hp h).1)`. Conclude with `coboundary_of_mem_B1 _ _ (hz _ h1.1 h1.2)`.
-/
theorem UpperTheory.V.Z.Kato.ptHyp_of :
    UpperTheory.V.Z.Kato.InpZ → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), Aut.AutB D ι g₁ → Aut.LemW D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    have e1 : push (toBar x₀) S.r.hom =
        (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom) := rfl
    rw [e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx, map_reducible_three_dim]
    rfl
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hI.toCohInp D hM (isPt_push D hM S f hf) hU hL
  · have h1 := tanCoc_isBK hI.toCohInp D hM S F (hF ▸ isLocPt_toBar x₀)
    rw [hF, h0] at h1
    rw [h0]
    exact coboundary_of_mem_B1 _ _ (bloch_kato_nonpositive_weight hI.toCohInp D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hI.toCohInp D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact bloch_kato_type_one hI.toCohInp hI.adK D hM hp ι h (hB U S _ _ hp.mult (isPush_push f _) h)
      · exact hI.rigII D hM hp ι h
          (hW U S _ _ (isPush_push f _) h (typeII_facts hI.toCohInp D hM hp h).1)
    exact coboundary_of_mem_B1 _ _ (hz _ h1.1 h1.2)
