import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u hL hu`. Establish `hmul : ∀ T (x y : L.B T), x ∈ I.map (algebraMap R (L.B T)) → y ∈ I.map (algebraMap R (L.B T)) → x * y = 0`. Introduce `T x y hx hy`. Establish `h` using `Ideal.mul_mem_mul hx hy`. Rewrite `h` using `[← pow_two, ← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot]`.

Conclude with `(Ideal.mem_bot).1 h`. Establish `hv : ∀ (T T' : C) (a : T ⟶ T'), ∃ v : (L.B T')ˣ, L.p T' (v : L.B T') = (u T T' a : F.obj T')`. Introduce `T T' a`. Take `⟨x, hx⟩` from `L.surj T' (u T T' a : F.obj T')`. Take `⟨y, hy⟩` from `L.surj T' (↑(u T T' a)⁻¹ : F.obj T')`.

Establish `hn : x * y - 1 ∈ I.map (algebraMap R (L.B T'))`. Rewrite using `[← L.ker T', map_sub, map_mul, map_one, hx, hy, Units.mul_inv, sub_self]`. Establish `hn2` using `hmul T' _ _ hn hn`. Conclude with `⟨⟨x, y * (1 - (x * y - 1)), by linear_combination (-1 : L.B T') * hn2, by linear_combination (-1 : L.B T') * hn2⟩, hx⟩`. Use `choose v hvp using hv`.

Establish `hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ` using `fun T ↦ exists_isSig R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)`. Use `choose σ hσ using hσ`. Establish `hbas` using `fun T ↦ sig_basic R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (σ T) (hσ T)`. Establish `hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'', α.KerQ y ∧ σ T'' y = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * ↑(v T T'' (a ≫ b))⁻¹ - 1`. Introduce `T T' T'' a b`.

Use `(hbas T'').2.2.2 _ ?_` and prove the remaining obligations. Establish `hpinv : L.p T'' ↑(v T T'' (a ≫ b))⁻¹ = ↑(u T T'' (a ≫ b))⁻¹` using `Units.eq_inv_of_mul_eq_one_left (by rw [← hvp, ← map_mul, Units.mul_inv, map_one])`. Rewrite using `[← L.ker T'', map_sub, map_mul, map_mul, map_one, L.nat, hvp, hvp, hpinv, ← hu a b, Units.mul_inv, sub_self]`. Use `choose z hzK hzσ using hz`. Establish `heq : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'')`.

Introduce `T T' T'' a b`. Rewrite using `[hzσ, add_sub_cancel, mul_assoc _ _ (v T T'' (a ≫ b) : L.B T''), Units.inv_mul, _root_.mul_one]`. Establish `hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F)`. Introduce `T T' T'' T''' a b c`. Use `haveI := L.smooth T'''`.

Use `haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _`. Establish `nat` using `sig_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''') (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')`. Establish `em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y` using `fun _ ↦ rfl`. Rewrite using `[← sub_eq_zero]`. Apply `sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''') (σ T''') (hσ T''')` to reduce the goal to its premises.

Establish `k1` using `nat.2 _ (hzK T T' T'' a b)`. Establish `k2` using `hzK T T'' T''' (a ≫ b) c`. Establish `k3` using `hzK T T' T''' a (b ≫ c)`. Establish `k4` using `hzK T' T'' T''' b c`. Unfold `Aug.KerQ at k1 k2 k3 k4 ⊢`.

Rewrite using `[em]`. Simplify using `only [map_sub, map_add, k1, k2, k3, k4, sub_self, add_zero]`. Establish `m1 : L.ρ c (σ T'' (z T T' T'' a b)) ∈ I.map (algebraMap R (L.B T'''))`. Rewrite using `[nat.1]`. Conclude with `(hbas T''').1 _`.

Establish `m2` using `(hbas T''').1 (z T T'' T''' (a ≫ b) c)`. Establish `m3` using `(hbas T''').1 (z T T' T''' a (b ≫ c))`. Establish `m4` using `(hbas T''').1 (z T' T'' T''' b c)`. Establish `h12` using `hmul T''' _ _ m1 m2`. Establish `h43` using `hmul T''' _ _ m4 m3`.

Establish `hA` using `congrArg (L.ρ c) (heq T T' T'' a b)`. Rewrite `hA` using `[map_mul, map_mul, map_add, map_one]`. Establish `hB` using `heq T T'' T''' (a ≫ b) c`. Establish `hC` using `heq T T' T''' a (b ≫ c)`. Establish `hD` using `heq T' T'' T''' b c`.

Establish `hF` using `hL b c (v T T' a : L.B T')`. Rewrite `hB` using `[Category.assoc]`. Rewrite using `[em, map_sub, map_add, map_add, ← nat.1]`. Use `set E1 := L.ρ c (σ T'' (z T T' T'' a b))`. Use `set E2 := σ T''' (z T T'' T''' (a ≫ b) c)`.

Use `set E3 := σ T''' (z T T' T''' a (b ≫ c))`. Use `set E4 := σ T''' (z T' T'' T''' b c)`. Use `set V := v T T''' (a ≫ b ≫ c)`. Establish `hVW : (V : L.B T''') * ↑V⁻¹ = 1` using `Units.mul_inv V`. Establish `key1 : (1 + E1) * (1 + E2) * (V : L.B T''') = (1 + E4) * (1 + E3) * (V : L.B T''')`.

Take the linear combination `(-(1 + E1)) * hB - (v T'' T''' c : L.B T''') * hA + (1 + E4) * hC + L.ρ (b ≫ c) (v T T' a : L.B T') * hD - L.ρ c (v T' T'' b : L.B T'') * (v T'' T''' c : L.B T''') * hF`. Establish `key2 : (1 + E1) * (1 + E2) = (1 + E4) * (1 + E3)`. Take the linear combination `(↑V⁻¹ : L.B T''') * key1 - ((1 + E1) * (1 + E2) - (1 + E4) * (1 + E3)) * hVW`. Take the linear combination `key2 - h12 + h43`. Use `⟨H2.mk _ ⟨_, hZ⟩, v, σ, ⟨_, hZ⟩, hvp, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, heq T T' T'' a b⟩⟩` and prove the remaining obligations.
-/
theorem exists_isObU : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), L.IsFun → UCoc F u → ∃ c, IsObU L α u c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u hL hu
  have hmul : ∀ T (x y : L.B T), x ∈ I.map (algebraMap R (L.B T)) → y ∈ I.map (algebraMap R (L.B T)) →
      x * y = 0 := by
    intro T x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    rw [← pow_two, ← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
    exact (Ideal.mem_bot).1 h
  have hv : ∀ (T T' : C) (a : T ⟶ T'), ∃ v : (L.B T')ˣ, L.p T' (v : L.B T') = (u T T' a : F.obj T') := by
    intro T T' a
    obtain ⟨x, hx⟩ := L.surj T' (u T T' a : F.obj T')
    obtain ⟨y, hy⟩ := L.surj T' (↑(u T T' a)⁻¹ : F.obj T')
    have hn : x * y - 1 ∈ I.map (algebraMap R (L.B T')) := by
      rw [← L.ker T', map_sub, map_mul, map_one, hx, hy, Units.mul_inv, sub_self]
    have hn2 := hmul T' _ _ hn hn
    exact ⟨⟨x, y * (1 - (x * y - 1)), by linear_combination (-1 : L.B T') * hn2,
      by linear_combination (-1 : L.B T') * hn2⟩, hx⟩
  choose v hvp using hv
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    exists_isSig R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hbas := fun T ↦ sig_basic R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T)
    (L.ker T) (σ T) (hσ T)
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * ↑(v T T'' (a ≫ b))⁻¹ - 1 := by
    intro T T' T'' a b
    refine (hbas T'').2.2.2 _ ?_
    have hpinv : L.p T'' ↑(v T T'' (a ≫ b))⁻¹ = ↑(u T T'' (a ≫ b))⁻¹ :=
      Units.eq_inv_of_mul_eq_one_left (by rw [← hvp, ← map_mul, Units.mul_inv, map_one])
    rw [← L.ker T'', map_sub, map_mul, map_mul, map_one, L.nat, hvp, hvp, hpinv, ← hu a b, Units.mul_inv, sub_self]
  choose z hzK hzσ using hz
  have heq : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''),
      L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'') := by
    intro T T' T'' a b
    rw [hzσ, add_sub_cancel, mul_assoc _ _ (v T T'' (a ≫ b) : L.B T''), Units.inv_mul, _root_.mul_one]
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := sig_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add, k1, k2, k3, k4, sub_self, add_zero]
    · have m1 : L.ρ c (σ T'' (z T T' T'' a b)) ∈ I.map (algebraMap R (L.B T''')) := by
        rw [nat.1]; exact (hbas T''').1 _
      have m2 := (hbas T''').1 (z T T'' T''' (a ≫ b) c)
      have m3 := (hbas T''').1 (z T T' T''' a (b ≫ c))
      have m4 := (hbas T''').1 (z T' T'' T''' b c)
      have h12 := hmul T''' _ _ m1 m2
      have h43 := hmul T''' _ _ m4 m3
      have hA := congrArg (L.ρ c) (heq T T' T'' a b)
      rw [map_mul, map_mul, map_add, map_one] at hA
      have hB := heq T T'' T''' (a ≫ b) c
      have hC := heq T T' T''' a (b ≫ c)
      have hD := heq T' T'' T''' b c
      have hF := hL b c (v T T' a : L.B T')
      rw [Category.assoc] at hB
      rw [em, map_sub, map_add, map_add, ← nat.1]
      set E1 := L.ρ c (σ T'' (z T T' T'' a b))
      set E2 := σ T''' (z T T'' T''' (a ≫ b) c)
      set E3 := σ T''' (z T T' T''' a (b ≫ c))
      set E4 := σ T''' (z T' T'' T''' b c)
      set V := v T T''' (a ≫ b ≫ c)
      have hVW : (V : L.B T''') * ↑V⁻¹ = 1 := Units.mul_inv V
      have key1 : (1 + E1) * (1 + E2) * (V : L.B T''') = (1 + E4) * (1 + E3) * (V : L.B T''') := by
        linear_combination (-(1 + E1)) * hB - (v T'' T''' c : L.B T''') * hA + (1 + E4) * hC
          + L.ρ (b ≫ c) (v T T' a : L.B T') * hD
          - L.ρ c (v T' T'' b : L.B T'') * (v T'' T''' c : L.B T''') * hF
      have key2 : (1 + E1) * (1 + E2) = (1 + E4) * (1 + E3) := by
        linear_combination (↑V⁻¹ : L.B T''') * key1 - ((1 + E1) * (1 + E2) - (1 + E4) * (1 + E3)) * hVW
      linear_combination key2 - h12 + h43
  refine ⟨H2.mk _ ⟨_, hZ⟩, v, σ, ⟨_, hZ⟩, hvp, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, heq T T' T'' a b⟩⟩

end GlobalTheory.LBObs
