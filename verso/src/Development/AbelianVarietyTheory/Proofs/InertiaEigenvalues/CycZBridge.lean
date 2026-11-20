import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostFieldImageMemUnramifiedAdjoinRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCycZEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFixAlt
import Development.AutomorphicArithmetic.CyclotomicBounds.FactorizationConductorLeLocalLevel

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.EpsInertia

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

/- English proof (translation)
Establish `hc : Continuous σ` using `(AddMonoidHomClass.isometry_of_norm σ fun x => (spectralNorm_eq_of_equiv σ x).symm).continuous`. Introduce and unpack `⟨x, hx⟩`. Establish `hcl : closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ {y | σ y = y}` using `closure_minimal (by rintro _ ⟨y, rfl⟩; exact h y) (isClosed_eq hc continuous_id)`. Conclude with `hcl (Bw.j_dense hx)`.
-/
theorem mem_GK (σ : GQ l) (h : ∀ x : E, σ (Bw.j (algebraMap E Ω x)) = Bw.j (algebraMap E Ω x)) :
    σ ∈ GK Bw.Kw := by
  have hc : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun x => (spectralNorm_eq_of_equiv σ x).symm).continuous
  rintro ⟨x, hx⟩
  have hcl : closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ {y | σ y = y} :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact h y) (isClosed_eq hc continuous_id)
  exact hcl (Bw.j_dense hx)

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : CharZero Ω := Bw.j.charZero`. Use `haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Use `Units.ext (PadicInt.ext_of_toZModPow.1 fun m => ?_)` and prove the remaining obligations. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩`.

Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)`. Establish `hζ'` using `hζ.map_of_injective Bw.j.injective`. Establish `ha : (g : Ω ≃ₐ[E] Ω) ζ = ζ ^ (((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω (g : Ω ≃ₐ[E] Ω)) ζ hζ.pow_eq_one`. Establish `hb : ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) (Bw.j ζ) = Bw.j ζ ^ (((cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) ((Bw.e g : ↥(GK Bw.Kw)) : GQ l)) _ hζ'.pow_eq_one`. Rewrite `hb` using `[Bw.e_comm, ha, map_pow]`.

Conclude with `ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)`.
-/
theorem cycZ_bridge [IsAlgClosed Ω] (g : ↥Gw) :
    cycZ E Ω l (g : Ω ≃ₐ[E] Ω) = cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) := by
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := Bw.j.charZero
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.1 fun m => ?_)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have hζ' := hζ.map_of_injective Bw.j.injective
  have ha : (g : Ω ≃ₐ[E] Ω) ζ =
      ζ ^ (((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω (g : Ω ≃ₐ[E] Ω)) ζ hζ.pow_eq_one
  have hb : ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) (Bw.j ζ) = Bw.j ζ ^
      (((cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l
      (MulSemiringAction.toRingAut (GQ l) (Om l) ((Bw.e g : ↥(GK Bw.Kw)) : GQ l)) _ hζ'.pow_eq_one
  rw [Bw.e_comm, ha, map_pow] at hb
  exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)

end Bridge

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hb : σ y = y ^ (((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow s).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) _ hy`. Establish `h0 : ((l : ZMod (l ^ s))) ^ s = 0` using `by rw [← Nat.cast_pow, ZMod.natCast_self]`. Rewrite `hb` using `[h, map_add, map_one, map_mul, map_pow, map_natCast, h0, zero_mul, add_zero, ZMod.val_one_eq_one_mod]`.

Rewrite using `[hb, ← pow_eq_pow_mod 1 hy, pow_one]`.
-/
theorem fix_roots {l : ℕ} [Fact l.Prime] (σ : GQ l) (s : ℕ) (z : ℤ_[l])
    (h : ((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * z) (y : Om l)
    (hy : y ^ l ^ s = 1) : σ y = y := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hb : σ y = y ^ (((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow s).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) _ hy
  have h0 : ((l : ZMod (l ^ s))) ^ s = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [h, map_add, map_one, map_mul, map_pow, map_natCast, h0, zero_mul, add_zero, ZMod.val_one_eq_one_mod] at hb
  rw [hb, ← pow_eq_pow_mod 1 hy, pow_one]

/- English proof (translation)
Introduce `D i w hw z`. Use `haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E`. Establish `hs : D.nd.s0 i ≠ 0`. Use `UpperTheory.KStar.S0.one_le_localLevel D.nd i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hu : IsUnit (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * z)`. Rewrite using `[← sub_neg_eq_add]`. Use `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h => ?_` and prove the remaining obligations. Establish `h1` using `(isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h))`. Conclude with `PadicInt.irreducible_p.not_isUnit h1`.

Take `⟨u, hu⟩` from `hu`. Take `⟨σ, hσK, hσu⟩` from `GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u`. Establish `hσ : σ ∈ GK (D.nbr i w hw).Kw`. Use `mem_GK _ σ fun x => ?_` and prove the remaining obligations. Establish `hle : MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} ≤ IntermediateField.fixedField (Subgroup.zpowers σ)`.

Establish `hm : ∀ y, σ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ)` using `fun y hy => by`. Introduce and unpack `⟨_, k, rfl⟩`. Conclude with `(MulAction.stabilizer (GQ (D.nd.l i)) y).zpow_mem hy k`. Use `sup_le (fun y hy => hm y (hσK y hy)) (IntermediateField.adjoin_le_iff.2 fun y hy => hm y ?_)` and prove the remaining obligations. Conclude with `fix_roots σ _ z (by rw [hσu, hu]) y hy`.

Conclude with `hle (GlobalTheory.T.hostField_image_mem_unramified_adjoin_rootsOfUnity D i w hw x) ⟨σ, Subgroup.mem_zpowers σ⟩`. Use `set g := (D.nbr i w hw).e.symm ⟨σ, hσ⟩ with hg`. Establish `he : (((D.nbr i w hw).e g : ↥(GK (D.nbr i w hw).Kw)) : GQ (D.nd.l i)) = σ`. Rewrite using `[hg, MulEquiv.apply_symm_apply]`. Use `⟨g.1, ⟨g.2, fun x hx => ?_⟩, by rw [cycZ_bridge (D.nbr i w hw) g, he, hσu, hu]⟩` and prove the remaining obligations.

Establish `h1` using `GlobalTheory.UnramInertia.norm_sub_lt_one_of_fix _ σ hσK _ ((D.nbr_ind i w hw x).1 (((D.nd.plOm.1 w).valuation_le_one_iff x).1 hx))`. Rewrite `h1` using `[← he, (D.nbr i w hw).e_comm, ← map_sub]`. Use `set y := g.1 x - x`. Distinguish the cases in `hy : y = 0`. Rewrite using `[hy, map_zero]`.

Conclude with `zero_lt_one`. Establish `hj : 0 < ‖(D.nbr i w hw).j y‖` using `norm_pos_iff.2 ((map_ne_zero _).2 hy)`. Establish `h` using `D.nbr_ind i w hw y⁻¹`. Rewrite `h` using `[← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hy))]`. Rewrite using `[← not_le, h, not_le]`.

Conclude with `h1`.
-/
theorem epsAll : ∀ (D : D7) (i : D.nd.Loc), EpsAll D i := by
  intro D i w hw z
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have hs : D.nd.s0 i ≠ 0 := by
    have := UpperTheory.KStar.S0.one_le_localLevel D.nd i
    omega
  have hu : IsUnit (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * z) := by
    rw [← sub_neg_eq_add]
    refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h => ?_
    have h1 := (isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h))
    exact PadicInt.irreducible_p.not_isUnit h1
  obtain ⟨u, hu⟩ := hu
  obtain ⟨σ, hσK, hσu⟩ := GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u
  have hσ : σ ∈ GK (D.nbr i w hw).Kw := by
    refine mem_GK _ σ fun x => ?_
    have hle : MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i]
        {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      have hm : ∀ y, σ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := fun y hy => by
        rintro ⟨_, k, rfl⟩
        exact (MulAction.stabilizer (GQ (D.nd.l i)) y).zpow_mem hy k
      refine sup_le (fun y hy => hm y (hσK y hy)) (IntermediateField.adjoin_le_iff.2 fun y hy => hm y ?_)
      exact fix_roots σ _ z (by rw [hσu, hu]) y hy
    exact hle (GlobalTheory.T.hostField_image_mem_unramified_adjoin_rootsOfUnity D i w hw x) ⟨σ, Subgroup.mem_zpowers σ⟩
  set g := (D.nbr i w hw).e.symm ⟨σ, hσ⟩ with hg
  have he : (((D.nbr i w hw).e g : ↥(GK (D.nbr i w hw).Kw)) : GQ (D.nd.l i)) = σ := by
    rw [hg, MulEquiv.apply_symm_apply]
  refine ⟨g.1, ⟨g.2, fun x hx => ?_⟩, by rw [cycZ_bridge (D.nbr i w hw) g, he, hσu, hu]⟩
  have h1 := GlobalTheory.UnramInertia.norm_sub_lt_one_of_fix _ σ hσK _
    ((D.nbr_ind i w hw x).1 (((D.nd.plOm.1 w).valuation_le_one_iff x).1 hx))
  rw [← he, (D.nbr i w hw).e_comm, ← map_sub] at h1
  set y := g.1 x - x
  by_cases hy : y = 0
  · rw [hy, map_zero]; exact zero_lt_one
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hy))] at h
  rw [← not_le, h, not_le]
  exact h1

end GlobalTheory.EpsInertia

end
