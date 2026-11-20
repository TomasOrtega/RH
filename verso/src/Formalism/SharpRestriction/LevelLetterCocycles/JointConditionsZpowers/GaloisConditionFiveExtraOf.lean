import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal

open NumberField IsDedekindDomain

/- English proof (translation)
Introduce `g k`. Take `⟨f, hf⟩` from `((h32 i).2.2 r hr).1 g k`. Establish `e : (fun x : D.nd.X i => ((Formalism.MainNotions.N.rO D.nd i r x g).charpolyRev).coeff k) = (f : D.nd.X i → D.nd.O i)` using `funext fun x => (hf x).symm`. Rewrite using `[e]`. Conclude with `f.2`.
-/
theorem galois_condition_one_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : Formalism.MainNotions.SumRepresentations.Conclusion41 D) (hr : Formalism.MainNotions.N.GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
  intro g k
  obtain ⟨f, hf⟩ := ((h32 i).2.2 r hr).1 g k
  have e : (fun x : D.nd.X i => ((Formalism.MainNotions.N.rO D.nd i r x g).charpolyRev).coeff k) =
      (f : D.nd.X i → D.nd.O i) := funext fun x => (hf x).symm
  rw [e]
  exact f.2

/- English proof (translation)
Introduce `x v hl hS hQ g hg`. Conclude with `((h32 i).2.2 r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg`.
-/
theorem galois_condition_four_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : Formalism.MainNotions.SumRepresentations.Conclusion41 D) (hr : Formalism.MainNotions.N.GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
  intro x v hl hS hQ g hg
  exact ((h32 i).2.2 r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg

/- English proof (translation)
Introduce `x hx`. Conclude with `(D.Z_tie i x).2 (h32 i hg r hr x hx).1`.
-/
theorem galois_condition_six_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : Formalism.MainNotions.SumRepresentations.ConclusionG6 D) (hg : Formalism.MainNotions.N.HG D.nd D.naut i) (hr : Formalism.MainNotions.N.GoodR D.nd i r) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG6 (D := D) i r := by
  intro x hx
  exact (D.Z_tie i x).2 (h32 i hg r hr x hx).1

/- English proof (translation)
Introduce `w hw`. Take `⟨ha, hb, -⟩` from `h32 i hg r hr w hw (D.nd.SQ_l i w hw)`. Conclude with `⟨ha, fun hk hS _ => hb hk hS⟩`.
-/
theorem galois_condition_five_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : Formalism.MainNotions.SumRepresentations.ConclusionG5 D) (hg : Formalism.MainNotions.N.HG D.nd D.naut i) (hr : Formalism.MainNotions.N.GoodR D.nd i r) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG5 (D := D) i r := by
  intro w hw
  obtain ⟨ha, hb, -⟩ := h32 i hg r hr w hw (D.nd.SQ_l i w hw)
  exact ⟨ha, fun hk hS _ => hb hk hS⟩

def LitGoodO : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL)

/- English proof (translation)
Introduce `w hw C`. Conclude with `⟨Formalism.MainNotions.TruncatedSeriesCountingIdentities.tate_duality_h2_of_all_coefficients _ _ _ (hT _ _) (hO _ _), hDim _ _ _, fun _ => Formalism.MainNotions.TruncatedSeriesCountingIdentities.bkBAt_of_core _ _ _ (h55 _ _).2.2.2.1 (hO _ _)⟩`.
-/
theorem bloch_kato_annihilators_of (D : D7) (i : D.nd.Loc) (h55 : Formalism.MainNotions.LocalSituation.Conclusion5 D) (hT : Formalism.MainNotions.LocalSituation.adm3 D)
    (hDim : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm8 D) (hO : LitGoodO) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admBK (D := D) i := by
  intro w hw C
  exact ⟨Formalism.MainNotions.TruncatedSeriesCountingIdentities.tate_duality_h2_of_all_coefficients _ _ _ (hT _ _) (hO _ _), hDim _ _ _,
    fun _ => Formalism.MainNotions.TruncatedSeriesCountingIdentities.bkBAt_of_core _ _ _ (h55 _ _).2.2.2.1 (hO _ _)⟩

/- English proof (translation)
Apply `IsTopologicalAddGroup.t2Space_of_zero_sep` to reduce the goal to its premises. Introduce `x hx`. Establish `hH : IsHausdorff (IsLocalRing.maximalIdeal (D.nd.O i)) (D.nd.O i)` using `(D.nd.O_complete i).toIsHausdorff`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Apply `hx` to reduce the goal to its premises. Apply `hH.haus' x` to reduce the goal to its premises. Introduce `n`. Establish `hU : ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal _) : Set (D.nd.O i)) ∈ nhds 0` using `((isAdic_iff.mp (D.nd.O_adic i)).1 n).mem_nhds (Ideal.zero_mem _)`. Use `hcon _ hU` as an intermediate fact.

Rewrite using `[SModEq.zero]`. Simplify using `using this`.
-/
theorem integers_t2Space (D : D7) (i : D.nd.Loc) : T2Space (D.nd.O i) := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  have hH : IsHausdorff (IsLocalRing.maximalIdeal (D.nd.O i)) (D.nd.O i) :=
    (D.nd.O_complete i).toIsHausdorff
  by_contra hcon
  push Not at hcon
  apply hx
  apply hH.haus' x
  intro n
  have hU : ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal _) : Set (D.nd.O i)) ∈ nhds 0 :=
    ((isAdic_iff.mp (D.nd.O_adic i)).1 n).mem_nhds (Ideal.zero_mem _)
  have := hcon _ hU
  rw [SModEq.zero]
  simpa using this

/- English proof (translation)
Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)` and prove the remaining obligations. Rewrite using `[cycZ_toZModPow_eq (v := v) hv (D.nd.plOm.2 v) (q := 1) (fun x hx => by simpa using hg.2 x hx) n]`. Simplify using the standard rewrite rules.
-/
theorem cycZ_one_of_Ine (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∉ placesOver D.host.E (D.nd.l i)) (g : GE D.nd)
    (hg : g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq (v := v) hv (D.nd.plOm.2 v) (q := 1) (fun x hx => by simpa using hg.2 x hx) n]
  simp

/- English proof (translation)
Use `integers_t2Space D i` as an intermediate fact. Use `set ζ := D.nd.chi i 1 (D.nd.gam0 i v) with hζ`. Establish `hS : ((Subgroup.zpowers ζ : Subgroup (D.nd.O i)ˣ) : Set (D.nd.O i)ˣ).Finite` using `finite_zpowers.mpr hfin`. Establish `hcl : IsClosed (((Subgroup.zpowers ζ).comap (D.nd.chi i 1) : Subgroup (GE D.nd)) : Set (GE D.nd))`. Establish `e : (((Subgroup.zpowers ζ).comap (D.nd.chi i 1) : Subgroup (GE D.nd)) : Set (GE D.nd)) = ⋃ u ∈ ((Subgroup.zpowers ζ : Subgroup (D.nd.O i)ˣ) : Set (D.nd.O i)ˣ), {g | ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) = (u : D.nd.O i)}`.

Use extensionality with `g`. Simplify using `only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨_, h, rfl⟩`.

Introduce and unpack `⟨u, hu, h⟩`. Rewrite using `[Units.ext h]` and apply the resulting hypothesis. Rewrite using `[e]`. Conclude with `hS.isClosed_biUnion fun u _ => isClosed_eq (D.nd.chi_cont i 1) continuous_const`. Establish `hle : Subgroup.closure (insert (D.nd.gam0 i v) (wildSet D.nd (D.nd.plOm.1 v))) ≤ (Subgroup.zpowers ζ).comap (D.nd.chi i 1)`.

Rewrite using `[Subgroup.closure_le]`. Introduce `σ hσ`. Break down `hσ with rfl | hσ` into its components or cases. Conclude with `Subgroup.mem_zpowers ζ`. Use `show D.nd.chi i 1 σ ∈ Subgroup.zpowers ζ`.

Rewrite using `[htame σ hσ]`. Conclude with `Subgroup.one_mem _`. Conclude with `closure_minimal hle hcl (hgen hg)`.
-/
theorem inertia_character_mem_zpowers (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hgen : TameGen D.nd (D.nd.plOm.1 v) (D.nd.gam0 i v))
    (htame : ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), D.nd.chi i 1 σ = 1)
    (hfin : IsOfFinOrder (D.nd.chi i 1 (D.nd.gam0 i v))) (g : GE D.nd)
    (hg : g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    D.nd.chi i 1 g ∈ Subgroup.zpowers (D.nd.chi i 1 (D.nd.gam0 i v)) := by
  have := integers_t2Space D i
  set ζ := D.nd.chi i 1 (D.nd.gam0 i v) with hζ
  have hS : ((Subgroup.zpowers ζ : Subgroup (D.nd.O i)ˣ) : Set (D.nd.O i)ˣ).Finite :=
    finite_zpowers.mpr hfin
  have hcl : IsClosed (((Subgroup.zpowers ζ).comap (D.nd.chi i 1) : Subgroup (GE D.nd)) : Set (GE D.nd)) := by
    have e : (((Subgroup.zpowers ζ).comap (D.nd.chi i 1) : Subgroup (GE D.nd)) : Set (GE D.nd)) =
        ⋃ u ∈ ((Subgroup.zpowers ζ : Subgroup (D.nd.O i)ˣ) : Set (D.nd.O i)ˣ),
          {g | ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) = (u : D.nd.O i)} := by
      ext g
      simp only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, Set.mem_iUnion,
        Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro h
        exact ⟨_, h, rfl⟩
      · rintro ⟨u, hu, h⟩
        rwa [Units.ext h]
    rw [e]
    exact hS.isClosed_biUnion fun u _ => isClosed_eq (D.nd.chi_cont i 1) continuous_const
  have hle : Subgroup.closure (insert (D.nd.gam0 i v) (wildSet D.nd (D.nd.plOm.1 v))) ≤
      (Subgroup.zpowers ζ).comap (D.nd.chi i 1) := by
    rw [Subgroup.closure_le]
    intro σ hσ
    rcases hσ with rfl | hσ
    · exact Subgroup.mem_zpowers ζ
    · show D.nd.chi i 1 σ ∈ Subgroup.zpowers ζ
      rw [htame σ hσ]
      exact Subgroup.one_mem _
  exact closure_minimal hle hcl (hgen hg)

def TameCharacterConditions (D : D7) (i : D.nd.Loc) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 D.host.E),
    (v ∈ D.nd.Q i ∨ (v ∈ D.nd.S i ∧ (v ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')))) →
    ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), D.nd.chi i 1 σ = 1) ∧
  Formalism.MainNotions.SumRepresentations.At.Del D.nd i

/- English proof (translation)
Introduce `v hv`. Establish `hgen : TameGen D.nd (D.nd.plOm.1 v) (D.nd.gam0 i v)` using `(D.nd.restN_tameGenerator_generates i v hv).2`. Establish `hl` using `D.nd.SQ_l i v hv`. Use `⟨hgen, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc' g hg`.

Rewrite `hc'` using `[Finset.mem_Icc]`. Rewrite using `[D.nd.chi_def i c hc'.1 hc'.2]`. Simplify using `[cycZ_one_of_Ine D i v hl g hg]`. Introduce `hQ hz`. Take `⟨g, hg, hne⟩` from `D.nd.chi_ram_Q i v hQ`.

Establish `h1 : D.nd.chi i 1 (D.nd.gam0 i v) = 1` using `Units.ext hz`. Use `inertia_character_mem_zpowers D i v hgen (hc.1 v (Or.inl hQ)) (by rw [h1]; exact IsOfFinOrder.one) g hg` as an intermediate fact. Rewrite `this` using `[h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]`. Conclude with `hne this`. Introduce `hS hp`.

Establish `hov : v ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)`. Break down `hp with hp | ⟨h1, hp⟩` into its components or cases. Establish `: D.nd.l i ≠ D.host.pde` using `fun h => hl (h ▸ hp)`. Rewrite using `[if_neg this]` and apply the resulting hypothesis. Rewrite using `[if_pos h1]` and apply the resulting hypothesis.

Establish `hcard` using `hc.2 v hS hov`. Use `set ζ := D.nd.chi i 1 (D.nd.gam0 i v) with hζ`. Establish `hmem : ζ ∈ (Ine (F` using `D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1) := ⟨_, D.nd.locNd_chebotarevPlace_mem i v, rfl⟩`. Establish `: Finite ↥((Ine (F` using `D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)`. Establish `hfin : IsOfFinOrder ζ`.

Use `isOfFinOrder_of_finite (⟨ζ, hmem⟩ : ↥((Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1)))` as an intermediate fact. Conclude with `(Subgroup.subtype _).isOfFinOrder this`. Establish `heq : (Ine (F` using `D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1) = Subgroup.zpowers ζ := by`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Conclude with `inertia_character_mem_zpowers D i v hgen (hc.1 v (Or.inr ⟨hS, hp⟩)) hfin g hg`. Rewrite using `[Subgroup.zpowers_le]`. Conclude with `hmem`. Establish `hord : orderOf ζ = 15`. Rewrite using `[← Nat.card_zpowers, ← heq, hcard]`.

Establish `hprim : IsPrimitiveRoot ((ζ : (D.nd.O i)ˣ) : D.nd.O i) 15`. Rewrite using `[IsPrimitiveRoot.coe_units_iff, ← hord]`. Conclude with `IsPrimitiveRoot.orderOf ζ`. Establish `hroot : (Polynomial.cyclotomic 15 (D.nd.O i)).eval ((ζ : (D.nd.O i)ˣ) : D.nd.O i) = 0` using `hprim.isRoot_cyclotomic (by norm_num)`. Establish `h1 : (Polynomial.cyclotomic 15 (D.nd.O i)).eval 1 = 1`.

Apply `Polynomial.eval_one_cyclotomic_not_prime_pow` to reduce the goal to its premises. Introduce `p hp k hk`. Establish `h3 : 3 ∣ p ^ k` using `by rw [hk]; norm_num`. Establish `h5 : 5 ∣ p ^ k` using `by rw [hk]; norm_num`. Establish `e3` using `(Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)`.

Establish `e5` using `(Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp (Nat.prime_five.dvd_of_dvd_pow h5)`. Use linear arithmetic over natural numbers and integers. Establish `hd` using `Polynomial.sub_dvd_eval_sub ((ζ : (D.nd.O i)ˣ) : D.nd.O i) 1 (Polynomial.cyclotomic 15 (D.nd.O i))`. Rewrite `hd` using `[hroot, h1, zero_sub]`. Conclude with `isUnit_of_dvd_unit hd (isUnit_one.neg)`.
-/
theorem galois_condition_five_extra_of (D : D7) (i : D.nd.Loc) (hc : TameCharacterConditions D i) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  intro v hv
  have hgen : TameGen D.nd (D.nd.plOm.1 v) (D.nd.gam0 i v) := (D.nd.restN_tameGenerator_generates i v hv).2
  have hl := D.nd.SQ_l i v hv
  refine ⟨hgen, ?_, ?_, ?_⟩
  · intro c hc' g hg
    rw [Finset.mem_Icc] at hc'
    rw [D.nd.chi_def i c hc'.1 hc'.2]
    simp [cycZ_one_of_Ine D i v hl g hg]
  · intro hQ hz
    obtain ⟨g, hg, hne⟩ := D.nd.chi_ram_Q i v hQ
    have h1 : D.nd.chi i 1 (D.nd.gam0 i v) = 1 := Units.ext hz
    have := inertia_character_mem_zpowers D i v hgen (hc.1 v (Or.inl hQ)) (by rw [h1]; exact IsOfFinOrder.one) g hg
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    exact hne this
  · intro hS hp
    have hov : v ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) := by
      rcases hp with hp | ⟨h1, hp⟩
      · have : D.nd.l i ≠ D.host.pde := fun h => hl (h ▸ hp)
        rwa [if_neg this]
      · rwa [if_pos h1]
    have hcard := hc.2 v hS hov
    set ζ := D.nd.chi i 1 (D.nd.gam0 i v) with hζ
    have hmem : ζ ∈ (Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1) :=
      ⟨_, D.nd.locNd_chebotarevPlace_mem i v, rfl⟩
    have : Finite ↥((Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hfin : IsOfFinOrder ζ := by
      have := isOfFinOrder_of_finite (⟨ζ, hmem⟩ : ↥((Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1)))
      exact (Subgroup.subtype _).isOfFinOrder this
    have heq : (Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1) = Subgroup.zpowers ζ := by
      apply le_antisymm
      · rintro _ ⟨g, hg, rfl⟩
        exact inertia_character_mem_zpowers D i v hgen (hc.1 v (Or.inr ⟨hS, hp⟩)) hfin g hg
      · rw [Subgroup.zpowers_le]
        exact hmem
    have hord : orderOf ζ = 15 := by
      rw [← Nat.card_zpowers, ← heq, hcard]
    have hprim : IsPrimitiveRoot ((ζ : (D.nd.O i)ˣ) : D.nd.O i) 15 := by
      rw [IsPrimitiveRoot.coe_units_iff, ← hord]
      exact IsPrimitiveRoot.orderOf ζ
    have hroot : (Polynomial.cyclotomic 15 (D.nd.O i)).eval ((ζ : (D.nd.O i)ˣ) : D.nd.O i) = 0 :=
      hprim.isRoot_cyclotomic (by norm_num)
    have h1 : (Polynomial.cyclotomic 15 (D.nd.O i)).eval 1 = 1 := by
      apply Polynomial.eval_one_cyclotomic_not_prime_pow
      intro p hp k hk
      have h3 : 3 ∣ p ^ k := by rw [hk]; norm_num
      have h5 : 5 ∣ p ^ k := by rw [hk]; norm_num
      have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
      have e5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp (Nat.prime_five.dvd_of_dvd_pow h5)
      omega
    have hd := Polynomial.sub_dvd_eval_sub ((ζ : (D.nd.O i)ˣ) : D.nd.O i) 1 (Polynomial.cyclotomic 15 (D.nd.O i))
    rw [hroot, h1, zero_sub] at hd
    exact isUnit_of_dvd_unit hd (isUnit_one.neg)

end Formalism.MainNotions.N
