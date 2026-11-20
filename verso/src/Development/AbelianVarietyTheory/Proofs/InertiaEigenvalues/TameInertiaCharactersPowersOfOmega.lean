import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInertiaQlIffResidueTrivialStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalRootOfUnityMulKummerRootMinpolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConjStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowFixingNormalOfNearStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixingKummerRootMovesLessStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameIner

/- English proof (translation)
The claim follows from `GlobalTheory.T.mem_inertia_Ql_iff_residue_trivial`.
-/
theorem mem_IK_iff : ∀ (l : ℕ) [Fact l.Prime] (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖(g : GQ l) x - x‖ < 1 :=
  GlobalTheory.T.mem_inertia_Ql_iff_residue_trivial

/- English proof (translation)
The claim follows from `GlobalTheory.T.aeval_rootOfUnity_mul_kummer_root_minpoly`.
-/
theorem minpoly_root : ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → ∀ (ρ ξ : Om l), ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 :=
  GlobalTheory.T.aeval_rootOfUnity_mul_kummer_root_minpoly

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_galois_fixing_maxUnramified_map_conj`.
-/
theorem exists_lift : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y :=
  GlobalTheory.T.exists_galois_fixing_maxUnramified_map_conj

/- English proof (translation)
The claim follows from `GlobalTheory.T.inertia_char_openKer_trivial_fixing_normal`.
-/
theorem exists_open_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 :=
  GlobalTheory.T.inertia_char_openKer_trivial_fixing_normal

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_prime_pow_fixing_normal_of_near`.
-/
theorem exists_pow_fix : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x :=
  GlobalTheory.T.exists_prime_pow_fixing_normal_of_near

/- English proof (translation)
The claim follows from `GlobalTheory.T.inertia_fixing_kummer_root_moves_less`.
-/
theorem near_of_fix_root : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ :=
  GlobalTheory.T.inertia_fixing_kummer_root_moves_less

variable {l : ℕ} [hl : Fact l.Prime]

open GlobalTheory.MemLoc.FrobLaws in

/- English proof (translation)
Establish `h1` using `(mem_IK_iff l g).1 hg ζ (norm_root hm hζ).le`. Establish `hgζ : ((g : GQ l) ζ) ^ m = 1` using `by rw [← map_pow, hζ, map_one]`. Set `a : OO l` to `⟨(g : GQ l) ζ, show ‖(g : GQ l) ζ‖ ≤ 1 from (norm_root hm hgζ).le⟩`. Set `b : OO l` to `⟨ζ, show ‖ζ‖ ≤ 1 from (norm_root hm hζ).le⟩`. Use `res_inj (a := a) (b := b) hm hlm (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgζ)) (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hζ)) ((res_eq_iff a b).2 h1)` as an intermediate fact.

Conclude with `congrArg Subtype.val this`.
-/
theorem fix_root (g : Gl l) (hg : g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l)) {ζ : Om l} {m : ℕ} (hm : 0 < m)
    (hlm : ¬ l ∣ m) (hζ : ζ ^ m = 1) : (g : GQ l) ζ = ζ := by
  have h1 := (mem_IK_iff l g).1 hg ζ (norm_root hm hζ).le
  have hgζ : ((g : GQ l) ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  let a : OO l := ⟨(g : GQ l) ζ, show ‖(g : GQ l) ζ‖ ≤ 1 from (norm_root hm hgζ).le⟩
  let b : OO l := ⟨ζ, show ‖ζ‖ ≤ 1 from (norm_root hm hζ).le⟩
  have := res_inj (a := a) (b := b) hm hlm (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgζ))
    (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hζ)) ((res_eq_iff a b).2 h1)
  exact congrArg Subtype.val this

open GlobalTheory.MemLoc.FrobLaws in

/- English proof (translation)
Establish `hK : ζ ∈ MaximalUnramifiedExtension l` using `IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩`. Establish `h1` using `hFr ζ hK (norm_root hm hζ).le`. Establish `hgζ : ((Fr : GQ l) ζ) ^ m = 1` using `by rw [← map_pow, hζ, map_one]`. Establish `hζl : (ζ ^ l) ^ m = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Set `a : OO l` to `⟨(Fr : GQ l) ζ, show ‖(Fr : GQ l) ζ‖ ≤ 1 from (norm_root hm hgζ).le⟩`.

Set `b : OO l` to `⟨ζ ^ l, show ‖ζ ^ l‖ ≤ 1 from (norm_root hm hζl).le⟩`. Use `res_inj (a := a) (b := b) hm hlm (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgζ)) (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hζl)) ((res_eq_iff a b).2 h1)` as an intermediate fact. Conclude with `congrArg Subtype.val this`.
-/
theorem frob_root (Fr : Gl l) (hFr : ∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Fr : GQ l) x - x ^ l‖ < 1)
    {ζ : Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (hζ : ζ ^ m = 1) : (Fr : GQ l) ζ = ζ ^ l := by
  have hK : ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩
  have h1 := hFr ζ hK (norm_root hm hζ).le
  have hgζ : ((Fr : GQ l) ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  have hζl : (ζ ^ l) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  let a : OO l := ⟨(Fr : GQ l) ζ, show ‖(Fr : GQ l) ζ‖ ≤ 1 from (norm_root hm hgζ).le⟩
  let b : OO l := ⟨ζ ^ l, show ‖ζ ^ l‖ ≤ 1 from (norm_root hm hζl).le⟩
  have := res_inj (a := a) (b := b) hm hlm (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgζ))
    (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hζl)) ((res_eq_iff a b).2 h1)
  exact congrArg Subtype.val this

open GlobalTheory.MemLoc.FrobLaws in

/- English proof (translation)
Establish `key : ∀ y : Om l, ‖y‖ < 1 → ‖(g : GQ l) y - y‖ < 1` using `fun y hy => by`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_gal]`. Conclude with `hy`.

Rewrite using `[norm_neg]`. Conclude with `hy`. Rewrite using `[mem_IK_iff]`. Introduce `x hx`. Break down `hx.lt_or_eq with h | h` into its components or cases.

Conclude with `key x h`. Take `⟨ζ, m, hm, hlm, hζ, hn⟩` from `exists_root x h`. Establish `e : (g : GQ l) x - x = (g : GQ l) (x - ζ) - (x - ζ)`. Rewrite using `[map_sub, hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `key _ hn`.
-/
theorem mem_IK_of_fix_Kur (g : Gl l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, (g : GQ l) x = x) :
    g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  have key : ∀ y : Om l, ‖y‖ < 1 → ‖(g : GQ l) y - y‖ < 1 := fun y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rw [mem_IK_iff]
  intro x hx
  rcases hx.lt_or_eq with h | h
  · exact key x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := exists_root x h
    have e : (g : GQ l) x - x = (g : GQ l) (x - ζ) - (x - ζ) := by
      rw [map_sub, hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩)]; ring
    rw [e]
    exact key _ hn

/- English proof (translation)
Take `⟨g, hgK, hgρ⟩` from `exists_lift l ρ (ζ * ρ) (minpoly_root l M hM ρ ζ hρ hζ)`. Establish `hmem : g ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l)`. Rewrite using `[GK, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `x ∈ (⊥ : IntermediateField ℚ_[l] (Om l)) at hx`.

Take `⟨c, rfl⟩` from `IntermediateField.mem_bot.1 hx`. Conclude with `g.commutes c`. Conclude with `⟨⟨g, hmem⟩, mem_IK_of_fix_Kur _ hgK, hgρ⟩`.
-/
theorem exists_inertia {M : ℕ} (hM : 0 < M) (ρ ζ : Om l) (hρ : ρ ^ M = -(l : Om l)) (hζ : ζ ^ M = 1) :
    ∃ g : Gl l, g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (g : GQ l) ρ = ζ * ρ := by
  obtain ⟨g, hgK, hgρ⟩ := exists_lift l ρ (ζ * ρ) (minpoly_root l M hM ρ ζ hρ hζ)
  have hmem : g ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change x ∈ (⊥ : IntermediateField ℚ_[l] (Om l)) at hx
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact g.commutes c
  exact ⟨⟨g, hmem⟩, mem_IK_of_fix_Kur _ hgK, hgρ⟩

/- English proof (translation)
Take `⟨F, hFn, hF⟩` from `exists_open_normal l LL χ ho`. Take `⟨M, hM, hlM, hnear⟩` from `near_of_fix_root l F`. Use `⟨M, hM, hlM, fun ρ hρ g hg => ?_⟩` and prove the remaining obligations. Establish `hres` using `(mem_IK_iff l (g : Gl l)).1 g.2`. Establish `h1` using `hnear ρ hρ _ hres hg`.

Take `⟨s, hs⟩` from `exists_pow_fix l F hFn _ h1`. Establish `h2 : χ (g ^ l ^ s) = 1` using `hF _ (fun x hx => by simpa using hs x hx)`. Establish `h3 : χ g ^ orderOf χ = 1` using `by rw [← MonoidHom.pow_apply, pow_orderOf_eq_one]; rfl`. Rewrite `h2` using `[map_pow]`. Use `pow_gcd_eq_one.2 ⟨h3, h2⟩` as an intermediate fact.

Rewrite `this` using `[Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right s hc), pow_one]`. Then use the resulting hypothesis.
-/
theorem chi_trivial (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ)
    (ho : IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)))) (hc : Nat.Coprime (orderOf χ) l) :
    ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) →
      ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), ((g : Gl l) : GQ l) ρ = ρ → χ g = 1 := by
  obtain ⟨F, hFn, hF⟩ := exists_open_normal l LL χ ho
  obtain ⟨M, hM, hlM, hnear⟩ := near_of_fix_root l F
  refine ⟨M, hM, hlM, fun ρ hρ g hg => ?_⟩
  have hres := (mem_IK_iff l (g : Gl l)).1 g.2
  have h1 := hnear ρ hρ _ hres hg
  obtain ⟨s, hs⟩ := exists_pow_fix l F hFn _ h1
  have h2 : χ (g ^ l ^ s) = 1 := hF _ (fun x hx => by simpa using hs x hx)
  have h3 : χ g ^ orderOf χ = 1 := by rw [← MonoidHom.pow_apply, pow_orderOf_eq_one]; rfl
  rw [map_pow] at h2
  have := pow_gcd_eq_one.2 ⟨h3, h2⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right s hc), pow_one] at this

end GlobalTheory.TameIner

namespace GlobalTheory.TameIner

/- English proof (translation)
Introduce `l _ a e _ _ ϖ LL _ _`. Establish `hp : l.Prime` using `Fact.out`. Take `⟨z, hz⟩` from `TameDescentExponentData.prim (K := ↥LL.1) (l := l) (e := e) (a := a)`. Establish `he0 : 0 < e` using `Nat.pos_of_ne_zero (NeZero.ne e)`. Establish `hle : ¬ l ∣ e`.

Introduce `h`. Establish `h1 : l ∣ l ^ a` using `dvd_pow_self l (NeZero.ne a)`. Rewrite `h1` using `[← TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a)]`. Conclude with `hp.not_dvd_one ((Nat.dvd_add_right h).1 h1)`. Establish `hzO : IsPrimitiveRoot ((z : ↥LL.1) : Om l) e` using `hz.map_of_injective (f := LL.1.val) LL.1.val.injective`.

Establish `hl0 : (l : Om l) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hπ0 : ϖ.seq 0 ≠ 0` using `ϖ.seq_ne_zero 0`. Establish `hroot : ∀ w : Om l, w ^ e = 1 → ∃ k < e, ((z ^ k : ↥LL.1) : Om l) = w`. Introduce `w hw`. Take `⟨k, hk, h⟩` from `hzO.eq_pow_of_pow_eq_one hw`.

Conclude with `⟨k, hk, by rw [← h]; rfl⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g _`. Establish `hw : ((g : GQ l) (ϖ.seq 0) / ϖ.seq 0) ^ e = 1`. Rewrite using `[div_pow, ← map_pow, ϖ.seq_zero, map_neg, map_natCast, div_self (neg_ne_zero.2 hl0)]`.

Take `⟨k, -, hk⟩` from `hroot _ hw`. Use `⟨z ^ k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]`.

Take `⟨g, hg, hgπ⟩` from `exists_inertia he0 (ϖ.seq 0) _ ϖ.seq_zero hzO.pow_eq_one`. Conclude with `⟨g, hg, z, hgπ.symm, hz⟩`. Introduce `χ hχo hχc`. Take `⟨M0, hM0, hlM0, hM0χ⟩` from `chi_trivial LL χ hχo hχc`. Establish `hM : 0 < M0 * e` using `Nat.mul_pos hM0 he0`.

Establish `hlM : ¬ l ∣ M0 * e` using `fun h => ((Nat.Prime.dvd_mul hp).1 h).elim hlM0 hle`. Use `haveI : NeZero (M0 * e) := ⟨hM.ne'⟩`. Take `⟨ρ, hρ⟩` from `IsAlgClosed.exists_pow_nat_eq (-(l : Om l)) hM`. Take `⟨ζ, hζ⟩ : ∃ ζ : Om l, IsPrimitiveRoot ζ (M0 * e)` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (M0 * e)`. Take `⟨σ, hσ, hσρ⟩` from `exists_inertia hM ρ ζ hρ hζ.pow_eq_one`.

Establish `hρ0 : ρ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hρ` using `[zero_pow hM.ne', eq_comm, neg_eq_zero]`. Conclude with `hl0 hρ`. Establish `hζσ : ∀ g : Gl l, g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → (g : GQ l) ζ = ζ` using `fun g hg => fix_root g hg hM hlM hζ.pow_eq_one`.

Establish `hrat : ∀ g : Gl l, ∃ j : ℕ, (g : GQ l) ρ = ζ ^ j * ρ`. Introduce `g`. Establish `h1 : ((g : GQ l) ρ / ρ) ^ (M0 * e) = 1`. Rewrite using `[div_pow, ← map_pow, hρ, map_neg, map_natCast, div_self (neg_ne_zero.2 hl0)]`. Take `⟨j, -, hj⟩` from `hζ.eq_pow_of_pow_eq_one h1`.

Conclude with `⟨j, by rw [hj]; field_simp⟩`. Establish `hσpow : ∀ j : ℕ, ((σ ^ j : Gl l) : GQ l) ρ = ζ ^ j * ρ`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`.

Consider the case `succ j ih`. Rewrite using `[pow_succ, Subgroup.coe_mul, AlgEquiv.mul_apply, hσρ, map_mul, ih, hζσ _ (Subgroup.pow_mem _ hσ j), pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Use `set σ' : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) := ⟨σ, hσ⟩ with hσ'`. Establish `hχg : ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (j : ℕ), ((g : Gl l) : GQ l) ρ = ζ ^ j * ρ → χ g = χ σ' ^ j`.

Introduce `g j hj`. Establish `hfix : ((((σ' ^ j)⁻¹ * g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) : GQ l) ρ = ρ`. Establish `h2` using `hσpow j`. Establish `h3 : ((((σ' ^ j)⁻¹ * g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) : GQ l) = ((σ ^ j : Gl l) : GQ l)⁻¹ * ((g : Gl l) : GQ l)`. Simplify using `[σ']`.

Rewrite using `[h3, AlgEquiv.mul_apply, hj, ← h2]`. Conclude with `AlgEquiv.symm_apply_apply _ ρ`. Establish `h1 : χ ((σ' ^ j)⁻¹ * g) = 1`. Use `hM0χ (ρ ^ e) (by rw [← pow_mul, mul_comm e M0]; exact hρ) _ ?_` and prove the remaining obligations. Rewrite using `[map_pow, hfix]`.

Rewrite `h1` using `[map_mul, map_inv, map_pow, inv_mul_eq_one]`. Conclude with `h1.symm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `Fr hFr g h hgh`. Take `⟨j, hj⟩` from `hrat g`.

Take `⟨i, hi⟩` from `hrat Fr⁻¹`. Establish `hFrζ : (Fr : GQ l) ζ = ζ ^ l` using `frob_root Fr hFr hM hlM hζ.pow_eq_one`. Establish `hh : (h : Gl l) = Fr * g * Fr⁻¹` using `by rw [hgh]; group`. Establish `hFr1 : (Fr : GQ l) (ζ ^ i * ρ) = ρ`. Rewrite using `[← hi]`.

Use `show (Fr : GQ l) (((Fr⁻¹ : Gl l) : GQ l) ρ) = ρ`. Rewrite using `[← AlgEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, AlgEquiv.one_apply]`. Establish `hhρ : ((h : Gl l) : GQ l) ρ = ζ ^ (j * l) * ρ`. Rewrite using `[hh, Subgroup.coe_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hi, map_mul, map_pow, hζσ g g.2, hj]`. Establish `e1 : ζ ^ i * (ζ ^ j * ρ) = ζ ^ j * (ζ ^ i * ρ)` using `by ring`.

Rewrite using `[e1, map_mul, hFr1, map_pow, hFrζ, ← pow_mul, mul_comm l j]`. Rewrite using `[hχg h _ hhρ, hχg g j hj, pow_mul]`. Introduce `hχe`. Establish `h1 : ((χ σ' : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχe]`.

Both sides reduce to the same expression. Establish `hζe : IsPrimitiveRoot (ζ ^ M0) e` using `hζ.pow hM rfl`. Take `⟨s, -, hs⟩` from `hroot (ζ ^ M0) hζe.pow_eq_one`. Establish `hzs : IsPrimitiveRoot (z ^ s) e`. Rewrite `hζe` using `[← hs]`.

Conclude with `(IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val) LL.1.val.injective).1 hζe`. Take `⟨c, hc, hcz⟩` from `hzs.eq_pow_of_pow_eq_one h1`. Use `⟨(c : ZMod e), fun g w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.val_natCast, Nat.mod_eq_of_lt hc]`. Take `⟨j, hj⟩` from `hrat g`.

Rewrite using `[hχg g j hj, Units.val_pow_eq_pow_val, ← hcz]`. Establish `hη : (ϖ.seq 0 / ρ ^ M0) ^ e = 1`. Rewrite using `[div_pow, ϖ.seq_zero, ← pow_mul, hρ, div_self (neg_ne_zero.2 hl0)]`. Establish `hgη` using `fix_root (g : Gl l) g.2 he0 hle hη`. Establish `hgπ : ((g : Gl l) : GQ l) (ϖ.seq 0) = (ζ ^ M0) ^ j * ϖ.seq 0`.

Establish `e1 : ϖ.seq 0 = (ϖ.seq 0 / ρ ^ M0) * ρ ^ M0` using `by field_simp`. Rewrite using `[e1, map_mul, hgη, map_pow, hj]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw' : w = (z ^ s) ^ j`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e2 : (w : Om l) * ϖ.seq 0 = (ζ ^ M0) ^ j * ϖ.seq 0` using `hw.trans hgπ`. Rewrite `e2` using `[mul_left_inj' hπ0, ← hs]`. Rewrite using `[e2]`. Both sides reduce to the same expression. Rewrite using `[hw']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ w ^ e = 1) ∧ (∃ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ IsPrimitiveRoot w e) ∧ ∀ (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → Nat.Coprime (orderOf χ) l → (∀ (Fr : Gl l), (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Fr : GQ l) x - x ^ l‖ < 1) → ∀ g h : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (g : Gl l) = Fr⁻¹ * h * Fr → χ h = χ g ^ l) ∧ (χ ^ e = 1 → ∃ c : ZMod e, ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (w : ↥LL.1), (w : Om l) * ϖ.seq 0 = ((g : Gl l) : GQ l) (ϖ.seq 0) → (χ g : ↥LL.1) = w ^ c.val) := by
  intro l _ a e _ _ ϖ LL _ _
  have hp : l.Prime := Fact.out
  obtain ⟨z, hz⟩ := TameDescentExponentData.prim (K := ↥LL.1) (l := l) (e := e) (a := a)
  have he0 : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hle : ¬ l ∣ e := by
    intro h
    have h1 : l ∣ l ^ a := dvd_pow_self l (NeZero.ne a)
    rw [← TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a)] at h1
    exact hp.not_dvd_one ((Nat.dvd_add_right h).1 h1)
  have hzO : IsPrimitiveRoot ((z : ↥LL.1) : Om l) e := hz.map_of_injective (f := LL.1.val) LL.1.val.injective
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hπ0 : ϖ.seq 0 ≠ 0 := ϖ.seq_ne_zero 0
  have hroot : ∀ w : Om l, w ^ e = 1 → ∃ k < e, ((z ^ k : ↥LL.1) : Om l) = w := by
    intro w hw
    obtain ⟨k, hk, h⟩ := hzO.eq_pow_of_pow_eq_one hw
    exact ⟨k, hk, by rw [← h]; rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g _
    have hw : ((g : GQ l) (ϖ.seq 0) / ϖ.seq 0) ^ e = 1 := by
      rw [div_pow, ← map_pow, ϖ.seq_zero, map_neg, map_natCast, div_self (neg_ne_zero.2 hl0)]
    obtain ⟨k, -, hk⟩ := hroot _ hw
    refine ⟨z ^ k, ?_, ?_⟩
    · rw [hk]; field_simp
    · rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  · obtain ⟨g, hg, hgπ⟩ := exists_inertia he0 (ϖ.seq 0) _ ϖ.seq_zero hzO.pow_eq_one
    exact ⟨g, hg, z, hgπ.symm, hz⟩
  · intro χ hχo hχc
    obtain ⟨M0, hM0, hlM0, hM0χ⟩ := chi_trivial LL χ hχo hχc
    have hM : 0 < M0 * e := Nat.mul_pos hM0 he0
    have hlM : ¬ l ∣ M0 * e := fun h => ((Nat.Prime.dvd_mul hp).1 h).elim hlM0 hle
    haveI : NeZero (M0 * e) := ⟨hM.ne'⟩
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (-(l : Om l)) hM
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Om l, IsPrimitiveRoot ζ (M0 * e) :=
      HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (M0 * e)
    obtain ⟨σ, hσ, hσρ⟩ := exists_inertia hM ρ ζ hρ hζ.pow_eq_one
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne', eq_comm, neg_eq_zero] at hρ
      exact hl0 hρ
    have hζσ : ∀ g : Gl l, g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → (g : GQ l) ζ = ζ := fun g hg =>
      fix_root g hg hM hlM hζ.pow_eq_one
    have hrat : ∀ g : Gl l, ∃ j : ℕ, (g : GQ l) ρ = ζ ^ j * ρ := by
      intro g
      have h1 : ((g : GQ l) ρ / ρ) ^ (M0 * e) = 1 := by
        rw [div_pow, ← map_pow, hρ, map_neg, map_natCast, div_self (neg_ne_zero.2 hl0)]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
      exact ⟨j, by rw [hj]; field_simp⟩
    have hσpow : ∀ j : ℕ, ((σ ^ j : Gl l) : GQ l) ρ = ζ ^ j * ρ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Subgroup.coe_mul, AlgEquiv.mul_apply, hσρ, map_mul, ih, hζσ _ (Subgroup.pow_mem _ hσ j), pow_succ]
        ring
    set σ' : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) := ⟨σ, hσ⟩ with hσ'
    have hχg : ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (j : ℕ), ((g : Gl l) : GQ l) ρ = ζ ^ j * ρ →
        χ g = χ σ' ^ j := by
      intro g j hj
      have hfix : ((((σ' ^ j)⁻¹ * g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) : GQ l) ρ = ρ := by
        have h2 := hσpow j
        have h3 : ((((σ' ^ j)⁻¹ * g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) : GQ l) =
            ((σ ^ j : Gl l) : GQ l)⁻¹ * ((g : Gl l) : GQ l) := by
          simp [σ']
        rw [h3, AlgEquiv.mul_apply, hj, ← h2]
        exact AlgEquiv.symm_apply_apply _ ρ
      have h1 : χ ((σ' ^ j)⁻¹ * g) = 1 := by
        refine hM0χ (ρ ^ e) (by rw [← pow_mul, mul_comm e M0]; exact hρ) _ ?_
        rw [map_pow, hfix]
      rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h1
      exact h1.symm
    refine ⟨?_, ?_⟩
    · intro Fr hFr g h hgh
      obtain ⟨j, hj⟩ := hrat g
      obtain ⟨i, hi⟩ := hrat Fr⁻¹
      have hFrζ : (Fr : GQ l) ζ = ζ ^ l := frob_root Fr hFr hM hlM hζ.pow_eq_one
      have hh : (h : Gl l) = Fr * g * Fr⁻¹ := by rw [hgh]; group
      have hFr1 : (Fr : GQ l) (ζ ^ i * ρ) = ρ := by
        rw [← hi]
        show (Fr : GQ l) (((Fr⁻¹ : Gl l) : GQ l) ρ) = ρ
        rw [← AlgEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, AlgEquiv.one_apply]
      have hhρ : ((h : Gl l) : GQ l) ρ = ζ ^ (j * l) * ρ := by
        rw [hh, Subgroup.coe_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hi, map_mul,
          map_pow, hζσ g g.2, hj]
        have e1 : ζ ^ i * (ζ ^ j * ρ) = ζ ^ j * (ζ ^ i * ρ) := by ring
        rw [e1, map_mul, hFr1, map_pow, hFrζ, ← pow_mul, mul_comm l j]
      rw [hχg h _ hhρ, hχg g j hj, pow_mul]
    · intro hχe
      have h1 : ((χ σ' : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχe]; rfl
      have hζe : IsPrimitiveRoot (ζ ^ M0) e := hζ.pow hM rfl
      obtain ⟨s, -, hs⟩ := hroot (ζ ^ M0) hζe.pow_eq_one
      have hzs : IsPrimitiveRoot (z ^ s) e := by
        rw [← hs] at hζe
        exact (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val) LL.1.val.injective).1 hζe
      obtain ⟨c, hc, hcz⟩ := hzs.eq_pow_of_pow_eq_one h1
      refine ⟨(c : ZMod e), fun g w hw => ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hc]
      obtain ⟨j, hj⟩ := hrat g
      rw [hχg g j hj, Units.val_pow_eq_pow_val, ← hcz]

      have hη : (ϖ.seq 0 / ρ ^ M0) ^ e = 1 := by
        rw [div_pow, ϖ.seq_zero, ← pow_mul, hρ, div_self (neg_ne_zero.2 hl0)]
      have hgη := fix_root (g : Gl l) g.2 he0 hle hη
      have hgπ : ((g : Gl l) : GQ l) (ϖ.seq 0) = (ζ ^ M0) ^ j * ϖ.seq 0 := by
        have e1 : ϖ.seq 0 = (ϖ.seq 0 / ρ ^ M0) * ρ ^ M0 := by field_simp
        rw [e1, map_mul, hgη, map_pow, hj]
        ring
      have hw' : w = (z ^ s) ^ j := by
        apply Subtype.ext
        have e2 : (w : Om l) * ϖ.seq 0 = (ζ ^ M0) ^ j * ϖ.seq 0 := hw.trans hgπ
        rw [mul_left_inj' hπ0, ← hs] at e2
        rw [e2]; rfl
      rw [hw']
      ring

end GlobalTheory.TameIner
