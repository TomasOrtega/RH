import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalarStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ScalarFrob

section Union

variable {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]

/- English proof (translation)
Set `T : Set M` to `⋃ m ∈ S, Set.range fun g => rho g m`. Establish `hT : T.Finite` using `hS.biUnion fun m _ => (isCompact_range (hc.comp (continuous_id.prodMk continuous_const))).finite_of_discrete`. Establish `hfin : Finite (AddSubgroup.closure T)`. Establish `: Finite T` using `hT`. Use `AddCommGroup.finite_of_fg_torsion _ fun m => ?_` and prove the remaining obligations.

Take `⟨n, hn⟩` from `hl m.1`. Conclude with `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨l ^ n, pow_pos hl0 n, Subtype.ext hn⟩`. Use `choose e he using hl`. Use `Fintype.ofFinite (AddSubgroup.closure T)` as an intermediate fact. Use `⟨AddSubgroup.closure T, (∑ m : AddSubgroup.closure T, e m.1) + 1, Nat.succ_pos _, hfin, fun m hm => ?_, fun g m hm => ?_, fun m => ?_⟩` and prove the remaining obligations.

Conclude with `AddSubgroup.subset_closure (Set.mem_biUnion hm ⟨1, by simp⟩)`. Establish `: AddSubgroup.closure T ≤ (AddSubgroup.closure T).comap (rho g).toAddMonoidHom`. Rewrite using `[AddSubgroup.closure_le]`. Introduce `x hx`. Simplify using `only [T, Set.mem_iUnion] at hx`.

Take `⟨y, hy, h, rfl⟩` from `hx`. Conclude with `AddSubgroup.subset_closure (Set.mem_biUnion hy ⟨g * h, by simp⟩)`. Conclude with `this hm`. Establish `h1 : e m.1 ≤ (∑ m : AddSubgroup.closure T, e m.1) + 1` using `(Finset.single_le_sum (f := fun m : AddSubgroup.closure T => e m.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)).trans (Nat.le_succ _)`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le h1`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hk, pow_add, mul_comm, mul_smul]`. Simplify using `[he]`.
-/
theorem exists_finite_stable [CompactSpace Γ] (rho : Representation R Γ M) (hc : ContAction rho) {l : ℕ} (hl0 : 0 < l)
    (hl : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0) {S : Set M} (hS : S.Finite) :
    ∃ (N : AddSubgroup M) (n : ℕ), 0 < n ∧ Finite N ∧ S ⊆ N ∧ (∀ g, ∀ m ∈ N, rho g m ∈ N) ∧ ∀ m : N, l ^ n • m = 0 := by
  let T : Set M := ⋃ m ∈ S, Set.range fun g => rho g m
  have hT : T.Finite := hS.biUnion fun m _ =>
    (isCompact_range (hc.comp (continuous_id.prodMk continuous_const))).finite_of_discrete
  have hfin : Finite (AddSubgroup.closure T) := by
    have : Finite T := hT
    refine AddCommGroup.finite_of_fg_torsion _ fun m => ?_
    obtain ⟨n, hn⟩ := hl m.1
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨l ^ n, pow_pos hl0 n, Subtype.ext hn⟩
  choose e he using hl
  have := Fintype.ofFinite (AddSubgroup.closure T)
  refine ⟨AddSubgroup.closure T, (∑ m : AddSubgroup.closure T, e m.1) + 1, Nat.succ_pos _, hfin, fun m hm => ?_,
    fun g m hm => ?_, fun m => ?_⟩
  · exact AddSubgroup.subset_closure (Set.mem_biUnion hm ⟨1, by simp⟩)
  · have : AddSubgroup.closure T ≤ (AddSubgroup.closure T).comap (rho g).toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      intro x hx
      simp only [T, Set.mem_iUnion] at hx
      obtain ⟨y, hy, h, rfl⟩ := hx
      exact AddSubgroup.subset_closure (Set.mem_biUnion hy ⟨g * h, by simp⟩)
    exact this hm
  · have h1 : e m.1 ≤ (∑ m : AddSubgroup.closure T, e m.1) + 1 :=
      (Finset.single_le_sum (f := fun m : AddSubgroup.closure T => e m.1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ m)).trans (Nat.le_succ _)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h1
    apply Subtype.ext
    rw [hk, pow_add, mul_comm, mul_smul]
    simp [he]

def subRep (rho : Representation R Γ M) (N : AddSubgroup M) (hN : ∀ g, ∀ m ∈ N, rho g m ∈ N) (n : ℕ)
    [Module (ZMod n) N] : Representation (ZMod n) Γ N where
  toFun g := (((rho g).toAddMonoidHom.comp N.subtype).codRestrict N fun m => hN g m.1 m.2).toZModLinearMap n
  map_one' := by ext m; simp
  map_mul' g h := by ext m; simp; rfl

omit [TopologicalSpace Γ] [TopologicalSpace M] [DiscreteTopology M] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem subRep_coe (rho : Representation R Γ M) (N : AddSubgroup M) (hN : ∀ g, ∀ m ∈ N, rho g m ∈ N) (n : ℕ)
    [Module (ZMod n) N] (g : Γ) (m : N) : (subRep rho N hN n g m : M) = rho g m := rfl

omit [DiscreteTopology M] in
/- English proof (translation)
The claim follows from `Continuous.subtype_mk (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _`.
-/
theorem contAction_subRep (rho : Representation R Γ M) (hc : ContAction rho) (N : AddSubgroup M)
    (hN : ∀ g, ∀ m ∈ N, rho g m ∈ N) (n : ℕ) [Module (ZMod n) N] : ContAction (subRep rho N hN n) :=
  Continuous.subtype_mk (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.Quotient.subsingleton_iff, eq_top_iff]`. Introduce and unpack `f -`. Take `⟨N, n, hn, hfin, hS, hN, hk⟩` from `exists_finite_stable rho hc hl0 hl (isCompact_range f.2.1).finite_of_discrete`. Use `letI : Module (ZMod (l ^ n)) N := AddCommGroup.zmodModule hk`.

Establish `h1` using `(h N hN n hn).1`. Rewrite `h1` using `[Submodule.Quotient.subsingleton_iff, eq_top_iff]`. Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 (h1 (x := ⟨fun g => ⟨f.1 g, hS ⟨g, rfl⟩⟩, f.2.1.subtype_mk _, fun g g' => Subtype.ext (f.2.2 g g')⟩) trivial)`. Conclude with `(mem_coboundaries1 _ _).2 ⟨m.1, fun g => congrArg Subtype.val (hm g)⟩`. Rewrite using `[Submodule.Quotient.subsingleton_iff, eq_top_iff]`.

Introduce and unpack `f -`. Take `⟨N, n, hn, hfin, hS, hN, hk⟩` from `exists_finite_stable rho hc hl0 hl (isCompact_range f.2.1).finite_of_discrete`. Use `letI : Module (ZMod (l ^ n)) N := AddCommGroup.zmodModule hk`. Establish `h1` using `(h N hN n hn).2`. Rewrite `h1` using `[Submodule.Quotient.subsingleton_iff, eq_top_iff]`.

Take `⟨c, hc', hm⟩` from `(separated_dvr_second_cohomology_mem _ _).1 (h1 (x := ⟨fun g => ⟨f.1 g, hS ⟨g, rfl⟩⟩, f.2.1.subtype_mk _, fun g g' k => Subtype.ext (f.2.2 g g' k)⟩) trivial)`. Conclude with `(separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => (c g).1, continuous_subtype_val.comp hc',`. Use function extensionality and compare the values at `fun p => congrArg Subtype.val (congrFun hm p)⟩`.
-/
theorem subsingleton_of_finite [CompactSpace Γ] (rho : Representation R Γ M) (hc : ContAction rho) {l : ℕ} (hl0 : 0 < l)
    (hl : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0)
    (h : ∀ (N : AddSubgroup M) (hN : ∀ g, ∀ m ∈ N, rho g m ∈ N) (n : ℕ) [Module (ZMod (l ^ n)) N] [Finite N], 0 < n →
      Subsingleton (H1 (subRep rho N hN (l ^ n))) ∧ Subsingleton (H2 (subRep rho N hN (l ^ n)))) :
    Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  constructor
  · rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro f -
    obtain ⟨N, n, hn, hfin, hS, hN, hk⟩ :=
      exists_finite_stable rho hc hl0 hl (isCompact_range f.2.1).finite_of_discrete
    letI : Module (ZMod (l ^ n)) N := AddCommGroup.zmodModule hk
    have h1 := (h N hN n hn).1
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff] at h1
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (h1 (x := ⟨fun g => ⟨f.1 g, hS ⟨g, rfl⟩⟩, f.2.1.subtype_mk _,
      fun g g' => Subtype.ext (f.2.2 g g')⟩) trivial)
    exact (mem_coboundaries1 _ _).2 ⟨m.1, fun g => congrArg Subtype.val (hm g)⟩
  · rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro f -
    obtain ⟨N, n, hn, hfin, hS, hN, hk⟩ :=
      exists_finite_stable rho hc hl0 hl (isCompact_range f.2.1).finite_of_discrete
    letI : Module (ZMod (l ^ n)) N := AddCommGroup.zmodModule hk
    have h1 := (h N hN n hn).2
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff] at h1
    obtain ⟨c, hc', hm⟩ := (separated_dvr_second_cohomology_mem _ _).1 (h1 (x := ⟨fun g => ⟨f.1 g, hS ⟨g, rfl⟩⟩, f.2.1.subtype_mk _,
      fun g g' k => Subtype.ext (f.2.2 g g' k)⟩) trivial)
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => (c g).1, continuous_subtype_val.comp hc',
      funext fun p => congrArg Subtype.val (congrFun hm p)⟩

end Union

section Local

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Establish `hq : ((cycMod F Ω l r φ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = normV v`. Use `cycZ_toZModPow_eq hv hA hφ.2 r` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this`. Establish `hsurj : Function.Surjective (rho φ - (normV v : ZMod (l ^ r)) • LinearMap.id : M →ₗ[ZMod (l ^ r)] M)`.

Rewrite using `[← Finite.injective_iff_surjective, injective_iff_map_eq_zero]`. Introduce `m hm`. Use `hb m ?_` and prove the remaining obligations. Rewrite `hm` using `[LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]`. Conclude with `hm`.

Establish `hd : Subsingleton (H0 ((twDual ((cycMod F Ω l r).comp (Dec (F` using `F) A).subtype) rho).comp (MonoidHom.id _))) := by`. Use `subsingleton_of_forall_eq 0 fun f => Subtype.ext (TDual.ext fun m => ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hsurj m`. Establish `e` using `DFunLike.congr_fun (f.2 φ) (rho φ y)`. Express the relevant statement in the definitionally equal form `((cycMod F Ω l r φ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * f.1 (rho φ⁻¹ (rho φ y)) = f.1 (rho φ y) at e`.

Rewrite `e` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hq]`. Set `f' : M →ₗ[ZMod (l ^ r)] ZMod (l ^ r)` to `f.1`. Express the relevant statement in the definitionally equal form `f' _ = 0`. Rewrite using `[LinearMap.sub_apply, map_sub, LinearMap.smul_apply, map_smul, sub_eq_zero]`. Conclude with `e.symm`.

Establish `hH2 : Subsingleton (H2 rho)` using `(h2 F Ω l r M A rho v hr hA hc).2.2.2.2.1.subsingleton`. Establish `hH0 : Subsingleton (H0 rho)` using `subsingleton_of_forall_eq 0 fun m => Subtype.ext (ha m.1 (m.2 φ))`. Establish `e` using `(h3 F Ω l r M A rho v hr hA hc).2 hv`. Use `(h1 F Ω l r M A rho v hr hA hc).2.1` as an intermediate fact. Rewrite `e` using `[Nat.card_unique (α := H0 rho), Nat.card_unique (α := H2 rho)]`.

Conclude with `⟨(Nat.card_eq_one_iff_unique.1 e).1, hH2⟩`.
-/
theorem finite_case (h1 : LocalFiniteness) (h2 : LocalTateDuality) (h3 : LocalEulerChar) (hA : IsPlaceOver A v)
    (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {r : ℕ} (hr : 0 < r) {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (hc : ContAction rho) (φ : Dec (F := F) A) (hφ : IsFrob A (normV v) (φ : G F Ω))
    (ha : ∀ m, rho φ m = m → m = 0) (hb : ∀ m, rho φ m = normV v • m → m = 0) :
    Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  have hq : ((cycMod F Ω l r φ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = normV v := by
    have := cycZ_toZModPow_eq hv hA hφ.2 r
    rw [map_natCast] at this
    exact this
  have hsurj : Function.Surjective (rho φ - (normV v : ZMod (l ^ r)) • LinearMap.id : M →ₗ[ZMod (l ^ r)] M) := by
    rw [← Finite.injective_iff_surjective, injective_iff_map_eq_zero]
    intro m hm
    refine hb m ?_
    rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul] at hm
    exact hm
  have hd : Subsingleton (H0 ((twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho).comp (MonoidHom.id _))) := by
    refine subsingleton_of_forall_eq 0 fun f => Subtype.ext (TDual.ext fun m => ?_)
    obtain ⟨y, rfl⟩ := hsurj m
    have e := DFunLike.congr_fun (f.2 φ) (rho φ y)
    change ((cycMod F Ω l r φ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * f.1 (rho φ⁻¹ (rho φ y)) = f.1 (rho φ y) at e
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hq] at e
    let f' : M →ₗ[ZMod (l ^ r)] ZMod (l ^ r) := f.1
    change f' _ = 0
    rw [LinearMap.sub_apply, map_sub, LinearMap.smul_apply, map_smul, sub_eq_zero]
    exact e.symm
  have hH2 : Subsingleton (H2 rho) := (h2 F Ω l r M A rho v hr hA hc).2.2.2.2.1.subsingleton
  have hH0 : Subsingleton (H0 rho) := subsingleton_of_forall_eq 0 fun m => Subtype.ext (ha m.1 (m.2 φ))
  have e := (h3 F Ω l r M A rho v hr hA hc).2 hv
  have := (h1 F Ω l r M A rho v hr hA hc).2.1
  rw [Nat.card_unique (α := H0 rho), Nat.card_unique (α := H2 rho)] at e
  exact ⟨(Nat.card_eq_one_iff_unique.1 e).1, hH2⟩

/- English proof (translation)
Establish `: IsGalois F Ω` using `{}`. Establish `: CompactSpace (Dec (F` using `F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact`. Use `⟨eq_bot_iff.2 fun m hm => ha m (hm φ), subsingleton_of_finite rho hc (Fact.out : l.Prime).pos hl fun N hN n _ _ hn => ?_⟩` and prove the remaining obligations. Conclude with `finite_case h1 h2 h3 hA hv hn _ (contAction_subRep rho hc N hN _) φ hφ (fun m hm => Subtype.ext (ha m.1 (congrArg Subtype.val hm))) (fun m hm => Subtype.ext (hb m.1 (congrArg Subtype.val hm)))`.
-/
theorem primary_case (h1 : LocalFiniteness) (h2 : LocalTateDuality) (h3 : LocalEulerChar) (hA : IsPlaceOver A v)
    (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R (Dec (F := F) A) M)
    (hc : ContAction rho) (hl : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0)
    (φ : Dec (F := F) A) (hφ : IsFrob A (normV v) (φ : G F Ω))
    (ha : ∀ m, rho φ m = m → m = 0) (hb : ∀ m, rho φ m = normV v • m → m = 0) :
    H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  have : IsGalois F Ω := {}
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  refine ⟨eq_bot_iff.2 fun m hm => ha m (hm φ),
    subsingleton_of_finite rho hc (Fact.out : l.Prime).pos hl fun N hN n _ _ hn => ?_⟩
  exact finite_case h1 h2 h3 hA hv hn _ (contAction_subRep rho hc N hN _) φ hφ
    (fun m hm => Subtype.ext (ha m.1 (congrArg Subtype.val hm)))
    (fun m hm => Subtype.ext (hb m.1 (congrArg Subtype.val hm)))

end Local

section Matrices

open IsLocalRing

/- English proof (translation)
Use `set M := ((ρ j : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) with hM`. Set `ι : ResidueField O →+* ResidueField Λ` to `ResidueField.map (algebraMap O Λ)`. Establish `: Fact l.Prime` using `⟨hl⟩`. Establish `: CharP (ResidueField Λ) l` using `(CharP.charP_iff_prime_eq_zero hl).2 (by`. Rewrite using `[← map_natCast ι, ← map_natCast (residue O), (residue_eq_zero_iff _).2 hO, map_zero])`.

Establish `hk : residue Λ (κ j) = 1`. Take `⟨n, hn⟩` from `hκ`. Establish `e : (residue Λ (κ j) - 1) ^ (l ^ n) = 0`. Rewrite using `[sub_pow_char_pow, one_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hn, Units.val_one, map_one, sub_self]`. Conclude with `sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero n hl.ne_zero) |>.1 e)`.

Establish `hq' : (q : ResidueField Λ) = 1` using `by rw [← map_natCast ι, hq, map_one]`. Set `W : Matrix (Fin r) (Fin r) Λ` to `(κ j : Λ) • M.map (algebraMap O Λ) - (q : Λ) • 1`. Establish `hW : IsUnit W.det`. Rewrite using `[← residue_ne_zero_iff_isUnit, RingHom.map_det]`. Establish `e : (residue Λ).mapMatrix W = (ι c - 1) • 1`.

Use extensionality with `a b`. Establish `e1` using `congrArg ι (congrFun (congrFun hρ a) b)`. Rewrite `e1` using `[Matrix.map_apply, ResidueField.map_residue]`. Apply the tactic sequence `by_cases hab : a = b <;> simp [W, hk, hq', e1, Matrix.one_apply, hab] <;> simpa [hab] using e1`. Rewrite using `[e, Matrix.det_smul, Matrix.det_one, mul_one]`.

Use `pow_ne_zero _ (sub_ne_zero.2 fun h => hc (ι.injective ?_))` and prove the remaining obligations. Rewrite using `[h, map_one]`. Establish `h1 : matAct (M` using `B) W m = 0 := by`. Use function extensionality and compare the values at `a`. Use `congrFun hm a` as an intermediate fact.

Express the relevant statement in the definitionally equal form `(κ j : Λ) • ∑ b, algebraMap O Λ (M a b) • m b = q • m a at this`. Express the relevant statement in the definitionally equal form `∑ b, W a b • m b = 0`. Rewrite `this` using `[Finset.smul_sum]`. Establish `e : ∀ b, W a b • m b = (κ j : Λ) • algebraMap O Λ (M a b) • m b - if a = b then q • m b else 0` using `fun b => by`. Express the relevant statement in the definitionally equal form `((κ j : Λ) * algebraMap O Λ (M a b) - (q : Λ) * (1 : Matrix (Fin r) (Fin r) Λ) a b) • m b = _`.

Rewrite using `[sub_smul, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Repeatedly rewrite using `[e]`. Rewrite using `[Finset.sum_sub_distrib, this]`. Simplify using the standard rewrite rules.

Establish `h2 : matAct (M` using `B) (W⁻¹ * W) m = 0 := by`. Rewrite using `[matAct_mul, Module.End.mul_apply, h1, map_zero]`. Rewrite `h2` using `[Matrix.nonsing_inv_mul _ hW, matAct_one]`. Then use the resulting hypothesis.
-/
theorem eq_zero_of_scalar {Γ O Λ B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ]
    [IsLocalHom (algebraMap O Λ)] [AddCommGroup B] [Module Λ B] {r l : ℕ} (hl : l.Prime) (hO : (l : O) ∈ maximalIdeal O)
    (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) {j : Γ} (hκ : ∃ n : ℕ, κ j ^ (l ^ n) = 1) {c : ResidueField O} (hc : c ≠ 1)
    (hρ : ((ρ j : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (residue O) = c • 1) {q : ℕ}
    (hq : (q : ResidueField O) = 1) (m : Fin r → B) (hm : repOn ρ κ B j m = q • m) : m = 0 := by
  set M := ((ρ j : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) with hM
  let ι : ResidueField O →+* ResidueField Λ := ResidueField.map (algebraMap O Λ)
  have : Fact l.Prime := ⟨hl⟩
  have : CharP (ResidueField Λ) l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast ι, ← map_natCast (residue O), (residue_eq_zero_iff _).2 hO, map_zero])
  have hk : residue Λ (κ j) = 1 := by
    obtain ⟨n, hn⟩ := hκ
    have e : (residue Λ (κ j) - 1) ^ (l ^ n) = 0 := by
      rw [sub_pow_char_pow, one_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hn, Units.val_one, map_one, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero n hl.ne_zero) |>.1 e)
  have hq' : (q : ResidueField Λ) = 1 := by rw [← map_natCast ι, hq, map_one]
  let W : Matrix (Fin r) (Fin r) Λ := (κ j : Λ) • M.map (algebraMap O Λ) - (q : Λ) • 1
  have hW : IsUnit W.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
    have e : (residue Λ).mapMatrix W = (ι c - 1) • 1 := by
      ext a b
      have e1 := congrArg ι (congrFun (congrFun hρ a) b)
      rw [Matrix.map_apply, ResidueField.map_residue] at e1
      by_cases hab : a = b <;> simp [W, hk, hq', e1, Matrix.one_apply, hab] <;> simpa [hab] using e1
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ (sub_ne_zero.2 fun h => hc (ι.injective ?_))
    rw [h, map_one]
  have h1 : matAct (M := B) W m = 0 := by
    funext a
    have := congrFun hm a
    change (κ j : Λ) • ∑ b, algebraMap O Λ (M a b) • m b = q • m a at this
    change ∑ b, W a b • m b = 0
    rw [Finset.smul_sum] at this
    have e : ∀ b, W a b • m b = (κ j : Λ) • algebraMap O Λ (M a b) • m b - if a = b then q • m b else 0 := fun b => by
      change ((κ j : Λ) * algebraMap O Λ (M a b) - (q : Λ) * (1 : Matrix (Fin r) (Fin r) Λ) a b) • m b = _
      rw [sub_smul, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [e]
    rw [Finset.sum_sub_distrib, this]
    simp
  have h2 : matAct (M := B) (W⁻¹ * W) m = 0 := by
    rw [matAct_mul, Module.End.mul_apply, h1, map_zero]
  rwa [Matrix.nonsing_inv_mul _ hW, matAct_one] at h2

/- English proof (translation)
Rewrite using `[map_mul, map_mul, h, mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one]`.
-/
theorem conj_scalar {Γ k : Type} [Group Γ] [CommRing k] {r : ℕ} (τ : Γ →* Matrix (Fin r) (Fin r) k) {x : Γ} {c : k}
    (h : τ x = c • 1) (g : Γ) : τ (g * x * g⁻¹) = c • 1 := by
  rw [map_mul, map_mul, h, mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one]

end Matrices

section HidaSetting

open IsLocalRing GlobalTheory.TwistDet GlobalTheory.PrimeToInertia

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

def resT : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (ResidueField (X.O0 i)) :=
  ((residue (X.O0 i)).mapMatrix.toMonoidHom.comp (Units.coeHom _)).comp (Tgl i s)

/- English proof (translation)
Rewrite using `[← Tgl_coe]`. Both sides reduce to the same expression.
-/
theorem resT_apply (g : GE N) : resT i s g = (Tmat i s g).map (residue (X.O0 i)) := by
  rw [← Tgl_coe]; rfl

/- English proof (translation)
Establish `h3 : IsUnit (Tmat i s g).det`. Rewrite using `[← Tgl_coe]`. Conclude with `Matrix.isUnits_det_units _`. Rewrite using `[resT_apply, ← Matrix.transpose_map, ← Matrix.map_mul, Tdual, smul_mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ h3, Matrix.transpose_one]`. Use extensionality with `a b`.

Apply the tactic sequence `by_cases hab : a = b <;> simp [Matrix.one_apply, hab, h]`.
-/
theorem dual_mul {g : GE N} (h : residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1) :
    (Tdual i s g).map (residue (X.O0 i)) * (resT i s g).transpose = 1 := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  rw [resT_apply, ← Matrix.transpose_map, ← Matrix.map_mul, Tdual, smul_mul_assoc, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv _ h3, Matrix.transpose_one]
  ext a b
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab, h]

/- English proof (translation)
Use `dual_mul i s h` as an intermediate fact. Rewrite `this` using `[e, Matrix.transpose_smul, Matrix.transpose_one, mul_smul_comm, mul_one]`. Rewrite using `[← this, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem dual_of_scalar {g : GE N} (h : residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1)
    {c : ResidueField (X.O0 i)} (hc : c ≠ 0) (e : resT i s g = c • 1) :
    (Tdual i s g).map (residue (X.O0 i)) = c⁻¹ • 1 := by
  have := dual_mul i s h
  rw [e, Matrix.transpose_smul, Matrix.transpose_one, mul_smul_comm, mul_one] at this
  rw [← this, smul_smul, inv_mul_cancel₀ hc, one_smul]

/- English proof (translation)
Use `congrArg Matrix.transpose (dual_mul i s h)` as an intermediate fact. Rewrite `this` using `[e, smul_mul_assoc, one_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_one]`. Rewrite using `[← this, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem scalar_of_dual {g : GE N} (h : residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1)
    {c : ResidueField (X.O0 i)} (hc : c ≠ 0) (e : (Tdual i s g).map (residue (X.O0 i)) = c • 1) :
    resT i s g = c⁻¹ • 1 := by
  have := congrArg Matrix.transpose (dual_mul i s h)
  rw [e, smul_mul_assoc, one_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  rw [← this, smul_smul, inv_mul_cancel₀ hc, one_smul]

/- English proof (translation)
Establish `hl : ((X.l i : ℕ) : ResidueField (X.O0 i)) = 0`. Rewrite using `[← map_natCast (residue (X.O0 i)), (residue_eq_zero_iff _).2 (l_mem i)]`. Rewrite using `[← Nat.mod_add_div q (2 * X.l i ^ M), hq]`. Use `push_cast`. Rewrite using `[hl, zero_pow (by omega)]`.

Simplify using the standard rewrite rules.
-/
theorem natCast_eq_one {M q : ℕ} (hM : 1 ≤ M) (hq : q % (2 * X.l i ^ M) = 1) : (q : ResidueField (X.O0 i)) = 1 := by
  have hl : ((X.l i : ℕ) : ResidueField (X.O0 i)) = 0 := by
    rw [← map_natCast (residue (X.O0 i)), (residue_eq_zero_iff _).2 (l_mem i)]
  rw [← Nat.mod_add_div q (2 * X.l i ^ M), hq]
  push_cast
  rw [hl, zero_pow (by omega)]
  simp

/- English proof (translation)
Use `cycZ_of_isFrob (l := X.l i) (fun h => hv (X.twistExcludedPlaces_contains_residueChar i h)) (N.plOm.2 v) hσ` as an intermediate fact. Express the relevant statement in the definitionally equal form `residue (X.O0 i) (algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E N.Om (X.l i) σ : ℤ_[X.l i]ˣ) : ℤ_[X.l i])) = 1`. Rewrite using `[this, map_natCast, map_natCast, hq]`.
-/
theorem eps_frob {v : PlE D.host} (hv : v ∉ X.S0 i) (hq : (normV v : ResidueField (X.O0 i)) = 1) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : residue (X.O0 i) ((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) = 1 := by
  have := cycZ_of_isFrob (l := X.l i) (fun h => hv (X.twistExcludedPlaces_contains_residueChar i h)) (N.plOm.2 v) hσ
  change residue (X.O0 i) (algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E N.Om (X.l i) σ : ℤ_[X.l i]ˣ) : ℤ_[X.l i])) = 1
  rw [this, map_natCast, map_natCast, hq]

/- English proof (translation)
Take `⟨hA, ⟨z, L, hz, hL, hS⟩, -⟩` from `hP`. Take `⟨e, he, -, hu, -⟩` from `GlobalTheory.T.tameInertiaElement_acts_by_scalar D N X bkP i s z h.1 hz`. Establish `c0 : residue (X.O0 i) e ≠ 0` using `(residue_ne_zero_iff_isUnit _).2 e.isUnit`. Establish `c1 : residue (X.O0 i) e ≠ 1`. Rewrite `hu` using `[← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero]`.

Conclude with `hu`. Establish `key : ∀ τ : GE N, IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) τ → resT i s τ = residue (X.O0 i) e • 1`. Introduce `τ hτ`. Take `⟨g, hg⟩` from `hS.1 a τ hτ`. Establish `e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1`.

Rewrite using `[map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]`. Use extensionality with `a b`. Apply the tactic sequence `by_cases hab : a = b <;> simp [Matrix.one_apply, hab]`. Establish `e2` using `conj_scalar _ e1 g⁻¹`. Rewrite `e2` using `[show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group]`. Then use the resulting hypothesis.

Establish `hp` using `hA.1 _ v hv`. Establish `hp0` using `hA.1 _ _ (over_refl (P (.inl a)))`. Break down `hv with rfl | hv` into its components or cases. Conclude with `⟨_, c0, c1, key σ hσ⟩`. Establish `ε` using `eps_frob i hp.2.2.2.1 (natCast_eq_one i hM hp.2.2.2.2.2) hσ`.

Take `⟨τ, g, hτ, rfl⟩` from `exists_frob_of_conj X hv hσ`. Establish `ε0` using `eps_frob i hp0.2.2.2.1 (natCast_eq_one i hM hp0.2.2.2.2.2) hτ`. Rewrite `ε` using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Use `⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩` and prove the remaining obligations. Take `⟨A, hA⟩` from `h.2.2.1`.

Establish `e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) = residue (X.O0 i) e • 1`. Rewrite using `[← key τ hτ, resT_apply]`. Use extensionality with `a b`. Simplify using `[ε0]`. Rewrite using `[hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem frob_scalar (bkP : BKPh X) (h : GalHyp bkP i s) {M R : ℕ} {P : Fin R ⊕ Fin R → PlE D.host} {d φ φ'} (hM : 1 ≤ M)
    (hP : Position i s M P d φ φ') {a : Fin R} {v : PlE D.host} (hv : Over (P (.inl a)) v) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : ∃ c : ResidueField (X.O0 i), c ≠ 0 ∧ c ≠ 1 ∧ resT i s σ = c • 1 := by
  obtain ⟨hA, ⟨z, L, hz, hL, hS⟩, -⟩ := hP
  obtain ⟨e, he, -, hu, -⟩ := GlobalTheory.T.tameInertiaElement_acts_by_scalar D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have key : ∀ τ : GE N, IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) τ →
      resT i s τ = residue (X.O0 i) e • 1 := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hS.1 a τ hτ
    have e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1 := by
      rw [map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have e2 := conj_scalar _ e1 g⁻¹
    rwa [show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group] at e2
  have hp := hA.1 _ v hv
  have hp0 := hA.1 _ _ (over_refl (P (.inl a)))
  rcases hv with rfl | hv
  · exact ⟨_, c0, c1, key σ hσ⟩
  · have ε := eps_frob i hp.2.2.2.1 (natCast_eq_one i hM hp.2.2.2.2.2) hσ
    obtain ⟨τ, g, hτ, rfl⟩ := exists_frob_of_conj X hv hσ
    have ε0 := eps_frob i hp0.2.2.2.1 (natCast_eq_one i hM hp0.2.2.2.2.2) hτ
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at ε
    refine ⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩
    obtain ⟨A, hA⟩ := h.2.2.1
    have e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) =
        residue (X.O0 i) e • 1 := by
      rw [← key τ hτ, resT_apply]
      ext a b
      simp [ε0]
    rw [hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

end HidaSetting

open GlobalTheory.PrimeToInertia in

/- English proof (translation)
Introduce `h1 h2 h3 _ D N X bkP i s h M R P d φ φ' hM hP Λ _ _ _ _ κ hκ hκl B _ _ _ _ hB ρ hρ a v hv`. Establish `hp` using `hP.1.1 _ v hv`. Establish `hq` using `natCast_eq_one i hM hp.2.2.2.2.2`. Take `⟨σ, hσ⟩` from `exists_isFrob (N.plOm.2 v)`. Take `⟨c, c0, c1, hc⟩` from `frob_scalar i s bkP h hM hP hv hσ`.

Choose the witnesses or unpack the hypotheses as in `⟨c', c1', hc'⟩ : ∃ c' : IsLocalRing.ResidueField (X.O0 i), c' ≠ 1 ∧ ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) = c' • 1 := by`. Break down `hρ with rfl | hρ` into its components or cases. Conclude with `⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩`. Conclude with `⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i hp.2.2.2.1 hq hσ) c0 hc]⟩`. Establish `hcont : Continuous fun g => ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))`.

Break down `hρ with rfl | hρ` into its components or cases. Repeatedly rewrite using `[Tgl_coe]`. Conclude with `continuous_Tmat i s`. Repeatedly rewrite using `[show ∀ g, _ = _ from hρ]`. Conclude with `continuous_Tdual i s`.

Use `primary_case (l := X.l i) h1 h2 h3 (N.plOm.2 v) (fun h => hp.2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i h)) _ ?_ (fun m => ?_) ⟨σ, hσ.1⟩ hσ (fun m hm => ?_) (fun m hm => ?_)` and prove the remaining obligations. Conclude with `(contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ hcont κ hκ hB).comp (f := fun p : DecV N v × (Fin D.R.r → B) => ((p.1 : GE N), p.2)) (by fun_prop)`. Take `⟨n, hn⟩` from `exists_pow_kill hB m`. Use `⟨n, funext fun a => ?_⟩` and prove the remaining obligations. Use `hn _ (map_mem_pow (Λ := Λ) (Ideal.pow_mem_pow (l_mem i) n)) a` as an intermediate fact.

Rewrite `this` using `[map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Conclude with `this`. Conclude with `eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)`. Conclude with `eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' hq m hm`.
-/
theorem firstHalf : LocalFiniteness → LocalTateDuality → LocalEulerChar → TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s := by
  intro h1 h2 h3 _ D N X bkP i s h M R P d φ φ' hM hP Λ _ _ _ _ κ hκ hκl B _ _ _ _ hB ρ hρ a v hv
  have hp := hP.1.1 _ v hv
  have hq := natCast_eq_one i hM hp.2.2.2.2.2
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
  obtain ⟨c, c0, c1, hc⟩ := frob_scalar i s bkP h hM hP hv hσ
  obtain ⟨c', c1', hc'⟩ : ∃ c' : IsLocalRing.ResidueField (X.O0 i), c' ≠ 1 ∧
      ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) = c' • 1 := by
    rcases hρ with rfl | hρ
    · exact ⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩
    · exact ⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i hp.2.2.2.1 hq hσ) c0 hc]⟩
  have hcont : Continuous fun g => ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
    rcases hρ with rfl | hρ
    · simp_rw [Tgl_coe]; exact continuous_Tmat i s
    · simp_rw [show ∀ g, _ = _ from hρ]; exact continuous_Tdual i s
  refine primary_case (l := X.l i) h1 h2 h3 (N.plOm.2 v) (fun h => hp.2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i h)) _
    ?_ (fun m => ?_) ⟨σ, hσ.1⟩ hσ (fun m hm => ?_) (fun m hm => ?_)
  · exact (contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ hcont κ hκ hB).comp
      (f := fun p : DecV N v × (Fin D.R.r → B) => ((p.1 : GE N), p.2)) (by fun_prop)
  · obtain ⟨n, hn⟩ := exists_pow_kill hB m
    refine ⟨n, funext fun a => ?_⟩
    have := hn _ (map_mem_pow (Λ := Λ) (Ideal.pow_mem_pow (l_mem i) n)) a
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
    exact this
  · exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)
  · exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' hq m hm

end GlobalTheory.ScalarFrob
